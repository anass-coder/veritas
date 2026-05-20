#include <algorithm>
#include <array>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
#include <chrono>

#include "translator.hpp"

// ============================================================
// Dispatch a non-control-flow instruction to the appropriate
// translator. The output state name is supplied by the caller
// so the CFG translation layer can decide how states flow across
// branches.
// ============================================================

static int translate_stateful_insn(const bpf_insn& insn,
                                   const std::string& in_state,
                                   const std::string& out_state,
                                   std::stringstream& out,
                                   RegUsage& regs,
                                   int depth) {
    if (MemoryDecoder::is_memory(insn))
        return translate_memory_insn(insn, in_state, out_state, out, regs, depth);
    if (DataMovDecoder::is_datamov(insn))
        return translate_datamov_insn(insn, in_state, out_state, out, regs, depth);
    if (ArithDecoder::is_arithmetic(insn))
        return translate_arith_insn(insn, in_state, out_state, out, regs, depth);
    return -1;
}

// ============================================================
// Core CFG-walking translation loop
// ============================================================

int insns_to_dafny(const bpf_insn* insns,
                   int insn_cnt,
                   std::stringstream& trans_dafny,
                   bool* used_regs,
                   uint64_t *duration) {
    if (!insns || !used_regs || insn_cnt < 1){
        if (duration) *duration = 0;
        return -1;
    }

    auto start = std::chrono::high_resolution_clock::now();
        

    FreshStateGen fresh_states;
    std::vector<ResumePoint> stack;

    int insn_idx     = 0;
    int trans_cnt    = 0;
    std::string current_state = "init_s";

    while (true) {
        if (trans_cnt > 1000) {
            trans_dafny << indent(0) << "// translation stopped after 1000 steps\n";
            break;
        }

        // ── Path finished: drain resume stack ──────────────────────────────
        if (insn_idx == -1) {
            if (stack.empty()) break;

            ResumePoint rp = stack.back();
            stack.pop_back();

            if (rp.kind == ResumeKind::CloseBlock) {
                trans_dafny << indent(static_cast<int>(stack.size() / 2)) << "}\n";
                continue;
            }

            if (rp.kind == ResumeKind::ElseBranch) {
                trans_dafny << indent(static_cast<int>(stack.size() / 2)) << "} else {\n";
                insn_idx      = rp.target_idx;
                current_state = rp.state_name;
                continue;
            }

            if (rp.kind == ResumeKind::ReturnFromCall) {
                trans_dafny << indent(static_cast<int>(stack.size() / 2)) << "}\n";
                insn_idx      = rp.target_idx;
                current_state = rp.state_name;
                continue;
            }

            if (rp.kind == ResumeKind::MergeContinue) {
                trans_dafny << indent(static_cast<int>(stack.size() / 2)) << "}\n";
                if (rp.target_idx == -1) {
                    continue;  // no common tail, keep draining
                }
                insn_idx      = rp.target_idx;
                current_state = rp.join_state_name;
                continue;
            }
        }

        if (insn_idx < 0 || insn_idx >= insn_cnt) {
            if (insn_idx == insn_cnt) {
                insn_idx = -1;
                continue;
            }
            trans_dafny << indent(static_cast<int>(stack.size() / 2))
                        << "// ERROR: out of range: " << insn_idx << "\n";
            return -1;
        }

        ++trans_cnt;
        const bpf_insn& insn = insns[insn_idx];

        RegUsage regs;
        std::copy(used_regs, used_regs + BPF_REG_COUNT, regs.used.begin());

        try {
            const int header_depth = static_cast<int>(stack.size() / 2);
            const int stmt_depth   = static_cast<int>((stack.size() + 1) / 2);

            // ── Fall-through-into-merge detection ──────────────────────────
            for (int i = static_cast<int>(stack.size()) - 1; i >= 0; --i) {
                if (stack[i].kind == ResumeKind::MergeContinue) {
                    if (stack[i].target_idx != -1 &&
                        insn_idx == stack[i].target_idx) {
                        trans_dafny << indent(stmt_depth)
                                    << stack[i].join_state_name
                                    << " := " << current_state << ";\n";
                        insn_idx = -1;
                    }
                    break;
                }
            }
            if (insn_idx == -1) continue;

            // ── Exit ───────────────────────────────────────────────────────
            if (is_exit_insn(insn)) {
                used_regs[0] = true;
                const std::string exit_state = fresh_states.next();
                trans_dafny << indent(stmt_depth)
                            << "var " << exit_state << " := Exit(" << current_state << ");\n";
                trans_dafny << indent(stmt_depth) << "return;\n";
                insn_idx = -1;
                continue;
            }

            // ── Call (opaque: helper or BPF-to-BPF subprogram) ─────────────────
            
                
            if (is_call(insn)) {
                const std::string out_state = fresh_states.next();
                trans_dafny << indent(stmt_depth)
                            << "var " << out_state
                            << " := call_step(" << current_state << ", CALL);\n";
                current_state = out_state;
                insn_idx      = insn_idx + 1;
                continue;
            }
            

            // ── Conditional jump ───────────────────────────────────────────
            if (is_cond_jump(insn)) {
                const bool reg_src = (insn.code & bpf_opcode::SRC_MASK) == bpf_opcode::X;
                regs.mark(insn.dst_reg);
                if (reg_src) regs.mark(insn.src_reg);

                const std::string jump_state = fresh_states.next();
                const std::string join_state = fresh_states.next();
                const std::string jump_call  = emit_cond_jump_call(insn, current_state);

                trans_dafny << indent(stmt_depth)
                            << "var " << jump_state << " := " << jump_call << ";\n";
                trans_dafny << indent(stmt_depth)
                            << "var " << join_state << " : State;\n";
                trans_dafny << indent(header_depth)
                            << "if " << jump_state << ".jmp_res {\n";

                std::copy(regs.used.begin(), regs.used.end(), used_regs);

                const int then_idx  = jump_target_idx(insn, insn_idx);
                const int else_idx  = insn_idx + 1;
                const int merge_target = find_merge_target(insns, insn_cnt, else_idx, then_idx);

                ResumePoint merge_rp;
                merge_rp.kind            = ResumeKind::MergeContinue;
                merge_rp.target_idx      = merge_target;
                merge_rp.state_name      = jump_state;
                merge_rp.join_state_name = join_state;

                ResumePoint else_rp;
                else_rp.kind       = ResumeKind::ElseBranch;
                else_rp.target_idx = else_idx;
                else_rp.state_name = jump_state;

                stack.push_back(merge_rp);
                stack.push_back(else_rp);

                current_state = jump_state;
                insn_idx      = then_idx;
                continue;
            }

            // ── Unconditional jump ─────────────────────────────────────────
            if (is_uncond_jump(insn)) {
                const int merge_target = jump_target_idx(insn, insn_idx);
                if (!stack.empty()) {
                    for (int i = static_cast<int>(stack.size()) - 1; i >= 0; --i) {
                        if (stack[i].kind == ResumeKind::MergeContinue) {
                            trans_dafny << indent(stmt_depth)
                                        << stack[i].join_state_name
                                        << " := " << current_state << ";\n";
                            break;
                        }
                    }
                    insn_idx = -1;
                } else {
                    insn_idx = merge_target;
                }
                continue;
            }

            // ── LD_IMM64 — two-slot wide immediate ─────────────────────────
            if (is_ld_imm64_pair(insn)) {
                if (insn_idx + 1 >= insn_cnt) {
                    trans_dafny << indent(stmt_depth)
                                << "// ERROR: LD_IMM64 at end of program\n";
                    return -1;
                }
                const bpf_insn& next = insns[insn_idx + 1];
                // Validate LD_IMM64 reserved fields
                if (insn.off != 0 ||
                    next.code != 0 ||
                    next.dst_reg != 0 ||
                    next.src_reg != 0 ||
                    next.off != 0) {
                    trans_dafny << indent(stmt_depth)
                                << "// ERROR: LD_IMM64 uses reserved fields\n";
                    return -1;
                }
                const uint64_t wide = ((uint64_t)(uint32_t)insn.imm) |
                                      ((uint64_t)(uint32_t)next.imm << 32);

                const char* moviop;
                if (insn.src_reg == BPF_PSEUDO_MAP_FD)
                    moviop = "LOADMAPFD";
                else if (insn.src_reg == BPF_PSEUDO_MAP_IDX)
                    moviop = "LOADMAPIDX";
                else
                    moviop = "LOADIMM64";

                const std::string out_state = fresh_states.next();
                trans_dafny << indent(stmt_depth)
                            << "var " << out_state << " := datamov_imm("
                            << current_state << ", DATAMOVIMM("
                            << reg_to_dafny(insn.dst_reg) << ", "
                            << bv64_literal(wide) << ", "
                            << moviop << "));\n";

                current_state = out_state;
                insn_idx += 2;
                ++trans_cnt;
                continue;
            }

            // ── Normal instruction ─────────────────────────────────────────
            const std::string out_state = fresh_states.next();
            const int rc = translate_stateful_insn(
                insn, current_state, out_state, trans_dafny, regs, stmt_depth);

            if (rc != 0) {
                trans_dafny << indent(stmt_depth)
                            << "// insn " << insn_idx << ": unsupported\n";
                return -1;
            }

            std::copy(regs.used.begin(), regs.used.end(), used_regs);
            current_state = out_state;
            insn_idx      = next_linear_insn_idx(insn, insn_idx);

        } catch (const std::exception& ex) {
            trans_dafny << indent(static_cast<int>((stack.size() + 1) / 2))
                        << "// insn " << insn_idx
                        << ": translation error: " << ex.what() << "\n";
            return -1;
        }
    }

    auto end = std::chrono::high_resolution_clock::now();
    if (duration) {
        *duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start).count();
    }

    return trans_cnt;
}


std::string build_dafny_string(const bpf_insn* insns,
                               int insn_cnt,
                               const std::string& method_name) {
    std::stringstream trans;
    bool used_regs[BPF_REG_COUNT] = {false};

    
    uint64_t duration = 0;
    const int translated = insns_to_dafny(insns, insn_cnt, trans, used_regs, &duration);
    if (translated < 0)
        throw std::runtime_error("Translation failed");

    trans << "\n    }\n";
    

    return trans.str();
}