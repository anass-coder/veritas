include "proof-utils.dfy"

module NoleakageProof {

    import opened Terms
    import opened DataTypes
    import opened States
    import opened Utils
    
    import opened eBPFArithSpec
    import opened eBPFDataMoveSpec
    import opened eBPFCtrlFlowSpec
    import opened eBPFMemSpec

    import opened ProofUtils

    lemma {:timeLimit 30} {:priority 2} non_leakage(
        s1: State, s2: State, insn: Instruction
    )
    //
    requires !s1.cfg.allow_ptr_leak && !s2.cfg.allow_ptr_leak
    requires precond_sat(s1, insn)
    requires precond_sat(s2, insn)
    // Constraints all scalars are the same
    requires same_low_sec_data(s1, s2)
    // Declassification: leak the relative relation of addrs
    //                   addr[off] = val : addr == addr'
    requires declassfy_addr_base(s1, s2, insn)
    //
    // Cmp addr1 addr2 : addr1 == addr1' && addr2 == addr2'
    requires declassfy_cmp(s1, s2, insn)
    //
    ensures same_low_sec_data(
                exec_one_insn(s1, insn),
                exec_one_insn(s2, insn)
            )
    {
        match insn {

            case ARITHUNARY(dst, uop) =>
                assert {:split_here} true;
                non_leakage_ARITHUNARY(s1, s2, insn);

            case ARITHBINREG(_, _, ADD64) => 
                assert {:split_here} true;  
                non_leakage_ADD64_reg(s1, s2, insn);
            case ARITHBINREG(_, _, SUB64) => 
                assert {:split_here} true;
                non_leakage_SUB64_reg(s1, s2, insn);
            case ARITHBINREG(_, _, _) =>
                assert {:split_here} true;
                non_leakage_ARITHBINREG(s1, s2, insn);
            
            case ARITHBINIMM(_, _, ADD64) => 
                assert {:split_here} true;
                non_leakage_ADD64_imm(s1, s2, insn);
            case ARITHBINIMM(_, _, SUB64) => 
                assert {:split_here} true;
                non_leakage_SUB64_imm(s1, s2, insn);
            case ARITHBINIMM(_, _, _) => 
                assert {:split_here} true;
                non_leakage_ARITHBINIMM(s1, s2, insn);
            
            case DATAMOVIMM(dst, src_imm, moviop) =>
                assert {:split_here} true;
                non_leakage_DATAMOVIMM(s1, s2, insn);
            
            case DATAMOVREG(dst, src, movrop) =>
                assert {:split_here} true;
                non_leakage_DATAMOVREG(s1, s2, insn);
            
            case CONDJMPREG(dst, src, jmpop) =>
                assert {:split_here} true;
                non_leakage_CONDJMPREG(s1, s2, insn);
            
            case CONDJMPIMM(dst, src_imm, jmpop) =>
                assert {:split_here} true;
                non_leakage_CONDJMPIMM(s1, s2, insn);
            
            case MEMLD(dst, src, off, size, sign_ext) =>
                assert {:split_here} true;
                non_leakage_MEMLD(s1, s2, insn);
            
            case MEMSTX(dst, src, off, size) =>
                assert {:split_here} true;
                non_leakage_MEMST_REG(s1, s2, insn);
            
            case MEMST(dst, src_imm, off, size) =>
                assert {:split_here} true;
                non_leakage_MEMST_IMM(s1, s2, insn);
            
            case ATOMICLS(dst, src, off, size, op) =>
                non_leakage_MEMATOMIC(s1, s2, insn);
        }
    }

    // ----------------------------------------------------------------
    //                   Predicates for non_leakage
    // ----------------------------------------------------------------

    ghost predicate same_low_sec_data(s1: State, s2: State)
    {
        // some scalar secretes can be marked as Scalar(Sec, val)
        // So here we only need to change is_scalar as
        // is_low_sec_scalar for both mem slots and regs
        //
        (is_scalar(s1.R0) || is_scalar(s2.R0) ==> s1.R0 == s2.R0)
        &&
        (is_scalar(s1.R1) || is_scalar(s2.R1) ==> s1.R1 == s2.R1)
        &&
        (is_scalar(s1.R2) || is_scalar(s2.R2) ==> s1.R2 == s2.R2)
        &&
        (is_scalar(s1.R3) || is_scalar(s2.R3) ==> s1.R3 == s2.R3)
        &&
        (is_scalar(s1.R4) || is_scalar(s2.R4) ==> s1.R4 == s2.R4)
        &&
        (is_scalar(s1.R5) || is_scalar(s2.R5) ==> s1.R5 == s2.R5)
        &&
        (is_scalar(s1.R6) || is_scalar(s2.R6) ==> s1.R6 == s2.R6)
        &&
        (is_scalar(s1.R7) || is_scalar(s2.R7) ==> s1.R7 == s2.R7)
        &&
        (is_scalar(s1.R8) || is_scalar(s2.R8) ==> s1.R8 == s2.R8)
        &&
        (is_scalar(s1.R9) || is_scalar(s2.R9) ==> s1.R9 == s2.R9)
        &&
        (is_scalar(s1.R10) || is_scalar(s2.R10) ==> s1.R10 == s2.R10)
        &&
        s1.cfg == s2.cfg
        &&
        s1.jmp_res == s2.jmp_res
        &&
        s1.maps_meta == s2.maps_meta
        &&
        // Seed for loading from concurrently accessed memory
        s1.rand == s2.rand
        &&
        //
        mem_preserve_sec(s1, s2)
        /*
        (
            |s1.mems| == |s2.mems|
            &&
            forall rid, memid | (
                0 <= rid < |s1.mems|
                &&
                0 <= memid < |s1.mems[rid]|
            )
            :: (
                |s1.mems[rid]| == |s2.mems[rid]|
                &&
                var mem1 := s1.mems[rid][memid];
                var mem2 := s2.mems[rid][memid];
                //
                |mem1.data| == |mem2.data|
                &&
                mem1.base == mem2.base
                &&
                mem1.mem_type == mem2.mem_type
                // &&
                // mem1.mem_perm == mem2.mem_perm
                &&
                mem1.is_concur == mem2.is_concur
                &&
                (
                    |mem1.data| == |mem2.data|
                    &&
                    forall i | 0 <= i < |mem1.data|
                    :: (
                        (
                            (
                                is_scalar(mem1.data[i].etypev)
                                ||
                                is_scalar(mem2.data[i].etypev)
                            )
                            ==> mem1.data[i] == mem2.data[i]
                        )
                        &&
                        mem1.data[i].field_size == mem2.data[i].field_size
                    )
                    
                )
            )
        )
        */
    }

    ghost predicate mem_preserve_sec(s1: State, s2: State)
    {
        (
            |s1.mems| == |s2.mems|
            &&
            forall rid, memid | (
                0 <= rid < |s1.mems|
                &&
                0 <= memid < |s1.mems[rid]|
            )
            :: (
                |s1.mems[rid]| == |s2.mems[rid]|
                &&
                var mem1 := s1.mems[rid][memid];
                var mem2 := s2.mems[rid][memid];
                //
                |mem1.data| == |mem2.data|
                &&
                mem1.base == mem2.base
                &&
                mem1.mem_type == mem2.mem_type
                // &&
                // mem1.mem_perm == mem2.mem_perm
                &&
                mem1.is_concur == mem2.is_concur
                &&
                (
                    |mem1.data| == |mem2.data|
                    &&
                    forall i | 0 <= i < |mem1.data|
                    :: (
                        (
                            (
                                is_scalar(mem1.data[i].etypev)
                                ||
                                is_scalar(mem2.data[i].etypev)
                            )
                            ==> mem1.data[i] == mem2.data[i]
                        )
                        &&
                        mem1.data[i].field_size == mem2.data[i].field_size
                    )
                    
                )
            )
        )
    }


    ghost predicate declassfy_cmp(s1: State, s2: State, insn: Instruction)
    {
        match insn {
            
            case CONDJMPREG(dst, src, jmpop) =>
                declassfy_cmp_reg(s1, s2, insn)
            
            case CONDJMPIMM(dst, src_imm, jmpop) =>
                declassfy_cmp_imm(s1, s2, insn)
            
            case _ => true
        }
    }

    ghost predicate declassfy_cmp_reg(s1: State, s2: State, insn: Instruction)
    {
        exists dst, src, jmpop ::
        (

            insn == CONDJMPREG(dst, src, jmpop)
            &&
            var dst_tv1 := get_reg_typeval(s1, dst);
            var dst_tv2 := get_reg_typeval(s2, dst);
            var src_tv1 := get_reg_typeval(s1, src);
            var src_tv2 := get_reg_typeval(s2, src);
            
            match jmpop {
                
                case JEQ64 | JNE64 =>
                (
                    (ptr_or_ptrornull(dst_tv1) && ptr_or_ptrornull(src_tv1))
                    ||
                    (ptr_or_ptrornull(dst_tv1) && is_scalar_zero(src_tv1))
                    ||
                    (is_scalar_zero(dst_tv1) && ptr_or_ptrornull(src_tv1))
                    ||
                    (ptr_or_ptrornull(dst_tv2) && ptr_or_ptrornull(src_tv2))
                    ||
                    (ptr_or_ptrornull(dst_tv2) && is_scalar_zero(src_tv2))
                    ||
                    (is_scalar_zero(dst_tv2) && ptr_or_ptrornull(src_tv2))
                ) ==> dst_tv1 == dst_tv2 && src_tv1 == src_tv2

                case JGT64 | JGE64 | JSGT64 | JSGE64 |
                     JLT64 | JLE64 | JSLT64 | JSLE64 => 
                (
                    (ptr_or_ptrornull(dst_tv1) && ptr_or_ptrornull(src_tv1))
                    ||
                    (ptr_or_ptrornull(dst_tv2) && ptr_or_ptrornull(src_tv2))
                ) ==> dst_tv1 == dst_tv2 && src_tv1 == src_tv2
                
                case _ => true
            }
        )
    }

    ghost predicate declassfy_cmp_imm(s1: State, s2: State, insn: Instruction)
    {
        exists dst, src_imm, jmpop ::
        (
            insn == CONDJMPIMM(dst, src_imm, jmpop)
            &&
            var dst_tv1 := get_reg_typeval(s1, dst);
            var dst_tv2 := get_reg_typeval(s2, dst);
            match jmpop {
                case JEQ64 | JNE64 =>
                (
                    src_imm == 0
                    &&
                    (
                        ptr_or_ptrornull(dst_tv1)
                        ||
                        ptr_or_ptrornull(dst_tv2)
                    )
                ) ==> dst_tv1 == dst_tv2
                
                case _ => true
            }
        )
    }

    ghost predicate declassfy_addr_base(s1: State, s2: State, insn: Instruction)
    {
        match insn {
            
            case MEMLD(_, src, _, _, _) =>
                get_reg_typeval(s1, src) == get_reg_typeval(s2, src)

            case MEMSTX(dst, _, _, _)   =>
                get_reg_typeval(s1, dst) == get_reg_typeval(s2, dst)
            
            case MEMST(dst, _, _, _)    =>
                get_reg_typeval(s1, dst) == get_reg_typeval(s2, dst)
            
            case ATOMICLS(dst, _, _, _, _) =>
                get_reg_typeval(s1, dst) == get_reg_typeval(s2, dst)
            
            case ARITHBINREG(dst, src, op) => (
                
                var dst_tv1 := get_reg_typeval(s1, dst);
                var src_tv1 := get_reg_typeval(s1, src);
                var dst_tv2 := get_reg_typeval(s2, dst);
                var src_tv2 := get_reg_typeval(s2, src);
                
                if (
                    is_ptr(dst_tv1) && is_ptr(src_tv1)
                    &&
                    same_mem_region(s1, dst, src)
                    &&
                    is_ptr(dst_tv2) && is_ptr(src_tv2)
                    &&
                    same_mem_region(s2, dst, src)
                )
                then dst_tv1 == dst_tv2 && src_tv1 == src_tv2
                else true
            )

            case _ => true
        }
    }

    // ----------------------------------------------------------------
    //        Helper lemmas for non_leakage of arithmetic insns
    // ----------------------------------------------------------------
    
    lemma {:timeLimit 30} non_leakage_ARITHUNARY(
        s1: State, s2: State, insn: Instruction
    )
    requires exists dst, uop :: insn == ARITHUNARY(dst, uop)
    //
    requires !s1.cfg.allow_ptr_leak && !s2.cfg.allow_ptr_leak
    requires precond_sat(s1, insn)
    requires precond_sat(s2, insn)
    //
    requires same_low_sec_data(s1, s2)
    //
    ensures same_low_sec_data(
                exec_one_insn(s1, insn),
                exec_one_insn(s2, insn)
            )
    {
        var (dst, uop) := (insn.dst, insn.uop);
        var dst_tv1 := get_reg_typeval(s1, dst);
        var dst_tv2 := get_reg_typeval(s2, dst);

        assert {:split_here} is_scalar(dst_tv1) && is_scalar(dst_tv2);
        assert {:split_here} dst_tv1 == dst_tv2;

        var dst_val1 := get_reg_arith_val(s1, dst);
        var dst_val2 := get_reg_arith_val(s2, dst);

        assert {:split_here} dst_val1 == dst_val2;
        assert {:split_here} s1.cfg.host_le == s2.cfg.host_le;

        var new_val1 := compute_unary(s1.cfg.host_le, dst_val1, uop);
        var new_val2 := compute_unary(s2.cfg.host_le, dst_val2, uop);

        assert {:split_here} new_val1 == new_val2;
        state_update_preserve_equal(
            s1, s2, dst,
            Scalar(Normal, new_val1), Scalar(Normal, new_val2)
        );
    }

    lemma {:timeLimit 20} non_leakage_ARITHBINREG(
        s1: State, s2: State, insn: Instruction
    )
    requires exists dst, src, binop
            ::
            insn == ARITHBINREG(dst, src, binop)
            &&
            binop != ADD64 && binop != SUB64
    //
    requires !s1.cfg.allow_ptr_leak && !s2.cfg.allow_ptr_leak
    requires precond_sat(s1, insn)
    requires precond_sat(s2, insn)
    //
    requires same_low_sec_data(s1, s2)
    //
    ensures same_low_sec_data(
                exec_one_insn(s1, insn),
                exec_one_insn(s2, insn)
            )
    {
        var (dst, src, binop) := (insn.dst, insn.src, insn.binop);
        var dst_tv1 := get_reg_typeval(s1, dst);
        var dst_tv2 := get_reg_typeval(s2, dst);
        var src_tv1 := get_reg_typeval(s1, src);
        var src_tv2 := get_reg_typeval(s2, src);

        assert {:split_here} is_scalar(dst_tv1) && is_scalar(dst_tv2);
        assert {:split_here} is_scalar(src_tv1) && is_scalar(src_tv2);
        assert {:split_here} dst_tv1 == dst_tv2;
        assert {:split_here} src_tv1 == src_tv2;

        var dst_val1 := get_reg_arith_val(s1, dst);
        var dst_val2 := get_reg_arith_val(s2, dst);

        var src_val1 := get_reg_arith_val(s1, src);
        var src_val2 := get_reg_arith_val(s2, src);

        assert {:split_here} dst_val1 == dst_val2;
        assert {:split_here} src_val1 == src_val2;

        var new_val1 := compute_bin_arith(binop, dst_val1, src_val1);
        var new_val2 := compute_bin_arith(binop, dst_val2, src_val2);

        assert {:split_here} new_val1 == new_val2;

        var new_reg_tv1 := Scalar(Normal, new_val1);
        var new_reg_tv2 := Scalar(Normal, new_val2);

        assert {:split_here} new_reg_tv1 == new_reg_tv2;

        state_update_preserve_equal(s1, s2, dst, new_reg_tv1, new_reg_tv2);
    }


    lemma {:timeLimit 20} non_leakage_ARITHBINIMM(
        s1: State, s2: State, insn: Instruction
    )
    requires exists dst, src_imm, binop
            ::
            insn == ARITHBINIMM(dst, src_imm, binop)
            &&
            binop != ADD64 && binop != SUB64
    //
    requires !s1.cfg.allow_ptr_leak && !s2.cfg.allow_ptr_leak
    requires precond_sat(s1, insn)
    requires precond_sat(s2, insn)
    //
    requires same_low_sec_data(s1, s2)
    //
    ensures same_low_sec_data(
                exec_one_insn(s1, insn),
                exec_one_insn(s2, insn)
            )
    {
        var (dst, src_imm, binop) := (insn.dst, insn.src_imm, insn.binop);
        var dst_tv1 := get_reg_typeval(s1, dst);
        var dst_tv2 := get_reg_typeval(s2, dst);

        assert {:split_here} is_scalar(dst_tv1) && is_scalar(dst_tv2);
        assert {:split_here} dst_tv1 == dst_tv2;

        var dst_val1 := get_reg_arith_val(s1, dst);
        var dst_val2 := get_reg_arith_val(s2, dst);

        assert {:split_here} dst_val1 == dst_val2;

        var new_val1 := compute_bin_arith(binop, dst_val1, src_imm);
        var new_val2 := compute_bin_arith(binop, dst_val2, src_imm);

        assert {:split_here} new_val1 == new_val2;

        var new_reg_tv1 := Scalar(Normal, new_val1);
        var new_reg_tv2 := Scalar(Normal, new_val2);

        assert {:split_here} new_reg_tv1 == new_reg_tv2;

        state_update_preserve_equal(s1, s2, dst, new_reg_tv1, new_reg_tv2);
    }

    lemma {:timeLimit 120} non_leakage_ADD64_reg(
        s1: State, s2: State, insn: Instruction
    )
    requires exists dst, src
            ::
            insn == ARITHBINREG(dst, src, ADD64)
    //
    requires !s1.cfg.allow_ptr_leak && !s2.cfg.allow_ptr_leak
    requires precond_sat(s1, insn)
    requires precond_sat(s2, insn)
    //
    requires same_low_sec_data(s1, s2)
    //
    ensures same_low_sec_data(
                exec_one_insn(s1, insn),
                exec_one_insn(s2, insn)
            )
    {
        var (dst, src) := (insn.dst, insn.src);
        var dst_tv1 := get_reg_typeval(s1, dst);
        var dst_tv2 := get_reg_typeval(s2, dst);
        var src_tv1 := get_reg_typeval(s1, src);
        var src_tv2 := get_reg_typeval(s2, src);

        var dst_arith1_val := get_reg_arith_val(s1, dst);
        var dst_arith2_val := get_reg_arith_val(s2, dst);
        var src_arith1_val := get_reg_arith_val(s1, src);
        var src_arith2_val := get_reg_arith_val(s2, src);
        
        assert {:split_here} (is_scalar(dst_tv1) || is_scalar(dst_tv2)) ==>
            dst_tv1 == dst_tv2;
        
        equal_reg(s1, s2, src);
        assert {:split_here} (is_scalar(src_tv1) || is_scalar(src_tv2)) ==> 
            src_tv1 == src_tv2;

        assert {:split_here}
            (is_ptr(dst_tv1) && is_scalar(src_tv1))
            ||
            (is_scalar(dst_tv1) && is_ptr(src_tv1))
            ||
            (is_scalar(dst_tv1) && is_scalar(src_tv1));

        assert {:split_here}
            (is_ptr(dst_tv2) && is_scalar(src_tv2))
            ||
            (is_scalar(dst_tv2) && is_ptr(src_tv2))
            ||
            (is_scalar(dst_tv2) && is_scalar(src_tv2));

        match (dst_tv1, src_tv1) {
            case (Scalar(_, val), PtrType(r, memid, off))  => 
            
                assert {:split_here} is_scalar(dst_tv1) && is_ptr(src_tv1);
                assert {:split_here} is_scalar(dst_tv2) && is_ptr(src_tv2);

                var new_reg_tv1 := PtrType(
                    r,
                    memid,
                    bvadd64(val, off)
                );

                var new_reg_tv2 := PtrType(
                    src_tv2.r,
                    src_tv2.memid,
                    bvadd64(dst_tv2.val, src_tv2.off)
                );

                assert {:split_here} ptr_or_ptrornull(new_reg_tv1);
                assert {:split_here} ptr_or_ptrornull(new_reg_tv2);
                assert {:split_here} true;
                state_update_preserve_equal(
                    s1, s2, dst, new_reg_tv1, new_reg_tv2
                );

            case (PtrType(r, memid, off), Scalar(_, val))  =>
            
                assert {:split_here} is_ptr(dst_tv1) && is_scalar(src_tv1);
                assert {:split_here} is_ptr(dst_tv2) && is_scalar(src_tv2);

                var new_reg_tv1 := PtrType(
                    r,
                    memid,
                    bvadd64(off, val)
                );

                var new_reg_tv2 := PtrType(
                    dst_tv2.r,
                    dst_tv2.memid,
                    bvadd64(dst_tv2.off, src_tv2.val)
                );

                assert {:split_here} ptr_or_ptrornull(new_reg_tv1);
                assert {:split_here} ptr_or_ptrornull(new_reg_tv2);
                assert {:split_here} true;
                state_update_preserve_equal(
                    s1, s2, dst, new_reg_tv1, new_reg_tv2
                );

            case _ =>
            
                assert {:split_here} is_scalar(dst_tv1) && is_scalar(src_tv1);
                assert {:split_here} is_scalar(dst_tv2) && is_scalar(src_tv2);
                assert {:split_here} dst_tv1 == dst_tv2;
                assert {:split_here} src_tv1 == src_tv2;

                var new_reg_tv1 := Scalar(
                    Normal,
                    bvadd64(dst_arith1_val, src_arith1_val)
                );

                var new_reg_tv2 := Scalar(
                    Normal,
                    bvadd64(dst_arith2_val, src_arith2_val)
                );

                assert {:split_here} new_reg_tv1 == new_reg_tv2;

                assert {:split_here} true;
                state_update_preserve_equal_on_scalars(
                    s1, s2, dst, new_reg_tv1
                );
        }
    }


    lemma {:timeLimit 120} non_leakage_ADD64_imm(
        s1: State, s2: State, insn: Instruction
    )
    requires exists dst, src_imm
            ::
            insn == ARITHBINIMM(dst, src_imm, ADD64)
    //
    requires !s1.cfg.allow_ptr_leak && !s2.cfg.allow_ptr_leak
    requires precond_sat(s1, insn)
    requires precond_sat(s2, insn)
    //
    requires same_low_sec_data(s1, s2)
    //
    ensures same_low_sec_data(
                exec_one_insn(s1, insn),
                exec_one_insn(s2, insn)
            )
    {
        var (dst, src_imm) := (insn.dst, insn.src_imm);
        var dst_tv1 := get_reg_typeval(s1, dst);
        var dst_tv2 := get_reg_typeval(s2, dst);

        var dst_arith1_val := get_reg_arith_val(s1, dst);
        var dst_arith2_val := get_reg_arith_val(s2, dst);
    
        var s1' := exec_one_insn(s1, insn);
        var s2' := exec_one_insn(s2, insn);
        
        assert {:split_here} (is_scalar(dst_tv1) || is_scalar(dst_tv2)) ==>
            dst_tv1 == dst_tv2;

        assert {:split_here} (is_ptr(dst_tv1) || is_scalar(dst_tv1));
        assert {:split_here} (is_ptr(dst_tv2) || is_scalar(dst_tv2));
        
        match dst_tv1 {
            
            case PtrType(r, memid, off)  => 
            
                assert {:split_here} is_ptr(dst_tv2);

                var new_reg_tv1 := PtrType(
                    r,
                    memid,
                    bvadd64(off, src_imm)   
                );

                var new_reg_tv2 := PtrType(
                    dst_tv2.r,
                    dst_tv2.memid,
                    bvadd64(dst_tv2.off, src_imm)
                );

                assert {:split_here} ptr_or_ptrornull(new_reg_tv1);
                assert {:split_here} ptr_or_ptrornull(new_reg_tv2);
                assert {:split_here} true;
                state_update_preserve_equal(
                    s1, s2, dst, new_reg_tv1, new_reg_tv2
                );

                assert {:split_here} same_low_sec_data(s1', s2');

            case _ =>
            
                assert {:split_here} is_scalar(dst_tv1);
                assert {:split_here} is_scalar(dst_tv2);
                assert {:split_here} dst_tv1 == dst_tv2;

                var new_reg_tv1 := Scalar(
                    Normal,
                    bvadd64(dst_arith1_val, src_imm)
                );

                var new_reg_tv2 := Scalar(
                    Normal,
                    bvadd64(dst_arith2_val, src_imm)
                );

                assert new_reg_tv1 == new_reg_tv2;

                assert {:split_here} is_scalar(new_reg_tv1);
                assert {:split_here} is_scalar(new_reg_tv2);
                assert {:split_here} true;
                state_update_preserve_equal(
                    s1, s2, dst, new_reg_tv1, new_reg_tv2
                );
                assert {:split_here} same_low_sec_data(s1', s2');
        }

        assert {:split_here} same_low_sec_data(s1', s2');
    }


    lemma {:timeLimit 120} non_leakage_SUB64_reg(
        s1: State, s2: State, insn: Instruction
    )
    requires exists dst, src :: insn == ARITHBINREG(dst, src, SUB64)
    //
    requires !s1.cfg.allow_ptr_leak && !s2.cfg.allow_ptr_leak
    requires precond_sat(s1, insn)
    requires precond_sat(s2, insn)
    //
    requires same_low_sec_data(s1, s2)
    requires declassfy_addr_base(s1, s2, insn)
    //
    ensures same_low_sec_data(
                exec_one_insn(s1, insn),
                exec_one_insn(s2, insn)
            )
    {
        var (dst, src) := (insn.dst, insn.src);
        var dst_tv1 := get_reg_typeval(s1, dst);
        var dst_tv2 := get_reg_typeval(s2, dst);
        var src_tv1 := get_reg_typeval(s1, src);
        var src_tv2 := get_reg_typeval(s2, src);

        var dst_arith1_val := get_reg_arith_val(s1, dst);
        var dst_arith2_val := get_reg_arith_val(s2, dst);
        var src_arith1_val := get_reg_arith_val(s1, src);
        var src_arith2_val := get_reg_arith_val(s2, src);
    
        var s1'' := exec_one_insn(s1, insn);
        var s2'' := exec_one_insn(s2, insn);
        
        assert {:split_here} (is_scalar(dst_tv1) || is_scalar(dst_tv2)) ==> 
            dst_tv1 == dst_tv2;
        equal_reg(s1, s2, src);
        assert {:split_here} (is_scalar(src_tv1) || is_scalar(src_tv2)) ==>
            src_tv1 == src_tv2;

        assert {:split_here}
            (is_ptr(dst_tv1) && is_scalar(src_tv1))
            ||
            (is_scalar(dst_tv1) && is_scalar(src_tv1))
            ||
            (
                is_ptr(dst_tv1) && is_ptr(src_tv1) &&
                same_mem_region(s1, dst, src)
            );

        assert {:split_here}
            (is_ptr(dst_tv2) && is_scalar(src_tv2))
            ||
            (is_scalar(dst_tv2) && is_scalar(src_tv2))
            ||
            (
                is_ptr(dst_tv2) && is_ptr(src_tv2) &&
                same_mem_region(s2, dst, src)
            );

        match (dst_tv1, src_tv1) {
            
            case (PtrType(r, memid, off), Scalar(_, val))  =>
            
                assert {:split_here} is_ptr(dst_tv1) && is_scalar(src_tv1);
                assert {:split_here} is_ptr(dst_tv2) && is_scalar(src_tv2);

                var new_reg_tv1 := PtrType(
                    r,
                    memid,
                    bvsub64(off, val)
                );

                var new_reg_tv2 := PtrType(
                    dst_tv2.r,
                    dst_tv2.memid,
                    bvsub64(dst_tv2.off, src_tv2.val)
                );

                assert {:split_here} is_ptr(new_reg_tv1);
                assert {:split_here} is_ptr(new_reg_tv2);
                assert {:split_here} true;
                state_update_preserve_equal(
                    s1, s2, dst, new_reg_tv1, new_reg_tv2
                );

                assert {:split_here} same_low_sec_data(s1'', s2'');

            case _ =>
            
                assert {:split_here} dst_tv1 == dst_tv2;
                assert {:split_here} src_tv1 == src_tv2;

                var new_reg_tv1 := Scalar(
                    Normal,
                    bvsub64(dst_arith1_val, src_arith1_val)
                );

                var new_reg_tv2 := Scalar(
                    Normal,
                    bvsub64(dst_arith2_val, src_arith2_val)
                );

                assert new_reg_tv1 == new_reg_tv2;

                assert {:split_here} is_scalar(new_reg_tv1);
                assert {:split_here} is_scalar(new_reg_tv2);
                assert {:split_here} true;
                state_update_preserve_equal(
                    s1, s2, dst, new_reg_tv1, new_reg_tv2
                );
                assert {:split_here} same_low_sec_data(s1'', s2'');
        }

        assert {:split_here} same_low_sec_data(s1'', s2'');
    }

    lemma {:timeLimit 120} non_leakage_SUB64_imm(
        s1: State, s2: State, insn: Instruction
    )
    requires exists dst, src_imm
            ::
            insn == ARITHBINIMM(dst, src_imm, SUB64)
    //
    requires !s1.cfg.allow_ptr_leak && !s2.cfg.allow_ptr_leak
    requires precond_sat(s1, insn)
    requires precond_sat(s2, insn)
    //
    requires same_low_sec_data(s1, s2)
    //
    ensures same_low_sec_data(
                exec_one_insn(s1, insn),
                exec_one_insn(s2, insn)
            )
    {
        var (dst, src_imm) := (insn.dst, insn.src_imm);
        var dst_tv1 := get_reg_typeval(s1, dst);
        var dst_tv2 := get_reg_typeval(s2, dst);

        var dst_arith1_val := get_reg_arith_val(s1, dst);
        var dst_arith2_val := get_reg_arith_val(s2, dst);
    
        var s1' := exec_one_insn(s1, insn);
        var s2' := exec_one_insn(s2, insn);
        
        assert {:split_here} (is_scalar(dst_tv1) || is_scalar(dst_tv2)) ==>
            dst_tv1 == dst_tv2;

        assert {:split_here} (is_ptr(dst_tv1) || is_scalar(dst_tv1));
        assert {:split_here} (is_ptr(dst_tv2) || is_scalar(dst_tv2));
        
        match dst_tv1 {
            
            case PtrType(r, memid, off)  => 
            
                assert {:split_here} is_ptr(dst_tv2);

                var new_reg_tv1 := PtrType(
                    r,
                    memid,
                    bvsub64(off, src_imm)   
                );

                var new_reg_tv2 := PtrType(
                    dst_tv2.r,
                    dst_tv2.memid,
                    bvsub64(dst_tv2.off, src_imm)
                );

                assert {:split_here} is_ptr(new_reg_tv1);
                assert {:split_here} is_ptr(new_reg_tv2);
                assert {:split_here} true;
                state_update_preserve_equal(
                    s1, s2, dst, new_reg_tv1, new_reg_tv2
                );

                assert {:split_here} same_low_sec_data(s1', s2');

            case _ =>
            
                assert {:split_here} is_scalar(dst_tv1);
                assert {:split_here} is_scalar(dst_tv2);
                assert {:split_here} dst_tv1 == dst_tv2;

                var new_reg_tv1 := Scalar(
                    Normal,
                    bvsub64(dst_arith1_val, src_imm)
                );

                var new_reg_tv2 := Scalar(
                    Normal,
                    bvsub64(dst_arith2_val, src_imm)
                );

                assert new_reg_tv1 == new_reg_tv2;

                assert {:split_here} is_scalar(new_reg_tv1);
                assert {:split_here} is_scalar(new_reg_tv2);
                assert {:split_here} true;
                state_update_preserve_equal(
                    s1, s2, dst, new_reg_tv1, new_reg_tv2
                );
                assert {:split_here} same_low_sec_data(s1', s2');
        }

        assert {:split_here} same_low_sec_data(s1', s2');
    }

    lemma equal_reg(s1: State, s2: State, reg: REG)
    requires same_low_sec_data(s1, s2)
    ensures (
                is_scalar(get_reg_typeval(s1, reg))
                ||
                is_scalar(get_reg_typeval(s2, reg))
            ) ==> get_reg_typeval(s1, reg) == get_reg_typeval(s2, reg)
    {}


    // ----------------------------------------------------------------
    //        Helper lemmas for non_leakage of data movement
    // ----------------------------------------------------------------

    lemma {:timeLimit 30} non_leakage_DATAMOVREG(
        s1: State, s2: State, insn: Instruction
    )
    requires exists dst, src, movrop :: insn == DATAMOVREG(dst, src, movrop)
    //
    requires !s1.cfg.allow_ptr_leak && !s2.cfg.allow_ptr_leak
    requires precond_sat(s1, insn)
    requires precond_sat(s2, insn)
    //
    requires same_low_sec_data(s1, s2)
    //
    ensures same_low_sec_data(
                exec_one_insn(s1, insn),
                exec_one_insn(s2, insn)
            )
    {
        var (dst, src, movrop) := (insn.dst, insn.src, insn.movrop);
        var src_tv1 := get_reg_typeval(s1, src);
        var src_tv2 := get_reg_typeval(s2, src);

        assert {:split_here} dst != R10;

        if movrop == MOV64 {
            if is_scalar(src_tv1) {
                assert {:split_here} is_scalar(src_tv2);
                assert src_tv1 == src_tv2;
                state_update_preserve_equal(s1, s2, dst, src_tv1, src_tv2);
                
            } else {
                assert {:split_here}
                    ptr_or_ptrornull(src_tv1) && ptr_or_ptrornull(src_tv2);
                state_update_preserve_equal(s1, s2, dst, src_tv1, src_tv2);
                
            }
        } else {
            assert {:split_here} is_scalar(src_tv1) && is_scalar(src_tv2);
            assert {:split_here}
                get_reg_arith_val(s1, src) == get_reg_arith_val(s2, src);

            assert {:split_here} true;
            var new_val1 := compute_new_dstval(
                movrop, get_reg_arith_val(s1, src)
            );
            
            var new_val2 := compute_new_dstval(
                movrop, get_reg_arith_val(s2, src)
            );

            assert {:split_here} new_val1 == new_val2;

            var new_tv1 := Scalar(Normal, new_val1);
            var new_tv2 := Scalar(Normal, new_val2);

            assert {:split_here}
                is_scalar(new_tv1) == is_scalar(new_tv2) && new_tv1 == new_tv2;
            
            state_update_preserve_equal_on_scalars(s1, s2, dst, new_tv1);
        }
    }


    lemma {:timeLimit 20} non_leakage_DATAMOVIMM(
        s1: State, s2: State, insn: Instruction
    )
    requires exists dst, src_imm, moviop
             :: insn == DATAMOVIMM(dst, src_imm, moviop)
    //
    requires !s1.cfg.allow_ptr_leak && !s2.cfg.allow_ptr_leak
    requires precond_sat(s1, insn)
    requires precond_sat(s2, insn)
    //
    requires same_low_sec_data(s1, s2)
    //
    ensures same_low_sec_data(
                exec_one_insn(s1, insn),
                exec_one_insn(s2, insn)
            )
    {}


    // ----------------------------------------------------------------
    //     Helper lemmas for non_leakage of control flow insns
    // ----------------------------------------------------------------


    lemma {:timeLimit 20} non_leakage_CONDJMPIMM(
        s1: State, s2: State, insn: Instruction
    )
    requires exists dst, src_imm, jmpop
             :: insn == CONDJMPIMM(dst, src_imm, jmpop)
    //
    requires !s1.cfg.allow_ptr_leak && !s2.cfg.allow_ptr_leak
    requires precond_sat(s1, insn)
    requires precond_sat(s2, insn)
    //
    requires same_low_sec_data(s1, s2)
    requires declassfy_cmp(s1, s2, insn)
    //
    ensures same_low_sec_data(
                exec_one_insn(s1, insn),
                exec_one_insn(s2, insn)
            )
    {
        var (dst, src_imm, jmpop) := (insn.dst, insn.src_imm, insn.jmpop);
        var dst_tv1 := get_reg_typeval(s1, dst);
        var dst_tv2 := get_reg_typeval(s2, dst);

        var dst_arithv1 := get_arith_val(s1, dst_tv1);
        var dst_arithv2 := get_arith_val(s2, dst_tv2);

        var dst_arithv1_u32 := low32(dst_arithv1);
        var dst_arithv2_u32 := low32(dst_arithv2);

        var src_arithv_u32 := low32(src_imm);

        assert {:split_here}
               (is_scalar(dst_tv1) && is_scalar(dst_tv2))
               ||
               (
                    ptr_or_ptrornull(dst_tv1)
                    &&
                    ptr_or_ptrornull(dst_tv2)
                    &&
                    src_imm == 0
                );
        
        assert {:split_here} dst_tv1 == dst_tv2;
        assert {:split_here} dst_arithv1 == dst_arithv2;
        assert {:split_here} dst_arithv1_u32 == dst_arithv2_u32;

        assert {:split_here} true;

        var jmp_res1 := compute_jmp_res(jmpop, dst_arithv1, src_imm);
        var jmp_res2 := compute_jmp_res(jmpop, dst_arithv2, src_imm);
        assert {:split_here} jmp_res1 == jmp_res2;

        var s1' := s1.(jmp_res := jmp_res1);
        var s2' := s2.(jmp_res := jmp_res2);

        assert {:split_here} same_low_sec_data(s1', s2');

        
        assert {:split_here}
            ptrornull(get_reg_typeval(s1', dst)) ==> dst != R10;
        
        assert {:split_here} true;
        adjust_regtv_for_nullness_imm_lemma(s1', s2', jmpop, dst, src_imm);
    }


    lemma {:timeLimit 10} adjust_regtv_for_nullness_imm_lemma(
        s1:State, s2:State, jmpop: JMPOP, dst:REG, src_imm:bv64
    )
    requires !s1.cfg.allow_ptr_leak && !s2.cfg.allow_ptr_leak
    //
    requires same_low_sec_data(s1, s2)
    requires (ptrornull(get_reg_typeval(s1, dst)) ==> dst != R10)
    requires get_reg_typeval(s1, dst) == get_reg_typeval(s2, dst)
    ensures var s1' := adjust_regtv_for_nullness_imm(s1, jmpop, dst, src_imm);
            var s2' := adjust_regtv_for_nullness_imm(s2, jmpop, dst, src_imm);
            same_low_sec_data(s1', s2')
    {}


    lemma {:timeLimit 60} adjust_regtv_for_nullness_reg_lemma(
        s1:State, s2:State, jmpop: JMPOP, dst:REG, src:REG
    )
    requires !s1.cfg.allow_ptr_leak && !s2.cfg.allow_ptr_leak
    //
    requires same_low_sec_data(s1, s2)
    requires get_reg_typeval(s1, dst) == get_reg_typeval(s2, dst)
    requires get_reg_typeval(s1, src) == get_reg_typeval(s2, src)
    //
    requires (ptrornull(get_reg_typeval(s1, dst)) ==> dst != R10)
    requires (ptrornull(get_reg_typeval(s1, src)) ==> src != R10)
    //
    ensures var s1' := adjust_regtv_for_nullness_reg(s1, jmpop, dst, src);
            var s2' := adjust_regtv_for_nullness_reg(s2, jmpop, dst, src);
            same_low_sec_data(s1', s2')
    {
        var s1' := adjust_regtv_for_nullness_reg(s1, jmpop, dst, src);
        var s2' := adjust_regtv_for_nullness_reg(s2, jmpop, dst, src);

        var dst_tv1 := get_reg_typeval(s1, dst);
        var src_tv1 := get_reg_typeval(s1, src);

        var dst_tv2 := get_reg_typeval(s2, dst);
        var src_tv2 := get_reg_typeval(s2, src);

        match jmpop {
            case JEQ64 =>
                // ptr_or_null == 0
                if (ptrornull(dst_tv1) && is_scalar_zero(src_tv1)) {
                    if s1.jmp_res {
                        state_update_preserve_equal(
                            s1, s2, dst, Scalar(Normal, 0), Scalar(Normal, 0)
                        );
                        assert {:split_here} same_low_sec_data(s1', s2');
                    } else {
                        state_update_preserve_equal(
                            s1, s2, dst,
                            ptrnull_to_ptr(dst_tv1),
                            ptrnull_to_ptr(dst_tv2)
                        );
                        assert {:split_here} same_low_sec_data(s1', s2');
                    }
                }
                //
                // 0 == ptr_or_null
                else if (is_scalar_zero(dst_tv1) && ptrornull(src_tv1)) {
                    if s1.jmp_res {
                        state_update_preserve_equal(
                            s1, s2, src, Scalar(Normal, 0), Scalar(Normal, 0)
                        );
                        assert {:split_here} same_low_sec_data(s1', s2');
                    } else {
                        state_update_preserve_equal(
                            s1, s2, src,
                            ptrnull_to_ptr(src_tv1),
                            ptrnull_to_ptr(src_tv2)
                        );
                        assert {:split_here} same_low_sec_data(s1', s2');
                    }
                }
                else {
                    assert {:split_here} same_low_sec_data(s1', s2');
                }

            case JNE64 =>
                // ptr_or_null != 0
                if (ptrornull(dst_tv1) && is_scalar_zero(src_tv1)) {
                    if s1.jmp_res {
                        state_update_preserve_equal(
                            s1, s2, dst,
                            ptrnull_to_ptr(dst_tv1),
                            ptrnull_to_ptr(dst_tv2)
                        );
                        assert {:split_here} same_low_sec_data(s1', s2');
                    } else {
                        state_update_preserve_equal(
                            s1, s2, dst, Scalar(Normal, 0), Scalar(Normal, 0)
                        );
                        assert {:split_here} same_low_sec_data(s1', s2');
                    }
                
                } else if (is_scalar_zero(dst_tv1) && ptrornull(src_tv1)) {
                    if s1.jmp_res {
                        state_update_preserve_equal(
                            s1, s2, src,
                            ptrnull_to_ptr(src_tv1),
                            ptrnull_to_ptr(src_tv2)
                        );
                        assert {:split_here} same_low_sec_data(s1', s2');
                    } else {
                        state_update_preserve_equal(
                            s1, s2, src, Scalar(Normal, 0), Scalar(Normal, 0)
                        );
                        assert {:split_here} same_low_sec_data(s1', s2');
                    }
                } else {

                    assert {:split_here} same_low_sec_data(s1', s2');
                }

            case _ => assert {:split_here} same_low_sec_data(s1', s2');
        }
    }


    lemma {:timeLimit 60} non_leakage_CONDJMPREG(
        s1: State, s2: State, insn: Instruction
    )
    requires exists dst, src, jmpop
             :: insn == CONDJMPREG(dst, src, jmpop)
    //
    requires !s1.cfg.allow_ptr_leak && !s2.cfg.allow_ptr_leak
    requires precond_sat(s1, insn)
    requires precond_sat(s2, insn)
    //
    requires same_low_sec_data(s1, s2)
    requires declassfy_cmp(s1, s2, insn)
    //
    ensures same_low_sec_data(
                exec_one_insn(s1, insn),
                exec_one_insn(s2, insn)
            )
    {
        var (dst, src, jmpop) := (insn.dst, insn.src, insn.jmpop);

        var dst_tv1 := get_reg_typeval(s1, dst);
        var src_tv1 := get_reg_typeval(s1, src);
        var dst_tv2 := get_reg_typeval(s2, dst);
        var src_tv2 := get_reg_typeval(s2, src);

        match jmpop {

            case JEQ64 | JNE64 => 
                assert {:split_here}
                (is_scalar(dst_tv1) && is_scalar(src_tv1) && is_scalar(dst_tv2) && is_scalar(src_tv2))
                ||
                (
                    ptr_or_ptrornull(dst_tv1) && ptr_or_ptrornull(src_tv1) && 
                    ptr_or_ptrornull(dst_tv2) && ptr_or_ptrornull(src_tv2)
                )
                ||
                (
                    ptr_or_ptrornull(dst_tv1) && is_scalar_zero(src_tv1) && 
                    ptr_or_ptrornull(dst_tv2) && is_scalar_zero(src_tv2)
                )
                ||
                (
                    is_scalar_zero(dst_tv1) && ptr_or_ptrornull(src_tv1) && 
                    is_scalar_zero(dst_tv2) && ptr_or_ptrornull(src_tv2)
                );
                
            case JGT64 | JGE64 | JSGT64 | JSGE64 |
                JLT64 | JLE64 | JSLT64 | JSLE64
                =>
                assert {:split_here}
                    (
                        is_scalar(dst_tv1) && is_scalar(src_tv1) &&
                        is_scalar(dst_tv2) && is_scalar(src_tv2)
                    )
                    ||
                    (
                        ptr_or_ptrornull(dst_tv1) &&
                        ptr_or_ptrornull(src_tv1) &&
                        ptr_or_ptrornull(dst_tv2) &&
                        ptr_or_ptrornull(src_tv2)
                    );
            
            case _ => assert {:split_here} (
                is_scalar(dst_tv1) && is_scalar(src_tv1) &&
                is_scalar(dst_tv2) && is_scalar(src_tv2)
            );
        }

        assert {:split_here} dst_tv1 == dst_tv2;
        assert {:split_here} src_tv1 == src_tv2;
        assert {:split_here} true;

        var dst_arithv1 := get_arith_val(s1, dst_tv1);
        var src_arithv1 := get_arith_val(s1, src_tv1);
        var dst_arithv2 := get_arith_val(s2, dst_tv2);
        var src_arithv2 := get_arith_val(s2, src_tv2);
        
        var jmp_res1 := compute_jmp_res(jmpop, dst_arithv1, src_arithv1);
        var jmp_res2 := compute_jmp_res(jmpop, dst_arithv2, src_arithv2);

        assert {:split_here} jmp_res1 == jmp_res2;

        var s1' := s1.(jmp_res := jmp_res1);
        var s2' := s2.(jmp_res := jmp_res2);

        assert {:split_here} s1.mems == s1'.mems;
        assert {:split_here} s2.mems == s2'.mems;

        assert {:split_here} same_low_sec_data(s1', s2');

        assert {:split_here} (ptrornull(dst_tv1) ==> dst != R10);
        assert {:split_here} (ptrornull(src_tv1) ==> src != R10);

        assert {:split_here} true;
        adjust_regtv_for_nullness_reg_lemma(s1', s2', jmpop, dst, src);
    }


    // ----------------------------------------------------------------
    //        Helper lemmas for non_leakage of memory insns
    // ----------------------------------------------------------------


    lemma {:timeLimit 5} non_leakage_MEMLD(
        s1: State, s2: State, insn: Instruction
    )
    requires exists dst, src, off, size, sign_ext
             :: insn == MEMLD(dst, src, off, size, sign_ext)
    //
    requires !s1.cfg.allow_ptr_leak && !s2.cfg.allow_ptr_leak
    requires precond_sat(s1, insn)
    requires precond_sat(s2, insn)
    //
    requires same_low_sec_data(s1, s2)
    requires declassfy_addr_base(s1, s2, insn)
    //
    ensures same_low_sec_data(
                exec_one_insn(s1, insn),
                exec_one_insn(s2, insn)
            )
    {
        var (dst, src, ioff, size, sign_ext) :=
            (insn.dst, insn.src, insn.ioff, insn.size, insn.sign_ext);

        var src_tv1 := get_reg_typeval(s1, src);
        var src_tv2 := get_reg_typeval(s2, src);
        assert {:split_here} src_tv1 == src_tv2;

        var rid := r2id(src_tv1.r);
        var memid := src_tv1.memid;

        assert {:split_here} true;
        var new_reg_tv1 :=
            read_n_byte_etypev(s1, src_tv1, ioff, size, sign_ext);
        assert {:split_here} true;
        var new_reg_tv2 :=
            read_n_byte_etypev(s2, src_tv2, ioff, size, sign_ext);

        assert {:split_here} true;
        read_n_byte_etypev_equiv(
            s1, s2, src_tv1, ioff, size, sign_ext
        );

        assert {:split_here} true;
        var new_reg_tv1' :=
            if s1.mems[rid][memid].is_concur
            then sim_concur_mem_val(s1, src, size)
            else new_reg_tv1;

        assert {:split_here} true;
        var new_reg_tv2' :=
            if s2.mems[rid][memid].is_concur
            then sim_concur_mem_val(s2, src, size)
            else new_reg_tv2;

        assert {:split_here} true;
        axiom_on_concur(s1, s2, src, size);

        assert {:split_here} true;
        state_update_preserve_equal(s1, s2, dst, new_reg_tv1', new_reg_tv2');
    }
    
    lemma {:timeLimit 30} non_leakage_MEMST_REG(
        s1: State, s2: State, insn: Instruction
    )
    requires exists dst, src, ioff, size ::
             insn == MEMSTX(dst, src, ioff, size)
    //
    requires !s1.cfg.allow_ptr_leak && !s2.cfg.allow_ptr_leak
    requires precond_sat(s1, insn)
    requires precond_sat(s2, insn)
    //
    requires same_low_sec_data(s1, s2)
    requires declassfy_addr_base(s1, s2, insn)
    //
    ensures same_low_sec_data(
                exec_one_insn(s1, insn),
                exec_one_insn(s2, insn)
            )
    {
        var (dst, src, ioff, size) := 
            (insn.dst, insn.src, insn.ioff, insn.size);
        
        var dst_tv1 := get_reg_typeval(s1, dst);
        var dst_tv2 := get_reg_typeval(s2, dst);
        assert {:split_here} dst_tv1 == dst_tv2;

        var src_tv1 := get_reg_typeval(s1, src);
        var src_tv2 := get_reg_typeval(s2, src);

        update_mem_preseves_low_sec_data(
            s1, s2, dst_tv1, ioff, size, src_tv1, src_tv2
        );
    }

    lemma {:timeLimit 60} non_leakage_MEMST_IMM(
        s1: State, s2: State, insn: Instruction
    )
    requires exists dst, src_imm, ioff, size ::
             insn == MEMST(dst, src_imm, ioff, size)
    //
    requires !s1.cfg.allow_ptr_leak && !s2.cfg.allow_ptr_leak
    requires precond_sat(s1, insn)
    requires precond_sat(s2, insn)
    //
    requires same_low_sec_data(s1, s2)
    requires declassfy_addr_base(s1, s2, insn)
    //
    ensures same_low_sec_data(
                exec_one_insn(s1, insn),
                exec_one_insn(s2, insn)
            )
    {
        var (dst, src_imm, ioff, size) := 
            (insn.dst, insn.src_imm, insn.ioff, insn.size);
        
        var dst_tv1 := get_reg_typeval(s1, dst);
        var dst_tv2 := get_reg_typeval(s2, dst);
        assert {:split_here} dst_tv1 == dst_tv2;

        update_mem_preseves_low_sec_data(
            s1, s2, dst_tv1, ioff, size,
            Scalar(Normal, src_imm),
            Scalar(Normal, src_imm)
        );
    }

    lemma {:timeLimit 80} non_leakage_MEMATOMIC(
        s1: State, s2: State, insn: Instruction
    )
    requires exists dst, src, ioff, size, op ::
             insn == ATOMICLS(dst, src, ioff, size, op)
    //
    requires !s1.cfg.allow_ptr_leak && !s2.cfg.allow_ptr_leak
    requires precond_sat(s1, insn) 
    requires precond_sat(s2, insn)
    //
    requires same_low_sec_data(s1, s2)
    requires declassfy_addr_base(s1, s2, insn)
    //
    ensures same_low_sec_data(
                exec_one_insn(s1, insn),
                exec_one_insn(s2, insn)
            )
    {
        var (dst, src, ioff, size, op) :=
            (insn.dst, insn.src, insn.ioff, insn.size, insn.op);

        var dst_tv1 := get_reg_typeval(s1, dst);
        var dst_tv2 := get_reg_typeval(s2, dst);

        assert {:split_here} dst_tv1 == dst_tv2;

        var (rid, memid, cur_off) := get_ptr_info(dst_tv1, ioff);
        var mem_type := s1.mems[rid][memid].mem_type;

        var src_tv1 := get_reg_typeval(s1, src);
        var src_tv2 := get_reg_typeval(s2, src);
 
        assert {:split_here} (
            is_scalar(src_tv1) && is_scalar(src_tv2)
            &&
            src_tv1 == src_tv2
        )
        || (
            ptr_or_ptrornull(src_tv1) && ptr_or_ptrornull(src_tv2)
        );

        assert {:split_here} true;
        var sim_slot_tv1 := sim_concur_mem_val(s1, dst, size);
        var sim_slot_tv2 := sim_concur_mem_val(s2, dst, size);
        assert {:split_here} true;
        axiom_on_concur(s1, s2, dst, size);
        assert {:split_here} sim_slot_tv1 == sim_slot_tv2;

        assert {:split_here} true;
        var src_arith_val1 := get_reg_arith_val(s1, src);
        var src_arith_val2 := get_reg_arith_val(s2, src);
    
        assert {:split_here} true;
        var store_val_tv1 :=
            cal_atomic_store_tv(s1, op, size, src, sim_slot_tv1);
        assert {:split_here} store_val_tv1 != Uninit;

        assert {:split_here} true;
        var store_val_tv2 :=
            cal_atomic_store_tv(s2, op, size, src, sim_slot_tv2);
        assert {:split_here} store_val_tv2 != Uninit;

        assert {:split_here} true;
        cal_atomic_store_tv_lemma(
            s1, s2, mem_type, op, size, src, sim_slot_tv1
        );

        assert {:split_here} true;
        var s1' := update_mem(s1, dst_tv1, ioff, size, store_val_tv1);
        assert {:split_here} true;
        var s2' := update_mem(s2, dst_tv2, ioff, size, store_val_tv2);

        assert {:split_here} true;
        update_mem_preseves_low_sec_data(
            s1, s2, dst_tv1, ioff, size, store_val_tv1, store_val_tv2
        );

        assert {:split_here} same_low_sec_data(s1', s2');

        match op {    
            case ATOMIC_FETCH_ADD | ATOMIC_FETCH_OR | ATOMIC_FETCH_AND |
                 ATOMIC_FETCH_XOR | ATOMIC_XCHG =>
                 // new_state_regonly(s1', src, sim_slot_tv1)
                 // new_state_regonly(s2', src, sim_slot_tv2)
                 assert {:split_here} true;
                 state_update_preserve_equal(
                    s1', s2', src, sim_slot_tv1, sim_slot_tv2
                 );

            case ATOMIC_CMPXCHG =>
                 // s1'.(R0 := sim_slot_tv1)
                 // s2'.(R0 := sim_slot_tv2)
                 assert {:split_here} true;
                 state_update_preserve_equal(
                    s1', s2', R0, sim_slot_tv1, sim_slot_tv2
                 );

            case _ =>
                assert {:split_here} same_low_sec_data(s1', s2');
        }
    }


    lemma {:timeLimit 5} read_n_byte_etypev_equiv(
        s1: State, s2: State, addr_tv: ETYPEV,
        ioff: s16, size: SIZE, sign_ext: bool
    )
    requires same_low_sec_data(s1, s2)
    requires !s1.cfg.allow_ptr_leak && !s2.cfg.allow_ptr_leak
    //
    requires is_ptr(addr_tv)
    requires valid_etypev_if_ptr(s1, addr_tv)
    requires valid_etypev_if_ptr(s2, addr_tv)
    requires access_mem_slots_valid(s1, addr_tv, ioff, size)
    requires access_mem_slots_valid(s2, addr_tv, ioff, size)
    requires slots_inited(s1, addr_tv, ioff, size)
    requires slots_inited(s2, addr_tv, ioff, size)
    requires var (rid, memid, cur_off) := get_ptr_info(addr_tv, ioff);
             // Initialized memory slots
             (
                forall i | cur_off <= i < cur_off + size_to_nat(size)
                ::
                s1.mems[rid][memid].data[i].etypev != Uninit
                &&
                s2.mems[rid][memid].data[i].etypev != Uninit
             )
             &&
             // No partial read of pointers if without priviledge
             (
                !s1.cfg.allow_ptr_leak && size != DW ==> 
                    forall i | cur_off <= i < cur_off + size_to_nat(size)
                    ::
                    is_scalar(s1.mems[rid][memid].data[i].etypev)
             )
             &&
             (
                !s2.cfg.allow_ptr_leak && size != DW ==> 
                    forall i | cur_off <= i < cur_off + size_to_nat(size)
                    ::
                    is_scalar(s2.mems[rid][memid].data[i].etypev)
             )
    //
    ensures var new_reg_tv1 :=
                read_n_byte_etypev(s1, addr_tv, ioff, size, sign_ext);
            var new_reg_tv2 :=
                read_n_byte_etypev(s2, addr_tv, ioff, size, sign_ext);
            //
            (
                is_scalar(new_reg_tv1)
                &&
                is_scalar(new_reg_tv2)
                &&
                new_reg_tv1 == new_reg_tv2
            )
            ||
            (
                ptr_or_ptrornull(new_reg_tv1)
                &&
                ptr_or_ptrornull(new_reg_tv2)
            )
    {
        var (rid, memid, cur_off) := get_ptr_info(addr_tv, ioff);

        assert {:split_here} true;
        var new_reg_tv1 :=
            read_n_byte_etypev(s1, addr_tv, ioff, size, sign_ext);
        
        assert {:split_here} true;
        var new_reg_tv2 :=
            read_n_byte_etypev(s2, addr_tv, ioff, size, sign_ext);

        var first_slot_tv1 := s1.mems[rid][memid].data[cur_off].etypev;
        var first_slot_tv2 := s2.mems[rid][memid].data[cur_off].etypev;
        
        assert {:split_here} true;
        if ptr_or_ptrornull(first_slot_tv1) {
            
            assert {:split_here} size == DW;
            assert {:split_here} ptr_or_ptrornull(new_reg_tv1);
            assert {:split_here} ptr_or_ptrornull(new_reg_tv2);

        } else {
            
            assert {:split_here} is_scalar(first_slot_tv1);
            assert {:split_here} is_scalar(first_slot_tv2);

            assert {:split_here} true;
            one_scalar_implies_8byte_scalar(s1, addr_tv, ioff, size);

            assert {:split_here} true;
            one_scalar_implies_8byte_scalar(s2, addr_tv, ioff, size);
            
            assert {:split_here} true;
            same_bytes_implies_same_loads(
                s1, s2, addr_tv, ioff, size, sign_ext
            );

            assert {:split_here} is_scalar(new_reg_tv1);
            assert {:split_here} is_scalar(new_reg_tv2);

            assert {:split_here} new_reg_tv1 == new_reg_tv2;
        }
    }


    lemma one_scalar_implies_8byte_scalar(
        s: State, addr_tv: ETYPEV, ioff: s16, size: SIZE
    )
    requires is_ptr(addr_tv) && valid_etypev_if_ptr(s, addr_tv)
    requires access_mem_slots_valid(s, addr_tv, ioff, size)
    requires var (rid, memid, cur_off) := get_ptr_info(addr_tv, ioff);
             is_scalar(s.mems[rid][memid].data[cur_off].etypev)
    requires var (rid, memid, cur_off) := get_ptr_info(addr_tv, ioff);
             forall i | cur_off <= i < cur_off + size_to_nat(size)
             :: s.mems[rid][memid].data[i].etypev != Uninit
    //
    ensures var (rid, memid, cur_off) := get_ptr_info(addr_tv, ioff);
            forall i | cur_off <= i < cur_off + size_to_nat(size)
            :: is_scalar(s.mems[rid][memid].data[i].etypev)
    {}

    lemma same_bytes_implies_same_loads(
        s1: State, s2: State,
        addr_tv: ETYPEV, ioff: s16, size: SIZE, sign_ext: bool
    )
    requires is_ptr(addr_tv)
    requires valid_etypev_if_ptr(s1, addr_tv)
    requires valid_etypev_if_ptr(s2, addr_tv)
    requires access_mem_slots_valid(s1, addr_tv, ioff, size)
    requires access_mem_slots_valid(s2, addr_tv, ioff, size)
    requires same_low_sec_data(s1, s2)
    requires var (rid, memid, cur_off) := get_ptr_info(addr_tv, ioff);
            forall i | cur_off <= i < cur_off + size_to_nat(size)
            ::
            is_scalar(s1.mems[rid][memid].data[i].etypev)
            ||
            is_scalar(s2.mems[rid][memid].data[i].etypev)
    //
    ensures var (rid, memid, cur_off) := get_ptr_info(addr_tv, ioff);
            forall i | cur_off <= i < cur_off + size_to_nat(size)
            ::
            s1.mems[rid][memid].data[i] == s2.mems[rid][memid].data[i]
    ensures var (rid, memid, cur_off) := get_ptr_info(addr_tv, ioff);
            read_n_byte_data(s1.mems[rid][memid].data, cur_off, size, sign_ext) 
            ==
            read_n_byte_data(s2.mems[rid][memid].data, cur_off, size, sign_ext)
    {}


    lemma {:timeLimit 30} cal_atomic_store_tv_lemma(
        s1: State, s2: State, mem_type: MEMTYPE,
        op: ATOMICOP, size: SIZE, src: REG, sim_slot_tv: ETYPEV
    )
    //
    requires same_low_sec_data(s1, s2)
    requires var src_tv := get_reg_typeval(s1, src);
             is_scalar(src_tv) && valid_etypev_if_ptr(s1, src_tv)
    //
    requires var src_tv := get_reg_typeval(s2, src);
             is_scalar(src_tv) && valid_etypev_if_ptr(s2, src_tv)
    //
    requires sim_slot_tv != Uninit
    requires valid_etypev_if_ptr(s1, sim_slot_tv)
    requires valid_etypev_if_ptr(s2, sim_slot_tv)
    requires (size != DW || mem_type == RAW) ==> (
                is_scalar(sim_slot_tv)
            )
    requires is_scalar(sim_slot_tv)
    //
    ensures var store_val_tv1 :=
                cal_atomic_store_tv(s1, op, size, src, sim_slot_tv);
            var store_val_tv2 :=
                cal_atomic_store_tv(s2, op, size, src, sim_slot_tv);
            //
            (
                (size != DW || mem_type == RAW) ==> (
                    is_scalar(store_val_tv1)
                    &&
                    is_scalar(store_val_tv2)
                )
            )
            &&
            (
                (
                    is_scalar(store_val_tv1)
                    &&
                    is_scalar(store_val_tv2)
                    &&
                    store_val_tv1 == store_val_tv2
                )
                || (
                    ptr_or_ptrornull(store_val_tv1)
                    &&
                    ptr_or_ptrornull(store_val_tv2)
                )
            )
    {
        var src_tv1 := get_reg_typeval(s1, src);
        var src_tv2 := get_reg_typeval(s2, src);

        assert {:split_here} (
            is_scalar(src_tv1) && is_scalar(src_tv2)
            &&
            src_tv1 == src_tv2
        )
        || (
            ptr_or_ptrornull(src_tv1) && ptr_or_ptrornull(src_tv2)
        );

        var src_arith_val1 := get_reg_arith_val(s1, src);
        var src_arith_val2 := get_reg_arith_val(s2, src);
        
        var kind1 := 
            match (sim_slot_tv, src_tv1) {
                case (Scalar(k1, _), Scalar(k2, _)) =>
                    if k1 == k2 then k1 else Normal
            case _ => Normal
        };

        var kind2 := 
            match (sim_slot_tv, src_tv2) {
                case (Scalar(k1, _), Scalar(k2, _)) =>
                    if k1 == k2 then k1 else Normal
            case _ => Normal
        };

        var store_val_tv1 :=
            cal_atomic_store_tv(s1, op, size, src, sim_slot_tv);
        var store_val_tv2 :=
            cal_atomic_store_tv(s2, op, size, src, sim_slot_tv);

        match op {
            case ATOMIC_ADD | ATOMIC_FETCH_ADD =>
                match (size, sim_slot_tv, src_tv1) {
                    
                    case (DW, Scalar(k1, v1), Scalar(k2, v2)) =>
                        // var new_tv :=
                        //     if k1==k2
                        //     then Scalar(k1, sim_arith_val + src_arith_val)
                        //     else Scalar(Normal, sim_arith_val + src_arith_val);
                        // assert {:split_here} sim_slot_tv1 == sim_slot_tv2
                        //     &&
                        //     src_tv1 == src_tv2;
                        assert {:split_here} (
                            is_scalar(store_val_tv1) && is_scalar(store_val_tv2)
                            &&
                            store_val_tv1 == store_val_tv2
                        );
                    
                    case (DW, Scalar(k3, v3), PtrType(r3, memid3, off3)) =>
                        // var new_tv := PtrType(r3, memid3, off3 + v3);
                        assert {:split_here}
                        ptr_or_ptrornull(store_val_tv1)
                        &&
                        ptr_or_ptrornull(store_val_tv2);
                    
                    case (DW, PtrType(r4, memid4, off4), Scalar(k4, v4)) =>
                        // var new_tv := PtrType(r4, memid4, off4 + v4);
                        assert {:split_here}
                        ptr_or_ptrornull(store_val_tv1)
                        &&
                        ptr_or_ptrornull(store_val_tv2);
                    
                    case (_, _, _) =>
                        // var new_tv := Scalar(Normal, sim_arith_val + src_arith_val);
                        assert {:split_here} is_scalar(sim_slot_tv) && is_scalar(src_tv1) && is_scalar(src_tv2);
                        assert {:split_here} src_arith_val1 == src_arith_val2;
                        assert {:split_here} (
                            is_scalar(store_val_tv1) && is_scalar(store_val_tv2)
                            &&
                            store_val_tv1 == store_val_tv2
                        );
                }
                
            case ATOMIC_OR  | ATOMIC_FETCH_OR  =>
                // var new_tv := Scalar(kind, sim_arith_val | src_arith_val);
                assert {:split_here} is_scalar(src_tv1) && is_scalar(src_tv2);
                assert {:split_here} src_tv1 == src_tv2;
                assert {:split_here} src_arith_val1 == src_arith_val2;
                assert {:split_here} kind1 == kind2;
                assert {:split_here} (
                    is_scalar(store_val_tv1) && is_scalar(store_val_tv2)
                    &&
                    store_val_tv1 == store_val_tv2
                );
            
            case ATOMIC_AND | ATOMIC_FETCH_AND =>
                // var new_tv := Scalar(kind, sim_arith_val & src_arith_val);
                assert {:split_here} (
                    is_scalar(store_val_tv1) && is_scalar(store_val_tv2)
                    &&
                    store_val_tv1 == store_val_tv2
                );
            
            case ATOMIC_XOR | ATOMIC_FETCH_XOR =>
                // var new_tv := Scalar(kind, sim_arith_val ^ src_arith_val);
                assert {:split_here} (
                    is_scalar(store_val_tv1) && is_scalar(store_val_tv2)
                    &&
                    store_val_tv1 == store_val_tv2
                );
            
            case ATOMIC_XCHG | ATOMIC_CMPXCHG    => 
                // src_tv
                assert {:split_here} (
                    is_scalar(store_val_tv1) && is_scalar(store_val_tv2)
                    &&
                    store_val_tv1 == store_val_tv2
                )
                || (
                    ptr_or_ptrornull(store_val_tv1)
                    &&
                    ptr_or_ptrornull(store_val_tv2)
                );
        }
    }

    lemma {:timeLimit 60} update_mem_preseves_low_sec_data(
        s1: State, s2: State,
        addr_tv: ETYPEV, ioff: s16, size:SIZE,
        src_tv1: ETYPEV, src_tv2: ETYPEV
    )
    //
    requires !s1.cfg.allow_ptr_leak && !s2.cfg.allow_ptr_leak
    requires same_low_sec_data(s1, s2)
    requires (is_scalar(src_tv1) || is_scalar(src_tv2)) ==> (
                 src_tv1 == src_tv2
             )
    //
    requires src_tv1 != Uninit
    requires valid_etypev_if_ptr(s1, src_tv1)
    requires src_tv2 != Uninit
    requires valid_etypev_if_ptr(s2, src_tv2)
    //
    requires is_ptr(addr_tv)
    requires valid_etypev_if_ptr(s1, addr_tv)
    requires valid_etypev_if_ptr(s2, addr_tv)
    requires access_mem_slots_valid(s1, addr_tv, ioff, size)
    requires access_mem_slots_valid(s2, addr_tv, ioff, size)
    //
    requires var (rid, memid, cur_off) := get_ptr_info(addr_tv, ioff);
             (size != DW || s1.mems[rid][memid].mem_type == RAW) ==> 
             is_scalar(src_tv1) && is_scalar(src_tv2)
    //
    requires var (rid, memid, cur_off) := get_ptr_info(addr_tv, ioff);
             forall i | cur_off <= i < cur_off + size_to_nat(size)
             ::
             s1.mems[rid][memid].data[i].field_perm == RDWR
             &&
             s2.mems[rid][memid].data[i].field_perm == RDWR
             &&
             (
                size != DW ==> (
                    !ptr_or_ptrornull(s1.mems[rid][memid].data[i].etypev)
                    &&
                    !ptr_or_ptrornull(s2.mems[rid][memid].data[i].etypev)
                )
             )
    //
    ensures same_low_sec_data(
                update_mem(s1, addr_tv, ioff, size, src_tv1),
                update_mem(s2, addr_tv, ioff, size, src_tv2)
            )
    {
        var src_arith_val1 := get_arith_val(s1, src_tv1);
        var src_arith_val2 := get_arith_val(s2, src_tv2);

        var (rid, memid, cur_off) := get_ptr_info(addr_tv, ioff);

        assert {:split_here} true;
        var data1 := s1.mems[rid][memid].data;
        var data2 := s2.mems[rid][memid].data;

        var mem_type1 := s1.mems[rid][memid].mem_type;
        var mem_type2 := s2.mems[rid][memid].mem_type;
        assert {:split_here} mem_type1 == mem_type2;

        var slot_tv1 := data1[cur_off].etypev;
        var slot_tv2 := data2[cur_off].etypev;

        assert {:split_here} true;
        var s1' := update_mem(s1, addr_tv, ioff, size, src_tv1);
        assert {:split_here} true;
        var s2' := update_mem(s2, addr_tv, ioff, size, src_tv2);
        assert {:split_here} true;

        if size == DW && mem_type1 != RAW {
            // 8-byte scalar or ptr
            
            var new_slots_tv1 := reg_to_8byte_data(s1, src_tv1);
            var new_slots_tv2 := reg_to_8byte_data(s2, src_tv2);
            assert {:split_here} |new_slots_tv1| == |new_slots_tv2| == 8;

            assert {:split_here} true;
                var new_data1 := update_mem_slots(
                    s1, mem_type1, data1, cur_off, size, new_slots_tv1
                );

            assert {:split_here} true;
                var new_data2 := update_mem_slots(
                    s2, mem_type2, data2, cur_off, size, new_slots_tv2
                );
            
            assert {:split_here} |data1| == |data2|;
            assert {:split_here} |new_data1| == |new_data2|;

            if is_scalar(src_tv1) {
                
                assert {:split_here} src_tv1 == src_tv2;    
                assert {:split_here} new_slots_tv1 == new_slots_tv2;
                assert {:split_here} same_low_sec_data(s1', s2');
                
            }
            else {
                assert {:split_here} 
                    forall i | 0 <= i < |new_slots_tv1|
                    ::
                    ptr_or_ptrornull(new_slots_tv1[i])
                    &&
                    ptr_or_ptrornull(new_slots_tv2[i]);
                
                assert {:split_here} same_low_sec_data(s1', s2');
            }

        } else if ptr_or_ptrornull(slot_tv1) && mem_type1 != RAW {
            // partial overwrite a pointer -> not allowed in unprivilege
            assert {:split_here} size == DW;
            assert false; 
        
        } else {
            // scalar
            var new_slot_kind1 :=
                if is_scalar(src_tv1) then src_tv1.kind else Normal;
            var slot_tv1 := data1[cur_off].etypev;
            var old_slot_kind1 :=
                if is_scalar(slot_tv1) then slot_tv1.kind else Normal;
            var kind1 :=
                if mem_type1 == STRUCT then old_slot_kind1 else new_slot_kind1;
            
            var new_slot_kind2 :=
                if is_scalar(src_tv2) then src_tv2.kind else Normal;
            var slot_tv2 := data2[cur_off].etypev;
            var old_slot_kind2 :=
                if is_scalar(slot_tv2) then slot_tv2.kind else Normal;
            var kind2 :=
                if mem_type2 == STRUCT then old_slot_kind2 else new_slot_kind2;

            assert {:split_here} kind1 == kind2;

            assert {:split_here} src_arith_val1 == src_arith_val2;

            assert {:split_here} true;
            var new_slots_tv1 := scalar_etypev_to_seq(
                Scalar(kind1, src_arith_val1),
                size_to_nat(size), 0
            );

            assert {:split_here} true;
            var new_slots_tv2 := scalar_etypev_to_seq(
                Scalar(kind2, src_arith_val2),
                size_to_nat(size), 0
            );

            assert {:split_here} new_slots_tv1 == new_slots_tv2;

            assert {:split_here} same_low_sec_data(s1', s2');
        }
    }

    lemma state_update_preserve_equal_on_scalars(
        s1: State, s2: State, dst: REG, new_reg_tv: ETYPEV
    )
    requires same_low_sec_data(s1, s2)
    requires dst != R10
    ensures var s1' := new_state_regonly(s1, dst, new_reg_tv);
            var s2' := new_state_regonly(s2, dst, new_reg_tv);
            same_low_sec_data(s1', s2')
    {}

    lemma state_update_preserve_equal(
        s1: State, s2: State, dst: REG,
        new_reg_tv1: ETYPEV, new_reg_tv2: ETYPEV
    )
    requires same_low_sec_data(s1, s2)
    requires dst != R10
    requires (
        (
            ptr_or_ptrornull(new_reg_tv1)
            &&
            ptr_or_ptrornull(new_reg_tv2)
        )
        ||
        (
            is_scalar(new_reg_tv1)
            &&
            is_scalar(new_reg_tv2)
            &&
            new_reg_tv1 == new_reg_tv2
        )
    )
    ensures var s1' := new_state_regonly(s1, dst, new_reg_tv1);
            var s2' := new_state_regonly(s2, dst, new_reg_tv2);
            same_low_sec_data(s1', s2')
    {}


    /*
    lemma read_same_data(
        data1: seq<MemSlot>, data2: seq<MemSlot>,
        cur_off: int, size: SIZE, sign_ext: bool
    )
    requires 0 <= cur_off < cur_off + size_to_nat(size) <= |data1|
    requires 0 <= cur_off < cur_off + size_to_nat(size) <= |data2|
    requires forall i | 0 <= cur_off <= i < cur_off + size_to_nat(size)
             ::
             data1[i].etypev != Uninit
             &&
             data2[i].etypev != Uninit
             &&
             data1[i] == data2[i]
    ensures read_n_byte_data(data1, cur_off, size, sign_ext) ==
            read_n_byte_data(data2, cur_off, size, sign_ext)
    {}

    lemma signext_byte_nto8_equiv(val1: bv64, val2: bv64, size: SIZE)
    requires val1 == val2
    ensures signext_byte_nto8(val1, size) == signext_byte_nto8(val2, size)
    {}

    lemma scalar_etypev_to_seq_lemma()
    ensures forall x,y,size |
            x == y
            &&
            is_scalar(x)
            &&
            is_scalar(y)
            ::
            scalar_etypev_to_seq(x, size_to_nat(size), 0)
            ==
            scalar_etypev_to_seq(y, size_to_nat(size), 0)
    {}
    */

        /*
        assert {:split_here} !s1.cfg.allow_ptr_leak && !s2.cfg.allow_ptr_leak;
        assert {:split_here} same_low_sec_data(s1, s2);
        assert {:split_here}
            (is_scalar(store_val_tv1) || is_scalar(store_val_tv2)) ==> (
                store_val_tv1 == store_val_tv2
            );
        
        assert {:split_here} store_val_tv1 != Uninit;
        assert {:split_here} valid_etypev_if_ptr(s1, store_val_tv1);
        assert {:split_here} store_val_tv2 != Uninit;
        assert {:split_here} valid_etypev_if_ptr(s2, store_val_tv2);
        //
        assert {:split_here} is_ptr(dst_tv1);
        assert {:split_here} valid_etypev_if_ptr(s1, dst_tv1);
        assert {:split_here} valid_etypev_if_ptr(s2, dst_tv2);
        assert {:split_here} access_slots_valid(s1, dst_tv1, ioff, size);
        assert {:split_here} access_slots_valid(s2, dst_tv2, ioff, size);
        */
}
