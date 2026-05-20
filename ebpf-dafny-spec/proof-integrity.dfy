include "proof-utils.dfy"

module IntgerityProof {

    import opened Terms
    import opened DataTypes
    import opened States
    import opened Utils
    import opened eBPFMemSpec
    import opened ProofUtils

    // ----------------------------------------------------------------
    //               Definition of eBPF (reg/mem) data integrity
    // ----------------------------------------------------------------

    lemma {:timeLimit 300} preserve_integrity(s: State, insn: Instruction)
    requires precond_sat(s, insn)
    //
    ensures var s' := exec_one_insn(s, insn);
            //
            // Read-only register R10 keeps unchanged
            s.R10 == s'.R10
            &&
            //
            // Memory with coarse-grained perm:
            // Read-only/inaccessible memory keeps unchanged or delete
            // coarse_grained_integrity_preserves(s, s')
            // &&
            //
            // Memory with fine-grained perm:
            // If exists in s', read-only/inaccessible slots keeps unchanged
            fine_grained_integrity_preserves(s, s')
    {
        var s' := exec_one_insn(s, insn);

        match insn {

            case MEMSTX(dst, src, off, size) =>
                fine_grained_integrity_on_store_reg(s, insn);
                // assert {:split_here} fine_grained_integrity_preserves(s, s');
            
            case MEMST(dst, src_imm, off, size) =>
                fine_grained_integrity_on_imm_reg(s, insn);
                // assert {:split_here} fine_grained_integrity_preserves(s, s');
            
            case ATOMICLS(dst, src, off, size, op) =>
                fine_grained_integrity_on_atomicls(s, insn);
                assert {:split_here} fine_grained_integrity_preserves(s, s');

            case _ =>
                assert {:split_here} s.mems == s'.mems;
                assert {:split_here} fine_grained_integrity_preserves(s, s');

        }

        assert {:split_here} fine_grained_integrity_preserves(s, s');
    }

    /*
    predicate coarse_grained_integrity_preserves(s: State, s': State)
    {
        forall rid, memid |
            0 <= rid < |s.mems| && 0 <= memid < |s.mems[rid]|
            &&
            |s.mems| <= |s'.mems| && (|s.mems[rid]| <= |s'.mems[rid]|)
            ::
            s.mems[rid][memid].mem_perm != RDWR ==> (
                s.mems[rid][memid] == s'.mems[rid][memid]
                ||
                |s.mems[rid][memid].data| == 0
            )
    }
    */

    predicate fine_grained_integrity_preserves(s: State, s': State)
    {
        forall rid, memid, j |
            0 <= rid < |s.mems| && 0 <= memid < |s.mems[rid]|
            &&
            |s.mems| <= |s'.mems| && (|s.mems[rid]| <= |s'.mems[rid]|)
            &&
            (|s.mems[rid][memid].data| == |s'.mems[rid][memid].data| != 0)
            &&
            0 <= j < |s.mems[rid][memid].data|
            ::
            (
                var data := s.mems[rid][memid].data;
                var data' := s'.mems[rid][memid].data;

                data[j].field_perm != RDWR ==> (
                    data[j] == data'[j]
                )
                /*
                s.mems[rid][memid].mem_perm == RDWR
                ==> (
                    data[j].field_perm != RDWR ==> (
                        data[j] == data'[j]
                    )
                )
                */
            )
    }


    // ----------------------------------------------------------------
    //               Helper lemmas on complex cases
    // ----------------------------------------------------------------

    lemma {:timeLimit 180} fine_grained_integrity_on_store_reg(s: State, insn:Instruction)
    requires mem_store_reg_precond(s, insn)
    ensures var s' := mem_store_reg(s, insn);
            fine_grained_integrity_preserves(s, s')
    {}
 

    lemma {:timeLimit 300} fine_grained_integrity_on_imm_reg(s: State, insn:Instruction)
    requires mem_store_imm_precond(s, insn)
    ensures var s' := mem_store_imm(s, insn);
            fine_grained_integrity_preserves(s, s')
    {}

    lemma {:timeLimit 300} fine_grained_integrity_on_atomicls(s: State, insn:Instruction)
    requires mem_atomic_precond(s, insn)
    ensures var s' := mem_atomic(s, insn);
            fine_grained_integrity_preserves(s, s')
    {}
}
