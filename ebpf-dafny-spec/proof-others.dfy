include "proof-utils.dfy"
include "../spec/mem-init.dfy"

module propertyProof {

    import opened Terms
    import opened DataTypes
    import opened States
    import opened MemInit
    import opened Utils
    import opened ProofUtils

    import opened eBPFArithSpec
    import opened eBPFDataMoveSpec
    import opened eBPFCtrlFlowSpec
    import opened eBPFMemSpec

    // ------------------------------------------------------------------------
    //     Semantic correctness : memory operations keeps mem invariants
    // ------------------------------------------------------------------------

    lemma mem_load_lemma(s: State, insn: Instruction)
    requires mem_load_precond(s, insn)
    ensures var s' := mem_load(s, insn);
            mem_inv(s')
    {}

    lemma mem_store_reg_lemma(s: State, insn: Instruction)
    requires mem_store_reg_precond(s, insn)
    ensures var s' := mem_store_reg(s, insn);
            mem_inv(s')
    {
        var s' := mem_store_reg(s, insn);

        assert {:split_here} forall reg
        ::
        get_reg_typeval(s, reg) == get_reg_typeval(s', reg);
    }

    lemma mem_store_imm_lemma(s: State, insn: Instruction)
    requires mem_store_imm_precond(s, insn)
    ensures var s' := mem_store_imm(s, insn);
            mem_inv(s')
    {
        var s' := mem_store_imm(s, insn);
        assert {:split_here} forall reg
        ::
        get_reg_typeval(s, reg) == get_reg_typeval(s', reg);
    }

    lemma mem_atomic_lemma(s: State, insn: Instruction)
    requires mem_atomic_precond(s, insn)
    ensures var s' := mem_atomic(s, insn);
            mem_inv(s')
    {
        var s' := mem_atomic(s, insn);
        
        assert {:split_here} forall reg | reg != insn.src && reg != R0
        ::
        get_reg_typeval(s, reg) == get_reg_typeval(s', reg);

        assert {:split_here}
        (
            // Memory region size
            forall i, j | 0 <= i < |s'.mems| && 0 <= j < |s'.mems[i]| ::
                if i == r2id(PTR_TO_PACKET_END)
                then 0 == |s'.mems[i][j].data|
                else 0 <= |s'.mems[i][j].data| < 0x8000_0000_0000_0000
        )
        &&
        (
            // Valid pointer reg
            forall reg :: valid_etypev_if_ptr(s', get_reg_typeval(s', reg))
        );
    }


    // ------------------------------------------------------------------------
    //     Semantic correctness : initial state are valid
    // ------------------------------------------------------------------------

    lemma init_state_satisifies_insn_preconds(
        cfg: ConfigState, rand: bv64
    )
    ensures var init_s := init_state(cfg, rand);
            mem_inv(init_s)
    ensures var init_s := init_state(cfg, rand);
            forall r, memid, cur_off |
            0 <= memid < |init_s.mems[r2id(r)]|
            &&
            0 <= cur_off < (|init_s.mems[r2id(r)]|-1)
            ::
            var mem := init_s.mems[r2id(r)][memid];
            access_slots_valid(
                init_s,
                mem.mem_type,
                mem.data,
                cur_off,
                B
            )
    {}


    // ------------------------------------------------------------------------
    //     Semantic correctness : store_then_load_same_data on private mem
    // ------------------------------------------------------------------------

    lemma {:timeLimit 20} store_then_load_same_data_v1(
        s: State, st_insn: Instruction, ld_insn: Instruction
    )
    requires exists dst, src, off, size ::
             st_insn == MEMSTX(dst, src, off, size)
             &&
             ld_insn == MEMLD(src, dst, off, size, unknown_bool())
             &&
             src != R10
    //
    requires s.cfg.allow_ptr_leak
    requires mem_store_reg_precond(s, st_insn)
    // requires var dst := st_insn.dst;
    //          var regtv := get_reg_typeval(s, dst);
    //          var rid := r2id(regtv.r);
    //          var memid := regtv.memid;
    //          !s.mems[rid][memid].is_concur
    {
        var (dst, src, off, size) :=
            (st_insn.dst, st_insn.src, st_insn.ioff, st_insn.size);

        assert {:split_here} true;
        var s1 := mem_store_reg(s, st_insn);

        assert {:split_here} get_reg_typeval(s, dst) == get_reg_typeval(s1, dst);
        
        assert {:split_here} mem_inv(s1);
        




        // assert {:split_here} true;
        // var s2 := mem_load(s1, ld_insn);
        // assert {:split_here} true;

        /*
        var (dst, src, off, size) := (st_insn.dst, st_insn.src, st_insn.off, st_insn.size);

        var dst_tv := get_reg_typeval(s, dst);
        var src_tv := get_reg_typeval(s, src);
        var src_arithv := get_arith_val(s, src_tv);

        var rid := r2id(dst_tv.r);
        var memid := dst_tv.memid;

        var cur_off := 
            if dst_tv.r == PTR_TO_STACK
            then bv64ToInt64(dst_tv.off) + off
            else bv64ToInt64(dst_tv.off) + off + 512;

        var data := s.mems[rid][memid].data;
        var slot_tv := data[cur_off].etypev;
        var sizen := size_to_nat(size);

        
        assert {:split_here} true;
        var s1 := mem_store_reg(s, st_insn);
        assert {:split_here} true;
        var s2 := mem_load(s1, ld_insn);
        assert {:split_here} true;

        if size == DW {
            assert {:split_here} true;

            assert {:split_here} valid_etypev_if_ptr(s, src_tv);
            var new_slots_tv := reg_to_8byte_data(src_tv);

            var new_data := update_mem_slots(data, cur_off, size, new_slots_tv);

            // assert {:split_here} new_data[cur_off+0].field_perm == data[cur_off+0].field_perm;
            // assert {:split_here} new_data[cur_off+1].field_perm == data[cur_off+1].field_perm;
            // assert {:split_here} new_data[cur_off+2].field_perm == data[cur_off+2].field_perm;
            // assert {:split_here} new_data[cur_off+3].field_perm == data[cur_off+3].field_perm;
            // assert {:split_here} new_data[cur_off+4].field_perm == data[cur_off+4].field_perm;
            // assert {:split_here} new_data[cur_off+5].field_perm == data[cur_off+5].field_perm;
            // assert {:split_here} new_data[cur_off+6].field_perm == data[cur_off+6].field_perm;
            // assert {:split_here} new_data[cur_off+7].field_perm == data[cur_off+7].field_perm;

            // !!!!!!!
            assert {:split_here} valid_ptr_slots(s, s.mems[rid][memid].mem_type, new_data, cur_off, size);
            // !!!!!!!

            assert {:split_here} true;
            var s1' := update_a_mem_in_state(s, dst_tv.r, memid, new_data);
            assert {:split_here} s1' == s1;

            //
            assert {:split_here} forall i | cur_off <= i < cur_off + size_to_nat(size) ::
                        s1'.mems[rid][memid].data[i].etypev != Uninit;
            assert {:split_here} valid_ptr_slots(s1', s1'.mems[rid][memid].mem_type, s1'.mems[rid][memid].data, cur_off, size);
            //


            assert {:split_here} true;
            var new_reg_tv := read_n_byte_etypev(s1', dst_tv.r, memid, cur_off, size);

            assert {:split_here} new_reg_tv == src_tv;

            assert {:split_here} new_reg_tv == get_reg_typeval(s2, src);
        
        }
        else {
            /*
            assert {:split_here} true;
            var new_slot_kind := if is_scalar(src_tv) then src_tv.kind else Normal;
            var new_slots_tv := scalar_etypev_to_seq(Scalar(new_slot_kind, src_arithv), size_to_nat(size), 0);

            assert {:split_here} forall i | 0 <= i < size_to_nat(size) :: 
                get_nth_byte(src_arithv, i) == new_slots_tv[i].val;

            assert {:split_here} true;
            // var new_data1 := update_mem(s, rid, memid, cur_off, size, src_tv);
            var new_data := update_mem_slots(data, cur_off, size, new_slots_tv);

            assert {:split_here} forall i | 0 <= i < size_to_nat(size) ::
                new_data[cur_off+i].etypev == new_slots_tv[i];

            assert {:split_here} forall i | cur_off <= i < cur_off+size_to_nat(size) ::
                new_data1[i].etypev == new_data[i].etypev;

            assert {:split_here} true;
            var s' := update_a_mem_in_state(s, dst_tv.r, memid, new_data1);    
            
            assert {:split_here} forall i | cur_off <= i < cur_off + size_to_nat(size) ::
            s'.mems[rid][memid].data[i].etypev == new_data1[i].etypev;

            var new_reg_tv := read_n_byte_etypev(s', dst_tv.r, memid, cur_off, size);    
            
            assert {:split_here} new_reg_tv.val == src_arithv;
            */
        }
        */
    }

    /*
    lemma bytes_equal_so_bv64_equal(val: bv64, reg_tv: ETYPEV)
    requires reg_tv != Uninit
    // requires forall i | 0 <= i < 8 :: get_nth_byte(val, i) == get_nth_byte(val2, i)
    requires get_nth_byte(val, 0) == get_nth_byte(etypev_2_val(reg_tv), 0)
    requires get_nth_byte(val, 1) == get_nth_byte(etypev_2_val(reg_tv), 1)
    requires get_nth_byte(val, 2) == get_nth_byte(etypev_2_val(reg_tv), 2)
    requires get_nth_byte(val, 3) == get_nth_byte(etypev_2_val(reg_tv), 3)
    requires get_nth_byte(val, 4) == get_nth_byte(etypev_2_val(reg_tv), 4)
    requires get_nth_byte(val, 5) == get_nth_byte(etypev_2_val(reg_tv), 5)
    requires get_nth_byte(val, 6) == get_nth_byte(etypev_2_val(reg_tv), 6)
    requires get_nth_byte(val, 7) == get_nth_byte(etypev_2_val(reg_tv), 7)
    ensures val == etypev_2_val(reg_tv)
    {}
    */

























    /*
        lemma {:timeLimit 120} update_mem_lemma_v1(s: State, insn: Instruction)
    requires mem_store_reg_precond(s, insn)
    // ensures var s' := mem_store_reg(s, insn);
    //         var (dst, src, off, size) := (insn.dst, insn.src, insn.off, insn.size);
    //         var dst_tv := get_reg_typeval(s, dst);
    //         var src_tv := get_reg_typeval(s, src);
    //         var src_arithv := get_arith_val(s, src_tv);
    //         var rid := r2id(dst_tv.r);
    //         var memid := dst_tv.memid;
    //         var cur_off := 
    //             if dst_tv.r == PTR_TO_STACK
    //             then bv64ToInt64(dst_tv.off) + off
    //             else bv64ToInt64(dst_tv.off) + off + 512;
    //         //
    //         var reread := read_n_byte_data(s'.mems[rid][memid].data, cur_off, size);
    //         if size == DW
    //         then reread == etypev_2_val(src_tv)
    //         else forall i | 0 <= i < size_to_nat(size)
    //              :: 
    //              get_nth_byte(src_arithv, i) == get_nth_byte(reread, i)
    {

        var (dst, src, off, size) := (insn.dst, insn.src, insn.off, insn.size);

        var dst_tv := get_reg_typeval(s, dst);
        var src_tv := get_reg_typeval(s, src);
        var src_arithv := get_arith_val(s, src_tv);

        var rid := r2id(dst_tv.r);
        var memid := dst_tv.memid;

        var cur_off := 
            if dst_tv.r == PTR_TO_STACK
            then bv64ToInt64(dst_tv.off) + off
            else bv64ToInt64(dst_tv.off) + off + 512;

        var data := s.mems[rid][memid].data;
        var slot_tv := data[cur_off].etypev;
        var sizen := size_to_nat(size);

        
        assert {:split_here} true;
        var new_data1 := update_mem(s, rid, memid, cur_off, size, src_tv);
        assert {:split_here} true;
        // var reread1 := read_n_byte_data(new_data1, cur_off, size);
        // assert {:split_here} true;

        if size == DW {
            assert {:split_here} true;

            var new_slots_tv := reg_to_8byte_data(src_tv);

            assert {:split_here} get_nth_byte(etypev_2_val(src_tv), 0) == (etypev_2_val(new_slots_tv[0]));
            assert {:split_here} get_nth_byte(etypev_2_val(src_tv), 1) == (etypev_2_val(new_slots_tv[1]));
            assert {:split_here} get_nth_byte(etypev_2_val(src_tv), 2) == (etypev_2_val(new_slots_tv[2]));
            assert {:split_here} get_nth_byte(etypev_2_val(src_tv), 3) == (etypev_2_val(new_slots_tv[3]));
            assert {:split_here} get_nth_byte(etypev_2_val(src_tv), 4) == (etypev_2_val(new_slots_tv[4]));
            assert {:split_here} get_nth_byte(etypev_2_val(src_tv), 5) == (etypev_2_val(new_slots_tv[5]));
            assert {:split_here} get_nth_byte(etypev_2_val(src_tv), 6) == (etypev_2_val(new_slots_tv[6]));
            assert {:split_here} get_nth_byte(etypev_2_val(src_tv), 7) == (etypev_2_val(new_slots_tv[7]));

            assert {:split_here} valid_ptr_slots(s, s.mems[rid][memid].mem_type, data, cur_off, size);

            var new_data := update_mem_slots(data, cur_off, size, new_slots_tv);
            assert {:split_here} new_data[cur_off+0].etypev == new_slots_tv[0];
            assert {:split_here} new_data[cur_off+1].etypev == new_slots_tv[1];
            assert {:split_here} new_data[cur_off+2].etypev == new_slots_tv[2];
            assert {:split_here} new_data[cur_off+3].etypev == new_slots_tv[3];
            assert {:split_here} new_data[cur_off+4].etypev == new_slots_tv[4];
            assert {:split_here} new_data[cur_off+5].etypev == new_slots_tv[5];
            assert {:split_here} new_data[cur_off+6].etypev == new_slots_tv[6];
            assert {:split_here} new_data[cur_off+7].etypev == new_slots_tv[7];
    
            assert {:split_here} new_data1 == new_data;

            assert {:split_here} new_data[cur_off+0].field_perm == data[cur_off+0].field_perm;
            assert {:split_here} new_data[cur_off+1].field_perm == data[cur_off+1].field_perm;
            assert {:split_here} new_data[cur_off+2].field_perm == data[cur_off+2].field_perm;
            assert {:split_here} new_data[cur_off+3].field_perm == data[cur_off+3].field_perm;
            assert {:split_here} new_data[cur_off+4].field_perm == data[cur_off+4].field_perm;
            assert {:split_here} new_data[cur_off+5].field_perm == data[cur_off+5].field_perm;
            assert {:split_here} new_data[cur_off+6].field_perm == data[cur_off+6].field_perm;
            assert {:split_here} new_data[cur_off+7].field_perm == data[cur_off+7].field_perm;

            assert {:split_here} true;
            var reread_data := read_n_byte_data(new_data, cur_off, size);
            assert {:split_here} get_nth_byte(reread_data, 0) == (etypev_2_val(new_data[cur_off+0].etypev));
            assert {:split_here} get_nth_byte(reread_data, 1) == (etypev_2_val(new_data[cur_off+1].etypev));
            assert {:split_here} get_nth_byte(reread_data, 2) == (etypev_2_val(new_data[cur_off+2].etypev));
            assert {:split_here} get_nth_byte(reread_data, 3) == (etypev_2_val(new_data[cur_off+3].etypev));
            assert {:split_here} get_nth_byte(reread_data, 4) == (etypev_2_val(new_data[cur_off+4].etypev));
            assert {:split_here} get_nth_byte(reread_data, 5) == (etypev_2_val(new_data[cur_off+5].etypev));
            assert {:split_here} get_nth_byte(reread_data, 6) == (etypev_2_val(new_data[cur_off+6].etypev));
            assert {:split_here} get_nth_byte(reread_data, 7) == (etypev_2_val(new_data[cur_off+7].etypev));
            // assert {:split_here} reread_data == reread1;

            assert {:split_here} get_nth_byte(reread_data, 0) == get_nth_byte(etypev_2_val(src_tv), 0);
            assert {:split_here} get_nth_byte(reread_data, 1) == get_nth_byte(etypev_2_val(src_tv), 1);
            assert {:split_here} get_nth_byte(reread_data, 2) == get_nth_byte(etypev_2_val(src_tv), 2);
            assert {:split_here} get_nth_byte(reread_data, 3) == get_nth_byte(etypev_2_val(src_tv), 3);
            assert {:split_here} get_nth_byte(reread_data, 4) == get_nth_byte(etypev_2_val(src_tv), 4);
            assert {:split_here} get_nth_byte(reread_data, 5) == get_nth_byte(etypev_2_val(src_tv), 5);
            assert {:split_here} get_nth_byte(reread_data, 6) == get_nth_byte(etypev_2_val(src_tv), 6);
            assert {:split_here} get_nth_byte(reread_data, 7) == get_nth_byte(etypev_2_val(src_tv), 7);

            bytes_equal_so_bv64_equal(reread_data, src_tv);
            
            assert {:split_here} reread_data == etypev_2_val(src_tv);
            // assert {:split_here} reread1 == etypev_2_val(src_tv);
            
        }
        else {
            assert {:split_here} true;
            var new_slot_kind := if is_scalar(src_tv) then src_tv.kind else Normal;
            var new_slots_tv := scalar_etypev_to_seq(Scalar(new_slot_kind, src_arithv), size_to_nat(size), 0);

            assert {:split_here} forall i | 0 <= i < size_to_nat(size) :: 
                get_nth_byte(src_arithv, i) == new_slots_tv[i].val;

            assert {:split_here} true;
            // var new_data1 := update_mem(s, rid, memid, cur_off, size, src_tv);
            var new_data := update_mem_slots(data, cur_off, size, new_slots_tv);

            assert {:split_here} forall i | 0 <= i < size_to_nat(size) ::
                new_data[cur_off+i].etypev == new_slots_tv[i];

            assert {:split_here} forall i | cur_off <= i < cur_off+size_to_nat(size) ::
                new_data1[i].etypev == new_data[i].etypev;

            assert {:split_here} true;
            var reread_data := read_n_byte_data(new_data, cur_off, size);
            
            // lemma
            read_n_byte_data_inv(new_data, cur_off, size);

            assert {:split_here} forall i | 0 <= i < size_to_nat(size) ::
                get_nth_byte(reread_data, i) == (etypev_2_val(new_data[cur_off+i].etypev) & 0xff);
            
            // assert {:split_here} reread_data == reread1;

            assert {:split_here} forall i | 0 <= i < size_to_nat(size) :: 
                get_nth_byte(src_arithv, i) == get_nth_byte(reread_data, i);
        
            // assert {:split_here} forall i | 0 <= i < size_to_nat(size) :: 
            //     get_nth_byte(arithv, i) == get_nth_byte(reread1, i);

        }

        assert {:split_here} true;
        var s' := update_a_mem_in_state(s, dst_tv.r, memid, new_data1);

        assert {:split_here} forall i | cur_off <= i < cur_off + size_to_nat(size) ::
            s'.mems[rid][memid].data[i].etypev == new_data1[i].etypev;


        var load_data := s'.mems[rid][memid].data;

        assert {:split_here} true;

        var new_reg_tv := read_n_byte_etypev(s', dst_tv.r, memid, cur_off, size);

        assert {:split_here} true;

        if size == DW {
            assert {:split_here} new_reg_tv == src_tv;
        }
        else {
            assert {:split_here} new_reg_tv.val == src_arithv;
        }
    }
    */


    /*
    lemma {:timeLimit 60} update_mem_lemma(s: State, rid: nat, memid: nat, off: int64, size:SIZE, src_tv: ETYPEV)
    requires 0 <= rid < |s.mems|
    requires 0 <= memid < |s.mems[rid]|
    requires 0 <= off < off + size_to_nat(size) <= |s.mems[rid][memid].data|
    requires src_tv != Uninit
    requires valid_ptr_slots(s, s.mems[rid][memid].data, off, size)
    requires valid_etypev_if_ptr(s, src_tv)
    ensures var src_arithv := get_arith_val(s, src_tv);
            var new_data := update_mem(s, rid, memid, off, size, src_tv);
            var reread := read_n_byte_data(new_data, off, size);
            if size == DW
            then reread == etypev_2_val(src_tv)
            else forall i | 0 <= i < size_to_nat(size)
                 :: 
                 get_nth_byte(src_arithv, i) == get_nth_byte(reread, i)
    {
        var data := s.mems[rid][memid].data;
        var slot_tv := data[off].etypev;
        var sizen := size_to_nat(size);

        var new_data1 := update_mem(s, rid, memid, off, size, src_tv);
        var reread1 := read_n_byte_data(new_data1, off, size);

        assert {:split_here} true;

        if size == DW {
            assert {:split_here} true;

            var new_slots_tv := reg_to_8byte_data(src_tv);
            assert {:split_here} get_nth_byte(etypev_2_val(src_tv), 0) == (etypev_2_val(new_slots_tv[0]));
            assert {:split_here} get_nth_byte(etypev_2_val(src_tv), 1) == (etypev_2_val(new_slots_tv[1]));
            assert {:split_here} get_nth_byte(etypev_2_val(src_tv), 2) == (etypev_2_val(new_slots_tv[2]));
            assert {:split_here} get_nth_byte(etypev_2_val(src_tv), 3) == (etypev_2_val(new_slots_tv[3]));
            assert {:split_here} get_nth_byte(etypev_2_val(src_tv), 4) == (etypev_2_val(new_slots_tv[4]));
            assert {:split_here} get_nth_byte(etypev_2_val(src_tv), 5) == (etypev_2_val(new_slots_tv[5]));
            assert {:split_here} get_nth_byte(etypev_2_val(src_tv), 6) == (etypev_2_val(new_slots_tv[6]));
            assert {:split_here} get_nth_byte(etypev_2_val(src_tv), 7) == (etypev_2_val(new_slots_tv[7]));

            var new_data := update_mem_slots(data, off, size, new_slots_tv);
            assert {:split_here} new_data[off+0].etypev == new_slots_tv[0];
            assert {:split_here} new_data[off+1].etypev == new_slots_tv[1];
            assert {:split_here} new_data[off+2].etypev == new_slots_tv[2];
            assert {:split_here} new_data[off+3].etypev == new_slots_tv[3];
            assert {:split_here} new_data[off+4].etypev == new_slots_tv[4];
            assert {:split_here} new_data[off+5].etypev == new_slots_tv[5];
            assert {:split_here} new_data[off+6].etypev == new_slots_tv[6];
            assert {:split_here} new_data[off+7].etypev == new_slots_tv[7];
    
            assert {:split_here} new_data1 == new_data;

            assert {:split_here} true;
            var reread_data := read_n_byte_data(new_data, off, size);
            assert {:split_here} get_nth_byte(reread_data, 0) == (etypev_2_val(new_data[off+0].etypev));
            assert {:split_here} get_nth_byte(reread_data, 1) == (etypev_2_val(new_data[off+1].etypev));
            assert {:split_here} get_nth_byte(reread_data, 2) == (etypev_2_val(new_data[off+2].etypev));
            assert {:split_here} get_nth_byte(reread_data, 3) == (etypev_2_val(new_data[off+3].etypev));
            assert {:split_here} get_nth_byte(reread_data, 4) == (etypev_2_val(new_data[off+4].etypev));
            assert {:split_here} get_nth_byte(reread_data, 5) == (etypev_2_val(new_data[off+5].etypev));
            assert {:split_here} get_nth_byte(reread_data, 6) == (etypev_2_val(new_data[off+6].etypev));
            assert {:split_here} get_nth_byte(reread_data, 7) == (etypev_2_val(new_data[off+7].etypev));
            assert {:split_here} reread_data == reread1;

            assert {:split_here} get_nth_byte(reread_data, 0) == get_nth_byte(etypev_2_val(src_tv), 0);
            assert {:split_here} get_nth_byte(reread_data, 1) == get_nth_byte(etypev_2_val(src_tv), 1);
            assert {:split_here} get_nth_byte(reread_data, 2) == get_nth_byte(etypev_2_val(src_tv), 2);
            assert {:split_here} get_nth_byte(reread_data, 3) == get_nth_byte(etypev_2_val(src_tv), 3);
            assert {:split_here} get_nth_byte(reread_data, 4) == get_nth_byte(etypev_2_val(src_tv), 4);
            assert {:split_here} get_nth_byte(reread_data, 5) == get_nth_byte(etypev_2_val(src_tv), 5);
            assert {:split_here} get_nth_byte(reread_data, 6) == get_nth_byte(etypev_2_val(src_tv), 6);
            assert {:split_here} get_nth_byte(reread_data, 7) == get_nth_byte(etypev_2_val(src_tv), 7);

            bytes_equal_so_bv64_equal(reread_data, src_tv);

            assert {:split_here} reread_data == etypev_2_val(src_tv);
            assert {:split_here} reread1 == etypev_2_val(src_tv);
        }
        else {

            assert {:split_here} true;
            var new_slot_kind := if is_scalar(src_tv) then src_tv.kind else Normal;
            var arithv := get_arith_val(s, src_tv);
            var new_slots_tv := scalar_etypev_to_seq(Scalar(new_slot_kind, arithv), size_to_nat(size), 0);

            assert {:split_here} forall i | 0 <= i < size_to_nat(size) :: 
                get_nth_byte(arithv, i) == new_slots_tv[i].val;

            assert {:split_here} true;
            var new_data := update_mem_slots(data, off, size, new_slots_tv);

            assert {:split_here} forall i | 0 <= i < size_to_nat(size) ::
                new_data[off+i].etypev == new_slots_tv[i];

            assert {:split_here} forall i | 0 <= i < size_to_nat(size) ::
                new_data1[off+i].etypev == new_data[off+i].etypev;

            assert {:split_here} true;
            var reread_data := read_n_byte_data(new_data, off, size);
            
            // lemma
            read_n_byte_data_inv(new_data, off, size);

            assert {:split_here} forall i | 0 <= i < size_to_nat(size) ::
                get_nth_byte(reread_data, i) == (etypev_2_val(new_data[off+i].etypev) & 0xff);
            
            assert {:split_here} reread_data == reread1;

            assert {:split_here} forall i | 0 <= i < size_to_nat(size) :: 
                get_nth_byte(arithv, i) == get_nth_byte(reread_data, i);
        
            assert {:split_here} forall i | 0 <= i < size_to_nat(size) :: 
                get_nth_byte(arithv, i) == get_nth_byte(reread1, i);
        }
    }
    */



    





    // ----------------------------------------------------------------
    //           Lemma: no partial pointers in memory slots
    // ----------------------------------------------------------------

    // lemma: all pointers are aligned at 8 bytes


    /*
    ghost predicate reg_dep_id_type(s: State, reg:REG)
        {
            var (val, reg_type, map_fd, mem_id) := get_reg_all(s, reg);

            // mem_id and dst_map_fd is -1 when they are not map/null or pointers/null
            (if is_mapx_or_null(reg_type) then map_fd != -1 else map_fd == -1)
            &&
            (if is_ptr_or_null(reg_type) then mem_id != -1 else mem_id == -1)
        }


    ghost predicate require_arith_inv(s: State, dst:REG := Rn, src: REG := Rn)
        {
            // mem_id and dst_map_fd is -1 when they are not map/null or pointers/null
            
            reg_dep_id_type(s, dst) &&
            reg_dep_id_type(s, src)
            &&
            s.R10.regType == ETYPE.PtrType(STACKMEM)
        }

    ghost predicate ensure_arith_inv(s: State, dst: REG)
        {
            // mem_id and dst_map_fd is -1 when they are not map/null or pointers/null
            reg_dep_id_type(s, dst)
            &&
            s.R10.regType == ETYPE.PtrType(STACKMEM)
        }


    lemma no_partial_pointers(s: State, dst:REG, src:REG, off:int64, size:int64)
    requires store_stackmem_precond(s, dst, src, off, size)
    requires reg_dep_id_type(s, src)
    requires pointers_are_8_byte(s.stack[get_reg(s, dst).memId])
    ensures var s' := store_stackmem(s, dst, src, off, size);
       pointers_are_8_byte(s'.stack[get_reg(s', dst).memId])
    {}

    ghost predicate pointers_are_8_byte(stack: seq<RegState>)
    requires |stack| == 512
    {
        forall i | 0 <= i < 512 :: (
            forall j | var align8 := i - (i % 8); align8 <= j < (align8 + 8) :: (
                
                var (reg_type, map_fd, mem_id):= (stack[j].regType, stack[j].mapFd, stack[j].memId);

                if is_ptr_or_null(stack[i].regType) then (
                    is_ptr_or_null(reg_type)
                    &&
                    (if is_mapx_or_null(reg_type) then map_fd != -1 else map_fd == -1)
                    &&
                    mem_id != -1
                ) else (
                    !is_ptr_or_null(reg_type)
                    &&
                    map_fd == -1
                    &&
                    mem_id == -1
                )
            )
        )
    }
    */

    // ----------------------------------------------------------------
    //           Lemma: other lemmas as future works
    // ----------------------------------------------------------------


    /*
    lemma stack_size_is_512(s: State, dst:REG, src:REG, off:int64, size:int64)
    requires store_stackmem_precond(s, dst, src, off, size)
    ensures var res := store_stackmem(s, dst, src, off, size);
        |res.stack| == |s.stack| &&
        |res.stack[get_reg(s, dst).memId]| == |s.stack[get_reg(s, dst).memId]|
    {}

    // TODO-Lemma: every type of memory regions starting their ids from 0 individually
    // e.g., all STACKMEM has id 0

    // TODO_Lemma: all operations preserves that memory offset is within 32-bit

    // requires require_arith_inv(s, dst)
    // ensures ensure_arith_inv(res, dst)

    // lemma: not ptr_or_null type with non-zero offset in any priviledge mode

    // lemma: memory region ids of ctx, map_meta, btf are always the last three ids

    // if mem_invs holds then after operation it still holds

    // packet_meta, _data, _end are continious in the s.mems at any point of a prog

    // lemma: pointers on all memory regions are 8-bytes with same id and region type
    */
}



    /*
    lemma {:timeLimit 60} store_then_load_same_data(
        s1: State, st_insn: Instruction, ld_insn: Instruction
    )
    requires exists addr_reg, val_reg1, val_reg2, off ::
             st_insn == MEMSTX(addr_reg, val_reg1, off, DW)
             &&
             ld_insn == MEMLD(val_reg2, addr_reg, off, DW, unknown_bool())
    //
    requires mem_store_reg_precond(s1, st_insn)
    //
    requires var addr_reg := st_insn.dst;
             var regtv := get_reg_typeval(s1, addr_reg);
             var rid := r2id(regtv.r);
             var memid := regtv.memid;
             !s1.mems[rid][memid].is_concur
    //
    requires var s2 := mem_store_reg(s1, st_insn);
             mem_load_precond(s2, ld_insn)
    // 
    // ensures  var s2 := mem_store_reg(s1, st_insn);
    //          var s3 := mem_load(s2, ld_insn);
    //          var st_val := get_reg_arith_val(s1, st_insn.src);
    //          var ld_val := get_reg_arith_val(s3, ld_insn.dst);
    //          low_nsize(st_val, st_insn.size) == low_nsize(ld_val, st_insn.size)
    {
        var (dst, src, off, size) := (st_insn.dst, st_insn.src, st_insn.off, st_insn.size);
        
        var s2 := mem_store_reg(s1, st_insn);
        
        assert {:split_here} true;

        var src_tv := get_reg_typeval(s1, src);
        var src_arithv := get_reg_arith_val(s1, src);
        var dst_tv := get_reg_typeval(s1, dst);
        var rid := r2id(dst_tv.r);
        var memid := dst_tv.memid;
        var cur_off := 
            if dst_tv.r == PTR_TO_STACK
            then bv64ToInt64(dst_tv.off) + off
            else bv64ToInt64(dst_tv.off) + off + 512;

        assert {:split_here} true;
        assert {:split_here} 0 <= rid < |s1.mems|;
        assert {:split_here} 0 <= memid < |s1.mems[rid]|;
        assert {:split_here} 0 <= cur_off < cur_off + size_to_nat(size) <= |s1.mems[rid][memid].data|;
        assert {:split_here} src_tv != Uninit;
        
        assert {:split_here} valid_ptr_slots(s1, s1.mems[rid][memid].mem_type,
            s1.mems[rid][memid].data, cur_off, size
        );
        assert {:split_here} valid_etypev_if_ptr(s1, src_tv);
        // update_mem_lemma(s1, rid, memid, cur_off, size, src_tv);
        assert {:split_here} true;

        // var new_data := s2.mems[rid][memid].data;
        // var reread := read_n_byte_data(new_data, off, size);
        // if size == DW {
        //     assert {:split_here} reread == etypev_2_val(src_tv);
        // }
        // else{
        //     assert {:split_here} forall i | 0 <= i < size_to_nat(size)
        //     :: 
        //     get_nth_byte(src_arithv, i) == get_nth_byte(reread, i);
        // }

        // var x := read_n_byte_data(s2.mems[rid][memid].data, cur_off, size);

        // assert {:split_here} true;
        
        // assert x == vreg_tv.val;
        // assert low_nsize(x, size) == low_nsize(vreg_tv.val, size);
        /*
        assert {:split_here} true;
        
        var s3 := mem_load(s2, ld_insn);
        
        assert {:split_here} true;

        var st_val := get_reg_arith_val(s1, st_insn.src);
        
        assert {:split_here} true;

        var ld_val := get_reg_arith_val(s3, ld_insn.dst);

        assert {:split_here} true;

        assert low_nsize(st_val, st_insn.size) == low_nsize(ld_val, st_insn.size);
        */
    }
    */
