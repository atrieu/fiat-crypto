Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.NTT.GallinaNTT.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.NTT.Bignums.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Representation.

Require Import bedrock2.Array.
Require Import bedrock2.Loops.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Scalars.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.ZnWords.

Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.

Require Import Crypto.Util.ListUtil.

(* For [to_byte_table] *)
Require Import Rupicola.Lib.InlineTables.
(* For [offset] *)
Require Import Rupicola.Lib.Arrays.

Require Coq.Strings.String.
Local Open Scope string_scope.

Section Bedrock.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Context {ntt ntt_inverse: String.string}.
  Context {q: positive}.
  Local Notation F := (F q).
  Context {n m: nat}.
  Context (zeta: F) {c:F} (zetas: list F).

  Hypothesis c_ok: id c = F.inv (F.pow (1 + 1)%F (N.of_nat (Nat.min m n))).

  Notation NTT_gallina := (@ntt_loop q zetas (Nat.min m n) n).
  Notation NTT_inverse_gallina := (@inverse_ntt_loop q zetas (Nat.min m n) n).

  Section FitsInWords.
    (* When a field element needs [felem_size_in_words] machine words to fit *)
    Context {mul add carry_add sub carry_sub opp square mul_inv_pow2 inv from_bytes to_bytes select_znz felem_copy from_word: String.string}.

    Local Instance field_parameters: FieldParameters :=
      Build_FieldParameters
        q c mul add add sub sub opp square mul_inv_pow2 inv from_bytes to_bytes select_znz felem_copy from_word.

    Context (n_words n_bytes : nat) (weight : nat -> Z)
      (bounds : Type)
      (list_in_bounds : bounds -> list Z -> Prop)
      (loose_bounds tight_bounds byte_bounds : bounds)
      (relax_bounds :
        forall X : list Z,
          list_in_bounds tight_bounds X ->
          list_in_bounds loose_bounds X)
      (eval_transformation : list Z -> list Z).

    Hypothesis loose_bounds_eq_tight_bounds: id loose_bounds = tight_bounds.

    Local Instance field_representation: FieldRepresentation :=
      frep n_words n_bytes weight bounds list_in_bounds loose_bounds tight_bounds byte_bounds eval_transformation.

    Local Instance field_representation_ok: FieldRepresentation_ok :=
      frep_ok n_words n_bytes weight bounds list_in_bounds loose_bounds tight_bounds byte_bounds relax_bounds eval_transformation.

    Instance spec_of_add: spec_of add :=
      spec_of_BinOp bin_add.
    Instance spec_of_sub: spec_of sub :=
      spec_of_BinOp bin_sub.
    Instance spec_of_mul: spec_of mul :=
      spec_of_BinOp bin_mul.
    (* Specialized multiplication by c = F.inv (F.pow (1 + 1)%F (N.of_nat (Nat.min m n))) *)
    Instance spec_of_mul_inv_pow2: spec_of mul_inv_pow2 :=
      spec_of_UnOp un_scmula24.
    Instance spec_of_felem_copy: spec_of felem_copy :=
      Field.spec_of_felem_copy (field_representation:=field_representation).

    Hypothesis n_words_pos: (0 < n_words)%nat.

    (* These are to ensure that content of the arrays are addresssable *)
    Hypothesis n_lt_width: (Z.of_nat (2 ^ n) * felem_size_in_bytes < 2 ^ width)%Z.
    Hypothesis m_lt_width: (Z.of_nat (2 ^ m) * felem_size_in_bytes < 2 ^ width)%Z.

    Hypothesis zetas_length_ok: length zetas = Nat.pow 2 m.

    Instance spec_of_ntt: spec_of ntt :=
      fnspec! ntt (z_ptr p_ptr: word) / (p: list F) (z': list felem) R,
        { requires tr mem :=
            exists p',
              Forall2 (fun x y => feval y = x) p p' /\
              Forall2 (fun x y => feval y = x) zetas z' /\
              Forall (bounded_by tight_bounds) p' /\
              Forall (bounded_by tight_bounds) z' /\
              mem =* (Bignums felem_size_in_words (Nat.pow 2 n) p_ptr p')
                     * (Bignums felem_size_in_words (Nat.pow 2 m) z_ptr z')
                     * R;
          ensures tr' mem' :=
            tr' = tr /\
              exists p',
                Forall2 (fun x y => feval y = x) (NTT_gallina p) p' /\
                Forall2 (fun x y => feval y = x) zetas z' /\
                Forall (bounded_by tight_bounds) p' /\
                Forall (bounded_by tight_bounds) z' /\
                mem' =* (Bignums felem_size_in_words (Nat.pow 2 n) p_ptr p')
                        * (Bignums felem_size_in_words (Nat.pow 2 m) z_ptr z')
                        * R }.

    Instance spec_of_ntt_inverse: spec_of ntt_inverse :=
      fnspec! ntt_inverse (z_ptr p_ptr: word) / (p: list F) (z': list felem) R,
        { requires tr mem :=
            exists p',
              Forall2 (fun x y => feval y = x) p p' /\
              Forall2 (fun x y => feval y = x) zetas z' /\
              mem =* (Bignums felem_size_in_words (Nat.pow 2 n) p_ptr p')
                     * (Bignums felem_size_in_words (Nat.pow 2 m) z_ptr z')
                     * R;
          ensures tr' mem' :=
            tr' = tr /\
              exists p',
                Forall2 (fun x y => feval y = x) (NTT_inverse_gallina p) p' /\
                Forall2 (fun x y => feval y = x) zetas z' /\
                mem' =* (Bignums felem_size_in_words (Nat.pow 2 n) p_ptr p') * R
                        * (Bignums felem_size_in_words (Nat.pow 2 m) z_ptr z')
                        * R }.

    Definition br2_ntt :=
      func! (z_ptr, p) {
          stackalloc felem_size_in_bytes as tmp;
          l = coq:(0);
          len = coq:(Z.pow 2 (Z.of_nat n));
          while (coq:(Z.pow 2 (Z.of_nat (n - Nat.min m n))) < len) {
              old_len = len;
              len = len >> coq:(1);
              start = coq:(0);
              while (start < coq:(Z.pow 2 (Z.of_nat n))) {
                  l = l + coq:(1);
                  z = coq:(offset (expr.var "z_ptr") bedrock_expr:(l) (expr.literal felem_size_in_bytes));
                  j = start;
                  while (j < (start + len)) {
                      x = coq:(offset (expr.var "p") bedrock_expr:(j + len) (expr.literal felem_size_in_bytes));
                      $mul(tmp, z, x);
                      y = coq:(offset (expr.var "p") bedrock_expr:(j) (expr.literal felem_size_in_bytes));
                      $sub(x, y, tmp);
                      $add(y, y, tmp);
                      j = j + coq:(1)
                    };
                  start = start + old_len
                }
            }
        }.

    Definition br2_ntt_inverse :=
      func! (z_ptr, p) {
          stackalloc felem_size_in_bytes as tmp;
          l = coq:(Z.of_nat (Nat.pow 2 (Nat.min m n)));
          len = coq:(Z.of_nat (Nat.pow 2 (n - (Nat.min m n))));
          while (len < coq:(Z.of_nat (Nat.pow 2 n))) {
              start = coq:(0);
              old_len = len;
              len = len << coq:(1);
              while (start < coq:(Z.of_nat (Nat.pow 2 n))) {
                  l = l - coq:(1);
                  z = coq:(offset (expr.var "z_ptr") bedrock_expr:(l) (expr.literal felem_size_in_bytes));
                  j = start;
                  while (j < start + old_len) {
                      $felem_copy(tmp, coq:(offset (expr.var "p") bedrock_expr:(j) (expr.literal felem_size_in_bytes)));
                      x = coq:(offset (expr.var "p") bedrock_expr:(j + old_len) (expr.literal felem_size_in_bytes));
                      y = coq:(offset (expr.var "p") bedrock_expr:(j) (expr.literal felem_size_in_bytes));
                      $add(y, tmp, x);
                      $sub(x, x, tmp);
                      $mul(x, z, x);
                      j = j + coq:(1)
                    };
                  start = start + len
                }
            };
          j = coq:(0);
          while (j < coq:(Z.of_nat (Nat.pow 2 n))) {
              x = coq:(offset (expr.var "p") bedrock_expr:(j) (expr.literal felem_size_in_bytes));
              $mul_inv_pow2(x, x);
              j = j + coq:(1)
            }
        }.

    Lemma Forall2_set_nth {A B: Type}:
      forall (R: A -> B -> Prop) (x: A) (y: B) (i: nat) (xs: list A) (ys: list B),
        Forall2 R xs ys ->
        R x y ->
        Forall2 R (set_nth i x xs) (set_nth i y ys).
    Proof. intros; apply Forall2_update_nth; auto. Qed.

    Lemma Forall_set_nth {A: Type}:
      forall (R: A -> Prop) (x: A) (i: nat) (xs: list A),
        Forall R xs ->
        R x ->
        Forall R (set_nth i x xs).
    Proof.
      intros R x i xs HF HR. apply Forall.Forall_forall_iff_nth_error.
      intros j v. rewrite nth_set_nth. intro Hnth.
      destruct (Nat.eq_dec j i) as [->|Hne].
      - destruct (lt_dec i (length xs)); inversion Hnth; subst v; assumption.
      - apply (proj1 Forall.Forall_forall_iff_nth_error HF j v Hnth).
    Qed.

    Lemma Bignum_as_anybytes:
      forall (n: nat) (addr: word.rep) (ws: list word.rep),
        Lift1Prop.impl1
          (@Bignum width word mem n addr ws)
          (@anybytes width word mem addr (Z.of_nat n * bytes_per_word width)).
    Proof.
      unfold Bignum. intros k addr ws.
      intros mm Hsep.
      apply sep_emp_l in Hsep. destruct Hsep as (Hws & Hsep).
      rewrite <- bytes_per_width_bytes_per_word in Hsep.
      apply bytes_of_words in Hsep.
      apply array_1_to_anybytes in Hsep.
      rewrite ws2bs_length, Nat2Z.inj_mul, Hws, Z.mul_comm, bytes_per_width_bytes_per_word in Hsep.
      exact Hsep.
    Qed.

    Lemma br2_ntt_ok:
      program_logic_goal_for br2_ntt
        (forall functions : map.rep,
            map.get functions ntt = Some br2_ntt ->
            spec_of_mul functions ->
            spec_of_sub functions -> spec_of_add functions -> spec_of_ntt functions).
    Proof.
      Local Opaque Memory.bytes_per to_byte_table Z.pow Z.of_nat List.map Z.div Z.sub Z.add Nat.sub Nat.min F.F felem_size_in_bytes.
      Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub un_outbounds bin_outbounds].
      pose proof felem_size_in_bytes_mod as XA.
      assert (0 < felem_size_in_bytes) as XB.
      { assert (felem_size_in_bytes = Z.of_nat n_words * bytes_per_word width) as -> by reflexivity.
        pose proof (Types.word_size_in_bytes_pos). Lia.lia. }
      assert (n < Z.to_nat width)%nat as n_lt_width'.
      { apply ((Nat.pow_lt_mono_r_iff 2 n (Z.to_nat width) ltac:(Lia.lia))).
        rewrite <- (Nat2Z.id (Nat.pow 2 n)).
        assert (2 ^ (Z.to_nat width) = Z.to_nat (2 ^ width))%nat as -> by (destruct (width_cases); rewrite Z2Nat.inj_pow; try Lia.lia; reflexivity).
        apply Z2Nat.inj_lt; Lia.nia. }
      repeat straightline. split; [assumption|].
      intros; do 7 straightline.
      apply wp_while.
      apply (FElem_from_bytes a mStack) in H7.
      (* First loop invariant *)
      pose (loop_inv1:= fun (fuel: nat) (tr': Semantics.trace) (mem': mem) (loc: locals) =>
                          (fuel <= Nat.min m n)%nat /\
                            let i := (Nat.min m n - fuel)%nat in
                            tr' = tr /\
                              exists p' px,
                                polynomial_layer_decomposition_loop zetas 0 i (0%nat, (2 ^ n)%nat, p) = (Nat.pow 2 i - 1, Nat.pow 2 (n - i), px)%nat /\
                                  Forall2 (fun x y => feval y = x) px p' /\
                                  Forall (bounded_by tight_bounds) p' /\
                                  map.get loc "p" = Some p_ptr /\
                                  map.get loc "z_ptr" = Some z_ptr /\
                                  map.get loc "tmp" = Some a /\
                                  map.get loc "l" = Some (word.of_Z (Z.of_nat ((Nat.pow 2 i) - 1))) /\
                                  map.get loc "len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - i)))) /\
                                  exists a_stk, ((FElem a a_stk) * ((Bignums felem_size_in_words (Nat.pow 2 n) p_ptr p') * (Bignums felem_size_in_words (2 ^ m) z_ptr z' * R)))%sep mem').
      exists nat, lt, loop_inv1.
      split; [apply lt_wf|].
      split. (* Invariant holds at beginning *)
      { exists (Nat.min m n). repeat split; [Lia.lia|..].
        exists x, p. unfold l2, l1, l0, l'0.
        repeat split; repeat (rewrite map.get_put_diff by (clear; congruence)); try (rewrite map.get_put_same); try rewrite PeanoNat.Nat.sub_diag; try rewrite Nat.sub_0_r; auto.
        - unfold len. rewrite Nat2Z.inj_pow. reflexivity.
        - destruct H7 as (a_stk & Hstk).
          exists a_stk, mStack, mem0. split; auto.
          rewrite map.split_comm. auto. }
      intros fuel tr' mem' loc' Hinv.
      destruct Hinv as (Hfuel & -> & p' & px' & HF1 & Heq & Hbounded & Hp & Hz_ptr & Htmp & Hm & Hlen & (a_stk & Hseps)).
      eexists; split; repeat straightline.
      { eexists; split; [eassumption|].
        instantiate (1 := if Nat.eq_dec fuel 0%nat then word.of_Z 0 else word.of_Z 1).
        unfold v. rewrite Nat2Z.inj_pow, <- Core.word.morph_ltu.
        2-3: split; [apply Z.pow_nonneg; clear; Lia.lia|].
        2-3: apply Zpow_facts.Zpower_lt_monotone; clear -n_lt_width'; Lia.lia.
        destruct (Nat.eq_dec fuel 0) as [->|Hfnz].
        - rewrite Nat.sub_0_r, Z.ltb_irrefl. reflexivity.
        - match goal with | |- context [Z.ltb ?a ?b] => pose proof (Zlt_cases a b) as Hcond end.
          destruct (_ <? _); [reflexivity|]. apply Z.ge_le in Hcond.
          apply Z.pow_le_mono_r_iff in Hcond; try (clear -Hfuel; Lia.lia).
          apply Nat2Z.inj_le in Hcond. clear -Hfuel Hfnz Hcond; Lia.lia. }
      assert (word.unsigned _ = if (Nat.eq_dec fuel 0) then 0%Z else 1%Z) as ->.
      { destruct (Nat.eq_dec fuel 0); [apply word.unsigned_of_Z_0|apply word.unsigned_of_Z_1]. }
      split; intro Hb; destruct (Nat.eq_dec fuel 0) as [->|Hfnz]; try (clear -Hb; congruence); clear Hb.
      { (* Invariant preservation *)
        repeat straightline. eexists; split; repeat straightline.
        { eexists; split; [eassumption|reflexivity]. }
        eexists; split; repeat straightline.
        { unfold l0. rewrite map.get_put_diff by (clear; congruence).
          eexists; split; [eassumption|]. cbn. repeat red.
          rewrite <- Core.word.morph_shiftr.
          2: clear -n_lt_width' Hfuel Hfnz; Lia.lia.
          2: split; [|rewrite Nat2Z.inj_pow; apply Zpow_facts.Zpower_lt_monotone]; clear -n_lt_width' Hfuel Hfnz; Lia.lia.
          rewrite Z.shiftr_div_pow2 by Lia.lia.
          replace (2 ^ 1) with (Z.of_nat (Nat.pow 2 1)) by reflexivity.
          rewrite <- Nat2Z.inj_div, <- PeanoNat.Nat.pow_sub_r by (clear -Hfuel Hfnz; Lia.lia).
          assert (n - _ - _ = n - (Nat.min m n - (fuel - 1)))%nat as -> by (clear -Hfuel Hfnz; Lia.lia).
          reflexivity. }
        apply wp_while.
        (* second loop *)
        pose (loop_inv2:= fun (fuel2: nat) (tr': Semantics.trace) (mem': mem) (loc: locals) =>
                            (fuel2 <= Nat.pow 2 (Nat.min m n - fuel))%nat /\
                              let i := ((Nat.pow 2 (Nat.min m n - fuel) - fuel2))%nat in
                              tr' = tr /\
                                exists p'' px'',
                                  polynomial_list_loop zetas i (Nat.pow 2 (n - (Nat.min m n - fuel))) (Nat.pow 2 (n - (Nat.min m n - (fuel - 1)))) ((Nat.pow 2 (Nat.min m n - fuel) - 1), 0, px')%nat = ((Nat.pow 2 (Nat.min m n - fuel) - 1) + i, i * (Nat.pow 2 (n - (Nat.min m n - fuel))), px'')%nat /\
                                    Forall2 (fun x y => feval y = x) px'' p'' /\
                                    Forall (bounded_by tight_bounds) p'' /\
                                    map.get loc "p" = Some p_ptr /\
                                    map.get loc "z_ptr" = Some z_ptr /\
                                    map.get loc "tmp" = Some a /\
                                    map.get loc "l" = Some (word.of_Z (Z.of_nat ((Nat.pow 2 (Nat.min m n - fuel)) - 1 + i))) /\
                                    map.get loc "len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - (Nat.min m n - (fuel - 1)))))) /\
                                    map.get loc "old_len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - (Nat.min m n - fuel))))) /\
                                    map.get loc "start" = Some (word.of_Z (Z.of_nat (i * (Nat.pow 2 (n - (Nat.min m n - fuel)))))) /\
                                    (exists a_stk : list word.rep, ((FElem a a_stk) * (Bignums felem_size_in_words (2 ^ n) p_ptr p'' ⋆ (Bignums felem_size_in_words (2 ^ m) z_ptr z' ⋆ R)))%sep mem')).
        exists nat, lt, loop_inv2. split; [apply lt_wf|]. split.
        { (* invariant holds at beginning *)
          exists (2 ^ (Nat.min m n - fuel))%nat. repeat split; [Lia.lia|].
          exists p', px'. unfold l2, l1, l0.
          repeat split; repeat (rewrite map.get_put_diff by (clear; congruence)); try (rewrite map.get_put_same); eauto.
          - rewrite PeanoNat.Nat.sub_diag. cbn.
            rewrite PeanoNat.Nat.add_0_r. reflexivity.
          - rewrite Hm, PeanoNat.Nat.sub_diag, PeanoNat.Nat.add_0_r. reflexivity.
          - rewrite PeanoNat.Nat.sub_diag, PeanoNat.Nat.mul_0_l.
            reflexivity. }
        intros fuel2 tr2 mem2 l3 Hinv2.
        destruct Hinv2 as (Hfuel2 & -> & p2 & px2 & Heq2 & HF2 & Hbounded2 & Hp2 & Hz_ptr2 & Htmp2 & Hm2 & Hlen2 & Hold_len2 & Hstart2 & (a_stk2 & Hseps2)).
        eexists; split; repeat straightline.
        { eexists; split; [eassumption|repeat straightline]. }
        rewrite <- Core.word.morph_ltu.
        3: split; [apply Z.pow_nonneg; clear; Lia.lia|apply Zpow_facts.Zpower_lt_monotone; clear -n_lt_width'; Lia.lia].
        2: split; [apply Nat2Z.is_nonneg|].
        2:{ rewrite Nat.mul_sub_distr_r, <- PeanoNat.Nat.pow_add_r.
            assert (Nat.min m n - fuel + _ = n)%nat as -> by (clear -Hfnz Hfuel; Lia.lia).
            assert (2 ^ width = Z.of_nat (2 ^ (Z.to_nat width))) as -> by (rewrite Nat2Z.inj_pow, Z2Nat.id by (clear -n_lt_width'; Lia.lia); reflexivity).
            apply Nat2Z.inj_lt.
            eapply Nat.le_lt_trans; [|eapply PeanoNat.Nat.pow_lt_mono_r; try eassumption; Lia.lia].
            clear; Lia.lia. }
        assert (word.unsigned _ = if Nat.eq_dec fuel2 0%nat then 0%Z else 1%Z) as ->.
        { destruct (Nat.eq_dec fuel2 0) as [-> |Hfnz2].
          - rewrite Nat.sub_0_r, <- Nat.pow_add_r.
            assert (_ - _ + _ = n)%nat as -> by (clear -Hfnz Hfuel; Lia.lia).
            rewrite Nat2Z.inj_pow, Z.ltb_irrefl, word.unsigned_of_Z_0. reflexivity.
          - rewrite Nat.mul_sub_distr_r, <- Nat.pow_add_r.
            assert (_ - _ + _ = n)%nat as -> by (clear -Hfnz Hfuel; Lia.lia).
            assert (2 ^ Z.of_nat n = Z.of_nat (Nat.pow 2 n)) as -> by (rewrite Nat2Z.inj_pow; reflexivity).
            match goal with | |- context [Z.ltb ?a ?b] => pose proof (Zlt_cases a b) as Hcond end.
            destruct (_ <? _); [apply word.unsigned_of_Z_1|]. apply Z.ge_le in Hcond.
            apply Nat2Z.inj_le in Hcond. clear -Hfnz2 Hcond; pose proof (NatUtil.pow_nonzero 2 n ltac:(congruence)); pose proof (NatUtil.pow_nonzero 2 (n - (Nat.min m n - fuel)) ltac:(congruence)); Lia.lia. }
        split; intro Hb; destruct (Nat.eq_dec fuel2 0) as [->|Hfnz2]; try (clear -Hb; congruence); clear Hb.
        { (* Invariant preservation *)
          repeat straightline.
          eexists; split; repeat straightline.
          { eexists; split; [eassumption|repeat straightline]. }
          eexists; split; repeat straightline.
          { unfold l0; rewrite map.get_put_diff by (clear; congruence).
            eexists; split; [eassumption|repeat straightline].
            rewrite map.get_put_same. eexists; split; [reflexivity|].
            unfold v. rewrite <- word.ring_morph_add, <- word.ring_morph_mul.
            reflexivity. }
          eexists; split; repeat straightline.
          { unfold l1, l0. repeat rewrite map.get_put_diff by (clear; congruence).
            eexists; split; [eassumption|reflexivity]. }
          apply wp_while.
          set (polynomial_decompose_loop' :=
                 fun k start len z p => fold_left
                                       (fun (p0 : list (ModularArithmetic.F q)) (i : nat) =>
                                          let t0 := nth_default 0%F p0 (i + len) in
                                          let t1 := (z * t0)%F in
                                          let t2 := nth_default 0%F p0 i in
                                          let p' := set_nth (i + len) (t2 - t1)%F p0 in set_nth i (t2 + t1)%F p')
                                       (seq start k) p).
          assert (polynomial_decompose_loop_eq: forall start len z p, polynomial_decompose_loop' len start len z p = polynomial_decompose_loop start len z p) by reflexivity.
          pose (loop_inv3 := fun (fuel3:nat) (tr': Semantics.trace) (mem': mem) (loc: locals) =>
                               (fuel3 <= Nat.pow 2 (n - (Nat.min m n - (fuel - 1))))%nat /\
                                 let i := (Nat.pow 2 (n - (Nat.min m n - (fuel - 1))) - fuel3)%nat in
                                 tr' = tr /\
                                   let px'' := polynomial_decompose_loop' i ((2 ^ (Nat.min m n - fuel) - fuel2) * 2 ^ (n - (Nat.min m n - fuel)))%nat (2 ^ (n - (Nat.min m n - (fuel - 1))))%nat (nth_default 0%F zetas (2 ^ (Nat.min m n - fuel) - 1 + 2 ^ (Nat.min m n - fuel) - fuel2 + 1)%nat)%nat px2 in
                                   exists p'',
                                     Forall2 (fun x y => feval y = x) px'' p'' /\
                                     Forall (bounded_by tight_bounds) p'' /\
                                     map.get loc "p" = Some p_ptr /\
                                     map.get loc "z_ptr" = Some z_ptr /\
                                     map.get loc "tmp" = Some a /\
                                     map.get loc "l" = Some (word.of_Z (Z.of_nat (2 ^ (Nat.min m n - fuel) - 1 + (2 ^ (Nat.min m n - fuel) - fuel2)) + 1)) /\
                                     map.get loc "len" = Some (word.of_Z (Z.of_nat (2 ^ (n - (Nat.min m n - (fuel - 1)))))) /\
                                     map.get loc "old_len" = Some (word.of_Z (Z.of_nat (2 ^ (n - (Nat.min m n - fuel))))) /\
                                     map.get loc "start" = Some (word.of_Z (Z.of_nat ((2 ^ (Nat.min m n - fuel) - fuel2) * 2 ^ (n - (Nat.min m n - fuel))))) /\
                                     map.get loc "j" = Some (word.of_Z (Z.of_nat ((2 ^ (Nat.min m n - fuel) - fuel2) * 2 ^ (n - (Nat.min m n - fuel)) + i))) /\
                                     map.get loc "z" = Some (word.add z_ptr (word.of_Z (felem_size_in_bytes * (Z.of_nat (2 ^ (Nat.min m n - fuel) - 1 + (2 ^ (Nat.min m n - fuel) - fuel2)) + 1)))) /\
                                     (exists a_stk : list word.rep, ((FElem a a_stk) * (Bignums felem_size_in_words (2 ^ n) p_ptr p'' ⋆ (Bignums felem_size_in_words (2 ^ m) z_ptr z' ⋆ R)))%sep mem')).
          exists nat, lt, loop_inv3. split; [apply lt_wf|].
          split.
          { (* Invariant holds at beginning *)
            exists (2 ^ (n - (Nat.min m n - (fuel - 1))))%nat. split; [reflexivity|].
            intros. split; [reflexivity|]. intros.
            assert (i = 0)%nat as -> by (clear; Lia.lia).
            exists p2. unfold l2, l1, l0.
            repeat split; repeat (rewrite map.get_put_diff by (clear; congruence)); try (rewrite map.get_put_same); auto.
            - rewrite word.ring_morph_add. reflexivity.
            - rewrite Nat.add_0_r. reflexivity.
            - eauto. }
          intros fuel3 tr3 m3 loc3 Hinv3.
          destruct Hinv3 as (Hfuel3 & -> & p3 & HF3 & Hbounded3 & Hp4 & Hz_ptr4 & Htmp4 & Hm4 & Hlen4 & Hold_len4 & Hstart4 & Hj4 & Hz4 & (a_stk4 & Hseps4)).
          eexists; split; repeat straightline.
          { eexists; split; [eassumption|]. repeat straightline.
            eexists; split; [eassumption|]. repeat straightline.
            eexists; split; [eassumption|].
            rewrite <- word.ring_morph_add, <- Core.word.morph_ltu.
            3: rewrite <- Nat2Z.inj_add.
            2-3: split; try (apply Nat2Z.is_nonneg).
            2-3: assert (2 ^ width = Z.of_nat (2 ^ (Z.to_nat width))) as -> by (rewrite Nat2Z.inj_pow, Z2Nat.id by (clear -n_lt_width'; Lia.lia); reflexivity).
            2-3: apply Nat2Z.inj_lt.
            2-3: eapply (Nat.le_lt_trans _ (Nat.pow 2 n)); [|apply Nat.pow_lt_mono_r; auto].
            2-3: rewrite Nat.mul_sub_distr_r, <- PeanoNat.Nat.pow_add_r.
            2-3: assert (Nat.min m n - fuel + _ = n)%nat as -> by (clear -Hfnz Hfuel; Lia.lia).
            2: transitivity (2 ^ n - fuel2 * 2 ^ (n - (Nat.min m n - fuel)) + (2 ^ (n - (Nat.min m n - (fuel - 1)))))%nat; [clear; Lia.lia|].
            2-3: rewrite <- (Nat.mul_1_l (Nat.pow 2 (n - (Nat.min _ _ - (fuel - 1))))).
            2-3: assert (n - (Nat.min m n - fuel) = S (n - (Nat.min m n - (fuel - 1))))%nat as -> by (clear -Hfuel Hfnz; Lia.lia).
            2-3: rewrite Nat.pow_succ_r'.
            2-3: assert (Nat.pow 2 n = (Nat.pow 2 (Nat.min m n - (fuel - 1))) * (Nat.pow 2 (n - (Nat.min m n - (fuel - 1)))))%nat as -> by (rewrite <- Nat.pow_add_r; f_equal; clear -Hfuel Hfnz; Lia.lia).
            2-3: rewrite Nat.mul_assoc, <- Nat.mul_sub_distr_r, <- Nat.mul_add_distr_r.
            2-3: apply Nat.mul_le_mono_r; clear -Hfuel Hfuel2 Hfnz Hfnz2.
            2-3: generalize (Nat.pow_nonzero 2%nat (Nat.min m n - (fuel - 1)) ltac:(Lia.lia)); Lia.lia.
            instantiate (1 := if (Nat.eq_dec fuel3 0%nat) then word.of_Z 0%Z else word.of_Z 1%Z).
            rewrite <- Nat2Z.inj_add.
            destruct (Nat.eq_dec fuel3 0) as [->|Hne].
            - rewrite PeanoNat.Nat.sub_0_r, Z.ltb_irrefl.
              reflexivity.
            - rewrite (proj1 (Zlt_is_lt_bool _ _)); [reflexivity|].
              apply Nat2Z.inj_lt.
              clear -Hfuel3 Hne. Lia.lia. }
          assert (word.unsigned _ = if Nat.eq_dec fuel3 0 then 0%Z else 1%Z) as ->.
          { destruct (Nat.eq_dec fuel3 0); [apply word.unsigned_of_Z_0|apply word.unsigned_of_Z_1]. }
          split; intro Hb; destruct (Nat.eq_dec fuel3 0) as [->|Hfnz3]; try (clear -Hb; congruence); clear Hb.
          { (* Invariant preservation *)
            assert ((2 ^ (Nat.min m n - fuel) - fuel2) * 2 ^ (n - (Nat.min m n - fuel)) + (2 ^ (n - (Nat.min m n - (fuel - 1))) - fuel3) + 2 ^ (n - (Nat.min m n - (fuel - 1))) < 2 ^ n)%nat as idx_ok.
            { clear -Hfuel Hfuel2 Hfuel3 Hfnz Hfnz2 Hfnz3.
              rewrite Nat.mul_sub_distr_r, <- Nat.pow_add_r.
              assert (Nat.min m n - fuel + _ = n)%nat as -> by Lia.lia.
              assert (2 ^ n - fuel2 * 2 ^ (n - (Nat.min m n - fuel)) + (2 ^ (n - (Nat.min m n - (fuel - 1))) - fuel3) + 2 ^ (n - (Nat.min m n - (fuel - 1))) = 2 ^ n - fuel2 * 2 ^ (n - (Nat.min m n - fuel)) + (2 * 2 ^ (n - (Nat.min m n - (fuel - 1))) - fuel3))%nat as -> by Lia.lia.
              rewrite <- Nat.pow_succ_r'.
              assert (S (n - (Nat.min m n - (fuel - 1))) = (n - (Nat.min m n - fuel)))%nat as -> by Lia.lia.
              generalize (NatUtil.pow_nonzero 2 n ltac:(Lia.lia)).
              generalize (NatUtil.pow_nonzero 2 (Nat.min m n - fuel) ltac:(Lia.lia)).
              generalize (NatUtil.pow_nonzero 2 (n - (Nat.min m n - fuel)) ltac:(Lia.lia)).
              generalize (NatUtil.pow_nonzero 2 (n - (Nat.min m n - (fuel - 1))) ltac:(Lia.lia)).
              generalize (Nat.pow_lt_mono_r 2%nat (n - (Nat.min m n - (fuel - 1)))%nat (n - (Nat.min m n - fuel))%nat ltac:(Lia.lia) ltac:(Lia.lia)).
              intros. assert (2 ^ n - fuel2 * 2 ^ (n - (Nat.min m n - fuel)) + (2 ^ (n - (Nat.min m n - fuel)) - fuel3) = 2 ^ n - (fuel2 - 1) * 2 ^ (n - (Nat.min m n - fuel)) - fuel3)%nat as ->; [|Lia.lia].
              rewrite Nat.add_sub_assoc; [|Lia.lia]. f_equal.
              assert (Nat.pow 2 n = Nat.pow 2 ((Nat.min m n - fuel)+ (n - (Nat.min m n - fuel))))%nat as -> by (f_equal; Lia.lia).
              rewrite Nat.pow_add_r. repeat rewrite <- Nat.mul_sub_distr_r.
              rewrite <- (Nat.mul_1_l (Nat.pow 2 (n - (_ - fuel))))%nat at 2.
              rewrite <- Nat.mul_add_distr_r. f_equal. Lia.lia. }
            repeat straightline. eexists; split; repeat straightline.
            { eexists; split; [eassumption|repeat straightline].
              eexists; split; [eassumption|repeat straightline].
              eexists; split; [eassumption|]. unfold v.
              rewrite <- word.ring_morph_add, <- word.ring_morph_mul, <- Nat2Z.inj_add.
              reflexivity. }
            eexists; split; repeat straightline.
            { unfold l0. rewrite map.get_put_diff by (clear; congruence).
              eexists; split; [eassumption|repeat straightline].
              rewrite map.get_put_diff by (clear; congruence).
              eexists; split; [eassumption|repeat straightline].
              rewrite map.get_put_same.
              eexists; split; [reflexivity|repeat straightline]. }
            assert (Z.of_nat _ + 1 = Z.of_nat (2 ^ (Nat.min m n - fuel) + (2 ^ (Nat.min m n - fuel) - fuel2)))%Z as -> by (clear -Hfuel Hfuel2 Hfnz Hfnz2; Lia.lia).
            assert ((2 ^ (Nat.min m n - fuel) + (2 ^ (Nat.min m n - fuel) - fuel2)) < Nat.pow 2 m)%nat as z_ok.
            { assert (_ + _ = 2 * (Nat.pow 2 (Nat.min m n - fuel)) - fuel2)%nat as -> by (clear -Hfuel Hfuel2 Hfnz Hfnz2; Lia.lia).
              rewrite <- Nat.pow_succ_r'.
              assert (S (_ - _) = Nat.min m n - (fuel - 1))%nat as -> by (clear -Hfuel Hfuel2 Hfnz Hfnz2; Lia.nia).
              apply (Nat.lt_le_trans _ (Nat.pow 2 (Nat.min m n - (fuel - 1)))).
              - pose proof (NatUtil.pow_nonzero 2 (Nat.min m n - (fuel - 1)) ltac:(clear; congruence)) as X.
                clear -X Hfnz2; Lia.lia.
              - apply Nat.pow_le_mono_r; clear; Lia.lia. }
            set (j := ((2 ^ (Nat.min m n - fuel) - fuel2) * 2 ^ (n - (Nat.min m n - fuel)) + (2 ^ (n - (Nat.min m n - (fuel - 1))) - fuel3))%nat).
            set (len4 := (2 ^ (n - (Nat.min m n - (fuel - 1))))%nat).
            assert (length p3  = Nat.pow 2 n)%nat as Xlen.
            { destruct Hseps4 as (mStack4 & mHeap4 & Hsplit4 & Hstk4 & Hseps4).
              eapply Bignums_length; eauto. }
            assert (length z' = Nat.pow 2 m)%nat as Ylen.
            { destruct Hseps4 as (mStack4 & mHeap4 & Hsplit4 & Hstk4 & Hseps4).
              destruct Hseps4 as (? & ? & ? & ? & Hseps4).
              eapply Bignums_length; eauto. }
            unfold felem in Xlen, Ylen.
            assert (Z.of_nat (length p3 * felem_size_in_words) * bytes_per_word width < 2 ^ width) as ZA.
            { unfold felem. rewrite Xlen.
              rewrite Nat2Z.inj_mul, <- Z.mul_assoc.
              exact n_lt_width. }
            assert (Z.of_nat (length z' * felem_size_in_words) * bytes_per_word width < 2 ^ width) as ZB.
            { unfold felem. rewrite Ylen.
              rewrite Nat2Z.inj_mul, <- Z.mul_assoc.
              exact m_lt_width. }
            pose proof Hseps4 as HsepsP.
            seprewrite_in (Bignums_nth_default nil felem_size_in_words (Nat.pow 2 n) p_ptr p3 (j + len4)%nat ltac:(rewrite Xlen; exact idx_ok) idx_ok ZA) HsepsP.
            fold FElem in HsepsP.
            assert (exists RP, (FElem (word.add p_ptr (word.of_Z (felem_size_in_bytes * Z.of_nat (j + len4)))) (nth_default nil p3 (j + len4)) * RP)%sep m3) as HsepsP'.
            { rewrite Z.mul_comm. cbv [felem_size_in_bytes].
              rewrite Z.mul_assoc, <- Nat2Z.inj_mul. eexists; seplog. }
            pose proof Hseps4 as HsepsZ.
            seprewrite_in (Bignums_nth_default nil felem_size_in_words (Nat.pow 2 m) z_ptr z' (2 ^ (Nat.min m n - fuel) + (2 ^ (Nat.min m n - fuel) - fuel2)) ltac:(rewrite Ylen; clear -z_ok; Lia.lia) ltac:(clear -z_ok; Lia.lia) ZB) HsepsZ.
            fold FElem in HsepsZ.
            assert (exists RX, (FElem (word.add z_ptr (word.of_Z (felem_size_in_bytes * Z.of_nat (2 ^ (Nat.min m n - fuel) + (2 ^ (Nat.min m n - fuel) - fuel2))))) (nth_default nil z' (2 ^ (Nat.min m n - fuel) + (2 ^ (Nat.min m n - fuel) - fuel2))) ⋆ RX)%sep m3) as HsepsZ'.
            { rewrite Z.mul_comm. cbv [felem_size_in_bytes].
              rewrite Z.mul_assoc, <- Nat2Z.inj_mul. eexists; seplog. }
            pose proof (proj1 (Forall_nth _ _) Hbounded3 (j + len4)%nat nil ltac:(unfold felem; rewrite Xlen; clear -idx_ok; Lia.lia)) as Xbounded.
            rewrite <- nth_default_eq in Xbounded.
            pose proof (proj1 (Forall_nth _ _) H5 (2 ^ (Nat.min m n - fuel) + (2 ^ (Nat.min m n - fuel) - fuel2))%nat nil ltac:(unfold felem in *; rewrite Ylen; exact z_ok)) as Ybounded.
            rewrite <- nth_default_eq in Ybounded.
            straightline_call; [repeat split; eauto|].
            { cbv [bin_xbounds bin_mul]. apply Field.relax_bounds. assumption. }
            { cbv [bin_ybounds bin_mul]. apply Field.relax_bounds. assumption. }
            clear HsepsZ' HsepsP'.
            do 7 straightline.
            eexists; split; [reflexivity|].
            repeat straightline.
            eexists; split; [repeat straightline|].
            { unfold l0. rewrite map.get_put_diff by (clear; congruence).
              eexists; split; [eassumption|repeat straightline].
              rewrite map.get_put_diff by (clear; congruence).
              eexists; split; [eassumption|].
              unfold v. rewrite <- word.ring_morph_mul, Z.mul_comm.
              cbv [felem_size_in_bytes]. rewrite Z.mul_assoc, <- Nat2Z.inj_mul.
              reflexivity. }
            repeat straightline.
            eexists; split; repeat straightline.
            { unfold l1, l0. rewrite map.get_put_diff by (clear; congruence).
              rewrite map.get_put_same. eexists; split; [reflexivity|repeat straightline].
              rewrite map.get_put_same. eexists; split; [reflexivity|repeat straightline].
              repeat rewrite map.get_put_diff by (clear; congruence).
              eexists; split; [eassumption|repeat straightline]. }
            cbv [felem_size_in_bytes].
            rewrite Z.mul_comm, Z.mul_assoc, <- Nat2Z.inj_mul.
            fold j len4.
            pose proof H13 as Hx.
            seprewrite_in (Bignums_nth_default nil felem_size_in_words (Nat.pow 2 n) p_ptr p3 (j + len4)%nat ltac:(rewrite Xlen; exact idx_ok) idx_ok ZA) Hx.
            fold FElem in Hx.
            assert (exists Rr, (FElem a x0 * Rr)%sep a1) as Hr by (eexists; seplog).
            assert ((FElem (word.add p_ptr (word.of_Z (Z.of_nat ((j + len4) * felem_size_in_words) * bytes_per_word width))) (nth_default nil p3 (j + len4)) * ((Bignums felem_size_in_words (Nat.min (j + len4) (2 ^ n)) p_ptr (List.firstn (j + len4) p3)) * (Bignums felem_size_in_words (2 ^ n - (j + len4 + 1)) (word.add p_ptr (word.of_Z (Z.of_nat ((j + len4 + 1) * felem_size_in_words) * bytes_per_word width))) (List.skipn (j + len4 + 1) p3)) * (FElem a x0 ⋆ (Bignums felem_size_in_words (2 ^ m) z_ptr z' ⋆ R))))%sep a1) as XX by seplog.
            seprewrite_in (Bignums_nth_default nil felem_size_in_words (Nat.pow 2 n) p_ptr p3 (j)%nat ltac:(rewrite Xlen; clear -idx_ok; Lia.lia) ltac:(clear -idx_ok; Lia.lia) ZA) H13.
            fold FElem in H13.
            assert (exists Ry, (FElem (word.add p_ptr (word.of_Z (Z.of_nat ((j) * felem_size_in_words) * bytes_per_word width))) (nth_default nil p3 (j)) * Ry)%sep a1) as Hy' by (eexists; seplog).
            straightline_call; repeat split.
            3: exact Hy'.
            3: exact Hr.
            3: exact XX.
            2: assumption.
            { rewrite nth_default_eq.
              apply (proj1 (Forall_nth _ _) Hbounded3).
              unfold felem. rewrite Xlen. clear -idx_ok; Lia.lia. }
            repeat straightline.
            eexists; split; repeat straightline.
            { unfold l1, l0.
              rewrite map.get_put_same.
              eexists; split; [reflexivity|repeat straightline].
              rewrite map.get_put_same.
              eexists; split; [reflexivity|repeat straightline].
              repeat (rewrite map.get_put_diff by (clear; congruence)).
              eexists; split; [eassumption|repeat straightline]. }
            fold j len4.
            assert (((Bignums felem_size_in_words (Nat.pow 2 n) p_ptr (set_nth (j + len4)%nat x3 p3)) * (FElem a x0 ⋆ (Bignums felem_size_in_words (2 ^ m) z_ptr z' ⋆ R)))%sep a3) as Hseps5.
            { seplog.
              rewrite (Bignums_set_nth felem_size_in_words (Nat.pow 2 n) p_ptr p3 (j + len4)%nat x3 ltac:(rewrite Xlen; exact idx_ok) idx_ok ZA).
              cbv [seps].
              cancel.
              cancel_seps_at_indices 0%nat 1%nat; [reflexivity|].
              reflexivity. }
            seprewrite_in (Bignums_nth_default nil felem_size_in_words (Nat.pow 2 n) p_ptr (set_nth (j+ len4)%nat x3 p3) (j)%nat ltac:(rewrite length_set_nth, Xlen; clear -idx_ok; Lia.lia) ltac:(clear -idx_ok; Lia.lia) ltac:(rewrite length_set_nth; apply ZA)) Hseps5.
            fold FElem in Hseps5.
            straightline_call.
            { repeat split.
              4: instantiate (1 := x0); eexists; seplog.
              3:{ instantiate (1 := (nth_default nil (set_nth (j + len4) x3 p3) j)).
                  eexists; seplog.
                  cancel_seps_at_indices 1%nat 0%nat; [reflexivity|].
                  cancel. }
              2: assumption.
              2:{ instantiate (2 := (nth_default nil (set_nth (j + len4) x3 p3) j)).
                  seplog. cancel_seps_at_indices 1%nat 0%nat; [reflexivity|].
                  cancel. }
              rewrite set_nth_nth_default by (rewrite Xlen; clear -idx_ok; Lia.lia).
              assert (0 < len4)%nat as WW by (clear; pose proof (NatUtil.pow_nonzero 2 (n - (Nat.min m n - (fuel - 1))) ltac:(congruence)); Lia.lia).
              destruct (Nat.eq_dec _ _) as [He|_]; [clear -He WW; Lia.lia|].
              rewrite nth_default_eq.
              eapply Forall_nth; eauto.
              rewrite Xlen; clear -idx_ok; Lia.lia. }
            repeat straightline.
            eexists; split; repeat straightline.
            { unfold l1, l0. repeat rewrite map.get_put_diff by (clear; congruence).
              eexists; split; [eassumption|repeat straightline]. }
            exists (fuel3 - 1)%nat. split; [|clear -Hfnz3; Lia.lia].
            unfold loop_inv3. split; [clear -Hfuel3; Lia.lia|].
            split; [reflexivity|].
            exists (set_nth j x4 (set_nth (j + len4)%nat x3 p3)).
            rewrite set_nth_nth_default in H19 by (rewrite Xlen; clear -idx_ok; Lia.lia).
            assert (0 < len4)%nat as WW by (clear; pose proof (NatUtil.pow_nonzero 2 (n - (Nat.min m n - (fuel - 1))) ltac:(congruence)); Lia.lia).
            destruct (Nat.eq_dec _ _) as [He|_]; [clear -He WW; Lia.lia|].
            unfold l2, l1, l0.
            repeat split; repeat (rewrite map.get_put_diff by (clear; congruence)); try rewrite map.get_put_same; try assumption.
            3:{ rewrite <- word.ring_morph_add.
                assert (1%Z = Z.of_nat 1) as -> by reflexivity.
                rewrite <- Nat2Z.inj_add. do 3 f_equal.
                clear -Hfnz3 Hfuel3 idx_ok. Lia.lia. }
            2:{ assert (bounded_by tight_bounds x4) by (simpl in *; rewrite <- loose_bounds_eq_tight_bounds; assumption).
                apply Forall_set_nth; [|assumption].
                assert (bounded_by tight_bounds x3) by (simpl in *; rewrite <- loose_bounds_eq_tight_bounds; assumption).
                apply Forall_set_nth; assumption. }
            2:{ exists x0. seplog.
                rewrite (Bignums_set_nth felem_size_in_words (Nat.pow 2 n) p_ptr (set_nth (j + len4)%nat x3 p3) j x4 ltac:(rewrite length_set_nth, Xlen; clear -idx_ok; Lia.lia) ltac:(clear -idx_ok; Lia.lia) ltac:(rewrite length_set_nth; apply ZA)).
                cancel. cbv [seps]. cancel. reflexivity. }
            assert (2 ^ (n - (Nat.min m n - (fuel - 1))) - (fuel3 - 1) = S (2 ^ (n - (Nat.min m n - (fuel - 1))) - fuel3))%nat as -> by (clear -Hfnz3 Hfuel3 idx_ok; Lia.lia).
            unfold polynomial_decompose_loop'. rewrite seq_S, fold_left_app.
            assert (fold_left _ (seq _ _) _ = (polynomial_decompose_loop' (2 ^ (n - (Nat.min m n - (fuel - 1))) - fuel3)%nat ((2 ^ (Nat.min m n - fuel) - fuel2) * 2 ^ (n - (Nat.min m n - fuel))) (2 ^ (n - (Nat.min m n - (fuel - 1))))%nat (nth_default 0%F zetas (2 ^ (Nat.min m n - fuel) - 1 + 2 ^ (Nat.min m n - fuel) - fuel2 + 1)) px2))%nat as -> by reflexivity.
            cbn [fold_left]. fold j len4.
            apply Forall2_set_nth; auto.
            2:{ rewrite H19. cbv [bin_model bin_add].
                rewrite H11. cbv [bin_model bin_mul].
                rewrite (proj1 (Forall2_forall_iff _ _ _ 0%F nil (Forall2_length HF3)) HF3 j ltac:(rewrite (Forall2_length HF3); unfold felem; rewrite Xlen; clear -idx_ok; Lia.lia)).
                rewrite (proj1 (Forall2_forall_iff _ _ _ 0%F nil (Forall2_length H3)) H3 (2 ^ (Nat.min m n - fuel) + (2 ^ (Nat.min m n - fuel) - fuel2))%nat ltac:(rewrite (Forall2_length H3); unfold felem; rewrite Ylen; clear -z_ok; Lia.lia)).
                rewrite (proj1 (Forall2_forall_iff _ _ _ 0%F nil (Forall2_length HF3)) HF3 (j + len4)%nat ltac:(rewrite (Forall2_length HF3); unfold felem; rewrite Xlen; clear -idx_ok; Lia.lia)).
                fold j len4. do 3 f_equal.
                clear -Hfnz Hfnz2 Hfnz3 Hfuel Hfuel2 Hfuel3; Lia.lia. }
            apply Forall2_set_nth; auto.
            rewrite H16. cbv [bin_model bin_sub].
            rewrite H11. cbv [bin_model bin_mul].
            rewrite (proj1 (Forall2_forall_iff _ _ _ 0%F nil (Forall2_length HF3)) HF3 j ltac:(rewrite (Forall2_length HF3); unfold felem; rewrite Xlen; clear -idx_ok; Lia.lia)).
                rewrite (proj1 (Forall2_forall_iff _ _ _ 0%F nil (Forall2_length H3)) H3 (2 ^ (Nat.min m n - fuel) + (2 ^ (Nat.min m n - fuel) - fuel2))%nat ltac:(rewrite (Forall2_length H3); unfold felem; rewrite Ylen; clear -z_ok; Lia.lia)).
                rewrite (proj1 (Forall2_forall_iff _ _ _ 0%F nil (Forall2_length HF3)) HF3 (j + len4)%nat ltac:(rewrite (Forall2_length HF3); unfold felem; rewrite Xlen; clear -idx_ok; Lia.lia)).
                fold j len4. do 3 f_equal.
                clear -Hfnz Hfnz2 Hfnz3 Hfuel Hfuel2 Hfuel3; Lia.lia. }
          repeat straightline.
          eexists; split; repeat straightline.
          { eexists; split; [eassumption|repeat straightline].
            eexists; split; [eassumption|repeat straightline]. }
          exists (fuel2 - 1)%nat. split; [|clear -Hfnz2; Lia.lia].
          unfold loop_inv2. split; [clear -Hfuel2; Lia.lia|].
          split; [reflexivity|].
          exists p3. eexists. unfold l0.
          repeat split; try (rewrite map.get_put_diff by (clear; congruence)); try rewrite map.get_put_same; try eassumption.
          2:{ rewrite Hm4. do 2 f_equal.
              clear -Hfuel2 Hfnz2; Lia.lia. }
          2:{ rewrite <- word.ring_morph_add, <- Nat2Z.inj_add.
              do 2 f_equal. clear -Hfuel2 Hfnz2 Hfuel Hfnz; Lia.nia. }
          2:{ exists a_stk4; assumption. }
          assert (2 ^ (Nat.min m n - fuel) - (fuel2 - 1) = S (2 ^ (Nat.min m n - fuel) - fuel2))%nat as -> by (clear -Hfuel2 Hfnz2; Lia.lia).
          rewrite Nat.sub_0_r.
          unfold polynomial_list_loop. rewrite seq_S, fold_left_app.
          assert (fold_left _ (seq _ _) _ = polynomial_list_loop zetas (2 ^ (Nat.min m n - fuel) - fuel2) (2 ^ (n - (Nat.min m n - fuel))) (2 ^ (n - (Nat.min m n - (fuel - 1)))) ((2 ^ (Nat.min m n - fuel) - 1)%nat, 0%nat, px'))%nat as -> by reflexivity.
          rewrite Heq2. cbn [fold_left]. f_equal; f_equal; try (clear -Hfuel2 Hfnz2; Lia.lia).
          rewrite polynomial_decompose_loop_eq. f_equal. f_equal.
          clear -Hfuel2 Hfnz2; Lia.lia. }
        exists (fuel - 1)%nat. split; [|clear -Hfnz; Lia.lia].
        unfold loop_inv1. split; [clear -Hfuel; Lia.lia|].
        split; [reflexivity|].
        exists p2, px2. rewrite PeanoNat.Nat.sub_0_r in *.
        repeat split; eauto.
        2:{ rewrite Hm2. do 3 f_equal.
            assert (Nat.min m n - (fuel - 1) = S (Nat.min m n - fuel))%nat as -> by (clear -Hfuel Hfnz; Lia.lia).
            rewrite Nat.pow_succ_r'. clear. Lia.lia. }
        assert (Nat.min m n - (fuel - 1) = S (Nat.min m n - fuel))%nat as -> by (clear -Hfnz Hfuel; Lia.lia).
        unfold polynomial_layer_decomposition_loop. rewrite seq_S, fold_left_app.
        assert (fold_left _ (seq _ _) _ = polynomial_layer_decomposition_loop zetas 0%nat (Nat.min m n - fuel) (0%nat, (2 ^ n)%nat, p))%nat as -> by reflexivity.
        rewrite HF1. cbn [fold_left].
        rewrite PeanoNat.Nat.add_0_l, Nat.shiftl_1_l.
        rewrite Nat.shiftr_div_pow2, <- Nat.pow_sub_r.
        2: clear; congruence.
        2: clear -Hfuel Hfnz; Lia.lia.
        assert (2 ^ (n - (Nat.min m n - fuel) - 1) = 2 ^ (n - (Nat.min m n - (fuel - 1))))%nat as -> by (f_equal; clear -Hfuel Hfnz; Lia.lia).
        rewrite Heq2. f_equal. f_equal.
        2: f_equal; clear -Hfuel Hfnz; Lia.lia.
        rewrite PeanoNat.Nat.pow_succ_r'. clear; Lia.lia. }
      destruct Hseps as (mStack' & m' & Hsplit & Hstk & Hseps).
      exists m', mStack'. unfold FElem in Hstk.
      cbv [felem_size_in_bytes]. apply Bignum_as_anybytes in Hstk.
      split; [exact Hstk|]. split; [rewrite map.split_comm; auto|].
      do 2 (split; [reflexivity|]).
      rewrite PeanoNat.Nat.sub_0_r in HF1.
      unfold NTT_gallina. rewrite HF1. eexists; repeat split; eauto.
      seplog.
    Qed.

    (* Lemma br2_ntt_inverse_ok: *)
    (*   program_logic_goal_for br2_ntt_inverse *)
    (*     (forall functions : map.rep, *)
    (*         map.get functions ntt_inverse = Some br2_ntt_inverse -> *)
    (*         spec_of_mul functions -> *)
    (*         spec_of_sub functions -> spec_of_add functions -> spec_of_ntt_inverse functions). *)
    (* Proof. *)
    (*   Local Opaque Memory.bytes_per to_byte_table Z.pow Z.of_nat List.map Z.div Z.sub Z.add Nat.sub Nat.min F.F word_of_F F.pow Nat.pow F.to_Z. *)
    (*   assert (len_chunk1: forall A (l: list A), length (List.chunk 1 l) = length l). *)
    (*   { intros; rewrite List.length_chunk by congruence. *)
    (*     rewrite <- (PeanoNat.Nat.mul_1_r (length l)), List.Nat.div_up_exact; Lia.lia. } *)
    (*   repeat straightline. unfold NTT_inverse_gallina. *)
    (*   apply wp_while. *)
    (*   set (inverse_layer_recomposition_loop' := *)
    (*          fun zetas k r state => *)
    (*            fold_left *)
    (*              (fun (state0 : nat * nat * list (ModularArithmetic.F q)) (i : nat) => *)
    (*                 let *)
    (*                   '(l, len, p) := state0 in *)
    (*                 let start := 0%nat in *)
    (*                 let old_len := len in *)
    (*                 let len0 := Init.Nat.shiftl len 1 in *)
    (*                 let *)
    (*                   '(l0, _, p1) := *)
    (*                   inverse_polynomial_list_loop zetas (Init.Nat.shiftl 1 (r - 1 - i)) *)
    (*                     old_len len0 (l, start, p) in (l0, len0, p1)) (seq 0 k) state). *)
    (*   assert (recomposition_loop_eq: forall zetas r state, inverse_layer_recomposition_loop' zetas r r state = inverse_layer_recomposition_loop zetas r state) by reflexivity. *)
    (*   set (loop_inv1 := fun (fuel1: nat) (tr': Semantics.trace) (mem': mem) (loc': locals) => *)
    (*                       (fuel1 <= Nat.min m n)%nat /\ *)
    (*                         tr' = tr /\ *)
    (*                         map.get loc' "p" = Some p_ptr /\ *)
    (*                         let i := (Nat.min m n - fuel1)%nat in *)
    (*                         exists p' px', *)
    (*                           inverse_layer_recomposition_loop' zetas i (Nat.min m n) (Init.Nat.shiftl 1 (Nat.min m n), Init.Nat.shiftl 1 (n - Nat.min m n), p) = (Nat.pow 2 fuel1, Nat.pow 2 (n - fuel1), px')%nat /\ *)
    (*                             Forall2 (fun x y => feval y = Some x) px' p' /\ *)
    (*                             map.get loc' "l" = Some (word.of_Z (Z.of_nat (Nat.pow 2 fuel1))) /\ *)
    (*                             map.get loc' "len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - fuel1)))) /\ *)
    (*                             (Bignums 1 (2 ^ n) p_ptr (List.chunk 1 p') ⋆ R)%sep mem'). *)
    (*   exists nat, lt, loop_inv1; split; [apply lt_wf|]. split. *)
    (*   { (* loop_inv1 holds at beginning *) *)
    (*     exists (Nat.min m n). repeat split; [reflexivity|unfold l1, l0; repeat (rewrite map.get_put_diff by congruence); apply map.get_put_same|]. *)
    (*     rewrite Nat.sub_diag. intros; subst i. *)
    (*     exists x, p. repeat split; auto. *)
    (*     2: unfold l1, l0; repeat (rewrite map.get_put_diff by (clear; congruence)); apply map.get_put_same. *)
    (*     2: apply map.get_put_same. *)
    (*     cbn. do 2 rewrite Nat.shiftl_1_l. reflexivity. } *)
    (*   intros fuel1 ? mem1 loc1 Hinv1. *)
    (*   destruct Hinv1 as (Hfuel1 & -> & Hptr1 & p1 & px1 & Heq1 & HF1 & Hm1 & Hlen1 & Hp1). *)
    (*   eexists; split. *)
    (*   { repeat straightline. *)
    (*     eexists; split; [eassumption|reflexivity]. } *)
    (*   rewrite <- Core.word.morph_ltu. *)
    (*   2-3: split; try Lia.lia. *)
    (*   2-3: rewrite Nat2Z.inj_pow. *)
    (*   2-3: apply Zpow_facts.Zpower_lt_monotone; Lia.lia. *)
    (*   assert (word.unsigned (if (_ <? _)%Z then _ else _) = if Nat.eq_dec fuel1 0%nat then 0%Z else 1%Z) as ->. *)
    (*   { match goal with | |- context [(Z.of_nat ?a <? Z.of_nat ?b)] => generalize (Zlt_cases (Z.of_nat a) (Z.of_nat b)); intro Hcond1 end. *)
    (*     destruct (Nat.eq_dec fuel1 0) as [->|Hfnz1]. *)
    (*     - rewrite PeanoNat.Nat.sub_0_r in *. *)
    (*       destruct (_ <? _); [clear -Hcond1; Lia.lia|]. *)
    (*       apply word.unsigned_of_Z_0. *)
    (*     - destruct (_ <? _); [apply word.unsigned_of_Z_1|]. *)
    (*       apply Nat2Z.inj_ge, Nat.pow_le_mono_r_iff in Hcond1; clear -Hcond1 Hfnz1 Hfuel1; Lia.lia. } *)
    (*   split; intros Hb; destruct (Nat.eq_dec fuel1 0) as [->|Hfnz1]; try (clear -Hb; congruence); clear Hb. *)
    (*   { (* loop_inv1 preserved *) *)
    (*     repeat straightline. eexists; split; repeat straightline. *)
    (*     { unfold l0; rewrite map.get_put_diff by (clear; congruence). *)
    (*       eexists; split; [eassumption|reflexivity]. } *)
    (*     eexists; split; repeat straightline. *)
    (*     { unfold l1, l0; do 2 (rewrite map.get_put_diff by (clear; congruence)). *)
    (*       eexists; split; [eassumption|repeat straightline]. } *)
    (*     apply wp_while. *)
    (*     set (loop_inv2 := fun (fuel2: nat) (tr': Semantics.trace) (mem': mem) (loc': locals) => *)
    (*                         (fuel2 <= Nat.pow 2 (fuel1 - 1))%nat /\ *)
    (*                           tr' = tr /\ *)
    (*                           map.get loc' "p" = Some p_ptr /\ *)
    (*                           let i := ((Nat.pow 2 (fuel1 - 1)) - fuel2)%nat in *)
    (*                           exists p' px', *)
    (*                             inverse_polynomial_list_loop zetas i (Nat.pow 2 (n - fuel1))%nat (Nat.pow 2 (n - (fuel1 - 1)))%nat (Nat.pow 2 fuel1, 0, px1)%nat = (Nat.pow 2 fuel1 - i, (i * (2 ^ (n - (fuel1 - 1)))), px')%nat  /\ *)
    (*                               Forall2 (fun x y => feval y = Some x) px' p' /\ *)
    (*                               map.get loc' "l" = Some (word.of_Z (Z.of_nat ((2 ^ fuel1) - i))) /\ *)
    (*                               map.get loc' "len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - (fuel1 - 1))))) /\ *)
    (*                               map.get loc' "old_len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - fuel1)))) /\ *)
    (*                               map.get loc' "start" = Some (word.of_Z (Z.of_nat (i * (2 ^ (n - (fuel1 - 1)))))) /\ *)
    (*                               (Bignums 1 (2 ^ n) p_ptr (List.chunk 1 p') ⋆ R)%sep mem'). *)
    (*     exists nat, lt, loop_inv2. split; [apply lt_wf|]. *)
    (*     split. *)
    (*     { (* loop_inv2 holds at start *) *)
    (*       exists (Nat.pow 2 (fuel1 - 1)). repeat split; [reflexivity|..]. *)
    (*       - unfold l2, l1, l0. repeat (rewrite map.get_put_diff by (clear; congruence)). auto. *)
    (*       - rewrite Nat.sub_diag. intro; subst i. *)
    (*         rewrite Nat.sub_0_r, Nat.mul_0_l. *)
    (*         unfold l2, l1, l0. repeat (rewrite map.get_put_diff by (clear; congruence)). *)
    (*         exists p1, px1; repeat split; auto; repeat (rewrite map.get_put_diff by (clear; congruence)); rewrite map.get_put_same; auto. *)
    (*         rewrite <- Core.word.morph_shiftl by Lia.lia. *)
    (*         f_equal. f_equal. rewrite Z.shiftl_mul_pow2 by Lia.lia. *)
    (*         assert (2 ^ 1 = Z.of_nat (2 ^ 1)) as -> by reflexivity. *)
    (*         rewrite <- Nat2Z.inj_mul, <- Nat.pow_add_r. f_equal. *)
    (*         f_equal. clear -Hfuel1 Hfnz1. Lia.lia. } *)
    (*     intros fuel2 ? mem2 loc2 Hinv2. *)
    (*     destruct Hinv2 as (Hfuel2 & -> & Hptr2 & p2 & px2 & Heq2 & HF2 & Hm2 & Hlen2 & Hold_len2 & Hstart2 & Hp2). *)
    (*     eexists; split. *)
    (*     { repeat straightline. *)
    (*       eexists; split; [eassumption|reflexivity]. } *)
    (*     rewrite <- Core.word.morph_ltu. *)
    (*     3: split; [|rewrite Nat2Z.inj_pow; apply Zpow_facts.Zpower_lt_monotone]; Lia.lia. *)
    (*     2: split; [Lia.nia|]. *)
    (*     2: apply (Z.le_lt_trans _ (Z.of_nat (Nat.pow 2 n))). *)
    (*     3: rewrite Nat2Z.inj_pow; apply Zpow_facts.Zpower_lt_monotone; Lia.lia. *)
    (*     2: apply Nat2Z.inj_le; rewrite Nat.mul_sub_distr_r, <- Nat.pow_add_r. *)
    (*     2: assert (_ + (_ - _) = n)%nat as -> by Lia.lia; Lia.lia. *)
    (*     assert (word.unsigned _ = if (Nat.eq_dec fuel2 0) then 0%Z else 1%Z) as ->. *)
    (*     { rewrite Nat.mul_sub_distr_r, <- Nat.pow_add_r. *)
    (*       assert (_ + (_ - _) = n)%nat as -> by Lia.lia. *)
    (*       destruct (Nat.eq_dec fuel2 0) as [->|Hfnz2]. *)
    (*       - rewrite Nat.sub_0_r. *)
    (*         match goal with | |- context [(Z.of_nat ?a <? Z.of_nat ?b)] => generalize (Zlt_cases (Z.of_nat a) (Z.of_nat b)); intro Hcond2 end. *)
    (*         destruct (_ <? _); [clear -Hcond2; Lia.lia|apply word.unsigned_of_Z_0]. *)
    (*       - match goal with | |- context [(Z.of_nat ?a <? Z.of_nat ?b)] => generalize (Zlt_cases (Z.of_nat a) (Z.of_nat b)); intro Hcond2 end. *)
    (*         destruct (_ <? _); [apply word.unsigned_of_Z_1|]. *)
    (*         clear -Hcond2 Hfuel2 Hfnz2 Hfuel1; apply Nat2Z.inj_ge in Hcond2. *)
    (*         pose proof (NatUtil.pow_nonzero 2 n ltac:(congruence)). *)
    (*         pose proof (NatUtil.pow_nonzero 2 (n - (fuel1 - 1)) ltac:(congruence)). *)
    (*         Lia.lia. } *)
    (*     split; intros Hb; destruct (Nat.eq_dec fuel2 0) as [->|Hfnz2]; try (clear -Hb; congruence); clear Hb. *)
    (*     { (* loop_inv2 is preserved *) *)
    (*       repeat straightline. eexists; split; repeat straightline. *)
    (*       { eexists; split; [eassumption|reflexivity]. } *)
    (*       eexists; split; repeat straightline. *)
    (*       { unfold l0. rewrite map.get_put_same. *)
    (*         rewrite <- word.ring_morph_sub. *)
    (*         assert (Nat.pow 2 fuel1 = 2 * (Nat.pow 2 (fuel1 - 1)))%nat as -> by (rewrite <- Nat.pow_succ_r'; f_equal; Lia.lia). *)
    (*         assert (1%Z = Z.of_nat 1) as -> by reflexivity. *)
    (*         rewrite <- Nat2Z.inj_sub by (clear -Hfuel2 Hfnz2; Lia.nia). *)
    (*         assert (2 * _ - _ - _ = Nat.pow 2 (fuel1 - 1) + (fuel2 - 1))%nat as -> by Lia.lia. *)
    (*         eexists; split; [reflexivity|]. repeat straightline. *)
    (*         unfold v. rewrite <- word.ring_morph_mul by (Lia.nia). *)
    (*         erewrite (load_from_word_table _ _ (word_of_F F.zero)); auto. *)
    (*         2:{ rewrite length_to_byte_table, length_map. *)
    (*             rewrite zetas_length_ok. assert (width / 8 = 4 \/ width / 8 = 8) as Hw. *)
    (*             { clear -BW. *)
    (*               destruct width_cases as [-> | ->]; [left|right]; reflexivity. } *)
    (*             rewrite Nat2Z.inj_mul, Z2Nat.id by (clear -Hw; destruct Hw; Lia.lia). *)
    (*             rewrite Nat2Z.inj_pow. *)
    (*             transitivity (2 ^ 3 * 2 ^ Z.of_nat m). *)
    (*             - apply Z.mul_le_mono_nonneg_r. *)
    (*               + apply Z.lt_le_incl, ZLib.Z.pow2_pos, Nat2Z.is_nonneg. *)
    (*               + clear -Hw. destruct Hw as [-> | ->]; Lia.lia. *)
    (*             - rewrite <- Z.pow_add_r by Lia.lia. *)
    (*               apply Z.pow_le_mono_r; clear -mp3_le_with; Lia.lia. } *)
    (*         2:{ rewrite length_map, zetas_length_ok. *)
    (*             eapply (Nat.lt_le_trans _ (2 ^ (Nat.min m n))%nat). *)
    (*             + eapply (Nat.lt_le_trans _ (2 ^ fuel1)%nat). *)
    (*               * assert (Nat.pow 2 fuel1 = 2 * Nat.pow 2 (fuel1 - 1))%nat as -> by (rewrite <- Nat.pow_succ_r'; f_equal; Lia.lia). *)
    (*                 clear -Hfuel2 Hfnz2; Lia.lia. *)
    (*               * apply Nat.pow_le_mono; clear -Hfuel1; Lia.lia. *)
    (*             + apply Nat.pow_le_mono; clear; Lia.lia. } *)
    (*         rewrite <- nth_default_eq. eexists; split; reflexivity. } *)
    (*       eexists; split; repeat straightline. *)
    (*       { unfold l1, l0. do 2 (rewrite map.get_put_diff by (clear; congruence)). *)
    (*         eexists; split; [eassumption|reflexivity]. } *)
    (*       apply wp_while. *)
    (*       set (v' := nth_default (word_of_F 0) (map word_of_F zetas) (2 ^ (fuel1 - 1) + (fuel2 - 1))). *)
    (*       set (v := nth_default 0%F zetas (2 ^ (fuel1 - 1) + (fuel2 - 1))). *)
    (*       assert (Hv_eq: v' = word_of_F v). *)
    (*       { unfold v', v. apply ListUtil.map_nth_default_always. } *)
    (*       set (loop_inv3 := fun (fuel3: nat) (tr': Semantics.trace) (mem': mem) (loc': locals) => *)
    (*                           (fuel3 <= Nat.pow 2 (n - fuel1))%nat /\ *)
    (*                             tr' = tr /\ *)
    (*                             map.get loc' "p" = Some p_ptr /\ *)
    (*                             let i := ((Nat.pow 2 (n - fuel1)) - fuel3)%nat in *)
    (*                             let px3 := inverse_polynomial_recompose_loop i (((2 ^ (fuel1 - 1) - fuel2) * 2 ^ (n - (fuel1 - 1)))) ((2 ^ (n - fuel1))) v px2 in *)
    (*                             exists p', *)
    (*                               Forall2 (fun x y => feval y = Some x) px3 p' /\ *)
    (*                                 map.get loc' "l" = Some (word.of_Z (Z.of_nat (2 ^ fuel1 - (2 ^ (fuel1 - 1) - fuel2) - 1))) /\ *)
    (*                                 map.get loc' "len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - (fuel1 - 1))))) /\ *)
    (*                                 map.get loc' "old_len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - fuel1)))) /\ *)
    (*                                 map.get loc' "start" = Some (word.of_Z (Z.of_nat ((2 ^ (fuel1 - 1) - fuel2) * 2 ^ (n - (fuel1 - 1))))) /\ *)
    (*                                 map.get loc' "j" = Some (word.of_Z (Z.of_nat ((2 ^ (fuel1 - 1) - fuel2) * 2 ^ (n - (fuel1 - 1)) + i))) /\ *)
    (*                                 map.get loc' "z" = Some v' /\ *)
    (*                                 (Bignums 1 (2 ^ n) p_ptr (List.chunk 1 p') ⋆ R)%sep mem'). *)
    (*       exists nat, lt, loop_inv3. split; [apply lt_wf|]. *)
    (*       split. *)
    (*       { (* loop_inv3 holds at beginning *) *)
    (*         exists (Nat.pow 2 (n - fuel1)). unfold l2, l1, l0. *)
    (*         repeat split; [reflexivity|..]. *)
    (*         - repeat (rewrite map.get_put_diff by (clear; congruence)); auto. *)
    (*         - exists p2. repeat split; auto; repeat (rewrite map.get_put_diff by (clear; congruence)); try rewrite map.get_put_same; auto. *)
    (*           + rewrite Nat.sub_diag. assert (inverse_polynomial_recompose_loop _ _ _ _ _ = px2) as -> by reflexivity; assumption. *)
    (*           + rewrite <- word.ring_morph_sub. *)
    (*             assert (1%Z = Z.of_nat 1) as -> by reflexivity. *)
    (*             rewrite <- Nat2Z.inj_sub; [reflexivity|]. *)
    (*             assert (Nat.pow 2 fuel1 = 2 * Nat.pow 2 (fuel1 - 1))%nat as -> by (rewrite <- Nat.pow_succ_r'; f_equal; Lia.lia). *)
    (*             clear -Hfuel2 Hfnz2; Lia.lia. *)
    (*           + rewrite Nat.sub_diag, Nat.add_0_r. reflexivity. } *)
    (*       intros fuel3 ? mem3 loc3 Hinv3. *)
    (*       destruct Hinv3 as (Hfuel3 & -> & Hptr3 & p3 & HF3 & Hm3 & Hlen3 & Hold_len3 & Hstart3 & Hj3 & Hz3 & Hp3). *)
    (*       eexists; split. *)
    (*       { repeat straightline. *)
    (*         eexists; split; [eassumption|repeat straightline]. *)
    (*         eexists; split; [eassumption|repeat straightline]. *)
    (*         eexists; split; [eassumption|repeat straightline]. } *)
    (*       rewrite <- word.ring_morph_add, <- Nat2Z.inj_add. *)
    (*       rewrite <- Core.word.morph_ltu. *)
    (*       2-3: split; [apply Zle_0_nat|]. *)
    (*       2: apply (Z.le_lt_trans _ (Z.of_nat ((2 ^ (fuel1 - 1) - fuel2) * 2 ^ (n - (fuel1 - 1)) + 2 ^ (n - fuel1)))); [apply Nat2Z.inj_le; clear; Lia.lia|]. *)
    (*       2-3: assert (Z.pow 2 width = Z.of_nat (Nat.pow 2 (Z.to_nat width))) as -> by (rewrite Nat2Z.inj_pow, Z2Nat.id; clear -mp3_le_with; Lia.lia). *)
    (*       2-3: apply Nat2Z.inj_lt. *)
    (*       2-3: eapply (Nat.le_lt_trans _ (Nat.pow 2 n)); [|apply Nat.pow_lt_mono_r; auto]. *)
    (*       2-3: rewrite Nat.mul_sub_distr_r, <- PeanoNat.Nat.pow_add_r. *)
    (*       2-3: assert (fuel1 - 1 + _ = n)%nat as -> by (clear -Hfnz1 Hfuel1; Lia.lia). *)
    (*       2-3: rewrite <- (Nat.mul_1_l (Nat.pow 2 (n - fuel1))). *)
    (*       2-3: assert (n - (fuel1 - 1) = S (n - fuel1))%nat as -> by (clear -Hfnz1 Hfuel1; Lia.lia). *)
    (*       2-3: rewrite Nat.pow_succ_r'. *)
    (*       2-3: assert (Nat.pow 2 n = (Nat.pow 2 fuel1) * (Nat.pow 2 (n - fuel1)))%nat as -> by (rewrite <- Nat.pow_add_r; f_equal; Lia.lia). *)
    (*       2-3: rewrite Nat.mul_assoc, <- Nat.mul_sub_distr_r, <- Nat.mul_add_distr_r. *)
    (*       2-3: apply Nat.mul_le_mono_r. *)
    (*       2-3: generalize (Nat.pow_nonzero 2 fuel1 ltac:(Lia.lia)); clear -Hfuel1 Hfnz1 Hfuel2 Hfnz2; Lia.lia. *)
    (*       assert (word.unsigned _ = if Nat.eq_dec fuel3 0 then 0%Z else 1%Z) as ->. *)
    (*       { destruct (Nat.eq_dec fuel3 0) as [->|Hfnz3]. *)
    (*         - rewrite Nat.sub_0_r, Z.ltb_irrefl. *)
    (*           apply word.unsigned_of_Z_0. *)
    (*         - match goal with | |- context [(Z.of_nat ?a <? Z.of_nat ?b)] => generalize (Zlt_cases (Z.of_nat a) (Z.of_nat b)); intro Hcond3 end. *)
    (*           destruct (_ <? _); [apply word.unsigned_of_Z_1|]. *)
    (*           apply Nat2Z.inj_ge in Hcond3. *)
    (*           clear -Hfnz3 Hfuel3 Hcond3; Lia.lia. } *)
    (*       split; intros Hb; destruct (Nat.eq_dec fuel3 0) as [->|Hfnz3]; try (clear -Hb; congruence); clear Hb. *)
    (*       { (* loop_inv3 preservation *) *)
    (*         assert ((2 ^ (fuel1 - 1) - fuel2) * 2 ^ (n - (fuel1 - 1)) + (2 ^ (n - fuel1) - fuel3) + 2 ^ (n - fuel1) < 2 ^ n)%nat as idx_ok. *)
    (*         { rewrite Nat.mul_sub_distr_r, <- Nat.pow_add_r. *)
    (*           assert (fuel1 - 1 + _ = n)%nat as -> by (clear -Hfuel1 Hfnz1 Hfuel2 Hfnz2; Lia.lia). *)
    (*           apply (Nat.lt_le_trans _ (2 ^ n - fuel2 * 2 ^ (n - (fuel1 - 1)) + (2 * 2 ^ (n - fuel1)))); [clear -Hfuel1 Hfnz1 Hfuel2 Hfnz2 Hfuel3 Hfnz3; Lia.lia|]. *)
    (*           rewrite <- Nat.pow_succ_r'. *)
    (*           assert (n - (fuel1 - 1) = S (n - fuel1))%nat as <- by (clear -Hfnz1 Hfuel1; Lia.lia). *)
    (*           clear -Hfuel1 Hfnz1 Hfuel2 Hfnz2 Hfuel3 Hfnz3. *)
    (*           assert (Nat.pow 2 n = (Nat.pow 2 (fuel1 - 1)) * (Nat.pow 2 (n - (fuel1 - 1))))%nat as -> by (rewrite <- Nat.pow_add_r; f_equal; Lia.lia). *)
    (*           rewrite <- Nat.mul_sub_distr_r. *)
    (*           rewrite <- (Nat.mul_1_l (2 ^ (n - (fuel1 - 1)))) at 2. *)
    (*           rewrite <- Nat.mul_add_distr_r. *)
    (*           apply Nat.mul_le_mono_r. Lia.lia. } *)
    (*         pose proof (Bignums_length _ _ _ _ _ _ Hp3) as Xlen. *)
    (*         rewrite len_chunk1 in Xlen. *)
    (*         repeat straightline. eexists; split; repeat straightline. *)
    (*         { eexists; split; [eassumption|repeat straightline]. *)
    (*           eexists; split; [eassumption|repeat straightline]. *)
    (*           unfold v0. rewrite bytes_per_width_bytes_per_word. *)
    (*           rewrite <- word.ring_morph_mul. rewrite Z.mul_comm. *)
    (*           erewrite (Bignums1_load_of_sep R (word_of_F F.zero) (Nat.pow 2 n) p_ptr _ _ p3); auto. *)
    (*           2: rewrite Xlen; clear -idx_ok; Lia.lia. *)
    (*           eexists; split; reflexivity. } *)
    (*         eexists; split; repeat straightline. *)
    (*         { unfold l0. rewrite map.get_put_diff by (clear; congruence). *)
    (*           eexists; split; [eassumption|repeat straightline]. *)
    (*           rewrite map.get_put_diff by (clear; congruence). *)
    (*           eexists; split; [eassumption|repeat straightline]. *)
    (*           rewrite map.get_put_diff by (clear; congruence). *)
    (*           eexists; split; [eassumption|repeat straightline]. *)
    (*           unfold v0. rewrite bytes_per_width_bytes_per_word. *)
    (*           rewrite <- word.ring_morph_add, <- Nat2Z.inj_add. *)
    (*           rewrite <- word.ring_morph_mul. rewrite Z.mul_comm. *)
    (*           erewrite (Bignums1_load_of_sep R (word_of_F F.zero) (Nat.pow 2 n) p_ptr _ _ p3); auto. *)
    (*           2: rewrite Xlen; clear -idx_ok; Lia.lia. *)
    (*           eexists; split; reflexivity. } *)
    (*         eexists; split; repeat straightline. *)
    (*         { unfold l1, l0. rewrite map.get_put_diff by (clear; congruence). *)
    (*           rewrite map.get_put_same. eexists; split; repeat straightline. *)
    (*           rewrite map.get_put_same. eexists; split; repeat straightline. } *)
    (*         straightline_call. *)
    (*         { split; apply (proj1 (@Forall.Forall2_forall_iff'' _ _ (fun x y => feval y = Some x) _ p3 0%F (word_of_F 0%F)) (conj HF3 (feval_ok _))). } *)
    (*         repeat straightline. eexists; split; repeat straightline. *)
    (*         { unfold l', l1, l0. *)
    (*           repeat (rewrite map.get_put_diff by (clear; congruence)). *)
    (*           eexists; split; [eassumption|repeat straightline]. *)
    (*           repeat (rewrite map.get_put_diff by (clear; congruence)). *)
    (*           eexists; split; [eassumption|repeat straightline]. } *)
    (*         eexists; split; repeat straightline. *)
    (*         { unfold l'. rewrite map.get_put_same. eexists; split; reflexivity. } *)
    (*         rewrite bytes_per_width_bytes_per_word. *)
    (*         rewrite <- word.ring_morph_mul. rewrite Z.mul_comm. *)
    (*         unfold store. *)
    (*         eapply (Bignums1_store_of_sep R (Nat.pow 2 n) p_ptr _ _ p3); auto. *)
    (*         { rewrite Xlen; clear -idx_ok; Lia.lia. } *)
    (*         intros mem4 Hp3'. *)
    (*         repeat straightline. *)
    (*         eexists; split; repeat straightline. *)
    (*         { unfold l', l1, l0. rewrite map.get_put_diff by (clear; congruence). *)
    (*           rewrite map.get_put_same. *)
    (*           eexists; split; [reflexivity|repeat straightline]. *)
    (*           repeat (rewrite map.get_put_diff by (clear; congruence)). *)
    (*           rewrite map.get_put_same. *)
    (*           eexists; split; [reflexivity|repeat straightline]. } *)
    (*         straightline_call. *)
    (*         { split; apply (proj1 (@Forall.Forall2_forall_iff'' _ _ (fun x y => feval y = Some x) _ p3 0%F (word_of_F 0%F)) (conj HF3 (feval_ok _))). } *)
    (*         repeat straightline. *)
    (*         eexists; split; repeat straightline. *)
    (*         { unfold l'0, l', l1, l0. repeat (rewrite map.get_put_diff by (clear; congruence)). *)
    (*           eexists; split; [eassumption|repeat straightline]. *)
    (*           rewrite map.get_put_same. eexists; split; [reflexivity|repeat straightline]. } *)
    (*         straightline_call. *)
    (*         { split; [|eassumption]. rewrite Hv_eq. apply feval_ok. } *)
    (*         repeat straightline. *)
    (*         eexists; split; repeat straightline. *)
    (*         { unfold l'1, l'0, l', l1, l0. repeat (rewrite map.get_put_diff by (clear; congruence)). *)
    (*           eexists; split; [eassumption|repeat straightline]. *)
    (*           repeat (rewrite map.get_put_diff by (clear; congruence)). *)
    (*           eexists; split; [eassumption|repeat straightline]. *)
    (*           repeat (rewrite map.get_put_diff by (clear; congruence)). *)
    (*           eexists; split; [eassumption|repeat straightline]. } *)
    (*         eexists; split; repeat straightline. *)
    (*         { unfold l'1. rewrite map.get_put_same. *)
    (*           eexists; split; reflexivity. } *)
    (*         unfold store. *)
    (*         rewrite bytes_per_width_bytes_per_word. *)
    (*         rewrite <- word.ring_morph_add, <- Nat2Z.inj_add. *)
    (*         rewrite <- word.ring_morph_mul. rewrite Z.mul_comm. *)
    (*         eapply (Bignums1_store_of_sep R (Nat.pow 2 n) p_ptr _ _ _); eauto. *)
    (*         { rewrite length_set_nth, Xlen; clear -idx_ok; Lia.lia. } *)
    (*         intros mem5 Hp3''. *)
    (*         repeat straightline. *)
    (*         eexists; split; repeat straightline. *)
    (*         { unfold l'1, l'0, l', l1, l0. repeat (rewrite map.get_put_diff by (clear; congruence)). *)
    (*           eexists; split; [eassumption|repeat straightline]. } *)
    (*         exists (fuel3 - 1)%nat; split; [|clear -Hfnz3; Lia.lia]. *)
    (*         unfold loop_inv3. split; [clear -Hfuel3; Lia.lia|]. *)
    (*         split; [reflexivity|]. *)
    (*         unfold l2, l'1, l'0, l', l1, l0. *)
    (*         split; [repeat (rewrite map.get_put_diff by (clear; congruence)); assumption|]. *)
    (*         eexists; repeat split; repeat (rewrite map.get_put_diff by (clear; congruence)); try rewrite map.get_put_same; eauto. *)
    (*         2:{ rewrite <- word.ring_morph_add. *)
    (*             assert (1 = Z.of_nat 1) as -> by reflexivity. *)
    (*             rewrite <- Nat2Z.inj_add. do 3 f_equal. *)
    (*             clear -Hfuel1 Hfuel2 Hfuel3 Hfnz1 Hfnz2 Hfnz3; Lia.lia. } *)
    (*         assert (_ - (fuel3 - 1) = S (Nat.pow 2 (n - fuel1) - fuel3))%nat as -> by (clear -Hfuel1 Hfuel2 Hfuel3 Hfnz1 Hfnz2 Hfnz3; Lia.lia). *)
    (*         unfold inverse_polynomial_recompose_loop. *)
    (*         rewrite seq_S, fold_left_app. *)
    (*         assert (fold_left _ (seq _ _) _ = inverse_polynomial_recompose_loop (2 ^ (n - fuel1) - fuel3) ((2 ^ (fuel1 - 1) - fuel2) * 2 ^ (n - (fuel1 - 1)))  (2 ^ (n - fuel1)) v px2)%nat as -> by reflexivity. *)
    (*         cbn [fold_left]. *)
    (*         apply Forall2_set_nth; auto. *)
    (*         apply Forall2_set_nth; auto. } *)
    (*       repeat straightline. *)
    (*       eexists; split; repeat straightline. *)
    (*       { eexists; split; [eassumption|repeat straightline]. *)
    (*         eexists; split; [eassumption|repeat straightline]. } *)
    (*       exists (fuel2 - 1)%nat; split; [|clear -Hfnz2; Lia.lia]. *)
    (*       unfold loop_inv2. *)
    (*       split; [clear -Hfuel2; Lia.lia|]. *)
    (*       split; [reflexivity|]. *)
    (*       unfold l0; rewrite map.get_put_diff by (clear; congruence). *)
    (*       split; [assumption|]. *)
    (*       rewrite Nat.sub_0_r in *. *)
    (*       exists p3. eexists. repeat split; repeat (rewrite map.get_put_diff by (clear; congruence)); try (rewrite map.get_put_same); eauto. *)
    (*       2:{ rewrite Hm3. do 3 f_equal. *)
    (*           clear -Hfuel1 Hfnz1 Hfuel2 Hfnz2; Lia.lia. } *)
    (*       2:{ rewrite <- word.ring_morph_add, <- Nat2Z.inj_add. *)
    (*           do 3 f_equal. clear -Hfuel1 Hfnz1 Hfuel2 Hfnz2; Lia.nia. } *)
    (*       assert (_ - (fuel2 - 1) = S (Nat.pow 2 (fuel1 - 1) - fuel2))%nat as -> by (clear -Hfuel1 Hfnz1 Hfuel2 Hfnz2; Lia.lia). *)
    (*       unfold inverse_polynomial_list_loop. *)
    (*       rewrite seq_S, fold_left_app. *)
    (*       assert (fold_left _ (seq _ _) _ = inverse_polynomial_list_loop zetas (Nat.pow 2 (fuel1 - 1) - fuel2) (2 ^ (n - fuel1)) (2 ^ (n - (fuel1 - 1))) ((2 ^ fuel1)%nat, 0%nat, px1))%nat as -> by reflexivity. *)
    (*       cbn [fold_left]. rewrite Heq2. *)
    (*       f_equal; [|unfold v]; f_equal; try (clear -Hfuel1 Hfnz1 Hfuel2 Hfnz2; Lia.lia). *)
    (*       f_equal. assert (Nat.pow 2 fuel1 = 2 * Nat.pow 2 (fuel1 - 1))%nat as -> by (rewrite <- Nat.pow_succ_r'; f_equal; clear -Hfnz1; Lia.lia). *)
    (*       clear -Hfuel1 Hfnz1 Hfuel2 Hfnz2; Lia.nia. } *)
    (*     rewrite Nat.sub_0_r in *. *)
    (*     exists (fuel1 - 1)%nat; split; [|clear -Hfnz1; Lia.lia]. *)
    (*     unfold loop_inv1. *)
    (*     split; [clear -Hfuel1; Lia.lia|]. *)
    (*     split; [reflexivity|]. *)
    (*     split; [assumption|]. *)
    (*     do 2 eexists; repeat split; eauto. *)
    (*     2:{ rewrite Hm2. assert (Nat.pow 2 fuel1 = 2 * Nat.pow 2 (fuel1 - 1))%nat as -> by (rewrite <- Nat.pow_succ_r'; f_equal; clear -Hfnz1; Lia.lia). *)
    (*         do 3 f_equal; clear; Lia.lia. } *)
    (*     assert (Nat.min m n - (fuel1 - 1) = S (Nat.min m n - fuel1))%nat as -> by (clear -Hfuel1 Hfnz1; Lia.lia). *)
    (*     unfold inverse_layer_recomposition_loop'. *)
    (*     rewrite seq_S, fold_left_app. *)
    (*     assert (fold_left _ (seq _ _) _ = inverse_layer_recomposition_loop' zetas (Nat.min m n - fuel1) (Nat.min m n) (Init.Nat.shiftl 1 (Nat.min m n), Init.Nat.shiftl 1 (n - Nat.min m n), p))%nat as -> by reflexivity. *)
    (*     rewrite Heq1. cbn. *)
    (*     assert (_ - 1 - _ = fuel1 - 1)%nat as -> by (clear -Hfnz1 Hfuel1; Lia.lia). *)
    (*     rewrite Nat.shiftl_1_l. *)
    (*     assert (Nat.pow 2 _ + Nat.pow 2 _ = Nat.pow 2 (n - (fuel1 - 1)))%nat as ->. *)
    (*     { assert (n - (_ - _) = S (n - fuel1))%nat as -> by (clear -Hfuel1 Hfnz1; Lia.lia). *)
    (*       rewrite Nat.pow_succ_r'; clear; Lia.lia. } *)
    (*     rewrite Heq2. do 2 f_equal. *)
    (*     assert (Nat.pow 2 fuel1 = 2 * Nat.pow 2 (fuel1 - 1))%nat as -> by (rewrite <- Nat.pow_succ_r'; f_equal; clear -Hfnz1; Lia.lia). *)
    (*     clear; Lia.lia. } *)
    (*   repeat straightline. rewrite Nat.sub_0_r in *. *)
    (*   rewrite recomposition_loop_eq in Heq1. *)
    (*   rewrite Heq1. apply wp_while. *)
    (*   rewrite Nat.shiftl_1_l. *)
    (*   set (loop_inv4 := fun (fuel4: nat) (tr': Semantics.trace) (mem': mem) (loc': locals) => *)
    (*                       (fuel4 <= Nat.pow 2 n)%nat /\ *)
    (*                         tr' = tr /\ *)
    (*                         map.get loc' "p" = Some p_ptr /\ *)
    (*                         let i := ((Nat.pow 2 n) - fuel4)%nat in *)
    (*                         exists p4, *)
    (*                           Forall2 (fun x y => feval y = Some x) (div_loop i (F.inv ((1 + 1) ^ N.of_nat (Nat.min m n))) px1) p4 /\ *)
    (*                             map.get loc' "j" = Some (word.of_Z (Z.of_nat i)) /\ *)
    (*                             (Bignums 1 (2 ^ n) p_ptr (List.chunk 1 p4) ⋆ R)%sep mem'). *)
    (*   exists nat, lt, loop_inv4; split; [apply lt_wf|]. *)
    (*   split. *)
    (*   { exists (Nat.pow 2 n). unfold loop_inv4. rewrite Nat.sub_diag. *)
    (*     repeat split; [Lia.lia|..]. *)
    (*     - unfold l0; rewrite map.get_put_diff by congruence; auto. *)
    (*     - exists p1; repeat split; auto. *)
    (*       apply map.get_put_same. } *)
    (*   intros fuel4 ? mem4 loc4 Hinv4. *)
    (*   destruct Hinv4 as (Hfuel4 & -> & Hptr4 & p4 & HF4 & Hj & Hp4). *)
    (*   eexists; split; repeat straightline. *)
    (*   { eexists; split; [eassumption|repeat straightline]. } *)
    (*   rewrite <- Core.word.morph_ltu. *)
    (*   2-3: split; [apply Nat2Z.is_nonneg|]. *)
    (*   2-3: assert (2 ^ width = Z.of_nat (Nat.pow 2 (Z.to_nat width))) as -> by (rewrite Nat2Z.inj_pow, Z2Nat.id by Lia.lia; reflexivity). *)
    (*   2-3: apply Nat2Z.inj_lt. *)
    (*   2: apply (Nat.le_lt_trans _ (Nat.pow 2 n)); [clear; Lia.lia|]. *)
    (*   2-3: apply Nat.pow_lt_mono_r; Lia.lia. *)
    (*   assert (word.unsigned _ = if Nat.eq_dec fuel4 0 then 0%Z else 1%Z) as ->. *)
    (*   { destruct (Nat.eq_dec fuel4 0) as [->|Hfnz4]. *)
    (*     - rewrite Nat.sub_0_r, Z.ltb_irrefl. apply word.unsigned_of_Z_0. *)
    (*     - match goal with | |- context [(Z.of_nat ?a <? Z.of_nat ?b)] => generalize (Zlt_cases (Z.of_nat a) (Z.of_nat b)); intro Hcond4 end. *)
    (*       destruct (_ <? _); [apply word.unsigned_of_Z_1|]. *)
    (*       apply Nat2Z.inj_ge in Hcond4. *)
    (*       clear -Hfnz4 Hfuel4 Hcond4; Lia.lia. } *)
    (*   pose proof (Bignums_length _ _ _ _ _ _ Hp4) as Xlen. *)
    (*   rewrite len_chunk1 in Xlen. *)
    (*   split; intros Hb; destruct (Nat.eq_dec fuel4 0) as [->|Hfnz4]; try (clear -Hb; congruence); clear Hb. *)
    (*   { repeat straightline. eexists; split; repeat straightline. *)
    (*     { eexists; split; [eassumption|repeat straightline]. *)
    (*       eexists; split; [eassumption|repeat straightline]. *)
    (*       unfold v. rewrite bytes_per_width_bytes_per_word. *)
    (*       rewrite <- word.ring_morph_mul. rewrite Z.mul_comm. *)
    (*       erewrite Bignums1_load_of_sep; eauto. *)
    (*       rewrite Xlen; clear -Hfuel4 Hfnz4; Lia.lia. } *)
    (*     eexists; split; repeat straightline. *)
    (*     { eexists; split; [apply map.get_put_same|repeat straightline]. } *)
    (*     straightline_call. *)
    (*     { split; [|apply (proj1 (@Forall.Forall2_forall_iff'' _ _ (fun x y => feval y = Some x) _ p4 0%F (word_of_F 0%F)) (conj HF4 (feval_ok _)))]. *)
    (*       assert (word.of_Z _ = word_of_F c) as -> by reflexivity. *)
    (*       apply feval_ok. } *)
    (*     repeat straightline. *)
    (*     eexists; split; repeat straightline. *)
    (*     { unfold l', l0. repeat (rewrite map.get_put_diff by (clear; congruence)). *)
    (*       eexists; split; [eassumption|repeat straightline]. *)
    (*       repeat (rewrite map.get_put_diff by (clear; congruence)). *)
    (*       eexists; split; [eassumption|repeat straightline]. } *)
    (*     eexists; split; repeat straightline. *)
    (*     { eexists; split; [apply map.get_put_same|reflexivity]. } *)
    (*     rewrite bytes_per_width_bytes_per_word. *)
    (*     rewrite <- word.ring_morph_mul. rewrite Z.mul_comm. *)
    (*     eapply Bignums1_store_of_sep; eauto. *)
    (*     { rewrite Xlen; clear -Hfuel4 Hfnz4; Lia.lia. } *)
    (*     intros mem5 Hmem5. *)
    (*     repeat straightline. eexists; split; repeat straightline. *)
    (*     { unfold l', l0. repeat (rewrite map.get_put_diff by (clear; congruence)). *)
    (*       eexists; split; [eassumption|repeat straightline]. } *)
    (*     exists (fuel4 - 1)%nat; split; [|clear -Hfnz4; Lia.lia]. *)
    (*     unfold loop_inv4. *)
    (*     split; [clear -Hfuel4; Lia.lia|]. *)
    (*     split; [reflexivity|]. *)
    (*     unfold l1, l', l0. repeat (rewrite map.get_put_diff by (clear; congruence)). *)
    (*     split; [assumption|]. *)
    (*     rewrite map.get_put_same. assert (1%Z = Z.of_nat 1%nat) as -> by reflexivity. *)
    (*     rewrite <- word.ring_morph_add, <- Nat2Z.inj_add. *)
    (*     assert (_ - _ + 1 = Nat.pow 2 n - (fuel4 - 1))%nat as -> by (clear -Hfuel4 Hfnz4; Lia.lia). *)
    (*     eexists; repeat split; eauto. *)
    (*     assert (Nat.pow 2 n - (fuel4 - 1) = S (Nat.pow 2 n - fuel4))%nat as -> by (clear -Hfuel4 Hfnz4; Lia.lia). *)
    (*     unfold div_loop. rewrite seq_S, fold_left_app. *)
    (*     assert (fold_left _ (seq _ _) _ = div_loop (Nat.pow 2 n - fuel4) (F.inv ((1 + 1) ^ N.of_nat (Nat.min m n))) px1) as -> by reflexivity. *)
    (*     cbn [fold_left]. *)
    (*     apply Forall2_set_nth; auto. } *)
    (*   rewrite Nat.sub_0_r in *. repeat straightline. *)
    (*   exists p4. auto. *)
    (* Qed. *)
  End FitsInWords.
End Bedrock.
