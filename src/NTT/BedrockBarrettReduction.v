Require Import Coq.ZArith.ZArith.

Require Import Crypto.Arithmetic.BarrettReduction.Wikipedia.
Require Import Crypto.Util.ZUtil.ModInv.
Require Import Crypto.Util.ZUtil.EquivModulo.

Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Scalars.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.BasicC32Semantics bedrock2.BasicC64Semantics.

Require Import Crypto.NTT.BedrockNTT.
Require Import Crypto.Spec.ModularArithmetic.

Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.

Require Coq.Strings.String.
Local Open Scope string_scope.

Section __.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}
    {mem: map.map word Byte.byte} {loc: map.map String.string word}
    {ext_spec: bedrock2.Semantics.ExtSpec}
    {word_ok : word.ok word} {map_ok : map.ok mem}
    {loc_ok : map.ok loc}
    {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Context {modulus_pos: positive}.
  Let modulus := Zpos modulus_pos.
  Context {modulus_prime: Znumtheory.prime modulus}.
  Context {modulus_not_2: 3 <= modulus}.

  Definition k := Z.log2_up modulus.

  Lemma modulus_lt_pow2k:
    modulus < Z.pow 2 k.
  Proof.
    unfold k. generalize (Z.log2_up_spec modulus ltac:(Lia.lia)). intros Y.
    assert (modulus = Z.pow 2 (Z.log2_up modulus) \/ modulus < Z.pow 2 (Z.log2_up modulus)) as [Z|?] by Lia.lia; auto.
    exfalso.
    generalize (Zpow_facts.prime_power_prime modulus 2 (Z.log2_up modulus) ltac:(apply Z.log2_up_nonneg) modulus_prime Znumtheory.prime_2 ltac:(rewrite <- Z; apply Z.divide_refl)).
    Lia.lia.
  Qed.

  Definition m := (4 ^ k / modulus). (* This is precomputed *)

  (* Correct when x < 2 * modulus *)
  Definition barrett_reduce_small (x: Z): Z :=
    let s := 1 - Z.b2z (Z.ltb x modulus) in
    let r := x - (s * modulus) in
    r.

  Lemma barrett_reduce_small_correct:
    forall x, (0 <= x < 2 * modulus) ->
         barrett_reduce_small x = x mod modulus.
  Proof.
    intros. unfold barrett_reduce_small.
    generalize (Zlt_cases x modulus); intros.
    destruct (Z.ltb x modulus).
    - rewrite Z.sub_0_r. rewrite Z.mod_small by Lia.lia. reflexivity.
    - rewrite Z.mul_1_l. apply (Zmod_unique _ _ 1); Lia.lia.
  Qed.

  (* Correct when x < 2^(2k) *)
  Definition barrett_reduce (x: Z): Z :=
    let q := Z.shiftr (m * x) (2 * k) in
    let r := x - q * modulus in
    let s := 1 - Z.b2z (Z.ltb r modulus) in
    let r := r - (s * modulus) in
    r.

  Lemma barrett_reduce_correct:
    forall x, (0 <= x < Z.pow 4 k) ->
         barrett_reduce x = x mod modulus.
  Proof.
    intros. rewrite (barrett_reduction_small modulus x ltac:(Lia.lia) k modulus_lt_pow2k m eq_refl ltac:(Lia.lia) ltac:(Lia.lia) ltac:(Lia.lia)).
    unfold barrett_reduce.
    assert (Hk: 1 < k).
    { unfold k. apply Z.log2_up_lt_pow2; Lia.lia. }
    assert ((m * x) / Z.pow 4 k = Z.shiftr (m * x) (2 * k)) as ->.
    { assert (4 ^ k = 2 ^ (2 * k)) as -> by (rewrite Z.pow_mul_r; f_equal; Lia.lia).
      rewrite Z.shiftr_div_pow2 by Lia.lia. reflexivity. }
    generalize (Zlt_cases (x - Z.shiftr (m * x) (2 * k) * modulus) modulus). intros.
    destruct (Z.ltb (x - Z.shiftr (m * x) (2 * k) * modulus) modulus); simpl.
    - rewrite Z.sub_0_r. reflexivity.
    - reflexivity.
  Qed.

  Context {reduce_small_name reduce_name: String.string}.
  Context {add_name sub_name mul_name: String.string}.

  Instance spec_of_reduce_small : spec_of reduce_small_name :=
    fnspec! reduce_small_name (X: word) / (x: Z) ~> r,
    { requires tr mem :=
        (0 <= x < 2 * modulus) /\
        X = word.of_Z x;
      ensures tr' mem' :=
        tr' = tr /\
        mem' = mem /\
        r = word.of_Z (barrett_reduce_small x) }.

  Instance spec_of_reduce : spec_of reduce_name :=
    fnspec! reduce_name (X: word) / (x: Z) ~> r,
    { requires tr mem :=
        (0 <= x < Z.pow 4 k) /\
        X = word.of_Z x;
      ensures tr' mem' :=
        tr' = tr /\
        mem' = mem /\
        r = word.of_Z (barrett_reduce x) }.

  Program Definition feval (x: word): option (F modulus_pos) :=
    if Z_lt_dec (word.unsigned x) modulus then Some (word.unsigned x) else None.
  Next Obligation.
    rewrite Z.mod_small; [reflexivity|]. generalize (word.unsigned_range x).
    Lia.lia.
  Qed.

  Lemma feval_is_Some_implies:
    forall x y, feval x = Some y ->
           0 <= word.unsigned x < modulus /\ F.to_Z y = word.unsigned x.
  Proof.
    intros x y Hx. unfold feval in Hx.
    generalize (word.unsigned_range x).
    destruct (Z_lt_dec (word.unsigned x) modulus); [split; [Lia.lia|]|congruence].
    inversion Hx; subst y; reflexivity.
  Qed.

  Instance spec_of_add : spec_of add_name := spec_of_add (q:=modulus_pos) (feval:=feval) (add:=add_name).
  Instance spec_of_sub : spec_of sub_name := spec_of_sub (q:=modulus_pos) (feval:=feval) (sub:=sub_name).
  Instance spec_of_mul : spec_of mul_name := spec_of_mul (q:=modulus_pos) (feval:=feval) (mul:=mul_name).

  Section VerySmall.
    Hypothesis k_very_small: 3 * k + 1 < width.
    Definition word_of_F (x: F modulus_pos): word := word.of_Z (F.to_Z x).

    Lemma modulus_small:
      2 * modulus < modulus * modulus < 2 ^ width.
    Proof.
      split; [apply Z.mul_lt_mono_pos_r; Lia.lia|].
      generalize (Z.log2_up_spec modulus ltac:(Lia.lia)); intros Hk.
      generalize (Z.log2_up_nonneg modulus). fold k. intro Hkpos.
      fold k in Hk. apply (Z.le_lt_trans _ (2 ^ (2 * k))); [|apply Z.pow_lt_mono_r; destruct BW; Lia.lia].
      rewrite (Z.mul_comm 2), Z.pow_mul_r, Z.pow_2_r by Lia.lia.
      apply Z.mul_le_mono_nonneg; try Lia.lia.
    Qed.

    Lemma feval_ok:
      forall (x: F modulus_pos), feval (word_of_F x) = Some x.
    Proof.
      intros. cbv [word_of_F feval].
      pose proof (ModularArithmeticTheorems.F.to_Z_range x ltac:(Lia.lia)) as Hx.
      pose proof modulus_small as Hsmall.
      destruct (Z_lt_dec _ _) as [Hlt|Hlt].
      - f_equal. apply ModularArithmeticTheorems.F.eq_to_Z_iff. cbn.
        rewrite word.unsigned_of_Z_nowrap; Lia.lia.
      - rewrite word.unsigned_of_Z_nowrap in Hlt; Lia.lia.
    Qed.

    Definition reduce_small_br2fn :=
      func! (x) ~> (r) {
          s = $1 - (x < $modulus);
          r = x - (s * $modulus)
      }.

    Lemma reduce_small_br2fn_ok:
      program_logic_goal_for reduce_small_br2fn
        (forall functions : map.rep,
            map.get functions reduce_small_name = Some reduce_small_br2fn ->
            spec_of_reduce_small functions).
    Proof.
      repeat straightline.
      eexists; split; repeat straightline.
      { unfold l. rewrite map.get_put_same.
        eexists; split; [reflexivity|repeat straightline]. }
      eexists; split; repeat straightline.
      { unfold l0, l. rewrite map.get_put_diff by (clear; congruence).
        rewrite map.get_put_same.
        eexists; split; [reflexivity|repeat straightline].
        rewrite map.get_put_same.
        eexists; split; [reflexivity|repeat straightline]. }
      unfold l1. rewrite map.get_put_same.
      eexists; split; [reflexivity|repeat straightline].
      unfold X, barrett_reduce_small.
      pose proof modulus_small.
      rewrite <- Core.word.morph_ltu by Lia.lia.
      fold modulus.
      assert ((if (x <? modulus) then word.of_Z 1 else word.of_Z 0) = word.of_Z (Z.b2z (x <? modulus))) as -> by (unfold Z.b2z; destruct (_ <? _); reflexivity).
      rewrite <- word.ring_morph_sub, <- word.ring_morph_mul, <- word.ring_morph_sub.
      reflexivity.
    Qed.

    Definition reduce_br2fn :=
      func! (x) ~> (r) {
          q = ($m * x) >> ($2 * $k);
          r = x - q * $modulus;
          s = $1 - (r < $modulus);
          r = r - (s * $modulus)
      }.

    Lemma reduce_br2fn_ok:
      program_logic_goal_for reduce_br2fn
        (forall functions : map.rep,
            map.get functions reduce_name = Some reduce_br2fn ->
            spec_of_reduce functions).
    Proof.
      Local Opaque m k.
      repeat straightline.
      eexists; split; repeat straightline.
      { unfold l; rewrite map.get_put_same.
        eexists; split; [reflexivity|repeat straightline]. }
      assert (Hk: 1 < k) by (cbv [k]; apply Z.log2_up_lt_pow2; Lia.lia).
      assert (Hm: 0 <= m) by (cbv [m]; generalize (Z_div_ge0 (4 ^ k) modulus ltac:(Lia.lia) ltac:(generalize (Z.pow_nonneg 4 k ltac:(Lia.lia)); Lia.lia)); Lia.lia).
      eexists; split; repeat straightline.
      { unfold l0, l. rewrite map.get_put_diff by congruence.
        rewrite map.get_put_same. eexists; split; [reflexivity|repeat straightline].
        rewrite map.get_put_same. subst X.
        rewrite <- word.ring_morph_mul, <- word.ring_morph_mul.
        assert (4 ^ k <= modulus * 2 ^ (k + 1)).
        { transitivity (Z.pow 2 (k - 1) * Z.pow 2 (k + 1)).
          * rewrite <- Z.pow_add_r by Lia.lia.
            assert (k - 1 + (k + 1) = 2 * k) as -> by Lia.lia.
            rewrite Z.pow_mul_r by Lia.lia. reflexivity.
          * apply Z.mul_le_mono_pos_r; [Lia.lia|].
            generalize (Z.log2_up_spec modulus ltac:(Lia.lia)). cbv [k]. Lia.lia. }
        pose proof (Z.div_le_upper_bound (Z.pow 4 k) modulus (Z.pow 2 (k + 1)) ltac:(Lia.lia) ltac:(Lia.lia)).
        rewrite <- Core.word.morph_shiftr; try (pose proof modulus_small; split; try Lia.lia).
        2:{ cbv [m]. transitivity (2 ^ (k + 1) * 4 ^ k)%Z; [Lia.nia|].
            assert (4 = 2 ^ 2)%Z as -> by reflexivity.
            rewrite <- Z.pow_mul_r by Lia.lia.
            rewrite <- Z.pow_add_r by Lia.lia.
            apply Z.pow_lt_mono_r; Lia.lia. }
        eexists; split; [reflexivity|repeat straightline]. }
      eexists; split; repeat straightline.
      { unfold l1, l0, l. repeat (rewrite map.get_put_diff by (clear; congruence)).
        rewrite map.get_put_same. eexists; split; [reflexivity|repeat straightline]. }
      eexists; split; repeat straightline.
      { unfold l2, l1, l0, l. repeat (rewrite map.get_put_diff by (clear; congruence)).
        rewrite map.get_put_same. eexists; split; [reflexivity|repeat straightline].
        rewrite map.get_put_same.
        eexists; split; [reflexivity|repeat straightline]. }
      unfold l3. rewrite map.get_put_same.
      eexists; split; [reflexivity|repeat straightline].
      unfold X, barrett_reduce.
      pose proof modulus_small. fold modulus.
      assert (4 ^ k < 2 ^ width).
      { assert (4 = 2 ^ 2)%Z as -> by reflexivity.
        rewrite <- Z.pow_mul_r by Lia.lia.
        apply Z.pow_lt_mono_r; Lia.lia. }
      rewrite <- word.ring_morph_mul, <- word.ring_morph_sub.
      rewrite <- Core.word.morph_ltu; try Lia.lia.
      2:{ generalize (qn_small modulus x ltac:(Lia.lia) k modulus_lt_pow2k m eq_refl ltac:(Lia.lia) ltac:(Lia.lia)).
          assert ((m * x) / Z.pow 4 k = Z.shiftr (m * x) (2 * k)) as ->.
          { rewrite Z.shiftr_div_pow2 by Lia.lia.
            rewrite Z.pow_mul_r by Lia.lia. reflexivity. }
          intros; split; [Lia.lia|].
          generalize (r_small modulus x ltac:(Lia.lia) k modulus_lt_pow2k m eq_refl ltac:(Lia.lia) ltac:(Lia.lia) ltac:(Lia.lia)).
          assert ((m * x) / Z.pow 4 k = Z.shiftr (m * x) (2 * k)) as ->.
          { assert (4 ^ k = 2 ^ (2 * k)) as -> by (rewrite Z.pow_mul_r; f_equal; Lia.lia).
            rewrite Z.shiftr_div_pow2 by Lia.lia. reflexivity. }
          intros.
          transitivity (2 * modulus); auto.
          transitivity (2 * 2 ^ k); [generalize modulus_lt_pow2k; Lia.lia|].
          rewrite <- Z.pow_succ_r by Lia.lia. apply Z.pow_lt_mono_r; Lia.lia. }
      assert ((if (_ <? modulus) then word.of_Z 1 else word.of_Z 0) = word.of_Z (Z.b2z (x - Z.shiftr (m * x) (2 * k) * modulus <? modulus))) as ->.
      { destruct (_ <? _); reflexivity. }
      rewrite <- word.ring_morph_sub, <- word.ring_morph_mul, <- word.ring_morph_sub.
      reflexivity.
    Qed.

    Definition add_br2fn :=
      func! (x, y) ~> r {
          unpack! r = $reduce_small_name(x + y)
        }.

    Definition sub_br2fn :=
      func! (x, y) ~> r {
          unpack! r = $reduce_small_name(x + ($modulus - y))
        }.

    Definition mul_br2fn :=
      func! (x, y) ~> r {
          unpack! r = $reduce_name(x * y)
        }.

    Lemma add_br2fn_ok:
      program_logic_goal_for add_br2fn
        (forall functions : map.rep,
            map.get functions add_name = Some add_br2fn ->
            spec_of_reduce_small functions ->
            spec_of_add functions).
    Proof.
      enter add_br2fn. red; intros. red. intros.
      eapply start_func; eauto.
      cbv beta match delta [WeakestPrecondition.func].
      repeat straightline. eexists; split.
      repeat straightline. eexists; split.
      unfold l. rewrite map.get_put_diff by congruence. eapply map.get_put_same.
      repeat straightline. eexists; split; [|repeat straightline].
      eapply map.get_put_same.
      straightline_call.
      { instantiate (1 := word.unsigned x + word.unsigned y).
        apply feval_is_Some_implies in H1, H2. destruct H1, H2.
        split; [Lia.lia|]. rewrite word.ring_morph_add.
        do 2 rewrite word.of_Z_unsigned. reflexivity. }
      eexists; split; repeat straightline; [reflexivity|].
      eexists; split; repeat straightline; [apply map.get_put_same|].
      apply feval_is_Some_implies in H1, H2. destruct H1, H2.
      rewrite barrett_reduce_small_correct by Lia.lia.
      pose proof modulus_small as Hsmall.
      unfold feval. destruct (Z_lt_dec _ _) as [Hlt|Hlt].
                  - f_equal. apply ModularArithmeticTheorems.F.eq_to_Z_iff.
                    rewrite ModularArithmeticTheorems.F.to_Z_add. cbn.
                    rewrite word.unsigned_of_Z_nowrap by Lia.lia.
                    rewrite H3, H4. reflexivity.
                  - generalize (Z.mod_pos_bound (word.unsigned x + word.unsigned y) modulus ltac:(Lia.lia)).
                    rewrite word.unsigned_of_Z_nowrap in Hlt by Lia.lia. Lia.lia.
    Qed.

    Lemma sub_br2fn_ok:
      program_logic_goal_for sub_br2fn
        (forall functions : map.rep,
            map.get functions sub_name = Some sub_br2fn ->
            spec_of_reduce_small functions ->
            spec_of_sub functions).
    Proof.
      enter sub_br2fn. red; intros. red. intros.
      eapply start_func; eauto.
      cbv beta match delta [WeakestPrecondition.func].
      repeat straightline. eexists; split.
      repeat straightline. eexists; split.
      unfold l. rewrite map.get_put_diff by congruence. eapply map.get_put_same.
      repeat straightline. eexists; split; [|repeat straightline].
      eapply map.get_put_same.
      straightline_call.
      { instantiate (1 := word.unsigned x + (modulus - word.unsigned y)).
        apply feval_is_Some_implies in H1, H2. destruct H1, H2.
        split; [Lia.lia|]. rewrite <- (word.of_Z_unsigned y) at 1.
        rewrite <- (word.of_Z_unsigned x) at 1.
        rewrite <- word.ring_morph_sub, <- word.ring_morph_add. reflexivity. }
      eexists; split; repeat straightline; [reflexivity|].
      eexists; split; repeat straightline; [apply map.get_put_same|].
      apply feval_is_Some_implies in H1, H2. destruct H1, H2.
      rewrite barrett_reduce_small_correct by Lia.lia.
      pose proof modulus_small as Hsmall.
      unfold feval. destruct (Z_lt_dec _ _) as [Hlt|Hlt].
      - f_equal. apply ModularArithmeticTheorems.F.eq_to_Z_iff.
        rewrite (Hierarchy.ring_sub_definition a b).
        rewrite ModularArithmeticTheorems.F.to_Z_add, ModularArithmeticTheorems.F.to_Z_opp.
        rewrite H3, H4. cbv [F.to_Z proj1_sig].
        rewrite word.unsigned_of_Z_nowrap by Lia.lia.
        destruct (Z.eq_dec (word.unsigned y) 0) as [->|Hynz].
        + rewrite Z.sub_0_r, Z.add_0_r.
          rewrite <- (Z.mul_1_l modulus) at 1.
          rewrite Modulo.Z.mod_add_full. reflexivity.
        + f_equal. f_equal. apply (Zmod_unique _ _ (-1)); Lia.lia.
      - generalize (Z.mod_pos_bound (word.unsigned x + (modulus - word.unsigned y)) modulus ltac:(Lia.lia)).
        rewrite word.unsigned_of_Z_nowrap in Hlt by Lia.lia. Lia.lia.
    Qed.

    Lemma mul_br2fn_ok:
      program_logic_goal_for mul_br2fn
        (forall functions : map.rep,
            map.get functions mul_name = Some mul_br2fn ->
            spec_of_reduce functions ->
            spec_of_mul functions).
    Proof.
      enter mul_br2fn. red; intros. red. intros.
      eapply start_func; eauto.
      cbv beta match delta [WeakestPrecondition.func].
      repeat straightline. eexists; split.
      repeat straightline. eexists; split.
      unfold l. rewrite map.get_put_diff by congruence. eapply map.get_put_same.
      repeat straightline. eexists; split; [|repeat straightline].
      eapply map.get_put_same.
      assert (0 <= word.unsigned x * word.unsigned y < 4 ^ k) as Hmul.
      { apply feval_is_Some_implies in H1, H2. destruct H1, H2.
        assert (4 = 2 ^ 2) as -> by reflexivity.
        generalize (Z.log2_up_nonneg modulus); intro Hkpos.
        generalize (Z.log2_up_spec modulus ltac:(Lia.lia)). intro Hk.
        rewrite <- Z.pow_mul_r, (Z.mul_comm 2), Z.pow_mul_r, Z.pow_2_r by (cbv [k]; Lia.lia).
        split; [Lia.lia|].
        apply (Z.lt_le_trans _ (modulus * modulus)).
        - apply Z.mul_lt_mono_nonneg; Lia.lia.
        - apply Z.mul_le_mono_nonneg; try (cbv [k]; Lia.lia). }
      straightline_call.
      { instantiate (1 := word.unsigned x * word.unsigned y).
        split; auto.
        rewrite word.ring_morph_mul.
        do 2 rewrite word.of_Z_unsigned. reflexivity. }
      eexists; split; repeat straightline; [reflexivity|].
      eexists; split; repeat straightline; [apply map.get_put_same|].
      apply feval_is_Some_implies in H1, H2. destruct H1, H2.
      rewrite barrett_reduce_correct by Lia.lia.
      pose proof modulus_small as Hsmall.
      unfold feval. destruct (Z_lt_dec _ _) as [Hlt|Hlt].
      - f_equal. apply ModularArithmeticTheorems.F.eq_to_Z_iff.
        rewrite ModularArithmeticTheorems.F.to_Z_mul. cbn.
        rewrite word.unsigned_of_Z_nowrap by Lia.lia.
        rewrite H3, H4. reflexivity.
      - generalize (Z.mod_pos_bound (word.unsigned x + word.unsigned y) modulus ltac:(Lia.lia)).
        rewrite word.unsigned_of_Z_nowrap in Hlt by Lia.lia. Lia.lia.
    Qed.
  End VerySmall.
End __.
