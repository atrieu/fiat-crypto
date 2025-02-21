Require Import Coq.PArith.BinPosDef. Local Open Scope positive_scope.
Require Import Coq.NArith.BinNat.
From Coq.Classes Require Import Morphisms.
Require Import Spec.ModularArithmetic.
Require Import Arithmetic.ModularArithmeticTheorems.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.Znumtheory Coq.Lists.List. Import ListNotations.
Require Import NTT.Polynomial.
Require PrimeFieldTheorems.

Require Import coqutil.Datatypes.List.

Section ProductHomomorphism.
  Context {R EQ ZERO ONE OPP ADD SUB MUL} `{@Hierarchy.ring R EQ ZERO ONE OPP ADD SUB MUL}.
  Context {R' EQ' ZERO' ONE' OPP' ADD' SUB' MUL'} `{@Hierarchy.ring R' EQ' ZERO' ONE' OPP' ADD' SUB' MUL'}.
  Context {S eq zero one opp add sub mul} `{@Hierarchy.ring S eq zero one opp add sub mul}.
  Context {S' eq' zero' one' opp' add' sub' mul'} `{@Hierarchy.ring S' eq' zero' one' opp' add' sub' mul'}.
  Context {phi:R->R'} {psi:S->S'}.
  Context `{@Ring.is_homomorphism R EQ ONE ADD MUL R' EQ' ONE' ADD' MUL' phi}.
  Context `{@Ring.is_homomorphism S eq one add mul S' eq' one' add' mul' psi}.

  Lemma product_homomorphism:
    @Ring.is_homomorphism
      (R * S) (fun x y => EQ (fst x) (fst y) /\ eq (snd x) (snd y)) (ONE, one) (Ring.apply_binop_pair ADD add) (Ring.apply_binop_pair MUL mul)
      (R' * S') (fun x y => EQ' (fst x) (fst y) /\ eq' (snd x) (snd y)) (ONE', one') (Ring.apply_binop_pair ADD' add') (Ring.apply_binop_pair MUL' mul')
      (Ring.apply_unop_pair phi psi).
  Proof.
    repeat constructor; cbn.
    - apply H3.(Ring.homomorphism_is_homomorphism).(Monoid.homomorphism).
    - apply H4.(Ring.homomorphism_is_homomorphism).(Monoid.homomorphism).
    - destruct H5.
      apply H3.(Ring.homomorphism_is_homomorphism).(Monoid.is_homomorphism_phi_proper); auto.
    - destruct H5.
      apply H4.(Ring.homomorphism_is_homomorphism).(Monoid.is_homomorphism_phi_proper); auto.
    - apply H3.(Ring.homomorphism_mul).
    - apply H4.(Ring.homomorphism_mul).
    - apply H3.(Ring.homomorphism_one).
    - apply H4.(Ring.homomorphism_one).
  Qed.
End ProductHomomorphism.

Section CyclotomicDecomposition.
  Local Coercion N.of_nat: nat >-> N.
  Context {q: positive} {prime_q: prime q}.
  Local Notation F := (F q). (* This is to have F.pow available, there is no Fpow defined for a general field *)
  Local Open Scope F_scope.
  Context {field: @Hierarchy.field F eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div}
    {char_ge_3: @Ring.char_ge F eq F.zero F.one F.opp F.add F.sub F.mul (BinNat.N.succ_pos (BinNat.N.two))}.
  Context {P}{poly_ops: @Polynomial.polynomial_ops F P}.
  Context {poly_defs: @Polynomial.polynomial_defs F eq F.zero F.one F.opp F.add F.sub F.mul P _}.
  Context {zeta: F} {m: nat} {Hm: zeta ^ (N.pow 2 m) = F.opp 1}.

  Local Notation Peq := (@Polynomial.Peq F eq P _).
  Local Notation Pmod := (@Polynomial.Pmod F F.zero P _ F.div).
  Local Notation Pmul := (@Polynomial.Pmul _ _ poly_ops).
  Local Notation Pconst := (@Polynomial.Pconst _ _ poly_ops).
  Local Notation negacyclic := (@Polynomial.negacyclic F P _).
  Local Notation posicyclic := (@Polynomial.posicyclic F P _).
  Local Notation coprime := (Polynomial.coprime (poly_defs:=poly_defs) (Fdiv:=F.div)).
  Local Notation Pquotl := (@Polynomial.Pquotl F eq F.zero P _ F.div).
  Local Notation of_pl := (Polynomial.of_pl (poly_defs:=poly_defs) (Finv:=F.inv) (Fdiv:=F.div) (field:=field)).
  Local Notation NTT_psi2 := (@Polynomial.NTT_base_psi_unpacked F F.one F.add P _ F.inv).
  Local Notation Pquot := (@Polynomial.Pquot F eq F.zero P _ F.div).
  Local Notation one := (@Polynomial.one F eq F.zero F.one F.opp F.add F.sub F.mul _ F.eq_dec _ poly_ops poly_defs F.inv F.div _).
  Local Notation eq1 := (@Polynomial.eq1 F eq F.zero _ poly_ops F.div).
  Local Notation add := (@Polynomial.add F eq F.zero F.one F.opp F.add F.sub F.mul _ F.eq_dec _ poly_ops poly_defs F.inv F.div _).
  Local Notation mul := (@Polynomial.mul F eq F.zero F.one F.opp F.add F.sub F.mul _ F.eq_dec _ poly_ops poly_defs F.inv F.div _).

  Program Definition Pquotl_app {ql1 ql2} (pl: Pquotl ql1 * Pquotl ql2): Pquotl (ql1 ++ ql2) :=
    proj1_sig (fst pl) ++ proj1_sig (snd pl).
  Next Obligation. apply Forall2_app; [apply (proj2_sig p)|apply (proj2_sig p0)]. Qed.

  Lemma Pquotl_app_homomorphism {ql1 ql2}:
    @Ring.is_homomorphism
      (Pquotl ql1 * Pquotl ql2) (fun x y => eql (fst x) (fst y) /\ eql (snd x) (snd y)) (onel, onel) (Ring.apply_binop_pair addl addl) (Ring.apply_binop_pair mull mull)
      (Pquotl (ql1 ++ ql2)) eql onel addl mull
      Pquotl_app.
  Proof.
    repeat constructor.
    - intros a b; destruct a as (a1 & a2); destruct b as (b1 & b2).
      pose proof (Hlena1 := Forall2_length (proj2_sig a1)).
      pose proof (Hlenb1 := Forall2_length (proj2_sig b1)).
      unfold eql; simpl. rewrite ListUtil.map2_app by congruence.
      apply Forall2_app; rewrite (ListUtil.Forall2_forall_iff _ _ _ Pzero Pzero); reflexivity.
    - intros x y (Hl & Hr). destruct x as (x1 & x2). destruct y as (y1 & y2).
      unfold eql; simpl. apply Forall2_app; [apply Hl|apply Hr].
    - intros a b; destruct a as (a1 & a2); destruct b as (b1 & b2).
      pose proof (Hlena1 := Forall2_length (proj2_sig a1)).
      pose proof (Hlenb1 := Forall2_length (proj2_sig b1)).
      unfold eql; simpl. rewrite ListUtil.map2_app by congruence.
      rewrite ListUtil.map2_app.
      + apply Forall2_app; rewrite (ListUtil.Forall2_forall_iff _ _ _ Pzero Pzero); reflexivity.
      + rewrite ListUtil.map2_length; Lia.lia.
    - unfold eql; cbn. rewrite app_length.
      rewrite <- ListUtil.map2_app by (rewrite repeat_length; reflexivity).
      rewrite repeat_app.
      rewrite (ListUtil.Forall2_forall_iff _ _ _ Pzero Pzero); reflexivity.
  Qed.

  Program Definition Pquotl_split {ql1 ql2} (pl: Pquotl (ql1 ++ ql2)): Pquotl ql1 * Pquotl ql2 :=
    (exist _ (List.firstn (length ql1) (proj1_sig pl)) _, exist _ (List.skipn (length ql1) (proj1_sig pl)) _).
  Next Obligation.
    pose proof (Hlen := Forall2_length (proj2_sig pl)).
    pose proof (X := proj2_sig pl). rewrite app_length in Hlen.
    rewrite <- (firstn_skipn (length ql1) (proj1_sig pl)) in X.
    apply Forall2_app_inv in X.
    2: rewrite firstn_length; Lia.lia.
    apply X.
  Qed.
  Next Obligation.
    pose proof (Hlen := Forall2_length (proj2_sig pl)).
    pose proof (X := proj2_sig pl). rewrite app_length in Hlen.
    rewrite <- (firstn_skipn (length ql1) (proj1_sig pl)) in X.
    apply Forall2_app_inv in X.
    2: rewrite firstn_length; Lia.lia.
    apply X.
  Qed.

  Lemma Pquotl_split_homomorphism {ql1 ql2}:
    @Ring.is_homomorphism
      (Pquotl (ql1 ++ ql2)) eql onel addl mull
      (Pquotl ql1 * Pquotl ql2) (fun x y => eql (fst x) (fst y) /\ eql (snd x) (snd y)) (onel, onel) (Ring.apply_binop_pair addl addl) (Ring.apply_binop_pair mull mull)
      Pquotl_split.
  Proof.
    repeat constructor.
    - destruct a as (a & Ha); destruct b as (b & Hb).
      pose proof (Hlena := Forall2_length Ha).
      pose proof (Hlenb := Forall2_length Hb).
      unfold eql; cbn. rewrite (ListUtil.Forall2_forall_iff _ _ _ Pzero Pzero).
      + intros. rewrite (ListUtil.nth_default_map2 _ _ _ _ _ Pzero Pzero).
        repeat rewrite firstn_length. rewrite Hlena, Hlenb, app_length.
        repeat rewrite min_l by Lia.lia.
        repeat rewrite ListUtil.nth_default_firstn.
        rewrite (ListUtil.nth_default_map2 _ _ _ _ _ Pzero Pzero).
        rewrite ListUtil.map2_length, Hlena, Hlenb, app_length.
        rewrite min_l by Lia.lia.
        rewrite firstn_length, ListUtil.map2_length, Hlena, Hlenb, app_length, min_l in H by Lia.lia.
        destruct (Compare_dec.le_dec _ _); [|Lia.lia].
        destruct (Compare_dec.lt_dec _ _); [|Lia.lia].
        destruct (Compare_dec.lt_dec _ _); [|Lia.lia]. reflexivity.
      + rewrite firstn_length, ListUtil.map2_length, ListUtil.map2_length, firstn_length, firstn_length, Hlena, Hlenb, app_length.
        repeat rewrite min_l by Lia.lia. reflexivity.
    - destruct a as (a & Ha); destruct b as (b & Hb).
      pose proof (Hlena := Forall2_length Ha).
      pose proof (Hlenb := Forall2_length Hb).
      unfold eql; cbn. rewrite (ListUtil.Forall2_forall_iff _ _ _ Pzero Pzero).
      + intros. rewrite (ListUtil.nth_default_map2 _ _ _ _ _ Pzero Pzero).
        repeat rewrite skipn_length. rewrite Hlena, Hlenb, app_length.
        repeat rewrite min_l by Lia.lia.
        repeat rewrite ListUtil.nth_default_skipn.
        rewrite (ListUtil.nth_default_map2 _ _ _ _ _ Pzero Pzero).
        rewrite Hlena, Hlenb, app_length.
        rewrite min_l by Lia.lia.
        rewrite skipn_length, ListUtil.map2_length, Hlena, Hlenb, app_length, min_l in H by Lia.lia.
        destruct (Compare_dec.lt_dec _ _); [|Lia.lia].
        destruct (Compare_dec.lt_dec _ _); [|Lia.lia]. reflexivity.
      + rewrite skipn_length, ListUtil.map2_length, ListUtil.map2_length, skipn_length, skipn_length, Hlena, Hlenb, app_length.
        repeat rewrite min_l by Lia.lia. reflexivity.
    - destruct x as (x & Hx); destruct y as (y & Hy).
      pose proof (Hlenx := Forall2_length Hx).
      pose proof (Hleny := Forall2_length Hy).
      unfold eql in *; cbn in *.
      rewrite <- (firstn_skipn (length ql1) x), <- (firstn_skipn (length ql1) y) in H.
      apply Forall2_app_inv in H.
      2: rewrite firstn_length, firstn_length, Hlenx, Hleny; reflexivity.
      apply H.
    - destruct x as (x & Hx); destruct y as (y & Hy).
      pose proof (Hlenx := Forall2_length Hx).
      pose proof (Hleny := Forall2_length Hy).
      unfold eql in *; cbn in *.
      rewrite <- (firstn_skipn (length ql1) x), <- (firstn_skipn (length ql1) y) in H.
      apply Forall2_app_inv in H.
      2: rewrite firstn_length, firstn_length, Hlenx, Hleny; reflexivity.
      apply H.
    - destruct x as (x & Hx); destruct y as (y & Hy).
      pose proof (Hlenx := Forall2_length Hx).
      pose proof (Hleny := Forall2_length Hy).
      unfold eql; cbn. rewrite (ListUtil.Forall2_forall_iff _ _ _ Pzero Pzero).
      + rewrite firstn_length, ListUtil.map2_length, ListUtil.map2_length, Hlenx, Hleny, app_length.
        repeat rewrite min_l by Lia.lia. intros.
        repeat rewrite ListUtil.nth_default_firstn.
        repeat rewrite (ListUtil.nth_default_map2 _ _ _ _ _ Pzero Pzero).
        repeat rewrite ListUtil.map2_length. repeat rewrite firstn_length.
        rewrite Hlenx, Hleny, app_length. repeat rewrite min_l by Lia.lia.
        destruct (Compare_dec.le_dec _ _); [|Lia.lia].
        destruct (Compare_dec.lt_dec _ _); [|Lia.lia].
        destruct (Compare_dec.lt_dec _ _); [|Lia.lia].
        repeat rewrite ListUtil.nth_default_firstn.
        rewrite Hlenx, Hleny, app_length. repeat rewrite min_l by Lia.lia.
        rewrite ListUtil.nth_default_app.
        destruct (Compare_dec.le_dec _ _); [|Lia.lia].
        destruct (Compare_dec.lt_dec _ _); [|Lia.lia].
        reflexivity.
      + rewrite firstn_length, ListUtil.map2_length, ListUtil.map2_length, ListUtil.map2_length, ListUtil.map2_length, firstn_length, firstn_length, Hlenx, Hleny, app_length.
        repeat rewrite min_l by Lia.lia. reflexivity.
    - destruct x as (x & Hx); destruct y as (y & Hy).
      pose proof (Hlenx := Forall2_length Hx).
      pose proof (Hleny := Forall2_length Hy).
      unfold eql; cbn. rewrite (ListUtil.Forall2_forall_iff _ _ _ Pzero Pzero).
      + rewrite skipn_length, ListUtil.map2_length, ListUtil.map2_length, Hlenx, Hleny, app_length.
        repeat rewrite min_l by Lia.lia. intros.
        repeat rewrite ListUtil.nth_default_skipn.
        repeat rewrite (ListUtil.nth_default_map2 _ _ _ _ _ Pzero Pzero).
        repeat rewrite ListUtil.map2_length. repeat rewrite skipn_length.
        rewrite Hlenx, Hleny, app_length. repeat rewrite min_l by Lia.lia.
        destruct (Compare_dec.lt_dec _ _); [|Lia.lia].
        destruct (Compare_dec.lt_dec _ _); [|Lia.lia].
        repeat rewrite ListUtil.nth_default_skipn.
        rewrite ListUtil.nth_default_app.
        destruct (Compare_dec.lt_dec _ _); [Lia.lia|].
        assert (_ + _ - _ = i)%nat as -> by Lia.lia.
        reflexivity.
      + rewrite skipn_length, ListUtil.map2_length, ListUtil.map2_length, ListUtil.map2_length, ListUtil.map2_length, skipn_length, skipn_length, Hlenx, Hleny, app_length.
        repeat rewrite min_l by Lia.lia. reflexivity.
    - unfold eql; cbn. rewrite app_length, (ListUtil.Forall2_forall_iff _ _ _ Pzero Pzero).
      + rewrite firstn_length, ListUtil.map2_length, repeat_length, app_length.
        repeat rewrite min_l by Lia.lia. intros.
        rewrite ListUtil.nth_default_firstn.
        repeat rewrite (ListUtil.nth_default_map2 _ _ _ _ _ Pzero Pzero).
        repeat rewrite ListUtil.nth_default_repeat.
        rewrite ListUtil.map2_length, app_length.
        repeat rewrite repeat_length.
        repeat rewrite min_l by Lia.lia.
        rewrite ListUtil.nth_default_app.
        destruct (Compare_dec.le_dec _ _); [|Lia.lia].
        destruct (Compare_dec.lt_dec _ _); [|Lia.lia].
        destruct (Compare_dec.lt_dec _ _); [|Lia.lia].
        destruct (Decidable.dec _); [|Lia.lia].
        destruct (Decidable.dec _); [|Lia.lia].
        reflexivity.
      + rewrite firstn_length, ListUtil.map2_length, ListUtil.map2_length, repeat_length, repeat_length, app_length.
        repeat rewrite min_l by Lia.lia. reflexivity.
    - unfold eql; cbn. rewrite app_length, (ListUtil.Forall2_forall_iff _ _ _ Pzero Pzero).
      + rewrite skipn_length, ListUtil.map2_length, repeat_length, app_length.
        repeat rewrite min_l by Lia.lia. intros.
        rewrite ListUtil.nth_default_skipn.
        repeat rewrite (ListUtil.nth_default_map2 _ _ _ _ _ Pzero Pzero).
        repeat rewrite ListUtil.nth_default_repeat.
        repeat rewrite repeat_length. rewrite app_length.
        repeat rewrite min_l by Lia.lia.
        rewrite ListUtil.nth_default_app.
        destruct (Compare_dec.lt_dec _ _); [|Lia.lia].
        destruct (Compare_dec.lt_dec _ _); [Lia.lia|].
        destruct (Decidable.dec _); [|Lia.lia].
        destruct (Decidable.dec _); [|Lia.lia].
        destruct (Compare_dec.lt_dec _ _); [|Lia.lia].
        assert (_ + _ - _ = i)%nat as -> by Lia.lia. reflexivity.
      + rewrite skipn_length, ListUtil.map2_length, ListUtil.map2_length, repeat_length, repeat_length, app_length.
        repeat rewrite min_l by Lia.lia. Lia.lia.
  Qed.

  Program Definition Pquot_convert {q1 q2} (Heq: Peq q1 q2) (p: Pquot q1): Pquot q2 := proj1_sig p.
  Next Obligation.
    rewrite (proj2_sig p). apply peq_mod_proper; auto. apply (proj2_sig p).
  Qed.

  Lemma Pquot_convert_homomorphism {q1 q2} (Heq: Peq q1 q2):
    @Ring.is_homomorphism
      (Pquot q1) eq1 one add mul
      (Pquot q2) eq1 one add mul
      (Pquot_convert Heq).
  Proof.
    repeat constructor.
    - intros a b. destruct a as (a & Ha). destruct b as (b & Hb).
      unfold eq1; cbn. apply peq_mod_proper; [reflexivity|assumption].
    - intros a b H. destruct a as (a & Ha). destruct b as (b & Hb).
      unfold eq1 in *; cbn in *. assumption.
    - intros a b. destruct a as (a & Ha). destruct b as (b & Hb).
      unfold eq1; cbn. apply peq_mod_proper; [reflexivity|assumption].
    - unfold eq1; cbn. apply peq_mod_proper; [reflexivity|assumption].
  Qed.

  Program Definition Pquotl_convert {ql1 ql2} (Heql: Forall2 Peq ql1 ql2) (pl: Pquotl ql1): Pquotl ql2 :=
    proj1_sig pl.
  Next Obligation.
    pose proof (Hlen1 := Forall2_length Heql).
    pose proof (Hlen2 := Forall2_length (proj2_sig pl)).
    pose proof (X := proj2_sig pl). simpl in X.
    rewrite (ListUtil.Forall2_forall_iff _ _ _ Pzero Pzero) by congruence.
    rewrite (ListUtil.Forall2_forall_iff _ _ _ Pzero Pzero) in Heql by congruence.
    rewrite (ListUtil.Forall2_forall_iff _ _ _ Pzero Pzero) in X by congruence.
    intros. rewrite (X i H). apply Polynomial.peq_mod_proper.
    - apply (X i H).
    - apply (Heql i ltac:(congruence)).
  Qed.

  Lemma Pquotl_convert_homomorphism {ql1 ql2} (Heql: Forall2 Peq ql1 ql2):
    @Ring.is_homomorphism
      (Pquotl ql1) eql onel addl mull
      (Pquotl ql2) eql onel addl mull
      (Pquotl_convert Heql).
  Proof.
    repeat constructor.
    - intros a b. destruct a as (a & Ha). destruct b as (b & Hb).
      unfold eql; cbn. rewrite (ListUtil.Forall2_forall_iff _ _ _ Pzero); reflexivity.
    - intros a b. destruct a as (a & Ha). destruct b as (b & Hb).
      unfold eql; cbn. auto.
    - intros a b. destruct a as (a & Ha). destruct b as (b & Hb).
      unfold eql; cbn. rewrite (ListUtil.Forall2_forall_iff _ _ _ Pzero Pzero).
      + repeat rewrite ListUtil.map2_length. rewrite (Forall2_length Ha), (Forall2_length Hb).
        repeat rewrite min_l by Lia.lia. intros.
        repeat rewrite (ListUtil.nth_default_map2 _ _ _ _ _ Pzero Pzero).
        repeat rewrite ListUtil.map2_length. rewrite (Forall2_length Ha), (Forall2_length Hb), <- (Forall2_length Heql).
        repeat rewrite min_l by Lia.lia. intros.
        destruct (Compare_dec.lt_dec _ _); [|Lia.lia].
        apply peq_mod_proper; [reflexivity|].
        apply (proj1 (ListUtil.Forall2_forall_iff _ _ _ Pzero Pzero (Forall2_length Heql)) Heql); auto.
      + repeat rewrite ListUtil.map2_length. rewrite (Forall2_length Heql).
        reflexivity.
    - unfold eql; cbn. rewrite (Forall2_length Heql).
      rewrite (ListUtil.Forall2_forall_iff _ _ _ Pzero Pzero) by (do 2 rewrite ListUtil.map2_length; rewrite (Forall2_length Heql); reflexivity).
      rewrite ListUtil.map2_length. rewrite (Forall2_length Heql), repeat_length, min_l by Lia.lia.
      intros. repeat rewrite (ListUtil.nth_default_map2 _ _ _ _ _ Pzero Pzero).
      rewrite repeat_length, (Forall2_length Heql), min_l by Lia.lia.
      rewrite ListUtil.nth_default_repeat.
      destruct (Compare_dec.lt_dec _ _); [|Lia.lia].
      destruct (Decidable.dec _); [|Lia.lia].
      apply peq_mod_proper; [reflexivity|].
      apply (proj1 (ListUtil.Forall2_forall_iff _ _ _ Pzero Pzero (Forall2_length Heql)) Heql).
      rewrite (Forall2_length Heql); auto.
  Qed.

  Lemma zeta_pow_nz:
    forall k, zeta ^ k <> 0.
  Proof.
    apply N.peano_ind.
    - rewrite F.pow_0_r. symmetry; apply Hierarchy.zero_neq_one.
    - intros n IH. rewrite F.pow_succ_r.
      intro X. apply Hierarchy.zero_product_zero_factor in X.
      destruct X as [X|X]; [|elim IH; auto].
      rewrite X in Hm. rewrite F.pow_0_l in Hm by Lia.lia.
      symmetry in Hm. apply Group.inv_id_iff in Hm.
      rewrite Group.inv_inv in Hm.
      symmetry in Hm. apply Hierarchy.zero_neq_one in Hm; auto.
  Qed.

  Lemma zeta_pow_succ_m:
    zeta ^ (N.pow 2 (N.succ m)) = 1.
  Proof.
    rewrite N.pow_succ_r', N.mul_comm, <- F.pow_pow_l, Hm.
    rewrite F.pow_2_r, (@Ring.mul_opp_l F eq _ _ _ _ _ _ _ 1 _), (@Ring.mul_opp_r F eq _ _ _ _ _ _ _ _ 1).
    rewrite (@Group.inv_inv F _ _ _ _ _).
    apply Hierarchy.left_identity.
  Qed.

  Lemma zeta_pow_mod:
    forall k, zeta ^ k = zeta ^ (k mod (N.pow 2 (N.succ m))).
  Proof.
    intros k; rewrite (N.Div0.div_mod k (N.pow 2 (N.succ m))) at 1.
    rewrite F.pow_add_r, <- F.pow_pow_l.
    rewrite zeta_pow_succ_m, F.pow_1_l.
    apply Hierarchy.left_identity.
  Qed.

  Lemma neg_zeta_power_eq:
    forall k,
      F.opp (zeta ^ k) = zeta ^ (N.add (N.pow 2 m) k).
  Proof.
    intros k. rewrite F.pow_add_r, Hm.
    rewrite Ring.mul_opp_l, (@Hierarchy.left_identity F eq F.mul _ _ _).
    reflexivity.
  Qed.

  Section Inductive_Case.
    Context (rec_decompose: nat -> nat -> list nat).

    Let rec_decomposition := fun r' k l => List.map (fun n => posicyclic (Nat.pow 2 (k - r')) (F.pow zeta (N.of_nat n))) (rec_decompose r' l).

    Context
      (rec_ntt: forall (r' k l: nat), (r' <= k)%nat -> (r' <= m)%nat -> (Nat.modulo l (Nat.pow 2 r') = 0)%nat -> Pquot (posicyclic (Nat.pow 2 k) (zeta ^ l)) -> Pquotl (rec_decomposition r' k l))
      (rec_intt: forall (r' k l: nat), (r' <= k)%nat -> (r' <= m)%nat -> (Nat.modulo l (Nat.pow 2 r') = 0)%nat -> Pquotl (rec_decomposition r' k l) -> Pquot (posicyclic (Nat.pow 2 k) (zeta ^ l))).

    Context (r' k l: nat) (r := S r').
    Context (r_leq_k: (r <= k)%nat).
    Context (r_leq_m: (r <= m)%nat).
    Context (r_leq_l: (Nat.modulo l (Nat.pow 2 r) = 0)%nat).

    Context
      (h_rec_ntt_isomorphism:
        forall (k: nat) (l: nat)
          (Hr_leq_k: (r' <= k)%nat)
          (Hr_leq_m: (r' <= m)%nat)
          (Hr_leq_l: (Nat.modulo l (Nat.pow 2 r') = 0)%nat),
          @Hierarchy.ring _ (eql (ql:=(rec_decomposition r' k l))) zerol onel oppl addl subl mull
          /\ @Ring.is_homomorphism _ eq1 one add mul _ eql onel addl mull (rec_ntt r' k l Hr_leq_k Hr_leq_m Hr_leq_l)
          /\ @Ring.is_homomorphism _ eql onel addl mull _ eq1 one add mul (rec_intt r' k l Hr_leq_k Hr_leq_m Hr_leq_l)).

    Let m0 := (posicyclic (Nat.pow 2 k) (zeta ^ N.of_nat l)).
    Let m1 := (posicyclic (Nat.pow 2 (k - 1)) (zeta ^ (N.of_nat (Nat.div l 2)))).
    Let m2 := (posicyclic (Nat.pow 2 (k - 1)) (zeta ^ (N.of_nat (Nat.pow 2 m + Nat.div l 2)))).

    Local Lemma r_leq_k': (r' <= k - 1)%nat. Proof. Lia.lia. Qed.
    Local Lemma r_leq_m': (r' <= m)%nat. Proof. Lia.lia. Qed.
    Local Lemma r_leq_l_lhs: (Nat.modulo (Nat.div l 2) (Nat.pow 2 r') = 0)%nat.
    Proof.
      rewrite <- PeanoNat.Nat.Div0.div_exact in r_leq_l.
      rewrite <- PeanoNat.Nat.Div0.div_exact.
      rewrite PeanoNat.Nat.Div0.div_div.
      rewrite r_leq_l at 1. unfold r; rewrite PeanoNat.Nat.pow_succ_r'.
      assert (2 * _ * _ = (PeanoNat.Nat.pow 2 r' * PeanoNat.Nat.div l (2 * PeanoNat.Nat.pow 2 r')) * 2)%nat as -> by Lia.lia.
      rewrite PeanoNat.Nat.div_mul by congruence. reflexivity.
    Qed.

    Local Lemma r_leq_l_rhs: (Nat.modulo (Nat.pow 2 m + Nat.div l 2) (Nat.pow 2 r') = 0)%nat.
    Proof.
      assert (m = r' + (m - r'))%nat as -> by Lia.lia.
      rewrite PeanoNat.Nat.pow_add_r.
      rewrite PeanoNat.Nat.add_comm, PeanoNat.Nat.mul_comm, PeanoNat.Nat.Div0.mod_add.
      apply r_leq_l_lhs.
    Qed.

    Local Lemma ok_m0:
      Peq m0 (posicyclic (2 * (Nat.pow 2 (k - 1))) ((zeta ^ (N.of_nat (Nat.div l 2))) * (zeta ^ (N.of_nat (Nat.div l 2))))%F).
    Proof.
      rewrite <- PeanoNat.Nat.pow_succ_r'.
      assert (S (k - 1) = k) as -> by Lia.lia.
      assert (_ * _ = zeta ^ l) as ->.
      { rewrite <- F.pow_2_r, F.pow_pow_l. f_equal.
        assert (2 = N.of_nat 2)%N as -> by reflexivity.
        rewrite <- Nnat.Nat2N.inj_mul, Nnat.Nat2N.inj_iff.
        rewrite <- PeanoNat.Nat.Div0.div_exact in r_leq_l.
        rewrite r_leq_l.
        unfold r. rewrite PeanoNat.Nat.pow_succ_r'.
        assert (2 * _ * _ = (PeanoNat.Nat.pow 2 r' * PeanoNat.Nat.div l (2 * PeanoNat.Nat.pow 2 r')) * 2)%nat as -> by Lia.lia.
        rewrite PeanoNat.Nat.div_mul by congruence. reflexivity. }
      reflexivity.
    Qed.

    Local Lemma ok_m1:
      Peq m1 (posicyclic (Nat.pow 2 (k - 1)) (zeta ^ (N.of_nat (Nat.div l 2)))).
    Proof. reflexivity. Qed.

    Local Lemma ok_m2:
      Peq m2 (negacyclic (Nat.pow 2 (k - 1)) (zeta ^ (N.of_nat (Nat.div l 2)))).
    Proof.
      rewrite <- posicyclic_opp, neg_zeta_power_eq.
      assert (2 ^ N.of_nat m = Nat.pow 2 m)%N as -> by (rewrite Nnat.Nat2N.inj_pow; reflexivity).
      rewrite <- Nnat.Nat2N.inj_add. reflexivity.
    Qed.

    Definition ntt2:
      Pquot m0 ->
      Pquot m1 * Pquot m2 :=
      @Polynomial.phi2 F eq F.zero F.one F.opp F.add F.sub F.mul _ F.eq_dec _ poly_ops poly_defs F.inv F.div _ m0 m1 m2.

    Program Definition intt2:
      Pquot m1 * Pquot m2 ->
      Pquot m0 :=
      @NTT_base_psi F eq F.zero F.one F.opp F.add F.sub F.mul _ F.eq_dec _ poly_ops poly_defs F.inv F.div _ char_ge_3 (Nat.pow 2 (k - 1)) _ m0 m1 m2 _ (zeta_pow_nz _) ok_m0 ok_m1 ok_m2.
    Next Obligation. pose proof (X := NatUtil.pow_nonzero 2 (k - 1) ltac:(Lia.lia)). Lia.lia. Qed.

    Lemma ntt_isomorphism2:
      @Hierarchy.ring _ (EQ2 m1 m2) (ZERO2 m1 m2) (ONE2 m1 m2) (OPP2 m1 m2) (ADD2 m1 m2) (SUB2 m1 m2) (MUL2 m1 m2)
      /\ @Ring.is_homomorphism _ eq1 one add mul _ (EQ2 m1 m2) (ONE2 m1 m2) (ADD2 m1 m2) (MUL2 m1 m2) ntt2
      /\ @Ring.is_homomorphism _ (EQ2 m1 m2) (ONE2 m1 m2) (ADD2 m1 m2) (MUL2 m1 m2) _ eq1 one add mul intt2.
    Proof. apply NTT_ring_isomorphism2. Qed.

    Definition decompose_body': list nat :=
      (rec_decompose r' (Nat.div l 2)) ++ (rec_decompose r' (Nat.pow 2 m + Nat.div l 2)).

    Let decomposition_body' := List.map (fun n => posicyclic (Nat.pow 2 (k - r)) (F.pow zeta (N.of_nat n))) decompose_body'.

    Lemma decomposition_body_spec':
      Forall2 Peq ((rec_decomposition r' (k - 1) (Nat.div l 2)) ++ (rec_decomposition r' (k - 1) (Nat.pow 2 m + Nat.div l 2))) decomposition_body'.
    Proof.
      unfold decomposition_body', decompose_body'.
      rewrite List.map_app. unfold rec_decomposition.
      assert (k - 1 - r' = k - r)%nat as -> by Lia.lia.
      rewrite (ListUtil.Forall2_forall_iff _ _ _ Pzero) by reflexivity.
      intros; reflexivity.
    Qed.

    Lemma decomposition_body_spec'':
      Forall2 Peq decomposition_body' ((rec_decomposition r' (k - 1) (Nat.div l 2)) ++ (rec_decomposition r' (k - 1) (Nat.pow 2 m + Nat.div l 2))).
    Proof. apply Forall2_flip. eapply Forall2_impl; [|apply decomposition_body_spec']. intros; symmetry; assumption. Qed.

    Definition ntt_body' (p: Pquot m0): Pquotl decomposition_body' :=
      Pquotl_convert decomposition_body_spec' (Pquotl_app (Ring.apply_unop_pair (rec_ntt r' (k - 1) (Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_lhs) (rec_ntt r' (k - 1) (Nat.pow 2 m + Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_rhs) (ntt2 p))).

    Definition intt_body' (pl: Pquotl decomposition_body'): Pquot m0 :=
      intt2 (Ring.apply_unop_pair (rec_intt r' (k - 1) (Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_lhs) (rec_intt r' (k - 1) (Nat.pow 2 m + Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_rhs) (Pquotl_split (Pquotl_convert decomposition_body_spec'' pl))).

    Lemma ntt_isomorphism':
      @Hierarchy.ring _ (eql (ql:=decomposition_body')) zerol onel oppl addl subl mull
      /\ @Ring.is_homomorphism _ eq1 one add mul _ eql onel addl mull ntt_body'
      /\ @Ring.is_homomorphism _ eql onel addl mull _ eq1 one add mul intt_body'.
    Proof.
      pose proof (Hlhs_iso := h_rec_ntt_isomorphism (k - 1) (Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_lhs).
      pose proof (Hrhs_iso := h_rec_ntt_isomorphism (k - 1) (Nat.pow 2 m + Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_rhs).
      destruct Hlhs_iso as (Hlhs_ring & Hlhs_ntt & Hlhs_intt).
      destruct Hrhs_iso as (Hrhs_ring & Hrhs_ntt & Hrhs_intt).
      pose proof (Hntt := ntt_isomorphism2).
      destruct Hntt as (Hring & Hntt2 & Hintt2).
      split; [apply PquotlRing|]. split.
      - eapply (@Ring.compose_homomorphism _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Pquotl_convert_homomorphism _)). Unshelve.
        eapply (@Ring.compose_homomorphism _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Pquotl_app_homomorphism)). Unshelve.
        eapply (@Ring.compose_homomorphism _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@product_homomorphism _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hlhs_ntt Hrhs_ntt)). Unshelve.
        4: eapply Ring.product_ring.
      - eapply (@Ring.compose_homomorphism _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hintt2). Unshelve.
        eapply (@Ring.compose_homomorphism _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@product_homomorphism _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hlhs_intt Hrhs_intt)). Unshelve.
        eapply (@Ring.compose_homomorphism _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Pquotl_split_homomorphism)). Unshelve.
        4: apply Ring.product_ring.
        apply (Pquotl_convert_homomorphism _).
    Qed.
  End Inductive_Case.

  Definition decompose_body rec_decompose (r l: nat): list nat :=
    match r with
    | S r' => decompose_body' rec_decompose r' l
    | O => [l]
    end.

  Fixpoint decompose (r l: nat): list nat := decompose_body decompose r l.

  Definition decomposition (r k l: nat) :=
    List.map (fun n => posicyclic (Nat.pow 2 (k - r)%nat) (zeta ^ (N.of_nat n))) (decompose r l).

  Program Definition ntt_body rec_ntt (r k l : nat) (Hr_leq_k: (r <= k)%nat) (Hr_leq_m: (r <= m)%nat) (Hr_leq_l: Nat.modulo l (Nat.pow 2 r) = 0%nat): Pquot (posicyclic (Nat.pow 2 k) (zeta ^ N.of_nat l)) -> Pquotl (decomposition r k l) :=
    match r with
    | S r' => ntt_body' decompose rec_ntt r' k l Hr_leq_k Hr_leq_m Hr_leq_l
    | O => fun p => [proj1_sig p]
    end.
  Next Obligation. constructor; [|constructor]. rewrite PeanoNat.Nat.sub_0_r. apply (proj2_sig p). Qed.

  Fixpoint ntt' (r k l: nat) :=
    ntt_body ntt' r k l.

  Program Definition ntt (n: nat) p :=
    ntt' (Nat.min n m) n (Nat.pow 2 m) _ _ _ p.
  Next Obligation. Lia.lia. Qed.
  Next Obligation. Lia.lia. Qed.
  Next Obligation.
    replace m with ((m - (Nat.min n m)) + Nat.min n m)%nat at 1 by Lia.lia.
    rewrite PeanoNat.Nat.pow_add_r.
    rewrite <- PeanoNat.Nat.Div0.div_exact.
    rewrite PeanoNat.Nat.div_mul by (apply PeanoNat.Nat.pow_nonzero; congruence).
    apply PeanoNat.Nat.mul_comm.
  Qed.

  Program Definition intt_body rec_intt (r k l : nat) (Hr_leq_k: (r <= k)%nat) (Hr_leq_m: (r <= m)%nat) (Hr_leq_l: Nat.modulo l (Nat.pow 2 r) = 0%nat): Pquotl (decomposition r k l) -> Pquot (posicyclic (Nat.pow 2 k) (zeta ^ N.of_nat l)) :=
    match r with
    | S r' => intt_body' decompose rec_intt r' k l _ _ _
    | O => fun pl => List.hd Pzero (proj1_sig pl)
    end.
  Next Obligation.
    cbv [decomposition decompose decompose_body map] in pl.
    destruct pl as [pl Hpl]. simpl.
    inversion Hpl; subst; clear Hpl. inversion H4; subst; clear H4.
    simpl. rewrite PeanoNat.Nat.sub_0_r in H3. exact H3.
  Qed.

  Fixpoint intt' (r k l: nat) :=
    intt_body intt' r k l.

  Program Definition intt (n: nat) pl :=
    intt' (Nat.min n m) n (Nat.pow 2 m) _ _ _ pl.
  Next Obligation. Lia.lia. Qed.
  Next Obligation. Lia.lia. Qed.
  Next Obligation.
    replace m with ((m - (Nat.min n m)) + Nat.min n m)%nat at 1 by Lia.lia.
    rewrite PeanoNat.Nat.pow_add_r.
    rewrite <- PeanoNat.Nat.Div0.div_exact.
    rewrite PeanoNat.Nat.div_mul by (apply PeanoNat.Nat.pow_nonzero; congruence).
    apply PeanoNat.Nat.mul_comm.
  Qed.

  Lemma ntt_rec_isomorphism:
    forall r k l (Hr_leq_k: (r <= k)%nat) (Hr_leq_m: (r <= m)%nat) (Hr_leq_l: Nat.modulo l (Nat.pow 2 r) = 0%nat),
      @Ring.is_homomorphism _ eq1 one add mul _ eql onel addl mull (ntt' r k l Hr_leq_k Hr_leq_m Hr_leq_l)
      /\ @Ring.is_homomorphism _ eql onel addl mull _ eq1 one add mul (intt' r k l Hr_leq_k Hr_leq_m Hr_leq_l).
  Proof.
    induction r; intros.
    - simpl. eapply Ring.ring_by_isomorphism; simpl.
      + intros x. destruct x as [x Hx]; unfold eq1; reflexivity.
      + intros a b. destruct a as [a Ha]; destruct b as [b Hb].
        unfold eq1, eql; simpl. destruct a as [|x]; inversion Ha; subst.
        destruct b as [|y]; inversion Hb; subst.
        inversion H4; inversion H6; subst.
        simpl. split; intros; [repeat constructor; auto|].
        inversion H; auto.
      + instantiate (1 := zerol).
        unfold zerol, zero, eq1; simpl; rewrite Pmod_0_l. reflexivity.
      + unfold onel, one, eq1; simpl.
        rewrite PeanoNat.Nat.sub_0_r. reflexivity.
      + instantiate (1 := oppl).
        intro a. destruct a as [a Ha]; unfold eq1; simpl.
        inversion Ha; subst. simpl. rewrite Pmod_opp.
        rewrite H2 at 1. rewrite PeanoNat.Nat.sub_0_r. reflexivity.
      + intros a b. destruct a as [a Ha]; destruct b as [b Hb].
        unfold eq1; simpl. inversion Ha; subst. inversion Hb; subst; simpl.
        rewrite H2, H4 at 1. rewrite Pmod_distr, PeanoNat.Nat.sub_0_r. reflexivity.
      + instantiate (1 := subl).
        intros a b. destruct a as [a Ha]; destruct b as [b Hb].
        unfold eq1; simpl. inversion Ha; subst. inversion Hb; subst; simpl.
        rewrite PeanoNat.Nat.sub_0_r in H4.
        rewrite Pmod_opp, <- H4, Hierarchy.ring_sub_definition.
        rewrite H2, H4 at 1. rewrite Pmod_distr, Pmod_opp, PeanoNat.Nat.sub_0_r.
        reflexivity.
      + intros a b. destruct a as [a Ha]; destruct b as [b Hb].
        unfold eq1; simpl. inversion Ha; subst. inversion Hb; subst; simpl.
        rewrite PeanoNat.Nat.sub_0_r. reflexivity.
    - simpl; split; eapply ntt_isomorphism'.
      + intros; split; [|eapply IHr]. apply PquotlRing.
      + intros; split; [|eapply IHr]. apply PquotlRing.
  Qed.

  Lemma ntt_isomorphism:
    forall n,
      @Ring.is_homomorphism _ eq1 one add mul _ eql onel addl mull (ntt n)
      /\ @Ring.is_homomorphism _ eql onel addl mull _ eq1 one add mul (intt n).
  Proof. intros; unfold ntt, intt. split; eapply ntt_rec_isomorphism. Qed.

End CyclotomicDecomposition.

Section SanityCheck.
  Local Definition bitrev (n: nat) (i: nat): nat :=
    let fix aux k := match k with
                     | O => if Nat.testbit i 0%nat then PeanoNat.Nat.setbit 0%nat (n - 1)%nat else 0%nat
                     | S k' => if Nat.testbit i k then PeanoNat.Nat.setbit (aux k') (n - 1 - k)%nat else aux k'
                     end in
    aux (n - 1)%nat.

  Local Notation bitrev8 := (bitrev 8%nat). (* Dilithium *)
  Local Notation bitrev7 := (bitrev 7%nat). (* Kyber *)

  (* Making sure the decomposition returns the same order expected by ML-DSA
     aka Dilithium *)
  (* See Section 7.5 of https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf *)
  Local Lemma dilithium_ok:
    (@decompose 8%nat 8%nat (Nat.pow 2 8)) = List.map (fun k => (2 * (bitrev8 k) + 1)%nat) (seq 0 256%nat).
  Proof. reflexivity. Qed.

  (* Making sure the decomposition returns the same order expected by ML-KEM
     aka Kyber *)
  (* See Section 4.3 of https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.203.pdf *)
  Local Lemma kyber_ok:
    (@decompose 7%nat 7%nat (Nat.pow 2 7)) = List.map (fun k => (2 * (bitrev7 k) + 1)%nat) (seq 0 128%nat).
  Proof. reflexivity. Qed.
End SanityCheck.
