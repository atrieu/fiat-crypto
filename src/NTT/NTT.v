Require Import Coq.PArith.BinPosDef. Local Open Scope positive_scope.
Require Import Coq.NArith.BinNat.
From Coq.Classes Require Import Morphisms.
Require Import Spec.ModularArithmetic.
Require Import Arithmetic.ModularArithmeticTheorems.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.Znumtheory Coq.Lists.List. Import ListNotations.
Require Import NTT.Polynomial NTT.PolynomialCRT.
Require PrimeFieldTheorems.

Require Import coqutil.Datatypes.List.

(** This file formalizes the (algebraic form of the) Number-Theoretic Theorem.
    Specifically, provided `ζ` such that `ζ^{2^m} = 1`, we define [decompose] such that `X^{2^n} + 1 = Π_{k ∈ decompose r n 2^m } (X^{2^{n - r}} - ζ^k)` when `r ≤ min(n, m)`.
    We then recursively define a ring isomorphism using the Chinese Remainder Theorem from `R[X]/(X^{2^n} + 1)` to `Π_{k ∈ decompose r n 2^m } R[X]/(X^{2^{n - r}} - ζ^k)`.

    We also define the corresponding versions using list representations ([nttl] and [inttl]), they are shown correct with regards to the ones using the polynomial representation.
*)

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

  (* Too many instances *)
  Remove Hints F.commutative_ring_modulo: typeclass_instances.

  Local Notation Peq := (@Polynomial.Peq F eq P _).
  Local Notation Pmod := (@Polynomial.Pmod F F.zero P _ F.div).
  Local Notation Pmul := (@Polynomial.Pmul _ _ poly_ops).
  Local Notation Pconst := (@Polynomial.Pconst _ _ poly_ops).
  Local Notation negacyclic := (@PolynomialCRT.negacyclic F P _).
  Local Notation posicyclic := (@PolynomialCRT.posicyclic F F.opp P _).
  Local Notation Pgcd := (Polynomial.Pgcd (poly_ops:=poly_ops)(poly_defs:=poly_defs)(Fdiv:=F.div)).
  Local Notation coprime := (Polynomial.coprime (poly_ops:=poly_ops)(poly_defs:=poly_defs)(Fdiv:=F.div)).
  Local Notation Pquotl := (@Polynomial.Pquotl F eq F.zero P _ F.div).
  Local Notation of_pl := (Polynomial.of_pl (poly_defs:=poly_defs) (Finv:=F.inv) (Fdiv:=F.div) (field:=field)).
  Local Notation CRT2 := (PolynomialCRT.phi2 (poly_ops:=poly_ops)).
  Local Notation iCRT2 := (PolynomialCRT.psi2 (Feq:=eq)(poly_ops:=poly_ops)).
  Local Notation Pquot := (@Polynomial.Pquot F eq F.zero P _ F.div).
  Local Notation one := (@Polynomial.one F eq F.zero F.one F.opp F.add F.sub F.mul _ F.eq_dec _ poly_ops poly_defs F.inv F.div _).
  Local Notation eq1 := (@Polynomial.eq1 F eq F.zero _ poly_ops F.div).
  Local Notation eq' := (Polynomial.eq' (Feq:=eq)).
  Local Notation eql' := (Polynomial.eql' (Feq:=eq)).
  Local Notation add := (@Polynomial.add F eq F.zero F.one F.opp F.add F.sub F.mul _ F.eq_dec _ poly_ops poly_defs F.inv F.div _).
  Local Notation add' := (Polynomial.add' (Fadd:=F.add)).
  Local Notation mul := (@Polynomial.mul F eq F.zero F.one F.opp F.add F.sub F.mul _ F.eq_dec _ poly_ops poly_defs F.inv F.div _).
  Local Notation addl' := (Polynomial.addl' (Fadd:=F.add)).
  Local Notation Pmod_cyclotomic_list := (@Pmod_cyclotomic_list F F.zero F.add F.sub F.mul).
  Local Notation recompose_cyclotomic_list := (@recompose_cyclotomic_list F F.zero F.add F.sub F.mul).

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
    Context (rec_decompose_length: forall r' l, length (rec_decompose r' l) = Nat.pow 2 r' :> _).

    Let rec_decomposition := fun r' k l => List.map (fun n => posicyclic (Nat.pow 2 (k - r')) (F.pow zeta (N.of_nat n))) (rec_decompose r' l).

    Context
      (rec_ntt: forall (r' k l: nat), (r' <= k)%nat -> (r' <= m)%nat -> (Nat.modulo l (Nat.pow 2 r') = 0)%nat -> Pquot (posicyclic (Nat.pow 2 k) (zeta ^ l)) -> Pquotl (rec_decomposition r' k l))
      (rec_intt: forall (r' k l: nat), (r' <= k)%nat -> (r' <= m)%nat -> (Nat.modulo l (Nat.pow 2 r') = 0)%nat -> Pquotl (rec_decomposition r' k l) -> Pquot (posicyclic (Nat.pow 2 k) (zeta ^ l))).

    Context
      (rec_ntt': forall (r' k l: nat), (r' <= k)%nat -> (r' <= m)%nat -> (Nat.modulo l (Nat.pow 2 r') = 0)%nat -> Pquot' (posicyclic (Nat.pow 2 k) (zeta ^ l)) -> Pquotl' (rec_decomposition r' k l))
      (rec_intt': forall (r' k l: nat), (r' <= k)%nat -> (r' <= m)%nat -> (Nat.modulo l (Nat.pow 2 r') = 0)%nat -> Pquotl' (rec_decomposition r' k l) -> Pquot' (posicyclic (Nat.pow 2 k) (zeta ^ l))).

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
          @Ring.is_isomorphism
            _ eq1 one add mul
            _ eql onel addl mull
            (rec_ntt r' k l Hr_leq_k Hr_leq_m Hr_leq_l)
            (rec_intt r' k l Hr_leq_k Hr_leq_m Hr_leq_l)).

    Context
      (h_rec_ntt_isomorphism':
        forall (k: nat) (l: nat)
          (Hr_leq_k: (r' <= k)%nat)
          (Hr_leq_m: (r' <= m)%nat)
          (Hr_leq_l: (Nat.modulo l (Nat.pow 2 r') = 0)%nat)
          (Hqnz: ~ Peq (posicyclic (Nat.pow 2 k) (zeta ^ l)) Pzero)
          (Hqlnz: Forall (fun q => ~ Peq q Pzero) (rec_decomposition r' k l)),
          @Ring.is_isomorphism
            _ eq' one' add' (mul' (Hqnz:=Hqnz))
            _ eql' onel' addl' (mull' (Hqlnz:=Hqlnz))
            (rec_ntt' r' k l Hr_leq_k Hr_leq_m Hr_leq_l)
            (rec_intt' r' k l Hr_leq_k Hr_leq_m Hr_leq_l)).

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

    Local Lemma m0_eq:
      eq m0 (posicyclic (2 * (Nat.pow 2 (k - 1))) ((zeta ^ (N.of_nat (Nat.div l 2))) * (zeta ^ (N.of_nat (Nat.div l 2))))%F).
    Proof.
      unfold m0. f_equal.
      - rewrite <- PeanoNat.Nat.pow_succ_r'.
        assert (S (k - 1) = k) as -> by Lia.lia.
        reflexivity.
      - rewrite <- F.pow_2_r, F.pow_pow_l. f_equal.
        assert (2 = N.of_nat 2)%N as -> by reflexivity.
        rewrite <- Nnat.Nat2N.inj_mul, Nnat.Nat2N.inj_iff.
        rewrite <- PeanoNat.Nat.Div0.div_exact in r_leq_l.
        rewrite r_leq_l.
        unfold r. rewrite PeanoNat.Nat.pow_succ_r'.
        assert (2 * _ * _ = (PeanoNat.Nat.pow 2 r' * PeanoNat.Nat.div l (2 * PeanoNat.Nat.pow 2 r')) * 2)%nat as -> by Lia.lia.
        rewrite PeanoNat.Nat.div_mul by congruence. reflexivity.
    Qed.

    Local Lemma ok_m0:
      Peq m0 (posicyclic (2 * (Nat.pow 2 (k - 1))) ((zeta ^ (N.of_nat (Nat.div l 2))) * (zeta ^ (N.of_nat (Nat.div l 2))))%F).
    Proof. rewrite m0_eq. reflexivity. Qed.

    Local Lemma m1_eq:
      eq m1 (posicyclic (Nat.pow 2 (k - 1)) (zeta ^ (N.of_nat (Nat.div l 2)))).
    Proof. reflexivity. Qed.

    Local Lemma ok_m1:
      Peq m1 (posicyclic (Nat.pow 2 (k - 1)) (zeta ^ (N.of_nat (Nat.div l 2)))).
    Proof. reflexivity. Qed.

    Local Lemma m2_eq:
      eq m2 (negacyclic (Nat.pow 2 (k - 1)) (zeta ^ (N.of_nat (Nat.div l 2)))).
    Proof.
      unfold m2, posicyclic. f_equal.
      rewrite Nnat.Nat2N.inj_add.
      assert (N.of_nat (Nat.pow 2 m) = 2 ^ N.of_nat m)%N as -> by (rewrite Nnat.Nat2N.inj_pow; reflexivity).
      rewrite <- neg_zeta_power_eq.
      rewrite Group.inv_inv. reflexivity.
    Qed.

    Local Lemma ok_m2:
      Peq m2 (negacyclic (Nat.pow 2 (k - 1)) (zeta ^ (N.of_nat (Nat.div l 2)))).
    Proof. rewrite m2_eq. reflexivity. Qed.

    Definition ntt2:
      Pquot m0 ->
      Pquot m1 * Pquot m2 :=
      CRT2 m0 m1 m2.

    Program Definition intt2:
      Pquot m1 * Pquot m2 ->
      Pquot m0 :=
      iCRT2 m0 m1 m2.

    Program Definition ntt2':
      Pquot' m0 ->
      Pquotl' [m1; m2] :=
      (Pmod_cyclotomic_list (Nat.pow 2 (k - 1)) (zeta ^ N.of_nat (Nat.div l 2))).
    Next Obligation.
      rewrite Pmod_cyclotomic_list_length, (proj2_sig x).
      unfold m0, m1, m2. repeat rewrite posicyclic_measure by (match goal with | |- context [Nat.pow ?x ?y] => pose proof (NatUtil.pow_nonzero x y ltac:(congruence)); Lia.lia end).
      assert (Nat.pow 2 k = 2 * (Nat.pow 2 (k - 1)) :> _)%nat as ->; [|Lia.lia].
      rewrite <- PeanoNat.Nat.pow_succ_r'. f_equal; Lia.lia.
    Qed.

    Program Definition intt2':
      Pquotl' [m1; m2] ->
      Pquot' m0 :=
      fun x => List.map (F.mul (F.inv (1 + 1))) (recompose_cyclotomic_list (Nat.pow 2 (k - 1)) (F.inv (zeta ^ N.of_nat (Nat.div l 2))) x).
    Next Obligation.
      rewrite length_map, recompose_cyclotomic_list_length.
      pose proof (proj2_sig x) as X. simpl in X. rewrite X.
      unfold m0, m1, m2. repeat rewrite posicyclic_measure by (match goal with | |- context [Nat.pow ?x ?y] => pose proof (NatUtil.pow_nonzero x y ltac:(congruence)); Lia.lia end).
      assert (Nat.pow 2 k = 2 * (Nat.pow 2 (k - 1)) :> _)%nat as ->; [|Lia.lia].
      rewrite <- PeanoNat.Nat.pow_succ_r'. f_equal; Lia.lia.
    Qed.

    Lemma ntt_isomorphism2:
      @Ring.is_isomorphism
        (Pquot m0) eq1 one add mul
        (Pquot m1 * Pquot m2) (EQ2 m1 m2) (ONE2 m1 m2) (ADD2 m1 m2) (MUL2 m1 m2)
        ntt2
        intt2.
    Proof.
      assert (Hcoprime: coprime m1 m2).
      { rewrite ok_m2. unfold m1.
        apply posicyclic_decomposition_coprime.
        - pose proof (NatUtil.pow_nonzero 2 (k - 1)%nat ltac:(congruence)); Lia.lia.
        - apply zeta_pow_nz. }
      assert (Heq: Peq m0 (Pmul m1 m2)).
      { rewrite ok_m2. unfold m1.
        rewrite <- posicyclic_decomposition. apply ok_m0. }
      apply (CRT_isomorphism2 m0 m1 m2 Hcoprime Heq).
    Qed.

    Lemma ntt_isomorphism2'
      (Hqnz: ~ Peq m0 Pzero)
      (Hqlnz: Forall (fun q => ~ Peq q Pzero) [m1; m2]):
      @Ring.is_isomorphism
        (Pquot' m0) eq' one' add' (mul' (Hqnz:=Hqnz))
        (Pquotl' [m1; m2]) eql' onel' addl' (mull' (Hqlnz:=Hqlnz))
        ntt2'
        intt2'.
    Proof.
      assert (Heq': forall x y: Pquot' m0, x = y <-> proj1_sig x = proj1_sig y).
      { intros x y; destruct x as (x & Hx); destruct y as (y & Hy).
        simpl. apply Decidable.eqsig_eq. }
      assert (Heql': forall x y: Pquotl' [m1; m2], x = y <-> proj1_sig x = proj1_sig y).
      { intros x y; destruct x as (x & Hx); destruct y as (y & Hy).
        simpl. apply Decidable.eqsig_eq. }
      assert (Hmeq: Forall2 Peq ([m1] ++ [m2]) ([m1; m2])) by reflexivity.
      assert (HF: forall (A: Type) (l1 l2: list A), Forall2 eq l1 l2 -> eq l1 l2).
      { induction 1; simpl; congruence. }
      assert (X: forall (p1: Pquot m1) (p2: Pquot m2), eq (recompose_cyclotomic_list (Nat.pow 2 (k - 1)) (F.inv (zeta ^ N.of_nat (Nat.div l 2))) ((proj1_sig (to_list' p1)) ++ (proj1_sig (to_list' p2)))) (map (F.mul (1 + 1)) (proj1_sig (to_list' (intt2 (p1, p2)))))).
      { intros; apply HF.
        pose proof (recompose_cyclotomic_list_spec (Nat.pow 2 (k - 1)) (zeta ^ N.of_nat (Nat.div l 2)) ltac:(pose proof (NatUtil.pow_nonzero 2 (k - 1)); Lia.lia) ltac:(apply zeta_pow_nz)) as X.
        rewrite <- m0_eq, <- m1_eq, <- m2_eq in X. apply X. }
      assert (Y: forall (p: Pquot m0), eq (Pmod_cyclotomic_list (Nat.pow 2 (k - 1)) (zeta ^ N.of_nat (Nat.div l 2)) (proj1_sig (to_list' p))) (proj1_sig (to_list' (fst (ntt2 p))) ++ proj1_sig (to_list' (snd (ntt2 p))))).
      { intros; apply HF.
        pose proof (Pmod_cyclotomic_list_spec (Nat.pow 2 (k - 1)) (zeta ^ N.of_nat (Nat.div l 2)) ltac:(pose proof (NatUtil.pow_nonzero 2 (k - 1)); Lia.lia) ltac:(apply zeta_pow_nz)) as Y.
        rewrite <- m0_eq, <- m1_eq, <- m2_eq in Y. apply Y. }
      assert (forall x, ntt2' x = to_listl' (Pquotl_convert Hmeq (Pquotl_app (Ring.apply_unop_pair to_pquotl1 to_pquotl1 (ntt2 (of_list' (Hqnz:=Hqnz) x)))))) as Hntt2.
      { intro x. pose proof (Y (of_list' (Hqnz:=Hqnz) x)) as HY.
        rewrite Heql'. destruct x as (x & Hx). cbn -[Nat.div F.inv to_list of_list].
        cbn -[Nat.div F.inv to_list of_list] in HY.
        rewrite app_nil_r. pose proof (to_list_of_list x) as Hl.
        apply HF in Hl. rewrite Hx in Hl. rewrite Hl in HY.
        exact HY. }
      assert (Hmeq': Forall2 Peq [m1; m2] ([m1] ++ [m2])) by reflexivity.
      assert (forall x, intt2' x = (to_list' (intt2 (Ring.apply_unop_pair from_pquotl1 from_pquotl1 (Pquotl_split (Pquotl_convert Hmeq' (of_listl' (Hqlnz:=Hqlnz) x))))))) as Hintt2.
      { intro x. pose proof (X (fst (Ring.apply_unop_pair from_pquotl1 from_pquotl1 (Pquotl_split (Pquotl_convert Hmeq' (of_listl' (Hqlnz:=Hqlnz) x))))) (snd (Ring.apply_unop_pair from_pquotl1 from_pquotl1 (Pquotl_split (Pquotl_convert Hmeq' (of_listl' (Hqlnz:=Hqlnz) x)))))) as HX.
        rewrite Heq'. destruct x as (x & Hx). cbn -[Nat.div F.inv to_list of_list].
        cbn -[Nat.div F.inv to_list of_list] in HX.
        replace (_ ++ _) with x in HX.
        - rewrite HX, map_map. clear -char_ge_3; induction (to_list _ _).
          + reflexivity.
          + cbn -[F.inv]; rewrite IHl0; auto.
            rewrite Hierarchy.associative, Hierarchy.left_multiplicative_inverse.
            * rewrite Hierarchy.left_identity; reflexivity.
            * pose proof (char_ge_3 (BinNums.xO BinNums.xH) ltac:(cbv; reflexivity)) as Hchar.
              simpl in Hchar. rewrite Hierarchy.left_identity in Hchar. exact Hchar.
        - cbn in Hx. pose proof (to_list_of_list (firstn (measure m1 - 1) x)) as Hl.
          pose proof (to_list_of_list (firstn (measure m2 - 1) (skipn (measure m1 - 1) x))) as Hr.
          apply HF in Hl. apply HF in Hr.
          assert (to_list (measure m1 - 1) _ = firstn (measure m1 - 1) x) as ->.
          { etransitivity; [|apply Hl]. f_equal.
            rewrite length_firstn. rewrite Hx, PeanoNat.Nat.min_l by Lia.lia.
            reflexivity. }
          assert (to_list _ _ = skipn (measure m1 - 1) x) as ->.
          { transitivity (firstn (measure m2 - 1) (skipn (measure m1 - 1) x)).
            - etransitivity; [|apply Hr]. f_equal.
              rewrite length_firstn, length_skipn.
              rewrite Hx. repeat (rewrite PeanoNat.Nat.min_l by Lia.lia).
              reflexivity.
            - etransitivity; [|apply firstn_all]. f_equal.
              rewrite length_skipn. rewrite Hx; Lia.lia. }
          rewrite firstn_skipn; reflexivity. }
      eapply (Ring.isomorphism_funext _ _ Hntt2 Hintt2).
      Unshelve.
      eapply (@Ring.compose_isomorphism
                _ _ _ _ _
                _ _ _ _ _
                _ _ _ _ _ _ _ _
                _
                _
                to_listl'
                (fun pl : Pquotl _ =>
                   to_list' (intt2 (Ring.apply_unop_pair from_pquotl1 from_pquotl1 (Pquotl_split (Pquotl_convert Hmeq' pl)))))); [|apply PquotlRingIsomorphism].
      eapply (@Ring.compose_isomorphism
                _ _ _ _ _
                _ _ _ _ _
                _ _ _ _ _ _ _ _
                _
                _
                (Pquotl_convert Hmeq)
                (fun pl : Pquotl _ =>
                   to_list' (intt2 (Ring.apply_unop_pair from_pquotl1 from_pquotl1 (Pquotl_split pl))))); [|apply Pquotl_convert_isomorphism].
      eapply (@Ring.compose_isomorphism
                _ _ _ _ _
                _ _ _ _ _
                _ _ _ _ _ _ _ _
                _
                _
                Pquotl_app
                (fun x : _ =>
                   to_list' (intt2 (Ring.apply_unop_pair from_pquotl1 from_pquotl1 x)))); [|apply PquotlAppRingIsomorphism].
      eapply (@Ring.compose_isomorphism
                _ _ _ _ _
                _ _ _ _ _
                _ _ _ _ _ _ _ _
                _
                _
                (Ring.apply_unop_pair to_pquotl1 to_pquotl1)
                (fun x : _ => to_list' (intt2 x))); [|eapply Ring.product_isomorphism].
      eapply (@Ring.compose_isomorphism
                _ _ _ _ _
                _ _ _ _ _
                _ _ _ _ _ _ _ _
                _
                _
                ntt2
                (fun x : _ => to_list' x)); [|apply ntt_isomorphism2].
      eapply Ring.isomorphism_inv. Unshelve.
      11: apply PquotRingIsomorphism.
      5,6: apply PquotlRingIsomorphism1.
      4,8: apply Ring.product_ring.
    Qed.

    Definition decompose_body': list nat :=
      (rec_decompose r' (Nat.div l 2)) ++ (rec_decompose r' (Nat.pow 2 m + Nat.div l 2)).

    Let decomposition_body' := List.map (fun n => posicyclic (Nat.pow 2 (k - r)) (F.pow zeta (N.of_nat n))) decompose_body'.

    Lemma decomposition_body_eq':
      (rec_decomposition r' (k - 1) (Nat.div l 2)) ++ (rec_decomposition r' (k - 1) (Nat.pow 2 m + Nat.div l 2)) = decomposition_body'.
    Proof.
      unfold decomposition_body', decompose_body', rec_decomposition.
      rewrite map_app. assert (k - r = k - 1 - r')%nat as ->; [|reflexivity].
      unfold r; Lia.lia.
    Qed.

    Lemma decomposition_body_eq'':
      decomposition_body' = (rec_decomposition r' (k - 1) (Nat.div l 2)) ++ (rec_decomposition r' (k - 1) (Nat.pow 2 m + Nat.div l 2)).
    Proof. symmetry; apply decomposition_body_eq'. Qed.

    Lemma decomposition_body_spec':
      Forall2 Peq ((rec_decomposition r' (k - 1) (Nat.div l 2)) ++ (rec_decomposition r' (k - 1) (Nat.pow 2 m + Nat.div l 2))) decomposition_body'.
    Proof.
      rewrite decomposition_body_eq'. reflexivity.
    Qed.

    Lemma decomposition_body_spec'':
      Forall2 Peq decomposition_body' ((rec_decomposition r' (k - 1) (Nat.div l 2)) ++ (rec_decomposition r' (k - 1) (Nat.pow 2 m + Nat.div l 2))).
    Proof. symmetry; apply decomposition_body_spec'. Qed.

    Definition ntt_body' (p: Pquot m0): Pquotl decomposition_body' :=
      Pquotl_convert decomposition_body_spec'
        (Pquotl_app
           (Ring.apply_unop_pair
              (rec_ntt r' (k - 1) (Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_lhs)
              (rec_ntt r' (k - 1) (Nat.pow 2 m + Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_rhs)
              (ntt2 p))).

    Definition intt_body' (pl: Pquotl decomposition_body'): Pquot m0 :=
      intt2 (Ring.apply_unop_pair
               (rec_intt r' (k - 1) (Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_lhs)
               (rec_intt r' (k - 1) (Nat.pow 2 m + Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_rhs)
               (Pquotl_split
                  (Pquotl_convert decomposition_body_spec'' pl))).

    Definition ntt_bodyl' (p: Pquot' m0): Pquotl' decomposition_body' :=
      Pquotl_convert' decomposition_body_eq'
        (Pquotl_app'
           (Ring.apply_unop_pair
              (rec_ntt' r' (k - 1) (Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_lhs)
              (rec_ntt' r' (k - 1) (Nat.pow 2 m + Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_rhs)
              (Ring.apply_unop_pair
                 from_pquotl1'
                 from_pquotl1'
                 (Pquotl_split'
                    (Pquotl_convert' (ql1:=[m1; m2]) (ql2:=[m1]++[m2]) ltac:(reflexivity) (ntt2' p)))))).

    Lemma proj1_sig_ntt_bodyl_eq f (Hf: forall k' l' Hr' Hk' Hl' p, proj1_sig (rec_ntt' r' k' l' Hr' Hk' Hl' p) = f r' k' l' (proj1_sig p)):
      forall p,
        proj1_sig (ntt_bodyl' p) =
          (f r' (k - 1)%nat (Nat.div l 2)
            (firstn (Nat.pow 2 (k - 1))
               (Pmod_cyclotomic_list (Nat.pow 2 (k - 1)) (zeta ^ N.of_nat (Nat.div l 2)) (proj1_sig p)))) ++
            (f r' (k - 1)%nat (Nat.pow 2 m + Nat.div l 2)%nat
               (skipn (Nat.pow 2 (k - 1))
                  (Pmod_cyclotomic_list (Nat.pow 2 (k - 1)) (zeta ^ N.of_nat (Nat.div l 2)) (proj1_sig p)))).
    Proof.
      intro p; cbn -[F.inv Nat.div].
      do 2 rewrite Hf. cbn -[F.inv Nat.div].
      unfold m1. rewrite posicyclic_measure by (pose proof (NatUtil.pow_nonzero 2 (k - 1) ltac:(congruence)); Lia.lia).
      f_equal; f_equal; f_equal; Lia.lia.
    Qed.

    Definition intt_bodyl' (pl: Pquotl' decomposition_body'): Pquot' m0 :=
      intt2'
        (Pquotl_convert' eq_refl
           (Pquotl_app'
              (Ring.apply_unop_pair
                 to_pquotl1'
                 to_pquotl1'
                 (Ring.apply_unop_pair
                    (rec_intt' r' (k - 1) (Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_lhs)
                    (rec_intt' r' (k - 1) (Nat.pow 2 m + Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_rhs)
                    (Pquotl_split'
                       (Pquotl_convert' decomposition_body_eq'' pl)))))).

    Lemma proj1_sig_intt_bodyl_eq f (Hf: forall k' l' Hr' Hk' Hl' p, proj1_sig (rec_intt' r' k' l' Hr' Hk' Hl' p) = f r' k' l' (proj1_sig p)):
      forall p,
        proj1_sig (intt_bodyl' p) =
          map (F.mul (F.inv (1 + 1)))
            (recompose_cyclotomic_list (Nat.pow 2 (k - 1)) (F.inv (zeta ^ N.of_nat (Nat.div l 2)))
               ((f r' (k - 1)%nat (Nat.div l 2) (firstn (Nat.pow 2 (k - 1)) (proj1_sig p))) ++
                (f r' (k - 1)%nat (Nat.pow 2 m + Nat.div l 2)%nat (skipn (Nat.pow 2 (k - 1)) (proj1_sig p))))).
    Proof.
      intro p; cbn -[F.inv Nat.div].
      do 2 rewrite Hf. cbn -[F.inv Nat.div].
      assert (list_sum _ = Nat.pow 2 (k - 1)) as ->; [|reflexivity].
      unfold rec_decomposition. rewrite map_map.
      rewrite (map_ext _ (fun _ => Nat.pow 2 (k - 1 - r'))).
      2: intros; rewrite posicyclic_measure by (pose proof (NatUtil.pow_nonzero 2 (k - 1 - r') ltac:(congruence)); Lia.lia); Lia.lia.
      unfold list_sum.
      assert (forall k l, fold_right Nat.add 0%nat (map (fun _ => k) l) = k * length l)%nat as ->.
      { induction l0; simpl; [|rewrite IHl0]; Lia.lia. }
      rewrite rec_decompose_length, <- PeanoNat.Nat.pow_add_r.
      f_equal; Lia.lia.
    Qed.

    Lemma ntt_isomorphism':
      @Ring.is_isomorphism _ eq1 one add mul _ eql onel addl mull ntt_body' intt_body'.
    Proof.
      pose proof (Hlhs_iso := h_rec_ntt_isomorphism (k - 1) (Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_lhs).
      pose proof (Hrhs_iso := h_rec_ntt_isomorphism (k - 1) (Nat.pow 2 m + Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_rhs).
      pose proof (Hntt2 := ntt_isomorphism2).
      eapply (@Ring.compose_isomorphism
                _ _ _ _ _
                _ _ _ _ _
                _ _ _ _ _ _ _ _
                _
                _
                (Pquotl_convert decomposition_body_spec')
                (fun pl : Pquotl _ =>
                   intt2 (Ring.apply_unop_pair
                            (rec_intt r' (k - 1) (Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_lhs)
                            (rec_intt r' (k - 1) (Nat.pow 2 m + Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_rhs)
                            (Pquotl_split pl)))
                (Pquotl_convert decomposition_body_spec'')); [|apply Pquotl_convert_isomorphism].
      eapply (@Ring.compose_isomorphism
                _ _ _ _ _
                _ _ _ _ _
                _ _ _ _ _ _ _ _
                _
                _
                Pquotl_app
                (fun x =>
                   intt2 (Ring.apply_unop_pair
                            (rec_intt r' (k - 1) (Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_lhs)
                            (rec_intt r' (k - 1) (Nat.pow 2 m + Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_rhs)
                            x))
                Pquotl_split); [|apply PquotlAppRingIsomorphism].
      eapply (@Ring.compose_isomorphism
                _ _ _ _ _
                _ _ _ _ _
                _ _ _ _ _ _ _ _
                _
                ntt2
                _
                intt2
                _); [apply Hntt2|].
      Unshelve. 5: apply Ring.product_ring.
      apply Ring.product_isomorphism.
    Qed.

    Lemma nttl_isomorphism'
      (Hqnz: ~ Peq m0 Pzero)
      (Hqlnz: Forall (fun q => ~ Peq q Pzero) decomposition_body'):
      @Ring.is_isomorphism _ eq' one' add' (mul' (Hqnz:=Hqnz)) _ eql' onel' addl' (mull' (Hqlnz:=Hqlnz)) ntt_bodyl' intt_bodyl'.
    Proof.
      assert (X1: Forall (fun q0 : P => ~ Peq q0 Pzero) (rec_decomposition r' (k - 1) (Nat.div l 2) ++ rec_decomposition r' (k - 1) (Nat.pow 2 m + Nat.div l 2))).
      { rewrite decomposition_body_eq'; assumption. }
      assert (X2: Forall (fun q0 : P => ~ Peq q0 Pzero) (rec_decomposition r' (k - 1) (Nat.div l 2))).
      { apply Forall_app in X1; destruct X1; auto. }
      assert (X3: Forall (fun q0 : P => ~ Peq q0 Pzero) (rec_decomposition r' (k - 1) (Nat.pow 2 m + Nat.div l 2))).
      { apply Forall_app in X1; destruct X1; auto. }
      assert (X4: ~ Peq m1 Pzero).
      { apply posicyclic_nz. pose proof (NatUtil.pow_nonzero 2 (k - 1) ltac:(congruence)); Lia.lia. }
      assert (X5: ~ Peq m2 Pzero).
      { apply posicyclic_nz. pose proof (NatUtil.pow_nonzero 2 (k - 1) ltac:(congruence)); Lia.lia. }
      assert (X6: Forall (fun q => ~ Peq q Pzero) [m1; m2]).
      { repeat constructor; auto. }
      eapply (@Ring.compose_isomorphism
                _ _ _ _ _
                _ _ _ _ _
                _ _ _ _ _ _ _ _
                _
                _
                (Pquotl_convert' decomposition_body_eq')
                (fun x => intt2' (Pquotl_convert' eq_refl (Pquotl_app' (Ring.apply_unop_pair to_pquotl1' to_pquotl1' (Ring.apply_unop_pair (rec_intt' r' (k - 1) (Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_lhs) (rec_intt' r' (k - 1) (Nat.pow 2 m + Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_rhs) (Pquotl_split' x))))))); [|apply Pquotl_convert_isomorphism'].
      eapply (@Ring.compose_isomorphism
                _ _ _ _ _
                _ _ _ _ _
                _ _ _ _ _ _ _ _
                _
                _
                Pquotl_app'
                (fun x => intt2' (Pquotl_convert' eq_refl (Pquotl_app' (Ring.apply_unop_pair to_pquotl1' to_pquotl1' (Ring.apply_unop_pair (rec_intt' r' (k - 1) (Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_lhs) (rec_intt' r' (k - 1) (Nat.pow 2 m + Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_rhs) x)))))); [|apply PquotlAppRingIsomorphism'].
      eapply (@Ring.compose_isomorphism
                _ _ _ _ _
                _ _ _ _ _
                _ _ _ _ _ _ _ _
                _
                _
                (Ring.apply_unop_pair _ _)
                (fun x => intt2' (Pquotl_convert' eq_refl (Pquotl_app' (Ring.apply_unop_pair to_pquotl1' to_pquotl1' x))))); [|apply Ring.product_isomorphism].
      eapply (@Ring.compose_isomorphism
                _ _ _ _ _
                _ _ _ _ _
                _ _ _ _ _ _ _ _
                _
                _
                (Ring.apply_unop_pair from_pquotl1' from_pquotl1')
                (fun x => intt2' (Pquotl_convert' eq_refl (Pquotl_app' x)))); [|eapply Ring.product_isomorphism].
      eapply (@Ring.compose_isomorphism
                _ _ _ _ _
                _ _ _ _ _
                _ _ _ _ _ _ _ _
                _
                _
                Pquotl_split'
                (fun (x: Pquotl' ([m1] ++ [m2])) => intt2' (Pquotl_convert' eq_refl x))); [|eapply Ring.isomorphism_inv].
      eapply (@Ring.compose_isomorphism
                _ _ _ _ _
                _ _ _ _ _
                _ _ _ _ _ _ _ _
                _
                _
                (Pquotl_convert' eq_refl)
                (fun x => intt2' x)); [|apply Pquotl_convert_isomorphism'].
      apply ntt_isomorphism2'.
      Unshelve.
      all: try assumption.
      all: try match goal with
             | |- @Hierarchy.ring (?T1 * ?T2) _ _ _ _ _ _ _ => eapply Ring.product_ring
             end.
      1,2: eapply Ring.isomorphism_inv; apply PquotlRingIsomorphism1'.
      4: apply PquotlRing_by_isomorphism.
      1: apply @PquotlAppRingIsomorphism'.
      Unshelve.
      6,11: apply PquotlRing_by_isomorphism.
      3,4: apply PquotlRingIsomorphism1'.
      1,2: repeat constructor; auto.
    Qed.
  End Inductive_Case.

  Definition decompose_body rec_decompose (r l: nat): list nat :=
    match r with
    | S r' => decompose_body' rec_decompose r' l
    | O => [l]
    end.

  Fixpoint decompose (r l: nat): list nat := decompose_body decompose r l.

  Lemma length_decompose:
    forall r l, length (decompose r l) = Nat.pow 2 r.
  Proof.
    induction r; intros; [reflexivity|].
    cbn. unfold decompose_body'. rewrite length_app.
    rewrite IHr, IHr. Lia.lia.
  Qed.

  Definition decomposition (r k l: nat) :=
    List.map (fun n => posicyclic (Nat.pow 2 (k - r)%nat) (zeta ^ (N.of_nat n))) (decompose r l).

  Program Definition ntt_body rec_ntt (r k l : nat) (Hr_leq_k: (r <= k)%nat) (Hr_leq_m: (r <= m)%nat) (Hr_leq_l: Nat.modulo l (Nat.pow 2 r) = 0%nat): Pquot (posicyclic (Nat.pow 2 k) (zeta ^ N.of_nat l)) -> Pquotl (decomposition r k l) :=
    match r with
    | S r' => ntt_body' decompose rec_ntt r' k l Hr_leq_k Hr_leq_m Hr_leq_l
    | O => fun p => [proj1_sig p]
    end.
  Next Obligation. constructor; [|constructor]. rewrite PeanoNat.Nat.sub_0_r. apply (proj2_sig p). Qed.

  Program Definition ntt_bodyl rec_ntt (r k l : nat) (Hr_leq_k: (r <= k)%nat) (Hr_leq_m: (r <= m)%nat) (Hr_leq_l: Nat.modulo l (Nat.pow 2 r) = 0%nat): Pquot' (posicyclic (Nat.pow 2 k) (zeta ^ N.of_nat l)) -> Pquotl' (decomposition r k l) :=
    match r with
    | S r' => ntt_bodyl' decompose rec_ntt r' k l Hr_leq_k Hr_leq_m Hr_leq_l
    | O => fun p => proj1_sig p
    end.
  Next Obligation.
    rewrite (proj2_sig p). rewrite PeanoNat.Nat.sub_0_r.
    Lia.lia.
  Qed.

  Fixpoint ntt' (r k l: nat) :=
    ntt_body ntt' r k l.

  Fixpoint nttl' (r k l: nat) :=
    ntt_bodyl nttl' r k l.

  Lemma pow_2_mod n:
    Nat.modulo (Nat.pow 2 m) (Nat.pow 2 (Nat.min n m)) = 0%nat.
  Proof.
    replace m with ((m - (Nat.min n m)) + Nat.min n m)%nat at 1 by Lia.lia.
    rewrite PeanoNat.Nat.pow_add_r.
    rewrite <- PeanoNat.Nat.Div0.div_exact.
    rewrite PeanoNat.Nat.div_mul by (apply PeanoNat.Nat.pow_nonzero; congruence).
    apply PeanoNat.Nat.mul_comm.
  Qed.

  Definition ntt (n: nat) p :=
    ntt' (Nat.min n m) n (Nat.pow 2 m) (PeanoNat.Nat.le_min_l _ _) (PeanoNat.Nat.le_min_r _ _) (pow_2_mod _) p.

  Definition nttl (n: nat) p :=
    nttl' (Nat.min n m) n (Nat.pow 2 m) (PeanoNat.Nat.le_min_l _ _) (PeanoNat.Nat.le_min_r _ _) (pow_2_mod _) p.

  Program Definition intt_body rec_intt (r k l : nat) (Hr_leq_k: (r <= k)%nat) (Hr_leq_m: (r <= m)%nat) (Hr_leq_l: Nat.modulo l (Nat.pow 2 r) = 0%nat): Pquotl (decomposition r k l) -> Pquot (posicyclic (Nat.pow 2 k) (zeta ^ N.of_nat l)) :=
    match r with
    | S r' => intt_body' decompose rec_intt r' k l Hr_leq_k Hr_leq_m Hr_leq_l
    | O => fun pl => List.hd Pzero (proj1_sig pl)
    end.
  Next Obligation.
    cbv [decomposition decompose decompose_body map] in pl.
    destruct pl as [pl Hpl]. simpl.
    inversion Hpl; subst; clear Hpl. inversion H4; subst; clear H4.
    simpl. rewrite PeanoNat.Nat.sub_0_r in H3. exact H3.
  Qed.

  Program Definition intt_bodyl rec_intt (r k l : nat) (Hr_leq_k: (r <= k)%nat) (Hr_leq_m: (r <= m)%nat) (Hr_leq_l: Nat.modulo l (Nat.pow 2 r) = 0%nat): Pquotl' (decomposition r k l) -> Pquot' (posicyclic (Nat.pow 2 k) (zeta ^ N.of_nat l)) :=
    match r with
    | S r' => intt_bodyl' decompose rec_intt r' k l Hr_leq_k Hr_leq_m Hr_leq_l
    | O => fun pl => proj1_sig pl
    end.
  Next Obligation.
    destruct pl as [pl Hpl]; simpl; rewrite Hpl.
    cbv [decomposition decompose decompose_body map].
    simpl. rewrite PeanoNat.Nat.sub_0_r. Lia.lia.
  Qed.

  Fixpoint intt' (r k l: nat) :=
    intt_body intt' r k l.

  Fixpoint inttl' (r k l: nat) :=
    intt_bodyl inttl' r k l.

  Definition intt (n: nat) pl :=
    intt' (Nat.min n m) n (Nat.pow 2 m) (PeanoNat.Nat.le_min_l _ _) (PeanoNat.Nat.le_min_r _ _) (pow_2_mod _) pl.

  Definition inttl (n: nat) pl :=
    inttl' (Nat.min n m) n (Nat.pow 2 m) (PeanoNat.Nat.le_min_l _ _) (PeanoNat.Nat.le_min_r _ _) (pow_2_mod _) pl.

  Lemma ntt_rec_isomorphism:
    forall r k l (Hr_leq_k: (r <= k)%nat) (Hr_leq_m: (r <= m)%nat) (Hr_leq_l: Nat.modulo l (Nat.pow 2 r) = 0%nat),
      @Ring.is_isomorphism
        _ eq1 one add mul
        _ eql onel addl mull
        (ntt' r k l Hr_leq_k Hr_leq_m Hr_leq_l)
        (intt' r k l Hr_leq_k Hr_leq_m Hr_leq_l).
  Proof.
    induction r; intros.
    - split; simpl.
      + split; simpl.
        * split; simpl.
          { intros a b; destruct a as (a & Ha); destruct b as (b & Hb).
            unfold eql; simpl. repeat constructor.
            rewrite Pmod_distr, <- Ha, <- Hb. reflexivity. }
          { intros a b; destruct a as (a & Ha); destruct b as (b & Hb).
            unfold eq1, eql; simpl. intros; repeat constructor; auto. }
        * unfold eql; simpl.
          intros a b; destruct a as (a & Ha); destruct b as (b & Hb); simpl.
          rewrite PeanoNat.Nat.sub_0_r. reflexivity.
        * unfold eql; simpl. rewrite PeanoNat.Nat.sub_0_r. reflexivity.
      + intro a; destruct a as (a & Ha); unfold eql; simpl.
        inversion Ha; subst. inversion H3. simpl.
        reflexivity.
      + intros a b; destruct a as (a & Ha); destruct b as (b & Hb).
        unfold eql, eq1; simpl. inversion 1; auto.
    - apply (ntt_isomorphism' _ _ _ _ _ _ _ _ _ IHr).
  Qed.

  Lemma nttl_rec_isomorphism:
    forall r k l (Hr_leq_k: (r <= k)%nat) (Hr_leq_m: (r <= m)%nat) (Hr_leq_l: Nat.modulo l (Nat.pow 2 r) = 0%nat) (Hqnz: ~ Peq (posicyclic (Nat.pow 2 k) (zeta ^ N.of_nat l)) Pzero)
      (Hqlnz: Forall (fun q0 : P => ~ Peq q0 Pzero) (map (fun n : nat => posicyclic (Nat.pow 2 (k - r)) (zeta ^ N.of_nat n)) (decompose r l))),
      @Ring.is_isomorphism
        _ eq' one' add' (mul' (Hqnz:=Hqnz))
        _ eql' onel' addl' (mull' (Hqlnz:=Hqlnz))
        (nttl' r k l Hr_leq_k Hr_leq_m Hr_leq_l)
        (inttl' r k l Hr_leq_k Hr_leq_m Hr_leq_l).
  Proof.
    induction r; intros.
    - repeat constructor.
      + intros (a & Ha) (b & Hb); unfold eql'; simpl. reflexivity.
      + intros (a & Ha) (b & Hb); unfold eq', eql'; simpl. auto.
      + intros (a & Ha) (b & Hb); unfold eql'; simpl.
        rewrite ListUtil.firstn_all by (rewrite Ha, PeanoNat.Nat.sub_0_r; reflexivity).
        rewrite ListUtil.firstn_all by (rewrite Hb, PeanoNat.Nat.sub_0_r; reflexivity).
        rewrite app_nil_r, PeanoNat.Nat.sub_0_r. reflexivity.
      + unfold eql'; simpl. rewrite app_nil_r, PeanoNat.Nat.sub_0_r. reflexivity.
      + intros (a & Ha). unfold eql'; simpl. reflexivity.
      + intros (a & Ha) (b & Hb); unfold eql', eq'; simpl. auto.
    - apply (nttl_isomorphism' _ _ _ _ _ _ _ _ _ IHr).
  Qed.

  Lemma ntt_isomorphism:
    forall n,
      @Ring.is_isomorphism
        (Pquot (posicyclic (Nat.pow 2 n) (zeta ^ N.of_nat (Nat.pow 2 m)))) eq1 one add mul
        (Pquotl (decomposition (Nat.min n m) n (Nat.pow 2 m))) eql onel addl mull
        (ntt n) (intt n).
  Proof. intros; apply ntt_rec_isomorphism. Qed.

  Lemma nttl_isomorphism:
    forall n
      (Hqnz: ~ Peq (posicyclic (Nat.pow 2 n) (zeta ^ N.of_nat (Nat.pow 2 m))) Pzero)
      (Hqlnz: Forall (fun q0 : P => ~ Peq q0 Pzero) (decomposition (Nat.min n m) n (Nat.pow 2 m))),
      @Ring.is_isomorphism
        (Pquot' (posicyclic (Nat.pow 2 n) (zeta ^ N.of_nat (Nat.pow 2 m)))) eq' one' add' (mul' (Hqnz:=Hqnz))
        (Pquotl' (decomposition (Nat.min n m) n (Nat.pow 2 m))) eql' onel' addl' (mull' (Hqlnz:=Hqlnz))
        (nttl n) (inttl n).
  Proof. intros; apply nttl_rec_isomorphism. Qed.
End CyclotomicDecomposition.

Module NTTSanityCheck.
  Section BitRev.
    (*
      In standards, the co-domain of the NTT is sometimes specified using
      bit-reversal order, we show here that the order given by our [decompose]
      is exactly the same (see theorem [decompose_is_bitrev] below).

      For instance, for MLKEM, the codomain is specified as
      (X^2 - \zeta^{2 * bitrev_7(0) + 1}) ... (X^2 - \zeta^{2 * bitrev_7(127) + 1})
    *)

    Fixpoint setbit_f (n: nat) (f: nat -> bool): nat :=
      match n with
      | O => 0%nat
      | S n' => if f n' then PeanoNat.Nat.setbit (setbit_f n' f) n' else (setbit_f n' f)
      end.

    Lemma setbit_f_spec:
      forall n f i,
        Nat.testbit (setbit_f n f) i = if Compare_dec.lt_dec i n then f i else false.
    Proof.
      induction n; intros; cbn.
      - apply PeanoNat.Nat.bits_0.
      - destruct (Compare_dec.lt_dec _ _) as [Hlt|Hnlt].
        + assert (i = n \/ i < n)%nat as [->|Hlt_n] by Lia.lia; [|clear Hlt].
          * destruct (f n); [apply PeanoNat.Nat.setbit_eq|].
            rewrite IHn. destruct (Compare_dec.lt_dec _ _); [Lia.lia|reflexivity].
          * destruct (f n); [rewrite PeanoNat.Nat.setbit_neq by Lia.lia|].
            all: rewrite IHn; destruct (Compare_dec.lt_dec _ _); [reflexivity|Lia.lia].
        + destruct (f n); [rewrite PeanoNat.Nat.setbit_neq by Lia.lia|].
          all: rewrite IHn; destruct (Compare_dec.lt_dec _ _); [Lia.lia|reflexivity].
    Qed.

    Lemma setbit_f_bounds:
      forall n f,
        (setbit_f n f < Nat.pow 2 n)%nat.
    Proof.
      induction n; intros; cbn; [Lia.lia|].
      specialize (IHn f). destruct (f n); [|Lia.lia].
      rewrite NatUtil.setbit_high; Lia.lia.
    Qed.

    (* [n]-bits bit reversal of [x] *)
    Definition bitrev (n: nat) (x: nat): nat :=
      setbit_f n (fun i => Nat.testbit x ((n - 1) - i)%nat).

    Lemma bitrev_0 (x: nat):
      bitrev 0%nat x = 0%nat.
    Proof. reflexivity. Qed.

    Lemma bitrev_spec:
      forall n x i,
        Nat.testbit (bitrev n x) i = if Compare_dec.lt_dec i n then Nat.testbit x (n - 1 - i)%nat else false.
    Proof. intros. unfold bitrev; rewrite setbit_f_spec. reflexivity. Qed.

    Lemma bitrev_bounds:
      forall n x,
        (bitrev n x < Nat.pow 2 n)%nat.
    Proof. intros; apply setbit_f_bounds. Qed.

    Lemma decompose_S_rec_eq:
      forall n r l,
        (S r <= n)%nat ->
        (Nat.modulo l (Nat.pow 2 (S r)) = 0)%nat ->
        @decompose n (S r) l = List.flat_map (fun i => [Nat.div i 2; Nat.pow 2 n + Nat.div i 2]%nat) (@decompose n r l).
    Proof.
      induction r; intros l Hrn Hrl; [reflexivity|].
      cbn [decompose decompose_body]. unfold decompose_body'.
      pose proof (@r_leq_l_lhs n (S r) n l Hrn Hrn Hrl) as Hrl1.
      rewrite IHr by Lia.lia.
      pose proof (@r_leq_l_rhs n (S r) n l Hrn Hrn Hrl) as Hrl2.
      rewrite IHr by Lia.lia.
      rewrite flat_map_app. reflexivity.
    Qed.

    Lemma decompose_S_eq':
      forall n r a,
        (r <= n)%nat ->
        @decompose (S n) r (2 * (a * Nat.pow 2 r)) = List.map (Nat.mul 2) (@decompose n r (a * Nat.pow 2 r)).
    Proof.
      induction r; intros a Hr_leq_n; [reflexivity|].
      cbn [decompose decompose_body]. unfold decompose_body'.
      rewrite (PeanoNat.Nat.mul_comm 2), PeanoNat.Nat.div_mul by congruence.
      rewrite PeanoNat.Nat.pow_succ_r', PeanoNat.Nat.mul_assoc, (PeanoNat.Nat.mul_comm _ 2), <- (PeanoNat.Nat.mul_assoc 2).
      rewrite (IHr a ltac:(Lia.lia)).
      rewrite (PeanoNat.Nat.mul_comm 2), PeanoNat.Nat.div_mul by congruence.
      rewrite map_app. f_equal.
      assert (Nat.pow 2 (S n) + a * _ * 2 = 2 * ((Nat.pow 2 (n - r) + a) * Nat.pow 2 r))%nat as ->.
      { rewrite PeanoNat.Nat.mul_add_distr_r, PeanoNat.Nat.mul_add_distr_l.
        rewrite PeanoNat.Nat.pow_succ_r', <- PeanoNat.Nat.pow_add_r.
        assert (n - r + r = n)%nat as -> by Lia.lia. Lia.lia. }
      rewrite IHr by Lia.lia.
      rewrite PeanoNat.Nat.mul_add_distr_r, <- PeanoNat.Nat.pow_add_r.
      assert (n - r + r = n)%nat as -> by Lia.lia. reflexivity.
    Qed.

    Lemma decompose_S_eq_1:
      forall n,
        @decompose (S n) n (Nat.pow 2 (S n))= List.map (Nat.mul 2) (@decompose n n (Nat.pow 2 n)).
    Proof.
      intros. rewrite <- (PeanoNat.Nat.mul_1_l (Nat.pow 2 n)).
      pose proof (decompose_S_eq' n n 1 ltac:(Lia.lia)) as <-.
      rewrite PeanoNat.Nat.pow_succ_r'; f_equal; Lia.lia.
    Qed.

    Lemma decompose_is_bitrev:
      forall n,
        @decompose n n (Nat.pow 2 n) = List.map (fun i => (2 * bitrev n i + 1)%nat) (seq 0 (Nat.pow 2 n)).
    Proof.
      induction n; [reflexivity|].
      rewrite (decompose_S_rec_eq (S n) n (Nat.pow 2 (S n)) ltac:(Lia.lia)) by (apply PeanoNat.Nat.Div0.mod_same).
      rewrite decompose_S_eq_1, IHn, ListUtil.flat_map_map.
      rewrite (flat_map_ext _ (fun x => [x; Nat.pow 2 (S n) + x]%nat)).
      2:{ intros. rewrite (PeanoNat.Nat.mul_comm 2), PeanoNat.Nat.div_mul by congruence.
          reflexivity. }
      rewrite ListUtil.flat_map_map.
      apply nth_error_ext. intros i.
      rewrite nth_error_map, ListUtil.nth_error_seq, PeanoNat.Nat.add_0_l.
      match goal with
      | |- context [flat_map ?f ?l] => assert (length (flat_map f l) = Nat.pow 2 (S n)) as Hlen
      end.
      { rewrite (length_flat_map _ 2) by reflexivity.
        rewrite length_seq, <- PeanoNat.Nat.pow_succ_r'. Lia.lia. }
      destruct (Compare_dec.lt_dec _ _) as [Hlt|Hnlt].
      2: rewrite ListUtil.nth_error_length_error by Lia.lia; reflexivity.
      set (L := flat_map _ _).
      assert (i < length L)%nat as HL by (unfold L; Lia.lia).
      destruct (ListUtil.nth_error_length_exists_value i L HL) as (x & Hx).
      rewrite Hx. cbn [option_map].
      subst L. apply (ListUtil.flat_map_constant_nth_error 2%nat) in Hx; [|reflexivity].
      destruct Hx as (y & Hy & Hx).
      rewrite ListUtil.nth_error_seq in Hy.
      destruct (Compare_dec.lt_dec _ _) as [_|]; [|congruence].
      Local Opaque Nat.div.
      rewrite PeanoNat.Nat.add_0_l in Hy; inversion Hy; subst y; clear Hy.
      f_equal. pose proof (NatUtil.mod_bound_lt i 2 ltac:(Lia.lia)) as Hmodlt.
      assert (Nat.modulo i 2 = 0 \/ Nat.modulo i 2 = 1)%nat as Hmodeq by Lia.lia.
      Local Opaque Nat.mul.
      destruct Hmodeq as [Hmodeq|Hmodeq]; rewrite Hmodeq in Hx; cbn in Hx; inversion Hx; subst x; clear Hx.
      - f_equal. f_equal.
        apply PeanoNat.Nat.bits_inj. intro k.
        do 2 rewrite bitrev_spec.
        rewrite PeanoNat.Nat.div2_bits.
        destruct (Compare_dec.lt_dec _ _); destruct (Compare_dec.lt_dec _ _); try Lia.lia.
        + f_equal; Lia.lia.
        + assert (S n - 1 - k = 0)%nat as -> by Lia.lia.
          apply PeanoNat.Nat.Lcm0.mod_divide in Hmodeq.
          destruct Hmodeq; subst i. rewrite PeanoNat.Nat.mul_comm.
          rewrite PeanoNat.Nat.testbit_even_0; reflexivity.
      - rewrite PeanoNat.Nat.add_assoc, <- PeanoNat.Nat.mul_add_distr_l.
        f_equal. f_equal.
        transitivity (bitrev (S n) (2 * Nat.div i 2 + Nat.modulo i 2)); [|rewrite <- PeanoNat.Nat.div_mod_eq; reflexivity].
        rewrite Hmodeq. apply PeanoNat.Nat.bits_inj. intro k.
        rewrite bitrev_spec. destruct (Compare_dec.lt_dec _ _).
        + assert (k = n \/ k < n)%nat as [->|?] by Lia.lia.
          * assert (S n - 1 - n = 0)%nat as -> by Lia.lia.
            rewrite PeanoNat.Nat.testbit_odd_0.
            etransitivity; [|eapply PeanoNat.Nat.bit_log2].
            1: f_equal.
            2: pose proof (PeanoNat.Nat.pow_nonzero 2 n ltac:(congruence)); Lia.lia.
            symmetry; apply PeanoNat.Nat.log2_unique; [Lia.lia|].
            rewrite PeanoNat.Nat.pow_succ_r'.
            pose proof (bitrev_bounds n (Nat.div i 2)). Lia.lia.
          * rewrite PeanoNat.Nat.add_nocarry_lxor.
            2:{ apply PeanoNat.Nat.bits_inj. intro m.
                rewrite PeanoNat.Nat.bits_0.
                rewrite PeanoNat.Nat.land_spec, bitrev_spec.
                rewrite PeanoNat.Nat.pow2_bits_eqb.
                pose proof (PeanoNat.Nat.eqb_spec n m) as Heqb; destruct Heqb; [subst m|].
                - destruct (Compare_dec.lt_dec _ _); [Lia.lia|]; reflexivity.
                - reflexivity. }
            rewrite PeanoNat.Nat.lxor_spec.
            rewrite PeanoNat.Nat.pow2_bits_false by Lia.lia.
            rewrite Bool.xorb_false_l, bitrev_spec.
            destruct (Compare_dec.lt_dec _ _) as [_|]; [|Lia.lia].
            assert (S n - 1 - k = S (n - 1 - k))%nat as -> by Lia.lia.
            rewrite PeanoNat.Nat.testbit_odd_succ'. reflexivity.
        + apply PeanoNat.Nat.bits_above_log2.
          assert (Nat.log2 _ = n)%nat as ->; [|Lia.lia].
          apply PeanoNat.Nat.log2_unique; [Lia.lia|].
          rewrite PeanoNat.Nat.pow_succ_r'.
          pose proof (bitrev_bounds n (Nat.div i 2)). Lia.lia.
    Qed.

    Local Notation bitrev8 := (bitrev 8%nat). (* Dilithium *)
    Local Notation bitrev7 := (bitrev 7%nat). (* Kyber *)

    (* Making sure the decomposition returns the same order expected by ML-DSA
     aka Dilithium *)
    (* See Section 7.5 of https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf *)
    Local Lemma dilithium_ok:
      (@decompose 8%nat 8%nat (Nat.pow 2 8)) = List.map (fun k => (2 * (bitrev8 k) + 1)%nat) (seq 0 256%nat).
    Proof. exact (decompose_is_bitrev 8%nat). Qed.

    (* Making sure the decomposition returns the same order expected by ML-KEM
     aka Kyber *)
    (* See Section 4.3 of https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.203.pdf *)
    Local Lemma kyber_ok:
      (@decompose 7%nat 7%nat (Nat.pow 2 7)) = List.map (fun k => (2 * (bitrev7 k) + 1)%nat) (seq 0 128%nat).
    Proof. exact (decompose_is_bitrev 7%nat). Qed.
  End BitRev.

  Section Mod.
    (* We show here that our NTT is equivalent to the simpler specification
          NTT(p) = (p mod P0(X), ..., p mod Pn(X))
       where P0(X), ..., Pn(X) are given by [decomposition].
    *)

    Local Coercion N.of_nat: nat >-> N.
    Context {q: positive} {prime_q: prime q}.
    Local Notation F := (F q). (* This is to have F.pow available, there is no Fpow defined for a general field *)
    Local Open Scope F_scope.
    Context {field: @Hierarchy.field F eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div}
      {char_ge_3: @Ring.char_ge F eq F.zero F.one F.opp F.add F.sub F.mul (BinNat.N.succ_pos (BinNat.N.two))}.
    Context {P}{poly_ops: @Polynomial.polynomial_ops F P}.
    Context {poly_defs: @Polynomial.polynomial_defs F eq F.zero F.one F.opp F.add F.sub F.mul P _}.
    Context {zeta: F} {m: nat} {Hm: zeta ^ (N.pow 2 m) = F.opp 1}.

    (* Too many instances *)
    Remove Hints F.commutative_ring_modulo: typeclass_instances.

    Local Notation Peq := (@Polynomial.Peq F eq P _).
    Local Notation Pmod := (@Polynomial.Pmod F F.zero P _ F.div).
    Local Notation Pmul := (@Polynomial.Pmul _ _ poly_ops).
    Local Notation posicyclic := (@PolynomialCRT.posicyclic F F.opp P _).
    Local Notation decompose := (@decompose m).
    Local Notation decomposition := (@decomposition q P poly_ops zeta m).
    Local Notation ntt' := (@ntt' q field P poly_ops poly_defs zeta m Hm).

    Lemma decomposition_is_decomposition:
      forall r k l,
        (r <= k)%nat ->
        (r <= m)%nat ->
        (Nat.modulo l (Nat.pow 2 r) = 0)%nat ->
        Peq (List.fold_right Pmul Pone (decomposition r k l)) (posicyclic (Nat.pow 2 k) (F.pow zeta l)).
    Proof.
      assert (forall l1 l2, Peq (List.fold_right Pmul Pone (l1 ++ l2)) (Pmul (List.fold_right Pmul Pone l1) (List.fold_right Pmul Pone l2))) as Hassoc.
      { induction l1; intros; cbn.
        - symmetry; apply Hierarchy.left_identity.
        - rewrite IHl1. apply Hierarchy.associative. }
      induction r; intros k l r_leq_k r_leq_m r_leq_l.
      - cbn. rewrite PeanoNat.Nat.sub_0_r.
        apply Hierarchy.right_identity.
      - unfold decomposition.
        cbn [decompose decompose_body]. unfold decompose_body'.
        rewrite map_app, Hassoc.
        unfold decomposition in IHr.
        assert (k - S r = (k - 1) - r)%nat as -> by Lia.lia.
        pose proof (@r_leq_l_lhs m r k l r_leq_k r_leq_m r_leq_l) as r_leq_l_lhs.
        pose proof (@r_leq_l_rhs m r k l r_leq_k r_leq_m r_leq_l) as r_leq_l_rhs.
        rewrite (IHr (k - 1)%nat _ ltac:(Lia.lia) ltac:(Lia.lia) r_leq_l_lhs).
        rewrite (IHr (k - 1)%nat _ ltac:(Lia.lia) ltac:(Lia.lia) r_leq_l_rhs).
        rewrite Nnat.Nat2N.inj_add, Nnat.Nat2N.inj_pow.
        rewrite <- (neg_zeta_power_eq (Hm:=Hm)).
        rewrite posicyclic_opp, <- posicyclic_decomposition.
        rewrite <- F.pow_add_r, <- PeanoNat.Nat.pow_succ_r', <- Nnat.Nat2N.inj_add.
        assert (S (k - 1) = k)%nat as -> by Lia.lia.
        apply PeanoNat.Nat.Lcm0.mod_divide in r_leq_l.
        destruct r_leq_l as (x & Hx).
        rewrite PeanoNat.Nat.pow_succ_r' in Hx.
        assert (Nat.div l 2 + Nat.div l 2 = l)%nat as ->.
        { rewrite Hx, (PeanoNat.Nat.mul_comm 2), PeanoNat.Nat.mul_assoc.
          rewrite PeanoNat.Nat.div_mul by congruence. Lia.lia. }
        reflexivity.
    Qed.

    Lemma decomposition_divides:
      forall r k l,
        (r <= k)%nat ->
        (r <= m)%nat ->
        (Nat.modulo l (Nat.pow 2 r) = 0)%nat ->
        forall p, In p (decomposition r k l) ->
             exists q, Peq (posicyclic (Nat.pow 2 k) (F.pow zeta l)) (Pmul p q).
    Proof.
      assert (forall l (p: P), In p l -> exists q, Peq (List.fold_right Pmul Pone l) (Pmul p q)).
      { induction l; intros p Hp; [inversion Hp|].
        apply in_inv in Hp. destruct Hp as [->|Hp].
        - cbn. eexists; reflexivity.
        - cbn. apply IHl in Hp. destruct Hp as (p' & Hp').
          exists (Pmul a p'). rewrite Hp'.
          rewrite Hierarchy.associative, (Hierarchy.commutative a).
          rewrite <- Hierarchy.associative. reflexivity. }
      intros r k l HA HB HC p Hp.
      apply H in Hp. destruct Hp as (p' & Hp').
      rewrite decomposition_is_decomposition in Hp'; auto.
      exists p'. assumption.
    Qed.

    Lemma ntt_is_modulo:
      forall r k l (r_leq_k: (r <= k)%nat) (r_leq_m: (r <= m)%nat)
        (r_leq_l: Nat.modulo l (Nat.pow 2 r) = 0%nat) p,
        List.Forall2 Peq (proj1_sig (ntt' r k l r_leq_k r_leq_m r_leq_l p)) (List.map (Pmod (proj1_sig p)) (decomposition r k l)).
    Proof.
      induction r; intros.
      - cbn. rewrite PeanoNat.Nat.sub_0_r.
        repeat constructor. apply (proj2_sig p).
      - unfold decomposition. cbn [decompose decompose_body].
        unfold decompose_body'. rewrite map_map.
        rewrite map_app. cbn [ntt' ntt_body].
        unfold ntt_body'. unfold Pquotl_convert. cbn [proj1_sig].
        unfold Pquotl_app. cbn [proj1_sig].
        destruct (ntt2 k l p) as (p1 & p2) eqn:Hntt2.
        unfold Ring.apply_unop_pair. cbn [fst snd].
        assert (k - S r = k - 1 - r)%nat as -> by Lia.lia.
        unfold ntt2, phi2, of_P, to_P in Hntt2.
        Local Opaque Nat.div.
          apply Forall2_app.
        + match goal with
          | |- context [ntt' r ?k ?l ?r_leq_k ?r_leq_m ?r_leq_l ?p] =>
              pose proof (IHr k l r_leq_k r_leq_m r_leq_l p) as ->
          end.
          unfold decomposition. rewrite map_map.
          apply Forall.Forall2_map_map_iff.
          inversion Hntt2; subst p1; clear Hntt2.
          cbn [proj1_sig]. apply (Forall2_impl_strong eq); [|reflexivity].
          intros x y <- Hx _. apply (in_map (fun n => posicyclic (Nat.pow 2 (k - 1 - r)%nat) (F.pow zeta (N.of_nat n)))) in Hx.
          pose proof (@r_leq_l_lhs m r k l r_leq_k r_leq_m r_leq_l) as r_leq_l'.
          apply decomposition_divides in Hx; try Lia.lia.
          destruct Hx as (p' & Hpp).
          rewrite (@peq_mod_proper _ _ _ _ _ _ _ _ _ P poly_ops poly_defs F.inv F.div field (proj1_sig p) (proj1_sig p) ltac:(reflexivity) _ _ Hpp).
          apply Pmod_mul_mod_l.
        + match goal with
          | |- context [ntt' r ?k ?l ?r_leq_k ?r_leq_m ?r_leq_l ?p] =>
              pose proof (IHr k l r_leq_k r_leq_m r_leq_l p) as ->
          end.
          unfold decomposition. rewrite map_map.
          apply Forall.Forall2_map_map_iff.
          inversion Hntt2; subst p2; clear Hntt2.
          cbn [proj1_sig]. apply (Forall2_impl_strong eq); [|reflexivity].
          intros x y <- Hx _. apply (in_map (fun n => posicyclic (Nat.pow 2 (k - 1 - r)%nat) (F.pow zeta (N.of_nat n)))) in Hx.
          pose proof (@r_leq_l_rhs m r k l r_leq_k r_leq_m r_leq_l) as r_leq_l'.
          apply decomposition_divides in Hx; try Lia.lia.
          destruct Hx as (p' & Hpp).
          rewrite (@peq_mod_proper _ _ _ _ _ _ _ _ _ P poly_ops poly_defs F.inv F.div field (proj1_sig p) (proj1_sig p) ltac:(reflexivity) _ _ Hpp).
          apply Pmod_mul_mod_l.
    Qed.
  End Mod.
End NTTSanityCheck.
