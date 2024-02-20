Require Import Coq.Classes.Morphisms.

Require Import Crypto.Spec.WeierstrassCurve Crypto.Algebra.ScalarMult.
Require Import Crypto.Curves.Weierstrass.Jacobian.Jacobian.
Require Import Crypto.Curves.Weierstrass.Affine Crypto.Curves.Weierstrass.AffineProofs.
Require Import Crypto.Curves.Weierstrass.Jacobian.CoZ.
Require Import Crypto.Util.Decidable Crypto.Algebra.Field.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SetoidSubst.
Require Import Crypto.Util.Notations Crypto.Util.LetIn.
Require Import Crypto.Util.Sum Crypto.Util.Prod Crypto.Util.Sigma.
Require Import Crypto.Util.FsatzAutoLemmas.
Require Import Crypto.Util.Loops.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Shift.
Require Import Crypto.Util.ZUtil.Peano.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Module ScalarMult.
  Section JoyeLadder.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {a b:F}
            {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {char_ge_3:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two))}
            {Feq_dec:DecidableRel Feq}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := Fzero. Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "-" := Fsub.
    Local Infix "*" := Fmul. Local Infix "/" := Fdiv.
    Local Notation "x ^ 2" := (x*x). Local Notation "x ^ 3" := (x^2*x).
    Local Notation "2" := (1+1). Local Notation "4" := (2+1+1).
    Local Notation "8" := (4+4). Local Notation "27" := (4*4 + 4+4 +1+1+1).
    Local Notation "'∞'" := (@W.zero F Feq Fadd Fmul a b).
    Local Notation Wpoint := (@W.point F Feq Fadd Fmul a b).
    Context {char_ge_12:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 12%positive}
            {discriminant_nonzero:id(4*a*a*a + 27*b*b <> 0)}.
    Local Notation Wopp := (@W.opp F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation Wadd := (@W.add F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv field Feq_dec char_ge_3 a b).
    Local Notation Wzero := (@W.zero F Feq Fadd Fmul a b).
    Local Notation Weq := (@W.eq F Feq Fadd Fmul a b).
    Local Notation Wgroup := (@W.commutative_group F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec char_ge_3 char_ge_12 discriminant_nonzero).
    Local Notation point := (@Jacobian.point F Feq Fzero Fadd Fmul a b Feq_dec).
    Local Notation eq := (@Jacobian.eq F Feq Fzero Fadd Fmul a b Feq_dec).
    Local Notation x_of := (@Jacobian.x_of F Feq Fzero Fadd Fmul a b Feq_dec).
    Local Notation y_of := (@Jacobian.y_of F Feq Fzero Fadd Fmul a b Feq_dec).
    Local Notation z_of := (@Jacobian.z_of F Feq Fzero Fadd Fmul a b Feq_dec).
    Local Notation add := (@Jacobian.add F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field char_ge_3 Feq_dec).
    Local Notation opp := (@Jacobian.opp F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation co_z := (@Jacobian.co_z F Feq Fzero Fadd Fmul a b Feq_dec).
    Local Notation make_co_z_inner := (@Jacobian.make_co_z_inner F Fmul).
    Local Notation make_co_z := (@Jacobian.make_co_z F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation of_affine := (@Jacobian.of_affine F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation to_affine := (@Jacobian.to_affine F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation zero := (of_affine Wzero).
    Local Notation dblu := (@Jacobian.dblu F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation tplu_inner := (@Jacobian.tplu_inner F Fone Fadd Fsub Fmul a).
    Local Notation tplu := (@Jacobian.tplu F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation zaddu_inner := (@Jacobian.zaddu_inner F Fsub Fmul).
    Local Notation zaddu := (@Jacobian.zaddu F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation zdau_inner := (@Jacobian.zdau_inner F Fadd Fsub Fmul).
    Local Notation zdau := (@Jacobian.zdau F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation is_point := (@Jacobian.is_point F Feq Fzero Fadd Fmul a b Feq_dec).

    Ltac prept_step_opt :=
      match goal with
      | [ H : ?T |- ?T ] => exact H
      | [ |- ?x = ?x ] => reflexivity
      | [ H : ?T, H' : ~?T |- _ ] => solve [ exfalso; apply H', H ]
      end.

    Ltac prept_step :=
      match goal with
      | _ => progress prept_step_opt
      | _ => progress intros
      (*| _ => progress specialize_by_assumption*)
      (*| _ => progress specialize_by trivial*)
      | _ => progress cbv [proj1_sig fst snd] in *
      | _ => progress autounfold with points_as_coordinates in *
      | _ => progress destruct_head'_True
      | _ => progress destruct_head'_unit
      | _ => progress destruct_head'_prod
      | _ => progress destruct_head'_sig
      | _ => progress destruct_head'_and
      | _ => progress destruct_head'_sum
      | _ => progress destruct_head'_bool
      | _ => progress destruct_head'_or
      | H: context[@dec ?P ?pf] |- _ => destruct (@dec P pf)
      | |- context[@dec ?P ?pf]      => destruct (@dec P pf)
      | |- ?P => lazymatch type of P with Prop => split end
      end.
    Ltac prept := repeat prept_step.
    Ltac t := prept; trivial; try contradiction; fsatz.

    Create HintDb points_as_coordinates discriminated.
    Hint Unfold Proper respectful Reflexive Symmetric Transitive : points_as_coordinates.
    Hint Unfold Jacobian.point Jacobian.eq W.eq W.point W.coordinates proj1_sig fst snd : points_as_coordinates.

    Hint Unfold Jacobian.x_of Jacobian.y_of Jacobian.z_of Jacobian.opp Jacobian.co_z : points_as_coordinates.

    Lemma tplu_inner_is_point (P : F*F*F) (HPaff : let '(X, Y, Z) := P in Z = 1)
      (HP : is_point P) :
      is_point (fst (tplu_inner P)) /\ is_point (snd (tplu_inner P)) /\ (snd (fst (tplu_inner P)) = snd (snd (tplu_inner P))).
    Proof.
      destruct (@Jacobian.tplu F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec (exist _ P HP) (ltac:(t))) as (Q & S) eqn:HQS.
      unfold Jacobian.tplu in HQS. inversion HQS; clear HQS.
      destruct Q as [Q HQ]. inversion H0; clear H0.
      destruct S as [S HS]. inversion H1; clear H1.
      rewrite H2, H0. repeat split; auto.
      rewrite <- H2, <- H0. unfold tplu_inner; simpl; t.
    Qed.

    Lemma zdau_inner_is_point (P Q : F*F*F) (HP : is_point P) (HQ : is_point Q)
      (H : snd P = snd Q) :
      is_point (fst (zdau_inner P Q)) /\ is_point (snd (zdau_inner P Q)) /\ (snd (fst (zdau_inner P Q)) = snd (snd (zdau_inner P Q))).
    Proof.
      destruct (@Jacobian.zdau F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec (exist _ P HP) (exist _ Q HQ) ltac:(t)) as (R0 & R1) eqn:HRR.
      unfold Jacobian.zdau in HRR. inversion HRR; clear HRR.
      destruct R0 as [R0 HR0]. inversion H1; clear H1.
      destruct R1 as [R1 HR1]. inversion H2; clear H2.
      rewrite H1, H3. repeat split; auto.
      rewrite <- H1, <- H3. unfold zdau_inner; simpl. t.
    Qed.

    Lemma make_co_z_inner_is_co_z (P Q : F*F*F) (HP: is_point P) (HQ : is_point Q)
      (H : snd Q = 1) :
      is_point (fst (make_co_z_inner P Q)) /\ is_point (snd (make_co_z_inner P Q)) /\ snd (fst (make_co_z_inner P Q)) = snd (snd (make_co_z_inner P Q)).
    Proof.
      destruct (@Jacobian.make_co_z F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec (exist _ P HP) (exist _ Q HQ) ltac:(t)) as (R0 & R1) eqn:Heq.
      unfold make_co_z in Heq. inversion Heq; clear Heq.
      destruct R0 as [R0 HR0]. inversion H1; clear H1.
      destruct R1 as [R1 HR1]. inversion H2; clear H2.
      rewrite H1, H3. repeat split; auto.
      destruct R0 as ((? & ?) & ?); destruct R1 as ((? & ?) & ?); auto.
      destruct P as ((? & ?) & ?); destruct Q as ((? & ?) & ?); auto.
      simpl in H1, H3; simpl; inversion H1; inversion H3.
      rewrite <- H8. rewrite H5. reflexivity.
    Qed.

    Lemma zaddu_inner_is_point (P Q : F*F*F) (HP : is_point P) (HQ : is_point Q)
      (H : snd P = snd Q) :
      is_point (fst (zaddu_inner P Q)) /\ is_point (snd (zaddu_inner P Q)) /\ snd (fst (zaddu_inner P Q)) = snd (snd (zaddu_inner P Q)).
    Proof.
      destruct (@Jacobian.zaddu F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec (exist _ P HP) (exist _ Q HQ) ltac:(t)) as (R0 & R1) eqn:HRR.
      unfold Jacobian.zaddu in HRR. inversion HRR; clear HRR.
      destruct R0 as [R0 HR0]. inversion H1; clear H1.
      destruct R1 as [R1 HR1]. inversion H2; clear H2.
      rewrite H1, H3. repeat split; auto.
      rewrite <- H1, <- H3. unfold zaddu_inner; simpl. t.
    Qed.

    Local Notation cswap := (fun (b : bool) '(P, Q) => if b then (Q, P) else (P, Q)).

    Definition opp_inner (P : F*F*F) : F*F*F :=
      match P with
      | (X, Y, Z) => (X, Fopp Y, Z)
      end.

    (* Scalar Multiplication on Weierstraß Elliptic Curves from Co-Z Arithmetic *)
    (* Goundar, Joye, Miyaji, Rivain, Vanelli *)
    (* Algorithm 14 Joye’s double-add algorithm with Co-Z addition formulæ *)
    (* Adapted *)
    Definition joye_ladder_inner (scalarbitsz : Z) (testbit : Z -> bool) (P : F*F*F) : F*F*F :=
      (* Assume lsb (aka testbit 0) is 1 *)
      let b := testbit 1%Z in
      (* if b = 0 then (R1, R0) = (3P, P) = (11b * P, 01b * P) *)
      (* if b = 1 then (R1, R0) = (P, 3P) = (01b * P, 11b * P) *)
      let '(R1, R0) := cswap b (tplu_inner P) in
      let '((R1, R0), _) :=
        (@while (((F*F*F)*(F*F*F))*Z) (fun '(_, i) => (Z.ltb i scalarbitsz))
                (fun '((R1, R0), i) =>
                   let b := testbit i in
                   let '(R1, R0) := cswap b (R1, R0) in
                   let '(R1, R0) := cswap b (zdau_inner R1 R0) in
                   let i := Z.succ i in
                   ((R1, R0), i))
                (Z.to_nat scalarbitsz)
                ((R1, R0), 2%Z)) in
      (* R0 is now (k | 1) P *)
      (* Substract P from R0 if lsb was actually 0 *)
      let b := testbit 0%Z in
      let mP := opp_inner P in
      (* Make sure R0 and -P are co-z *)
      let '(R0, R1) := make_co_z_inner R0 mP in
      (* if b = 0 then R0 = R0 - P and R1 = R0 *)
      (* if b = 1 then R0 = R0 and R1 = R0 - P *)
      let '(R0, R1) := cswap b (zaddu_inner R0 R1) in
      R0.

    Lemma joye_ladder_inner_is_point (scalarbitsz : Z) (testbit : Z -> bool) (P : F*F*F)
      (HP : is_point P) (HPaff : let '(X, Y, Z) := P in Z = 1) :
      is_point (joye_ladder_inner scalarbitsz testbit P).
    Proof.
      destruct P as ((X & Y) & Z).
      unfold joye_ladder_inner.
      destruct (tplu_inner_is_point (X, Y, Z) ltac:(auto) HP) as (A & B & C).
      rewrite (surjective_pairing (tplu_inner _)).
      replace (if testbit 1%Z then (snd (tplu_inner (X, Y, Z)), fst (tplu_inner (X, Y, Z))) else (fst (tplu_inner (X, Y, Z)), snd (tplu_inner (X, Y, Z)))) with ((if testbit 1%Z then snd (tplu_inner (X, Y, Z)) else fst (tplu_inner (X, Y, Z)), if testbit 1%Z then fst (tplu_inner (X, Y, Z)) else snd (tplu_inner (X, Y, Z)))) by (destruct (testbit 1%Z); reflexivity).
      pose (CD := (while (fun '(_, i) => (i <? scalarbitsz)%Z)
        (fun '(R1, R0, i) =>
         let
         '(R2, R3) := if testbit i then (R0, R1) else (R1, R0) in
          let
          '(R4, R5) :=
           let '(P, Q) := zdau_inner R2 R3 in if testbit i then (Q, P) else (P, Q) in
           (R4, R5, Z.succ i)) (Z.to_nat scalarbitsz)
        (if testbit 1%Z then snd (tplu_inner (X, Y, Z)) else fst (tplu_inner (X, Y, Z)),
          if testbit 1%Z then fst (tplu_inner (X, Y, Z)) else snd (tplu_inner (X, Y, Z)), 2%Z))).
      pose (inv := fun '(R1, R0, i) => is_point R1 /\ is_point R0 /\ (i >= 0)%Z /\ snd R1 = snd R0).
      assert (HCD: inv CD).
      { unfold CD. set (measure := fun (state : ((F*F*F)*(F*F*F)*BinNums.Z)) => ((Z.to_nat scalarbitsz) + 2 - (Z.to_nat (snd state)))%nat).
        replace (Z.to_nat scalarbitsz) with (measure ((if testbit 1%Z then snd (tplu_inner (X, Y, Z)) else fst (tplu_inner (X, Y, Z)), if testbit 1%Z then fst (tplu_inner (X, Y, Z)) else snd (tplu_inner (X, Y, Z)), 2%Z))) by (unfold measure; simpl; lia).
        eapply (while.by_invariant inv measure inv).
        - destruct (testbit 1%Z); unfold inv; repeat split; auto; lia.
        - intros. destruct s as ((R1 & R0) & i).
          destruct (Z.ltb i scalarbitsz) eqn:Hi; [|assumption].
          destruct H as (A1 & B1 & D1 & C1).
          split; replace (if testbit i then (R0, R1) else (R1, R0)) with (if testbit i then R0 else R1, if testbit i then R1 else R0) by (destruct (testbit i); reflexivity); rewrite (surjective_pairing (zdau_inner _ _)); [|destruct (testbit i); unfold measure; simpl; lia].
          destruct (zdau_inner_is_point R0 R1 B1 A1 ltac:(symmetry; apply C1)) as (A2 & B2 & C2).
          destruct (zdau_inner_is_point R1 R0 A1 B1 ltac:(apply C1)) as (A3 & B3 & C3).
          destruct (testbit i); unfold inv; simpl; repeat split; auto; try lia.
          symmetry; exact C2. }
      fold CD. destruct CD as ((R1 & R0) & i).
      assert (HmP : is_point (opp_inner (X, Y, Z))) by (unfold is_point, opp_inner in *; t).
      rewrite (surjective_pairing (make_co_z_inner _ _)).
      rewrite (surjective_pairing (zaddu_inner _ _)).
      destruct HCD as (HR1 & HR0 & _ & HRZ).
      destruct (make_co_z_inner_is_co_z R0 (X, Fopp Y, Z) HR0 HmP HPaff) as (X1 & X2 & Xeq).
      destruct (zaddu_inner_is_point _ _ X1 X2 Xeq) as (Y1 & Y2 & Yeq).
      destruct (testbit 0%Z); assumption.
    Qed.

    Program Definition joye_ladder (scalarbitsz : Z) (testbit : Z -> bool) (P : Wpoint)
      (HPnz : P <> ∞ :> Wpoint) : Wpoint :=
      to_affine (joye_ladder_inner scalarbitsz testbit (proj1_sig (of_affine P))).
    Next Obligation. Proof.
      destruct P as [P HP]. destruct P as [ [X Y] | ?]; [|t].
      simpl. eapply joye_ladder_inner_is_point; unfold is_point; [|fsatz].
      destruct (dec (1 = 0)); [exfalso; fsatz|rewrite HP; fsatz].
    Qed.

    Section Proof.

      Local Notation scalarmult := (@scalarmult_ref Wpoint Wadd Wzero Wopp).
      Local Notation scalarmult':= (@scalarmult_ref point add zero opp).

      Local Instance Equivalence_Weq : Equivalence Weq.
      Proof. apply Wgroup.(Hierarchy.commutative_group_group).(Hierarchy.group_monoid).(Hierarchy.monoid_Equivalence). Qed.

      Lemma Pgroup :
        @Hierarchy.group point eq add zero opp.
      Proof.
        destruct (@Group.group_by_isomorphism _ _ _ _ _ point eq add zero opp of_affine to_affine Wgroup.(Hierarchy.commutative_group_group) ltac:(apply Jacobian.to_affine_of_affine)); auto.
        - intros; split; intros.
          + rewrite <- (Jacobian.of_affine_to_affine a0), <- (Jacobian.of_affine_to_affine b0).
            rewrite H. reflexivity.
          + apply Jacobian.Proper_to_affine; auto.
        - apply Jacobian.to_affine_add.
        - intros. destruct a0 as (((X & Y) & Z) & HP).
          unfold to_affine, Wopp, opp, Weq. simpl.
          t.
        - rewrite Jacobian.to_affine_of_affine. reflexivity.
      Qed.

      Lemma scalarmult_scalarmult' (n : Z) (P : Wpoint) (Hn : (n >= 0)%Z) :
        eq (of_affine (scalarmult n P)) (scalarmult' n (of_affine P)).
      Proof.
        eapply natlike_ind with (x:=n); [reflexivity| |lia].
        intros x Hposx Hx.
        rewrite (@scalarmult_ref_is_scalarmult Wpoint Weq Wadd Wzero Wopp Wgroup.(Hierarchy.commutative_group_group)).(scalarmult_succ_l_nn); auto.
        rewrite Jacobian.of_affine_add, Hx.
        rewrite (@scalarmult_ref_is_scalarmult point eq add zero opp Pgroup).(scalarmult_succ_l_nn); auto.
        reflexivity.
      Qed.

      Section Auxiliary.

        Variables n scalarbitsz : Z.
        Hypotheses (Hn : (0 <= n < 2^scalarbitsz)%Z)
          (Hscalarbitsz : (0 < scalarbitsz)%Z).
        Local Notation testbitn := (Z.testbit n).

        (* Highly regular right-to-left algorithms for scalar multiplication *)
        (* Marc Joye *)
        (* §2.1 Double-add algorithm *)
        Fixpoint SS (i : nat) :=
          match i with
          | O => Z.b2z (testbitn 0)
          | S j => if (testbitn (Z.of_nat i)) then (2 * SS j + TT j)%Z else SS j
          end
        with TT (i : nat ) :=
               match i with
               | O => 2 - Z.b2z (testbitn 0)
               | S j => if (testbitn (Z.of_nat i)) then TT j else (2 * TT j + SS j)%Z
               end.

        Fixpoint SS' (i : nat) :=
          match i with
          | O => Z.b2z (testbitn 0)
          | S j => ((Z.b2z (testbitn (Z.of_nat i)) * 2^(Z.of_nat i)) + SS' j)%Z
          end.

        Definition TT' (i: nat) := (2^(Z.of_nat (S i)) - SS' i)%Z.

        Lemma SS_is_SS' (i : nat) :
          SS i = SS' i :> Z
        with TT_is_TT' (i : nat) :
          TT i = TT' i :> Z.
        Proof.
          { destruct i.
            - reflexivity.
            - cbn [SS SS'].
              destruct (testbitn (Z.of_nat (S i))).
              + rewrite TT_is_TT'. unfold TT'.
                rewrite <- SS_is_SS'. cbv [Z.b2z]. lia.
              + cbv [Z.b2z]. rewrite <- SS_is_SS'. lia. }
          { destruct i.
            - reflexivity.
            - cbn [TT]. unfold TT'; fold TT'.
              cbn [SS']. destruct (testbitn (Z.of_nat (S i))).
              + cbv [Z.b2z]. rewrite TT_is_TT'. unfold TT'; fold TT'.
                replace (2 ^ Z.of_nat (S (S i)))%Z with (2 * 2 ^ Z.of_nat (S i))%Z.
                2:{ repeat rewrite <- two_power_nat_equiv.
                    rewrite (two_power_nat_S (S i)). reflexivity. }
                lia.
              + cbv [Z.b2z]. rewrite TT_is_TT'.
                unfold TT'; fold TT'. rewrite SS_is_SS'.
                replace (2 ^ Z.of_nat (S (S i)))%Z with (2 * 2 ^ Z.of_nat (S i))%Z.
                2:{ repeat rewrite <- two_power_nat_equiv.
                    rewrite (two_power_nat_S (S i)). reflexivity. }
                lia. }
        Qed.

        Lemma SS_decomposition (i : nat) :
          SS i = Z.land n (Z.ones (Z.of_nat (S i))) :> Z.
        Proof.
          rewrite SS_is_SS'. induction i.
          - cbn [SS' testbitn]. replace (Z.of_nat 1) with 1%Z by lia.
            rewrite (Z.land_ones n 1 ltac:(lia)).
            replace (2^1)%Z with 2%Z by reflexivity.
            rewrite Zmod_odd. reflexivity.
          - cbn [SS']. rewrite IHi.
            apply Z.bits_inj'. intros k Hk.
            rewrite Z.land_spec. rewrite (Z.testbit_ones (Z.of_nat (S (S i))) k ltac:(lia)).
            rewrite (Zle_imp_le_bool _ _ Hk), Bool.andb_true_l.
            rewrite Z.add_nocarry_lxor.
            2:{ clear. apply Z.bits_inj'; intros k Hk.
                rewrite Z.land_spec, Z.bits_0.
                rewrite Z.land_spec.
                rewrite (Z.testbit_ones (Z.of_nat (S i)) k ltac:(lia)).
                rewrite (Zle_imp_le_bool _ _ Hk), Bool.andb_true_l.
                destruct (dec (Z.lt k (Z.of_nat (S i)))).
                - rewrite (proj1 (Zlt_is_lt_bool k _) l), Bool.andb_true_r.
                  replace (Z.testbit (Z.b2z (testbitn (Z.of_nat (S i))) * 2 ^ Z.of_nat (S i)) k) with false; [reflexivity|].
                  destruct (testbitn (Z.of_nat (S i))).
                  + rewrite Z.mul_1_l. rewrite Z.pow2_bits_false; auto. lia.
                  + rewrite Z.mul_0_l. rewrite Z.bits_0. reflexivity.
                - rewrite (proj2 (Z.ltb_nlt k _) n0).
                  repeat rewrite (Bool.andb_false_r); reflexivity. }
            rewrite Z.lxor_spec, Z.land_spec.
            destruct (dec (Z.lt k (Z.of_nat (S (S i))))).
            + rewrite (proj1 (Zlt_is_lt_bool k _) l).
              rewrite Bool.andb_true_r.
              destruct (dec (Z.lt k (Z.of_nat (S i)))).
              * rewrite Z.ones_spec_low; [|lia].
                rewrite Bool.andb_true_r.
                replace (Z.testbit (Z.b2z (testbitn (Z.of_nat (S i))) * 2 ^ Z.of_nat (S i)) k) with false; [reflexivity|].
                destruct (testbitn (Z.of_nat (S i))).
                { rewrite Z.mul_1_l. rewrite Z.pow2_bits_false; auto. lia. }
                { rewrite Z.mul_0_l. rewrite Z.bits_0. reflexivity. }
              * assert (k = Z.of_nat (S i) :> Z) as -> by lia.
                clear. rewrite Z.ones_spec_high; [|lia].
                rewrite Bool.andb_false_r, Bool.xorb_false_r.
                destruct (testbitn (Z.of_nat (S i))).
                { rewrite Z.mul_1_l. rewrite Z.pow2_bits_true; auto. lia. }
                { rewrite Z.mul_0_l. rewrite Z.bits_0. reflexivity. }
            + rewrite (proj2 (Z.ltb_nlt k _) n0).
              rewrite Bool.andb_false_r. rewrite Z.ones_spec_high; [|lia].
              rewrite Bool.andb_false_r, Bool.xorb_false_r.
              destruct (testbitn (Z.of_nat (S i))).
              * rewrite Z.mul_1_l. rewrite Z.pow2_bits_false; auto. lia.
              * rewrite Z.mul_0_l. rewrite Z.bits_0. reflexivity.
        Qed.

        Lemma SSn :
          SS (Z.to_nat scalarbitsz - 1) = n :> Z.
        Proof.
          rewrite SS_decomposition.
          replace (Z.of_nat (S (Z.to_nat scalarbitsz - 1)))%Z with scalarbitsz by lia.
          apply Ones.Z.land_ones_low_alt. split; lia.
        Qed.

        Lemma SS_plus_TT (k: nat) :
          (SS k + TT k)%Z = (2^(Z.of_nat (S k)))%Z :> Z.
        Proof.
          rewrite SS_is_SS', TT_is_TT'.
          unfold TT'. lia.
        Qed.

        Lemma SS_sub_TT0 :
          (TT 0 - SS 0)%Z = (2 * (1 - Z.b2z (testbitn 0)))%Z :> Z.
        Proof. unfold TT, SS. lia. Qed.

        Lemma SS_sub_TT_S (k : nat) :
          if testbitn (Z.of_nat (S k)) then
            (SS (S k) - TT (S k))%Z = (2 * SS k)%Z :> Z
          else
            (TT (S k) - SS (S k))%Z = (2 * TT k)%Z :> Z.
        Proof. cbn [SS TT]. destruct (testbitn (Z.of_nat (S k))); lia. Qed.

        Lemma SS_bounds (k : nat) :
          (0 <= SS k <= n)%Z.
        Proof.
          rewrite SS_decomposition, Z.land_ones; [|lia].
          split; [apply Z_mod_nonneg_nonneg| apply Z.mod_le]; lia.
        Qed.

        Lemma SS_bounds2 (k : nat) :
          (0 <= SS k <= 2^(Z.of_nat (S k)))%Z.
        Proof.
          rewrite SS_is_SS'. induction k.
          - simpl. destruct (Z.odd n); simpl; lia.
          - cbn [SS']. destruct (testbitn (Z.of_nat (S k))); cbn [Z.b2z];
              repeat rewrite <- two_power_nat_equiv in *;
              repeat rewrite two_power_nat_S in *; lia.
        Qed.

        Lemma TT_bounds (k : nat) :
          (0 <= TT k <= 2^(Z.of_nat (S k)))%Z.
        Proof.
          rewrite TT_is_TT'; unfold TT'. rewrite <- SS_is_SS'.
          generalize (SS_bounds2 k). intros HH. lia.
        Qed.
      End Auxiliary.

      (* We compute [n]P where P ≠ ∞ and n < ord(P) *)
      Context {n scalarbitsz : Z}
              {Hn : (2 <= n < 2^scalarbitsz)%Z}
              {Hscalarbitsz : (2 <= scalarbitsz)%Z}
              {P : Wpoint} {HPnz : P <> ∞ :> Wpoint}
              {ordP : Z} {HordPpos : (3 < ordP)%Z}
              {HordP : forall k, (0 < k < ordP)%Z -> not (Weq (scalarmult k P) ∞)}
              {HordPn : (n + 2 < ordP)%Z}

              (* Is this realistic ? *)
              {HordPbig : (2^(scalarbitsz - 1) <= ordP)%Z}.

      Local Notation testbitn := (Z.testbit n).
      Local Notation n' := (if testbitn 0 then n else (n + 1)%Z).
      Local Notation testbitn' := (Z.testbit n').

      Lemma Hn' :
        (2 <= n' < 2^scalarbitsz)%Z.
      Proof.
        split; [destruct (testbitn 0); lia|].
        destruct (testbitn 0) eqn:Y; [lia|].
        destruct (dec (Z.lt (n + 1)%Z (2 ^ scalarbitsz)%Z)); auto.
        assert (Z.succ n = 2 ^ scalarbitsz :> Z)%Z by lia.
        rewrite Z.bit0_odd in Y.
        assert (Z.odd n = true :> bool); [|congruence].
        rewrite <- Z.even_succ, H, <- Z.negb_odd, <- Z.bit0_odd.
        rewrite Z.pow2_bits_false; auto. lia.
      Qed.

      Lemma Htestbitn'0 :
        testbitn' 0 = true :> bool.
      Proof.
        destruct (testbitn 0) eqn:Heq; auto.
        rewrite Z.bit0_odd in *. replace (n + 1)%Z with (Z.succ n) by lia.
        rewrite Z.odd_succ. rewrite <- Z.negb_odd, Heq. reflexivity.
      Qed.

      Lemma Htestbitn' :
         forall j, (1 <= j)%Z ->
              testbitn j = testbitn' j :> bool.
      Proof.
        destruct (testbitn 0) eqn:Heq; auto.
        intros. destruct n.
        - rewrite Z.bits_0. rewrite Testbit.Z.bits_1.
          destruct (Z.eq_dec j 0); auto; lia.
        - destruct p.
          + simpl in Heq. congruence.
          + replace j with (Z.succ (j - 1)%Z) by lia.
            replace (Z.pos p~0) with (2 * Z.pos p)%Z by lia.
            rewrite Z.testbit_even_succ, Z.testbit_odd_succ; auto; lia.
          + rewrite Testbit.Z.bits_1 in Heq.
            destruct (Z.eq_dec 0 0); congruence.
        - lia.
      Qed.

      Lemma Pynz :
        y_of (of_affine P) <> 0.
      Proof.
        destruct P as [ [ [X Y] | u] HP]; [|elim HPnz; clear; t].
        cbn. intro HY.
        apply (HordP (Z.succ 1%Z)); [lia|].
        rewrite (@scalarmult_ref_is_scalarmult Wpoint Weq Wadd Wzero Wopp Wgroup.(Hierarchy.commutative_group_group)).(scalarmult_succ_l_nn); auto; try lia.
        generalize (Wgroup.(Hierarchy.commutative_group_group).(Hierarchy.group_monoid).(Hierarchy.monoid_op_Proper)). intros.
        rewrite (@scalarmult_1_l _ _ _ _ _ Wgroup.(Hierarchy.commutative_group_group) _ (@scalarmult_ref_is_scalarmult Wpoint Weq Wadd Wzero Wopp Wgroup.(Hierarchy.commutative_group_group))).
        cbv [Wadd Weq]. simpl.
        destruct (dec (X = X)); try fsatz.
        destruct (dec (Y = Fopp Y)); auto; fsatz.
      Qed.

      Lemma joye_ladder_correct0 (Hscalarbitsz0 : scalarbitsz = 0%Z :> Z) :
        Weq (joye_ladder scalarbitsz testbitn P HPnz) (scalarmult 0%Z P).
      Proof.
        subst scalarbitsz. assert (n = 0%Z :> Z) by lia. subst n. simpl.
        rewrite <- (Jacobian.to_affine_of_affine Wzero).
        unfold joye_ladder. apply Jacobian.Proper_to_affine.
        unfold eq; simpl. destruct P as [ [ [X Y] | ?] HP]; [|elim HPnz; clear; t].
        cbn [W.coordinates]. rewrite (surjective_pairing (joye_ladder_inner 0 (Z.testbit 0) _)).
        rewrite (surjective_pairing (fst _)).
        destruct (dec (snd (joye_ladder_inner 0 (Z.testbit 0) (X, Y, 1)) = 0)) as [?|HH]; [reflexivity| elim HH].
        cbn. fsatz.
      Qed.

      Lemma dblu_scalarmult' (Hz1 : z_of (of_affine P) = 1) :
        eq (fst (dblu (of_affine P) Hz1)) (scalarmult' 2 (of_affine P))
        /\ eq (snd (dblu (of_affine P) Hz1)) (scalarmult' 1 (of_affine P)).
      Proof.
        generalize (@Jacobian.dblu_correct F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field char_ge_3 Feq_dec char_ge_12 (of_affine P) Hz1 Pynz).
        rewrite (surjective_pairing (dblu _ _)) at 1.
        intros (A & B & C). split.
        - rewrite <- A. replace 2%Z with (1 + 1)%Z by lia.
          rewrite (@scalarmult_add_l point eq add zero opp Pgroup); [|apply (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)].
          rewrite (@scalarmult_1_l point eq add zero opp Pgroup); [|apply (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)].
          rewrite <- Jacobian.add_double; reflexivity.
        - rewrite (@scalarmult_1_l point eq add zero opp Pgroup); [|apply (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)].
          symmetry. assumption.
      Qed.

      Lemma co_xz_implies (P1 P2 : point) (Hxeq : x_of P1 = x_of P2)
        (Hzeq : z_of P1 = z_of P2) :
        eq P1 P2 \/ eq P1 (opp P2).
      Proof.
        clear -Hxeq Hzeq. prept; [tauto|fsatz|fsatz|].
        assert (f4 = f1 \/ f4 = Fopp f1) by (destruct (dec (f4 = f1)); [left; assumption|right; fsatz]).
        destruct H; [left; repeat split; fsatz|right; repeat split; fsatz].
      Qed.

      Lemma tplu_scalarmult' (Hz1 : z_of (of_affine P) = 1) :
        eq (fst (tplu (of_affine P) Hz1)) (scalarmult' 3 (of_affine P))
        /\ eq (snd (tplu (of_affine P) Hz1)) (scalarmult' 1 (of_affine P))
        /\ co_z (fst (tplu (of_affine P) Hz1)) (snd (tplu (of_affine P) Hz1)).
      Proof.
        rewrite (proj1 (Jacobian.tplu_tplu2 _ _)) at 1.
        rewrite (proj2 (Jacobian.tplu_tplu2 _ _)) at 1.
        unfold Jacobian.tplu2. generalize (dblu_scalarmult' Hz1).
        set (P1 := (snd (dblu (of_affine P) Hz1))).
        set (P2 := (fst (dblu (of_affine P) Hz1))). intros [A1 A2].
        destruct (dec (x_of P1 = x_of P2)) as [Hxe|Hxne].
        { destruct (co_xz_implies P1 P2 Hxe (CoZ.Jacobian.tplu2_obligation_1 (of_affine P) Hz1)) as [A|A].
          - rewrite A1, A2 in A.
            elim (HordP 1%Z ltac:(lia)).
            rewrite <- (Jacobian.to_affine_of_affine). symmetry.
            rewrite <- (Jacobian.to_affine_of_affine) at 1.
            apply Jacobian.Proper_to_affine.
            rewrite scalarmult_scalarmult'; [|lia].
            rewrite <- (@scalarmult_0_l point eq add zero opp scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) (of_affine P)) at 1.
            replace 1%Z with (2 - 1)%Z by lia.
            rewrite (@scalarmult_sub_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) 2 1).
            rewrite A.
            rewrite <- (@scalarmult_opp_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)).
            rewrite <- (@scalarmult_add_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) 2 (- 2)).
            replace (2 + -2)%Z with 0%Z by lia. reflexivity.
          - rewrite A1, A2 in A.
            elim (HordP 3%Z ltac:(lia)).
            rewrite <- (Jacobian.to_affine_of_affine). symmetry.
            rewrite <- (Jacobian.to_affine_of_affine) at 1.
            apply Jacobian.Proper_to_affine.
            rewrite scalarmult_scalarmult'; [|lia].
            rewrite <- (@scalarmult_0_l point eq add zero opp scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) (of_affine P)) at 1.
            replace 0%Z with (2 - 2)%Z by lia.
            rewrite (@scalarmult_sub_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) 2 2).
            rewrite <- A.
            rewrite <- (@scalarmult_add_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) 2 1).
            replace (2 + 1)%Z with 3%Z by lia. reflexivity. }
        generalize (@Jacobian.zaddu_correct F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field char_ge_3 Feq_dec P1 P2 (CoZ.Jacobian.tplu2_obligation_1 (of_affine P) Hz1) Hxne).
        rewrite (surjective_pairing (zaddu _ _ _)) at 1.
        intros (A & B & C). rewrite <- B. split; auto.
        rewrite <- A. rewrite A1, A2.
        rewrite <- (@scalarmult_add_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) 1 2).
        replace (1 + 2)%Z with 3%Z by lia. reflexivity.
      Qed.

      Lemma eq_proof_irr (P1 P2 : point) :
        proj1_sig P1 = proj1_sig P2 :> (F*F*F) ->
        eq P1 P2.
      Proof. clear -field; intros. unfold eq. rewrite H. t. Qed.

      Lemma joye_inner_correct (Hjoye : is_point (joye_ladder_inner scalarbitsz testbitn (proj1_sig (of_affine P)))) :
        eq
          (exist _
             (joye_ladder_inner scalarbitsz testbitn (proj1_sig (of_affine P)))
             Hjoye)
          (scalarmult' n (of_affine P)).
      Proof.
        assert (HPaff: z_of (of_affine P) = 1) by (destruct P as [ [ [X Y] | ?] HP] eqn:HPeq; [reflexivity|elim HPnz; clear; t]).
        unfold joye_ladder_inner, eq.
        set (TPLU := (tplu (of_affine P) HPaff)).
        red. replace (tplu_inner (proj1_sig (of_affine P))) with (proj1_sig (fst TPLU), proj1_sig (snd TPLU)); [|symmetry; unfold TPLU, tplu; apply surjective_pairing].
        set (R1 := if testbitn 1 then proj1_sig (snd TPLU) else proj1_sig (fst TPLU)).
        set (R0 := if testbitn 1 then proj1_sig (fst TPLU) else proj1_sig (snd TPLU)).
        replace (if testbitn 1 then (proj1_sig (snd TPLU), proj1_sig (fst TPLU)) else (proj1_sig (fst TPLU), proj1_sig (snd TPLU))) with (R1, R0) by (destruct (testbitn 1); reflexivity).
        set (WW := while (fun '(_, i) => (i <? scalarbitsz)%Z)
        (fun '(R2, R3, i) =>
         let
         '(R4, R5) := if testbitn i then (R3, R2) else (R2, R3) in
          let
          '(R6, R7) :=
           let '(P0, Q) := zdau_inner R4 R5 in if testbitn i then (Q, P0) else (P0, Q)
          in (R6, R7, Z.succ i)) (Z.to_nat scalarbitsz) (R1, R0, 2%Z)).
        set (inv :=
               fun '(R1, R0, i) =>
                 is_point R1 /\ is_point R0 /\ snd R1 = snd R0 /\
                   (2 <= i <= scalarbitsz)%Z  /\
                   forall (pR1 : is_point R1) (pR0 : is_point R0),
                     (eq (exist _ R1 pR1) (scalarmult' (TT n' ((Z.to_nat i) - 1)%nat) (of_affine P))
                     /\ eq (exist _ R0 pR0) (scalarmult' (SS n' ((Z.to_nat i) - 1)%nat) (of_affine P)))
                     /\ ((i < scalarbitsz - 1)%Z -> x_of (exist _ R1 pR1) <> x_of (exist _ R0 pR0))).
        assert (WWinv : inv WW /\ (snd WW = scalarbitsz :> Z)).
        { set (measure := fun (state : ((F*F*F)*(F*F*F)*BinNums.Z)) => ((Z.to_nat scalarbitsz) + 2 - (Z.to_nat (snd state)))%nat).
          unfold WW. replace (Z.to_nat scalarbitsz) with (measure (R1, R0, 2%Z)) by (unfold measure; simpl; lia).
          eapply (while.by_invariant inv measure (fun s => inv s /\ (snd s = scalarbitsz :> Z))).
          - unfold inv. do 3 (try split).
            + unfold R1. destruct (testbitn 1);
              match goal with |- is_point (proj1_sig ?X) => destruct X as (? & ?Y); exact Y end.
            + unfold R0. destruct (testbitn 1);
              match goal with |- is_point (proj1_sig ?X) => destruct X as (? & ?Y); exact Y end.
            + destruct (tplu_scalarmult' HPaff) as [Heq1 [Heq2 Heqz] ].
              fold TPLU in Heq1, Heq2, Heqz. intros.
              unfold R1, R0; unfold co_z, z_of in Heqz; destruct (proj1_sig (snd TPLU)) as ((? & ?) & ?); destruct (proj1_sig (fst TPLU)) as ((? & ?) & ?); destruct (testbitn 1); simpl; fsatz.
            + replace (Z.to_nat 2 - 1)%nat with 1%nat by lia.
              cbn [TT SS]. rewrite Htestbitn'0.
              replace (Z.of_nat 1%nat) with 1%Z by lia.
              rewrite <- (Htestbitn' 1%Z ltac:(lia)).
              cbn [Z.b2z]. replace (2 - 1)%Z with 1%Z by lia.
              replace (2 * 1 + 1)%Z with 3%Z by lia.
              destruct (tplu_scalarmult' HPaff) as [Heq1 [Heq2 Heqz] ].
              fold TPLU in Heq1, Heq2, Heqz. split; [lia|].
              intros. split.
              * intros. unfold R1, R0; destruct (testbitn 1); rewrite <- Heq1, <- Heq2; split; eapply eq_proof_irr; reflexivity.
              * intros AB Hxe. destruct (co_xz_implies (fst TPLU) (snd TPLU)).
                { unfold x_of. unfold R1, R0 in Hxe.
                  destruct (proj1_sig (snd TPLU)) as ((? & ?) & ?); destruct (proj1_sig (fst TPLU)) as ((? & ?) & ?); destruct (testbitn 1); simpl; fsatz. }
                { exact Heqz. }
                { rewrite Heq1, Heq2 in H.
                  eapply (HordP 2 ltac:(lia)).
                  rewrite <- (Jacobian.to_affine_of_affine). symmetry.
                  rewrite <- (Jacobian.to_affine_of_affine) at 1.
                  apply Jacobian.Proper_to_affine.
                  rewrite scalarmult_scalarmult'; [|lia].
                  replace 2%Z with (3 + (- 1))%Z by lia.
                  rewrite (@scalarmult_add_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) 3 (-1)).
                  rewrite H.
                  rewrite <- (@scalarmult_add_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) 1 (-1)).
                  replace (1 + -1)%Z with 0%Z by lia.
                  rewrite <- (@scalarmult_0_l point eq add zero opp scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) (of_affine P)) at 1.
                  reflexivity. }
                { rewrite Heq1, Heq2 in H.
                  eapply (HordP 4).
                  - split; [lia|].
                    assert (4 < 2 ^ (scalarbitsz - 1))%Z; [|lia].
                    replace 4%Z with (Z.pow 2 2)%Z by lia. clear -AB.
                    apply Z.pow_lt_mono_r; auto; lia.
                  - rewrite <- (Jacobian.to_affine_of_affine). symmetry.
                    rewrite <- (Jacobian.to_affine_of_affine) at 1.
                    apply Jacobian.Proper_to_affine.
                    rewrite scalarmult_scalarmult'; [|lia].
                    rewrite (@scalarmult_1_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)) in H.
                    rewrite <- (@scalarmult_opp1_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)) in H.
                    replace 4%Z with (3 - -1)%Z by lia.
                    rewrite (@scalarmult_sub_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) 3 (-1) (of_affine P)).
                    rewrite H.
                    rewrite <- (@scalarmult_sub_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) (-1) (-1) (of_affine P)).
                    replace (-1 - (-1))%Z with 0%Z by lia.
                    apply (@scalarmult_0_l point eq add zero opp scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) (of_affine P)). }
          - intros s Hinv. destruct s as ((X1 & X0) & i).
            destruct Hinv as (HX1 & HX0 & HXze & Hi & Heqs).
            destruct (Z.ltb i scalarbitsz) eqn:Hltb.
            + split.
              * (* invariant preservation *)
                admit.
              * (* measure decreases *)
                replace (if testbitn i then (X0, X1) else (X1, X0)) with (if testbitn i then X0 else X1, if testbitn i then X1 else X0) by (destruct (testbitn i); reflexivity).
                destruct (zdau_inner (if testbitn i then X0 else X1) (if testbitn i then X1 else X0)); destruct (testbitn i); unfold measure; simpl; lia.
            + (* post condition *)
              split; [split; auto|].
              simpl. rewrite Z.ltb_ge in Hltb. lia. }
        destruct WW as ((R1' & R0') & I).
        simpl in WWinv. destruct WWinv as [ [HpR1 [HpR0 [Hz [_ WWinv] ] ] ] ->].
        specialize (WWinv HpR1 HpR0). destruct WWinv as [ [HR1eq HR0eq] _].
        rewrite SSn in HR0eq; [|generalize Hn'; fold n'; lia|lia].
        replace (opp_inner (proj1_sig (of_affine P))) with (proj1_sig (opp (of_affine P))) by reflexivity.
        assert (HPaff' : z_of (opp (of_affine P)) = 1) by (destruct P as [ [ [X Y] | ?] HP] eqn:HPeq; [reflexivity|elim HPnz; clear; t]).
        pose (COZ := make_co_z (exist _ R0' HpR0) (opp (of_affine P)) HPaff').
        replace (make_co_z_inner R0' (proj1_sig (opp (of_affine P)))) with (proj1_sig (fst COZ), proj1_sig (snd COZ)) by (symmetry; unfold COZ, make_co_z; simpl; apply surjective_pairing).
        assert (HR0znz : z_of (exist is_point R0' HpR0) <> 0).
        { intro. apply (HordP (if Z.odd n then n else (n + 1)%Z)).
          - destruct (Z.odd n); lia.
          - rewrite <- (Jacobian.to_affine_of_affine). symmetry.
            rewrite <- (Jacobian.to_affine_of_affine) at 1.
            apply Jacobian.Proper_to_affine.
            rewrite scalarmult_scalarmult'; [|destruct (Z.odd n); lia].
            rewrite <- HR0eq. unfold z_of in H. unfold eq, zero. simpl.
            simpl in H. destruct (dec (0 = 0)) as [?|Hnn]; [|elim Hnn; reflexivity].
            destruct R0' as ((? & ?) & ?); auto. }
        destruct (@Jacobian.make_co_z_correct F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec (exist is_point R0' HpR0) (opp (of_affine P)) HPaff' HR0znz) as (Heq0 & Heq1 & HCOZ).
        rewrite Heq0 in HR0eq.
        rewrite <- (@scalarmult_opp1_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) (of_affine P)) in Heq1 at 1.
        set (ZADDU := zaddu (fst COZ) (snd COZ) HCOZ).
        replace (zaddu_inner (proj1_sig (fst COZ)) (proj1_sig (snd COZ))) with (proj1_sig (fst ZADDU), proj1_sig (snd ZADDU)) by (symmetry; unfold ZADDU, zaddu; simpl; apply surjective_pairing).
        assert (Hxne: x_of (fst COZ) <> x_of (snd COZ)).
        { intro Hxe. destruct (co_xz_implies _ _ Hxe HCOZ) as [HEq|HNeq].
          - unfold COZ in HEq.
            rewrite HR0eq in HEq.
            rewrite <- Heq1 in HEq.
            apply (HordP ((if Z.odd n then n else (n + 1)%Z) - -1)%Z).
            + split; destruct (Z.odd n); lia.
            + rewrite <- (Jacobian.to_affine_of_affine). symmetry.
              rewrite <- (Jacobian.to_affine_of_affine) at 1.
              apply Jacobian.Proper_to_affine.
              rewrite scalarmult_scalarmult'; [|destruct (Z.odd n); lia].
              rewrite (@scalarmult_sub_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)).
              rewrite HEq.
              rewrite <- (@scalarmult_sub_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)).
              replace (-1 - -1)%Z with 0%Z by lia.
              apply (@scalarmult_0_l point eq add zero opp scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) (of_affine P)).
          - unfold COZ in HNeq.
            rewrite HR0eq in HNeq.
            rewrite <- Heq1 in HNeq.
            apply (HordP ((if Z.odd n then n else (n + 1)%Z) - 1)%Z).
            + split; destruct (Z.odd n); lia.
            + rewrite <- (Jacobian.to_affine_of_affine). symmetry.
              rewrite <- (Jacobian.to_affine_of_affine) at 1.
              apply Jacobian.Proper_to_affine.
              rewrite scalarmult_scalarmult'; [|destruct (Z.odd n); lia].
              rewrite (@scalarmult_sub_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)).
              rewrite HNeq.
              rewrite <- (@scalarmult_opp_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)) at 1.
              rewrite <- (@scalarmult_sub_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)).
              replace (- -1 - 1)%Z with 0%Z by lia.
              apply (@scalarmult_0_l point eq add zero opp scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) (of_affine P)). }
        generalize (@Jacobian.zaddu_correct F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field char_ge_3 Feq_dec (fst COZ) (snd COZ) HCOZ Hxne).
        fold ZADDU. rewrite (surjective_pairing ZADDU) at 1.
        intros [Heq2 [Heq3 HCOZ1] ]. rewrite Z.bit0_odd.
        replace (if Z.odd n then (proj1_sig (snd ZADDU), proj1_sig (fst ZADDU)) else (proj1_sig (fst ZADDU), proj1_sig (snd ZADDU))) with (proj1_sig (if Z.odd n then snd ZADDU else fst ZADDU), proj1_sig (if Z.odd n then fst ZADDU else snd ZADDU)) by (destruct (Z.odd n); reflexivity).
        assert (eq (if Z.odd n then snd ZADDU else fst ZADDU) (scalarmult' n (of_affine P))); auto.
        destruct (Z.odd n); fold COZ in Heq0, Heq1, HR0eq.
        - rewrite <- Heq3, HR0eq. reflexivity.
        - rewrite <- Heq2, HR0eq, <- Heq1.
          rewrite <- (@scalarmult_add_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)).
          replace (n + 1 + -1)%Z with n by lia. reflexivity.
      Admitted.

      Lemma joye_ladder_correct :
        Weq (joye_ladder scalarbitsz testbitn P HPnz) (scalarmult n P).
      Proof.
        rewrite <- (Jacobian.to_affine_of_affine (scalarmult n P)).
        apply Jacobian.Proper_to_affine. rewrite scalarmult_scalarmult'; [|lia].
        eapply joye_inner_correct.
      Qed.

    End Proof.
  End JoyeLadder.
End ScalarMult.
