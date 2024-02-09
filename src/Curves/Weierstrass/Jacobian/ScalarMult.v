Require Import Coq.Classes.Morphisms.

Require Import Crypto.Spec.WeierstrassCurve Crypto.Algebra.ScalarMult.
Require Import Crypto.Curves.Weierstrass.Jacobian.Jacobian.
Require Import Crypto.Curves.Weierstrass.Affine Crypto.Curves.Weierstrass.Jacobian.CoZ.
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
    Local Notation "2" := (1+1). Local Notation "8" := (2+2+2+2).
    Local Notation "'∞'" := (@W.zero F Feq Fadd Fmul a b).
    Local Notation Wpoint := (@W.point F Feq Fadd Fmul a b).
    Local Notation Wopp := (@W.opp F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation Wadd := (@W.add F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv field Feq_dec char_ge_3 a b).
    Local Notation Wzero := (@W.zero F Feq Fadd Fmul a b).
    Local Notation Weq := (@W.eq F Feq Fadd Fmul a b).
    Local Notation point := (@Jacobian.point F Feq Fzero Fadd Fmul a b Feq_dec).
    Local Notation eq := (@Jacobian.eq F Feq Fzero Fadd Fmul a b Feq_dec).
    Local Notation x_of := (@Jacobian.x_of F Feq Fzero Fadd Fmul a b Feq_dec).
    Local Notation y_of := (@Jacobian.y_of F Feq Fzero Fadd Fmul a b Feq_dec).
    Local Notation z_of := (@Jacobian.z_of F Feq Fzero Fadd Fmul a b Feq_dec).
    Local Notation opp := (@Jacobian.opp F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation make_co_z_inner := (@Jacobian.make_co_z_inner F Fmul).
    Local Notation make_co_z := (@Jacobian.make_co_z F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation of_affine := (@Jacobian.of_affine F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation to_affine := (@Jacobian.to_affine F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation tplu_inner := (@Jacobian.tplu_inner F Fone Fadd Fsub Fmul a).
    Local Notation zaddu_inner := (@Jacobian.zaddu_inner F Fsub Fmul).
    Local Notation zdau_inner := (@Jacobian.zdau_inner F Fadd Fsub Fmul).
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
      destruct (@Jacobian.make_co_z F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec (exist _ P HP) (exist _ Q HQ) ltac:(t)) as ((R0 & R1) & Y) eqn:Heq.
      unfold make_co_z in Heq. inversion Heq; clear Heq.
      destruct R0 as [R0 HR0]. inversion H1; clear H1.
      destruct R1 as [R1 HR1]. inversion H2; clear H2.
      rewrite H1, H3. unfold Jacobian.co_z in Y. unfold z_of in Y.
      simpl in Y. repeat split; auto.
      destruct R0 as ((? & ?) & ?); destruct R1 as ((? & ?) & ?); assumption.
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
      let '(x, y, z) := P in
      let mP := (x, Fopp y, z) in
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
      assert (HmP : is_point (X, Fopp Y, Z)) by (unfold is_point in *; t).
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

    Lemma joye_ladder_correct
      (n : Z) (P : Wpoint)
      (bitsize : Z) (HPnz : P <> ∞ :> Wpoint)
      (Hn : (0 <= n < 2^bitsize)%Z)
      (Hbitsize : (0 <= bitsize)%Z)
      : Weq (joye_ladder bitsize (Z.testbit n) P HPnz) (scalarmult n P).
    Proof.
      unfold joye_ladder; simpl.
      cbv [joye_ladder]. simpl.

  End JoyeLadder.
End ScalarMult.
