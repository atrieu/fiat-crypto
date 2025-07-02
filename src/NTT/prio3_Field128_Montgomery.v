Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.NTT.BedrockNTTn.
Require Import bedrock2.BasicC64Semantics.
Require Import Rupicola.Lib.Core.
Require Import bedrock2.ToCString.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Interface.Representation.
Require Import Crypto.Bedrock.Field.Synthesis.New.ComputedOp.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Bedrock.Specs.Field.

From Coqprime.PrimalityTest Require Import Pocklington PocklingtonCertificat.

Import BasicC64Semantics.

Section Field128.
  (* q = 2^66 * 4611686018427387897 + 1 *)
  Local Notation q := 340282366920938462946865773367900766209%positive.
  Local Notation F := (F q).

  (* Sanity check *)
  Lemma q_def:
    Z.pos q = 2^66 * 4611686018427387897 + 1.
  Proof.
    reflexivity.
  Qed.

  (* Sanity check *)
  Lemma fp128_prime_q: prime (Z.pos q).
  Proof.
    apply (Pocklington_refl
             (Pock_certif 340282366920938462946865773367900766209 7 ((2,66)::nil)%positive 1)
             ((Proof_certif 2 prime_2) ::
                nil)).
    native_cast_no_check (refl_equal true).
  Qed.

  Existing Instances Bitwidth64.BW64
    Defaults64.default_parameters Defaults64.default_parameters_ok.
  Definition prefix : string := "fp128_"%string.

  Section Ops.

    (* Define Field128 parameters *)
    Instance field_parameters : FieldParameters.
    Proof using Type.
      let M := (eval vm_compute in (Z.to_pos (q))) in
      (* 'A' parameter *)
      let a := constr:(F.of_Z M 0) in
      let prefix := prefix in
      eapply
        (field_parameters_prefixed
           M ((a + F.of_Z _ 2) / F.of_Z _ 4)%F prefix).
    Defined.

    Definition to_mont_string := (prefix ++ "to_mont")%string.
    Definition from_mont_string := (prefix ++ "from_mont")%string.

    (* Call fiat-crypto pipeline on all field operations *)
    Instance fp128_ops : @word_by_word_Montgomery_ops from_mont_string to_mont_string _ _ _ _ _ _ _ _ _ _ (WordByWordMontgomery.n q machine_wordsize) q.
    Proof using Type. Time constructor; make_computed_op. Defined.

    (**** Translate each field operation into bedrock2 and apply bedrock2 backend
        field pipeline proofs to prove the bedrock2 functions are correct. ****)

    Local Ltac begin_derive_bedrock2_func :=
      lazymatch goal with
      | |- context [spec_of_BinOp bin_mul] => eapply mul_func_correct
      | |- context [spec_of_UnOp un_square] => eapply square_func_correct
      | |- context [spec_of_BinOp bin_add] => eapply add_func_correct
      | |- context [spec_of_BinOp bin_sub] => eapply sub_func_correct
      | |- context [spec_of_UnOp un_opp] => eapply opp_func_correct
      | |- context [spec_of_from_bytes] => eapply from_bytes_func_correct
      | |- context [spec_of_to_bytes] => eapply to_bytes_func_correct
      | |- context [spec_of_selectznz] => eapply select_znz_func_correct
      | |- context [spec_of_felem_copy] => eapply felem_copy_func_correct
      | |- context [spec_of_UnOp un_from_mont] => eapply (from_mont_func_correct _ _ _ from_mont_string to_mont_string)
      | |- context [spec_of_UnOp un_to_mont] => eapply (to_mont_func_correct _ _ _ from_mont_string to_mont_string)
      end.

    Ltac epair :=
      lazymatch goal with
      | f := _ : string * Syntax.func |- _ =>
               let p := open_constr:((_, _)) in
               unify f p;
               subst f
      end.

    Ltac derive_bedrock2_func op :=
      epair;
      begin_derive_bedrock2_func;
      (* this goal fills in the evar, so do it first for [abstract] to be happy *)
      try lazymatch goal with
        | |- _ = b2_func _ => vm_compute; reflexivity
        end;
      (* solve all the remaining goals *)
      lazymatch goal with
      | |- _ = @ErrorT.Success ?ErrT unit tt =>
          abstract (vm_cast_no_check (@eq_refl _ (@ErrorT.Success ErrT unit tt)))
      | |- Func.valid_func _ =>
          eapply Func.valid_func_bool_iff;
          abstract vm_cast_no_check (eq_refl true)
      | |- (_ = _)%Z => vm_compute; reflexivity
      end.

    Local Notation functions_contain functions f :=
      (Interface.map.get functions (fst f) = Some (snd f)).

    Derive fp128_felem_copy
      SuchThat (forall functions,
                   functions_contain functions fp128_felem_copy ->
                   spec_of_felem_copy
                     (field_representation:=field_representation_raw q)
                     functions)
      As fp128_felem_copy_correct.
    Proof. Time derive_bedrock2_func felem_copy_op. Qed.

    Derive fp128_from_bytes
      SuchThat (forall functions,
                   functions_contain functions fp128_from_bytes ->
                   spec_of_from_bytes
                     (field_representation:=field_representation_raw q)
                     functions)
      As fp128_from_bytes_correct.
    Proof. Time derive_bedrock2_func from_bytes_op. Qed.

    Derive fp128_to_bytes
      SuchThat (forall functions,
                   functions_contain functions fp128_to_bytes ->
                   spec_of_to_bytes
                     (field_representation:=field_representation_raw q)
                     functions)
      As fp128_to_bytes_correct.
    Proof. Time derive_bedrock2_func to_bytes_op. Qed.

    Derive fp128_opp
      SuchThat (forall functions,
                   functions_contain functions fp128_opp ->
                   spec_of_UnOp un_opp
                     (field_representation:=field_representation q)
                     functions)
      As fp128_opp_correct.
    Proof. Time derive_bedrock2_func opp_op. Qed.

    Derive fp128_mul
      SuchThat (forall functions,
                   functions_contain functions fp128_mul ->
                   spec_of_BinOp bin_mul
                     (field_representation:=field_representation q)
                     functions)
      As fp128_mul_correct.
    Proof. Time derive_bedrock2_func mul_op. Qed.

    Derive fp128_square
      SuchThat (forall functions,
                   functions_contain functions fp128_square ->
                   spec_of_UnOp un_square
                     (field_representation:=field_representation q)
                     functions)
      As fp128_square_correct.
    Proof. Time derive_bedrock2_func square_op. Qed.

    Derive fp128_add
      SuchThat (forall functions,
                   functions_contain functions fp128_add ->
                   spec_of_BinOp bin_add
                     (field_representation:=field_representation q)
                     functions)
      As fp128_add_correct.
    Proof. Time derive_bedrock2_func add_op. Qed.

    Derive fp128_sub
      SuchThat (forall functions,
                   functions_contain functions fp128_sub ->
                   spec_of_BinOp bin_sub
                     (field_representation:=field_representation q)
                     functions)
      As fp128_sub_correct.
    Proof. Time derive_bedrock2_func sub_op. Qed.

    Derive fp128_select_znz
      SuchThat (forall functions,
                   functions_contain functions fp128_select_znz ->
                   spec_of_selectznz
                     (field_representation:=field_representation q)
                     functions)
      As fp128_select_znz_correct.
    Proof. Time derive_bedrock2_func select_znz_op. Qed.

    Derive fp128_from_mont
      SuchThat (forall functions,
                   functions_contain functions fp128_from_mont ->
                   spec_of_UnOp un_from_mont
                     (field_representation:=field_representation q)
                     functions)
      As fp128_from_mont_correct.
    Proof. Time derive_bedrock2_func from_mont_op. Unshelve. 1,2: auto. Qed.

    Derive fp128_to_mont
      SuchThat (forall functions,
                   functions_contain functions fp128_to_mont ->
                   spec_of_UnOp un_to_mont
                     (field_representation:=field_representation q)
                     functions)
      As fp128_to_mont_correct.
    Proof. Time derive_bedrock2_func to_mont_op. Unshelve. 1,2: auto. Qed.

    #[export] Instance fp128_ok : FieldRepresentation_ok(field_representation:=field_representation q).
    Proof.
      apply Crypto.Bedrock.Field.Synthesis.New.Signature.field_representation_ok.
      auto.
    Qed.
  End Ops.
  Section NTT.
    Definition zeta: F := F.of_Z _ 145091266659756586618791329697897684742.
    Definition n: nat := 20.
    Definition m: nat := 65.

    Fixpoint fast_pow2 (x: F) (n: nat): F :=
      match n with
      | O => x
      | S n' => let a := (fast_pow2 x n') in F.mul a a
      end.

    Lemma fast_pow2_spec:
      forall x k,
        F.pow x (N.of_nat (Nat.pow 2 k)) = fast_pow2 x k.
    Proof.
      induction k.
      - rewrite F.pow_1_r. reflexivity.
      - rewrite PeanoNat.Nat.pow_succ_r', Nnat.Nat2N.inj_mul.
        assert (N.of_nat 2 * _ = N.of_nat (2 ^ k) + N.of_nat (2 ^ k))%N as -> by Lia.lia.
        rewrite F.pow_add_r, IHk. reflexivity.
    Qed.

    (* Sanity check ζ^(2^m) = -1 *)
    Lemma fp128_zeta_m_ok:
      F.pow zeta (N.of_nat (Nat.pow 2 m)) = F.of_Z _ (-1).
    Proof.
      rewrite fast_pow2_spec. apply F.eq_to_Z_iff. rewrite F.to_Z_of_Z.
      native_compute. reflexivity.
    Qed.

    Definition prio3_ntt := @br2_ntt 64 _ (Naive.word _) _ field_parameters (field_representation q) n m.

    Definition prio3_funcs :=
      [ ("prio3_ntt", prio3_ntt)
      ; (fp128_add)
      ; (fp128_sub)
      ; (fp128_mul)
      ].

    Lemma prio3_ntt_ok:
      @spec_of_ntt _ _ _ _ _ _ "prio3_ntt" field_parameters (field_representation q) n m nil (map.of_list prio3_funcs).
    Proof.
      eapply (br2_ntt_ok nil).
      - assert (felem_size_in_words = 2%nat) as -> by reflexivity. Lia.lia.
      - unfold felem_size_in_bytes.
        assert (felem_size_in_words = 2%nat) as -> by reflexivity.
        assert (Memory.bytes_per_word 64 = 8%Z) as -> by reflexivity.
        assert (Z.of_nat 2 * 8 = 2^4)%Z as -> by reflexivity.
        rewrite Nat2Z.inj_pow, <- Z.pow_add_r by Lia.lia.
        apply Z.pow_lt_mono_r; unfold n; Lia.lia.
      - reflexivity.
      - apply fp128_mul_correct. reflexivity.
      - apply fp128_sub_correct. reflexivity.
      - apply fp128_add_correct. reflexivity.
        Unshelve. reflexivity.
    Qed.

    Eval compute in ToCString.c_module prio3_funcs.
  End NTT.
End Field128.





