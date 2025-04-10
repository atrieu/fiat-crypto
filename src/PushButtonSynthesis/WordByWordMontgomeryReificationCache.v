(** * Push-Button Synthesis of Word-By-Word Montgomery: Reification Cache *)
From Coq Require Import ZArith.
From Coq Require Import Derive.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Freeze.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.API.
Require Import Crypto.PushButtonSynthesis.ReificationCache.
Local Open Scope Z_scope.

Import
  Language.Wf.Compilers
  Language.Compilers
  Language.API.Compilers.
Import Compilers.API.

Import Associational Positional.

Local Set Keyed Unification. (* needed for making [autorewrite] fast, c.f. COQBUG(https://github.com/coq/coq/issues/9283) *)

Module Export WordByWordMontgomery.
  Import WordByWordMontgomery.WordByWordMontgomery.

  Definition zeromod bitwidth n m m' := encodemod bitwidth n m m' 0.
  Definition onemod bitwidth n m m' := encodemod bitwidth n m m' 1.
  Definition evalmod bitwidth n := @eval bitwidth n.
  Definition bytes_evalmod s := @eval 8 (bytes_n s).

  (* we would do something faster, but it generally breaks extraction COQBUG(https://github.com/coq/coq/issues/7954) *)
  Local Ltac precache_reify_faster _ :=
    split;
    [ let marker := fresh "marker" in
      pose I as marker;
      intros;
      let LHS := lazymatch goal with |- ?LHS = _ => LHS end in
      let reified_op_gen := lazymatch LHS with context[expr.Interp _ ?reified_op_gen] => reified_op_gen end in
      subst reified_op_gen;
      etransitivity;
      [
      | let opmod := match goal with |- _ = ?RHS => head RHS end in
        cbv [opmod]; solve [ eauto with reify_cache_gen nocore ] ];
      repeat lazymatch goal with
             | [ H : _ |- _ ] => tryif constr_eq H marker then fail else revert H
             end;
      clear marker
    | ].
  Local Ltac cache_reify_faster_2arg _ :=
    precache_reify_faster ();
    [ lazymatch goal with
      | [ |- forall bw n m m' v, ?interp ?ev bw n m m' v = ?interp' ?reified_mul_gen bw n m m' (@?A bw n m m' v) (@?B bw n m m' v) ]
        => let rv := constr:(fun F bw n m m' v => (F bw n m m' (A bw n m m' v) (B bw n m m' v)):list Z) in
           intros;
           instantiate (1:=ltac:(let r := Reify rv in
                                 refine (r @ reified_mul_gen)%Expr))
      end;
      reflexivity
    | prove_Wf () ].
  Local Ltac cache_reify_faster_1arg _ :=
    precache_reify_faster ();
    [ lazymatch goal with
      | [ |- forall bw n m m', ?interp ?ev bw n m m' = ?interp' ?reified_op_gen bw n m m' (@?A bw n m m') ]
        => let rv := constr:(fun F bw n m m' => (F bw n m m' (A bw n m m')):list Z) in
           intros;
           instantiate (1:=ltac:(let r := Reify rv in
                                 refine (r @ reified_op_gen)%Expr))
      end;
      reflexivity
    | prove_Wf () ].
  (**
<<
#!/usr/bin/env python

indent = '  '

print((indent + '(' + r'''**
<<
%s
>>
*''' + ')\n') % open(__file__, 'r').read())

for i in ('mul', 'add', 'sub', 'opp', 'to_bytes', 'from_bytes', 'nonzero', 'eval', 'bytes_eval'):
    print((fr'''{indent}Derive reified_{i}_gen
       SuchThat (is_reification_of reified_{i}_gen {i}mod)
       As reified_{i}_gen_correct.
Proof. Time cache_reify (). Time Qed.
Local Definition reified_{i}_gen_correct_proj1 := proj1 reified_{i}_gen_correct.
Local Definition reified_{i}_gen_correct_proj2 := proj2 reified_{i}_gen_correct.
#[global]
Hint Extern 1 (_ = _) => apply_cached_reification {i}mod reified_{i}_gen_correct_proj1 : reify_cache_gen.
#[global]
Hint Immediate reified_{i}_gen_correct_proj2 : wf_gen_cache.
#[global]
Hint Rewrite reified_{i}_gen_correct_proj1 : interp_gen_cache.
Local Opaque reified_{i}_gen. (* needed for making [autorewrite] not take a very long time *)''').replace('\n', f'\n{indent}') + '\n')

for i in ('square', 'encode', 'from_montgomery', 'to_montgomery'):
    print((fr'''{indent}Derive reified_{i}_gen
       SuchThat (is_reification_of reified_{i}_gen {i}mod)
       As reified_{i}_gen_correct.
Proof.
  Time cache_reify ().
  (* we would do something faster, but it breaks extraction COQBUG(https://github.com/coq/coq/issues/7954) *)
  (* Time cache_reify_faster_2arg (). *)
Time Qed.
Local Definition reified_{i}_gen_correct_proj1 := proj1 reified_{i}_gen_correct.
Local Definition reified_{i}_gen_correct_proj2 := proj2 reified_{i}_gen_correct.
#[global]
Hint Extern 1 (_ = _) => apply_cached_reification {i}mod reified_{i}_gen_correct_proj1 : reify_cache_gen.
#[global]
Hint Immediate reified_{i}_gen_correct_proj2 : wf_gen_cache.
#[global]
Hint Rewrite reified_{i}_gen_correct_proj1 : interp_gen_cache.
Local Opaque reified_{i}_gen. (* needed for making [autorewrite] not take a very long time *)''').replace('\n', f'\n{indent}') + '\n')


for i in ('zero', 'one'):
    print((fr'''{indent}Derive reified_{i}_gen
       SuchThat (is_reification_of reified_{i}_gen {i}mod)
       As reified_{i}_gen_correct.
Proof.
  (* Time cache_reify (). *)
  (* we do something faster *)
  Time cache_reify_faster_1arg ().
Time Qed.
Local Definition reified_{i}_gen_correct_proj1 := proj1 reified_{i}_gen_correct.
Local Definition reified_{i}_gen_correct_proj2 := proj2 reified_{i}_gen_correct.
#[global]
Hint Extern 1 (_ = _) => apply_cached_reification {i}mod reified_{i}_gen_correct_proj1 : reify_cache_gen.
#[global]
Hint Immediate reified_{i}_gen_correct_proj2 : wf_gen_cache.
#[global]
Hint Rewrite reified_{i}_gen_correct_proj1 : interp_gen_cache.
Local Opaque reified_{i}_gen. (* needed for making [autorewrite] not take a very long time *)''').replace('\n', f'\n{indent}') + '\n')

>>
*)

  Derive reified_mul_gen
         SuchThat (is_reification_of reified_mul_gen mulmod)
         As reified_mul_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_mul_gen_correct_proj1 := proj1 reified_mul_gen_correct.
  Local Definition reified_mul_gen_correct_proj2 := proj2 reified_mul_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification mulmod reified_mul_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_mul_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_mul_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_mul_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_add_gen
         SuchThat (is_reification_of reified_add_gen addmod)
         As reified_add_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_add_gen_correct_proj1 := proj1 reified_add_gen_correct.
  Local Definition reified_add_gen_correct_proj2 := proj2 reified_add_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification addmod reified_add_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_add_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_add_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_add_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_sub_gen
         SuchThat (is_reification_of reified_sub_gen submod)
         As reified_sub_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_sub_gen_correct_proj1 := proj1 reified_sub_gen_correct.
  Local Definition reified_sub_gen_correct_proj2 := proj2 reified_sub_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification submod reified_sub_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_sub_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_sub_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_sub_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_opp_gen
         SuchThat (is_reification_of reified_opp_gen oppmod)
         As reified_opp_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_opp_gen_correct_proj1 := proj1 reified_opp_gen_correct.
  Local Definition reified_opp_gen_correct_proj2 := proj2 reified_opp_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification oppmod reified_opp_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_opp_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_opp_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_opp_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_to_bytes_gen
         SuchThat (is_reification_of reified_to_bytes_gen to_bytesmod)
         As reified_to_bytes_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_to_bytes_gen_correct_proj1 := proj1 reified_to_bytes_gen_correct.
  Local Definition reified_to_bytes_gen_correct_proj2 := proj2 reified_to_bytes_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification to_bytesmod reified_to_bytes_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_to_bytes_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_to_bytes_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_to_bytes_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_from_bytes_gen
         SuchThat (is_reification_of reified_from_bytes_gen from_bytesmod)
         As reified_from_bytes_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_from_bytes_gen_correct_proj1 := proj1 reified_from_bytes_gen_correct.
  Local Definition reified_from_bytes_gen_correct_proj2 := proj2 reified_from_bytes_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification from_bytesmod reified_from_bytes_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_from_bytes_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_from_bytes_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_from_bytes_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_nonzero_gen
         SuchThat (is_reification_of reified_nonzero_gen nonzeromod)
         As reified_nonzero_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_nonzero_gen_correct_proj1 := proj1 reified_nonzero_gen_correct.
  Local Definition reified_nonzero_gen_correct_proj2 := proj2 reified_nonzero_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification nonzeromod reified_nonzero_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_nonzero_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_nonzero_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_nonzero_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_eval_gen
         SuchThat (is_reification_of reified_eval_gen evalmod)
         As reified_eval_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_eval_gen_correct_proj1 := proj1 reified_eval_gen_correct.
  Local Definition reified_eval_gen_correct_proj2 := proj2 reified_eval_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification evalmod reified_eval_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_eval_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_eval_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_eval_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_bytes_eval_gen
         SuchThat (is_reification_of reified_bytes_eval_gen bytes_evalmod)
         As reified_bytes_eval_gen_correct.
  Proof. Time cache_reify (). Time Qed.
  Local Definition reified_bytes_eval_gen_correct_proj1 := proj1 reified_bytes_eval_gen_correct.
  Local Definition reified_bytes_eval_gen_correct_proj2 := proj2 reified_bytes_eval_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification bytes_evalmod reified_bytes_eval_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_bytes_eval_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_bytes_eval_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_bytes_eval_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_square_gen
         SuchThat (is_reification_of reified_square_gen squaremod)
         As reified_square_gen_correct.
  Proof.
    Time cache_reify ().
    (* we would do something faster, but it breaks extraction COQBUG(https://github.com/coq/coq/issues/7954) *)
    (* Time cache_reify_faster_2arg (). *)
  Time Qed.
  Local Definition reified_square_gen_correct_proj1 := proj1 reified_square_gen_correct.
  Local Definition reified_square_gen_correct_proj2 := proj2 reified_square_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification squaremod reified_square_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_square_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_square_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_square_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_encode_gen
         SuchThat (is_reification_of reified_encode_gen encodemod)
         As reified_encode_gen_correct.
  Proof.
    Time cache_reify ().
    (* we would do something faster, but it breaks extraction COQBUG(https://github.com/coq/coq/issues/7954) *)
    (* Time cache_reify_faster_2arg (). *)
  Time Qed.
  Local Definition reified_encode_gen_correct_proj1 := proj1 reified_encode_gen_correct.
  Local Definition reified_encode_gen_correct_proj2 := proj2 reified_encode_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification encodemod reified_encode_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_encode_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_encode_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_encode_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_from_montgomery_gen
         SuchThat (is_reification_of reified_from_montgomery_gen from_montgomerymod)
         As reified_from_montgomery_gen_correct.
  Proof.
    Time cache_reify ().
    (* we would do something faster, but it breaks extraction COQBUG(https://github.com/coq/coq/issues/7954) *)
    (* Time cache_reify_faster_2arg (). *)
  Time Qed.
  Local Definition reified_from_montgomery_gen_correct_proj1 := proj1 reified_from_montgomery_gen_correct.
  Local Definition reified_from_montgomery_gen_correct_proj2 := proj2 reified_from_montgomery_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification from_montgomerymod reified_from_montgomery_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_from_montgomery_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_from_montgomery_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_from_montgomery_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_to_montgomery_gen
         SuchThat (is_reification_of reified_to_montgomery_gen to_montgomerymod)
         As reified_to_montgomery_gen_correct.
  Proof.
    Time cache_reify ().
    (* we would do something faster, but it breaks extraction COQBUG(https://github.com/coq/coq/issues/7954) *)
    (* Time cache_reify_faster_2arg (). *)
  Time Qed.
  Local Definition reified_to_montgomery_gen_correct_proj1 := proj1 reified_to_montgomery_gen_correct.
  Local Definition reified_to_montgomery_gen_correct_proj2 := proj2 reified_to_montgomery_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification to_montgomerymod reified_to_montgomery_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_to_montgomery_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_to_montgomery_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_to_montgomery_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_zero_gen
         SuchThat (is_reification_of reified_zero_gen zeromod)
         As reified_zero_gen_correct.
  Proof.
    (* Time cache_reify (). *)
    (* we do something faster *)
    Time cache_reify_faster_1arg ().
  Time Qed.
  Local Definition reified_zero_gen_correct_proj1 := proj1 reified_zero_gen_correct.
  Local Definition reified_zero_gen_correct_proj2 := proj2 reified_zero_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification zeromod reified_zero_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_zero_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_zero_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_zero_gen. (* needed for making [autorewrite] not take a very long time *)

  Derive reified_one_gen
         SuchThat (is_reification_of reified_one_gen onemod)
         As reified_one_gen_correct.
  Proof.
    (* Time cache_reify (). *)
    (* we do something faster *)
    Time cache_reify_faster_1arg ().
  Time Qed.
  Local Definition reified_one_gen_correct_proj1 := proj1 reified_one_gen_correct.
  Local Definition reified_one_gen_correct_proj2 := proj2 reified_one_gen_correct.
  #[global]
  Hint Extern 1 (_ = _) => apply_cached_reification onemod reified_one_gen_correct_proj1 : reify_cache_gen.
  #[global]
  Hint Immediate reified_one_gen_correct_proj2 : wf_gen_cache.
  #[global]
  Hint Rewrite reified_one_gen_correct_proj1 : interp_gen_cache.
  Local Opaque reified_one_gen. (* needed for making [autorewrite] not take a very long time *)
End WordByWordMontgomery.
