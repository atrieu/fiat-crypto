Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.NTT.GallinaNTT.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.NTT.Bignums.

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
  Context (zeta: F) (c:F) (zetas: list F).

  Hypothesis c_ok: c = F.inv (F.pow (1 + 1)%F (N.of_nat (Nat.min m n))).

  Notation NTT_gallina := (@ntt_loop q zetas (Nat.min m n) n).
  Notation NTT_inverse_gallina := (@inverse_ntt_loop q zetas (Nat.min m n) n).

  Section FitsInOneWord.
    (* When a field element fits inside one machine word *)

    (* Assume we have a partial word evaluation function, returns none if input is invalid *)
    Context {feval: word -> option F}.
    Local Coercion F.to_Z: F >-> Z.
    Context {word_of_F : F -> word}.

    (* Converting a field element to a word, and back is correct *)
    Hypothesis feval_ok: forall x, feval (word_of_F x) = Some x.

    (* The field operations we need *)
    Context {add sub mul: String.string}.

    Hypothesis n_lt_width: (n < Z.to_nat width)%nat.
    Hypothesis zetas_length_ok: length zetas = Nat.pow 2 m.

    (* This is only needed because we need 2^(width/8) * 2^m ≤ 2^width to use InlineTables... Not a problem in practice *)
    Hypothesis mp3_le_with: (m + 3 <= Z.to_nat width)%nat.

    Definition spec_of_binop {name: String.string} (model: F -> F -> F): spec_of name :=
      fnspec! name (x y: word) / (a b: F) ~> (res: word),
        { requires tr mem :=
            feval x = Some a /\ feval y = Some b;
          ensures tr' mem' :=
            tr'= tr /\ mem' = mem /\ feval res = Some (model a b)
        }.

    Instance spec_of_add: spec_of add :=
      spec_of_binop F.add.
    Instance spec_of_sub: spec_of sub :=
      spec_of_binop F.sub.
    Instance spec_of_mul: spec_of mul :=
      spec_of_binop F.mul.

    Instance spec_of_ntt: spec_of ntt :=
      fnspec! ntt (p_ptr: word) / (p: list F) R,
        { requires tr mem :=
            exists p',
              Forall2 (fun x y => feval y = Some x) p p' /\
                mem =* (Bignums 1 (Nat.pow 2 n) p_ptr (List.chunk 1 p')) * R;
          ensures tr' mem' :=
            tr' = tr /\
              exists p',
                Forall2 (fun x y => feval y = Some x) (NTT_gallina p) p' /\
                  mem' =* (Bignums 1 (Nat.pow 2 n) p_ptr (List.chunk 1 p')) * R }.

    Instance spec_of_ntt_inverse: spec_of ntt_inverse :=
      fnspec! ntt_inverse (p_ptr: word) / (p: list F) R,
        { requires tr mem :=
            exists p',
              Forall2 (fun x y => feval y = Some x) p p' /\
                mem =* (Bignums 1 (Nat.pow 2 n) p_ptr (List.chunk 1 p')) * R;
          ensures tr' mem' :=
            tr' = tr /\
              exists p',
                Forall2 (fun x y => feval y = Some x) (NTT_inverse_gallina p) p' /\
                  mem' =* (Bignums 1 (Nat.pow 2 n) p_ptr (List.chunk 1 p')) * R }.

    Definition br2_ntt :=
      func! (p) {
          l = coq:(0);
          len = coq:(Z.pow 2 (Z.of_nat n));
          while (coq:(Z.pow 2 (Z.of_nat (n - Nat.min m n))) < len) {
              old_len = len;
              len = len >> coq:(1);
              start = coq:(0);
              while (start < coq:(Z.pow 2 (Z.of_nat n))) {
                  l = l + coq:(1);
                  z = coq:(expr.inlinetable access_size.word (to_byte_table (List.map word_of_F zetas)) (expr.op bopname.mul (expr.literal (width / 8)) (expr.var "l")));
                  j = start;
                  while (j < (start + len)) {
                      x = load(coq:(offset (expr.var "p") bedrock_expr:(j + len) (expr.literal (Z.of_nat (@Memory.bytes_per width access_size.word)))));
                      unpack! tmp = $mul(z, x);
                      y = load(coq:(offset (expr.var "p") bedrock_expr:(j) (expr.literal (Z.of_nat (@Memory.bytes_per width access_size.word)))));
                      unpack! x = $sub(y, tmp);
                      store(coq:(offset (expr.var "p") bedrock_expr:(j + len) (expr.literal (Z.of_nat (@Memory.bytes_per width access_size.word)))), x);
                      unpack! x = $add(y, tmp);
                      store(coq:(offset (expr.var "p") bedrock_expr:(j) (expr.literal (Z.of_nat (@Memory.bytes_per width access_size.word)))), x);
                      j = j + coq:(1)
                    };
                  start = start + old_len
                }
            }
        }.

    Definition br2_ntt_inverse :=
      func! (p) {
          l = coq:(Z.of_nat (Nat.pow 2 (Nat.min m n)));
          len = coq:(Z.of_nat (Nat.pow 2 (n - (Nat.min m n))));
          while (len < coq:(Z.of_nat (Nat.pow 2 n))) {
              start = coq:(0);
              old_len = len;
              len = len << coq:(1);
              while (start < coq:(Z.of_nat (Nat.pow 2 n))) {
                  l = l - coq:(1);
                  z = coq:(expr.inlinetable access_size.word (to_byte_table (List.map word_of_F zetas)) (expr.op bopname.mul (expr.literal (width / 8)) (expr.var "l")));
                  j = start;
                  while (j < start + old_len) {
                      tmp = load(coq:(offset (expr.var "p") bedrock_expr:(j) (expr.literal (Z.of_nat (@Memory.bytes_per width access_size.word)))));
                      x = load(coq:(offset (expr.var "p") bedrock_expr:(j + old_len) (expr.literal (Z.of_nat (@Memory.bytes_per width access_size.word)))));
                      unpack! y = $add(tmp, x);
                      store(coq:(offset (expr.var "p") bedrock_expr:(j) (expr.literal (Z.of_nat (@Memory.bytes_per width access_size.word)))), y);
                      unpack! x = $sub(x, tmp);
                      unpack! y = $mul(z, x);
                      store(coq:(offset (expr.var "p") bedrock_expr:(j + old_len) (expr.literal (Z.of_nat (@Memory.bytes_per width access_size.word)))), y);
                      j = j + coq:(1)
                    };
                  start = start + len
                }
            };
          j = coq:(0);
          while (j < coq:(Z.of_nat (Nat.pow 2 n))) {
              x = load(coq:(offset (expr.var "p") bedrock_expr:(j) (expr.literal (Z.of_nat (@Memory.bytes_per width access_size.word)))));
              unpack! x = $mul($(word.unsigned (word_of_F c)), x);
              store(coq:(offset (expr.var "p") bedrock_expr:(j) (expr.literal (Z.of_nat (@Memory.bytes_per width access_size.word)))), x);
              j = j + coq:(1)
            }
        }.

    Lemma Forall2_set_nth {A B: Type}:
      forall (R: A -> B -> Prop) (x: A) (y: B) (i: nat) (xs: list A) (ys: list B),
        Forall2 R xs ys ->
        R x y ->
        Forall2 R (set_nth i x xs) (set_nth i y ys).
    Proof. intros; apply Forall2_update_nth; auto. Qed.

    Lemma br2_ntt_ok:
      program_logic_goal_for br2_ntt
        (forall functions : map.rep,
            map.get functions ntt = Some br2_ntt ->
            spec_of_mul functions ->
            spec_of_sub functions -> spec_of_add functions -> spec_of_ntt functions).
    Proof.
      Local Opaque Memory.bytes_per to_byte_table Z.pow Z.of_nat List.map Z.div Z.sub Z.add Nat.sub Nat.min F.F word.unsigned.
      assert (len_chunk1: forall A (l: list A), length (List.chunk 1 l) = length l).
      { intros; rewrite List.length_chunk by congruence.
        rewrite <- (PeanoNat.Nat.mul_1_r (length l)), List.Nat.div_up_exact; Lia.lia. }
      repeat straightline.
      unfold NTT_gallina.
      apply wp_while.
      (* First loop invariant *)
      pose (loop_inv1:= fun (fuel: nat) (tr': Semantics.trace) (mem': mem) (loc: locals) =>
                          (fuel <= Nat.min m n)%nat /\
                            let i := (Nat.min m n - fuel)%nat in
                            tr' = tr /\
                              exists p' px,
                                polynomial_layer_decomposition_loop zetas 0 i (0%nat, (2 ^ n)%nat, p) = (Nat.pow 2 i - 1, Nat.pow 2 (n - i), px)%nat /\
                                  Forall2 (fun x y => feval y = Some x) px p' /\
                                  map.get loc "p" = Some p_ptr /\
                                  map.get loc "l" = Some (word.of_Z (Z.of_nat ((Nat.pow 2 i) - 1))) /\
                                  map.get loc "len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - i)))) /\
                                  ((Bignums 1 (Nat.pow 2 n) p_ptr (List.chunk 1 p')) * R)%sep mem').
      exists nat, lt, loop_inv1.
      split; [apply lt_wf|].
      split. (* Invariant holds at beginning *)
      { exists (Nat.min m n). repeat split; [Lia.lia|..].
        exists x, p. repeat split.
        - rewrite PeanoNat.Nat.sub_diag. cbn.
          rewrite PeanoNat.Nat.sub_0_r, PeanoNat.Nat.sub_diag. reflexivity.
        - assumption.
        (* These map goals could be automated *)
        - unfold l1, l0, l. do 2 (rewrite map.get_put_diff by congruence).
          apply map.get_put_same.
        - unfold l1, l0, l. rewrite map.get_put_diff by congruence.
          rewrite map.get_put_same. rewrite PeanoNat.Nat.sub_diag.
          reflexivity.
        - unfold l1. rewrite map.get_put_same. unfold len.
          rewrite PeanoNat.Nat.sub_diag, PeanoNat.Nat.sub_0_r.
          rewrite Nat2Z.inj_pow. reflexivity.
        - assumption. }
      intros fuel tr' mem' loc' Hinv.
      destruct Hinv as (Hfuel & -> & p' & px' & HF1 & Heq & Hp & Hm & Hlen & Hseps).
      eexists. split.
      { repeat straightline. eexists; split; eauto. }
      split.
      { (* Invariant preservation *)
        intro Hb. rewrite Nat2Z.inj_pow in Hb.
        rewrite <- Core.word.morph_ltu in Hb.
        2-3: split; try Lia.lia.
        2-3: apply Zpow_facts.Zpower_lt_monotone; Lia.lia.
        generalize (Zlt_cases (2 ^ Z.of_nat (n - Nat.min m n)) (Z.of_nat 2 ^ Z.of_nat (n - (Nat.min m n - fuel)))).
        destruct (_ <? _); intros Hlt1; [|rewrite word.unsigned_of_Z_0 in Hb; congruence].
        assert (Hfnz: (fuel <> 0)%nat) by (intro X; subst fuel; rewrite PeanoNat.Nat.sub_0_r in Hlt1; Lia.lia).
        repeat straightline. eexists. split; [eexists; split; eauto|].
        repeat straightline. eexists. split; [eexists; unfold l0; rewrite map.get_put_diff by congruence; split; eauto|]; repeat straightline.
        assert (Hp1: map.get l2 "p" = Some p_ptr).
        { unfold l2, l1, l0; repeat (rewrite map.get_put_diff by (clear; congruence)). auto. }
        assert (Hl1: map.get l2 "l" = Some (word.of_Z (Z.of_nat ((Nat.pow 2 (Nat.min m n - fuel)) - 1)))).
        { unfold l2, l1, l0. repeat (rewrite map.get_put_diff by (clear; congruence)). auto. }
        assert (Hlen1: map.get l2 "len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - (Nat.min m n - (fuel - 1))))))).
        { unfold l2, l1, l0; repeat (rewrite map.get_put_diff by (clear; congruence)).
          rewrite map.get_put_same, <- Core.word.morph_shiftr.
          2: Lia.lia.
          2: split; [|rewrite Nat2Z.inj_pow; apply Zpow_facts.Zpower_lt_monotone]; Lia.lia.
          rewrite Z.shiftr_div_pow2 by Lia.lia.
          replace (2 ^ 1) with (Z.of_nat (Nat.pow 2 1)) by reflexivity.
          rewrite <- Nat2Z.inj_div, <- PeanoNat.Nat.pow_sub_r by Lia.lia.
          f_equal. f_equal. f_equal. f_equal.
          clear -Hfuel Hfnz. Lia.lia. }
        assert (Hold_len1: map.get l2 "old_len" = Some _) by (unfold l2, l1, l0; repeat (rewrite map.get_put_diff by (clear; congruence)); apply map.get_put_same).
        apply wp_while.
        (* second loop *)
        pose (loop_inv2:= fun (fuel2: nat) (tr': Semantics.trace) (mem': mem) (loc: locals) =>
                            (fuel2 <= Nat.pow 2 (Nat.min m n - fuel))%nat /\
                              let i := ((Nat.pow 2 (Nat.min m n - fuel) - fuel2))%nat in
                              tr' = tr /\
                                exists p'' px'',
                                  polynomial_list_loop zetas i (Nat.pow 2 (n - (Nat.min m n - fuel))) (Nat.pow 2 (n - (Nat.min m n - (fuel - 1)))) ((Nat.pow 2 (Nat.min m n - fuel) - 1), 0, px')%nat = ((Nat.pow 2 (Nat.min m n - fuel) - 1) + i, i * (Nat.pow 2 (n - (Nat.min m n - fuel))), px'')%nat /\
                                    Forall2 (fun x y => feval y = Some x) px'' p'' /\
                                    map.get loc "p" = Some p_ptr /\
                                    map.get loc "l" = Some (word.of_Z (Z.of_nat ((Nat.pow 2 (Nat.min m n - fuel)) - 1 + i))) /\
                                    map.get loc "len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - (Nat.min m n - (fuel - 1)))))) /\
                                    map.get loc "old_len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - (Nat.min m n - fuel))))) /\
                                    map.get loc "start" = Some (word.of_Z (Z.of_nat (i * (Nat.pow 2 (n - (Nat.min m n - fuel)))))) /\
                                    ((Bignums 1 (Nat.pow 2 n) p_ptr (List.chunk 1 p'')) * R)%sep mem').
        exists nat, lt, loop_inv2. split; [apply lt_wf|]. split.
        { (* invariant holds at beginning *)
          exists (2 ^ (Nat.min m n - fuel))%nat. repeat split; [Lia.lia|].
          exists p', px'. repeat split; auto.
          - rewrite PeanoNat.Nat.sub_diag. cbn.
            rewrite PeanoNat.Nat.add_0_r. reflexivity.
          - rewrite Hl1, PeanoNat.Nat.sub_diag, PeanoNat.Nat.add_0_r. reflexivity.
          - rewrite PeanoNat.Nat.sub_diag, PeanoNat.Nat.mul_0_l.
            apply map.get_put_same. }
        intros fuel2 tr2 mem2 l3 Hinv2.
        destruct Hinv2 as (Hfuel2 & -> & p2 & px2 & Heq2 & HF2 & Hp2 & Hm2 & Hlen2 & Hold_len2 & Hstart2 & Hseps2).
        eexists; split.
        { repeat straightline. eexists; split; [eassumption|].
          repeat straightline. }
        rewrite <- Core.word.morph_ltu.
        2-3: split; try Lia.lia.
        4: apply Zpow_facts.Zpower_lt_monotone; Lia.lia.
        2: apply Nat2Z.is_nonneg.
        2:{ rewrite Nat.mul_sub_distr_r, <- PeanoNat.Nat.pow_add_r.
            assert (Nat.min m n - fuel + _ = n)%nat as -> by (clear -Hfnz Hfuel; Lia.lia).
            assert (2 ^ width = Z.of_nat (2 ^ (Z.to_nat width))) as -> by (rewrite Nat2Z.inj_pow, Z2Nat.id by (clear -n_lt_width; Lia.lia); reflexivity).
            apply Nat2Z.inj_lt.
            eapply Nat.le_lt_trans; [|eapply PeanoNat.Nat.pow_lt_mono_r; try eassumption; Lia.lia].
            clear; Lia.lia. }
        split.
        { (* Invariant preservation *) intro Hcond.
          assert (fuel2 <> 0)%nat as Hfnz2.
          { destruct (Nat.eq_dec fuel2 0%nat) as [->|]; auto.
            elim Hcond. clear Hcond. rewrite PeanoNat.Nat.sub_0_r.
            rewrite <- Nat.pow_add_r.
            assert (_ - _ + _ = n)%nat as -> by (clear -Hfnz Hfuel; Lia.lia).
            rewrite Nat2Z.inj_pow, Z.ltb_irrefl, word.unsigned_of_Z_0. reflexivity. }
          repeat straightline.
          eexists. split.
          { repeat straightline. eexists; split; [eassumption|].
            repeat straightline. }
          rewrite <- word.ring_morph_add.
          repeat straightline. exists (word_of_F (nth_default 0%F zetas ((2 ^ (Nat.min m n - fuel) - 1 + 2 ^ (Nat.min m n - fuel) - fuel2) + 1)%nat)).
          split.
          { eexists; split.
            - apply map.get_put_same.
            - cbn. rewrite <- word.ring_morph_mul.
              unfold load.
              assert (Z.of_nat _ + 1 = Z.of_nat _ + Z.of_nat 1) as -> by reflexivity.
              rewrite <- Nat2Z.inj_add.
              erewrite load_from_word_table; auto.
              2:{ rewrite length_to_byte_table, length_map.
                  rewrite zetas_length_ok. assert (width / 8 = 4 \/ width / 8 = 8) as Hw.
                  { clear -BW.
                    destruct width_cases as [-> | ->]; [left|right]; reflexivity. }
                  rewrite Nat2Z.inj_mul, Z2Nat.id by (clear -Hw; destruct Hw; Lia.lia).
                  rewrite Nat2Z.inj_pow.
                  transitivity (2 ^ 3 * 2 ^ Z.of_nat m).
                  - apply Z.mul_le_mono_nonneg_r.
                    + apply Z.lt_le_incl, ZLib.Z.pow2_pos, Nat2Z.is_nonneg.
                    + clear -Hw. destruct Hw as [-> | ->]; Lia.lia.
                  - rewrite <- Z.pow_add_r by Lia.lia.
                    apply Z.pow_le_mono_r; clear -mp3_le_with; Lia.lia. }
              2:{ rewrite length_map, zetas_length_ok.
                  eapply (Nat.lt_le_trans _ (2 ^ (Nat.min m n - (fuel - 1)))%nat).
                  + assert (Nat.min m n - (fuel - 1) = S (Nat.min m n - fuel))%nat as -> by (clear -Hfuel Hfnz; Lia.lia).
                    rewrite Nat.pow_succ_r'. clear -Hfuel2 Hfnz2. Lia.lia.
                  + apply Nat.pow_le_mono; clear -mp3_le_with; Lia.lia. }
              eexists; split; [reflexivity|].
              rewrite map_nth, nth_default_eq.
              f_equal. f_equal. clear -Hfuel Hfuel2; Lia.lia. }
          repeat straightline. eexists. split.
          { repeat straightline. unfold l5, l4.
            repeat rewrite map.get_put_diff by congruence.
            rewrite Hstart2; eexists; split; reflexivity. }
          repeat straightline.
          apply wp_while.
          assert (Hj: map.get l6 "j" = Some _) by (apply map.get_put_same).
          assert (Hz: map.get l6 "z" = Some _) by (unfold l6; rewrite map.get_put_diff by congruence; apply map.get_put_same).
          assert (Hm3: map.get l6 "l" = Some _) by (unfold l6, l5; do 2 (rewrite map.get_put_diff by congruence); apply map.get_put_same).
          assert (Hstart3: map.get l6 "start" = Some _) by (unfold l6, l5, l4; repeat (rewrite map.get_put_diff by (clear; congruence)); eassumption).
          assert (Hold_len3: map.get l6 "old_len" = Some _) by (unfold l6, l5, l4; repeat (rewrite map.get_put_diff by (clear; congruence)); eassumption).
          assert (Hlen3: map.get l6 "len" = Some _) by (unfold l6, l5, l4; repeat (rewrite map.get_put_diff by (clear; congruence)); eassumption).
          assert (Hp3: map.get l6 "p" = Some _) by (unfold l6, l5, l4; repeat (rewrite map.get_put_diff by (clear; congruence)); eassumption).
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
                                     Forall2 (fun x y => feval y = Some x) px'' p'' /\
                                       map.get loc "p" = Some p_ptr /\
                                       map.get loc "l" = Some (word.of_Z (Z.of_nat (2 ^ (Nat.min m n - fuel) - 1 + (2 ^ (Nat.min m n - fuel) - fuel2)) + 1)) /\
                                       map.get loc "len" = Some (word.of_Z (Z.of_nat (2 ^ (n - (Nat.min m n - (fuel - 1)))))) /\
                                       map.get loc "old_len" = Some (word.of_Z (Z.of_nat (2 ^ (n - (Nat.min m n - fuel))))) /\
                                       map.get loc "start" = Some (word.of_Z (Z.of_nat ((2 ^ (Nat.min m n - fuel) - fuel2) * 2 ^ (n - (Nat.min m n - fuel))))) /\
                                       map.get loc "j" = Some (word.of_Z (Z.of_nat ((2 ^ (Nat.min m n - fuel) - fuel2) * 2 ^ (n - (Nat.min m n - fuel)) + i))) /\
                                       map.get loc "z" = Some (word_of_F (nth_default 0%F zetas (2 ^ (Nat.min m n - fuel) - 1 + 2 ^ (Nat.min m n - fuel) - fuel2 + 1)%nat)) /\
                                       ((Bignums 1 (Nat.pow 2 n) p_ptr (List.chunk 1 p'')) * R)%sep mem').
          exists nat, lt, loop_inv3. split; [apply lt_wf|].
          split.
          { (* Invariant holds at beginning *)
            exists (2 ^ (n - (Nat.min m n - (fuel - 1))))%nat. split; [reflexivity|].
            intros. split; [reflexivity|]. intros.
            assert (i = 0)%nat as -> by (clear; Lia.lia).
            exists p2. repeat split; auto.
            assert (px'' = px2) as ->; auto.
            rewrite Hj, PeanoNat.Nat.add_0_r. reflexivity. }
          intros fuel3 tr3 m3 loc3 Hinv3.
          destruct Hinv3 as (Hfuel3 & -> & p3 & HF3 & Hp4 & Hm4 & Hlen4 & Hold_len4 & Hstart4 & Hj4 & Hz4 & Hseps4).
          eexists; split.
          { repeat straightline.
            eexists; split; [eassumption|]. repeat straightline.
            eexists; split; [eassumption|]. repeat straightline.
            eexists; split; [eassumption|].
            rewrite <- word.ring_morph_add, <- Core.word.morph_ltu.
            3: rewrite <- Nat2Z.inj_add.
            2-3: split; try (apply Nat2Z.is_nonneg).
            2-3: assert (2 ^ width = Z.of_nat (2 ^ (Z.to_nat width))) as -> by (rewrite Nat2Z.inj_pow, Z2Nat.id by (clear -n_lt_width; Lia.lia); reflexivity).
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
          split; intro Hcond2.
          { (* Invariant preservation *)
            clear Hb. destruct (Nat.eq_dec fuel3 0) as [|Hfnz3]; [clear -Hcond2; congruence|clear Hcond2].
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
            pose proof (Bignums_length _ _ _ _ _ _ Hseps4) as Xlen.
            rewrite len_chunk1 in Xlen.
            repeat straightline.
            eexists; split.
            { repeat straightline.
              eexists; split; [eassumption|repeat straightline].
              eexists; split; [eassumption|repeat straightline].
              eexists; split; [eassumption|repeat straightline].
              set (j := ((2 ^ (Nat.min m n - fuel) - fuel2) * 2 ^ (n - (Nat.min m n - fuel)) + (2 ^ (n - (Nat.min m n - (fuel - 1))) - fuel3))%nat).
              set (len4 := (2 ^ (n - (Nat.min m n - (fuel - 1))))%nat).
              rewrite (Bignums1_load_of_sep R (word_of_F 0%F) (Nat.pow 2 n) p_ptr _ (j + len4)%nat p3); eauto.
              - clear -idx_ok Xlen. Lia.lia.
              - unfold v. rewrite <- MakeAccessSizes.bytes_per_word_eq.
                rewrite Z2Nat.id by (apply Z.lt_le_incl, Types.word_size_in_bytes_pos).
                rewrite <- word.ring_morph_add, <- Nat2Z.inj_add.
                rewrite <- word.ring_morph_mul, Z.mul_comm. reflexivity. }
            repeat straightline.
            eexists; split; repeat straightline.
            { unfold l7; rewrite map.get_put_diff by congruence.
              rewrite Hz4. eexists; split; [reflexivity|repeat straightline].
              rewrite map.get_put_same. eexists; split; [reflexivity|repeat straightline]. }
            straightline_call.
            { split; [apply feval_ok|].
              set (j := ((2 ^ (Nat.min m n - fuel) - fuel2) * 2 ^ (n - (Nat.min m n - fuel)) + (2 ^ (n - (Nat.min m n - (fuel - 1))) - fuel3))%nat).
              set (len4 := (2 ^ (n - (Nat.min m n - (fuel - 1))))%nat).
              apply (proj1 (@Forall.Forall2_forall_iff'' _ _ (fun x y => feval y = Some x) _ p3 0%F (word_of_F 0%F)) (conj HF3 (feval_ok _))). }
            repeat straightline. eexists; split; repeat straightline.
            { unfold l', l7. do 2 (rewrite map.get_put_diff by congruence).
              eexists; split; [eassumption|repeat straightline].
              do 2 (rewrite map.get_put_diff by congruence).
              eexists; split; [eassumption|repeat straightline].
              set (j := ((2 ^ (Nat.min m n - fuel) - fuel2) * 2 ^ (n - (Nat.min m n - fuel)) + (2 ^ (n - (Nat.min m n - (fuel - 1))) - fuel3))%nat).
              rewrite (Bignums1_load_of_sep R (word_of_F 0%F) (Nat.pow 2 n) p_ptr _ j p3); eauto.
              - clear -idx_ok Xlen. Lia.lia.
              - unfold v. rewrite <- MakeAccessSizes.bytes_per_word_eq.
                rewrite Z2Nat.id by (apply Z.lt_le_incl, Types.word_size_in_bytes_pos).
                rewrite <- word.ring_morph_mul, Z.mul_comm. reflexivity. }
            eexists; split; repeat straightline.
            { unfold l8. rewrite map.get_put_same.
              eexists; split; [reflexivity|repeat straightline].
              unfold l'. rewrite map.get_put_diff, map.get_put_same by congruence.
              eexists; split; [reflexivity|repeat straightline]. }
            straightline_call.
            { split; [|eassumption].
              set (j := ((2 ^ (Nat.min m n - fuel) - fuel2) * 2 ^ (n - (Nat.min m n - fuel)) + (2 ^ (n - (Nat.min m n - (fuel - 1))) - fuel3))%nat).
              apply (proj1 (@Forall.Forall2_forall_iff'' _ _ (fun x y => feval y = Some x) _ p3 0%F (word_of_F 0%F)) (conj HF3 (feval_ok _))). }
            repeat straightline.
            eexists; split; repeat straightline.
            { unfold l'0, l8, l', l7.
              repeat rewrite map.get_put_diff by congruence.
              eexists; split; [eassumption|repeat straightline].
              repeat rewrite map.get_put_diff by congruence.
              eexists; split; [eassumption|repeat straightline].
              repeat rewrite map.get_put_diff by congruence.
              eexists; split; [eassumption|repeat straightline]. }
            eexists; split; repeat straightline.
            { unfold l'0. rewrite map.get_put_same.
              eexists; split; reflexivity. }
            unfold store.
            set (px3 := (polynomial_decompose_loop ((2 ^ (Nat.min m n - fuel) - fuel2) * 2 ^ (n - (Nat.min m n - fuel))) (2 ^ (n - (Nat.min m n - (fuel - 1))) - fuel3) (nth_default 0%F zetas (2 ^ (Nat.min m n - fuel) - 1 + 2 ^ (Nat.min m n - fuel) - fuel2 + 1)) px2)).
            set (j := ((2 ^ (Nat.min m n - fuel) - fuel2) * 2 ^ (n - (Nat.min m n - fuel)) + (2 ^ (n - (Nat.min m n - (fuel - 1))) - fuel3))%nat).
            set (len4 := (2 ^ (n - (Nat.min m n - (fuel - 1))))%nat).
            eapply (Bignums1_store_of_sep R (Nat.pow 2 n) _ _ (j + len4)%nat); try eassumption.
            { clear -idx_ok Xlen; Lia.lia. }
            { rewrite <- MakeAccessSizes.bytes_per_word_eq.
              rewrite Z2Nat.id by (apply Z.lt_le_incl, Types.word_size_in_bytes_pos).
              rewrite <- word.ring_morph_add, <- Nat2Z.inj_add.
              rewrite <- word.ring_morph_mul, Z.mul_comm. reflexivity. }
            repeat straightline. eexists; split; repeat straightline.
            { unfold l'0, l8. rewrite map.get_put_diff by congruence.
              rewrite map.get_put_same. eexists; split; [reflexivity|repeat straightline].
              unfold l'. do 2 (rewrite map.get_put_diff by congruence).
              rewrite map.get_put_same. eexists; split; [reflexivity|repeat straightline]. }
            straightline_call.
            { split; [|eassumption].
              apply (proj1 (@Forall.Forall2_forall_iff'' _ _ (fun x y => feval y = Some x) _ p3 0%F (word_of_F 0%F)) (conj HF3 (feval_ok _))). }
            repeat straightline.
            eexists; split; repeat straightline.
            { unfold l'1, l'0, l8, l', l7.
              repeat (rewrite map.get_put_diff by (clear; congruence)).
              eexists; split; [eassumption|repeat straightline].
              repeat (rewrite map.get_put_diff by (clear; congruence)).
              eexists; split; [eassumption|repeat straightline]. }
            eexists; split; repeat straightline.
            { unfold l'1. rewrite map.get_put_same. eexists; split; reflexivity. }
            eapply (Bignums1_store_of_sep R (Nat.pow 2 n) _ _ j); try eassumption.
            { clear -idx_ok Xlen; rewrite length_set_nth; Lia.lia. }
            { rewrite <- MakeAccessSizes.bytes_per_word_eq.
              rewrite Z2Nat.id by (apply Z.lt_le_incl, Types.word_size_in_bytes_pos).
              rewrite <- word.ring_morph_mul, Z.mul_comm. reflexivity. }
            repeat straightline. eexists; split; repeat straightline.
            { unfold l'1, l'0, l8, l', l7.
              repeat (rewrite map.get_put_diff by (clear; congruence)).
              eexists; split; [eassumption|repeat straightline]. }
            exists (fuel3 - 1)%nat. split; [|clear -Hfnz3; Lia.lia].
            unfold loop_inv3.
            split; [clear -Hfuel3; Lia.lia|].
            split; [reflexivity|].
            exists (set_nth j x2 (set_nth (j + len4)%nat x1 p3)).
            unfold l9, l'1, l'0, l8, l', l7.
            repeat (rewrite map.get_put_diff by (clear; congruence)).
            repeat rewrite map.get_put_same.
            repeat split; try assumption.
            3: repeat (rewrite map.get_put_diff by (clear; congruence)); assumption.
            2:{ rewrite <- word.ring_morph_add. do 2 f_equal.
                clear -Hfnz3 Hfuel3 idx_ok. Lia.lia. }
            assert (2 ^ (n - (Nat.min m n - (fuel - 1))) - (fuel3 - 1) = S (2 ^ (n - (Nat.min m n - (fuel - 1))) - fuel3))%nat as -> by (clear -Hfnz3 Hfuel3 idx_ok; Lia.lia).
            unfold polynomial_decompose_loop'. rewrite seq_S, fold_left_app.
            assert (fold_left _ (seq _ _) _ = (polynomial_decompose_loop' (2 ^ (n - (Nat.min m n - (fuel - 1))) - fuel3)%nat ((2 ^ (Nat.min m n - fuel) - fuel2) * 2 ^ (n - (Nat.min m n - fuel))) (2 ^ (n - (Nat.min m n - (fuel - 1))))%nat (nth_default 0%F zetas (2 ^ (Nat.min m n - fuel) - 1 + 2 ^ (Nat.min m n - fuel) - fuel2 + 1)) px2))%nat as -> by reflexivity.
            cbn [fold_left]. do 2 (apply Forall2_set_nth; auto). }
          destruct (Nat.eq_dec fuel3 0) as [->|]; [clear Hcond2|clear -Hcond2; congruence].
          rewrite PeanoNat.Nat.sub_0_r in *.
          rewrite polynomial_decompose_loop_eq in HF3.
          repeat straightline.
          eexists; split; repeat straightline.
          { eexists; split; [eassumption|repeat straightline].
            eexists; split; [eassumption|repeat straightline]. }
          exists (fuel2 - 1)%nat. split; [|clear -Hfnz2; Lia.lia].
          unfold loop_inv2. split; [clear -Hfuel2; Lia.lia|].
          split; [reflexivity|].
          unfold l7. repeat (rewrite map.get_put_diff by (clear; congruence)).
          rewrite map.get_put_same. exists p3. eexists; repeat split; eauto.
          2:{ rewrite Hm4. do 2 f_equal.
              clear -Hfuel2 Hfnz2; Lia.lia. }
          2:{ rewrite <- word.ring_morph_add, <- Nat2Z.inj_add.
              do 2 f_equal. clear -Hfuel2 Hfnz2 Hfuel Hfnz; Lia.nia. }
          assert (2 ^ (Nat.min m n - fuel) - (fuel2 - 1) = S (2 ^ (Nat.min m n - fuel) - fuel2))%nat as -> by (clear -Hfuel2 Hfnz2; Lia.lia).
          unfold polynomial_list_loop. rewrite seq_S, fold_left_app.
          assert (fold_left _ (seq _ _) _ = polynomial_list_loop zetas (2 ^ (Nat.min m n - fuel) - fuel2) (2 ^ (n - (Nat.min m n - fuel))) (2 ^ (n - (Nat.min m n - (fuel - 1)))) ((2 ^ (Nat.min m n - fuel) - 1)%nat, 0%nat, px'))%nat as -> by reflexivity.
          rewrite Heq2. cbn [fold_left]. f_equal; f_equal; try (clear -Hfuel2 Hfnz2; Lia.lia).
          f_equal. clear -Hfuel2 Hfnz2; Lia.lia. }
        intro Hcond. generalize (Zlt_cases (Z.of_nat ((2 ^ (Nat.min m n - fuel) - fuel2) * 2 ^ (n - (Nat.min m n - fuel)))) (2 ^ Z.of_nat n)).
        destruct (_ <? _); intros Hcondd; [rewrite word.unsigned_of_Z_1 in Hcond; clear -Hcond; congruence|clear Hcond].
        assert (fuel2 = 0)%nat as ->.
        { destruct (Nat.eq_dec fuel2 0%nat); auto.
          replace (2 ^ Z.of_nat n) with (Z.of_nat (Nat.pow 2 n)) in Hcondd by (rewrite Nat2Z.inj_pow; reflexivity).
          apply Nat2Z.inj_ge in Hcondd.
          rewrite Nat.mul_sub_distr_r, <- PeanoNat.Nat.pow_add_r in Hcondd.
          replace (Nat.min m n - fuel + _)%nat with n in Hcondd by (clear -Hfnz Hfuel; Lia.lia).
          clear -Hcondd n0.
          generalize (NatUtil.pow_nonzero 2 (n - (Nat.min m n - fuel)) ltac:(Lia.lia)).
          generalize (NatUtil.pow_nonzero 2 n ltac:(Lia.lia)).
          Lia.lia. }
        exists (fuel - 1)%nat. split; [|clear -Hfnz; Lia.lia].
        unfold loop_inv1. split; [clear -Hfuel; Lia.lia|].
        split; [reflexivity|].
        exists p2, px2. rewrite PeanoNat.Nat.sub_0_r in *.
        repeat split; auto.
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
      rewrite <- Core.word.morph_ltu.
      2-3: split; try Lia.lia.
      3: rewrite Nat2Z.inj_pow.
      2-3: apply Zpow_facts.Zpower_lt_monotone; Lia.lia.
      intros Hb.
      generalize (Zlt_cases (2 ^ Z.of_nat (n - Nat.min m n)) (Z.of_nat (2 ^ (n - (Nat.min m n - fuel))))).
      destruct (_ <? _); intros; [rewrite word.unsigned_of_Z_1 in Hb; congruence|clear Hb].
      assert (fuel = 0)%nat as ->.
      { generalize (Zpow_facts.Zpower_le_monotone 2 (Z.of_nat (n - Nat.min m n)) (Z.of_nat (n - (Nat.min m n - fuel))) ltac:(Lia.lia) ltac:(Lia.lia)).
        intro. assert (n - Nat.min m n = n - (Nat.min m n - fuel))%nat; [|Lia.lia].
        apply Nat2Z.inj_iff. rewrite Nat2Z.inj_pow in H4.
        apply (Z.pow_inj_r 2); Lia.lia. }
      repeat red. do 2 (split; [reflexivity|]).
      rewrite PeanoNat.Nat.sub_0_r in HF1.
      rewrite HF1. eexists; split; eauto.
    Qed.

    Lemma br2_ntt_inverse_ok:
      program_logic_goal_for br2_ntt_inverse
        (forall functions : map.rep,
            map.get functions ntt_inverse = Some br2_ntt_inverse ->
            spec_of_mul functions ->
            spec_of_sub functions -> spec_of_add functions -> spec_of_ntt_inverse functions).
    Proof.
      Local Opaque Memory.bytes_per to_byte_table Z.pow Z.of_nat List.map Z.div Z.sub Z.add Nat.sub Nat.min F.F word_of_F F.pow Nat.pow F.to_Z.
      assert (len_chunk1: forall A (l: list A), length (List.chunk 1 l) = length l).
      { intros; rewrite List.length_chunk by congruence.
        rewrite <- (PeanoNat.Nat.mul_1_r (length l)), List.Nat.div_up_exact; Lia.lia. }
      repeat straightline. unfold NTT_inverse_gallina.
      apply wp_while.
      set (inverse_layer_recomposition_loop' :=
             fun zetas k r state =>
               fold_left
                 (fun (state0 : nat * nat * list (ModularArithmetic.F q)) (i : nat) =>
                    let
                      '(l, len, p) := state0 in
                    let start := 0%nat in
                    let old_len := len in
                    let len0 := Init.Nat.shiftl len 1 in
                    let
                      '(l0, _, p1) :=
                      inverse_polynomial_list_loop zetas (Init.Nat.shiftl 1 (r - 1 - i))
                        old_len len0 (l, start, p) in (l0, len0, p1)) (seq 0 k) state).
      assert (recomposition_loop_eq: forall zetas r state, inverse_layer_recomposition_loop' zetas r r state = inverse_layer_recomposition_loop zetas r state) by reflexivity.
      set (loop_inv1 := fun (fuel1: nat) (tr': Semantics.trace) (mem': mem) (loc': locals) =>
                          (fuel1 <= Nat.min m n)%nat /\
                            tr' = tr /\
                            map.get loc' "p" = Some p_ptr /\
                            let i := (Nat.min m n - fuel1)%nat in
                            exists p' px',
                              inverse_layer_recomposition_loop' zetas i (Nat.min m n) (Init.Nat.shiftl 1 (Nat.min m n), Init.Nat.shiftl 1 (n - Nat.min m n), p) = (Nat.pow 2 fuel1, Nat.pow 2 (n - fuel1), px')%nat /\
                                Forall2 (fun x y => feval y = Some x) px' p' /\
                                map.get loc' "l" = Some (word.of_Z (Z.of_nat (Nat.pow 2 fuel1))) /\
                                map.get loc' "len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - fuel1)))) /\
                                (Bignums 1 (2 ^ n) p_ptr (List.chunk 1 p') ⋆ R)%sep mem').
      exists nat, lt, loop_inv1; split; [apply lt_wf|]. split.
      { (* loop_inv1 holds at beginning *)
        exists (Nat.min m n). repeat split; [reflexivity|unfold l1, l0; repeat (rewrite map.get_put_diff by congruence); apply map.get_put_same|].
        rewrite Nat.sub_diag. intros; subst i.
        exists x, p. repeat split; auto.
        2: unfold l1, l0; repeat (rewrite map.get_put_diff by (clear; congruence)); apply map.get_put_same.
        2: apply map.get_put_same.
        cbn. do 2 rewrite Nat.shiftl_1_l. reflexivity. }
      intros fuel1 ? mem1 loc1 Hinv1.
      destruct Hinv1 as (Hfuel1 & -> & Hptr1 & p1 & px1 & Heq1 & HF1 & Hm1 & Hlen1 & Hp1).
      eexists; split.
      { repeat straightline.
        eexists; split; [eassumption|reflexivity]. }
      rewrite <- Core.word.morph_ltu.
      2-3: split; try Lia.lia.
      2-3: rewrite Nat2Z.inj_pow.
      2-3: apply Zpow_facts.Zpower_lt_monotone; Lia.lia.
      assert (word.unsigned (if (_ <? _)%Z then _ else _) = if Nat.eq_dec fuel1 0%nat then 0%Z else 1%Z) as ->.
      { match goal with | |- context [(Z.of_nat ?a <? Z.of_nat ?b)] => generalize (Zlt_cases (Z.of_nat a) (Z.of_nat b)); intro Hcond1 end.
        destruct (Nat.eq_dec fuel1 0) as [->|Hfnz1].
        - rewrite PeanoNat.Nat.sub_0_r in *.
          destruct (_ <? _); [clear -Hcond1; Lia.lia|].
          apply word.unsigned_of_Z_0.
        - destruct (_ <? _); [apply word.unsigned_of_Z_1|].
          apply Nat2Z.inj_ge, Nat.pow_le_mono_r_iff in Hcond1; clear -Hcond1 Hfnz1 Hfuel1; Lia.lia. }
      split; intros Hb; destruct (Nat.eq_dec fuel1 0) as [->|Hfnz1]; try (clear -Hb; congruence); clear Hb.
      { (* loop_inv1 preserved *)
        repeat straightline. eexists; split; repeat straightline.
        { unfold l0; rewrite map.get_put_diff by (clear; congruence).
          eexists; split; [eassumption|reflexivity]. }
        eexists; split; repeat straightline.
        { unfold l1, l0; do 2 (rewrite map.get_put_diff by (clear; congruence)).
          eexists; split; [eassumption|repeat straightline]. }
        apply wp_while.
        set (loop_inv2 := fun (fuel2: nat) (tr': Semantics.trace) (mem': mem) (loc': locals) =>
                            (fuel2 <= Nat.pow 2 (fuel1 - 1))%nat /\
                              tr' = tr /\
                              map.get loc' "p" = Some p_ptr /\
                              let i := ((Nat.pow 2 (fuel1 - 1)) - fuel2)%nat in
                              exists p' px',
                                inverse_polynomial_list_loop zetas i (Nat.pow 2 (n - fuel1))%nat (Nat.pow 2 (n - (fuel1 - 1)))%nat (Nat.pow 2 fuel1, 0, px1)%nat = (Nat.pow 2 fuel1 - i, (i * (2 ^ (n - (fuel1 - 1)))), px')%nat  /\
                                  Forall2 (fun x y => feval y = Some x) px' p' /\
                                  map.get loc' "l" = Some (word.of_Z (Z.of_nat ((2 ^ fuel1) - i))) /\
                                  map.get loc' "len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - (fuel1 - 1))))) /\
                                  map.get loc' "old_len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - fuel1)))) /\
                                  map.get loc' "start" = Some (word.of_Z (Z.of_nat (i * (2 ^ (n - (fuel1 - 1)))))) /\
                                  (Bignums 1 (2 ^ n) p_ptr (List.chunk 1 p') ⋆ R)%sep mem').
        exists nat, lt, loop_inv2. split; [apply lt_wf|].
        split.
        { (* loop_inv2 holds at start *)
          exists (Nat.pow 2 (fuel1 - 1)). repeat split; [reflexivity|..].
          - unfold l2, l1, l0. repeat (rewrite map.get_put_diff by (clear; congruence)). auto.
          - rewrite Nat.sub_diag. intro; subst i.
            rewrite Nat.sub_0_r, Nat.mul_0_l.
            unfold l2, l1, l0. repeat (rewrite map.get_put_diff by (clear; congruence)).
            exists p1, px1; repeat split; auto; repeat (rewrite map.get_put_diff by (clear; congruence)); rewrite map.get_put_same; auto.
            rewrite <- Core.word.morph_shiftl by Lia.lia.
            f_equal. f_equal. rewrite Z.shiftl_mul_pow2 by Lia.lia.
            assert (2 ^ 1 = Z.of_nat (2 ^ 1)) as -> by reflexivity.
            rewrite <- Nat2Z.inj_mul, <- Nat.pow_add_r. f_equal.
            f_equal. clear -Hfuel1 Hfnz1. Lia.lia. }
        intros fuel2 ? mem2 loc2 Hinv2.
        destruct Hinv2 as (Hfuel2 & -> & Hptr2 & p2 & px2 & Heq2 & HF2 & Hm2 & Hlen2 & Hold_len2 & Hstart2 & Hp2).
        eexists; split.
        { repeat straightline.
          eexists; split; [eassumption|reflexivity]. }
        rewrite <- Core.word.morph_ltu.
        3: split; [|rewrite Nat2Z.inj_pow; apply Zpow_facts.Zpower_lt_monotone]; Lia.lia.
        2: split; [Lia.nia|].
        2: apply (Z.le_lt_trans _ (Z.of_nat (Nat.pow 2 n))).
        3: rewrite Nat2Z.inj_pow; apply Zpow_facts.Zpower_lt_monotone; Lia.lia.
        2: apply Nat2Z.inj_le; rewrite Nat.mul_sub_distr_r, <- Nat.pow_add_r.
        2: assert (_ + (_ - _) = n)%nat as -> by Lia.lia; Lia.lia.
        assert (word.unsigned _ = if (Nat.eq_dec fuel2 0) then 0%Z else 1%Z) as ->.
        { rewrite Nat.mul_sub_distr_r, <- Nat.pow_add_r.
          assert (_ + (_ - _) = n)%nat as -> by Lia.lia.
          destruct (Nat.eq_dec fuel2 0) as [->|Hfnz2].
          - rewrite Nat.sub_0_r.
            match goal with | |- context [(Z.of_nat ?a <? Z.of_nat ?b)] => generalize (Zlt_cases (Z.of_nat a) (Z.of_nat b)); intro Hcond2 end.
            destruct (_ <? _); [clear -Hcond2; Lia.lia|apply word.unsigned_of_Z_0].
          - match goal with | |- context [(Z.of_nat ?a <? Z.of_nat ?b)] => generalize (Zlt_cases (Z.of_nat a) (Z.of_nat b)); intro Hcond2 end.
            destruct (_ <? _); [apply word.unsigned_of_Z_1|].
            clear -Hcond2 Hfuel2 Hfnz2 Hfuel1; apply Nat2Z.inj_ge in Hcond2.
            pose proof (NatUtil.pow_nonzero 2 n ltac:(congruence)).
            pose proof (NatUtil.pow_nonzero 2 (n - (fuel1 - 1)) ltac:(congruence)).
            Lia.lia. }
        split; intros Hb; destruct (Nat.eq_dec fuel2 0) as [->|Hfnz2]; try (clear -Hb; congruence); clear Hb.
        { (* loop_inv2 is preserved *)
          repeat straightline. eexists; split; repeat straightline.
          { eexists; split; [eassumption|reflexivity]. }
          eexists; split; repeat straightline.
          { unfold l0. rewrite map.get_put_same.
            rewrite <- word.ring_morph_sub.
            assert (Nat.pow 2 fuel1 = 2 * (Nat.pow 2 (fuel1 - 1)))%nat as -> by (rewrite <- Nat.pow_succ_r'; f_equal; Lia.lia).
            assert (1%Z = Z.of_nat 1) as -> by reflexivity.
            rewrite <- Nat2Z.inj_sub by (clear -Hfuel2 Hfnz2; Lia.nia).
            assert (2 * _ - _ - _ = Nat.pow 2 (fuel1 - 1) + (fuel2 - 1))%nat as -> by Lia.lia.
            eexists; split; [reflexivity|]. repeat straightline.
            unfold v. rewrite <- word.ring_morph_mul by (Lia.nia).
            erewrite (load_from_word_table _ _ (word_of_F F.zero)); auto.
            2:{ rewrite length_to_byte_table, length_map.
                rewrite zetas_length_ok. assert (width / 8 = 4 \/ width / 8 = 8) as Hw.
                { clear -BW.
                  destruct width_cases as [-> | ->]; [left|right]; reflexivity. }
                rewrite Nat2Z.inj_mul, Z2Nat.id by (clear -Hw; destruct Hw; Lia.lia).
                rewrite Nat2Z.inj_pow.
                transitivity (2 ^ 3 * 2 ^ Z.of_nat m).
                - apply Z.mul_le_mono_nonneg_r.
                  + apply Z.lt_le_incl, ZLib.Z.pow2_pos, Nat2Z.is_nonneg.
                  + clear -Hw. destruct Hw as [-> | ->]; Lia.lia.
                - rewrite <- Z.pow_add_r by Lia.lia.
                  apply Z.pow_le_mono_r; clear -mp3_le_with; Lia.lia. }
            2:{ rewrite length_map, zetas_length_ok.
                eapply (Nat.lt_le_trans _ (2 ^ (Nat.min m n))%nat).
                + eapply (Nat.lt_le_trans _ (2 ^ fuel1)%nat).
                  * assert (Nat.pow 2 fuel1 = 2 * Nat.pow 2 (fuel1 - 1))%nat as -> by (rewrite <- Nat.pow_succ_r'; f_equal; Lia.lia).
                    clear -Hfuel2 Hfnz2; Lia.lia.
                  * apply Nat.pow_le_mono; clear -Hfuel1; Lia.lia.
                + apply Nat.pow_le_mono; clear; Lia.lia. }
            rewrite <- nth_default_eq. eexists; split; reflexivity. }
          eexists; split; repeat straightline.
          { unfold l1, l0. do 2 (rewrite map.get_put_diff by (clear; congruence)).
            eexists; split; [eassumption|reflexivity]. }
          apply wp_while.
          set (v' := nth_default (word_of_F 0) (map word_of_F zetas) (2 ^ (fuel1 - 1) + (fuel2 - 1))).
          set (v := nth_default 0%F zetas (2 ^ (fuel1 - 1) + (fuel2 - 1))).
          assert (Hv_eq: v' = word_of_F v).
          { unfold v', v. apply ListUtil.map_nth_default_always. }
          set (loop_inv3 := fun (fuel3: nat) (tr': Semantics.trace) (mem': mem) (loc': locals) =>
                              (fuel3 <= Nat.pow 2 (n - fuel1))%nat /\
                                tr' = tr /\
                                map.get loc' "p" = Some p_ptr /\
                                let i := ((Nat.pow 2 (n - fuel1)) - fuel3)%nat in
                                let px3 := inverse_polynomial_recompose_loop i (((2 ^ (fuel1 - 1) - fuel2) * 2 ^ (n - (fuel1 - 1)))) ((2 ^ (n - fuel1))) v px2 in
                                exists p',
                                  Forall2 (fun x y => feval y = Some x) px3 p' /\
                                    map.get loc' "l" = Some (word.of_Z (Z.of_nat (2 ^ fuel1 - (2 ^ (fuel1 - 1) - fuel2) - 1))) /\
                                    map.get loc' "len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - (fuel1 - 1))))) /\
                                    map.get loc' "old_len" = Some (word.of_Z (Z.of_nat (Nat.pow 2 (n - fuel1)))) /\
                                    map.get loc' "start" = Some (word.of_Z (Z.of_nat ((2 ^ (fuel1 - 1) - fuel2) * 2 ^ (n - (fuel1 - 1))))) /\
                                    map.get loc' "j" = Some (word.of_Z (Z.of_nat ((2 ^ (fuel1 - 1) - fuel2) * 2 ^ (n - (fuel1 - 1)) + i))) /\
                                    map.get loc' "z" = Some v' /\
                                    (Bignums 1 (2 ^ n) p_ptr (List.chunk 1 p') ⋆ R)%sep mem').
          exists nat, lt, loop_inv3. split; [apply lt_wf|].
          split.
          { (* loop_inv3 holds at beginning *)
            exists (Nat.pow 2 (n - fuel1)). unfold l2, l1, l0.
            repeat split; [reflexivity|..].
            - repeat (rewrite map.get_put_diff by (clear; congruence)); auto.
            - exists p2. repeat split; auto; repeat (rewrite map.get_put_diff by (clear; congruence)); try rewrite map.get_put_same; auto.
              + rewrite Nat.sub_diag. assert (inverse_polynomial_recompose_loop _ _ _ _ _ = px2) as -> by reflexivity; assumption.
              + rewrite <- word.ring_morph_sub.
                assert (1%Z = Z.of_nat 1) as -> by reflexivity.
                rewrite <- Nat2Z.inj_sub; [reflexivity|].
                assert (Nat.pow 2 fuel1 = 2 * Nat.pow 2 (fuel1 - 1))%nat as -> by (rewrite <- Nat.pow_succ_r'; f_equal; Lia.lia).
                clear -Hfuel2 Hfnz2; Lia.lia.
              + rewrite Nat.sub_diag, Nat.add_0_r. reflexivity. }
          intros fuel3 ? mem3 loc3 Hinv3.
          destruct Hinv3 as (Hfuel3 & -> & Hptr3 & p3 & HF3 & Hm3 & Hlen3 & Hold_len3 & Hstart3 & Hj3 & Hz3 & Hp3).
          eexists; split.
          { repeat straightline.
            eexists; split; [eassumption|repeat straightline].
            eexists; split; [eassumption|repeat straightline].
            eexists; split; [eassumption|repeat straightline]. }
          rewrite <- word.ring_morph_add, <- Nat2Z.inj_add.
          rewrite <- Core.word.morph_ltu.
          2-3: split; [apply Zle_0_nat|].
          2: apply (Z.le_lt_trans _ (Z.of_nat ((2 ^ (fuel1 - 1) - fuel2) * 2 ^ (n - (fuel1 - 1)) + 2 ^ (n - fuel1)))); [apply Nat2Z.inj_le; clear; Lia.lia|].
          2-3: assert (Z.pow 2 width = Z.of_nat (Nat.pow 2 (Z.to_nat width))) as -> by (rewrite Nat2Z.inj_pow, Z2Nat.id; clear -mp3_le_with; Lia.lia).
          2-3: apply Nat2Z.inj_lt.
          2-3: eapply (Nat.le_lt_trans _ (Nat.pow 2 n)); [|apply Nat.pow_lt_mono_r; auto].
          2-3: rewrite Nat.mul_sub_distr_r, <- PeanoNat.Nat.pow_add_r.
          2-3: assert (fuel1 - 1 + _ = n)%nat as -> by (clear -Hfnz1 Hfuel1; Lia.lia).
          2-3: rewrite <- (Nat.mul_1_l (Nat.pow 2 (n - fuel1))).
          2-3: assert (n - (fuel1 - 1) = S (n - fuel1))%nat as -> by (clear -Hfnz1 Hfuel1; Lia.lia).
          2-3: rewrite Nat.pow_succ_r'.
          2-3: assert (Nat.pow 2 n = (Nat.pow 2 fuel1) * (Nat.pow 2 (n - fuel1)))%nat as -> by (rewrite <- Nat.pow_add_r; f_equal; Lia.lia).
          2-3: rewrite Nat.mul_assoc, <- Nat.mul_sub_distr_r, <- Nat.mul_add_distr_r.
          2-3: apply Nat.mul_le_mono_r.
          2-3: generalize (Nat.pow_nonzero 2 fuel1 ltac:(Lia.lia)); clear -Hfuel1 Hfnz1 Hfuel2 Hfnz2; Lia.lia.
          assert (word.unsigned _ = if Nat.eq_dec fuel3 0 then 0%Z else 1%Z) as ->.
          { destruct (Nat.eq_dec fuel3 0) as [->|Hfnz3].
            - rewrite Nat.sub_0_r, Z.ltb_irrefl.
              apply word.unsigned_of_Z_0.
            - match goal with | |- context [(Z.of_nat ?a <? Z.of_nat ?b)] => generalize (Zlt_cases (Z.of_nat a) (Z.of_nat b)); intro Hcond3 end.
              destruct (_ <? _); [apply word.unsigned_of_Z_1|].
              apply Nat2Z.inj_ge in Hcond3.
              clear -Hfnz3 Hfuel3 Hcond3; Lia.lia. }
          split; intros Hb; destruct (Nat.eq_dec fuel3 0) as [->|Hfnz3]; try (clear -Hb; congruence); clear Hb.
          { (* loop_inv3 preservation *)
            assert ((2 ^ (fuel1 - 1) - fuel2) * 2 ^ (n - (fuel1 - 1)) + (2 ^ (n - fuel1) - fuel3) + 2 ^ (n - fuel1) < 2 ^ n)%nat as idx_ok.
            { rewrite Nat.mul_sub_distr_r, <- Nat.pow_add_r.
              assert (fuel1 - 1 + _ = n)%nat as -> by (clear -Hfuel1 Hfnz1 Hfuel2 Hfnz2; Lia.lia).
              apply (Nat.lt_le_trans _ (2 ^ n - fuel2 * 2 ^ (n - (fuel1 - 1)) + (2 * 2 ^ (n - fuel1)))); [clear -Hfuel1 Hfnz1 Hfuel2 Hfnz2 Hfuel3 Hfnz3; Lia.lia|].
              rewrite <- Nat.pow_succ_r'.
              assert (n - (fuel1 - 1) = S (n - fuel1))%nat as <- by (clear -Hfnz1 Hfuel1; Lia.lia).
              clear -Hfuel1 Hfnz1 Hfuel2 Hfnz2 Hfuel3 Hfnz3.
              assert (Nat.pow 2 n = (Nat.pow 2 (fuel1 - 1)) * (Nat.pow 2 (n - (fuel1 - 1))))%nat as -> by (rewrite <- Nat.pow_add_r; f_equal; Lia.lia).
              rewrite <- Nat.mul_sub_distr_r.
              rewrite <- (Nat.mul_1_l (2 ^ (n - (fuel1 - 1)))) at 2.
              rewrite <- Nat.mul_add_distr_r.
              apply Nat.mul_le_mono_r. Lia.lia. }
            pose proof (Bignums_length _ _ _ _ _ _ Hp3) as Xlen.
            rewrite len_chunk1 in Xlen.
            repeat straightline. eexists; split; repeat straightline.
            { eexists; split; [eassumption|repeat straightline].
              eexists; split; [eassumption|repeat straightline].
              unfold v0. rewrite bytes_per_width_bytes_per_word.
              rewrite <- word.ring_morph_mul. rewrite Z.mul_comm.
              erewrite (Bignums1_load_of_sep R (word_of_F F.zero) (Nat.pow 2 n) p_ptr _ _ p3); auto.
              2: rewrite Xlen; clear -idx_ok; Lia.lia.
              eexists; split; reflexivity. }
            eexists; split; repeat straightline.
            { unfold l0. rewrite map.get_put_diff by (clear; congruence).
              eexists; split; [eassumption|repeat straightline].
              rewrite map.get_put_diff by (clear; congruence).
              eexists; split; [eassumption|repeat straightline].
              rewrite map.get_put_diff by (clear; congruence).
              eexists; split; [eassumption|repeat straightline].
              unfold v0. rewrite bytes_per_width_bytes_per_word.
              rewrite <- word.ring_morph_add, <- Nat2Z.inj_add.
              rewrite <- word.ring_morph_mul. rewrite Z.mul_comm.
              erewrite (Bignums1_load_of_sep R (word_of_F F.zero) (Nat.pow 2 n) p_ptr _ _ p3); auto.
              2: rewrite Xlen; clear -idx_ok; Lia.lia.
              eexists; split; reflexivity. }
            eexists; split; repeat straightline.
            { unfold l1, l0. rewrite map.get_put_diff by (clear; congruence).
              rewrite map.get_put_same. eexists; split; repeat straightline.
              rewrite map.get_put_same. eexists; split; repeat straightline. }
            straightline_call.
            { split; apply (proj1 (@Forall.Forall2_forall_iff'' _ _ (fun x y => feval y = Some x) _ p3 0%F (word_of_F 0%F)) (conj HF3 (feval_ok _))). }
            repeat straightline. eexists; split; repeat straightline.
            { unfold l', l1, l0.
              repeat (rewrite map.get_put_diff by (clear; congruence)).
              eexists; split; [eassumption|repeat straightline].
              repeat (rewrite map.get_put_diff by (clear; congruence)).
              eexists; split; [eassumption|repeat straightline]. }
            eexists; split; repeat straightline.
            { unfold l'. rewrite map.get_put_same. eexists; split; reflexivity. }
            rewrite bytes_per_width_bytes_per_word.
            rewrite <- word.ring_morph_mul. rewrite Z.mul_comm.
            unfold store.
            eapply (Bignums1_store_of_sep R (Nat.pow 2 n) p_ptr _ _ p3); auto.
            { rewrite Xlen; clear -idx_ok; Lia.lia. }
            intros mem4 Hp3'.
            repeat straightline.
            eexists; split; repeat straightline.
            { unfold l', l1, l0. rewrite map.get_put_diff by (clear; congruence).
              rewrite map.get_put_same.
              eexists; split; [reflexivity|repeat straightline].
              repeat (rewrite map.get_put_diff by (clear; congruence)).
              rewrite map.get_put_same.
              eexists; split; [reflexivity|repeat straightline]. }
            straightline_call.
            { split; apply (proj1 (@Forall.Forall2_forall_iff'' _ _ (fun x y => feval y = Some x) _ p3 0%F (word_of_F 0%F)) (conj HF3 (feval_ok _))). }
            repeat straightline.
            eexists; split; repeat straightline.
            { unfold l'0, l', l1, l0. repeat (rewrite map.get_put_diff by (clear; congruence)).
              eexists; split; [eassumption|repeat straightline].
              rewrite map.get_put_same. eexists; split; [reflexivity|repeat straightline]. }
            straightline_call.
            { split; [|eassumption]. rewrite Hv_eq. apply feval_ok. }
            repeat straightline.
            eexists; split; repeat straightline.
            { unfold l'1, l'0, l', l1, l0. repeat (rewrite map.get_put_diff by (clear; congruence)).
              eexists; split; [eassumption|repeat straightline].
              repeat (rewrite map.get_put_diff by (clear; congruence)).
              eexists; split; [eassumption|repeat straightline].
              repeat (rewrite map.get_put_diff by (clear; congruence)).
              eexists; split; [eassumption|repeat straightline]. }
            eexists; split; repeat straightline.
            { unfold l'1. rewrite map.get_put_same.
              eexists; split; reflexivity. }
            unfold store.
            rewrite bytes_per_width_bytes_per_word.
            rewrite <- word.ring_morph_add, <- Nat2Z.inj_add.
            rewrite <- word.ring_morph_mul. rewrite Z.mul_comm.
            eapply (Bignums1_store_of_sep R (Nat.pow 2 n) p_ptr _ _ _); eauto.
            { rewrite length_set_nth, Xlen; clear -idx_ok; Lia.lia. }
            intros mem5 Hp3''.
            repeat straightline.
            eexists; split; repeat straightline.
            { unfold l'1, l'0, l', l1, l0. repeat (rewrite map.get_put_diff by (clear; congruence)).
              eexists; split; [eassumption|repeat straightline]. }
            exists (fuel3 - 1)%nat; split; [|clear -Hfnz3; Lia.lia].
            unfold loop_inv3. split; [clear -Hfuel3; Lia.lia|].
            split; [reflexivity|].
            unfold l2, l'1, l'0, l', l1, l0.
            split; [repeat (rewrite map.get_put_diff by (clear; congruence)); assumption|].
            eexists; repeat split; repeat (rewrite map.get_put_diff by (clear; congruence)); try rewrite map.get_put_same; eauto.
            2:{ rewrite <- word.ring_morph_add.
                assert (1 = Z.of_nat 1) as -> by reflexivity.
                rewrite <- Nat2Z.inj_add. do 3 f_equal.
                clear -Hfuel1 Hfuel2 Hfuel3 Hfnz1 Hfnz2 Hfnz3; Lia.lia. }
            assert (_ - (fuel3 - 1) = S (Nat.pow 2 (n - fuel1) - fuel3))%nat as -> by (clear -Hfuel1 Hfuel2 Hfuel3 Hfnz1 Hfnz2 Hfnz3; Lia.lia).
            unfold inverse_polynomial_recompose_loop.
            rewrite seq_S, fold_left_app.
            assert (fold_left _ (seq _ _) _ = inverse_polynomial_recompose_loop (2 ^ (n - fuel1) - fuel3) ((2 ^ (fuel1 - 1) - fuel2) * 2 ^ (n - (fuel1 - 1)))  (2 ^ (n - fuel1)) v px2)%nat as -> by reflexivity.
            cbn [fold_left].
            apply Forall2_set_nth; auto.
            apply Forall2_set_nth; auto. }
          repeat straightline.
          eexists; split; repeat straightline.
          { eexists; split; [eassumption|repeat straightline].
            eexists; split; [eassumption|repeat straightline]. }
          exists (fuel2 - 1)%nat; split; [|clear -Hfnz2; Lia.lia].
          unfold loop_inv2.
          split; [clear -Hfuel2; Lia.lia|].
          split; [reflexivity|].
          unfold l0; rewrite map.get_put_diff by (clear; congruence).
          split; [assumption|].
          rewrite Nat.sub_0_r in *.
          exists p3. eexists. repeat split; repeat (rewrite map.get_put_diff by (clear; congruence)); try (rewrite map.get_put_same); eauto.
          2:{ rewrite Hm3. do 3 f_equal.
              clear -Hfuel1 Hfnz1 Hfuel2 Hfnz2; Lia.lia. }
          2:{ rewrite <- word.ring_morph_add, <- Nat2Z.inj_add.
              do 3 f_equal. clear -Hfuel1 Hfnz1 Hfuel2 Hfnz2; Lia.nia. }
          assert (_ - (fuel2 - 1) = S (Nat.pow 2 (fuel1 - 1) - fuel2))%nat as -> by (clear -Hfuel1 Hfnz1 Hfuel2 Hfnz2; Lia.lia).
          unfold inverse_polynomial_list_loop.
          rewrite seq_S, fold_left_app.
          assert (fold_left _ (seq _ _) _ = inverse_polynomial_list_loop zetas (Nat.pow 2 (fuel1 - 1) - fuel2) (2 ^ (n - fuel1)) (2 ^ (n - (fuel1 - 1))) ((2 ^ fuel1)%nat, 0%nat, px1))%nat as -> by reflexivity.
          cbn [fold_left]. rewrite Heq2.
          f_equal; [|unfold v]; f_equal; try (clear -Hfuel1 Hfnz1 Hfuel2 Hfnz2; Lia.lia).
          f_equal. assert (Nat.pow 2 fuel1 = 2 * Nat.pow 2 (fuel1 - 1))%nat as -> by (rewrite <- Nat.pow_succ_r'; f_equal; clear -Hfnz1; Lia.lia).
          clear -Hfuel1 Hfnz1 Hfuel2 Hfnz2; Lia.nia. }
        rewrite Nat.sub_0_r in *.
        exists (fuel1 - 1)%nat; split; [|clear -Hfnz1; Lia.lia].
        unfold loop_inv1.
        split; [clear -Hfuel1; Lia.lia|].
        split; [reflexivity|].
        split; [assumption|].
        do 2 eexists; repeat split; eauto.
        2:{ rewrite Hm2. assert (Nat.pow 2 fuel1 = 2 * Nat.pow 2 (fuel1 - 1))%nat as -> by (rewrite <- Nat.pow_succ_r'; f_equal; clear -Hfnz1; Lia.lia).
            do 3 f_equal; clear; Lia.lia. }
        assert (Nat.min m n - (fuel1 - 1) = S (Nat.min m n - fuel1))%nat as -> by (clear -Hfuel1 Hfnz1; Lia.lia).
        unfold inverse_layer_recomposition_loop'.
        rewrite seq_S, fold_left_app.
        assert (fold_left _ (seq _ _) _ = inverse_layer_recomposition_loop' zetas (Nat.min m n - fuel1) (Nat.min m n) (Init.Nat.shiftl 1 (Nat.min m n), Init.Nat.shiftl 1 (n - Nat.min m n), p))%nat as -> by reflexivity.
        rewrite Heq1. cbn.
        assert (_ - 1 - _ = fuel1 - 1)%nat as -> by (clear -Hfnz1 Hfuel1; Lia.lia).
        rewrite Nat.shiftl_1_l.
        assert (Nat.pow 2 _ + Nat.pow 2 _ = Nat.pow 2 (n - (fuel1 - 1)))%nat as ->.
        { assert (n - (_ - _) = S (n - fuel1))%nat as -> by (clear -Hfuel1 Hfnz1; Lia.lia).
          rewrite Nat.pow_succ_r'; clear; Lia.lia. }
        rewrite Heq2. do 2 f_equal.
        assert (Nat.pow 2 fuel1 = 2 * Nat.pow 2 (fuel1 - 1))%nat as -> by (rewrite <- Nat.pow_succ_r'; f_equal; clear -Hfnz1; Lia.lia).
        clear; Lia.lia. }
      repeat straightline. rewrite Nat.sub_0_r in *.
      rewrite recomposition_loop_eq in Heq1.
      rewrite Heq1. apply wp_while.
      rewrite Nat.shiftl_1_l.
      set (loop_inv4 := fun (fuel4: nat) (tr': Semantics.trace) (mem': mem) (loc': locals) =>
                          (fuel4 <= Nat.pow 2 n)%nat /\
                            tr' = tr /\
                            map.get loc' "p" = Some p_ptr /\
                            let i := ((Nat.pow 2 n) - fuel4)%nat in
                            exists p4,
                              Forall2 (fun x y => feval y = Some x) (div_loop i (F.inv ((1 + 1) ^ N.of_nat (Nat.min m n))) px1) p4 /\
                                map.get loc' "j" = Some (word.of_Z (Z.of_nat i)) /\
                                (Bignums 1 (2 ^ n) p_ptr (List.chunk 1 p4) ⋆ R)%sep mem').
      exists nat, lt, loop_inv4; split; [apply lt_wf|].
      split.
      { exists (Nat.pow 2 n). unfold loop_inv4. rewrite Nat.sub_diag.
        repeat split; [Lia.lia|..].
        - unfold l0; rewrite map.get_put_diff by congruence; auto.
        - exists p1; repeat split; auto.
          apply map.get_put_same. }
      intros fuel4 ? mem4 loc4 Hinv4.
      destruct Hinv4 as (Hfuel4 & -> & Hptr4 & p4 & HF4 & Hj & Hp4).
      eexists; split; repeat straightline.
      { eexists; split; [eassumption|repeat straightline]. }
      rewrite <- Core.word.morph_ltu.
      2-3: split; [apply Nat2Z.is_nonneg|].
      2-3: assert (2 ^ width = Z.of_nat (Nat.pow 2 (Z.to_nat width))) as -> by (rewrite Nat2Z.inj_pow, Z2Nat.id by Lia.lia; reflexivity).
      2-3: apply Nat2Z.inj_lt.
      2: apply (Nat.le_lt_trans _ (Nat.pow 2 n)); [clear; Lia.lia|].
      2-3: apply Nat.pow_lt_mono_r; Lia.lia.
      assert (word.unsigned _ = if Nat.eq_dec fuel4 0 then 0%Z else 1%Z) as ->.
      { destruct (Nat.eq_dec fuel4 0) as [->|Hfnz4].
        - rewrite Nat.sub_0_r, Z.ltb_irrefl. apply word.unsigned_of_Z_0.
        - match goal with | |- context [(Z.of_nat ?a <? Z.of_nat ?b)] => generalize (Zlt_cases (Z.of_nat a) (Z.of_nat b)); intro Hcond4 end.
          destruct (_ <? _); [apply word.unsigned_of_Z_1|].
          apply Nat2Z.inj_ge in Hcond4.
          clear -Hfnz4 Hfuel4 Hcond4; Lia.lia. }
      pose proof (Bignums_length _ _ _ _ _ _ Hp4) as Xlen.
      rewrite len_chunk1 in Xlen.
      split; intros Hb; destruct (Nat.eq_dec fuel4 0) as [->|Hfnz4]; try (clear -Hb; congruence); clear Hb.
      { repeat straightline. eexists; split; repeat straightline.
        { eexists; split; [eassumption|repeat straightline].
          eexists; split; [eassumption|repeat straightline].
          unfold v. rewrite bytes_per_width_bytes_per_word.
          rewrite <- word.ring_morph_mul. rewrite Z.mul_comm.
          erewrite Bignums1_load_of_sep; eauto.
          rewrite Xlen; clear -Hfuel4 Hfnz4; Lia.lia. }
        eexists; split; repeat straightline.
        { eexists; split; [apply map.get_put_same|repeat straightline]. }
        straightline_call.
        { split; [|apply (proj1 (@Forall.Forall2_forall_iff'' _ _ (fun x y => feval y = Some x) _ p4 0%F (word_of_F 0%F)) (conj HF4 (feval_ok _)))].
          rewrite word.of_Z_unsigned.
          apply feval_ok. }
        repeat straightline.
        eexists; split; repeat straightline.
        { unfold l', l0. repeat (rewrite map.get_put_diff by (clear; congruence)).
          eexists; split; [eassumption|repeat straightline].
          repeat (rewrite map.get_put_diff by (clear; congruence)).
          eexists; split; [eassumption|repeat straightline]. }
        eexists; split; repeat straightline.
        { eexists; split; [apply map.get_put_same|reflexivity]. }
        rewrite bytes_per_width_bytes_per_word.
        rewrite <- word.ring_morph_mul. rewrite Z.mul_comm.
        eapply Bignums1_store_of_sep; eauto.
        { rewrite Xlen; clear -Hfuel4 Hfnz4; Lia.lia. }
        intros mem5 Hmem5.
        repeat straightline. eexists; split; repeat straightline.
        { unfold l', l0. repeat (rewrite map.get_put_diff by (clear; congruence)).
          eexists; split; [eassumption|repeat straightline]. }
        exists (fuel4 - 1)%nat; split; [|clear -Hfnz4; Lia.lia].
        unfold loop_inv4.
        split; [clear -Hfuel4; Lia.lia|].
        split; [reflexivity|].
        unfold l1, l', l0. repeat (rewrite map.get_put_diff by (clear; congruence)).
        split; [assumption|].
        rewrite map.get_put_same. assert (1%Z = Z.of_nat 1%nat) as -> by reflexivity.
        rewrite <- word.ring_morph_add, <- Nat2Z.inj_add.
        assert (_ - _ + 1 = Nat.pow 2 n - (fuel4 - 1))%nat as -> by (clear -Hfuel4 Hfnz4; Lia.lia).
        eexists; repeat split; eauto.
        assert (Nat.pow 2 n - (fuel4 - 1) = S (Nat.pow 2 n - fuel4))%nat as -> by (clear -Hfuel4 Hfnz4; Lia.lia).
        unfold div_loop. rewrite seq_S, fold_left_app.
        assert (fold_left _ (seq _ _) _ = div_loop (Nat.pow 2 n - fuel4) (F.inv ((1 + 1) ^ N.of_nat (Nat.min m n))) px1) as -> by reflexivity.
        cbn [fold_left].
        apply Forall2_set_nth; auto. }
      rewrite Nat.sub_0_r in *. repeat straightline.
      exists p4. auto.
    Qed.
  End FitsInOneWord.
End Bedrock.
