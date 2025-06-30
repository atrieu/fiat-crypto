Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.

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
Require Import Crypto.Util.ListUtil.Forall.

(* For [to_byte_table] *)
Require Import Rupicola.Lib.InlineTables.
(* For [offset] *)
Require Import Rupicola.Lib.Arrays.

Section Bignums.
  Context {width: Z}
          {BW: Bitwidth width}
          {word: word.word width}
          {mem: map.map word Byte.byte}.

  (* A flat array of n-words bignum *)
  Definition Bignums (n: nat) (len: nat) (addr: word) (xs: list (list word)): (@map.rep _ _ mem) -> Prop :=
    ((emp (length xs = len)) * (array (Bignum n) (word.of_Z (Z.of_nat n * (bytes_per_word width))) addr xs))%sep.

  Section Proofs.
    Context {word_ok: @word.ok width word} {map_ok: @map.ok word Byte.byte mem}.

    Lemma Bignums_nth_default:
      forall d n len addr xs i,
        (i < length xs)%nat ->
        (i < len)%nat ->
        (Z.of_nat (length xs * n) * bytes_per_word width < 2 ^ width)%Z ->
        Lift1Prop.iff1
          (Bignums n len addr xs)%sep
          ((Bignums n (Nat.min i len) addr (List.firstn i xs))
           ⋆ (Bignum n (word.add addr (word.of_Z (Z.of_nat (i * n) * (bytes_per_word width)))) (nth_default d xs i))
           ⋆ (Bignums n (len - (i + 1))%nat (word.add addr (word.of_Z (Z.of_nat ((i + 1) * n) * (bytes_per_word width)))) (List.skipn (i + 1) xs)))%sep.
    Proof.
      intros d n len addr xs i Hi Hi' Haddressible.
      pose proof Types.word_size_in_bytes_pos as Hpos.
      unfold Bignums. intro m. rewrite sep_emp_l.
      rewrite ((array_index_nat_inbounds (default:=d) (Bignum n) (word.of_Z (Z.of_nat n * (bytes_per_word width))) xs addr i Hi) m).
      rewrite word.unsigned_of_Z.
      rewrite <- word.add_assoc, <- word.ring_morph_add.
      unfold word.wrap. repeat rewrite Z.mod_small by Lia.nia.
      assert (Z.of_nat n * _ * Z.of_nat i = Z.of_nat (i * n) * bytes_per_word width)%Z as -> by Lia.lia.
      assert (Z.of_nat (i * n) * _ + _ * _ = Z.of_nat ((i + 1) * n) * bytes_per_word width)%Z as -> by Lia.lia.
      assert (S i = i + 1)%nat as -> by Lia.lia.
      rewrite List.hd_skipn_nth_default, length_firstn, length_skipn.
      repeat rewrite (sep_assoc _ _ _ m). rewrite sep_emp_l.
      split.
      - intros (HA & HB). rewrite HA; split; [reflexivity|].
        destruct HB as (ma & mb & Hsplit & Hleft & Hright).
        exists ma, mb. do 2 (split; [assumption|]).
        destruct Hright as (mrighta & mrightb & Hsplitright & Hrl & Hrr).
        exists mrighta, mrightb. do 2 (split; [assumption|]).
        rewrite sep_emp_l. split; [reflexivity|]. assumption.
      - intros (HA & HB). destruct HB as (ma & mb & Hsplit & Hl & Hr).
        destruct Hr as (mba & mbb &Hrsplit & Hrl & Hrr).
        rewrite sep_emp_l in Hrr. destruct Hrr as (Heq & Hrr).
        split; [Lia.lia|]. exists ma, mb. do 2 (split; [assumption|]).
        exists mba, mbb. do 2 (split; [assumption|]). assumption.
    Qed.

    Lemma Bignums_set_nth:
      forall n len addr xs i x,
        (i < length xs)%nat ->
        (i < len)%nat ->
        (Z.of_nat (length xs * n) * bytes_per_word width < 2 ^ width)%Z ->
        Lift1Prop.iff1
          (Bignums n len addr (set_nth i x xs))%sep
          ((Bignums n (Nat.min i len) addr (List.firstn i xs))
           ⋆ (Bignum n (word.add addr (word.of_Z (Z.of_nat (i * n) * (bytes_per_word width)))) x)
           ⋆ (Bignums n (len - (i + 1))%nat (word.add addr (word.of_Z (Z.of_nat ((i + 1) * n) * (bytes_per_word width)))) (List.skipn (i + 1) xs)))%sep.
    Proof.
      intros n len addr xs i x Hi Hi' Haddressible.
      rewrite (Bignums_nth_default x n len addr (set_nth i x xs) i ltac:(rewrite length_set_nth; auto) Hi' ltac:(rewrite length_set_nth; auto)).
      rewrite (set_nth_nth_default) by Lia.lia.
      destruct (Nat.eq_dec i i); [|Lia.lia].
      rewrite firstn_set_nth_out_of_bounds by Lia.lia.
      rewrite skipn_set_nth_out_of_bounds by Lia.lia.
      reflexivity.
    Qed.

    Lemma Bignums_length:
      forall n len addr xs m R,
        (Bignums n len addr xs * R)%sep m -> length xs = len.
    Proof.
      intros n len addr xs m R Hm.
      unfold Bignums in Hm.
      rewrite (sep_assoc _ _ _ m), sep_emp_l in Hm.
      destruct Hm; assumption.
    Qed.

    Lemma Bignums_length_forall:
      forall n len addr xs m R,
        (Bignums n len addr xs * R)%sep m ->
        Forall (fun x => length x = n) xs.
    Proof.
      intros n len addr xs m R Hm.
      apply Forall.Forall_forall_iff_nth_error.
      intros i v Hnth. pose proof (ListUtil.nth_error_value_length _ _ _ _ Hnth) as Hlen.
      pose proof (Bignums_length _ _ _ _ _ _ Hm) as Hlen'.
      unfold Bignums in Hm.
      seprewrite_in ((array_index_nat_inbounds (default:=nil) (Bignum n) (word.of_Z (Z.of_nat n * (bytes_per_word width))) xs addr i Hlen)) Hm.
      rewrite <- List.hd_skipn_nth_default in Hm.
      rewrite (ListUtil.nth_error_value_eq_nth_default _ _ _ Hnth) in Hm.
      seprewrite_in sep_comm Hm.
      destruct Hm as (ma & mb & ? & Ha & ?).
      destruct Ha as (? & ? & ? & Ha' & ?).
      apply sep_emp_l in Ha'. destruct Ha'; assumption.
    Qed.

    Lemma Bignums1_iff:
      forall len addr xs,
        Lift1Prop.iff1
          (Bignums 1 len addr (List.chunk 1 xs))%sep
          (emp (length xs = len) * array scalar (word.of_Z (bytes_per_word width)) addr xs)%sep.
    Proof.
      intros. intro m. unfold Bignums.
      do 2 rewrite sep_emp_l.
      rewrite List.length_chunk by congruence.
      assert (List.Nat.div_up _ _ = length xs) as ->.
      { rewrite <- (PeanoNat.Nat.mul_1_r (length xs)), List.Nat.div_up_exact by congruence.
        Lia.lia. }
      rewrite Z.mul_1_l.
      assert (array (Bignum 1) _ _ _ _ <-> array scalar (word.of_Z (bytes_per_word width)) addr xs m) as ->; [|reflexivity].
      unfold Bignum.
      revert addr m. induction xs; [reflexivity|].
      assert (List.chunk 1 (a::xs) = ((a::nil)::(List.chunk 1 xs))) as -> by reflexivity.
      cbn [array].
      split; intro X.
      - destruct X as (ma & mb & ? & Hl & Hr).
        rewrite sep_emp_l, sep_emp_r in Hl.
        rewrite IHxs in Hr.
        destruct Hl as (? & ? & ?).
        exists ma, mb. do 2 (split; auto).
      - destruct X as (ma & mb & ? & Hl & Hr).
        exists ma, mb. rewrite sep_emp_l, sep_emp_r.
        rewrite IHxs. do 2 (split; auto).
    Qed.

    Lemma Bignums1_load_of_sep:
      forall R d len addr addr' i xs m,
        (i < length xs)%nat ->
        (Bignums 1 len addr (List.chunk 1 xs) * R)%sep m ->
        addr' = word.add addr (word.of_Z (Z.of_nat i * (bytes_per_word width))) ->
        Memory.load access_size.word m addr' = Some (nth_default d xs i).
    Proof.
      intros R d len addr addr' i xs m Hi Harray Haddr.
      destruct Harray as (ma & mb & Hsplit & Harray & HR).
      pose proof (proj1 (Bignums1_iff len addr xs ma) Harray) as HA.
      apply sep_emp_l in HA. destruct HA as (Hlen & HA).
      seprewrite_in (array_index_nat_inbounds (default:=d) scalar (word.of_Z (bytes_per_word width)) xs addr i Hi) HA.
      rewrite <- List.hd_skipn_nth_default in HA.
      rewrite word.unsigned_of_Z in HA.
      unfold word.wrap in HA. rewrite Z.mod_small in HA by (pose proof Core.bytes_per_word_range; Lia.lia).
      rewrite (Z.mul_comm _ (Z.of_nat i)), <- Haddr in HA.
      rewrite (sep_comm _ _ ma), sep_emp_l in HA. destruct HA as (_ & HA).
      rewrite <- (sep_assoc _ _ _ ma) in HA.
      seprewrite_in sep_comm HA.
      rewrite (sep_assoc _ _ _ ma) in HA.
      assert (exists R', ((scalar addr' (nth_default d xs i)) * R')%sep m) as (R'& HR').
      { exists ((array scalar (word.of_Z (bytes_per_word width)) addr (List.firstn i xs) ⋆ array scalar (word.of_Z (bytes_per_word width)) (word.add addr' (word.of_Z (bytes_per_word width))) (List.skipn (S i) xs)) * R)%sep.
        rewrite <- (sep_assoc _ _ _ m).
        exists ma, mb. split; auto. }
      eapply load_word_of_sep; eauto.
    Qed.

    Lemma Bignums1_store_of_sep:
      forall R len addr addr' i xs m x post,
        (i < length xs)%nat ->
        (Bignums 1 len addr (List.chunk 1 xs) * R)%sep m ->
        addr' = word.add addr (word.of_Z (Z.of_nat i * (bytes_per_word width))) ->
        (forall m', (Bignums 1 len addr (List.chunk 1 (set_nth i x xs)) * R)%sep m' -> post m') ->
        exists m',
          Memory.store access_size.word m addr' x = Some m' /\ post m'.
    Proof.
      intros R len addr addr' i xs m x post Hi Harray Haddr Hpost.
      destruct Harray as (ma & mb & Hsplit & Harray & HR).
      pose proof (proj1 (Bignums1_iff len addr xs ma) Harray) as HA.
      apply sep_emp_l in HA. destruct HA as (Hlen & HA).
      seprewrite_in (array_index_nat_inbounds (default:=word.of_Z 0%Z) scalar (word.of_Z (bytes_per_word width)) xs addr i Hi) HA.
      rewrite <- List.hd_skipn_nth_default in HA.
      rewrite word.unsigned_of_Z in HA.
      unfold word.wrap in HA. rewrite Z.mod_small in HA by (pose proof Core.bytes_per_word_range; Lia.lia).
      rewrite (Z.mul_comm _ (Z.of_nat i)), <- Haddr in HA.
      rewrite (sep_comm _ _ ma), sep_emp_l in HA. destruct HA as (_ & HA).
      rewrite <- (sep_assoc _ _ _ ma) in HA.
      seprewrite_in sep_comm HA.
      rewrite (sep_assoc _ _ _ ma) in HA.
      assert (((scalar addr' (nth_default (word.of_Z 0%Z) xs i)) * ((array scalar (word.of_Z (bytes_per_word width)) addr (List.firstn i xs) ⋆ array scalar (word.of_Z (bytes_per_word width)) (word.add addr' (word.of_Z (bytes_per_word width))) (List.skipn (S i) xs)) * R))%sep m) as HR'.
      { rewrite <- (sep_assoc _ _ _ m).
        exists ma, mb. split; auto. }
      eapply store_word_of_sep; eauto.
      intros m' X; apply Hpost.
      rewrite <- (sep_assoc _ _ _ m') in X.
      destruct X as (ma' & mb' & Hsplit' & XA & XB).
      exists ma', mb'. do 2 (split; auto).
      rewrite (Bignums1_iff len addr _ ma'), sep_emp_l.
      rewrite length_set_nth. split; auto.
      rewrite (array_index_nat_inbounds (default:=word.of_Z 0%Z) scalar (word.of_Z (bytes_per_word width)) (set_nth i x xs) addr i ltac:(rewrite length_set_nth; assumption) ma').
      rewrite <- List.hd_skipn_nth_default, word.unsigned_of_Z.
      unfold word.wrap. rewrite Z.mod_small by (pose proof Core.bytes_per_word_range; Lia.lia).
      rewrite set_nth_nth_default by Lia.lia.
      rewrite NatUtil.eq_nat_dec_refl.
      rewrite (Z.mul_comm _ (Z.of_nat i)), <- Haddr.
      rewrite firstn_set_nth_out_of_bounds by Lia.lia.
      rewrite skipn_set_nth_out_of_bounds by Lia.lia.
      rewrite <- (sep_assoc _ _ _ ma').
      rewrite <- (sep_assoc _ _ _ ma') in XA.
      destruct XA as (? & ? & ? & ? & ?).
      do 2 eexists; do 2 (split; eauto).
      rewrite (sep_comm _ _ _). assumption.
    Qed.
  End Proofs.
End Bignums.
