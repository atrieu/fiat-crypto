Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.NTT.BedrockNTT.
Require Import Crypto.NTT.BedrockBarrettReduction.
Require Import bedrock2.BasicC64Semantics.
Require Import Rupicola.Lib.Core.
Require Import bedrock2.ToCString.
From Coqprime.PrimalityTest Require Import Pocklington PocklingtonCertificat.

Section Zetas.
  Context {q: positive} {zeta: F q}.

  (* Computes the list of ζ^0 to ζ^n, hence the length is (n + 1) *)
  Fixpoint make_zetas (n: nat): list (F q) :=
    match n with
    | O => [1%F]
    | S n => 1%F::(List.map (F.mul zeta) (make_zetas n))
    end.

  Lemma make_zetas_spec n:
    forall k, (k <= n)%nat ->
         nth_error (make_zetas n) k = Some (F.pow zeta (N.of_nat k)).
  Proof.
    induction n; intros.
    - assert (k = 0)%nat as -> by Lia.lia. simpl.
      rewrite ModularArithmeticTheorems.F.pow_0_r. reflexivity.
    - simpl. destruct k.
      + simpl. rewrite ModularArithmeticTheorems.F.pow_0_r. reflexivity.
      + simpl. rewrite nth_error_map.
        rewrite IHn by Lia.lia. simpl.
        rewrite <- ModularArithmeticTheorems.F.pow_succ_r.
        assert (N.succ (N.of_nat k) = N.pos (Pos.of_succ_nat k)) as -> by Lia.lia.
        reflexivity.
  Qed.

  Lemma make_zetas_length n:
    length (make_zetas n) = S n.
  Proof.
    induction n; [reflexivity|].
    simpl. rewrite length_map, IHn. reflexivity.
  Qed.
End Zetas.

Section Fast_Decompose.
  (* Use N instead of Nat for faster computation *)
  Context {m: nat}.
  Fixpoint fast_decompose i (l: N): list N :=
    match i with
    | O => [l]
    | S i => (fast_decompose i (N.div l 2%N)) ++ (fast_decompose i (N.pow 2 (N.of_nat m) + N.div l 2)%N)
    end.

  Lemma fast_decompose_spec:
    forall i l, fast_decompose i l = List.map N.of_nat (@NTT.decompose m i (N.to_nat l)).
  Proof.
    induction i; intros l; cbn.
    - rewrite Nnat.N2Nat.id. reflexivity.
    - unfold NTT.decompose_body'. rewrite List.map_app.
      do 2 rewrite IHi. f_equal.
      + f_equal. f_equal.
        rewrite Nnat.N2Nat.inj_div.
        f_equal; reflexivity.
      + f_equal. f_equal.
        rewrite Nnat.N2Nat.inj_add, Nnat.N2Nat.inj_div, Nnat.N2Nat.inj_pow.
        rewrite Nnat.Nat2N.id.
        reflexivity.
  Qed.

  Fixpoint fast_zeta_powers (i: nat) (l: N): list N :=
    match i with
    | O => [l]
    | S i => (fast_zeta_powers i l) ++ List.map (fun k => nth_default 0%N (fast_decompose (S i) l) (2 * k)) (seq 0 (Nat.pow 2 i))
    end.

  Lemma fast_zeta_powers_spec:
    forall i l,
      fast_zeta_powers i l = List.map N.of_nat (@GallinaNTT.zeta_powers m (N.to_nat l) i).
  Proof.
    induction i; intros l.
    - cbn. rewrite Nnat.N2Nat.id. reflexivity.
    - cbn -[fast_decompose NTT.decompose].
      rewrite List.map_app, IHi. f_equal.
      rewrite fast_decompose_spec, List.map_map.
      apply List.map_ext.
      intros. assert (0%N = N.of_nat 0%nat) as -> by reflexivity.
      rewrite ListUtil.map_nth_default_always. reflexivity.
  Qed.
End Fast_Decompose.

Section FNDSA1024.
  Local Notation q := 12289%positive.
  Local Notation F := (F q).
  Local Notation zeta := (F.of_Z q 7%Z).
  Local Notation n := 10%nat.
  Local Notation m := 10%nat.
  Local Notation add := "fndsa_felem_add".
  Local Notation sub := "fndsa_felem_sub".
  Local Notation mul := "fndsa_felem_mul".
  Local Notation reduce := "fndsa_barrett_reduce".
  Local Notation reduce_small := "fndsa_barrett_reduce_small".

  Local Notation fndsa_make_zetas := (@make_zetas q zeta).

  Local Notation firstn := List.firstn.
  Local Notation skipn := List.skipn.

  (* Sanity check *)
  Lemma fndsa_prime_q: prime (Z.pos q).
  Proof.
    apply (Pocklington_refl
             (Pock_certif 12289 11 ((2,12)::nil)%positive 1)
             ((Proof_certif 2 prime_2) ::
                nil)).
    native_cast_no_check (refl_equal true).
  Qed.

  (* (* ζ^0 to ζ^1024 *) *)
  Definition fndsa_zetas_1024 :=
    [1; 7; 49; 343; 2401; 4518; 7048; 180; 1260; 8820; 295; 2065; 2166; 2873; 7822;
     5598; 2319; 3944; 3030; 8921; 1002; 7014; 12231; 11883; 9447; 4684; 8210;
     8314; 9042; 1849; 654; 4578; 7468; 3120; 9551; 5412; 1017; 7119; 677; 4739;
     8595; 11009; 3329; 11014; 3364; 11259; 5079; 10975; 3091; 9348; 3991; 3359;
     11224; 4834; 9260; 3375; 11336; 5618; 2459; 4924; 9890; 7785; 5339; 506; 3542;
     216; 1512; 10584; 354; 2478; 5057; 10821; 2013; 1802; 325; 2275; 3636; 874;
     6118; 5959; 4846; 9344; 3963; 3163; 9852; 7519; 3477; 12050; 10616; 578; 4046;
     3744; 1630; 11410; 6136; 6085; 5728; 3229; 10314; 10753; 1537; 10759; 1579;
     11053; 3637; 881; 6167; 6302; 7247; 1573; 11011; 3343; 11112; 4050; 3772;
     1826; 493; 3451; 11868; 9342; 3949; 3065; 9166; 2717; 6730; 10243; 10256;
     10347; 10984; 3154; 9789; 7078; 390; 2730; 6821; 10880; 2426; 4693; 8273;
     8755; 12129; 11169; 4449; 6565; 9088; 2171; 2908; 8067; 7313; 2035; 1956;
     1403; 9821; 7302; 1958; 1417; 9919; 7988; 6760; 10453; 11726; 8348; 9280;
     3515; 27; 189; 1323; 9261; 3382; 11385; 5961; 4860; 9442; 4649; 7965; 6599;
     9326; 3837; 2281; 3678; 1168; 8176; 8076; 7376; 2476; 5043; 10723; 1327; 9289;
     3578; 468; 3276; 10643; 767; 5369; 716; 5012; 10506; 12097; 10945; 2881; 7878;
     5990; 5063; 10863; 2307; 3860; 2442; 4805; 9057; 1954; 1389; 9723; 6616; 9445;
     4670; 8112; 7628; 4240; 5102; 11136; 4218; 4948; 10058; 8961; 1282; 8974;
     1373; 9611; 5832; 3957; 3121; 9558; 5461; 1360; 9520; 5195; 11787; 8775;
     12269; 12149; 11309; 5429; 1136; 7952; 6508; 8689; 11667; 7935; 6389; 7856;
     5836; 3985; 3317; 10930; 2776; 7143; 845; 5915; 4538; 7188; 1160; 8120; 7684;
     4632; 7846; 5766; 3495; 12176; 11498; 6752; 10397; 11334; 5604; 2361; 4238;
     5088; 11038; 3532; 146; 1022; 7154; 922; 6454; 8311; 9021; 1702; 11914; 9664;
     6203; 6554; 9011; 1632; 11424; 6234; 6771; 10530; 12265; 12121; 11113; 4057;
     3821; 2169; 2894; 7969; 6627; 9522; 5209; 11885; 9461; 4782; 8896; 827; 5789;
     3656; 1014; 7098; 530; 3710; 1392; 9744; 6763; 10474; 11873; 9377; 4194; 4780;
     8882; 729; 5103; 11143; 4267; 5291; 170; 1190; 8330; 9154; 2633; 6142; 6127;
     6022; 5287; 142; 994; 6958; 11839; 9139; 2528; 5407; 982; 6874; 11251; 5023;
     10583; 347; 2429; 4714; 8420; 9784; 7043; 145; 1015; 7105; 579; 4053; 3793;
     1973; 1522; 10654; 844; 5908; 4489; 6845; 11048; 3602; 636; 4452; 6586; 9235;
     3200; 10111; 9332; 3879; 2575; 5736; 3285; 10706; 1208; 8456; 10036; 8807;
     204; 1428; 9996; 8527; 10533; 12286; 12268; 12142; 11260; 5086; 11024; 3434;
     11749; 8509; 10407; 11404; 6094; 5791; 3670; 1112; 7784; 5332; 457; 3199;
     10104; 9283; 3536; 174; 1218; 8526; 10526; 12237; 11925; 9741; 6742; 10327;
     10844; 2174; 2929; 8214; 8342; 9238; 3221; 10258; 10361; 11082; 3840; 2302;
     3825; 2197; 3090; 9341; 3942; 3016; 8823; 316; 2212; 3195; 10076; 9087; 2164;
     2859; 7724; 4912; 9806; 7197; 1223; 8561; 10771; 1663; 11641; 7753; 5115;
     11227; 4855; 9407; 4404; 6250; 6883; 11314; 5464; 1381; 9667; 6224; 6701;
     10040; 8835; 400; 2800; 7311; 2021; 1858; 717; 5019; 10555; 151; 1057; 7399;
     2637; 6170; 6323; 7394; 2602; 5925; 4608; 7678; 4590; 7552; 3708; 1378; 9646;
     6077; 5672; 2837; 7570; 3834; 2260; 3531; 139; 973; 6811; 10810; 1936; 1263;
     8841; 442; 3094; 9369; 4138; 4388; 6138; 6099; 5826; 3915; 2827; 7500; 3344;
     11119; 4099; 4115; 4227; 5011; 10499; 12048; 10602; 480; 3360; 11231; 4883;
     9603; 5776; 3565; 377; 2639; 6184; 6421; 8080; 7404; 2672; 6415; 8038; 7110;
     614; 4298; 5508; 1689; 11823; 9027; 1744; 12208; 11722; 8320; 9084; 2143;
     2712; 6695; 9998; 8541; 10631; 683; 4781; 8889; 778; 5446; 1255; 8785; 50;
     350; 2450; 4861; 9449; 4698; 8308; 9000; 1555; 10885; 2461; 4938; 9988; 8471;
     10141; 9542; 5349; 576; 4032; 3646; 944; 6608; 9389; 4278; 5368; 709; 4963;
     10163; 9696; 6427; 8122; 7698; 4730; 8532; 10568; 242; 1694; 11858; 9272;
     3459; 11924; 9734; 6693; 9984; 8443; 9945; 8170; 8034; 7082; 418; 2926; 8193;
     8195; 8209; 8307; 8993; 1506; 10542; 60; 420; 2940; 8291; 8881; 722; 5054;
     10800; 1866; 773; 5411; 1010; 7070; 334; 2338; 4077; 3961; 3149; 9754; 6833;
     10964; 3014; 8809; 218; 1526; 10682; 1040; 7280; 1804; 339; 2373; 4322; 5676;
     2865; 7766; 5206; 11864; 9314; 3753; 1693; 11851; 9223; 3116; 9523; 5216;
     11934; 9804; 7183; 1125; 7875; 5969; 4916; 9834; 7393; 2595; 5876; 4265; 5277;
     72; 504; 3528; 118; 826; 5782; 3607; 671; 4697; 8301; 8951; 1212; 8484; 10232;
     10179; 9808; 7211; 1321; 9247; 3284; 10699; 1159; 8113; 7635; 4289; 5445;
     1248; 8736; 11996; 10238; 10221; 10102; 9269; 3438; 11777; 8705; 11779; 8719;
     11877; 9405; 4390; 6152; 6197; 6512; 8717; 11863; 9307; 3704; 1350; 9450;
     4705; 8357; 9343; 3956; 3114; 9509; 5118; 11248; 5002; 10436; 11607; 7515;
     3449; 11854; 9244; 3263; 10552; 130; 910; 6370; 7723; 4905; 9757; 6854; 11111;
     4043; 3723; 1483; 10381; 11222; 4820; 9162; 2689; 6534; 8871; 652; 4564; 7370;
     2434; 4749; 8665; 11499; 6759; 10446; 11677; 8005; 6879; 11286; 5268; 9; 63;
     441; 3087; 9320; 3795; 1987; 1620; 11340; 5646; 2655; 6296; 7205; 1279; 8953;
     1226; 8582; 10918; 2692; 6555; 9018; 1681; 11767; 8635; 11289; 5289; 156;
     1092; 7644; 4352; 5886; 4335; 5767; 3502; 12225; 11841; 9153; 2626; 6093;
     5784; 3621; 769; 5383; 814; 5698; 3019; 8844; 463; 3241; 10398; 11341; 5653;
     2704; 6639; 9606; 5797; 3712; 1406; 9842; 7449; 2987; 8620; 11184; 4554; 7300;
     1944; 1319; 9233; 3186; 10013; 8646; 11366; 5828; 3929; 2925; 8186; 8146;
     7866; 5906; 4475; 6747; 10362; 11089; 3889; 2645; 6226; 6715; 10138; 9521;
     5202; 11836; 9118; 2381; 4378; 6068; 5609; 2396; 4483; 6803; 10754; 1544;
     10808; 1922; 1165; 8155; 7929; 6347; 7562; 3778; 1868; 787; 5509; 1696; 11872;
     9370; 4145; 4437; 6481; 8500; 10344; 10963; 3007; 8760; 12164; 11414; 6164;
     6281; 7100; 544; 3808; 2078; 2257; 3510; 12281; 12233; 11897; 9545; 5370; 723;
     5061; 10849; 2209; 3174; 9929; 8058; 7250; 1594; 11158; 4372; 6026; 5315; 338;
     2366; 4273; 5333; 464; 3248; 10447; 11684; 8054; 7222; 1398; 9786; 7057; 243;
     1701; 11907; 9615; 5860; 4153; 4493; 6873; 11244; 4974; 10240; 10235; 10200;
     9955; 8240; 8524; 10512; 12139; 11239; 4939; 9995; 8520; 10484; 11943; 9867;
     7624; 4212; 4906; 9764; 6903; 11454; 6444; 8241; 8531; 10561; 193; 1351; 9457;
     4754; 8700; 11744; 8474; 10162; 9689; 6378; 7779; 5297; 212; 1484; 10388;
     11271; 5163; 11563; 7207; 1293; 9051; 1912; 1095; 7665; 4499; 6915; 11538;
     7032; 68; 476; 3332; 11035; 3511; -1].

  (* How to make proof faster ??? *)
  Lemma fndsa_zetas_1024_spec:
    forall k x, nth_error fndsa_zetas_1024 k = Some x ->
           F.of_Z q x = F.pow zeta (N.of_nat k).
  Proof.
    assert (Hsplit: forall n l, length l = Nat.pow 2 (S n) ->
                       (forall k x, nth_error (firstn (Nat.pow 2 n) l) k = Some x -> F.of_Z q x = F.pow zeta (N.of_nat (S k))) ->
                       (let y := nth_default 0%Z (firstn (Nat.pow 2 n) l) ((Nat.pow 2 n) - 1) in forall k x1 x2, nth_error (firstn (Nat.pow 2 n) l) k = Some x1 -> nth_error (skipn (Nat.pow 2 n) l) k = Some x2 -> F.of_Z q x2 = F.of_Z q (y * x1)) ->
                       (forall k x, nth_error l k = Some x -> F.of_Z q x = F.pow zeta (N.of_nat (S k)))).
    { intros n l Hlen IHl IHr k x Hx. generalize (ListUtil.nth_error_value_length _ _ _ _ Hx).
      rewrite Hlen; intros X.
      destruct (lt_dec k (Nat.pow 2 n)) as [Hk|Hk].
      - rewrite <- (nth_error_firstn _ _ _ Hk) in Hx.
        apply IHl; auto.
      - set (k' := (k - Nat.pow 2 n)%nat).
        assert (Hx2: nth_error (skipn (Nat.pow 2 n) l) k' = Some x) by (rewrite ListUtil.nth_error_skipn, <- Hx; f_equal; Lia.lia).
        assert (Hlen': length (firstn (Nat.pow 2 n) l) = Nat.pow 2 n) by (rewrite length_firstn, Hlen; Lia.lia).
        rewrite PeanoNat.Nat.pow_succ_r' in X.
        destruct (ListUtil.nth_error_length_exists_value k' (firstn (Nat.pow 2 n) l) ltac:(Lia.lia)) as [x1 Hx1].
        erewrite IHr; eauto.
        rewrite ModularArithmeticTheorems.F.of_Z_mul.
        rewrite (IHl _ _ Hx1).
        generalize (ListUtil.nth_error_Some_nth_default ((Nat.pow 2 n) - 1)%nat 0%Z (firstn (Nat.pow 2 n) l) ltac:(Lia.lia)). intro Hy.
        rewrite (IHl _ _ Hy).
        rewrite <- ModularArithmeticTheorems.F.pow_add_r, <- Nnat.Nat2N.inj_add.
        do 2 f_equal. Lia.lia. }
    assert (Hstrong: forall l,
               (forall x0,
                   nth_error l 0%nat = Some x0 -> F.of_Z _ x0 = zeta) ->
               (forall k x1 x2,
                   nth_error l k = Some x1 ->
                   nth_error l (S k) = Some x2 ->
                   F.of_Z q x2 = F.mul zeta (F.of_Z q x1)) ->
               (forall k x,
                   nth_error l k = Some x -> F.of_Z _ x = (zeta ^ N.of_nat (S k))%F)).
    { intros l H0 HS. induction k; intros x Hx.
      - apply H0 in Hx. rewrite Hx. rewrite ModularArithmeticTheorems.F.pow_1_r; reflexivity.
      - destruct (ListUtil.nth_error_length_exists_value k l ltac:(apply ListUtil.nth_error_value_length in Hx; Lia.lia)) as [x1 Hx1].
        erewrite HS; eauto. rewrite (IHk _ Hx1).
        rewrite <- ModularArithmeticTheorems.F.pow_succ_r; reflexivity. }
    destruct k.
    - intros x Hx. cbv in Hx. inversion Hx; subst x; clear Hx.
      rewrite ModularArithmeticTheorems.F.pow_0_r. reflexivity.
    - revert k.
      unfold fndsa_zetas_1024. intros k x. rewrite nth_error_cons.
      revert k x.
      apply (Hsplit 9%nat); [reflexivity|..]; cbn.
      { apply (Hsplit 8%nat); [reflexivity|..]; cbn.
        { apply (Hsplit 7%nat); [reflexivity|..]; cbn.
          { apply (Hsplit 6%nat); [reflexivity|..]; cbn.
            { apply Hstrong.
              - simpl. intros x0 Hx0; inversion Hx0; subst x0; clear Hx0.
                reflexivity.
              - intros k x1 x2 Hx1 Hx2.
                do 64 (destruct k; cbn in Hx1, Hx2; [inversion Hx1; subst x1; inversion Hx2; subst x2; clear Hx1 Hx2; rewrite <- ModularArithmeticTheorems.F.of_Z_mul; apply ModularArithmeticTheorems.F.eq_of_Z_iff; reflexivity|]).
                inversion Hx2. }
            { cbn. intros k x1 x2 Hx1 Hx2.
              do 64 (destruct k; cbn in Hx1, Hx2; [inversion Hx1; subst x1; inversion Hx2; subst x2; clear Hx1 Hx2; apply ModularArithmeticTheorems.F.eq_of_Z_iff; reflexivity|]).
              rewrite nth_error_nil in Hx1. inversion Hx1. } }
          { cbn. intros k x1 x2 Hx1 Hx2.
            do 128 (destruct k; cbn in Hx1, Hx2; [inversion Hx1; subst x1; inversion Hx2; subst x2; clear Hx1 Hx2; apply ModularArithmeticTheorems.F.eq_of_Z_iff; reflexivity|]).
            rewrite nth_error_nil in Hx1. inversion Hx1. } }
        { cbn. intros k x1 x2 Hx1 Hx2.
          do 256 (destruct k; cbn in Hx1, Hx2;[inversion Hx1; subst x1; inversion Hx2; subst x2; clear Hx1 Hx2; apply ModularArithmeticTheorems.F.eq_of_Z_iff; reflexivity|]).
          rewrite nth_error_nil in Hx1. inversion Hx1. } }
      { cbn. intros k x1 x2 Hx1 Hx2.
        do 512 (destruct k; cbn in Hx1, Hx2; [inversion Hx1; subst x1; inversion Hx2; subst x2; clear Hx1 Hx2; apply ModularArithmeticTheorems.F.eq_of_Z_iff; reflexivity|]).
        rewrite nth_error_nil in Hx1. inversion Hx1. }
  Qed.

  (* Sanity check ζ^(2^m) = -1 *)
  Lemma fndsa1024_zeta_m_ok:
    F.pow zeta (N.of_nat (Nat.pow 2 m)) = F.of_Z _ (-1).
  Proof.
    erewrite <- fndsa_zetas_1024_spec; [reflexivity|].
    cbn. reflexivity.
  Qed.

  Definition fndsa1024_zetas := List.map (fun k => nth_default 0%F (List.map (F.of_Z q) fndsa_zetas_1024) (N.to_nat k)) (@fast_zeta_powers m m (N.pow 2 (N.of_nat m))).

  Lemma fndsa1024_zetas_correct:
    fndsa1024_zetas = List.map (fun k => F.pow zeta (N.of_nat k)) (@GallinaNTT.zeta_powers m (Nat.pow 2 m) m).
  Proof.
    unfold fndsa1024_zetas.
    rewrite fast_zeta_powers_spec, List.map_map.
    rewrite Nnat.N2Nat.inj_pow, Nnat.Nat2N.id.
    apply nth_error_ext. intros.
    do 2 rewrite nth_error_map.
    destruct (nth_error (GallinaNTT.zeta_powers _ _) i) as [k|] eqn:Hk; [|reflexivity].
    cbn [option_map].
    f_equal. unfold F.zero.
    rewrite ListUtil.map_nth_default_always.
    rewrite Nnat.Nat2N.id.
    rewrite (fndsa_zetas_1024_spec k (nth_default 0 fndsa_zetas_1024 k)); [reflexivity|].
    apply ListUtil.nth_error_Some_nth_default.
    cbn. assert (k <= Nat.pow 2 m)%nat as Hkm; [|cbn in Hkm; Lia.lia].
    apply nth_error_In in Hk.
    apply GallinaNTT.In_zeta_powers in Hk; Lia.lia.
  Qed.

  Definition fndsa_c: F := F.of_Z _ 12277.

  Lemma fndsa_c_correct:
    fndsa_c = F.inv (F.pow (1 + 1)%F (N.of_nat (Nat.min m n))).
  Proof.
    apply ModularArithmeticTheorems.F.eq_to_Z_iff.
    reflexivity.
  Qed.

  Definition fndsa1024_ntt := @br2_ntt 64 (Naive.word _) q n m fndsa1024_zetas word_of_F add sub mul.
  Definition fndsa1024_inverse_ntt := @br2_ntt_inverse 64 (Naive.word _) q n m fndsa_c fndsa1024_zetas word_of_F add sub mul.

  Definition fndsa_barrett_reduce_small := @reduce_small_br2fn q.
  Definition fndsa_barrett_reduce := @reduce_br2fn q.
  Definition fndsa_felem_add := @add_br2fn reduce_small.
  Definition fndsa_felem_sub := @sub_br2fn q reduce_small.
  Definition fndsa_felem_mul := @mul_br2fn reduce.

  Definition fndsa_funcs :=
    [ ("fndsa1024_ntt", fndsa1024_ntt)
    ; ("fndsa1024_inverse_ntt", fndsa1024_inverse_ntt)
    ; (reduce_small, fndsa_barrett_reduce_small)
    ; (reduce, fndsa_barrett_reduce)
    ; (add, fndsa_felem_add)
    ; (sub, fndsa_felem_sub)
    ; (mul, fndsa_felem_mul)
    ].

  Lemma fndsa_reduce_small_ok:
    @spec_of_reduce_small _ _ _ _ _ _ q reduce_small (map.of_list fndsa_funcs).
  Proof.
    assert (3 <= Z.pos q) as Hle by Lia.lia.
    apply (reduce_small_br2fn_ok (modulus_not_2:=Hle)); reflexivity.
  Qed.

  Lemma fndsa_felem_add_ok:
    @spec_of_add _ _ _ _ _ _ _ q add (map.of_list fndsa_funcs).
  Proof.
    apply (add_br2fn_ok (modulus_pos:=q) (modulus_not_2:=ltac:(Lia.lia)) (reduce_small_name:=reduce_small)).
    - compute. reflexivity.
    - reflexivity.
    - apply fndsa_reduce_small_ok.
  Qed.

  Lemma fndsa_felem_sub_ok:
    @spec_of_sub _ _ _ _ _ _ _ q sub (map.of_list fndsa_funcs).
  Proof.
    apply (sub_br2fn_ok (modulus_pos:=q) (modulus_not_2:=ltac:(Lia.lia)) (reduce_small_name:=reduce_small)).
    - compute. reflexivity.
    - reflexivity.
    - apply fndsa_reduce_small_ok.
  Qed.

  Lemma fndsa_reduce_ok:
    @spec_of_reduce _ _ _ _ _ _ q reduce (map.of_list fndsa_funcs).
  Proof.
    apply (reduce_br2fn_ok (modulus_pos:=q) (modulus_prime:=fndsa_prime_q) (modulus_not_2:=ltac:(Lia.lia))); auto.
    cbv. reflexivity.
  Qed.

  Lemma fndsa_felem_mul_ok:
    @spec_of_mul _ _ _ _ _ _ _ q mul (map.of_list fndsa_funcs).
  Proof.
    apply (mul_br2fn_ok (modulus_pos:=q) (modulus_prime:=fndsa_prime_q) (modulus_not_2:=ltac:(Lia.lia)) (reduce_name:=reduce)); try reflexivity.
    apply fndsa_reduce_ok.
  Qed.

  Lemma fndsa1024_ntt_ok:
    @spec_of_ntt _ _ _ _ _ _ "fndsa1024_ntt" q n m fndsa1024_zetas feval (map.of_list fndsa_funcs).
  Proof.
    eapply (br2_ntt_ok fndsa_c fndsa1024_zetas fndsa_c_correct).
    2-4: cbn; Lia.lia.
    - eapply feval_ok. cbn. Lia.lia.
    - reflexivity.
    - apply fndsa_felem_mul_ok.
    - apply fndsa_felem_sub_ok.
    - apply fndsa_felem_add_ok.
    Unshelve. Lia.lia.
  Qed.

  Lemma fndsa1024_inverse_ntt_ok:
    @spec_of_ntt_inverse _ _ _ _ _ _ "fndsa1024_inverse_ntt" q n m fndsa1024_zetas feval (map.of_list fndsa_funcs).
  Proof.
    eapply (br2_ntt_inverse_ok fndsa_c fndsa1024_zetas fndsa_c_correct).
    2-4: cbn; Lia.lia.
    - eapply feval_ok. cbn. Lia.lia.
    - reflexivity.
    - apply fndsa_felem_mul_ok.
    - apply fndsa_felem_sub_ok.
    - apply fndsa_felem_add_ok.
      Unshelve. Lia.lia.
  Qed.

  Time Eval compute in ToCString.c_module fndsa_funcs.
End FNDSA1024.
