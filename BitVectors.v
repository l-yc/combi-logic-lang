Require Import NArith.

Require Import Lia.

Require Import UROP.Types.
Require Import UROP.ExtraArith.
Require Import UROP.Tactics.
Require Import UROP.ExtraLists.

Local Open Scope UROP_scope.

Module bv.
  Local Open Scope N_scope.
  Definition zeroes (n : nat) : list N := List.repeat 0 n.

  (* Pos *)
  Local Open Scope positive_scope.
  Compute 1~1~0.
  Fixpoint of_pos (p : positive) : list N :=
    match p with
    | 1 => [1%N]
    | p~0 => 0%N :: of_pos p
    | p~1 => 1%N :: of_pos p
    end.
  Close Scope positive_scope.

  (* N *)
  Local Open Scope N_scope.
  Definition of_N (n : N) : list N :=
    match n with
    | N0 => [0]
    | Npos p => of_pos p
    end.

  Fixpoint to_N (bv : list N) : N :=
    match bv with
    | [] => 0
    | h :: t => (to_N t) * 2 + h
    end.

  Lemma N_bv_equiv : forall n,
    n = to_N (of_N n).
  Proof.
    destruct n; trivial; simpl.
    induction p; simpl; try lia.
  Qed.

  (* zeroes *)
  Lemma zeroes_is_zero : forall n,
    to_N (zeroes n) = 0.
  Proof.
    unfold zeroes.
    induction n; simpl; eauto.
    rewrite IHn; lia.
  Qed.

  (* size *)
  Lemma bv_size_equiv : forall n,
    n <> 0
    -> List.length (of_N n) = N.to_nat (N.size n).
  Proof.
    intros n HP.
    induction n; simpl; try lia.
    induction p; simpl; try lia.
  Qed.

  Lemma N_bv_nz : forall n,
    (List.length (of_N n)) <> 0%nat.
  Proof.
    induction n; simpl; eauto.
    induction p; simpl; eauto.
  Qed.

  Lemma Pos_size : forall n m,
    Pos.le n m -> Pos.le (Pos.size n) (Pos.size m).
  Proof.
    induction n; simpl; try lia; intros;
      induction m; simpl; try lia;
        rewrite <- Pos.succ_le_mono; apply IHn; lia.
  Qed.

  Lemma N_size : forall n m,
    n <= m -> N.size n <= N.size m.
  Proof.
    induction n; simpl; try lia.
    induction m; simpl; try lia.
    apply Pos_size.
  Qed.

  Lemma N_bv_add : forall n m,
    n <> 0 /\ m <> 0
    -> le (List.length (of_N (n + m)))
    ((max (List.length (of_N n)) (List.length (of_N m))) + 1).
  Proof.
    intros.
    rewrite! bv_size_equiv by lia.
    destruct (N.leb n m) eqn:Heq.
    - rewrite N.leb_le in Heq.
      replace (Nat.max (N.to_nat (N.size n)) (N.to_nat (N.size m))) with (N.to_nat (N.max (N.size n) (N.size m))) by lia.

      apply PeanoNat.Nat.le_trans with (m := (N.to_nat (N.size (2 * m + 1)))).
      + rewrite! N.size_log2 by lia.
        assert (N.log2 (n + m) <= N.log2 (2 * m + 1)).
        apply N.log2_le_mono.
        lia.
        lia.
      + rewrite! N.size_log2 by lia.
        rewrite N.log2_succ_double by lia.
        lia.

    - Search (N.leb).
      rewrite N.leb_gt in Heq.
      replace (Nat.max (N.to_nat (N.size n)) (N.to_nat (N.size m))) with (N.to_nat (N.max (N.size n) (N.size m))) by lia.

      apply PeanoNat.Nat.le_trans with (m := (N.to_nat (N.size (2 * n + 1)))).
      + rewrite! N.size_log2 by lia.
        assert (N.log2 (n + m) <= N.log2 (2 * n + 1)).
        apply N.log2_le_mono.
        lia.
        lia.
      + rewrite! N.size_log2 by lia.
        rewrite N.log2_succ_double by lia.
        lia.
  Qed.

  Lemma of_N_spec : forall n d i,
    lt i (N.to_nat (N.size n))
    -> List.nth i (bv.of_N n) d = N.b2n (N.testbit n (N.of_nat i)).
  Proof.
    induction n; simpl.
    inversion 1.

    induction p; simpl; destruct i; simpl; try lia;
    intros;
    assert ((i < Pos.to_nat (Pos.size p))%nat) by lia;
    pose proof (IHp d _ H0);
    rewrite H1;
    f_equal;
    f_equal;
    lia.
  Qed.

  Close Scope N_scope.
End bv.

Module bvM.
  Local Open Scope N_scope.

  (* Conversion {{{ *)
  Definition of_N (m : nat) (n : N) : list N :=
    if Nat.eqb m 0 then []
    else 
      let l := bv.of_N n in
      let len := (List.length l) in
      if Nat.leb len m then List.app l (bv.zeroes (m - len)) else List.firstn m l.

  Lemma of_0 : forall b,
    bvM.of_N b 0 = bv.zeroes b.
  Proof.
    induction b; simpl; eauto.
    assert (S b <> O) by lia.
    unfold of_N; simpl.
    rewrite PeanoNat.Nat.sub_0_r.
    unfold bv.zeroes; eauto.
  Qed.

  Lemma of_N_0 : forall n,
    bvM.of_N 0 n = [].
  Proof.
    eauto.
  Qed.

  Lemma of_N_length : forall n m,
    List.length (bvM.of_N m n) = m.
  Proof.
    induction m; simpl; eauto.
    unfold bvM.of_N.
    assert (Nat.eqb (S m) 0 = false).
    rewrite PeanoNat.Nat.eqb_neq; lia.
    Opaque List.firstn.
    simpl.

    destruct (Nat.leb (Datatypes.length (bv.of_N n)) (S m)) eqn:Hle.
    - apply PeanoNat.Nat.leb_le in Hle; lists.
      unfold bv.zeroes.
      destruct (Datatypes.length (bv.of_N n)); lists.
      rewrite PeanoNat.Nat.add_sub_assoc; lia.
    - destruct (Datatypes.length (bv.of_N n)) eqn:Heq.
      + inversion Hle.
      + apply PeanoNat.Nat.leb_gt in Hle.
        rewrite <- Heq in Hle.
        rewrite List.firstn_length.
        apply min_l; lia.
  Qed.
  Local Hint Rewrite of_N_length : core.

  Lemma of_N_spec : forall i m n d,
    lt i m
    -> List.nth i (bvM.of_N m n) d = N.b2n (N.testbit n (N.of_nat i)).
  Proof.
    intros.
    unfold bvM.of_N.
    destruct (Nat.eqb m 0) eqn:Heq.
    - rewrite PeanoNat.Nat.eqb_eq in Heq; lia.
    - destruct (Nat.leb (Datatypes.length (bv.of_N n)) m) eqn:Hleb.
      + rewrite PeanoNat.Nat.leb_le in Hleb.
        destruct (N.eqb n 0) eqn:HN. 
        * rewrite N.eqb_eq in HN.
          subst; simpl.
          destruct i eqn:Hi; eauto.
          unfold bv.zeroes.
          rewrite List.nth_indep with (d' := 0%N); lists; lia.
        * rewrite N.eqb_neq in HN.
          destruct (Nat.ltb i (List.length (bv.of_N n))) eqn:Hin.
          { rewrite PeanoNat.Nat.ltb_lt in Hin.
            rewrite List.app_nth1; eauto.
            apply bv.of_N_spec.
            rewrite <- bv.bv_size_equiv; lia. }
          { rewrite PeanoNat.Nat.ltb_ge in Hin.
            rewrite List.app_nth2; eauto.

            unfold bv.zeroes.
            rewrite List.nth_indep with (d' := 0%N); lists; try lia.
            rewrite bit_fact; simpl; try lia.
            rewrite bv.bv_size_equiv in Hin; lia. }
      + rewrite PeanoNat.Nat.leb_gt in Hleb.
        destruct (N.eqb n 0) eqn:HN. 
        * rewrite N.eqb_eq in HN.
          subst; simpl.
          simpl in Hleb; lia.
        * rewrite N.eqb_neq in HN.
          rewrite list_fact; try lia.
          apply bv.of_N_spec.
          rewrite bv.bv_size_equiv in Hleb; try lia.
  Qed.

  Lemma of_N_succ : forall m n,
    bvM.of_N (S m) n = List.app (bvM.of_N m n) [N.b2n (N.testbit n (N.of_nat m))].
  Proof.
    intros.
    eapply List.nth_ext; lists; simplify.
    - lia.
    - intros.
      destruct (Nat.ltb n0 m) eqn:ineq.
      + rewrite PeanoNat.Nat.ltb_lt in ineq.
        rewrite List.app_nth1; try reflexivity.
        rewrite! bvM.of_N_spec; eauto.
        rewrite bvM.of_N_length; lia.
      + rewrite PeanoNat.Nat.ltb_ge in ineq.
        assert (n0 = m) by lia; subst.
        rewrite List.app_nth2; rewrite bvM.of_N_length; try lia.
        rewrite! bvM.of_N_spec; eauto.
        replace (m - m)%nat with O by lia; eauto.
    Unshelve.
    all: eauto.
  Qed.
  (* }}} *)

  (* L-Shifting {{{ *)
  Definition shiftl (n : nat) (l : list N) :=
    List.firstn (List.length l) (List.app (List.repeat 0 n) l).

  Lemma firstn_firstn_repeat : forall l l' x a b,
    (a = List.length l)%nat ->
    (a <= b)%nat ->
    List.firstn a (List.app (List.repeat 0 x) l)
    = List.firstn a (List.firstn b (List.app (List.repeat 0 x) (l ++l l'))).
  Proof.
    induction l; simpl; intros; unfold shiftl; lists; rewrite List.firstn_firstn.
    - subst; lists.
    - replace (Nat.min a0 b) with a0 by lia; lists.
      rewrite! List.firstn_app.
      f_equal; lists.
      replace (a :: (l ++l l')) with (a :: l ++l l') by eauto.
      rewrite List.firstn_app with (l2 := l'); lists.
      replace (a0 - x - S (Datatypes.length l))%nat with O; lists; lia.
  Qed.

  Lemma shiftl_length_equiv : forall s b n,
    shiftl (Nat.pow 2 s) (bvM.of_N b n) =
    List.firstn b
      (shiftl (Nat.pow 2 s)
         (bvM.of_N b n ++l [N.b2n (N.testbit n (N.of_nat b))])).
  Proof.
    intros.
    unfold shiftl; lists.
    rewrite bvM.of_N_length; lists.
    eapply firstn_firstn_repeat; lists; try rewrite bvM.of_N_length; try lia.
  Qed.

  Lemma shiftl_length : forall x b n,
    Datatypes.length (bvM.shiftl x (bvM.of_N b n)) = b.
  Proof.
    intros.
    unfold bvM.shiftl; lists.
    rewrite of_N_length; lia.
  Qed.

  Lemma shiftl_correct : forall x b n,
    bvM.shiftl x (bvM.of_N b n) = bvM.of_N b (N.shiftl n (N.of_nat x)).
  Proof.
    intros.
    apply List.nth_ext with (d := 0) (d' := 0); lists; rewrite shiftl_length.
    - rewrite of_N_length; eauto.
    - intros.
      unfold bvM.shiftl; rewrite list_fact; lists; try rewrite of_N_length; try lia.
      rewrite bvM.of_N_spec; try lia.

      assert (Hnx: lt n0 x \/ ge n0 x) by lia; destruct Hnx.
      + rewrite N.shiftl_spec_low; lists; try lia.
        rewrite List.app_nth1; lists.
      + rewrite N.shiftl_spec_high; lists; try lia.
        rewrite List.app_nth2; lists.
        rewrite bvM.of_N_spec; eauto; try lia.
        do 2 f_equal; lia.
  Qed.

  (* need a lemma here about N_to_bvM being modulo *)
  Lemma of_N_is_mod : forall s n n',
    n mod 2 ^ N.of_nat s = n' mod 2 ^ N.of_nat s
    -> bvM.of_N s n = bvM.of_N s n'.
  Proof.
    intros.
    apply List.nth_ext with (d := 0) (d' := 0); try rewrite! of_N_length; lists.

    intros; rewrite! bvM.of_N_spec; eauto.

    rewrite <- N.mod_pow2_bits_low with (n := (N.of_nat s)) by lia.
    rewrite <- N.mod_pow2_bits_low with (n := (N.of_nat s)) (a := n') by lia.
    rewrite H; eauto.
  Qed.

  (*H0 : i < N.pos (2 ^ Pos.of_succ_nat s)
     bvM.of_N s (i mod 2 ^ N.of_nat s) = bvM.of_N s i*)

  (* }}} *)
End bvM.

Close Scope UROP_scope.
