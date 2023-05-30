Require Import NArith.
Require Import UROP.Types.

Require Import Lia.

Local Open Scope N_scope.

Lemma bit_fact : forall n i,
  N.size n <= i -> N.testbit n i = false.
Proof.
  induction n; simpl; eauto.
  induction p; simpl; destruct i; simpl; try lia;
    intros;
    assert (N.pos (Pos.size p) <= Pos.pred_N p0) by lia;
    pose proof (IHp _ H0);
    eauto.
Qed.

Lemma i_mod_plus_bit : forall i s,
  i < 2 ^ (s + 1)
  -> i mod 2 ^ s + N.b2n (N.testbit i s) * 2 ^ s = i.
Proof.
  intros.
  rewrite N.testbit_eqb.
  destruct (N.ltb i (2 ^ s)) eqn:Hlt.
  - rewrite N.ltb_lt in Hlt.
    rewrite N.mod_small; eauto.
    replace (i / 2 ^ s) with 0; simpl; try rewrite N.div_small; lia.
  - rewrite N.ltb_ge in Hlt.
    rewrite N.mod_eq; try lia.
    replace (i / 2 ^ s) with 1; simpl N.b2n; try lia.
    assert (i / 2 ^ s < 2).
    { apply N.div_lt_upper_bound; try lia.
      rewrite N.mul_comm.
      rewrite <- N.pow_succ_r; lia. }
    assert (i / 2 ^ s > 0).
    { apply N.lt_gt.
      apply N.div_str_pos; lia. }
    lia.
Qed.

Local Close Scope N_scope.
