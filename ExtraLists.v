Require Import NArith.
Require Import UROP.Types.
Require Import Lia.

Local Open Scope UROP_scope.

Ltac simplify_list :=
  try match goal with
  | [|- context[Datatypes.length (List.map _ _)]] => rewrite List.map_length
  | [|- context[Datatypes.length (List.repeat _ _)]] => rewrite List.repeat_length
  | [|- context[List.firstn 0 _]] => rewrite List.firstn_O
  | [|- context[_ ++l []]] => rewrite List.app_nil_r
  | [|- context[List.length (List.firstn _ _)]] => rewrite List.firstn_length
  | [|- context[Datatypes.length (_ ++l _)]] => rewrite List.app_length
  | [H: (_ < 0)%nat |- _] => inversion H
  | [|- context[List.firstn (S _) (_ :: _)]] => rewrite List.firstn_cons
  | [|- context[List.skipn (S _) (_ :: _)]] => rewrite List.skipn_cons
  | [|- context[List.nth _ (List.repeat _ _) _]] => rewrite List.nth_repeat
  (*| [|- context[List.firstn _ (_ ++l _)]] => rewrite List.firstn_app*)
  | _ => idtac
  end; simpl; eauto.

Ltac lists := repeat simplify_list.

(* List Helper Lemmas {{{ *)
Lemma list_fact {A} : forall n m (l : list A) d,
  lt n m
  -> ge (List.length l) m
  -> List.nth n (List.firstn m l) d = List.nth n l d.
Proof.
  intros.
  replace (List.nth n l d) with (List.nth n (List.firstn m l ++l List.skipn m l) d).
  Search (List.nth).
  rewrite List.app_nth1; eauto.
  rewrite List.firstn_length; lia.
  rewrite List.firstn_skipn; eauto.
Qed.

Lemma rev_rev {A} : forall (l : list A),
  List.NoDup (List.rev l) -> List.NoDup l.
Proof.
  intros.
  apply List.NoDup_rev in H.
  rewrite List.rev_involutive in H.
  assumption.
Qed.

Open Scope list_scope.
Lemma zip_app {A} {B} : forall (a1 : list A) (b1 : list B) a2 b2,
  List.length a1 = List.length b1
  -> zip (a1 ++ a2) (b1 ++ b2) = zip a1 b1 ++ zip a2 b2.
Proof.
  induction a1; induction b1; eauto.
  inversion 1.
  inversion 1.
  intros; simpl.
  f_equal.
  eauto.
Qed.

Lemma zip_length {A} {B} : forall (a : list A) (b : list B),
  List.length (zip a b) = Nat.min (List.length a) (List.length b).
Proof.
  induction a; induction b; simpl; eauto.
Qed.
Close Scope list_scope.

Lemma list_firstn_skipn_succ : forall A (l : list A) i d,
  lt i (List.length l) ->
  List.skipn i (List.firstn (i+1) l) = [List.nth i l d].
Proof.
  induction l.
  inversion 1.

  lists.
  intros.
  destruct i.
  lists.
  replace ((S i + 1)%nat) with (S (i + 1)) by lia.
  lists.
  apply IHl.
  lia.
Qed.

Lemma list_firstn_succ : forall A (l : list A) i d,
  lt i (List.length l) ->
  List.firstn (S i) l = (List.firstn i l ++l [List.nth i l d]).
Proof.
  induction l.
  inversion 1.

  lists.
  intros.
  destruct i.
  lists.
  replace ((S i + 1)%nat) with (S (i + 1)) by lia.
  lists.
  f_equal.
  apply IHl.
  lia.
Qed.
(* }}} *)
