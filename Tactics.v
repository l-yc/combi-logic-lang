Require Import NArith.
Require Import UROP.Types.
Require Import UROP.ExtraLists.
(*Require Import UROP.BitVectors.*)

Local Open Scope UROP_scope.

Ltac all_branches :=
  repeat match goal with
  (*| [ |- context[match ?e with | Ok _ => _ | Err _ => _ end] ] => destruct e eqn:?*)
  | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
  end.

Ltac propositional :=
  repeat match goal with
  | [H: _ /\ _ |- _] => inversion H; clear H
  end.

Ltac simplify := autorewrite with core; simpl.

(*Local Hint Rewrite N_to_bvM_length : core.
   Local Hint Rewrite var_names_length : core.*)
