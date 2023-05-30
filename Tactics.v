Require Import NArith.
Require Import UROP.Types.
(*Require Import UROP.BitVectors.*)

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
  (*| [|- context[List.firstn 0 _]] => rewrite List.firstn_O*)
  | _ => idtac
  end; simpl; eauto.

Ltac lists := repeat simplify_list.

(*Local Hint Rewrite N_to_bvM_length : core.
   Local Hint Rewrite var_names_length : core.*)
