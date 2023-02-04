From Coq Require Import NArith.BinNat.
From Coq Require Import BinNums.
From Coq Require Import Strings.String.
From Coq Require Import FSets.FMapList.
From Coq Require Import Structures.OrderedTypeEx.

Require Import CombExp.IdentParsing.

Module CombExp.

Local Open Scope N_scope.

(* Shorthands - List {{{ *)
Notation "x :: l" := (cons x l)
  (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
(* }}} *)

(* Types - Syntax {{{ *)
Fixpoint Arity (A B : Type) (n: nat) : Type :=
  match n with
  | O => B
  | S n' => A -> (Arity A B n')
  end.

Check Arity N N 2.

Inductive comb_fn : Type :=
  | fn (n : nat) (f : Arity N N n).

(* Alternative inductive definition that isn't used *)
(* Inductive comb_fn' : Type :=
  | fn_unit (f : N -> N)
  | fn_curry (f : N -> comb_fn').

Check (fn_curry (fun (x : N) => fn_unit (fun (y : N) => y))) : comb_fn'. *)
(* }}} *)

(* Syntax - AST {{{ *)
Inductive comb_exp : Type :=
  | Constant (x : N)
  | Var (x : string)
  | Call (f : string) (l : list comb_exp)
  | Bind (x : string) (c1 : comb_exp) (c2 : comb_exp)
  .

(* Tests {{{ *)
Definition constant_0 : comb_exp :=
  Constant N0.

Definition var_x : comb_exp :=
  Var "x".

Definition call_fn : comb_exp := 
  Call "x" [constant_0].
(* }}} *)
(* }}} *)

(* Syntax - Notation {{{ *)
Coercion Constant : N >-> comb_exp.
Coercion Var : string >-> comb_exp.

Open Scope string.
Check "test" : comb_exp.

Declare Custom Entry com.
Declare Scope com_scope.

Notation "'<{' e '}>'" := e (at level 0, e custom com at level 99) : com_scope.
Notation "x" := (Var (ident_to_string! x)) (in custom com at level 0, x constr at level 0) : com_scope.
Notation "'#' x" := (Constant x) (in custom com at level 0, x constr at level 0) : com_scope.
(* Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
 *)
(*Notation "f args" := (Call f args)
  (in custom com at level 0, only parsing,
   f constr at level 0, args constr at level 9) : com_scope.*)
Notation "'@' f x .. y" := (Call (ident_to_string! f) (cons x .. (cons y nil) ..))
  (in custom com at level 10, only parsing,
  f constr at level 0, x custom com at level 9,
  y custom com at level 9) : com_scope.
Notation "'let' x ':=' y 'in' e"  := (Bind (ident_to_string! x) y e)
  (in custom com at level 0, x constr at level 0,
  y custom com at level 85, e custom com at level 85, no associativity) : com_scope.

(*Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
 Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).*)

Open Scope com_scope.

(* Tests {{{ *)
(*Definition X0 : string := "X0".
   Definition X1 : string := "X1".*)
Definition example_comb_exp1 : comb_exp := <{ N0 }>.
Definition example_comb_exp2 : comb_exp := <{ X0 }>.
Definition example_comb_exp3 : comb_exp := <{ let X0 := N0 in N0 }>.
(* }}} *)
(* }}} *)

(* Types - Interpreter State {{{ *)
Module Import M := FMapList.Make(String_as_OT).
Definition state: Type := M.t N.
Definition env: Type := M.t comb_fn.

Arguments M.empty {elt}.

Notation "x '|->' v ';' m" := (M.add (ident_to_string! x) v m)
  (at level 100, v at next level, right associativity).
Notation "x '|->' v" := (M.add (ident_to_string! x) v M.empty)
  (at level 100).
(* }}} *)

(* Types - Interpreter Result {{{ *)
Inductive error : Type :=
  | UnboundNameError
  | InvalidArgumentError
  | TypeError
  | EvaluationError
  .

Inductive result (T : Type) : Type :=
  | Ok (v : T)
  | Err (e : error)
  .

Arguments Ok {T}.
Arguments Err {T}.

Fixpoint all_ok_or_first {T : Type} (l : list (result T)) : result (list T) :=
  match l with
  | nil => Ok nil
  | h :: l' => 
      match h with
      | Ok v1 => 
          match all_ok_or_first l' with
          | Ok v2 => Ok (v1 :: v2)
          | Err e => Err e
          end
      | Err e => Err e
      end
  end.
(* }}} *)

(* Interpreter {{{ *)
(* Functions are pure; evaluates expression to an N.
  This function does the function signature matching. *)
Fixpoint apply (c : comb_fn) (l : list N) : result N :=
  match c, l with
  | fn 0 f, nil => Ok f
  | fn (S n') f, h :: l' => apply (fn n' (f h)) l'
  | _, _ => Err TypeError
  end.

(* Parameters
- Gamma is the state
- Sigma is the map from function names to semantics (function with a specific arity) *)
Fixpoint interpret (c : comb_exp) (g : state) (s : env) : result N :=
  match c with
  | Constant x => Ok x
  | Var x => 
      match (M.find x g) with
      | Some v => Ok v
      | None => Err UnboundNameError
      end
  | Call f l => 
      match (M.find f s) with
      | Some c => 
          match all_ok_or_first (List.map (fun c => interpret c g s) l) with
          | Ok l => apply c l
          | Err e => Err e
          end
      | None => Err UnboundNameError
      end
  | Bind x c1 c2 => 
      match interpret c1 g s with
      | Ok v => interpret c2 (M.add x v g) s
      | Err e => Err e
      end
  end.
(* }}} *)

(* Default Lib {{{ *)
Definition N1 : N := N.succ N0.

Definition add_fn (a b : N) : N := N.add a b.

Definition land_fn (a b : N) : N :=
  match a, b with
  | N0, N0 => N0
  | N0, _ => N0
  | _, N0 => N0
  | _, _ => N1
  end.

Definition lor_fn (a b : N) : N :=
  match a, b with
  | N0, N0 => N0
  | _, _ => N1
  end.

Definition lnot_fn (a : N) : N :=
  match a with
  | N0 => N1
  | _ => N0
  end.

(* FIXME all N > N0 are coerced to True in the current impl *)

Definition default_env : env := (
  add |-> fn 2 add_fn;
  land |-> fn 2 land_fn;
  lor |-> fn 2 lor_fn;
  lnot |-> fn 1 lnot_fn
).
(* }}} *)

(* Interpreter - Test {{{ *)
Example test_interpret1:
  interpret (Bind "X0" N0 ("X0")) M.empty default_env = Ok N0.
Proof. unfold interpret. simpl. reflexivity. Qed.

Example test_interpret2:
  interpret (Var "X0") (X0 |-> N0) default_env = Ok N0.
Proof. simpl. reflexivity. Qed.

Example test_interpret3:
  interpret (
    Bind "X0" 1 (Call "add" ["X0" : comb_exp; "X0" : comb_exp])
  ) M.empty default_env = Ok (N.succ (N.succ N0)).
Proof. simpl. reflexivity. Qed.

Example test_interpret4:
  interpret (
    Bind "X0" N0 (
      Bind "X1" 1 (
        Call "add" [Call "land" [Var "X0"; Var "X1"]; Call "lor" [Var "X0"; Var "X1"]]
      )
    )
  ) M.empty default_env = Ok 1.
Proof. simpl. reflexivity. Qed.

Example test_interpret5:
  interpret (
    Call "land" [Constant N0; Constant N0]
  ) M.empty default_env = Ok N0.
Proof. simpl. reflexivity. Qed.

Example test_interpret6:
  interpret (
    Call "land" [Constant N0; Constant N0; Constant N0]
  ) M.empty default_env = Err TypeError.
Proof. simpl. reflexivity. Qed.

(* FIXME: 
another issue is that I don't fully understand how the parser works 
so I can't get the string working and have to work around by defining X0 X1 *)
Example test_interpret_parse1:
  interpret <{ let X0 := #0 in X0 }> M.empty default_env = Ok N0.
Proof. simpl. reflexivity. Qed.

Example test_interpret_parse2:
  interpret <{ X0 }> (X0 |-> N0) default_env = Ok N0.
Proof. simpl. reflexivity. Qed.

Example test_interpret_parse3:
  interpret <{ @land X0 X0 }> (X0 |-> N0) default_env = Ok N0.
(*interpret <{ land (Var X0) (Var X0) }> (X0 |-> N0) default_env = Ok N0.*)
Proof. simpl. reflexivity. Qed.

Example test_interpret_parseN:
  interpret <{ let X0 := #1 in @land X0 X0 }> M.empty default_env = Ok 1.
Proof. simpl. reflexivity. Qed.

(* }}} *)

End CombExp.
