From Coq Require Import NArith.BinNat.
From Coq Require Import BinNums.
From Coq Require Import Strings.String.
From Coq Require Import FSets.FMapList.
From Coq Require Import Structures.OrderedTypeEx.

 Local Open Scope N_scope.

(* META: Shorthands {{{ *)
Notation "x :: l" := (cons x l)
  (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
(* }}} *)

(* Syntax {{{ *)
Inductive comb_exp : Type :=
  | Constant (x : N)
  | Var (x : string)
  | Call (f : string) (l : list comb_exp)
  | Bind (x : string) (c1 : comb_exp) (c2 : comb_exp)
  .

  (*Inductive comb_fn : Type :=
  | fn_unit (f : N -> N)
  | fn_curry (f : N -> comb_fn).

Check (fn_curry (fun (x : N) => fn_unit (fun (y : N) => y))) : comb_fn.

Inductive comb_fn (f : N -> N) : Type :=
  | fn_unit : comb_fn f.
     | fn_curry (f : N -> comb_fn) (f' : comb_fn) : comb_fn f f'.*)
(* }}} *)

(* Syntax - Notation {{{ *)
Coercion Constant : N >-> comb_exp.
Coercion Var : string >-> comb_exp.

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f args" := (Call f args)
  (in custom com at level 0, only parsing,
  f constr at level 0, args constr at level 9) : com_scope.
(*Notation "f x .. y" := (.. (f x) .. y)
  (in custom com at level 0, only parsing,
  f constr at level 0, x constr at level 9,
   y constr at level 9) : com_scope.*)
Notation "'let' x ':=' y 'in' e"  := (Bind x y e)
  (in custom com at level 0, x constr at level 0,
     y at level 85, no associativity) : com_scope.

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
(* }}} *)

(* Syntax - Tests *)
Definition constant_0 : comb_exp :=
  Constant N0.

Definition var_x : comb_exp :=
  Var "x".

Definition call_fn : comb_exp := 
  Call "x" [constant_0].

Definition X : string := "X".
Definition example_comb_exp1 : comb_exp := <{ N0 }>.
Definition example_comb_exp2 : comb_exp := <{ X }>.
Definition example_comb_exp3 : comb_exp := <{ let X := N0 in N0 }>.
(* }}} *)

(* State {{{ *)
Module Import M := FMapList.Make(String_as_OT).

Definition state_var: Type := M.t N.
Definition state_fn: Type := M.t (list N -> N).

Inductive error : Type :=
  | UnboundNameError
  | EvaluationError
  .

Inductive result (T : Type) : Type :=
  | Ok (v : T)
  | Err (e : error)
  .
(* }}} *)

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

(* Interpreter {{{ *)
(* Idea: pure function; evaluates expression to an N *)
Fixpoint interpret (c : comb_exp) (g : state_var) (s : state_fn) : result N :=
  match c with
  | Constant x => Ok x
  | Var x => 
      match (M.find x g) with
      | Some v => Ok v
      | None => Err UnboundNameError
      end
  | Call f l => 
      match (M.find f s) with
      | Some fn =>
          match all_ok_or_first (List.map (fun c => interpret c g s) l) with
          | Ok l => Ok (fn l)
          | Err e => Err e
          end
          (*Ok (fn (List.map (fun c => N0) l)) *)
(*(map (fun (c' : comb_exp) => interpret c g s) l)*)
      | None => Err UnboundNameError
      end
  | Bind x c1 c2 => 
      match interpret c1 g s with
      | Ok v => interpret c2 (M.add x v g) s
      | Err => Err
      end
  end.

Definition empty_state_var := M.empty N.
Definition empty_state_fn := M.empty (list N -> N).

Example test_interpret1:
  interpret <{ let X = N0 in X }> empty_state_var empty_state_fn = Ok N N0.
Proof. reflexivity. Qed.

Example test_interpret2:
  interpret <{ X }> (M.add X N0 empty_state_var) empty_state_fn = Ok _ N0.
Proof. simpl. reflexivity. Qed.

Definition add_fn_id : string := "add".
Fixpoint add_fn (l : list N) : N :=
  match l with
  | nil => N0
  | h :: l' => N.add h (add_fn l')
  end.
Definition default_state_fn := M.add add_fn_id add_fn empty_state_fn.
Definition N1 : N := N.succ N0.

Example test_interpret3:
 interpret (Bind X N1 (Call "add" [Var X; Var X])) empty_state_var default_state_fn = Ok _ (N.succ (N.succ N0)).
Proof. simpl. reflexivity. Qed.

Example test_interpret4:
 interpret <{ let X = N1 in add_fn_id [X;X] }> empty_state_var empty_state_fn = Ok (N.succ (N.succ N0)).
Proof. reflexivity. Qed.

(* interpret (AND [1; 1]) {} s = Ok 1 *)
(* }}} *)

  (*
- Gamma is the state
- Sigma is the map from function names to semantics, i.e. String -> list N -> N
- The result can just be a special entry in the returned state of type Gamma.
*)

