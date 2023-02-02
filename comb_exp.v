From Coq Require Import NArith.BinNat.
From Coq Require Import BinNums.
From Coq Require Import Strings.String.
From Coq Require Import FSets.FMapList.
From Coq Require Import Structures.OrderedTypeEx.


Module CombExp.

Local Open Scope N_scope.

(* Shorthands - List {{{ *)
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

(* Syntax - Tests {{{ *)
Definition constant_0 : comb_exp :=
  Constant N0.

Definition var_x : comb_exp :=
  Var "x".

Definition call_fn : comb_exp := 
  Call "x" [constant_0].

Definition X0 : string := "X0".
Definition X1 : string := "X1".
Definition example_comb_exp1 : comb_exp := <{ N0 }>.
Definition example_comb_exp2 : comb_exp := <{ X0 }>.
Definition example_comb_exp3 : comb_exp := <{ let X0 := N0 in N0 }>.
(* }}} *)

(* State {{{ *)
Module Import M := FMapList.Make(String_as_OT).
Definition state: Type := M.t N.
Definition env: Type := M.t (list N -> N).

Arguments M.empty {elt}.

Notation "x '|->' v ';' m" := (M.add x v m)
  (at level 100, v at next level, right associativity).
Notation "x '|->' v" := (M.add x v M.empty)
  (at level 100).
(* }}} *)

(* Return types {{{ *)
Inductive error : Type :=
  | UnboundNameError
  | InvalidArgumentError
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
(* Idea: pure function; evaluates expression to an N *)
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
      | Some fn =>
          match all_ok_or_first (List.map (fun c => interpret c g s) l) with
          | Ok l => Ok (fn l)
          | Err e => Err e
          end
      | None => Err UnboundNameError
      end
  | Bind x c1 c2 => 
      match interpret c1 g s with
      | Ok v => interpret c2 (x |-> v; g) s
      | Err e => Err e
      end
  end.
(* }}} *)

(* Default Lib {{{ *)
Definition N1 : N := N.succ N0.

Definition add : string := "add".
Fixpoint add_fn (l : list N) : N :=
  match l with
  | nil => N0
  | h :: l' => N.add h (add_fn l')
  end.

Definition land : string := "land".
Fixpoint land_fn (l : list N) : N :=
  match l with
  | nil => N1
  | N0 :: l' => N0
  | _ :: l' => land_fn l'
  end.

Example land_test1: land_fn [N0; N0] = N0.
Proof. reflexivity. Qed.
Example land_test2: land_fn [N0; N1] = N0.
Proof. reflexivity. Qed.
Example land_test3: land_fn [N1; N0] = N0.
Proof. reflexivity. Qed.
Example land_test4: land_fn [N1; N1] = N1.
Proof. reflexivity. Qed.
Example land_test5: land_fn [N.succ N1; N.succ N1] = N1.
Proof. simpl. reflexivity. Qed.

Definition lor : string := "lor".
Fixpoint lor_fn (l : list N) : N :=
  match l with
  | nil => N0
  | N0 :: l' => lor_fn l'
  | _ :: l' => N1
  end.

Example lor_test1: lor_fn [N0; N0] = N0.
Proof. reflexivity. Qed.
Example lor_test2: lor_fn [N0; N1] = N1.
Proof. reflexivity. Qed.
Example lor_test3: lor_fn [N1; N0] = N1.
Proof. reflexivity. Qed.
Example lor_test4: lor_fn [N1; N1] = N1.
Proof. reflexivity. Qed.
Example lor_test5: lor_fn [N.succ N1; N.succ N1] = N1.
Proof. simpl. reflexivity. Qed.

(* FIXME all N > N0 are coerced to True in the current impl *)
(* FIXME the list implementation doesn't allow for nice matching with lnot *)

Definition default_env := (
  add |-> add_fn;
  land |-> land_fn;
  lor |-> lor_fn
).
(* }}} *)

(* Interpreter - Test {{{ *)
Example test_interpret1:
  interpret (Bind X0 N0 (X0)) M.empty default_env = Ok N0.
Proof. simpl. reflexivity. Qed.

Example test_interpret2:
  interpret (Var X0) (X0 |-> N0) default_env = Ok N0.
Proof. simpl. reflexivity. Qed.

Example test_interpret3:
  interpret (
    Bind X0 N1 (Call add [Var X0; Var X0])
  ) M.empty default_env = Ok (N.succ (N.succ N0)).
Proof. simpl. reflexivity. Qed.

Example test_interpret4:
  interpret (
    Bind X0 N0 (
      Bind X1 N1 (
        Call add [Call land [Var X0; Var X1]; Call lor [Var X0; Var X1]]
      )
    )
  ) M.empty default_env = Ok N1.
Proof. simpl. reflexivity. Qed.

Example test_interpret5:
  interpret (
    Call land [Constant N0; Constant N0]
  ) M.empty default_env = Ok N0.
Proof. simpl. reflexivity. Qed.

(* FIXME: another issue is that I don't fully understand how the parser works *)
Example test_interpret_parse1:
  interpret <{ let X0 := N0 in X0 }> M.empty default_env = Ok N0.
Proof. simpl. reflexivity. Qed.

Example test_interpret_parse2:
  interpret <{ X0 }> (X0 |-> N0) default_env = Ok N0.
Proof. simpl. reflexivity. Qed.

(*Example test_interpret_parseN:
 interpret <{ let X := N1 in land [X;X] }> M.empty default_env = Ok (N.succ (N.succ N0)).
   Proof. reflexivity. Qed.*)

(* }}} *)

  (*
- Gamma is the state
- Sigma is the map from function names to semantics, i.e. String -> list N -> N
- The result can just be a special entry in the returned state of type Gamma.
*)

(* interpret (AND [1; 1]) {} s = Ok 1 *)

End CombExp.
