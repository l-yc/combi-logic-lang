Require Import NArith String FMapList OrderedTypeEx.
Require Import UROP.IdentParsing.

Declare Scope UROP_scope.
Delimit Scope UROP_scope with UROP.
(* Shorthands - List {{{ *)
Local Open Scope UROP_scope.
Notation "x :: l" := (cons x l)
  (at level 60, right associativity) : UROP_scope.
Notation "[ ]" := nil : UROP_scope.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..) : UROP_scope.
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

(* Types - Interpreter State {{{ *)
Module Import M := FMapList.Make(String_as_OT).
Definition state: Type := M.t N.
Definition env: Type := M.t comb_fn.

Arguments M.empty {elt}.

Notation "x '|->' v ';' m" := (M.add (ident_to_string! x) v m)
  (at level 100, v at next level, right associativity) : UROP_scope.
Notation "x '|->' v" := (M.add (ident_to_string! x) v M.empty)
  (at level 100) : UROP_scope.
(* }}} *)

(* Types - Interpreter Result {{{ *)
Inductive error : Type :=
  | UnboundNameError
  | InvalidArgumentError
  | TypeError
  | EvaluationError
  | InvalidModuleError
  | IOError
  .

Inductive result (T : Type) : Type :=
  | Ok (v : T)
  | Err (e : error)
  .

Arguments Ok {T}.
Arguments Err {T}.

Fixpoint zip {A} {B} (a : list A) (b : list B) : list (A * B) :=
  match a, b with
  | ha :: ta, hb :: tb => (ha, hb) :: zip ta tb
  | _, _ => []
  end.

Definition map_ok {A} {B} (r : result A) (f : A -> B) : result B :=
  match r with
  | Ok a => Ok (f a)
  | Err e => Err e
  end.

Definition flat_map_ok {A} {B} (r : result A) (f : A -> result B) : result B :=
  match r with
  | Ok a => f a
  | Err e => Err e
  end.

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
