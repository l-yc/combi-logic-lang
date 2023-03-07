Require Import Eqdep String NArith Arith Lia Program Relations.

Require Import Coq.NArith.NArith. Open Scope N_scope.
(*From Coq Require Import NArith.BinNat.
   From Coq Require Import BinNums.*)
From Coq Require Import Strings.String.
From Coq Require Import FSets.FMapList.
   From Coq Require Import Structures.OrderedTypeEx.

Require Import CombExp.IdentParsing.

Module CombExp.

(*Local Open Scope N_scope.*)

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
  | Bind (x : string) (c0 : comb_exp) (c2 : comb_exp)
  | Mux (cs : comb_exp) (c1 : comb_exp) (c2 : comb_exp)
  (* Common unary/binary operations *)
  | Not (c1 : comb_exp)
  | And (c1 : comb_exp) (c2 : comb_exp)
  | Or (c1 : comb_exp) (c2 : comb_exp)
  | Xor (c1 : comb_exp) (c2 : comb_exp)
  | Nand (c1 : comb_exp) (c2 : comb_exp)
  | Nor (c1 : comb_exp) (c2 : comb_exp)
  .

  (*Print comb_exp_ind.*)
Print List.Forall.

Section list_forall.
Variable A : Type.
Variable P : A -> Prop.
Variable (fn : forall (a : A), P a).
Fixpoint list_forall (l : list A) : List.Forall P l :=
  match l with
  | h :: t => List.Forall_cons h (fn h) (list_forall t)
  | nil => List.Forall_nil _
  end.
End list_forall.
Print list_forall.

Definition my_comb_exp_ind :=
fun (P : comb_exp -> Prop) (f : forall x : N, P (Constant x))
  (f0 : forall x : string, P (Var x))
  (f1 : forall (f1 : string) (l : list comb_exp) (IHl : List.Forall P l), P (Call f1 l))
  (f2 : forall (x : string) (c0 : comb_exp),
        P c0 -> forall c2 : comb_exp, P c2 -> P (Bind x c0 c2))
  (f3 : forall cs : comb_exp,
        P cs ->
        forall c1 : comb_exp,
        P c1 -> forall c2 : comb_exp, P c2 -> P (Mux cs c1 c2))
  (f4 : forall c1 : comb_exp, P c1 -> P (Not c1))
  (f5 : forall c1 : comb_exp,
        P c1 -> forall c2 : comb_exp, P c2 -> P (And c1 c2))
  (f6 : forall c1 : comb_exp,
        P c1 -> forall c2 : comb_exp, P c2 -> P (Or c1 c2))
  (f7 : forall c1 : comb_exp,
        P c1 -> forall c2 : comb_exp, P c2 -> P (Xor c1 c2))
  (f8 : forall c1 : comb_exp,
        P c1 -> forall c2 : comb_exp, P c2 -> P (Nand c1 c2))
  (f9 : forall c1 : comb_exp,
        P c1 -> forall c2 : comb_exp, P c2 -> P (Nor c1 c2)) =>
fix F (c : comb_exp) : P c :=
  match c as c0 return (P c0) with
  | Constant x => f x
  | Var x => f0 x
  | Call f10 l => f1 f10 l (list_forall _ P F l)
  | Bind x c0 c2 => f2 x c0 (F c0) c2 (F c2)
  | Mux cs c1 c2 => f3 cs (F cs) c1 (F c1) c2 (F c2)
  | Not c1 => f4 c1 (F c1)
  | And c1 c2 => f5 c1 (F c1) c2 (F c2)
  | Or c1 c2 => f6 c1 (F c1) c2 (F c2)
  | Xor c1 c2 => f7 c1 (F c1) c2 (F c2)
  | Nand c1 c2 => f8 c1 (F c1) c2 (F c2)
  | Nor c1 c2 => f9 c1 (F c1) c2 (F c2)
  end.

Inductive node_exp : Type :=
  | NInput (l : list string)
  | NOutput (l : list string)
  | NDef (n : string) (c : comb_exp)
  | NSeq (e1 e2 : node_exp)
  | NMod (i : node_exp) (o : node_exp) (p : node_exp)
  .

(* Tests {{{ *)
Definition constant_0 : comb_exp :=
  Constant 0.

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
Notation "'?' s '->' x ':' y" := (Mux s x y)
  (in custom com at level 10, only parsing,
  s custom com at level 9, x custom com at level 9,
  y custom com at level 9) : com_scope.


Notation "'node' n ':' c" := (NDef (ident_to_string! n) c)
  (in custom com at level 0, n constr at level 0, 
  c custom com at level 85, no associativity) : com_scope.
Notation "x ; y" :=
  (NSeq x y)
  (in custom com at level 90, right associativity) : com_scope.
Notation "'$' x" := (ident_to_string! x)
  (in custom com at level 0, x constr at level 0) : com_scope.
Notation "'input' xi .. yi ';' 'output' xo .. yo ';' e" := 
  (NMod
    (NInput (cons xi .. (cons yi nil) ..))
    (NOutput (cons xo .. (cons yo nil) ..))
    e
  )
  (in custom com at level 100, 
  xi custom com at level 0, yi custom com at level 0,
  xo custom com at level 0, yo custom com at level 0,
  e custom com at level 100,
  no associativity) : com_scope.
(* defining IO in two steps according to https://stackoverflow.com/questions/51092642/define-recursive-notation-with-two-recursive-variables-in-coq *)

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
Definition example_comb_exp1 : comb_exp := <{ #0 }>.
Definition example_comb_exp2 : comb_exp := <{ X0 }>.
Definition example_comb_exp3 : comb_exp := <{ let X0 := #0 in #0 }>.
Definition example_node_exp1 : node_exp := <{ node a : #0; node b : #1 }>.
Definition example_node_exp2 : node_exp := <{ 
  input $a $b $c;
  output $a $b $c;
  node a : #0;
  node b : #1
}>.
Definition example_node_exp3 : node_exp := <{
  input $a0 $a1;
  output $b0 $b1;

  node b0 : @land a0 a1;
  node b1 : @lor a0 a1
}>.
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

Fixpoint map_ok {A} {B} (r : result A) (f : A -> B) : result B :=
  match r with
  | Ok a => Ok (f a)
  | Err e => Err e
  end.

Fixpoint flat_map_ok {A} {B} (r : result A) (f : A -> result B) : result B :=
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

(* Default Lib {{{ *)
Definition add_fn (a b : N) : N := N.add a b.

Definition lnot_fn (a : N) : N :=
  match a mod 2 with
  | 0 => 1
  | _ => 0
  end.

Definition land_fn (a b : N) : N :=
  match a mod 2, b mod 2 with
  | 0, 0 => 0
  | 0, _ => 0
  | _, 0 => 0
  | _, _ => 1
  end.

Definition lor_fn (a b : N) : N :=
  match a mod 2, b mod 2 with
  | 0, 0 => 0
  | _, _ => 1
  end.

Definition lxor_fn (a b : N) : N :=
  match a mod 2, b mod 2 with
  | 0, 0 => 0
  | 0, _ => 1
  | _, 0 => 1
  | _, _ => 0
  end.

Definition lnand_fn (a b : N) : N :=
  lnot_fn (land_fn a b).

Definition lnor_fn (a b : N) : N :=
  lnot_fn (lor_fn a b).

Definition default_env : env := (
  add |-> fn 2 add_fn;
  land |-> fn 2 land_fn;
  lor |-> fn 2 lor_fn;
  lnot |-> fn 1 lnot_fn
).
(* }}} *)

(* Evaluator & Interpreter {{{ *)
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
Fixpoint evaluate (c : comb_exp) (g : state) (s : env) : result N :=
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
          match all_ok_or_first (List.map (fun c => evaluate c g s) l) with
          | Ok l => apply c l
          | Err e => Err e
          end
      | None => Err UnboundNameError
      end
  | Bind x c1 c2 => 
      match evaluate c1 g s with
      | Ok v => evaluate c2 (M.add x v g) s
      | Err e => Err e
      end
  | Mux cs c1 c2 =>
      match evaluate cs g s with
      | Ok v => match v mod 2 with
                | 0 => evaluate c1 g s
                | _ => evaluate c2 g s
                end
      | Err e => Err e
      end

  | Not c1 => match (evaluate c1 g s) with
              | Ok v => Ok (lnot_fn v)
              | Err e => Err e
              end
  | And c1 c2 => 
      match (evaluate c1 g s), (evaluate c2 g s) with
      | Ok v1, Ok v2 => Ok (land_fn v1 v2)
      | Err e, _ => Err e
      | _, Err e => Err e
      end
  | Or c1 c2 =>
      match (evaluate c1 g s), (evaluate c2 g s) with
      | Ok v1, Ok v2 => Ok (lor_fn v1 v2)
      | Err e, _ => Err e
      | _, Err e => Err e
      end
  | Xor c1 c2 =>
      match (evaluate c1 g s), (evaluate c2 g s) with
      | Ok v1, Ok v2 => Ok (lxor_fn v1 v2)
      | Err e, _ => Err e
      | _, Err e => Err e
      end
  | Nand c1 c2 => 
      match (evaluate c1 g s), (evaluate c2 g s) with
      | Ok v1, Ok v2 => Ok (lnand_fn v1 v2)
      | Err e, _ => Err e
      | _, Err e => Err e
      end
  | Nor c1 c2 =>
      match (evaluate c1 g s), (evaluate c2 g s) with
      | Ok v1, Ok v2 => Ok (lnor_fn v1 v2)
      | Err e, _ => Err e
      | _, Err e => Err e
      end
  end.

Fixpoint interpret (e : node_exp) (g : state) (s : env) : result state :=
  match e with
  | NDef n c => 
      match evaluate c g s with 
      | Ok v => Ok (M.add n v g)
      | Err e => Err e
      end
  | NSeq e1 e2 => 
      match interpret e1 g s with
      | Ok g' => interpret e2 g' s
      | Err e => Err e
      end
  | _ => Err InvalidModuleError
  end.

Fixpoint values_to_state (args : list string) (values : list N) : result state :=
  match args, values with
  | k :: args', v :: values' => map_ok (values_to_state args' values') (M.add k v)
  | nil, nil => Ok M.empty
  | _, _ => Err IOError
     end.

Fixpoint state_to_values (args : list string) (g : state) : result (list N) :=
  match args with
  | k :: args' => match M.find k g with
                  | Some x => map_ok (state_to_values args' g) (fun l => x :: l)
                  | _ => Err IOError
                  end
  | nil => Ok nil
  end.

(*Theorem value_to_state_convertible :
  forall args values g, 
    values_to_state args values = Ok g ->
    state_to_values args g = Ok values.
   Proof. Admitted.*)

Definition run (e : node_exp) (inp : list N) (s : env) : result (list N) :=
  match e with
  | NMod (NInput i) (NOutput o) c =>
      flat_map_ok
      (flat_map_ok (values_to_state i inp) (fun g => interpret c g s))
      (state_to_values o)
  | _ => Err InvalidModuleError
  end.
(* }}} *)

(* Evaluate - Test {{{ *)
Example test_evaluate1:
  evaluate (Bind "X0" 0 ("X0")) M.empty default_env = Ok 0.
Proof. unfold evaluate. simpl. reflexivity. Qed.

Example test_evaluate2:
  evaluate (Var "X0") (X0 |-> 0) default_env = Ok 0.
Proof. simpl. reflexivity. Qed.

Example test_evaluate3:
  evaluate (
    Bind "X0" 1 (Call "add" ["X0" : comb_exp; "X0" : comb_exp])
  ) M.empty default_env = Ok 2.
Proof. simpl. reflexivity. Qed.

Example test_evaluate4:
  evaluate (
    Bind "X0" 0 (
      Bind "X1" 1 (
        Call "add" [Call "land" [Var "X0"; Var "X1"]; Call "lor" [Var "X0"; Var "X1"]]
      )
    )
  ) M.empty default_env = Ok 1.
Proof. simpl. reflexivity. Qed.

Example test_evaluate5:
  evaluate (
    Call "land" [Constant 0; Constant 0]
  ) M.empty default_env = Ok 0.
Proof. simpl. reflexivity. Qed.

Example test_evaluate6:
  evaluate (
    Call "land" [Constant 0; Constant 0; Constant 0]
  ) M.empty default_env = Err TypeError.
Proof. simpl. reflexivity. Qed.

Example test_evaluate7:
  evaluate (
    Mux 1 0 1
  ) M.empty default_env = Ok 1.
Proof. simpl. reflexivity. Qed.

Example test_evaluate_parse1:
  evaluate <{ let X0 := #0 in X0 }> M.empty default_env = Ok 0.
Proof. simpl. reflexivity. Qed.

Example test_evaluate_parse2:
  evaluate <{ X0 }> (X0 |-> 0) default_env = Ok 0.
Proof. simpl. reflexivity. Qed.

Example test_evaluate_parse3:
  evaluate <{ @land X0 X0 }> (X0 |-> 0) default_env = Ok 0.
Proof. simpl. reflexivity. Qed.

Example test_evaluate_parse4:
  evaluate <{ let X0 := #1 in @land X0 X0 }> M.empty default_env = Ok 1.
Proof. simpl. reflexivity. Qed.

Example test_evaluate_parse5:
  evaluate <{ let X0 := #0 in let X1 := #1 in let X := @land X0 X1 in ? X -> X0 : X1 }> M.empty default_env = Ok 0.
Proof. simpl. reflexivity. Qed.
(* }}} *)

(* Shifter {{{ *)
Definition interpret_test1 : node_exp := 
  NSeq (NDef "n0" <{ #0 }>) (NDef "n1" <{ #1 }>).

Definition interpret_test2 : node_exp := 
  <{ node n0 : #0; node n1 : #1 }>.

Definition shiftl4_exp (x i : list N) := 
  run <{
    input $x0 $x1 $x2 $x3 $i0 $i1;
    output $b0 $b1 $b2 $b3;

    node a0: ? i0 -> x0 : #0;
    node a1: ? i0 -> x1 : x0;
    node a2: ? i0 -> x2 : x1;
    node a3: ? i0 -> x3 : x2;

    node b0: ? i1 -> a0 : #0;
    node b1: ? i1 -> a1 : #0;
    node b2: ? i1 -> a2 : a0;
    node b3: ? i1 -> a3 : a1
  }> 
  (x ++ i)
  default_env.

Example shiftl4_exp_test0: 
  shiftl4_exp [1; 1; 0; 0] [0; 0] = Ok [1; 1; 0; 0].
Proof. simpl. reflexivity. Qed.

Example shiftl4_exp_test1: 
  shiftl4_exp [1; 1; 0; 0] [1; 0] = Ok [0; 1; 1; 0].
Proof. simpl. reflexivity. Qed.

Example shiftl4_exp_test2: 
  shiftl4_exp [1; 1; 0; 0] [0; 1] = Ok [0; 0; 1; 1].
Proof. simpl. reflexivity. Qed.

Example shiftl4_exp_test3: 
  shiftl4_exp [1; 1; 0; 0] [1; 1] = Ok [0; 0; 0; 1].
Proof. simpl. reflexivity. Qed.

(* helpers for proving equivalence with Coq library functions {{{ *)
Local Open Scope positive_scope.
Compute 1~1~0.

Fixpoint pos_to_bv (p : positive) : list N :=
  match p with
  | 1 => [1%N]
  | p~0 => 0%N :: pos_to_bv p
  | p~1 => 1%N :: pos_to_bv p
  end.

Fixpoint N_to_bv (n : N) : list N :=
  match n with
  | N0 => [0%N]
  | Npos p => pos_to_bv p
  end.

Fixpoint zeroes (n : nat) : list N :=
  match n with
  | O => []
  | S n' => 0%N :: zeroes n'
  end.

Definition N_to_bvM (n : N) (m : nat) : list N :=
  let l := N_to_bv n in
  List.app l (zeroes (m - (List.length l))).

Close Scope positive_scope.

Compute N_to_bvM 10 32. (* N to fixed length bit vectors *)
(* }}} *)

Definition modulo_set (n m : N) := n = n mod m.

(*Lemma modulo_set_le: forall n m,
  m <> 0 -> modulo_set n m <-> n < m.
Proof.
  induction n using N.peano_rect; intros.
  - intros. destruct m eqn:Heq.
    
    exfalso. easy.

    split. lia. intros. apply modulo_set_0. assumption.
   -*)

Lemma modulo_set_one: forall n,
  modulo_set n 1 -> n = 0.
Proof.
  intros.
  unfold modulo_set in H.
  rewrite N.mod_1_r in H.
  assumption.
Qed.

Lemma lt_explode: forall m n,
  n < m -> n = m-1 \/ n < m-1.
Proof.
  Search (_ mod _).
  intros.
  lia.
Qed.

Lemma modulo_set_lt: forall m n,
  m <> 0 -> modulo_set n m <-> n < m.
Proof.
  unfold modulo_set; split; intros.

  apply N.mod_upper_bound with (a:=n) in H.
  lia.

  symmetry.
  apply N.mod_small.
  assumption.
Qed.

Lemma modulo_set_explode: forall m n,
  m > 1 -> modulo_set n m -> n = m-1 \/ modulo_set n (m-1).
Proof.
  intros.
  rewrite modulo_set_lt in H0.
  rewrite modulo_set_lt.

  all: lia.
Qed.

Lemma shiftl4_correct_naive: forall n i,
  modulo_set n 16 ->
  modulo_set i 4 ->
  shiftl4_exp (N_to_bvM n 4) (N_to_bvM i 2) = Ok (N_to_bvM ((N.shiftl n i) mod 16) 4).
Proof.
  intros n i Hn Hi.
  repeat match goal with
  | [Hn: modulo_set n ?E |- _ ] =>
    match E with
    | 1 => apply modulo_set_one in Hn as H0
    | _ => apply modulo_set_explode in Hn;
            cycle 1; try lia;
            try destruct Hn as [H0 | Hn]; try simpl in Hn
    end;
    try rewrite H0;

    repeat match goal with
    | [H0: n = _ , Hi: modulo_set i ?E |- _ ] =>
        match E with
        | 1 => apply modulo_set_one in Hi as H1
        | _ => apply modulo_set_explode in Hi;
                cycle 1; try lia;
                try destruct Hi as [H1 | Hi]; try simpl in Hi
        end;
        try rewrite H1;
        try reflexivity
    end
  end.
Qed.

(*Lemma shiftl4_correct: forall n i,
  n = n mod 16 ->
  i = i mod 4 ->
  shiftl4_exp (N_to_bvM n 4) (N_to_bvM i 2) = Ok (N_to_bvM (N.shiftl n i) 4).
Proof.
  intros.

  unfold shiftl4_exp.
  unfold run.
  destruct (N_to_bvM n 4 ++ N_to_bvM i 2)%list eqn:Heq.
  simpl.
   Qed.*)

Definition shiftl8_exp (x i : list N) := 
  run <{
    input $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7 $i0 $i1 $i2;

    output $b0 $b1 $b2 $b3 $b4 $b5 $b6 $b7;

    node a0: ? i0 -> x0 : #0;
    node a1: ? i0 -> x1 : x0;
    node a2: ? i0 -> x2 : x1;
    node a3: ? i0 -> x3 : x2;
    node a4: ? i0 -> x4 : x3;
    node a5: ? i0 -> x5 : x4;
    node a6: ? i0 -> x6 : x5;
    node a7: ? i0 -> x7 : x6;

    node b0: ? i1 -> a0 : #0;
    node b1: ? i1 -> a1 : #0;
    node b2: ? i1 -> a2 : a0;
    node b3: ? i1 -> a3 : a1;
    node b4: ? i1 -> a4 : a2;
    node b5: ? i1 -> a5 : a3;
    node b6: ? i1 -> a6 : a4;
    node b7: ? i1 -> a7 : a5
  }> 
  (x ++ i)
  default_env.

(*Lemma shiftl8_correct_naive: forall n i,
  modulo_set n 256 ->
  modulo_set i 8 ->
  shiftl4_exp (N_to_bvM n 8) (N_to_bvM i 3) = Ok (N_to_bvM ((N.shiftl n i) mod 256) 8).
Proof.
  intros n i Hn Hi.
  repeat match goal with
  | [Hn: modulo_set n ?E |- _ ] =>
    match E with
    | 1 => apply modulo_set_one in Hn as H0
    | _ => apply modulo_set_explode in Hn;
            cycle 1; try lia;
            try destruct Hn as [H0 | Hn]; try simpl in Hn
    end;
    try rewrite H0;

    repeat match goal with
    | [H0: n = _ , Hi: modulo_set i ?E |- _ ] =>
        match E with
        | 1 => apply modulo_set_one in Hi as H1
        | _ => apply modulo_set_explode in Hi;
                cycle 1; try lia;
                try destruct Hi as [H1 | Hi]; try simpl in Hi
        end;
        try rewrite H1;
        try reflexivity
    end
  end.
   Qed.*)

(* }}} *)

(* Optimizations {{{ *)
Fixpoint const_prop (c : comb_exp) : comb_exp :=
  match c with
  | Constant x => c
  | Var x => c
      (*| Call f l => c (* non-trivial to prove, since IHs aren't generated *) *)
  | Call f l => Call f (List.map const_prop l)
  | Bind x c1 c2 => Bind x (const_prop c1) (const_prop c2)

  | Mux (Constant n) c1 c2 =>
      match n mod 2 with
      | 0 => const_prop c1
      | _ => const_prop c2
      end
  | Mux cs c1 c2 => Mux (const_prop cs) (const_prop c1) (const_prop c2)
  | Not (Constant n) => Constant (lnot_fn n)
  | Not c => Not (const_prop c)
  | And (Constant n1) (Constant n2) => Constant (land_fn n1 n2)
  | And c1 c2 => And (const_prop c1) (const_prop c2)
  | Or (Constant n1) (Constant n2) => Constant (lor_fn n1 n2)
  | Or c1 c2 => Or (const_prop c1) (const_prop c2)
  | Xor (Constant n1) (Constant n2) => Constant (lxor_fn n1 n2)
  | Xor c1 c2 => Xor (const_prop c1) (const_prop c2)
  | Nand (Constant n1) (Constant n2) => Constant (lnand_fn n1 n2)
  | Nand c1 c2 => Nand (const_prop c1) (const_prop c2)
  | Nor (Constant n1) (Constant n2) => Constant (lnor_fn n1 n2)
  | Nor c1 c2 => Nor (const_prop c1) (const_prop c2)
  end.

Ltac explode :=
  repeat match goal with
         | [ |- context[match ?E with _ => _ end] ] => destruct E; simpl
         end.

Ltac match_match :=
  match goal with
  | [ |- context[match ?E1 with _ => _ end = match ?E2 with _ => _ end] ] => assert (E1 = E2)
  end.

Theorem const_prop_ok :
  forall c g s, evaluate c g s = evaluate (const_prop c) g s.
Proof.
  induction c using my_comb_exp_ind; try reflexivity; simpl.

  (* Call *)
  intros; destruct (find (elt:=comb_fn) f1 s); try reflexivity.
  match_match.
  
  f_equal.
  induction l.

  simpl. reflexivity.

  simpl. inversion IHl. rewrite IHl0. f_equal.
  apply H1.
  apply H2.

  rewrite H. reflexivity.

  (* Bind *)
  intros. rewrite IHc1.
  destruct evaluate; try rewrite IHc2; reflexivity.
  
  (* Mux *)
  destruct c1; simpl.

  destruct (x mod 2); try apply IHc2; try apply IHc3.

  all: try (intros; explode; try rewrite IHc2; try rewrite IHc3; reflexivity).
  all: try (intros; match_match; try apply IHc1; rewrite H; explode; try apply IHc2; try apply IHc3; try reflexivity).

  (* Not Gate *)
  destruct c; simpl; try reflexivity;
    try (intros; match_match; try apply IHc; rewrite H; explode; try reflexivity).

  (* And Gate *)
  destruct c1; simpl; try reflexivity; intros.
  destruct c2; simpl; try reflexivity.
    all: try (intros; match_match; try apply IHc2; try rewrite H; explode; reflexivity).
    all: try (intros; try rewrite IHc2; reflexivity).
    all: try (intros; match_match; try apply IHc1; rewrite H; try rewrite IHc2; reflexivity).

  (* Or Gate *)
  destruct c1; simpl; try reflexivity; intros.
  destruct c2; simpl; try reflexivity.
    all: try (intros; match_match; try apply IHc2; try rewrite H; explode; reflexivity).
    all: try (intros; try rewrite IHc2; reflexivity).
    all: try (intros; match_match; try apply IHc1; rewrite H; try rewrite IHc2; reflexivity).

  (* Xor Gate *)
  destruct c1; simpl; try reflexivity; intros.
  destruct c2; simpl; try reflexivity.
    all: try (intros; match_match; try apply IHc2; try rewrite H; explode; reflexivity).
    all: try (intros; try rewrite IHc2; reflexivity).
    all: try (intros; match_match; try apply IHc1; rewrite H; try rewrite IHc2; reflexivity).

  (* Nand Gate *)
  destruct c1; simpl; try reflexivity; intros.
  destruct c2; simpl; try reflexivity.
    all: try (intros; match_match; try apply IHc2; try rewrite H; explode; reflexivity).
    all: try (intros; try rewrite IHc2; reflexivity).
    all: try (intros; match_match; try apply IHc1; rewrite H; try rewrite IHc2; reflexivity).

  (* Nor Gate *)
  destruct c1; simpl; try reflexivity; intros.
  destruct c2; simpl; try reflexivity.
    all: try (intros; match_match; try apply IHc2; try rewrite H; explode; reflexivity).
    all: try (intros; try rewrite IHc2; reflexivity).
    all: try (intros; match_match; try apply IHc1; rewrite H; try rewrite IHc2; reflexivity).
Qed.

  (* need more automation :( *)
(* }}} *)

End CombExp.
