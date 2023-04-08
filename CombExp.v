(* Coq Library Types *)
Require Import NArith String FMapList OrderedTypeEx.
Require Import Numbers.DecimalString.

(* Coq Library Tactics *) 
Require Import Lia.

(* UROP *)
Require Import UROP.IdentParsing.
Require Import UROP.Types.

Module CombExp.

Local Open Scope N_scope.
Local Open Scope UROP_scope.

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
  | NSkip
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

Local Open Scope string.
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
Notation "x ';' y" :=
  (NSeq x y)
  (in custom com at level 90, right associativity) : com_scope.
Notation "'done'" :=
  (NSkip)
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
  | NSkip => Ok g
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

(* HLL {{{ *)
Local Open Scope positive_scope.
Compute 1~1~0.

Fixpoint pos_to_bv (p : positive) : list N :=
  match p with
  | 1 => [1%N]
  | p~0 => 0%N :: pos_to_bv p
  | p~1 => 1%N :: pos_to_bv p
  end.

Close Scope positive_scope.

Fixpoint N_to_bv (n : N) : list N :=
  match n with
  | N0 => [0]
  | Npos p => pos_to_bv p
  end.

Fixpoint zeroes (n : nat) : list N :=
  match n with
  | O => []
  | S n' => 0 :: zeroes n'
  end.

Definition N_to_bvM (n : N) (m : nat) : list N :=
  let l := N_to_bv n in
  let len := (List.length l) in
  if Nat.leb len m then List.app l (zeroes (m - len)) else List.firstn (m - len) l.

Fixpoint bv_to_N (bv : list N) : N :=
  match bv with
  | [] => 0
  | h :: t => (bv_to_N t) * 2 + h
  end.

Lemma N_bv_equiv : forall n,
  n = bv_to_N (N_to_bv n).
Proof.
  destruct n; trivial; simpl.
  induction p; simpl; try lia.
Qed.

Lemma zeroes_is_zero : forall n,
  bv_to_N (zeroes n) = 0.
Proof.
  induction n; simpl; lia.
Qed.

(* MARK trying to prove bitvector equiv *)
Lemma bv_size_equiv : forall n,
  n <> 0
  -> List.length (N_to_bv n) = N.to_nat (N.size n).
Proof.
  intros n HP.
  induction n; simpl; try lia.
  induction p; simpl; try lia.
Qed.

Lemma N_bv_nz : forall n,
  (List.length (N_to_bv n)) <> 0%nat.
Proof.
  induction n; simpl; eauto.
  induction p; simpl; eauto.
Qed.

Lemma N_bv_add : forall n m,
  n <> 0 /\ m <> 0
  -> le (List.length (N_to_bv (n + m)))
  ((max (List.length (N_to_bv n)) (List.length (N_to_bv m))) + 1).
Proof.
  intros.
  rewrite! bv_size_equiv by lia.
  destruct (N.leb n m) eqn:Heq.
  - rewrite N.leb_le in Heq.

    replace (Nat.max (N.to_nat (N.size n)) (N.to_nat (N.size m))) with (N.to_nat (N.size m)).

    apply PeanoNat.Nat.le_trans with (m := (N.to_nat (N.size (2 * m + 1)))).
    admit.

    rewrite! N.size_log2 by lia.
    rewrite N.log2_succ_double by lia.
    lia.

    (*induction n; simpl.
  - induction m; simpl; try lia.
    induction p; simpl; lia.
  - induction m; simpl; try lia.

    induction p; simpl; induction p0; simpl; eauto.

    lia.

  (*induction n; simpl; try induction p; simpl; 
     induction m; simpl; try induction p0; simpl; eauto.*)

  - destruct (Datatypes.length (N_to_bv m)) eqn:Heq.
       rewrite*)
Admitted.

Lemma N_bv_len : forall m,
  gt m 0
  -> (forall n, 0 < n < (N.shiftl 1 (N.of_nat m))
  -> le (List.length (N_to_bv n)) m).
Proof.
  induction m; simpl; intros.
  - assert (n = 0) by lia; subst.
    lia.
  - rewrite bv_size_equiv by lia.
    
    admit.
Admitted.

Theorem N_bvM_equiv : forall m,
  gt m 0
  -> (forall n, n < (N.shiftl 1 (N.of_nat m))
  -> n = bv_to_N (N_to_bvM n m)).
Proof.
  induction m; simpl; intros.
  - assert (n = 0) by lia.
    subst.
    trivial.
  - unfold N_to_bvM.
    
    case n; simpl.
    rewrite zeroes_is_zero; lia.
    intros.
    admit.
  (*intros.
  destruct n.

  induction m using N.peano_ind; eauto.
  unfold N_to_bvM.
  case (Nat.leb (Datatypes.length (N_to_bv 0)) (N.to_nat (N.succ m))); simpl.
  { rewrite zeroes_is_zero; lia. }
  { replace (Nat.sub (N.to_nat (N.succ m)) 1) with (N.to_nat m) by lia.
    case (N.to_nat m); eauto.
    intros; case n; simpl; lia. }

  induction p; simpl.
     simpl in H.*)
Admitted.

Compute N_to_bvM 10 32. (* N to fixed length bit vectors *)

Definition modulo_set (n m : N) := n = n mod m.

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
(* }}} *)

(* Shifter {{{ *)
Definition interpret_test1 : node_exp := 
  NSeq (NDef "n0" <{ #0 }>) (NDef "n1" <{ #1 }>).

Definition interpret_test2 : node_exp := 
  <{ node n0 : #0; node n1 : #1 }>.

Definition shiftl4 (x i : list N) := 
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

Example shiftl4_test0: 
  shiftl4 [1; 1; 0; 0] [0; 0] = Ok [1; 1; 0; 0].
Proof. simpl. reflexivity. Qed.

Example shiftl4_test1: 
  shiftl4 [1; 1; 0; 0] [1; 0] = Ok [0; 1; 1; 0].
Proof. simpl. reflexivity. Qed.

Example shiftl4_test2: 
  shiftl4 [1; 1; 0; 0] [0; 1] = Ok [0; 0; 1; 1].
Proof. simpl. reflexivity. Qed.

Example shiftl4_test3: 
  shiftl4 [1; 1; 0; 0] [1; 1] = Ok [0; 0; 0; 1].
Proof. simpl. reflexivity. Qed.

Lemma shiftl4_correct_naive: forall n i,
  modulo_set n 16 ->
  modulo_set i 4 ->
  shiftl4 (N_to_bvM n 4) (N_to_bvM i 2) = Ok (N_to_bvM ((N.shiftl n i) mod 16) 4).
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

(* Generic shifter *)

Definition to_string (n : N) := NilZero.string_of_uint (N.to_uint n).

Definition var_names (prefix : string) (n : N) : list string := 
  List.rev (
    N.recursion
      []
      (fun n' l => (prefix ++ to_string n') :: l)
      n
  ).

Example var_names_1: 
  var_names "x" 3 = ["x0"; "x1"; "x2"].
Proof. reflexivity. Qed.

Definition shiftl_list (n : N) (l : list comb_exp) :=
  let tmp := N.recursion l (fun n' l' => <{ #0 }> :: l') n in
  N.recursion 
    tmp 
    (fun _ l' => List.removelast l')
    (N.of_nat (List.length tmp - List.length l)).

Compute shiftl_list 2 [Var "x0"; Var "x1"; Var "x2"; Var "x3"].

Fixpoint shiftl_layer (svar : comb_exp) (io : list (string * (comb_exp * comb_exp))) (base : node_exp) : node_exp :=
  match io with
  | [] => base
  | (ovar, (i0var, i1var)) :: t => 
      NSeq (NDef ovar (Mux svar i0var i1var)) (shiftl_layer svar t base)
  end.

Definition shiftl_exp (nbits : N) := 
  let sbits := N.log2 nbits in
  NMod
    (NInput ((var_names "x0" nbits) ++ (var_names "i" sbits)))
    (NOutput (var_names ("x" ++ to_string sbits) nbits))
    (N.recursion
      NSkip
      (fun si' lexp =>
        let si := sbits - si' - 1 in
          let svar := Var ("i" ++ to_string si) in
          let ovars := var_names ("x" ++ to_string (si + 1)) nbits in
          let i0vars := List.map Var (var_names ("x" ++ to_string si) nbits) in
          let i1vars := shiftl_list (si + 1) i0vars in
            shiftl_layer svar (zip ovars (zip i0vars i1vars)) lexp)
      sbits).

Compute shiftl_exp 4.

Definition shiftl' (n : N) (x i : list N) := 
  run (shiftl_exp n) (x ++ i) default_env.

Compute shiftl' 4 [1; 1; 0; 0] [0; 1].

Definition shiftl (nbits : N) (n i : N) :=
  let sbits := N.log2 nbits in
  run (shiftl_exp nbits) ((N_to_bvM n (N.to_nat nbits)) ++ (N_to_bvM i (N.to_nat sbits))) default_env.

Compute shiftl 4 3 2.

Theorem shiftl_equiv : forall b n i,
  i < b /\ n < (N.shiftl 1 b)
  -> shiftl b n i = Ok (N_to_bvM (N.shiftl n i) (N.to_nat b)).
Proof.
  intros.
  inversion H.
Admitted.
(* }}} *)

(* Optimizations {{{ *)
Fixpoint const_prop (c : comb_exp) : comb_exp :=
  match c with
  | Constant x => c
  | Var x => c
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
  intros; destruct (M.find (elt:=comb_fn) f1 s); try reflexivity.
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
