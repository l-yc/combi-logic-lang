(* Coq Library Types *)
Require Import NArith String FMapList OrderedTypeEx.
Require Import Numbers.DecimalString.

(* Coq Library Tactics *) 
Require Import Lia.
Require Import ZArith.

(* UROP *)
Require Import UROP.IdentParsing.
Require Import UROP.Types.
Require Import UROP.BitVectors.
Require Import UROP.Tactics.
Require Import UROP.ExtraArith.

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

Inductive cmd : Type :=
  | CSkip
  | CDef (n : string) (c : comb_exp)
  | CSeq (c1 c2 : cmd)
  .

Definition io : Type := list string.

Record module := {
  Input : io;
  Output : io;
  Program : cmd;
}.

Check {| Input := []; Output := []; Program := CSkip |}.


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


Notation "'node' n ':' c" := (CDef (ident_to_string! n) c)
  (in custom com at level 0, n constr at level 0, 
  c custom com at level 85, no associativity) : com_scope.
Notation "x ';' y" :=
  (CSeq x y)
  (in custom com at level 90, right associativity) : com_scope.
Notation "'skip" :=
  (CSkip)
  (in custom com at level 90, right associativity) : com_scope.
Notation "'$' x" := (ident_to_string! x)
  (in custom com at level 0, x constr at level 0) : com_scope.
Notation "'input' xi .. yi ';' 'output' xo .. yo ';' e" := 
  {|
    Input := (cons xi .. (cons yi nil) ..);
    Output := (cons xo .. (cons yo nil) ..);
    Program := e;
  |}
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
Definition example_program : cmd := <{ node a : #0; node b : #1 }>.
Definition example_module1 : module := <{ 
  input $a $b $c;
  output $a $b $c;
  node a : #0;
  node b : #1
}>.
Definition example_module2 : module := <{
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

Fixpoint interpret (e : cmd) (g : state) (s : env) : result state :=
  match e with
  | CSkip => Ok g
  | CDef n c => 
      match evaluate c g s with 
      | Ok v => Ok (M.add n v g)
      | Err e => Err e
      end
  | CSeq e1 e2 => 
      match interpret e1 g s with
      | Ok g' => interpret e2 g' s
      | Err e => Err e
      end
  end.

Fixpoint values_to_state (args : list string) (values : list N) : result state :=
  match args, values with
  | k :: args', v :: values' => map_ok (values_to_state args' values') (M.add k v)
  | nil, nil => Ok M.empty
  | _, _ => Err IOError
  end.

Fixpoint state_to_values (args : list string) (g : state) : result (list N) :=
  match args with
  | k :: args' => 
      match M.find k g with
      | Some x => map_ok (state_to_values args' (M.remove k g)) (fun l => x :: l)
      | _ => Err IOError
      end
  | nil => Ok nil
  end.





(*Inductive interp: result state -> node_exp -> result state -> Prop :=
  | InterpSkip: forall v,
      interp v NSkip v
  | InterpDefOk: forall c g s v n,
      evaluate c g s = Ok v
      -> interp (Ok g) (NDef n c) (Ok (M.add n v g))
  | InterpDefErr: forall c g s e n,
      evaluate c g s = Err e
      -> interp (Ok g) (NDef n c) (Err e)
  | InterpSeqOk: forall v1 v2 v3 c1 c2,
      interp (Ok v1) c1 (Ok v2)
      -> interp (Ok v2) c2 (Ok v3)
      -> interp (Ok v1) (NSeq c1 c2) (Ok v3)
  | InterpSeqErr1: forall v1 e c1 c2,
      interp (Ok v1) c1 (Err e)
      -> interp (Ok v1) (NSeq c1 c2) (Err e)
  | InterpSeqErr2: forall v1 v2 e c1 c2,
      interp (Ok v1) c1 (Ok v2)
      -> interp (Ok v2) c2 (Err e)
      -> interp (Ok v1) (NSeq c1 c2) (Err e)
.

Theorem interp_interpret_equiv: forall g c g' s,
  interp (Ok g) c g' <-> interpret c g s = g'.
Proof. *)

Ltac all_branches :=
  repeat match goal with
    (*| [ |- context[match ?e with | Ok _ => _ | Err _ => _ end] ] => destruct e eqn:?*)
         | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
         end.

Lemma interpret_seq_ok: forall c1 c2 g s g1 g2,
  interpret c1 g s = Ok g1
  -> interpret c2 g1 s = Ok g2
  -> interpret (CSeq c1 c2) g s = Ok g2.
Proof.
  intros.
  simpl.
  all_branches.
  inversion H.
  subst.
  eauto.
  inversion H.
Qed.





Theorem map_ok_is_ok (A: Type) (B: Type) : forall opt fn v,
  @map_ok A B opt fn = Ok v -> exists v', opt = Ok v' /\ v = fn v'.
Proof.
  unfold map_ok.
  intros; simpl.
  destruct opt; inversion H; eauto.
Qed.

Theorem flat_map_ok_is_ok (A: Type) (B: Type) : forall opt fn v,
  @flat_map_ok A B opt fn = Ok v <-> exists v', fn v' = Ok v /\ opt = Ok v'.
Proof.
  unfold map_ok; split.
  - intros; simpl.
    destruct opt; inversion H; eauto.
  - intros; simpl.
    inversion H.
    inversion H0.
    subst; eauto.
Qed.



Theorem find_add (A: Type) : forall k v m,
  M.find (elt:=A) k (M.add k v m) = Some v.
Proof.
Admitted.

Theorem remove_add (A: Type) : forall k v m,
  ~ (M.In k m) -> M.remove (elt:=A) k (M.add k v m) = m.
Proof.
Admitted.

Compute values_to_state ["a"; "b"; "c"] [1;2;3].
Compute match values_to_state ["a"; "b"; "c"] [1;2;3] with
        | Ok v => state_to_values ["a"; "b"; "c"] v
        | Err e => Err e
        end.

Theorem values_to_state_ok : forall args values, 
  List.length args = List.length values
  -> exists g, values_to_state args values = Ok g.
Proof.
  induction args; induction values; simpl; try lia; eauto.
  intros.
  inversion H.
  specialize (IHargs _ H1).
  destruct IHargs.
  rewrite H0; simpl; eauto.
Qed.

Definition map_keys {elt: Type} (m : M.t elt) := List.map fst (M.elements m).
Definition map_vals {elt: Type} (m : M.t elt) := List.map snd (M.elements m).

Theorem map_keys_ok {elt: Type} : forall k v m,
  ~ M.In k m
  -> map_keys (M.add k v m) = k :: @map_keys elt m.
Proof.
Admitted.

Theorem map_keys_equiv {elt: Type} : forall k m,
  M.In (elt:=elt) k m <-> List.In k (map_keys m).
Proof.
Admitted.

Definition merge_fmap_seq {elt} (m1 m2 : M.t elt) := List.fold_left (fun a kv => M.add (fst kv) (snd kv) a) (M.elements m2) m1.

Definition m1 := M.add "a" 1 M.empty.
Definition m2 := M.add "b" 2 M.empty.
Compute merge_fmap_seq m1 m2.

(*Theorem values_to_state_app : forall arg1 arg2 val1 val2 g,
  values_to_state (arg1 ++ arg2) (val1 ++ val2) = Ok g
  -> exists g1 g2, values_to_state arg1 val1 = Ok g1 /\ values_to_state arg2 val2 = Ok g2 /\ g = merge_fmap_seq g1 g2.
Proof.

Theorem values_to_state_app_2 : forall arg1 arg2 val1 val2 g1 g2,
  values_to_state arg1 val1 = Ok g1 /\ values_to_state arg2 val2 = Ok g2
  -> values_to_state (arg1 ++ arg2) (val1 ++ val2) = Ok (merge_fmap_seq g1 g2).
Proof. *)

Theorem values_to_state_convertible' : forall args values g, 
  (* missing some clause about uniqueness *)
  List.NoDup args
  -> values_to_state args values = Ok g 
  -> state_to_values args g = Ok values /\ args = map_keys g.
Proof.
  induction args, values.
  - simpl; intros; inversion H0; eauto.
  - simpl; inversion 2.
  - simpl; inversion 2.
  - simpl; intros.
    apply map_ok_is_ok in H0.
    destruct H0 as [H0 e].
    inversion e as [e1 e2]; clear e.
    subst.
    rewrite find_add.
    inversion H.
    specialize (IHargs values H0 H4 e1).
    inversion IHargs as [IH1 IH2]; clear IHargs.
    split.

    rewrite remove_add; eauto.
    rewrite IH1; simpl; eauto.
    rewrite map_keys_equiv; rewrite <- IH2; eauto.

    rewrite map_keys_ok.
    rewrite IH2; eauto.
    rewrite map_keys_equiv; rewrite <- IH2; eauto.
Qed.

Theorem values_to_state_convertible : forall args values g, 
  (* missing some clause about uniqueness *)
  List.NoDup args
  -> values_to_state args values = Ok g
  -> state_to_values args g = Ok values.
Proof.
  apply values_to_state_convertible'; eauto.
Qed.

Definition run (m : module) (inp : list N) (s : env) : result (list N) :=
  flat_map_ok
  (flat_map_ok (values_to_state (m.(Input)) inp) (fun g => interpret m.(Program) g s))
  (state_to_values m.(Output)).
(* }}} *)

  (*Theorem run_strengthen : forall i o c inp s r,
  run (NMod (NInput i) (NOutput o) c) inp s = r
  -> forall k v, run (NMod (NInput (i ++ [k])) (NOutput (o ++ [k])) c) (inp ++ [v]) s = r.
Proof. *)

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

(* 4-Shifter {{{ *)
Definition interpret_test1 : cmd := 
  CSeq (CDef "n0" <{ #0 }>) (CDef "n1" <{ #1 }>).

Definition interpret_test2 : cmd := 
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
  shiftl4 (bvM.of_N 4 n) (bvM.of_N 2 i) = Ok (bvM.of_N 4 ((N.shiftl n i) mod 16)).
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
(* }}} *)

(* var_names lemmas for generic shifter {{{ *)
Definition to_string (n : N) := NilZero.string_of_uint (N.to_uint n).

Fixpoint var_names_ (prefix : string) (n : nat) : list string := 
  match n with
  | O => []
  | S n' => (prefix ++ to_string (N.of_nat n')) :: var_names_ prefix n'
  end.

Definition var_names (prefix : string) (n : nat) : list string := 
  List.rev (var_names_ prefix n).

Example var_names_1: 
  var_names "x" 3 = ["x0"; "x1"; "x2"].
Proof. reflexivity. Qed.

Lemma var_names_nil : forall v,
  var_names v 0 = [].
Proof.
  eauto.
Qed.

Lemma var_names_length' : forall v n,
  List.length (var_names_ v n) = n.
Proof.
  induction n; simpl; eauto.
Qed.

Lemma var_names_length : forall v n,
  List.length (var_names v n) = n.
Proof.
  unfold var_names.
  intros.
  rewrite List.rev_length.
  apply var_names_length'.
Qed.

Lemma var_names_succ' : forall v n,
  var_names_ v (S n) = (v ++ to_string (N.of_nat (n))) :: var_names_ v n.
Proof.
  intros; simpl; eauto.
Qed.

Lemma var_names_succ : forall v n,
  var_names v (S n) = List.app (var_names v n) [v ++ to_string (N.of_nat (n))].
Proof.
  unfold var_names.
  intros.
  rewrite var_names_succ'.
  eauto.
Qed.

(* not going to prove these string things *)
Lemma string_app_neq : forall a b c,
  b <> c <-> a ++ b <> a ++ c.
Proof.
Admitted.

Lemma to_string_neq : forall n m,
  n <> m <-> to_string n <> to_string m.
Proof.
Admitted.

Lemma var_names_not_in : forall m v n,
  le m n
  -> ~ List.In (v ++s to_string (N.of_nat n)) (List.rev (var_names v m)).
Proof.
  induction m; simpl; intros; eauto.
  rewrite var_names_succ.
  rewrite List.rev_app_distr; simpl List.rev; simpl List.app.
  rewrite List.not_in_cons.
  split.
  - apply string_app_neq.
    apply to_string_neq.
    lia.
  - apply IHm; lia.
Qed.

Lemma var_names_nodup : forall v n,
  List.NoDup (var_names v n).
Proof.
  induction n.
  rewrite var_names_nil; apply List.NoDup_nil.
  rewrite var_names_succ.
  
  apply rev_rev.
  rewrite List.rev_app_distr; simpl.
  apply List.NoDup_cons.
  apply var_names_not_in; lia.
  apply List.NoDup_rev.
  assumption.
Qed.
(* }}} *)

(* Run Helpers {{{ *)
Lemma state_to_values_idempotent : forall v,
  state_to_values (map_keys v) v = Ok (map_vals v).
Proof.
Admitted.

Lemma values_to_state_idempotent : forall v,
  values_to_state (map_keys v) (map_vals v) = Ok v.
Proof.
Admitted.

Lemma map_keys_nodup {elt : Type} : forall (m : M.t elt),
  List.NoDup (map_keys m).
Proof.
Admitted.

Fixpoint untouched (p : cmd) (s : string) : Prop :=
  match p with
  | CSkip => True
  | CDef n c => s <> n
  | CSeq c1 c2 => untouched c1 s /\ untouched c2 s
  end.

Fixpoint covers_exp (c : comb_exp) (vars : list string) : Prop :=
  match c with
  | Constant x => True
  | Var x => List.In x vars
  | Call f l => True (*List.Forall (fun c => covers_exp c vars) l *) (* this is kinda bad *)
  | Bind x c1 c2 => covers_exp c1 vars /\ covers_exp c2 vars
  | Mux cs c1 c2 => covers_exp cs vars /\ covers_exp c1 vars /\ covers_exp c2 vars
  | Not c1 => covers_exp c1 vars
  | And c1 c2 => covers_exp c1 vars /\ covers_exp c2 vars
  | Or c1 c2 => covers_exp c1 vars /\ covers_exp c2 vars
  | Xor c1 c2 => covers_exp c1 vars /\ covers_exp c2 vars
  | Nand c1 c2 => covers_exp c1 vars /\ covers_exp c2 vars
  | Nor c1 c2 => covers_exp c1 vars /\ covers_exp c2 vars
  end.

Fixpoint covers (p : cmd) (vars : list string) : Prop :=
  match p with
  | CSkip => True
  | CDef n c => covers_exp c vars
  | CSeq c1 c2 => covers c1 vars /\ covers c2 vars
  end.
(* }}} *)

(* Run {{{ *)
Lemma run_seq : forall iv ov ov' p1 p2 inp res res',
  run {|
    Input := iv;
    Output := ov';
    Program := p1
  |} inp default_env = Ok res'
  -> run {|
    Input := ov';
    Output := ov;
    Program := p2
  |} res' default_env = Ok res
  -> covers p2 ov'
  -> run {|
    Input := iv;
    Output := ov;
    Program := CSeq p1 p2
  |} inp default_env = Ok res.
Proof.
Admitted.

Lemma run_split : forall iv ov1 ov2 p1 p2 bv1 bv2 inp,
  run {|
    Input := iv;
    Output := ov1;
    Program := p1;
  |} inp
  default_env = Ok bv1
  -> run {|
    Input := iv;
    Output := ov2;
    Program := p2;
  |} inp
  default_env = Ok bv2
  -> List.Forall (untouched p1) iv
  -> List.Forall (untouched p2) ov1
  -> run {|
    Input := iv;
    Output := (ov1 ++ ov2)%list;
    Program := CSeq p1 p2%list;
  |} inp
  default_env = Ok (bv1 ++ bv2)%list.
Proof.
  unfold run; simpl.
  intros.

  rewrite flat_map_ok_is_ok in H.
  destruct H as [res1 [Ha H]].
  rewrite flat_map_ok_is_ok in H.
  destruct H as [vin [Hb Hin]].

  rewrite Hin in H0; simpl in H0.
  rewrite flat_map_ok_is_ok in H0.
  destruct H0 as [res2 [H0a H0b]].

  rewrite Hin; simpl.
  rewrite Hb.
  rewrite flat_map_ok_is_ok.
  eexists.

  (* need some constraint on whether things are touched *)
  (*rewrite flat_map_ok_is_ok.
  eexists.
  apply state_to_values_app. eauto.
     Search state_to_values.*)
Admitted.
(*List.Forall P l*)

(* need to add conditions *)
Lemma run_pass_through : forall iv ov p inp res bv bv_vals,
  List.Forall (untouched p) bv
  -> run {|
    Input := iv;
    Output := ov;
    Program := p
  |} inp default_env = Ok res
  -> run {|
    Input := (iv ++l bv);
    Output := (ov ++l bv);
    Program := p
  |} (inp ++l bv_vals) default_env = Ok (res ++l bv_vals).
Proof.
  unfold run; simpl.
  intros.
Admitted.

(* need to add conditions *)
Lemma run_extra_args : forall iv1 iv iv2 ov p inp1 inp inp2 res,
  List.Forall (fun v => ~ List.In v iv2) iv
  -> run {|
    Input := (iv1 ++ iv2)%list;
    Output := ov;
    Program := p
  |} (inp1 ++ inp2)%list default_env = Ok res
  -> run {|
    Input := (iv1 ++ iv ++ iv2)%list;
    Output := ov;
    Program := p 
  |} (inp1 ++ inp ++ inp2)%list default_env = Ok res.
Proof.
Admitted.
(* }}} *)

(* Generic shifter {{{ *)
Close Scope N_scope. (* temporary thing *)
Definition shiftl_list (n : nat) (l : list comb_exp) :=
  List.firstn (List.length l) (List.app (List.repeat <{#0}> n) l).

Example shiftl_list_ex1 :
  shiftl_list 2 [Var "x0"; Var "x1"; Var "x2"; Var "x3"] = [<{#0}>; <{#0}>; Var "x0"; Var "x1"].
Proof. reflexivity. Qed.

Fixpoint shiftl_layer (svar : comb_exp) (io_vars : list (string * (comb_exp * comb_exp))) : cmd :=
  match io_vars with
  | [] => CSkip
  | (ovar, (i0var, i1var)) :: t => 
      CSeq (shiftl_layer svar t) (CDef ovar (Mux svar i0var i1var))
  end.

Fixpoint shiftl_exp_body' (nbits : nat) (sbits : nat) :=
  match sbits with
  | O => CSkip
  | S si =>
    let svar := Var ("i" ++ to_string (N.of_nat si)) in
    let ovars := var_names ("x" ++ to_string (N.of_nat si + 1)) nbits in
    let i0vars := List.map Var (var_names ("x" ++ to_string (N.of_nat si)) nbits) in
    let i1vars := shiftl_list (Nat.pow 2 si) i0vars in
      CSeq 
        (shiftl_exp_body' nbits si)
        (shiftl_layer svar (List.rev (zip ovars (zip i0vars i1vars))))
   end.

Definition shiftl_exp_body (nbits : nat) (sbits : nat) := 
  shiftl_exp_body' nbits sbits.

Compute shiftl_exp_body 3 3.

Definition shiftl_exp (nbits : nat) (sbits : nat) := 
  {|
    Input := List.app (var_names "x0" nbits) (var_names "i" sbits);
    Output := var_names ("x" ++ to_string (N.of_nat sbits)) nbits;
    Program := (shiftl_exp_body nbits sbits);
  |}.

Definition shiftl (nbits : nat) (n i : N) :=
  let sbits := PeanoNat.Nat.log2_up nbits in
  run (shiftl_exp nbits sbits) ((bvM.of_N nbits n) ++ (bvM.of_N sbits i)) default_env.

Compute shiftl 6 12 0.

Close Scope string_scope.
Open Scope N_scope.
Example generic_shiftl_test : shiftl 5 31 4 = Ok [0; 0; 0; 0; 1].
Proof. unfold shiftl. simpl. reflexivity. Qed.
(* }}} *)

Ltac propositional :=
  repeat match goal with
  | [H: _ /\ _ |- _] => inversion H; clear H
  end.

(* Search N.shiftl. *)
(* _spec... *)

(* Proof for generic shifter {{{ *)
Opaque String.append.
Open Scope string_scope.




Lemma shiftl_list_length : forall x l,
  List.length (shiftl_list x l) = List.length l.
Proof.
  intros.
  unfold shiftl_list.
  rewrite List.firstn_length.
  rewrite List.app_length.
  lia.
Qed.

Ltac simplify :=
  try simplify_list; match goal with
  | [|- context[N.shiftl _ 0]] => rewrite N.shiftl_0_r
  | [|- context[Datatypes.length (bvM.of_N _ _)]] => rewrite bvM.of_N_length
  | [|- context[Datatypes.length (var_names _ _)]] => rewrite var_names_length
  | [|- context[Datatypes.length (shiftl_list _ _)]] => rewrite shiftl_list_length
  | [|- context[Datatypes.length (zip _ _)]] => rewrite zip_length
  | [|- context[List.firstn ?b (bvM.of_N ?b ?n)]] => 
    replace (List.firstn b (bvM.of_N b n)) 
    with (List.firstn (List.length (bvM.of_N b n)) (bvM.of_N b n));
    try apply List.firstn_all
  | _ => idtac
  end; simpl; eauto.

Ltac simp := repeat simplify.




Compute (shiftl_list 0 (List.map Var (var_names "x" 2))).
Compute (shiftl_list 1 (List.map Var (var_names "x" 2))).
Compute (shiftl_list 1 (List.map Var (var_names "x" 3))).
Compute (shiftl_list 1 (List.map Var (var_names "x" 4))).

Definition shiftl_bvM (n : nat) (l : list N) :=
  List.firstn (List.length l) (List.app (List.repeat 0 n) l).

Lemma firstn_firstn_repeat : forall l l' x a b,
  (a = List.length l)%nat ->
  (a <= b)%nat ->
  List.firstn a (List.app (List.repeat 0 x) l)
  = List.firstn a (List.firstn b (List.app (List.repeat 0 x) (l ++l l'))).
Proof.
  induction l; simpl; intros; unfold shiftl_bvM; simpl.

  - rewrite List.firstn_firstn.
    replace (Nat.min a b) with a by lia.
    subst.
    rewrite List.firstn_O; eauto.

  - rewrite List.firstn_firstn.
    replace (Nat.min a0 b) with a0 by lia.
    rewrite! List.firstn_app.
    f_equal.
    replace (a :: l) with ([a] ++l l) by eauto.
    replace (a :: (l ++l l')) with ([a] ++l l ++l l') by eauto.

    Search (List.firstn).
    rewrite List.firstn_app with (l2 := l').

    replace (Nat.sub (Nat.sub a0 (Datatypes.length (List.repeat 0 x))) (Datatypes.length ([a] ++l l))) with O.
    rewrite List.firstn_O.
    rewrite List.app_nil_r.
    eauto.

    rewrite List.app_length; simpl.
    rewrite List.repeat_length.
    lia.
Qed.

Lemma shiftl_bvM_length_equiv : forall s b n,
  shiftl_bvM (Nat.pow 2 s) (bvM.of_N b n) =
  List.firstn b
    (shiftl_bvM (Nat.pow 2 s)
       (bvM.of_N b n ++l [N.b2n (N.testbit n (N.of_nat b))])).
Proof.
  intros.
  unfold shiftl_bvM.
  rewrite bvM.of_N_length.
  eapply firstn_firstn_repeat.
  rewrite bvM.of_N_length; lia.
  rewrite List.app_length.
  rewrite bvM.of_N_length; lia.
Qed.

Lemma var_names_spec : forall i s n d,
  lt i n
  -> List.nth i (var_names s n) d = (s ++s to_string (N.of_nat i)).
Proof.
  induction n.
  inversion 1.
  intros.
  assert ((i < n)%nat \/ (i = n)%nat) by lia.
  destruct H0.
  - rewrite var_names_succ.
    rewrite List.app_nth1; eauto; simp.
  - subst; clear H.
    rewrite var_names_succ.
    rewrite List.app_nth2; simp.
    replace (n - n)%nat with O by lia; eauto.
Qed.

Lemma shiftl_layer_one : forall s b n v1 v2 svar,
  run {|
    Input := (var_names v1 b ++ [svar])%list;
    Output := var_names v2 b;
    Program :=
      shiftl_layer svar
        (List.rev
          (zip 
            (var_names v2 b)
            (zip
               (List.map Var (var_names v1 b))
               (shiftl_list (Nat.pow 2 s) (List.map Var (var_names v1 b))))))
  |}
  (bvM.of_N b n ++ [1]) default_env 
  = Ok (shiftl_bvM (Nat.pow 2 s) (bvM.of_N b n)).
Proof.
  induction b; eauto.

  intros.
  (* some var names property we use a lot *)
  assert (~ List.In (v1 ++s to_string (N.of_nat b)) [svar]) by admit.
  assert (Hbig: (2 ^ s <= b \/ 2 ^ s > b)%nat) by lia.
  destruct Hbig.
  { replace 
    (shiftl_list (Nat.pow 2 s) (List.map Var (var_names v1 (S b)))) 
  with
    (shiftl_list (Nat.pow 2 s) (List.map Var (var_names v1 b)) ++ [Var (v1 ++ to_string (N.of_nat (b - Nat.pow 2 s)))])%list.
  rewrite! var_names_succ.
  rewrite! bvM.of_N_succ.
  rewrite! List.map_app.
  rewrite! zip_app; simp; try lia.
  rewrite List.rev_app_distr; simpl.
  rewrite <- List.firstn_skipn with (n := b) (l := shiftl_bvM _ _).
  apply run_split.
  - { replace (List.firstn b 
      (shiftl_bvM (Nat.pow 2 s)
      (bvM.of_N b n ++ [N.b2n (N.testbit n (N.of_nat b))])))
    with (shiftl_bvM (Nat.pow 2 s) (bvM.of_N b n)).
    rewrite <- List.app_assoc.
    rewrite <- List.app_assoc.
    apply run_extra_args with
      (iv := [(v1 ++ to_string (N.of_nat b))%string])
      (inp := [N.b2n (N.testbit n (N.of_nat b))]).
    apply List.Forall_cons; eauto.
    apply IHb; eauto.
    apply shiftl_bvM_length_equiv. }
  - { Opaque values_to_state.
      Opaque interpret.
      Opaque state_to_values.
      unfold run. simpl.
      assert (Hargs: List.length ((var_names v1 b ++ [v1 ++ to_string (N.of_nat b)]) ++ [svar]) = List.length ((bvM.of_N b n ++ [N.b2n (N.testbit n (N.of_nat b))]) ++ [1])).
      { rewrite! List.app_length.
        rewrite var_names_length.
        rewrite bvM.of_N_length.
        reflexivity. }
      apply values_to_state_ok in Hargs.
      destruct Hargs as [inp Hinp]; rewrite Hinp; simpl.

      (* get the values *)
      assert (Hs: M.find svar inp = Some 1) by admit. (* prove some map property *)
      assert (Hother: M.find (v1 ++ to_string (N.of_nat (b - Nat.pow 2 s))) inp = Some (N.b2n (N.testbit n (N.of_nat (b - Nat.pow 2 s))))) by admit.
      (*assert (Htmp: exists v, M.find (v1 ++ to_string (N.of_nat (b - Nat.pow 2 s))) inp = Some v).
       destruct Htmp as [other Hother].*)

      (* ok *)
      apply flat_map_ok_is_ok.
      eexists; split; cycle 1.
      Transparent interpret.
      simpl.

      rewrite Hs; simpl.
      rewrite Hother; reflexivity.

      Transparent state_to_values.
      simpl; rewrite find_add.

      f_equal.
      unfold shiftl_bvM.
      simp.
      rewrite List.skipn_firstn_comm.
      replace ((b + 1 - b)%nat) with 1%nat by lia.
      destruct (Nat.ltb b (2 ^ s)) eqn:rel.
      + rewrite Nat.ltb_lt in rel; lia.
      + rewrite Nat.ltb_ge in rel.
        rewrite List.skipn_app.
        replace (List.skipn b (List.repeat 0 (2 ^ s))) with ([] : list N); cycle 1.
        { rewrite List.skipn_all2; eauto.
        rewrite List.repeat_length; lia. }
        Opaque List.firstn.
        simp.
        rewrite List.firstn_skipn_comm.
        rewrite List.firstn_app.
        simp.

        assert (Htrivial: (2 <> 0)%nat) by lia.
        epose proof (Nat.pow_nonzero 2 s Htrivial).

        replace ((b - 2 ^ s + 1 - b)%nat) with O by lia.
        rewrite List.firstn_O.
        rewrite List.app_nil_r.
        Search (List.skipn).
        
        erewrite list_firstn_skipn_succ.
        erewrite bvM.of_N_spec; eauto; lia.
        simp; lia. }
  - admit. (* var names property *)
  - admit. (* var names property *)
  - rewrite var_names_succ.
    rewrite List.map_app; simp.
    unfold shiftl_list; simp.

    rewrite List.firstn_app.
    replace (List.firstn b (List.repeat <{ # 0 }> (2 ^ s))) with (List.repeat <{ # 0 }> (2 ^ s)); cycle 1.
    rewrite List.firstn_all2; simp.

    rewrite List.firstn_app.
    replace (List.firstn (b + 1) (List.repeat <{ # 0 }> (2 ^ s))) with (List.repeat <{ # 0 }> (2 ^ s)); cycle 1.
    rewrite List.firstn_all2; simp; lia.

    rewrite <- List.app_assoc; f_equal.
    simp.

    rewrite List.firstn_app; simp.
    assert (Htrivial: (2 <> 0)%nat) by lia.
    epose proof (Nat.pow_nonzero 2 s Htrivial).
    replace (b + 1 - 2 ^ s - b)%nat with O by lia; simp.
    replace (b + 1 - 2 ^ s)%nat with (S (b - 2 ^ s)) by lia.
    erewrite list_firstn_succ.
    f_equal.
    rewrite List.map_nth.
    rewrite var_names_spec; simp; lia.
    rewrite List.map_length; simp; lia. }
  { replace (shiftl_list (Nat.pow 2 s) (List.map Var (var_names v1 (S b)))) 
    with (shiftl_list (Nat.pow 2 s) (List.map Var (var_names v1 b)) ++ [<{ # 0 }>])%list.
    rewrite! var_names_succ.
    rewrite! bvM.of_N_succ.
    rewrite! List.map_app.
    rewrite! zip_app; simp; try lia.
    rewrite List.rev_app_distr; simpl.
    rewrite <- List.firstn_skipn with (n := b) (l := shiftl_bvM _ _).
    apply run_split.
    - { replace (List.firstn b 
        (shiftl_bvM (Nat.pow 2 s)
        (bvM.of_N b n ++ [N.b2n (N.testbit n (N.of_nat b))])))
      with (shiftl_bvM (Nat.pow 2 s) (bvM.of_N b n)).
      rewrite <- List.app_assoc.
      rewrite <- List.app_assoc.
      apply run_extra_args with
        (iv := [(v1 ++ to_string (N.of_nat b))%string])
        (inp := [N.b2n (N.testbit n (N.of_nat b))]).
      apply List.Forall_cons; eauto.
      apply IHb; eauto.
      apply shiftl_bvM_length_equiv. }
    - { Opaque values_to_state.
        Opaque interpret.
        Opaque state_to_values.
        unfold run. simpl.
        assert (Hargs: List.length ((var_names v1 b ++ [v1 ++ to_string (N.of_nat b)]) ++ [svar]) = List.length ((bvM.of_N b n ++ [N.b2n (N.testbit n (N.of_nat b))]) ++ [1])) by simp.
        apply values_to_state_ok in Hargs.
        destruct Hargs as [inp Hinp]; rewrite Hinp; simpl.

        (* get the values *)
        assert (Hs: M.find svar inp = Some 1) by admit. (* prove some map property *)

        (* ok *)
        apply flat_map_ok_is_ok.
        eexists; split; cycle 1.
        Transparent interpret.
        simpl.

        rewrite Hs; simpl.
        (*rewrite Hother; *) reflexivity.
        Transparent state_to_values.
        simpl; rewrite find_add.

        f_equal.
        unfold shiftl_bvM.
        simp.
        rewrite List.firstn_app.
        simp.
        replace ((b + 1 - 2 ^ s)%nat) with O by lia.
        rewrite List.firstn_O.
        rewrite List.app_nil_r.
        erewrite list_firstn_skipn_succ by simp.
        rewrite List.nth_repeat; eauto. }
  - admit. (* var names property *)
  - admit. (* var names property *)
  - unfold shiftl_list; simp.
    rewrite List.firstn_app; simp.
    replace (b - 2 ^ s)%nat with O by lia; simp.

    Opaque Nat.sub.
    rewrite List.firstn_app; simp.
    replace (S b - 2 ^ s)%nat with O by lia; simp.

    replace (List.firstn (S b) (List.repeat <{ # 0 }> (2 ^ s)))
    with (List.firstn b (List.repeat <{ # 0 }> (2 ^ s)) ++l [List.nth b (List.repeat <{ # 0 }> (2 ^ s)) 0]); simp.
    erewrite list_firstn_succ by simp; simp. }

    Unshelve.
    all: eauto.
Admitted.

Lemma shiftl_layer_zero : forall s b n v1 v2 svar,
  run {|
    Input := (var_names v1 b ++ [svar])%list;
    Output := var_names v2 b;
    Program :=
      shiftl_layer svar
        (List.rev
          (zip 
            (var_names v2 b)
            (zip
               (List.map Var (var_names v1 b))
               (shiftl_list (Nat.pow 2 s) (List.map Var (var_names v1 b))))))
  |}
  (bvM.of_N b n ++ [0]) default_env 
  = Ok (bvM.of_N b n).
Proof.
  induction b; eauto.

  intros.
  (* some var names property we use a lot *)
  assert (~ List.In (v1 ++s to_string (N.of_nat b)) [svar]) by admit.
  assert (Hbig: (2 ^ s <= b \/ 2 ^ s > b)%nat) by lia.
     destruct Hbig.
  { replace 
    (shiftl_list (Nat.pow 2 s) (List.map Var (var_names v1 (S b)))) 
  with
    (shiftl_list (Nat.pow 2 s) (List.map Var (var_names v1 b)) ++ [Var (v1 ++ to_string (N.of_nat (b - Nat.pow 2 s)))])%list.
  rewrite! var_names_succ.
  rewrite! bvM.of_N_succ.
  rewrite! List.map_app.
  rewrite! zip_app; simp; try lia.
  rewrite List.rev_app_distr; simpl.
  apply run_split.
  - { replace (List.firstn b 
      (shiftl_bvM (Nat.pow 2 s)
      (bvM.of_N b n ++ [N.b2n (N.testbit n (N.of_nat b))])))
    with (shiftl_bvM (Nat.pow 2 s) (bvM.of_N b n)).
    rewrite <- List.app_assoc.
    rewrite <- List.app_assoc.
    apply run_extra_args with
      (iv := [(v1 ++ to_string (N.of_nat b))%string])
      (inp := [N.b2n (N.testbit n (N.of_nat b))]).
    apply List.Forall_cons; eauto.
    apply IHb; eauto.
    apply shiftl_bvM_length_equiv. }
  - { Opaque values_to_state.
      Opaque interpret.
      Opaque state_to_values.
      unfold run. simpl.
      assert (Hargs: List.length ((var_names v1 b ++ [v1 ++ to_string (N.of_nat b)]) ++ [svar]) = List.length ((bvM.of_N b n ++ [N.b2n (N.testbit n (N.of_nat b))]) ++ [0])).
      { rewrite! List.app_length.
        rewrite var_names_length.
        rewrite bvM.of_N_length.
        reflexivity. }
      apply values_to_state_ok in Hargs.
      destruct Hargs as [inp Hinp]; rewrite Hinp; simpl.

      (* get the values *)
      assert (Hs: M.find svar inp = Some 0) by admit. (* prove some map property *)
      assert (Hother: M.find (v1 ++ to_string (N.of_nat b)) inp = Some (N.b2n (N.testbit n (N.of_nat b)))) by admit.
      (*assert (Htmp: exists v, M.find (v1 ++ to_string (N.of_nat (b - Nat.pow 2 s))) inp = Some v).
       destruct Htmp as [other Hother].*)

      (* ok *)
      apply flat_map_ok_is_ok.
      eexists; split; cycle 1.
      Transparent interpret.
      simpl.

      rewrite Hs; simpl.
      rewrite Hother; reflexivity.

      Transparent state_to_values.
      simpl; rewrite find_add.

      reflexivity. }
  - admit.
  - admit.
  - rewrite var_names_succ.
    rewrite List.map_app; simp.
    unfold shiftl_list; simp.

    rewrite List.firstn_app.
    replace (List.firstn b (List.repeat <{ # 0 }> (2 ^ s))) with (List.repeat <{ # 0 }> (2 ^ s)); cycle 1.
    rewrite List.firstn_all2; simp.

    rewrite List.firstn_app.
    replace (List.firstn (b + 1) (List.repeat <{ # 0 }> (2 ^ s))) with (List.repeat <{ # 0 }> (2 ^ s)); cycle 1.
    rewrite List.firstn_all2; simp; lia.

    rewrite <- List.app_assoc; f_equal.
    simp.

    rewrite List.firstn_app; simp.
    assert (Htrivial: (2 <> 0)%nat) by lia.
    epose proof (Nat.pow_nonzero 2 s Htrivial).
    replace (b + 1 - 2 ^ s - b)%nat with O by lia; simp.
    replace (b + 1 - 2 ^ s)%nat with (S (b - 2 ^ s)) by lia.
    erewrite list_firstn_succ.
    f_equal.
    rewrite List.map_nth.
    rewrite var_names_spec; simp; lia.
    rewrite List.map_length; simp; lia. }
  { replace (shiftl_list (Nat.pow 2 s) (List.map Var (var_names v1 (S b)))) 
    with (shiftl_list (Nat.pow 2 s) (List.map Var (var_names v1 b)) ++ [<{ # 0 }>])%list.
    rewrite! var_names_succ.
    rewrite! bvM.of_N_succ.
    rewrite! List.map_app.
    rewrite! zip_app; simp; try lia.
    rewrite List.rev_app_distr; simpl.
    apply run_split.
    - { replace (List.firstn b 
        (shiftl_bvM (Nat.pow 2 s)
        (bvM.of_N b n ++ [N.b2n (N.testbit n (N.of_nat b))])))
      with (shiftl_bvM (Nat.pow 2 s) (bvM.of_N b n)).
      rewrite <- List.app_assoc.
      rewrite <- List.app_assoc.
      apply run_extra_args with
        (iv := [(v1 ++ to_string (N.of_nat b))%string])
        (inp := [N.b2n (N.testbit n (N.of_nat b))]).
      apply List.Forall_cons; eauto.
      apply IHb; eauto.
      apply shiftl_bvM_length_equiv. }
    - { Opaque values_to_state.
        Opaque interpret.
        Opaque state_to_values.
        unfold run. simpl.
        assert (Hargs: List.length ((var_names v1 b ++ [v1 ++ to_string (N.of_nat b)]) ++ [svar]) = List.length ((bvM.of_N b n ++ [N.b2n (N.testbit n (N.of_nat b))]) ++ [0])) by simp.
        apply values_to_state_ok in Hargs.
        destruct Hargs as [inp Hinp]; rewrite Hinp; simpl.

        (* get the values *)
        assert (Hs: M.find svar inp = Some 0) by admit. (* prove some map property *)
        assert (Hother: M.find (v1 ++ to_string (N.of_nat b)) inp = Some (N.b2n (N.testbit n (N.of_nat b)))) by admit.

        (* ok *)
        apply flat_map_ok_is_ok.
        eexists; split; cycle 1.
        Transparent interpret.
        simpl.

        rewrite Hs; simpl.
        rewrite Hother; reflexivity.
        Transparent state_to_values.
        simpl; rewrite find_add.

        reflexivity. }
  - admit.
  - admit.
  - unfold shiftl_list; simp.
    rewrite List.firstn_app; simp.
    replace (b - 2 ^ s)%nat with O by lia; simp.

    Opaque Nat.sub.
    rewrite List.firstn_app; simp.
    replace (S b - 2 ^ s)%nat with O by lia; simp.

    replace (List.firstn (S b) (List.repeat <{ # 0 }> (2 ^ s)))
    with (List.firstn b (List.repeat <{ # 0 }> (2 ^ s)) ++l [List.nth b (List.repeat <{ # 0 }> (2 ^ s)) 0]); simp.
    erewrite list_firstn_succ by simp; simp. }

    Unshelve.
    all: eauto.
Admitted.

Lemma shiftl_bvM_length : forall x b n,
  Datatypes.length (shiftl_bvM x (bvM.of_N b n)) = b.
Proof.
  intros.
  unfold shiftl_bvM.
  simp.
  lia.
Qed.

Lemma shiftl_bvM_equiv : forall x b n,
  shiftl_bvM x (bvM.of_N b n) = bvM.of_N b (N.shiftl n (N.of_nat x)).
Proof.
  intros.
  apply List.nth_ext with (d := 0) (d' := 0); simp.
  - apply shiftl_bvM_length.
  - rewrite shiftl_bvM_length; intros.
    unfold shiftl_bvM; rewrite list_fact; simp; try lia.
    rewrite bvM.of_N_spec; try lia.

    assert (Hnx: lt n0 x \/ ge n0 x) by lia; destruct Hnx.
    + rewrite N.shiftl_spec_low; simp; try lia.
      rewrite List.app_nth1; simp.
    + rewrite N.shiftl_spec_high; simp; try lia.
      rewrite List.app_nth2; simp.
      replace (N.of_nat n0 - N.of_nat x) with (N.of_nat (n0 - x)) by lia.
      rewrite bvM.of_N_spec; eauto; try lia.
Qed.

Lemma shiftl_layer_equiv : forall s b n i v1 v2 svar,
  let bit := N.b2n (N.testbit i (N.of_nat s)) in
  run {|
    Input := (var_names v1 b ++ [svar])%list;
    Output := var_names v2 b;
    Program :=
      shiftl_layer svar
        (List.rev
          (zip 
            (var_names v2 b)
            (zip
               (List.map Var (var_names v1 b))
               (shiftl_list (Nat.pow 2 s) (List.map Var (var_names v1 b))))))
  |}
  (bvM.of_N b n ++ [bit]) default_env 
  = Ok (bvM.of_N b (N.shiftl n (bit * 2 ^ (N.of_nat s)))).
Proof.
  intros.
  destruct (N.testbit i (N.of_nat s)); subst bit; simpl N.b2n.
  rewrite shiftl_layer_one.
  { f_equal; rewrite shiftl_bvM_equiv.
    repeat f_equal; rewrite Nat2N.inj_pow; lia. }
  rewrite shiftl_layer_zero; simpl.
  { rewrite N.shiftl_0_r; eauto. }
Qed.

(* zify. *)
(* need a lemma here about N_to_bvM being modulo *)
Lemma bvM_is_mod : forall s n n',
  n mod 2 ^ N.of_nat s = n' mod 2 ^ N.of_nat s
  -> bvM.of_N s n = bvM.of_N s n'.
Proof.
  intros.
  Search (List.nth).
  apply List.nth_ext with (d := 0) (d' := 0); simp.

  intros.
  rewrite! bvM.of_N_spec; eauto.

  rewrite <- N.mod_pow2_bits_low with (n := (N.of_nat s)) by lia.
  rewrite <- N.mod_pow2_bits_low with (n := (N.of_nat s)) (a := n') by lia.
  rewrite H.
  eauto.
Qed.

(*H0 : i < N.pos (2 ^ Pos.of_succ_nat s)
   bvM.of_N s (i mod 2 ^ N.of_nat s) = bvM.of_N s i*)

Theorem shiftl_equiv : forall s b n i,
  ge b (Nat.pow 2 s)
  (*-> n < 2 ^ (N.of_nat b)*)
  -> i < 2 ^ (N.of_nat s)
  -> run (shiftl_exp b s) (bvM.of_N b n ++ bvM.of_N s i) default_env
    = Ok (bvM.of_N b (N.shiftl n i)).
Proof.
  induction s.
  - simpl; intros.

    (* show no shift *)
    assert (i = 0) by lia; subst; rewrite N.shiftl_0_r.
    unfold shiftl_exp; rewrite var_names_nil; rewrite bvM.of_N_0; rewrite! List.app_nil_r.
    simpl.

    (* show run output is ok *)
    unfold run; simpl.
    assert (Hargs: List.length (var_names "x0" b) = List.length (bvM.of_N b n)).
    { rewrite var_names_length.
      rewrite bvM.of_N_length.
      reflexivity. }
    apply values_to_state_ok in Hargs.
    destruct Hargs as [inp Hinp]; rewrite Hinp; simpl.
    apply values_to_state_convertible; eauto.
    apply var_names_nodup.

  - simpl; intros.

    (* show recursive structure *)
    unfold shiftl_exp.
    rewrite var_names_succ.
    rewrite bvM.of_N_succ.
    do 2 rewrite List.app_assoc.
    simpl shiftl_exp_body.

    (* run seq *)
    eapply run_seq with (ov' := (var_names ("x" ++s to_string (N.of_nat s)) b) ++l [("i" ++s to_string (N.of_nat s))]).
    + replace (bvM.of_N s i) with (bvM.of_N s (i mod 2 ^ N.of_nat s)).
      eapply run_pass_through with
        (bv := [("i" ++s to_string (N.of_nat s))])
        (bv_vals := [N.b2n (N.testbit i (N.of_nat s))]); eauto.
        admit. (* var names list property *)
      apply IHs with (i := (i mod 2 ^ N.of_nat s)).
      lia.
      apply N.mod_lt; lia.
      Search (N.testbit).

      apply bvM_is_mod.
      rewrite N.mod_mod; lia.
    + replace (N.of_nat (S s)) with (N.of_nat s + 1) by lia.
      rewrite shiftl_layer_equiv.
      rewrite N.shiftl_shiftl.
      do 3 f_equal.
      apply i_mod_plus_bit; lia. (* prove some bits thing here, using H0 *)
    + admit. (* var names property *)
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
