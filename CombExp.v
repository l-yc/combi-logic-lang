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
Proof.
   Admitted.*)

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
Admitted.

Definition map_keys {elt: Type} (m : M.t elt) := List.map fst (M.elements m).

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

Theorem values_to_state_app : forall arg1 arg2 val1 val2 g,
  values_to_state (arg1 ++ arg2) (val1 ++ val2) = Ok g
  -> exists g1 g2, values_to_state arg1 val1 = Ok g1 /\ values_to_state arg2 val2 = Ok g2 /\ g = merge_fmap_seq g1 g2.
Proof.
Admitted.

Theorem values_to_state_app_2 : forall arg1 arg2 val1 val2 g1 g2,
  values_to_state arg1 val1 = Ok g1 /\ values_to_state arg2 val2 = Ok g2
  -> values_to_state (arg1 ++ arg2) (val1 ++ val2) = Ok (merge_fmap_seq g1 g2).
Proof.
Admitted.

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
  apply values_to_state_convertible'.
Qed.

Definition run (m : module) (inp : list N) (s : env) : result (list N) :=
  flat_map_ok
  (flat_map_ok (values_to_state (m.(Input)) inp) (fun g => interpret m.(Program) g s))
  (state_to_values m.(Output)).
(* }}} *)

  (*Theorem run_strengthen : forall i o c inp s r,
  run (NMod (NInput i) (NOutput o) c) inp s = r
  -> forall k v, run (NMod (NInput (i ++ [k])) (NOutput (o ++ [k])) c) (inp ++ [v]) s = r.
Proof.
     Admitted.*)

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

Definition zeroes (n : nat) : list N := List.repeat 0 n.
(*Fixpoint zeroes (n : nat) : list N :=
  match n with
  | O => []
  | S n' => 0 :: zeroes n'
   end.*)

Definition N_to_bvM (n : N) (m : nat) : list N :=
  if Nat.eqb m 0 then []
  else 
    let l := N_to_bv n in
    let len := (List.length l) in
    if Nat.leb len m then List.app l (zeroes (m - len)) else List.firstn m l.

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
  unfold zeroes.
  induction n; simpl; eauto.
  rewrite IHn; lia.
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

Lemma Pos_size : forall n m,
  Pos.le n m -> Pos.le (Pos.size n) (Pos.size m).
Proof.
  induction n; simpl; try lia; intros;
    induction m; simpl; try lia;
      rewrite <- Pos.succ_le_mono; apply IHn; lia.
Qed.

Lemma N_size : forall n m,
  n <= m -> N.size n <= N.size m.
Proof.
  induction n; simpl; try lia.
  induction m; simpl; try lia.
  apply Pos_size.
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
    replace (Nat.max (N.to_nat (N.size n)) (N.to_nat (N.size m))) with (N.to_nat (N.max (N.size n) (N.size m))) by lia.

    apply PeanoNat.Nat.le_trans with (m := (N.to_nat (N.size (2 * m + 1)))).
    + rewrite! N.size_log2 by lia.
      assert (N.log2 (n + m) <= N.log2 (2 * m + 1)).
      apply N.log2_le_mono.
      lia.
      lia.
    + rewrite! N.size_log2 by lia.
      rewrite N.log2_succ_double by lia.
      lia.

  - Search (N.leb).
    rewrite N.leb_gt in Heq.
    replace (Nat.max (N.to_nat (N.size n)) (N.to_nat (N.size m))) with (N.to_nat (N.max (N.size n) (N.size m))) by lia.

    apply PeanoNat.Nat.le_trans with (m := (N.to_nat (N.size (2 * n + 1)))).
    + rewrite! N.size_log2 by lia.
      assert (N.log2 (n + m) <= N.log2 (2 * n + 1)).
      apply N.log2_le_mono.
      lia.
      lia.
    + rewrite! N.size_log2 by lia.
      rewrite N.log2_succ_double by lia.
      lia.
Qed.

Lemma N_bv_len : forall m,
  gt m 0
  -> (forall n, 0 < n < (N.shiftl 1 (N.of_nat m))
  -> le (List.length (N_to_bv n)) m).
Proof.
  induction m; intros; simpl.
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

(* 4- Shifter {{{ *)
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
(* }}} *)

(* Generic shifter *)
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

(* MARK: Important lemma *)
(*Theorem shiftl_exp_body'_ok: forall nbits sbits base g g1 g2 s,
  interpret (shiftl_exp_body' nbits sbits) g s = Ok g1
  -> interpret base g1 s = Ok g2
  -> interpret (shiftl_exp_body' nbits sbits base) g s = Ok g2.
Proof.
   Admitted.*)


(*Definition shiftl_exp (nbits : nat) (sbits : nat) := 
  let sbits := PeanoNat.Nat.log2_up nbits in
  {|
    Input := List.app (var_names "x0" nbits) (var_names "i" sbits);
    Output := var_names ("x" ++ to_string (N.of_nat sbits)) nbits;
    Program := (shiftl_exp_body nbits sbits);
   |}.*)

Definition shiftl_exp (nbits : nat) (sbits : nat) := 
  {|
    Input := List.app (var_names "x0" nbits) (var_names "i" sbits);
    Output := var_names ("x" ++ to_string (N.of_nat sbits)) nbits;
    Program := (shiftl_exp_body nbits sbits);
  |}.

Definition shiftl (nbits : nat) (n i : N) :=
  let sbits := PeanoNat.Nat.log2_up nbits in
  run (shiftl_exp nbits sbits) ((N_to_bvM n nbits) ++ (N_to_bvM i sbits)) default_env.

Compute shiftl 6 12 0.

Ltac propositional :=
  repeat match goal with
  | [H: _ /\ _ |- _] => inversion H; clear H
  end.

(* MARK: some lemmas *)
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

Search N.shiftl.
(* _spec... *)

Compute (N_to_bv 0).
Lemma N_to_bvM_0_l : forall b,
  N_to_bvM 0 b = zeroes b.
Proof.
  induction b; simpl; eauto.
  assert (S b <> 0) by lia.
  unfold N_to_bvM; simpl.
  rewrite PeanoNat.Nat.sub_0_r.
  unfold zeroes; eauto.
Qed.

Lemma N_to_bvM_0_r : forall n,
  N_to_bvM n 0 = [].
Proof.
  eauto.
Qed.

Lemma N_to_bvM_length : forall n m,
  List.length (N_to_bvM n m) = m.
Proof.
  induction m; simpl; eauto.
  unfold N_to_bvM.
  assert (Nat.eqb (S m) 0 = false).
  rewrite PeanoNat.Nat.eqb_neq; lia.
  Opaque List.firstn.
  simpl.

  destruct (Nat.leb (Datatypes.length (N_to_bv n)) (S m)) eqn:Hle.
  - apply PeanoNat.Nat.leb_le in Hle.
    rewrite List.app_length.
    unfold zeroes.
    destruct (Datatypes.length (N_to_bv n)).
    + rewrite List.repeat_length; eauto.
    + rewrite List.repeat_length.
      rewrite PeanoNat.Nat.add_sub_assoc; lia.
  - destruct (Datatypes.length (N_to_bv n)) eqn:Heq.
    + inversion Hle.
    + apply PeanoNat.Nat.leb_gt in Hle.
      rewrite <- Heq in Hle.
      rewrite List.firstn_length.
      apply min_l; lia.
Qed.

Definition coerce (b : bool) : N := if b then 1 else 0.
Lemma N_to_bvM_succ : forall n m,
  N_to_bvM n (S m) = List.app (N_to_bvM n m) [coerce (N.testbit n (N.of_nat m))].
Proof.
Admitted.




Close Scope string_scope.
Open Scope N_scope.
Example generic_shiftl_test : shiftl 5 31 4 = Ok [0; 0; 0; 0; 1].
Proof. unfold shiftl. simpl. reflexivity. Qed.

(* MARK: some simple lemmas first *)
(*Lemma run_ok : forall m inp s bv,
  run m inp s = Ok bv
  -> run m inp s = Ok bv.
   Proof.*)

(* helpers above this *)

Lemma shiftl_ok : forall s b n i,
  Nat.log2 b = s /\ n < 2^(N.of_nat b) /\ i < n
  -> exists v, shiftl b n i = Ok v.
Proof.
Admitted.

Lemma run_seq : forall iv ov p1 p2 inp res,
  run {|
    Input := iv;
    Output := ov;
    Program := CSeq p1 p2
  |} inp default_env = Ok res
  <-> exists ov' res',
    run {|
      Input := iv;
      Output := ov';
      Program := p1
    |} inp default_env = Ok res' /\ 
    run {|
      Input := ov';
      Output := ov;
      Program := p2
    |} res' default_env = Ok res.
Proof.
Admitted.

Lemma run_extra_args : forall iv ov p inp res bv bv_vals iv' ov' inp' res',
  run {|
    Input := iv;
    Output := ov;
    Program := p 
  |} inp default_env = Ok res
  -> iv' = List.app iv bv
  -> ov' = List.app ov bv
  -> inp' = List.app inp bv_vals
  -> res' = List.app res bv_vals
  -> run {|
    Input := iv';
    Output := ov';
    Program := p
  |} inp' default_env = Ok res'.
Proof.
Admitted.


Lemma var_names_nodup : forall v n,
  List.NoDup (var_names v n).
Proof.
Admitted.

Open Scope list_scope.
Lemma zip_app {A} {B} : forall (a1 a2 : list A) (b1 b2 : list B),
  List.length a1 = List.length b1
  -> zip (a1 ++ a2) (b1 ++ b2) = zip a1 b1 ++ zip a2 b2.
Proof.
Admitted.
Close Scope list_scope.

Open Scope string_scope.
Lemma shiftl_0_r' : forall s b n,
  ge b (Nat.pow 2 s)
  -> n < 2 ^ (N.of_nat b)
  -> run (shiftl_exp b s) (N_to_bvM n b ++ N_to_bvM 0 s) default_env = Ok (N_to_bvM (N.shiftl n 0) b).
Proof.
  induction s.
  - simpl; intros.
    unfold shiftl_exp; simpl.
    rewrite var_names_nil.
    rewrite N_to_bvM_0_r.
    rewrite! List.app_nil_r.
    unfold run; simpl.

    (* get rid of values_to_state *)
    assert (Heq: List.length (var_names "x0" b) = List.length (N_to_bvM n b)).
    { 
      rewrite! var_names_length.
      rewrite! N_to_bvM_length.
      eauto.
    }
    apply values_to_state_ok in Heq.
    destruct Heq as [sval Hval].
    rewrite Hval; simpl.

    (* get rid of state_to_values *)
    replace (String (Ascii.Ascii false false false true true true true false)
        (to_string 0)) with "x0" by reflexivity.
    apply values_to_state_convertible in Hval.
    rewrite Hval; rewrite N.shiftl_0_r; eauto.
    apply var_names_nodup.
  - simpl; intros.
    assert (Hs: ge b (Nat.pow 2 s)) by lia.
    specialize (IHs b n Hs H0).

    (*unfold shiftl_exp in IHs.
    unfold shiftl_exp.
    rewrite var_names_succ.
       unfold shiftl_exp_body.*)

    apply run_seq.
    do 2 eexists; split.
    + rewrite var_names_succ.
      rewrite N_to_bvM_succ.
      do 2 rewrite List.app_assoc.
      erewrite run_extra_args.
      reflexivity.
      exact IHs.
      reflexivity.
      reflexivity.
      reflexivity.
      reflexivity.
    + Opaque String.append.
      (*unfold run; simpl.*)

      (* evaluate this layer *)
      replace (N.pos (Pos.of_succ_nat s)) with (N.of_nat s + 1) by lia.
      induction (var_names ("x" ++ to_string (N.of_nat s)) b).
      induction b.
      * eauto.
      * rewrite! var_names_succ. 
        rewrite! List.map_app.
        (* need to handle modulo here, but we assert sth false first *)
        assert (Hfalse:
        (shiftl_list (Nat.pow 2 s)
                    (List.map Var
                       (var_names ("x" ++ to_string (N.of_nat s)) b) ++
                     List.map Var
                       [("x" ++ to_string (N.of_nat s)) ++
                        to_string (N.of_nat b)]))
        = List.app (shiftl_list (Nat.pow 2 s)
                      (List.map Var
                         (var_names ("x" ++ to_string (N.of_nat s)) b))) 
                   (List.map Var
                     [("x" ++ to_string (N.of_nat s)) ++
                      to_string (N.of_nat b)])).
        admit.
        rewrite Hfalse; clear Hfalse.
        rewrite! zip_app; simpl.
        rewrite List.rev_app_distr.
        simpl shiftl_layer.
        apply run_seq.
        do 2 eexists; split.
        (*eapply run_extra_args; eauto.
        apply IHb; eauto; try lia.
        ; eauto.
           admit.*)
        admit.
        

        (* get rid of values_to_state *)
        assert (Heq: List.length (var_names ("x" ++ to_string (N.of_nat s)) b ++
           ["i" ++ to_string (N.of_nat s)]) = List.length (N_to_bvM (N.shiftl n 0) b ++ [0])).
        { 
          rewrite! List.app_length.
          rewrite var_names_length.
          rewrite N_to_bvM_length.
          eauto.
        }
        apply values_to_state_ok in Heq.
        destruct Heq as [sval Hval].
        rewrite Hval; simpl.



        rewrite! var_names_length.
        

      (*(* get rid of state_to_values *)
      apply values_to_state_convertible in Hval.
         rewrite Hval; rewrite N.shiftl_0_r; eauto.*)
      apply var_names_nodup.


      (*unfold run; simpl.
      unfold shiftl_exp in IHs.
      unfold shiftl_exp_body in IHs.
         simpl.*)
      admit.
Admitted.
Close Scope string_scope.

Lemma shiftl_shiftl' : forall b n i j,
  ge b (Nat.pow 2 s)
  -> n < 2 ^ (N.of_nat b)
    (*-> run (shiftl_exp b s) (N_to_bvM n b ++ N_to_bvM i s) default_env = Ok (N_to_bvM (N.shiftl n i) b).

       shiftl b n (i + j) = Ok (N_to_bvM (N.shiftl (N.shiftl n i) j) b).*)
Proof.
  intros.
  unfold shiftl.
Admitted.

Lemma shiftl_equiv' : forall s b n i,
  ge b (Nat.pow 2 s)
  -> n < 2 ^ (N.of_nat b)
  -> run (shiftl_exp b s) (N_to_bvM n b ++ N_to_bvM i s) default_env = Ok (N_to_bvM (N.shiftl n i) b).
Proof.
  (*induction s.
  - simpl; intros.
    apply shiftl_0_r'; eauto.
     - admit.*)

  intros; unfold shiftl.
  intros; induction i using N.peano_ind.
  + apply shiftl_0_r'; eauto.
  + replace (N.succ i) with (i + 1) by lia.
    rewrite shiftl_shiftl.
    f_equal; f_equal.
    apply N.shiftl_shiftl.

Admitted.

(* MARK: OK, so it seems like we will need 2 lemmas:
   - shiftl_0_r
   - shiftl_shiftl
   And those should be enough.
 *)



Lemma shiftl_0_r : forall b n,
  n < 2^(N.of_nat b)
  -> shiftl b n 0 = Ok (N_to_bvM n b).
Proof.
  intros.
  unfold shiftl; rewrite N_to_bvM_0_l.
  unfold run; unfold shiftl_exp; simpl.
  induction b.
  - eauto.
  - (* here, we have to split N into 2 parts *)
    (* if N satisfies IH, we can just use that *)
    (* otherwise, we have to handle the extra bit separately *)
    assert (Hfalse : n < 2 ^ N.of_nat b). admit.
    specialize (IHb Hfalse).
    apply flat_map_ok_is_ok in IHb; destruct IHb as [e1 [IHb1 IHb]].
    apply flat_map_ok_is_ok in IHb; destruct IHb as [e2 [IHb2 IHb3]].
    apply values_to_state_app in IHb3; destruct IHb3 as [g1 [g2 [IHb3a [IHb3b IHb3c]]]].

    eapply flat_map_ok_is_ok; eexists; split; cycle 1.
    + eapply flat_map_ok_is_ok; eexists; split; cycle 1.
      * eapply values_to_state_app_2.
        split.
        { rewrite var_names_succ.
          rewrite N_to_bvM_succ.
          eapply values_to_state_app_2.
          split.
          - eassumption.
          - reflexivity. }
        { admit. }
      * admit.
    + admit.
Admitted.

Lemma shiftl_0_l : forall b i,
  i < N.of_nat b
  -> shiftl b 0 i = Ok (N_to_bvM 0 b).
Proof.
Admitted.

(*Lemma shiftl_shiftl : forall s b n i j,
  b = Nat.pow 2 s ->
  shiftl b n (i + j) = Ok (N_to_bvM (N.shiftl (N.shiftl n i) j) b).
Proof.
  intros.
  unfold shiftl; unfold shiftl_exp.
  induction s.
  simpl.
  unfold run.
   Admitted.*)

Lemma shiftl_shiftl : forall b n i j,
  shiftl b n (i + j) = Ok (N_to_bvM (N.shiftl (N.shiftl n i) j) b).
Proof.
  intros.
  unfold shiftl.
Admitted.

Theorem shiftl_equiv'' : forall b n i,
  i < N.of_nat b /\ n < 2^(N.of_nat b)
  -> shiftl b n i = Ok (N_to_bvM (N.shiftl n i) b).
Proof.
  intros; unfold shiftl.
  apply shiftl_equiv'.
  intros; induction i using N.peano_ind.
  + rewrite N.shiftl_0_r. apply shiftl_0_r. lia.
  + replace (N.succ i) with (i + 1) by lia.
    rewrite shiftl_shiftl.
    f_equal; f_equal.
    apply N.shiftl_shiftl.
Qed.
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
