Set Warnings "-notation-overridden,-parsing".

Require Import Init.
Require Import Coq.Arith.PeanoNat.
Require Import NArith.
Require Import ZArith.
Require Import String.
Require Import Lists.List.
Import ListNotations.


Set Implicit Arguments.

(* CAT-like *)

Inductive instr : Type :=
  | IENop
  | IEQuot : list instr -> instr
  | IENum : Z -> instr
  | IEBool : bool -> instr
  | IFEval
  | IPLteq
  | IPIf
  | IPPop
  | IPDup
  | IPSwap
  | IPDip
  | IBNot
  | IBAnd
  | IBOr
  | INPlus
  | INMinus
  | INMult
  .

Inductive data :=
| DNum : Z -> data
| DBool : bool -> data
| DQuot : list instr -> data
.

Inductive type : Set :=
| TNum
| TBool
| TVar : nat -> type
| TQuot : exp_type -> type
with exp_type : Set :=
| TArrow : list type -> list type -> exp_type.

Scheme type_ind' := Minimality for type Sort Prop
with exp_type_ind' := Minimality for exp_type Sort Prop.

Hint Constructors type.
Hint Constructors exp_type.

Fixpoint type_dec (t1 t2 : type) {struct t1} : { t1 = t2 } + { t1 <> t2 }
with exp_type_dec (t1 t2 : exp_type) { struct t1} : { t1 = t2 } + { t1 <> t2 }.
Proof.
  decide equality.
  decide equality.
  destruct t1, t2; decide equality.
  apply list_eq_dec. apply type_dec.
  apply list_eq_dec. apply type_dec.
Qed.

(* Coercion TVar : atom >-> type. *)

(* This arrow uses stack variables *)
Notation "x ---> y" := (TArrow x y) (at level 70) : type_scope.
Notation "---> y" := (TArrow [] y) (at level 70) : type_scope.
Notation "x --->" := (TArrow x []) (at level 70) : type_scope.

Notation "x ===> y" := (TQuot (TArrow x y)) (at level 65) : type_scope.
Notation "===> y" := (TQuot (TArrow [] y)) (at level 65) : type_scope.
Notation "x ===>" := (TQuot (TArrow x [])) (at level 65) : type_scope.


Inductive has_type : list instr -> exp_type -> Prop :=
| HtNil : forall A, has_type [] (A ---> A)
| HtENop : forall A B is,
    has_type is (A ---> B) ->
    has_type (IENop :: is) (A ---> B)
| HtEQuot : forall A B C D e is,
    has_type e (A ---> B) ->
    has_type is ((A ===> B) :: C ---> D) ->
    has_type (IEQuot e :: is) (C ---> D)
(*   ENum : -> int *)
| HtENum : forall A B n is,
    has_type is ((TNum :: A) ---> B) ->
    has_type (IENum n :: is) (A ---> B)
(*   EBool : -> int *)
| HtEBool : forall A B b is,
    has_type is ((TBool :: A) ---> B) ->
    has_type (IEBool b :: is) (A ---> B)
  (* eval : 'A ('A -> 'B) -> 'B *)
| HtFEval : forall A B C is,
    has_type is (B ---> C) ->
    has_type (IFEval :: is) ((A ===> B) :: A ---> C)
(*   lteq : int int -> bool *)
| HtPLteq : forall A B is,
    has_type is ((TBool :: A) ---> B) ->
    has_type (IPLteq :: is) (TNum :: TNum :: A ---> B)
(*   if : 'A bool ('A -> 'B) ('A -> 'B) -> 'B *)
| HtPIf : forall A B C is,
    has_type is (B ---> C) ->
    has_type (IPIf :: is) (TBool::(TQuot (A ---> B))::(TQuot (A ---> B))::A ---> C)
(*   pop : 'a -> *)
| HtPPop : forall A B x is,
    has_type is (A ---> B) ->
    has_type (IPPop :: is) (x :: A ---> B)
(*   dup : 'a -> 'a 'a *)
| HtPDup : forall A B a is,
    has_type is ((a :: a :: A) ---> B) ->
    has_type (IPDup :: is) (a :: A ---> B)
(*   swap : 'a 'b -> 'b 'a *)
| HtPSwap : forall A B a b is,
    has_type is (b :: a :: A ---> B) ->
    has_type (IPSwap :: is) (a :: b :: A ---> B)
(*   dip : 'A 'b '('A -> 'C) -> 'C 'b *)
| HtPDip : forall A B b C is,
    has_type is (b :: B ---> C) ->
    has_type (IPDip :: is) (((A ===> B) :: b :: A) ---> C)
(* not : bool -> bool *)
| HtBNot : forall A B is,
    has_type is (TBool :: A ---> B) ->
    has_type (IBNot :: is) (TBool :: A ---> B)
(* and : bool bool -> bool *)
| HtBAnd : forall A B is,
    has_type is (TBool :: A ---> B) ->
    has_type (IBAnd :: is) (TBool :: TBool :: A ---> B)
(* or : bool bool -> bool *)
| HtBOr : forall A B is,
    has_type is (TBool :: A ---> B) ->
    has_type (IBOr :: is) (TBool :: TBool :: A ---> B)
(* plus : num num -> num *)
| HtNPlus : forall A B is,
    has_type is (TNum :: A ---> B) ->
    has_type (INPlus :: is) (TNum :: TNum :: A ---> B)
(* minus : num num -> num *)
| HtNMinus : forall A B is,
    has_type is (TNum :: A ---> B) ->
    has_type (INMinus :: is) (TNum :: TNum :: A ---> B)
(* mult : num num -> num *)
| HtNMult : forall A B is,
    has_type is (TNum :: A ---> B) ->
    has_type (INMult :: is) (TNum :: TNum :: A ---> B).

Hint Constructors has_type.

Notation "'ID'" := IENop : cat_scope.
Notation "'EVAL'" := IFEval : cat_scope.
Notation "{ x , .. , y }" := (IEQuot (cons x .. (cons y nil) ..)) : cat_scope.
Notation " x 'num'" := (IENum x) (at level 91) : cat_scope.
Notation "'TRUE'" := (IEBool true) : cat_scope.
Notation "'FALSE'" := (IEBool false) : cat_scope.
Notation "'.<='" := (IPLteq) : cat_scope.
Notation "'DUP'" := (IPDup) : cat_scope.
Notation "'POP'" := (IPPop) : cat_scope.
Notation "'SWAP'" := (IPSwap) : cat_scope.
Notation "'DIP'" := (IPDip) : cat_scope.
Notation "'IF?'" := (IPIf) : cat_scope.
Notation "~" := (IBNot) : cat_scope.
Notation "&&" := (IBAnd) : cat_scope.
Notation ".||" := (IBOr) : cat_scope.
Notation ".+" := (INPlus) : cat_scope.
Notation ".-" := (INMinus) : cat_scope.
Notation ".*" := (INMult) : cat_scope.

Open Scope cat_scope.

Ltac typecheck := repeat econstructor.

Theorem example : has_type (rev [.*; (3 num); (2 num)]) (---> [TNum]).
Proof. typecheck. Qed.

Theorem example_quot : forall A, has_type [DUP] ([A] ---> [A; A] ).
Proof. typecheck. Qed.

Theorem example_eval : has_type [{DUP, .*}; EVAL]  ([TNum] ---> [TNum]).
Proof. typecheck. Qed.

Theorem example2 : has_type (rev [.+; .*; DIP; { DUP }; (2 num); (3 num)]) (---> [TNum]).
Proof. typecheck. Qed.

Theorem example_if : has_type (rev [IF?; TRUE; { 3 num }; { 2 num }]) (---> [TNum]).
Proof. typecheck. Qed.

(*

1. Typechecker
2. Evaluator
3. Progress and preservation
4. Decidable termination

*)

Definition stack := list data.

Close Scope cat_scope.

Open Scope Z_scope.

(* instructions -> stack before -> stack after *)
Inductive EvalR : list instr -> stack -> stack -> Prop :=
  | EmptyR : forall dst,
    EvalR [] dst dst

  | PlusR : forall ist dst1 dst2 m n,
    forall mn, mn = m + n ->
    EvalR ist (DNum mn :: dst1) dst2 ->
    EvalR (INPlus :: ist) (DNum n :: DNum m :: dst1) dst2

  | MinusR : forall ist dst1 dst2 m n,
    forall mn, mn = n - m ->
    EvalR ist (DNum mn :: dst1) dst2 ->
    EvalR (INMinus :: ist) (DNum n :: DNum m :: dst1) dst2
    
  | MultR : forall ist dst1 dst2 m n,
    forall mn, mn = m * n ->
    EvalR ist (DNum mn :: dst1) dst2 ->
    EvalR (INMult :: ist) (DNum n :: DNum m :: dst1) dst2
  
  | AndR : forall ist dst1 dst2 a b,
    forall c, c = andb a b ->
    EvalR ist (DBool c :: dst1) dst2 ->
    EvalR (IBAnd :: ist) (DBool a :: DBool b :: dst1) dst2
  
  | OrR : forall ist dst1 dst2 a b,
    forall c, c = orb a b ->
    EvalR ist (DBool c :: dst1) dst2 ->
    EvalR (IBOr :: ist) (DBool a :: DBool b :: dst1) dst2
  
  | NotR : forall ist dst1 dst2 a,
    EvalR ist (DBool (negb a) :: dst1) dst2 ->
    EvalR (IBNot :: ist) (DBool a :: dst1) dst2
  
  | LteqTrueR : forall ist dst1 dst2 m n, m <= n ->
    EvalR ist (DBool true :: dst1) dst2 ->
    EvalR (IPLteq :: ist) (DNum n :: DNum m :: dst1) dst2
  
  | LteqFalseR : forall ist dst1 dst2 m n, m > n ->
    EvalR ist (DBool false :: dst1) dst2 ->
    EvalR (IPLteq :: ist) (DNum n :: DNum m :: dst1) dst2
  
  | PopR : forall ist dst1 dst2 x,
    EvalR ist dst1 dst2 ->
    EvalR (IPPop :: ist) (x :: dst1) dst2

  | DupR : forall ist dst1 dst2 x,
    EvalR ist (x :: x :: dst1) dst2 ->
    EvalR (IPDup :: ist) (x :: dst1) dst2

  | SwapR : forall ist dst1 dst2 x y,
    EvalR ist (y :: x :: dst1) dst2 ->
    EvalR (IPSwap :: ist) (x :: y :: dst1) dst2

  | NumR : forall ist dst1 dst2 n,
    EvalR ist (DNum n :: dst1) dst2 ->
    EvalR (IENum n :: ist) dst1 dst2

  | BoolR : forall ist dst1 dst2 b,
    EvalR ist (DBool b :: dst1) dst2 ->
    EvalR (IEBool b :: ist) dst1 dst2

  | NopR : forall ist dst1 dst2,
    EvalR ist dst1 dst2 ->
    EvalR (IENop :: ist) dst1 dst2

  | QuotR : forall ist dst1 dst2 q,
    EvalR ist (DQuot q :: dst1) dst2 ->
    EvalR (IEQuot q :: ist) dst1 dst2

  | EvalQuotR : forall ist dst1 dst2 dst3 f,
    EvalR f dst1 dst2 ->
    EvalR ist dst2 dst3 ->
    EvalR (IFEval :: ist) (DQuot f :: dst1) dst3

  | DipR : forall ist dst1 dst2 dst3 f x,
    EvalR f dst1 dst2 ->
    EvalR ist (x :: dst2) dst3 ->
    EvalR (IPDip :: ist) (DQuot f :: x :: dst1) dst3

  | IfTrueR : forall ist dst1 dst2 dst3 l r,
    EvalR l dst1 dst2 ->
    EvalR ist dst2 dst3 ->
    EvalR (IPIf :: ist) (DBool true :: DQuot l :: DQuot r :: dst1) dst3

  | IfFalseR :  forall ist dst1 dst2 dst3 l r,
    EvalR r dst1 dst2 ->
    EvalR ist dst2 dst3 ->
    EvalR (IPIf :: ist) (DBool true :: DQuot l :: DQuot r :: dst1) dst3
.

Hint Constructors EvalR.

Section ComputationExamples.
  Variable i : list instr.
  Variable d : stack.

  Example ex_plus_sing: EvalR [INPlus] [DNum 3; DNum 2] [DNum 5].
  Proof.
    eauto.
  Qed.
  
  Example involved :
    EvalR [IENum 2; IENum 3; IEQuot [IPDup]; IPDip; INMult; INPlus] [] [DNum 8].
  Proof.
    apply NumR.
    apply NumR.
    apply QuotR.
    eapply DipR.
    apply DupR. apply EmptyR.
    eapply MultR. simpl.
    eauto.
    eapply PlusR. simpl.
    eauto.
    apply EmptyR.
  Qed.

  (* Example ex_plus :
     EvalR (INPlus :: i) (DNum 3 :: DNum 2 :: d) -> EvalR i (DNum 5 :: d).
  eauto. Qed.

  Example ex_lteq_true : forall (m n : Z), m <= n ->
                                 EvalR (IPLteq :: i) (DNum n :: DNum m :: d) ->
                                 EvalR i (DBool true :: d).
  eauto. Qed.

  Example ex_lteq_false : forall (m n : Z), m > n ->
                                 EvalR (IPLteq :: i) (DNum n :: DNum m :: d) ->
                                 EvalR i (DBool false :: d).
  eauto. Qed.

  Example ex_pop : forall (x : data), EvalR (IPPop :: i) (x :: d) -> EvalR i d.
  eauto. Qed.

  Example ex_dup : forall (x : data), EvalR (IPDup :: i) (x :: d) -> EvalR i (x :: x :: d).
  eauto. Qed. *)
End ComputationExamples.

Section Correctness.

  Definition last_ind (l : list nat) : nat :=
    fold_left (fun m x => max m x) l O.
  
  Fixpoint type_to_nat (t : type) : nat :=
    match t with
    | TNum => 0
    | TBool => 0
    | TVar n => n
    | TQuot (TArrow l1 l2) => max (last_ind (map type_to_nat l1)) (last_ind (map type_to_nat l2))
    end.

  Definition fresh_ind (t : exp_type) : nat := 
    match t with
      TArrow l1 l2 => 1 + max (last_ind (map type_to_nat l1)) (last_ind (map type_to_nat l2))
    end.

  Fixpoint tmatch (a b : type) : bool :=
    match (a, b) with
    | (TNum, TNum) => true
    | (TBool, TBool) => true
    | (TVar n, x) => true
    | (x, TVar n) => true
    | (TQuot et1, TQuot et2) => exp_types_match et1 et2
    | p => false
    end
  with types_match (a b : list type) : bool :=
    forallb (fun p => tmatch (fst p) (snd p)) (combine a b)
  with exp_types_match (a b : exp_type) : bool :=
    match (a, b) with
    | (TArrow a b, TArrow c d) => andb (types_match a c) (types_match b d)
    end.
  
  
  Definition type_check : forall is : list instr, option (sig (fun t : exp_type => has_type is t)).
    refine (fix F (is : list instr) : option (sig (fun t : exp_type => has_type is t)) :=
    match is return option (sig (fun t : exp_type => has_type is t)) with
    | [] => exist _ (TArrow (TVar 0) (TVar 0)) _
    | (IENop :: is) => F is
    | (IEQuot e :: is) => let
        (TArrow a b, p) := F e;
        (TArrow (TQuot (TArrow a b) :: c) d, p1) := F is
      in exist _ (TArrow c d) _
    | (IENum n :: is) => let
        (TArrow (TNum :: a) b, p) := F is
      in exist _ (TArrow a b) _
    | (IEBool v :: is) => let
        (TArrow (TBool :: a) b, p) := F is
      in exist _ (TArrow a b) _
    | (IFEval :: is) => let
        (TArrow b c, p) := F is
      in exist _ (TArrow ((TQuot (TArrow a b)) :: a) c) _
    | (IPLteq :: is) => let
        (TArrow (TBool :: a) b, p) := F is
      in exist _ (TArrow (TNum :: TNum :: a) b) _
    | (IPIf :: is) => let
        (TArrow b c, p) := F is
      in exist _ (TArrow (TBool :: (TQuot (A ---> B)) :: (TQuot (A ---> B)) :: a) c) _
    | (IPPop :: is) => let
        (TArrow a b, p) := F is;
        tvar := TVar (fresh_ind (TArrow a b))
      in exist _ (TArrow (tvar :: a) b) _
    | (IPDup :: is) => let
        (TArrow (x :: x :: a) b, p) := F is;
      in exist _ (TArrow (x :: a) b) _
    | (IPSwap :: is) => let
        (TArrow (x :: y :: a) b, p) := F is;
      in exist _ (TArrow (y :: x :: a) b) _
    | (IPDip :: is) => let
        (TArrow (x :: b) c, p) := F is
      in exist _ (TArrow ((TQuot (TArrow a b)) :: x :: a) c) _
    | (IBNot :: is) => let
        (TArrow (TBool :: a) b, p) := F is
      in exist _ (TArrow (TBool :: a) b) _
    | (IBAnd :: is) => let
        (TArrow (TBool :: a) b, p) := F is
      in exist _ (TArrow (TBool :: TBool :: a) b) _
    | (IBOr :: is) => let
        (TArrow (TBool :: a) b, p) := F is
      in exist _ (TArrow (TBool :: TBool :: a) b) _
    | (INPlus :: is) => let
        (TArrow (TNum :: a) b, p) := F is
      in exist _ (TArrow (TNum :: TNum :: a) b) _
    | (INMinus :: is) => let
        (TArrow (TNum :: a) b, p) := F is
      in exist _ (TArrow (TNum :: TNum :: a) b) _
    | (INMult :: is) => let
        (TArrow (TNum :: a) b, p) := F is
      in exist _ (TArrow (TNum :: TNum :: a) b) _
    end).
  Defined.
  

  Definition get_type (d : data) : type :=
    match d with
    | DNum _ => TNum
    | DNool _ => TBool
    | DQuot is => TQuot (type_check is)
    end.
  

  Definition stacks_type (dst1 dst2 : list data) :=
    let tl1 := map get_type dst1;
        tl2 := map get_type dst2
    in TArrow tl1 tl2.
 

  Inductive stacks_type : stack -> stack -> exp_type -> Prop :=
  | SsTEmptyB : stacks_type [] [] (TArrow [] [])
  | SsTEmptyL : forall A AT,
      stack_type A AT ->
      stacks_type [] A (TArrow [] AT)
  | SsTEmptyR : forall A AT,
      stack_type A AT ->
      stacks_type A [] (TArrow AT [])
  | SsTEmptyN : forall A B AT BT,
      stack_type A AT ->
      stack_type B BT ->
      stacks_type A B (TArrow AT BT)
  with stack_type : stack -> list type -> Prop :=
  | StEmpty : stack_type [] []
  | StNum   : forall n s t,
      stack_type s t ->
      stack_type (DNum n :: s)  (TNum :: t)
  | StBool  : forall b s t,
      stack_type s t ->  
      stack_type (DBool b :: s) (TBool :: t)
  | StQuot  : forall is t s st,
      has_type is t ->
      stack_type s st ->
      stack_type (DQuot is :: s) (TQuot t :: st).

  Hint Constructors stack_type.
  Hint Constructors stacks_type.

  Lemma IENop_type: forall is t, has_type is t -> has_type (IENop :: is) t.
  Proof.
    intros.
    destruct t.
    eapply HtENop.
    assumption.
  Qed.

  Lemma IENop_type_r: forall is t, has_type (IENop :: is) t -> has_type is t.
  Proof.
    intros.
    destruct t.
    inversion H.
    assumption.
  Qed.

  Fixpoint nil_type_nil_data dst : stack_type dst [] -> dst = [].
  Proof.
    intros.
    destruct dst.
    - reflexivity.
    - (* symmetry. eapply nil_cons. *)
      inversion H.
  Qed.

  Theorem eq_stack_eq_type:
    forall dst A B, stacks_type dst dst (A ---> B) -> A = B.
  Proof.
    intros.
    induction dst.
    + inversion H.
      - reflexivity.
      - inversion H3. reflexivity.
      - inversion H3. reflexivity.
      - inversion H4. inversion H5. reflexivity.
    + inversion H. inversion H4. inversion H5.
      - (* oops... *)
  Qed.
  

  Theorem preservation:
    forall is dst1 dst2 t,
    has_type is t ->
    EvalR is dst1 dst2 ->
    stacks_type dst1 dst2 t.
  Proof.
    intros.
    induction is. (* Wrong induction hypothesis? *)
    - inversion H0. destruct t. inversion H. apply eq_stack_eq_type.
  Qed.

End Correctness.


(* big-step evaluator *)
(* ql stands for quot list *)
Fixpoint stack_eval (ql : list istack) (ist : istack) (dst : dstack) {struct ist} : option dstack :=
match ist with
| nil => Some dst
| cons i ist' =>
  match i with
  | EId =>
    let ql' := match ql with
    | nil => nil
    | cons x qtl => (i :: x) :: qtl
    end in
    stack_eval ql' ist' dst
  | EQuot => stack_eval (nil::ql) ist' dst
  | EQuotEnd =>
    match ql with
    | nil => None
    | cons q qtl => stack_eval qtl ist' (DQuot q :: dst)
    end
  | EConst d =>
    let ql' := match ql with
    | nil => nil
    | cons x qtl => (i :: x) :: qtl
    end in
    stack_eval ql' ist' dst
  | FEval =>
    match ql with
    | nil => None
    | cons q qst =>
      match qst with
      | nil => stack_eval nil (q ++ ist') dst
      | h :: qst' => stack_eval ((q::h)::qst') ist' dst
      end
    end
  | PLteq =>
    (* let ql' := match ql with *)
    (* | nil => *)
    (*   match dst with *)
    (*   | DNum x :: DNum y :: tl => stack_eval ist' ((DBool (x <=? y)) :: tl) *)
    (*   | _ => None *)
    (*   end *)
    (* | cons x qtl => *)
    (* in stack_eval ((i :: x) :: qtl) ist' *)
    (* end *)
  | PPop =>
    match dst with
    | nil => None
    | x :: tl => stack_eval ist' tl
    end
  | PDup =>
    match dst with
    | nil => None
    | cons x tl => stack_eval ist' (x :: x :: tl)
    end
  | PSwap =>
    match dst with
    | x :: y :: tl => stack_eval ist' (y :: x :: tl)
    | _ => None
    end
  | PDip =>
    match dst with
    | nil => None
    | cons x tl =>
      match stack_eval ist' tl with
      | Some tl' =>
        match ist' with
        | nil => None
        | cons x ist'' => stack_eval ist'' tl'
        end
      | None => None
      end
    end

  | PIf =>
    match dst with
    | nil => None
    | c :: dtl =>
      match c with
      | DBool true =>
        match ist' with
        | f :: _ :: itl => stack_eval (f::itl) dtl
        | _ => None
        end
      | DBool false =>
        match ist' with
        | _ :: f :: itl => stack_eval (f::itl) dtl
        | _ => None
        end
      | _ => None
      end
    end

  | BNot =>
    match dst with
    | cons (DBool b) dst' => stack_eval ist' (DBool (negb b) :: dst')
    | _ => None
    end
  | BAnd =>
    match dst with
    | (DBool x) :: (DBool y) :: dst' => stack_eval ist' (DBool (andb y x) :: dst')
    | _ => None
    end
  | BOr =>
    match dst with
    | (DBool x) :: (DBool y) :: dst' => stack_eval ist' (DBool (orb y x) :: dst')
    | _ => None
    end
  | NAdd =>
    match dst with
    | (DNum x) :: (DNum y) :: dst' => stack_eval ist' (DNum (y + x) :: dst')
    | _ => None
    end
  | NMinus =>
    match dst with
    | (DNum x) :: (DNum y) :: dst' => stack_eval ist' (DNum (y - x) :: dst')
    | _ => None
    end
  | NMult =>
    match dst with
    | (DNum x) :: (DNum y) :: dst' => stack_eval ist' (DNum (y * x) :: dst')
    | _ => None
    end
  end
end
.

Open Scope list_scope.
Example ex1 : stack_eval [EConst (DNum 3); EConst (DNum 4); NAdd] [] = Some [DNum 7].
Proof. reflexivity. Qed.


(* naive *)
Inductive type :=
  | int : type
  | arrow : type -> type -> type
.

Class StackFrame A : Type :=
  {
    stype : A -> type
  }.

Instance stackFrameZ : StackFrame Z :=
  {
    stype := fun _ => int
  }.

(* Existentially quantified stack frame
FIXME: can i do this w/o explicit wrapper? exists seems to work only with Prop's
 *)
Inductive ESF : Type :=
  | E : forall {A : Type} `{StackFrame A}, A -> ESF.

Definition three : Z := 3.

Check (E three).

Definition to_stype : ESF -> type := fun e =>
  match e with
  | E x => stype x
  end.

Example to_stype_works : to_stype (E three) = int.
reflexivity. Qed.

Inductive sinstr : Type :=
| SPush : ESF -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr
| SIf : sinstr -> sinstr -> sinstr -> sinstr
| STrue : sinstr
| SFalse : sinstr
| SAnd : sinstr -> sinstr -> sinstr
| SOr : sinstr -> sinstr -> sinstr
| SNot : sinstr -> sinstr
| SWhile : sinstr -> sinstr
.

Definition not_empty {A} (l: list A) : bool :=
match l with
  | nil => false
  | _ => true
end.

Inductive nonempty (A : Type) : Type :=
  | ncons : A -> list A -> nonempty A.

Infix ":::" := ncons (at level 60, right associativity) : nonempty_scope.

Definition stack := nonempty ESF.

Definition to_list (A : Type) (ne : nonempty A) : list A :=
  match ne with
  | ncons x x0 => x :: x0
  end.

Theorem nonempty_nonempty_list : forall {A} (ne : nonempty A) (l : list A),
    length (to_list ne) > 0.
Proof. intros A ne l; induction ne; simpl; apply gt_Sn_O. Qed.

Definition program := list sinstr.

Open Scope nonempty_scope.

Fixpoint s_eval (st : stack) (p : program) : option stack :=
  match p with
  | nil => Some st
  | cons x x0 =>
    match x with
    | SPush v => Some (v ::: to_list st)
    | SPlus =>
      match st with
      | ncons x tl =>
        match tl with
        | nil => None (* empty stack *)
        | cons y tl' => match plus x y with
        end
      end
    | SMinus => _
    | SMult => _
    | SIf x x0 x1 => _
    | STrue => _
    | SFalse => _
    | SAnd x x0 => _
    | SOr x x0 => _
    | SNot x => _
    | SWhile x => _
    end
  end.