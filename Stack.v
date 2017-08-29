Set Warnings "-notation-overridden,-parsing".

Require Import Init.
Require Import ZArith.
Require Import String.
Require Import Lists.List.
Import ListNotations.

(* Require Import Metalib.Metatheory. *)


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
(* | TVar : nat -> type *)
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
  destruct t1, t2.
  decide equality.
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

(* Definition abs : exp_type -> list type -> exp_type := *)
(*   fun t S => match t with *)
(*   | TArrow x y => x ++ S ---> y ++ S *)
(*   end. *)

(* Top of the stack is on the left. *)
(* The last instruction is on the right *)
Inductive instr_comp : exp_type -> exp_type -> exp_type -> Prop :=
| ICNilL : forall A B C, instr_comp (A --->) (B ---> C) (A ++ B ---> C)
| ICNilR : forall A B C, instr_comp (A ---> B) (---> C) (A ---> C ++ B)
| ICComp : forall A B C D X Y i,
    instr_comp (A ---> B) (C ---> D) (X ---> Y) ->
    instr_comp (A ---> i :: B) (i :: C ---> D) (X ---> Y).

Hint Constructors instr_comp.


(* f : (A -> B) g : (B -> C) *)
(* ------------------------- T-COMPOSE *)
(* f g : (A -> C) *)

(* f : (A -> B) *)
(* ----------------------- T-QUOTE *)
(* [f] : (C -> C (A -> B)) *)


  (* | IENop *)
  (* | IEQuot : list instr -> instr *)
  (* | IENum : Z -> instr *)
  (* | IEBool : bool -> instr *)
  (* | IFEval *)
  (* | IPLteq *)
  (* | IPIf *)
  (* | IPPop *)
  (* | IPDup *)
  (* | IPSwap *)
  (* | IPDip *)
  (* | IBNot *)
  (* | IBAnd *)
  (* | IBOr *)
  (* | INPlus *)
  (* | INMinus *)
  (* | INMult *)

Inductive has_type : list instr -> exp_type -> Prop :=
| HtENop : forall A, has_type [IENop] (A ---> A)
| HtEQuot : forall A B e,
    has_type e (A ---> B) ->
    has_type [IEQuot e] (---> [A ===> B])
(*   ENum : -> int *)
| HtENum : forall n, has_type [IENum n] (---> [TNum])
(*   EBool : -> int *)
| HtEBool : forall b, has_type [IEBool b] (---> [TBool])
  (* eval : 'A ('A -> 'B) -> 'B *)
| HtFEval : forall A B, has_type [IFEval] ((A ===> B) :: A ---> B)
(*   lteq : int int -> bool *)
| HtPLteq : has_type [IPLteq] ([TNum; TNum] ---> [TBool])
(*   if : 'A bool ('A -> 'B) ('A -> 'B) -> 'B *)
| HtPIf : forall A B,
    has_type [IPIf] (TBool::(TQuot (A ---> B))::(TQuot (A ---> B))::A ---> B)
(*   pop : 'a -> *)
| HtPPop : forall A, has_type [IPPop] (A --->)
(*   dup : 'a -> 'a 'a *)
| HtPDup : forall a, has_type [IPDup] ([a] ---> a :: [a])
(*   swap : 'a 'b -> 'b 'a *)
| HtPSwap : forall a b, has_type [IPSwap] ([a;b] ---> [b;a])
(*   dip : 'A 'b '('A -> 'C) -> 'C 'b *)
| HtPDip : forall A b C,
    has_type [IPDip] (((A ===> C) :: b :: A) ---> b :: C)
(* not : bool -> bool *)
| HtBNot : has_type [IBNot] ([TBool] ---> [TBool])
(* and : bool bool -> bool *)
| HtBAnd : has_type [IBAnd] ([TBool; TBool] ---> [TBool])
(* or : bool bool -> bool *)
| HtBOr : has_type [IBOr] ([TBool; TBool] ---> [TBool])
(* plus : num num -> num *)
| HtNPlus : has_type [INPlus] ([TNum; TNum] ---> [TNum])
(* minus : num num -> num *)
| HtNMinus : has_type [INMinus] ([TNum; TNum] ---> [TNum])
(* mult : num num -> num *)
| HtNMult : has_type [INMult] ([TNum; TNum] ---> [TNum])
| HtSeq : forall A B C D X Y e1 E,
    has_type E (A ---> B) ->
    has_type [e1] (C ---> D) ->
    instr_comp (A ---> B) (C ---> D) (X ---> Y) ->
    has_type (e1 :: E) (X ---> Y).

Hint Constructors has_type.

Notation "'ID'" := IENop : cat_scope.
Notation "'EVAL'" := IFEval : cat_scope.
Notation "{ x , .. , y }" := (IEQuot (cons x .. (cons y nil) ..)) : cat_scope.
Notation " x 'num'" := (IENum x) (at level 91) : cat_scope.
Notation "'TRUE'" := (IEBool true) : cat_scope.
Notation "'FALSE'" := (IEBool false) : cat_scope.
Notation "'<='" := (IPLteq) : cat_scope.
Notation "'DUP'" := (IPDup) : cat_scope.
Notation "'POP'" := (IPPop) : cat_scope.
Notation "'SWAP'" := (IPSwap) : cat_scope.
Notation "'DIP'" := (IPDip) : cat_scope.
Notation "'IF?'" := (IPIf) : cat_scope.
Notation "~" := (IBNot) : cat_scope.
Notation "&&" := (IBAnd) : cat_scope.
Notation "||" := (IBOr) : cat_scope.
Notation "+" := (INPlus) : cat_scope.
Notation "-" := (INMinus) : cat_scope.
Notation "*" := (INMult) : cat_scope.

Open Scope cat_scope.

Ltac typecheck := repeat econstructor.

Theorem example : has_type [*; (3 num); (2 num)] (---> [TNum]).
Proof. typecheck. Qed.

Theorem example_quot : forall A, has_type [DUP] ([A] ---> [A; A] ).
Proof. typecheck. Qed.

Theorem example_eval : has_type [EVAL; {*, DUP} ]  ([TNum] ---> [TNum]).
Proof. typecheck. Qed.

Theorem example2 : has_type [+; *; DIP; { DUP }; (2 num); (3 num)] (---> [TNum]).
Proof. typecheck. Qed.

Theorem example_if : has_type [IF?; TRUE; { 3 num }; { 2 num }] (---> [TNum]).
Proof. typecheck. Qed.

Definition ctx : Set := list (atom * type).

Definition Monomorphic a := a = TNum \/ a = TBool.

Definition Polymorphic b := { a : atom & b = TVar a }.

Inductive All : forall (A : Type), (A -> A -> Prop) -> list A -> list A -> Type :=
| AllOne : forall A (x y :A) (P : A -> A -> Prop), P x y -> All P [x] [y]
| AllCons : forall A (x y : A) xs ys (P : A -> A -> Prop), All P xs ys -> All P (x :: xs) (y :: ys).

Inductive UnifiableVar : ctx -> type -> type -> Prop :=
| USame : forall c a, UnifiableVar c a a
| UConcreteVarL : forall c a b, Monomorphic a -> Polymorphic b -> UnifiableVar c a b
| UConcreteVarR : forall c a b, Polymorphic a -> Monomorphic b -> UnifiableVar c a b
| UVars : forall c a b, Polymorphic a -> Polymorphic b ->
.

| UArrow : forall a b a' b' c, All (Unifiable c) a a' -> All (Unifiable c) b b' ->
                          Unifiable c (a ---> b) (a' ---> b').

(* PROVE Г |- t : T -> sig . Гi |- sig . t : sig . T *)

Inductive TypeRule : list type -> Prop :=
| TrQuot : forall (a b c : list type) S new, TypeRule ((a ---> b) :: S) ->
                      new = (c ---> (c ++ [ a ---> b ])) ->
                      TypeRule (new :: S)
| TrCompose : forall a b1 b2 c S,
    Unifiable b1 b2 ->
    TypeRule ((a ---> b1) :: (b2 ---> c) :: S) ->
    TypeRule ((a ---> c) :: S).


Definition X : atom := fresh nil.
Definition Y : atom := fresh [X].
Definition Z : atom := fresh [X;Y].


Section CatTyping2.
  (* monomorphic type system *)

  Inductive type : Set :=
  | TNum
  | TBool
  | TQuote : itype -> type
  with itype : Set :=
  | TArrow : list type -> list type -> itype.

  Notation "X --> Y" := (TArrow X Y).
  Notation "X -->" := (TArrow X nil) (at level 70, right associativity).
  Notation "--> Y" := (TArrow nil Y) (at level 70, right associativity).
  Variables X Y Z : list type.
  Check (X --> Y).
  Check ((X -->) --> Y).

  Inductive icompose : itype -> itype -> itype :=
  | IRightNil : X --> nil ->

End CatTyping2.

Definition stack := list instr.

Open Scope Z_scope.

Print Datatypes.length.
Print well_founded.

Inductive EvalR : istack -> dstack -> Prop :=
  | PlusR : forall ist dst m n, EvalR (NAdd :: ist) (DNum n :: DNum m :: dst) ->
    forall mn, mn = m + n ->
    EvalR ist (DNum mn :: dst)
  | LteqTrueR : forall ist dst m n, m <= n ->
                           EvalR (PLteq :: ist) (DNum n :: DNum m :: dst) ->
                           EvalR ist (DBool true :: dst)
  | LteqFalseR : forall ist dst m n, m > n ->
                           EvalR (PLteq :: ist) (DNum n :: DNum m :: dst) ->
                           EvalR ist (DBool false :: dst)
  | PopR : forall ist dst x, EvalR (PPop :: ist) (x :: dst) ->
    EvalR ist dst
  | DupR : forall ist dst x, EvalR (PDup :: ist) (x :: dst) ->
    EvalR ist (x :: x :: dst)
  | SwapR : forall ist dst x y, EvalR (PSwap :: ist) (x :: y :: dst) ->
    EvalR ist (y :: x :: dst)
  | ConstR : forall ist dst x, EvalR (FConst :: ist) (x :: dst) ->
    EvalR ist (DQuot [EConst x] :: dst)
  | ComposeR : forall ist dst f g, EvalR (FCompose :: ist) (DQuot f :: DQuot g :: dst) ->
    forall fg, fg = f ++ g ->
    EvalR ist (DQuot fg :: dst)
  | EvalQuotR : forall ist dst f, EvalR (FEval :: ist) (DQuot f :: dst) ->
    forall ist', ist' = f ++ ist ->
    EvalR ist' dst
  | DipR : forall ist dst f x, EvalR (PDip :: ist) (DQuot f :: x :: dst) ->
    forall ist', ist' = f ++ ist ->
    EvalR ist' (x :: dst)
  | IfTrueR : forall ist dst l r, EvalR (PIf :: ist) (DBool true :: DQuot l :: DQuot r :: dst) ->
    forall ist', ist' = l ++ ist ->
    EvalR ist' dst
  | IfFalseR : forall ist dst l r, EvalR (PIf :: ist) (DBool false :: DQuot l :: DQuot r :: dst) ->
    forall ist', ist' = r ++ ist ->
    EvalR ist' dst
.

Hint Constructors EvalR.

Section ComputationExamples.
  Variable i : istack.
  Variable d : dstack.

  Example ex_plus :
     EvalR (NAdd :: i) (DNum 3 :: DNum 2 :: d) -> EvalR i (DNum 5 :: d).
  eauto. Qed.

  Example ex_lteq_true : forall (m n : Z), m <= n ->
                                 EvalR (PLteq :: i) (DNum n :: DNum m :: d) ->
                                 EvalR i (DBool true :: d).
  eauto. Qed.

  Example ex_lteq_false : forall (m n : Z), m > n ->
                                 EvalR (PLteq :: i) (DNum n :: DNum m :: d) ->
                                 EvalR i (DBool false :: d).
  eauto. Qed.

  Example ex_pop : forall (x : data), EvalR (PPop :: i) (x :: d) -> EvalR i d.
  eauto. Qed.

  Example ex_dup : forall (x : data), EvalR (PDup :: i) (x :: d) -> EvalR i (x :: x :: d).
  eauto. Qed.
End ComputationExamples.

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