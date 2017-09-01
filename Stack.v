Set Warnings "-notation-overridden,-parsing".

Require Import Init.
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
| ICLNilR : forall A B C, instr_comp (A --->  ) (B ---> C) (A ++ B ---> C)
| ICLNilL : forall A B,   instr_comp (  ---> A) (A ---> B) (---> B)
| ICRNilR : forall A B,   instr_comp (A ---> B) (B --->  ) (A --->)
| ICRNilL : forall A B C, instr_comp (A ---> B) (  ---> C) (A ---> C ++ B)
| ICComp : forall A B C,
    instr_comp (A ---> B) (B ---> C) (A ---> C).

Hint Constructors instr_comp.

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
    has_type [e1] (A ---> B) ->
    has_type E    (C ---> D) ->
    instr_comp (A ---> B) (C ---> D) (X ---> Y) ->
    has_type (e1 :: E) (X ---> Y).

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

Theorem example : has_type [.*; (3 num); (2 num)] (---> [TNum]).
Proof. typecheck. Qed.

Theorem example_quot : forall A, has_type [DUP] ([A] ---> [A; A] ).
Proof. typecheck. Qed.

Theorem example_eval : has_type [EVAL; {.*, DUP} ]  ([TNum] ---> [TNum]).
Proof.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  eapply ICLNilL.
  econstructor.
  typecheck. Qed.

Theorem example2 : has_type [.+; .*; DIP; { DUP }; (2 num); (3 num)] (---> [TNum]).
Proof. typecheck. Qed.

Theorem example_if : has_type [IF?; TRUE; { 3 num }; { 2 num }] (---> [TNum]).
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
  Print sig.

  (*
    That's too complicated.
    Fuck da functions, embrace relations!
    Failed attempt is left for didactics.

  Definition type_check : forall is : list instr, {t | has_type is t}.
    refine (fix F (is : list instr) : {t | has_type is t} :=
    match is return {t | has_type is t} with
    | [] => _ (* Impossible? *)
    | [IENop] => exist _ (TArrow [A] [A])
    | [IEQuot e] => let tq := F e
      in exist _ (TArrow [] [TQuot (proj1_sig tq)])
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
  *)

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
  | StNum   : forall n, stack_type [DNum n]  [TNum]
  | StBool  : forall b, stack_type [DBool b] [TBool]
  | StQuot  : forall is t,
      has_type is t ->
      stack_type [DQuot is] [TQuot t]
  | StCons  : forall d ds t ts,
      stack_type [d] t ->
      stack_type ds ts ->
      stack_type (d :: ds) (t ++ ts).

  Hint Constructors stack_type.
  Hint Constructors stacks_type.

  Lemma IENop_type: forall is t, has_type is t -> has_type (IENop :: is) t.
  Proof.
    intros.
    destruct t.
    eapply HtSeq.
    eauto.
    constructor.
    constructor.
  Qed.

  Lemma IENop_type_r: forall is t, has_type (IENop :: is) t -> has_type is t.
  Proof.
    intros.
  Admitted.

  Theorem preservation:
    forall is dst1 dst2 t,
    stacks_type dst1 dst2 t ->
    has_type is t ->
    EvalR is dst1 dst2.
  Proof.
    intros.
    induction is. (* Wrong induction hypothesis? *)
    - inversion H0.
    - destruct a.
      + constructor. apply IHis. apply IENop_type_r. assumption.
      + constructor. eapply IHis.
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