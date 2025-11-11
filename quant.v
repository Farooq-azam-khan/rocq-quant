
Require Import String.
Require Import List.
Import  ListNotations. 
Parameter Scalar : Type.

Definition var := string.

(* proposition *)
Inductive prop: Type  :=
  | One :prop
  | PApp : prop -> prop -> prop 
  | MultConj : prop -> prop -> prop
  | Top : prop
  | Zero : prop
  | AddConj : prop -> prop -> prop
  | AddDisj : prop -> prop -> prop
.


Compute (One ).
Check (PApp One ).
Compute (MultConj One Top).
Compute (AddDisj Zero Top).

Fixpoint count_constructors (c : prop) : nat := 
  match c with 
    One => 1 
  | PApp p1 p2 => 1  + count_constructors p1 + count_constructors p2
  | MultConj p1 p2 => 1 + count_constructors p1 + count_constructors p2 
  | Top => 1 
  | Zero => 1 
  | AddConj p1 p2 => 1 + count_constructors p1 + count_constructors p2
  | AddDisj p1 p2 => 1 + count_constructors p1 + count_constructors p2
  end. 

Compute count_constructors (MultConj One Top).
Compute count_constructors (MultConj (AddConj Top Zero) Top).

(* proof terms *)

Inductive term: Type := 
  | TVar : var -> term 
  | Sum : term -> term -> term 
  | Scale : Scalar -> term -> term 
  | OneIntro: Scalar -> term 
  | OneElim: term -> term -> term 
  | Lambda : var -> term -> term 
  | TApp : term -> term -> term 
  | MultConjIntro : term -> term -> term 
  | MultConjElim : term -> var -> var -> term  -> term 
  | TopIntro : term 
  | ZeroElim : term -> term 
  | AddConjIntro : term -> term -> term 
  | AddConjElim1 : term -> var -> term -> term
  | AddConjElim2 : term -> var -> term -> term
  | AddDisjIntro1 : term -> term 
  | AddDisjIntro2 : term -> term 
  | AddDisjElim : term -> var -> term -> var -> term -> term
.

Definition Context := list (var * prop).

(* Figure 1 *)
Inductive typing : Context -> term -> prop -> Prop := 
  | TypAX : forall (x: var) (A: prop), typing [(x, A)] (TVar x) A 
  | TypSum : forall (G: Context) (A: prop) (u: term) (v: term), 
      typing G u A -> typing G v A -> typing G (Sum u v) A
  | TypProd : forall (G: Context) (A: prop) (t: term) (a: Scalar), 
      typing G t A -> typing G (Scale a t) A
  | TypOneIntro : forall (a: Scalar), typing [] (OneIntro a) One 
  | TypeOneElim : forall (G: Context) (D: Context) (A: prop) (t: term) (u: term), 
      typing G t One -> typing D u A -> typing (G++D) (OneElim t u) A
  | TypeLambda : forall (G: Context) (A: prop) (x: var) (t: term) (B: prop), 
      typing ((x, A) :: G) t B -> typing G (Lambda x t) (PApp A B)
  | TypeTApp : forall (G: Context) (t: term) (A: prop) (B: prop) (D: Context) (u: term),  
      typing G t (PApp A B) -> typing D u A -> typing (G++D) (TApp t u) B 
  | TypeMultConjIntro : forall (G: Context) (D: Context) (t: term) (u: term) (A: prop) (B: prop), 
      typing G t A -> typing D u B -> typing (G++D) (MultConjIntro t u) (MultConj A B) 
  | TypeMultConjElim : forall (G D: Context) (x y: var) (t u: term) (A B C: prop), 
      typing G t (MultConj A B) -> typing ((x, A)::(y,B)::D) u C -> typing (G++D) (MultConjElim t x y u)  C
  | TypeTopIntro : forall (G: Context),  typing G TopIntro Top
  | TypeZeroElim : forall (G D: Context) (t: term) (C: prop), 
      typing G t Zero -> typing (G++D) (ZeroElim t) C
  | TypeAddConjIntro : forall (G: Context) (t u: term) (A B: prop),
      typing G t A -> typing G u B -> typing G (AddConjIntro t u) (AddConj A B)
  | TypeAddConjElim1 : forall (G D: Context) (x: var) (t u: term) (A B C: prop), 
      typing G t (AddConj A B) -> typing ((x, A) :: D) u C -> typing (G++D) (AddConjElim1 t x u) C
  | TypeAddConjElim2 : forall (G D: Context) (x: var) (t u: term) (A B C: prop), 
      typing G t (AddConj A B) -> typing ((x, B) :: D) u C -> typing (G++D) (AddConjElim2 t x u) C
  | TypeAddDisjIntro1 : forall (G:Context) (t: term) (A B: prop) , 
      typing G t A -> typing G (AddDisjIntro1 t) (AddDisj A B)
  | TypeAddDisjIntro2 : forall (G:Context) (t: term) (A B: prop) , 
      typing G t B -> typing G (AddDisjIntro2 t) (AddDisj A B)
  | TypeAddDisjElim : forall (G D: Context) (x y: var) (t u v: term) (A B C: prop),      typing G t (AddDisj A B)  -> typing ((x, A)::D) u C -> typing ((y, B) :: D ) v C -> typing (G++D) (AddDisjElim t x u y v) C 
. 

(* t[u / x] *)
Fixpoint subs (t : term) (x : var) (u : term) : term :=
  match t with
  (* x [u / x] -> u *)
  (* y [u / x] -> y *)
  | TVar y => if eqb x y then u else TVar y
  (* (t_one + t_two)[u / x] -> (t_one[u / x] + t_two[u / x]*)
  | Sum t_one t_two => Sum (subs t_one x u) (subs t_two x u)
  (* Scale : Scalar -> term -> term *)
  | Scale s t_one => Scale s (subs t_one x u)
  (* OneIntro: Scalar -> term *)
  | OneIntro s => OneIntro s
  (* OneElim: term -> term -> term *)
  | OneElim t_one t_two => OneElim (subs t_one x u) (subs t_two x u)
  (* Lambda : var -> term -> term *)
  | Lambda y t_one => if eqb x y then t_one else Lambda y (subs t_one x u)
  (* TApp : term -> term -> term *)
  | TApp t_one t_two => TApp (subs t_one x u) (subs t_two x u)
  (*  MultConjIntro : term -> term -> term *)
  | MultConjIntro t_one t_two => MultConjIntro (subs t_one x u) (subs t_two x u)
  (* MultConjElim : term -> var -> var -> term  -> term  *)
  (* TopIntro : term  *)
  | TopIntro => TopIntro
  (* ZeroElim : term -> term  *)
  | ZeroElim t_one => ZeroElim (subs t_one x u)
  (* AddConjIntro : term -> term -> term  *)
  | AddConjIntro t_one t_two => AddConjIntro (subs t_one x u) (subs t_two x u)
  (* AddConjElim1 : term -> var -> term -> term *)
  (* AddConjElim2 : term -> var -> term -> term *)
  (* AddDisjIntro1 : term -> term  *)
  | AddDisjIntro1 t_one => AddDisjIntro1 (subs t_one x u)
  (* AddDisjIntro2 : term -> term  *)
  | AddDisjIntro2 t_one => AddDisjIntro2 (subs t_one x u)
  (* AddDisjElim : term -> var -> term -> var -> term -> term *)
  | _  => u
  end.

Open Scope string_scope.
Compute (subs (TVar "x") "x" (TVar "y")).
Compute (subs (TApp (TVar "y") (TVar "x")) "x" (TVar "y")).
Close Scope string_scope.
