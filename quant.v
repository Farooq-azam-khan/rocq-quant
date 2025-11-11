
Require Import String.
Require Import List.
Import  ListNotations. 
Parameter Scalar : Type.

Definition Var := string.

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
  | TVar : Var -> term
  | Sum : term -> term -> term
  | Scale : Scalar -> term -> term
  | OneIntro: Scalar -> term
  | OneElim: term -> term -> term
  | Lambda : Var -> term -> term
  | TApp : term -> term -> term
  | MultConjIntro : term -> term -> term
  | MultConjElim : term -> Var -> Var -> term  -> term 
  | TopIntro : term 
  | ZeroElim : term -> term 
  | AddConjIntro : term -> term -> term 
  | AddConjElim1 : term -> Var -> term -> term
  | AddConjElim2 : term -> Var -> term -> term
  | AddDisjIntro1 : term -> term 
  | AddDisjIntro2 : term -> term 
  | AddDisjElim : term -> Var -> term -> Var -> term -> term
.

Definition Context := list (Var * prop).

(* Figure 1: Typing Rules *)
Inductive typing : Context -> term -> prop -> Prop := 
  | TypAX : forall (x: Var) (A: prop), typing [(x, A)] (TVar x) A 
  | TypSum : forall (G: Context) (A: prop) (u: term) (v: term), 
      typing G u A -> typing G v A -> typing G (Sum u v) A
  | TypProd : forall (G: Context) (A: prop) (t: term) (a: Scalar), 
      typing G t A -> typing G (Scale a t) A
  | TypOneIntro : forall (a: Scalar), typing [] (OneIntro a) One 
  | TypeOneElim : forall (G: Context) (D: Context) (A: prop) (t: term) (u: term), 
      typing G t One -> typing D u A -> typing (G++D) (OneElim t u) A
  | TypeLambda : forall (G: Context) (A: prop) (x: Var) (t: term) (B: prop), 
      typing ((x, A) :: G) t B -> typing G (Lambda x t) (PApp A B)
  | TypeTApp : forall (G: Context) (t: term) (A: prop) (B: prop) (D: Context) (u: term),  
      typing G t (PApp A B) -> typing D u A -> typing (G++D) (TApp t u) B 
  | TypeMultConjIntro : forall (G: Context) (D: Context) (t: term) (u: term) (A: prop) (B: prop), 
      typing G t A -> typing D u B -> typing (G++D) (MultConjIntro t u) (MultConj A B) 
  | TypeMultConjElim : forall (G D: Context) (x y: Var) (t u: term) (A B C: prop), 
      typing G t (MultConj A B) -> typing ((x, A)::(y,B)::D) u C -> typing (G++D) (MultConjElim t x y u)  C
  | TypeTopIntro : forall (G: Context),  typing G TopIntro Top
  | TypeZeroElim : forall (G D: Context) (t: term) (C: prop), 
      typing G t Zero -> typing (G++D) (ZeroElim t) C
  | TypeAddConjIntro : forall (G: Context) (t u: term) (A B: prop),
      typing G t A -> typing G u B -> typing G (AddConjIntro t u) (AddConj A B)
  | TypeAddConjElim1 : forall (G D: Context) (x: Var) (t u: term) (A B C: prop), 
      typing G t (AddConj A B) -> typing ((x, A) :: D) u C -> typing (G++D) (AddConjElim1 t x u) C
  | TypeAddConjElim2 : forall (G D: Context) (x: Var) (t u: term) (A B C: prop), 
      typing G t (AddConj A B) -> typing ((x, B) :: D) u C -> typing (G++D) (AddConjElim2 t x u) C
  | TypeAddDisjIntro1 : forall (G:Context) (t: term) (A B: prop) , 
      typing G t A -> typing G (AddDisjIntro1 t) (AddDisj A B)
  | TypeAddDisjIntro2 : forall (G:Context) (t: term) (A B: prop) , 
      typing G t B -> typing G (AddDisjIntro2 t) (AddDisj A B)
  | TypeAddDisjElim : forall (G D: Context) (x y: Var) (t u v: term) (A B C: prop), 
      typing G t (AddDisj A B)  -> typing ((x, A)::D) u C -> typing ((y, B) :: D ) v C -> typing (G++D) (AddDisjElim t x u y v) C 
. 

(* Figure 2: Reduction Rules *)
Inductive step : term -> term -> Prop := 
  | R1 : forall (a: Scalar) (t: term), step (TApp (OneIntro a) t) (Scale a t) 
(*
  | R2 : forall 
  | R3 : forall 
  | R4 : forall 
  | R5 : forall 
  | R6 : forall 
  | R7 : forall 
  | R8 : forall 
  | R9 : forall 
  | R10 : forall 
  | R11 : forall 
  | R12 : forall 
  | R13 : forall 
  | R14 : forall 
  | R15 : forall 
  | R16 : forall 
  | R17 : forall 
  | R18 : forall 
  | R19 : forall 
*)
.
