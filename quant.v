Parameter Scalar : Type.  

Require Import String. 
Definition Var := string. 

(* proposition *)
Inductive prop: Type  := 
  | One :prop
  | PApp : prop -> prop -> prop 
  | MultConj : prop -> prop -> prop 
  | Top : prop
  | Zero : prop
  | AddConj : prop -> prop -> prop 
  |  AddDisj : prop -> prop -> prop 
.

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

