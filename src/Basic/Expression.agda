{-# OPTIONS --safe --exact-split --prop #-}
module Basic.Expression where

open import Universes
open import Data.Nat using (ℕ)
open import Data.Int using (ℤ)
open import Data.Bool

record Variable : 𝒰₀ ˙ where
  constructor mk-var
  field
    var : ℕ

open Variable public

record Value : 𝒰₀ ˙ where
  constructor mk-val
  field
    val : ℤ

open Value public

open import Proposition.Decidable
open import Proposition.Identity renaming (_==_ to _===_)

instance
  DecidableVar== : HasDecidableIdentity Variable
  DecidableVar== {v₀} {v₁} = 
    dif var v₀ === var v₁
      then (λ p → true (ap mk-var p))
      else λ ¬p → false λ { (refl v) → ¬p (refl (var v)) }

data BoolExpr : 𝒰₀ ˙

data ArithOp : 𝒰₀ ˙ where
  + - * : ArithOp

data ArithExpr : 𝒰₀ ˙ where
  avar : (v : Variable) → ArithExpr
  aval : (n : ℤ) → ArithExpr
  op : (op : ArithOp)(a₀ a₁ : ArithExpr) → ArithExpr

data BoolOp : 𝒰₀ ˙ where
  ∧ ∨ : BoolOp

data ArithmBoolOp : 𝒰₀ ˙ where
  == < : ArithmBoolOp

data BoolExpr where
  bval : (b : Bool) → BoolExpr
  ¬_ : (b : BoolExpr) → BoolExpr
  bop : (op : BoolOp)(b₀ b₁ : BoolExpr) → BoolExpr
  abop : (op : ArithmBoolOp)(a₀ a₁ : ArithExpr) → BoolExpr

