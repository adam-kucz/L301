{-# OPTIONS --exact-split --prop #-}
module Basic.Evaluation where

import Basic.Expression as Expr
open Expr using (ArithExpr; BoolExpr; Value; Variable; ArithOp; BoolOp; ArithmBoolOp)
open ArithExpr
open BoolExpr
module Aop = ArithOp
module Bop = BoolOp
module ABop = ArithmBoolOp
open import Basic.Class

open import PropUniverses
open import Proposition.Empty
open import Proposition.Identity
open import Proposition.Decidable
open import Data.Int
open import Data.Bool
open import Data.List hiding (_++_)
open import Data.Collection
open import Data.Collection.Listable.Function
open import Logic hiding (⊥-recursion)

aeval-in-ctx : (σ : Variable → ℤ)(a : ArithExpr) → ℤ
aeval-in-ctx σ (avar v) = σ v
aeval-in-ctx σ (aval n) = n
aeval-in-ctx σ (op Aop.+ a₀ a₁) = aeval-in-ctx σ a₀ + aeval-in-ctx σ a₁
aeval-in-ctx σ (op Aop.- a₀ a₁) = aeval-in-ctx σ a₀ - aeval-in-ctx σ a₁
aeval-in-ctx σ (op Aop.* a₀ a₁) = aeval-in-ctx σ a₀ * aeval-in-ctx σ a₁

aeval : (a : ArithExpr)(p : fv a =∅) → ℤ

private
  combine-with :
    (op : (x y : ℤ) → ℤ)
    (a₀ a₁ : ArithExpr)
    (p : fv a₀ ++ fv a₁ =∅)
    → -----------------------
    ℤ
  combine-with _∙_ a₀ a₁ p =
    aeval a₀
      (λ { (v , q) → p (v , ⟵ (++-prop {l' = fv a₁}) (∨left q))})
    ∙
    aeval a₁
      (λ { (v , q) → p (v , ⟵ (++-prop {l = fv a₀}) (∨right q))})

aeval (avar v) p = ⊥-recursion ℤ (p (v , x∈x∷ []))
aeval (aval n) p = n
aeval (op Aop.+ a₀ a₁) p = combine-with _+_ a₀ a₁ p
aeval (op Aop.- a₀ a₁) p = combine-with _-_ a₀ a₁ p
aeval (op Aop.* a₀ a₁) p = combine-with _*_ a₀ a₁ p

beval-in-ctx : (σ : Variable → ℤ)(b : BoolExpr) → Bool
beval-in-ctx σ (bval b) = b
beval-in-ctx σ (¬ b) = not (beval-in-ctx σ b)
beval-in-ctx σ (bop Bop.∧ b₀ b₁) = beval-in-ctx σ b₀ and beval-in-ctx σ b₁
beval-in-ctx σ (bop Bop.∨ b₀ b₁) = beval-in-ctx σ b₀ or beval-in-ctx σ b₁
beval-in-ctx σ (abop ABop.== a₀ a₁) = to-bool (aeval-in-ctx σ a₀ == aeval-in-ctx σ a₁)
beval-in-ctx σ (abop ABop.< a₀ a₁) = to-bool (aeval-in-ctx σ a₀ < aeval-in-ctx σ a₁)

beval : (b : BoolExpr)(p : fv b =∅) → Bool

private
  b-combine-with-a :
    (op : (x y : ℤ) → 𝒰 ᵖ)
    ⦃ _ : ∀ {x y} → Decidable (op x y) ⦄
    (a₀ a₁ : ArithExpr)
    (p : fv a₀ ++ fv a₁ =∅)
    → -----------------------
    Bool
  b-combine-with-a _∙_ a₀ a₁ p = to-bool (
    aeval a₀
      (λ { (v , q) → p (v , ⟵ (++-prop {l' = fv a₁}) (∨left q))})
    ∙
    aeval a₁
      (λ { (v , q) → p (v , ⟵ (++-prop {l = fv a₀}) (∨right q))})
    )

  b-combine-with-b :
    (op : (b₀ b₁ : Bool) → Bool)
    (b₀ b₁ : BoolExpr)
    (p : fv b₀ ++ fv b₁ =∅)
    → -----------------------
    Bool
  b-combine-with-b _∙_ b₀ b₁ p =
    beval b₀
      (λ { (v , q) → p (v , ⟵ (++-prop {l' = fv b₁}) (∨left q))})
    ∙
    beval b₁
      (λ { (v , q) → p (v , ⟵ (++-prop {l = fv b₀}) (∨right q))})

beval (bval b) p = b
beval (¬ b) p = not (beval b p)
beval (bop Bop.∧ b₀ b₁) p = b-combine-with-b _and_ b₀ b₁ p
beval (bop Bop.∨ b₀ b₁) p = b-combine-with-b _or_ b₀ b₁ p
beval (abop ABop.== a₀ a₁) p = b-combine-with-a _==_ a₀ a₁ p
beval (abop ABop.< a₀ a₁) p = b-combine-with-a _<_ a₀ a₁ p
