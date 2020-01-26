{-# OPTIONS --exact-split --prop #-}
module Basic.Class where

open import PropUniverses
open import Proposition.Identity hiding (refl)
open import Proposition.Decidable
open import Data.Maybe
open import Data.List as L hiding (_++_)
open import Data.Vec hiding (_++_)
open import Data.Collection
open import Data.Collection.Listable.Function -- unsafe
open import Basic.Expression using (
  Variable; DecidableVar==; Value; val;
  ArithExpr; BoolExpr; ArithOp)
open ArithExpr 
open BoolExpr 
open import Logic hiding (¬_)

Substitution : 𝒰₀ ˙
Substitution = Variable ⇀ ArithExpr

_↦_ : (x : Variable)(a : ArithExpr) → Substitution
(x ↦ a) x' = if x == x' then just a else nothing

open import Function using (id; _∘_; _~_)

record WithVariables (E : 𝒰 ˙) : 𝒰 ˙ where
  field
    fv : (e : E) → List Variable
    sub : (σ : Substitution)(e : E) → E
    sub-id : sub (just ∘ avar) ~ id
    -- sub-one : ∀ e v z → v ∉ fv (sub (v ↦ aval z) e)

  closed : (e : E) → 𝒰₀ ᵖ
  closed e = fv e =∅

  -- be careful about simultaneous / sequential substitution effects
  infix 145 _[_/_] _[[_/_]]
  _[_/_] : ∀ {n}(e : E)(as : Vec ArithExpr n)(xs : Vec Variable n) → E
  e [ [] / [] ] = e
  e [ a ∷ as / x ∷ xs ] = sub (x ↦ a) e [ as / xs ]

  _[[_/_]] : (e : E)(n : Value)(x : Variable) → E
  e [[ n / x ]] = e [ [ aval (val n) ] / [ x ] ]

open WithVariables ⦃ … ⦄ public

open import Proof

private
  afv : (a : ArithExpr) → List Variable
  afv (avar v) = [ v ]
  afv (aval n) = []
  afv (op _ a₀ a₁) = afv a₀ ++ afv a₁

instance
  ArithExprVars : WithVariables ArithExpr

fv ⦃ ArithExprVars ⦄ = afv
sub ⦃ ArithExprVars ⦄ σ (avar v) = from-maybe' id (avar v) (σ v)
sub ⦃ ArithExprVars ⦄ σ (aval n) = aval n
sub ⦃ ArithExprVars ⦄ σ (op ∙ a₀ a₁) = op ∙ (sub σ a₀) (sub σ a₁)
sub-id ⦃ ArithExprVars ⦄ (avar v) = refl (avar v)
sub-id ⦃ ArithExprVars ⦄ (aval n) = refl (aval n)
sub-id ⦃ ArithExprVars ⦄ (op ∙ a₀ a₁) = Id.ap2 (op ∙) (sub-id a₀) (sub-id a₁)
-- sub-one ⦃ ArithExprVars ⦄ (op ∙ a₀ a₁) v z p
--   with ⟶ (++-prop {l = fv (sub _ a₀)}{fv (sub _ a₁)}) p
-- sub-one ArithExprVars (op ∙ a₀ a₁) v z p | ∨left q = sub-one a₀ v z q
-- sub-one ArithExprVars (op ∙ a₀ a₁) v z p | ∨right q = sub-one a₁ v z q
-- sub-one ⦃ ArithExprVars ⦄ (avar v₁) v _ p
--   with decide (v == v₁) ⦃ DecidableVar== ⦄
-- sub-one ArithExprVars (avar v₁) v _ p | true _ = (v ∉∅) p
-- sub-one ArithExprVars (avar v) v _ (x∈x∷ []) | false ¬p = ¬p (refl v)

private
  bfv : (b : BoolExpr) → List Variable
  bfv (bval b) = []
  bfv (¬ b) = bfv b
  bfv (bop _ b₀ b₁) = bfv b₀ ++ bfv b₁
  bfv (abop _ a₀ a₁) = afv a₀ ++ afv a₁

instance
  BoolExprVars : WithVariables BoolExpr

fv ⦃ BoolExprVars ⦄ = bfv
sub ⦃ BoolExprVars ⦄ σ (bval b) = bval b
sub ⦃ BoolExprVars ⦄ σ (¬ b) = ¬ sub σ b
sub ⦃ BoolExprVars ⦄ σ (bop ∙ b₀ b₁) = bop ∙ (sub σ b₀) (sub σ b₁)
sub ⦃ BoolExprVars ⦄ σ (abop ≈ a₀ a₁) = abop ≈ (sub σ a₀) (sub σ a₁)
sub-id ⦃ BoolExprVars ⦄ (bval v) = refl (bval v)
sub-id ⦃ BoolExprVars ⦄ (¬ b) = ap ¬_ $ sub-id b
sub-id ⦃ BoolExprVars ⦄ (bop ∙ b₀ b₁) = Id.ap2 (bop ∙) (sub-id b₀) (sub-id b₁)
sub-id ⦃ BoolExprVars ⦄ (abop ≈ a₀ a₁) = Id.ap2 (abop ≈) (sub-id a₀) (sub-id a₁)
-- sub-one ⦃ BoolExprVars ⦄ (¬ b) = sub-one b
-- sub-one ⦃ BoolExprVars ⦄ (abop ≈ a₀ a₁) = sub-one (op ArithOp.+ a₀ a₁)
-- sub-one ⦃ BoolExprVars ⦄ (bop ∙ b₀ b₁) v _ p
--   with ⟶ (++-prop {l = fv (sub _ b₀)}{fv (sub _ b₁)}) p
-- sub-one BoolExprVars (bop ∙ b₀ b₁) v z p | ∨left q = sub-one b₀ v z q
-- sub-one BoolExprVars (bop ∙ b₀ b₁) v z p | ∨right q = sub-one b₁ v z q
