{-# OPTIONS --exact-split --prop #-}
module PureCCS.Definition where

open import PropUniverses
open import Data.Nat hiding (_⊔_)

data Action (X : 𝒰 ˙) : 𝒰 ˙ where
  τ : Action X
  name : (x : X) → Action X
  compl : (x : X) → Action X

bar : (a : Action X) → Action X
bar τ = τ
bar (name x) = compl x
bar (compl x) = name x

open import Type.Subset.Decidable
open import Data.List hiding ([_])

infix 140 _,,_ ∑_,_ _∥_ _\\_ _[_]
data Process 𝒰 𝒯 (X : 𝒱 ˙) (ProcId : 𝒲 ˙) : 𝒰 ⊔ 𝒱 ⁺ ⊔ 𝒲 ⊔ 𝒯 ⁺ ˙ where
  nil : Process 𝒰 𝒯 X ProcId
  _,,_ : (ƛ : Action X)(p : Process 𝒰 𝒯 X ProcId) → Process 𝒰 𝒯 X ProcId
  ∑_,_ : (I : 𝒱 ˙)(p : (i : I) → Process 𝒰 𝒯 X ProcId) → Process 𝒰 𝒯 X ProcId
  _∥_ : (p₀ p₁ : Process 𝒰 𝒯 X ProcId) → Process 𝒰 𝒯 X ProcId
  _\\_ : (p : Process 𝒰 𝒯 X ProcId)(L : DecSubset 𝒯 (Action X)) → Process 𝒰 𝒯 X ProcId
  _[_] : (p : Process 𝒰 𝒯 X ProcId)(f : Action X → Action X) → Process 𝒰 𝒯 X ProcId
  Pid : (P : ProcId) → Process 𝒰 𝒯 X ProcId

record ProcessDef 𝒰 𝒯 (X : 𝒱 ˙)(ProcId : 𝒲 ˙) : 𝒰 ⊔ 𝒱 ⁺ ⊔ 𝒲 ⊔ 𝒯 ⁺ ˙ where
  constructor _≝_
  field
    pid : ProcId
    proc : Process 𝒰 𝒯 X ProcId

open ProcessDef public

open import Proposition.Identity
open import Data.Collection
open import Data.Functor
open import Data.List.Functor

variable
  p p₀ p₁ p' p₀' p₁' : Process 𝒰 𝒯 X Y
  ƛ : Action X

infix 35 _—_⟶_
data _—_⟶_ {𝒰 𝒯}{X : 𝒱 ˙}{ProcId : 𝒲 ˙} :
      (p₀ : Process 𝒰 𝒯 X ProcId)
      (ƛ : Action X)
      (p₁ : Process 𝒰 𝒯 X ProcId)
      → --------------------
      𝒰 ⊔ 𝒱 ⁺ ⊔ 𝒲 ⊔ 𝒯 ⁺ ᵖ
      where
  guard : ƛ ,, p — ƛ ⟶ p

  sum : ∀ {I}{p : (j : I) → Process 𝒰 𝒯 X ProcId}
    (q : ∀ (j : I) → p j — ƛ ⟶ p' )
    → ------------------------
    ∑ I , p — ƛ ⟶ p'

  pc-left : 
    (q : p₀ — ƛ ⟶ p₀' )
    → ------------------------
    p₀ ∥ p₁ — ƛ ⟶ p₀' ∥ p₁

  pc-right :
    (q : p₁ — ƛ ⟶ p₁' )
    → ------------------------
    p₀ ∥ p₁ — ƛ ⟶ p₀ ∥ p₁'

  pc-sync : {a : Action X}
    (q₀ : p₀ — a ⟶ p₀' )
    (q₁ : p₁ — bar a ⟶ p₁' )
    → ------------------------
    p₀ ∥ p₁ — τ ⟶ p₀ ∥ p₁'

  restrict : ∀ {L}
    (q₀ : ƛ ∉ L ∪ (fmap bar L))
    (q₁ : p — ƛ ⟶ p' )
    → ------------------------
    p \\ L — ƛ ⟶ p \\ L

  relabel : ∀ {f}
    (q : ∀ a → f (bar a) == bar (f a))
    (q' : p — ƛ ⟶ p' )
    → ------------------------
    p [ f ] — f ƛ ⟶ p' [ f ]

  identifier : ∀ {P}
    (q : proc P — ƛ ⟶ p' )
    → --------------------------------------------------
    Pid (pid P) — ƛ ⟶ p'

