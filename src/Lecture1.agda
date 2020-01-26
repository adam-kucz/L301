{-# OPTIONS --safe --exact-split --prop #-}
module Lecture1 where

open import PropUniverses
open import Proposition.Identity
open import Proposition.Decidable using (Decidable; if_then_else_)
open import Data.Nat hiding (_+_)

private
  variable
    m : ℕ

data Location : 𝒰₀ ˙ where

instance
  DecidableLocation== : {l₀ l₁ : Location} → Decidable (l₀ == l₁)
  DecidableLocation== {()}

data Value : 𝒰₀ ˙ where
data ValExpr : 𝒰₀ ˙ where
data BoolExpr : 𝒰₀ ˙ where

data Bool : 𝒰₀ ˙ where
  true false : Bool

Σ : 𝒰₀ ˙
Σ = (l : Location) → Value

open import Type.Sum hiding (Σ)

beval : BoolExpr × Σ → Bool
beval (() , _)
veval : ValExpr × Σ → Value
veval (() , _)
  
record Config (Com : 𝒰 ˙) : 𝒰 ˙ where
  constructor 〈_,_〉
  field
    command : Com
    state : Σ

module While where
  data Command : 𝒰₀ ˙ where
    skip : Command
    _:=_ : (X : Location)(a : ValExpr) → Command
    if'_then_else_ : (b : BoolExpr)(c₁ c₂ : Command) → Command
    _∶_ : (c₀ c₁ : Command) → Command
    while_do'_ : (b : BoolExpr)(c : Command) → Command

  data _⟶_ : (conf₀ conf₁ : Config Command) → 𝒰₀ ᵖ where
    seq1 : ∀ {c₀ c₁ c₀' σ σ'}
      (p : 〈 c₀ , σ 〉 ⟶ 〈 c₀' , σ' 〉)
      → ------------------------------
      〈 c₀ ∶ c₁ , σ 〉 ⟶ 〈 c₀' ∶ c₁ , σ' 〉

    seq2 : ∀ {c₀ c₁ σ σ'}
      (p : 〈 c₀ , σ 〉 ⟶ 〈 skip , σ' 〉)
      → ------------------------------
      〈 c₀ ∶ c₁ , σ 〉 ⟶ 〈 c₁ , σ' 〉

    while : ∀ {b c c' σ σ'}
      (p : beval (b , σ) == true)
      (q : 〈 c , σ 〉 ⟶ 〈 c' , σ' 〉)
      → ------------------------------------------------
      〈 while b do' c , σ 〉 ⟶ 〈 c' ∶ (while b do' c) , σ' 〉

module While+ParallelComp where
  data Command : 𝒰₀ ˙ where
    skip : Command
    _:=_ : (X : Location)(a : ValExpr) → Command
    if'_then_else_ : (b : BoolExpr)(c₁ c₂ : Command) → Command
    _∶_ : (c₀ c₁ : Command) → Command
    _∥_ : (c₀ c₁ : Command) → Command
  
  data _⟶_ : (conf₀ conf₁ : Config Command) → 𝒰₀ ᵖ where
    par1 : ∀ {c₀ c₁ c₀' σ σ'}
      (p : 〈 c₀ , σ 〉 ⟶ 〈 c₀' , σ' 〉)
      → ------------------------------
      〈 c₀ ∥ c₁ , σ 〉 ⟶ 〈 c₀' ∥ c₁ , σ' 〉

    par2 : ∀ {c₀ c₁ c₁' σ σ'}
      (p : 〈 c₁ , σ 〉 ⟶ 〈 c₁' , σ' 〉)
      → ------------------------------
      〈 c₀ ∥ c₁ , σ 〉 ⟶ 〈 c₀ ∥ c₁' , σ' 〉

module GuardedCommandsLanguage where
  data GuardedCommand : 𝒰₀ ˙
  
  data Command : 𝒰₀ ˙ where
    skip abort : Command
    _:=_ : (X : Location)(a : ValExpr) → Command
    _∶_ : (c₀ c₁ : Command) → Command
    if_fi : (gc : GuardedCommand) → Command
    do'_od : (gc : GuardedCommand) → Command

  data GuardedCommand where
    guard : (b : BoolExpr)(c : Command) → GuardedCommand
    _[]_ : (gc₀ gc₁ : GuardedCommand) → GuardedCommand

  open import Type.BinarySum

  data _⟶fail : (conf : Config GuardedCommand) → 𝒰₀ ᵖ where
    guard-fail : ∀ {c b σ}
      (p : beval (b , σ) == false)
      → ------------------------------
      〈 guard b c , σ 〉 ⟶fail

    []-fail : ∀ {gc₀ gc₁ σ}
      (p : 〈 gc₀ , σ 〉 ⟶fail) (p : 〈 gc₁ , σ 〉 ⟶fail)
      → -----------------------------------------------
      〈 gc₀ [] gc₁ , σ 〉 ⟶fail

  data _⟶_ : (conf₀ conf₁ : Config (Command + GuardedCommand)) → 𝒰₀ ᵖ where
    gc-true : ∀ {c b σ}
      (p : beval (b , σ) == true)
      → ------------------------------
      〈 inr (guard b c) , σ 〉 ⟶ 〈 inl c , σ 〉

    gc1 : ∀ {gc₀ gc₁ c σ σ'}
      (p : 〈 inr gc₀ , σ 〉 ⟶ 〈 inl c , σ' 〉)
      → ------------------------------
      〈 inr (gc₀ [] gc₁) , σ 〉 ⟶ 〈 inl c , σ' 〉

    gc2 : ∀ {gc₀ gc₁ c σ σ'}
      (p : 〈 inr gc₁ , σ 〉 ⟶ 〈 inl c , σ' 〉)
      → ------------------------------
      〈 inr (gc₀ [] gc₁) , σ 〉 ⟶ 〈 inl c , σ' 〉

    if : ∀ {gc c σ σ'}
      (p : 〈 inr gc , σ 〉 ⟶ 〈 inl c , σ' 〉)
      → ------------------------------
      〈 inl (if gc fi) , σ 〉 ⟶ 〈 inl c , σ' 〉

    loop-end : ∀ {gc σ}
      (p : 〈 gc , σ 〉 ⟶fail)
      → ------------------------------
      〈 inl (do' gc od) , σ 〉 ⟶ 〈 inl skip , σ 〉

    loop-step : ∀ {gc c σ σ'}
      (p : 〈 inr gc , σ 〉 ⟶ 〈 inl c , σ' 〉)
      → ------------------------------
      〈 inl (do' gc od) , σ 〉 ⟶ 〈 inl (c ∶ do' gc od) , σ' 〉

module GCL+sync where
  data  Channel : 𝒰₀ ˙ where
  
  data Command : 𝒰₀ ˙ where
    skip abort : Command
    _!_ : (α : Channel)(a : ValExpr) → Command
    _⁇_ : (α : Channel)(X : Location) → Command
    _\\_ : (c : Command)(α : Channel) → Command
    _:=_ : (X : Location)(a : ValExpr) → Command
    _∶_ : (c₀ c₁ : Command) → Command
    _∥_ : (c₀ c₁ : Command) → Command
  
  data Label : 𝒰₀ ˙ where
    τ : Label
    _⁇_ _!_ : (α : Channel)(n : Value) → Label

  _[_/_] : (σ : Σ)(n : Value)(X : Location) → Σ
  (σ [ n / X ]) l = if l == X then n else σ l

  open import Logic hiding (_,_)
  open import Data.Collection

  instance
    LabelCollection : Collection 𝒰₀ Label Channel
    _∈_ ⦃ LabelCollection ⦄ α τ = ⊥
    _∈_ ⦃ LabelCollection ⦄ α (β ⁇ _) = α == β
    _∈_ ⦃ LabelCollection ⦄ α (β ! _) = α == β

  data _—_⟶_ :
      (conf₀ : Config Command)
      (ƛ : Label)
      (conf₁ : Config Command)
      → --------------------------------------------------
      𝒰₀ ᵖ
      where
    receive : ∀ {α X σ n}
      → ---------------------------------------------------------
      〈 α ⁇ X , σ 〉 — α ⁇ n ⟶ 〈 skip , σ [ n / X ] 〉

    send : ∀ {α σ a n}
      (p : veval (a , σ) == n )
      → ---------------------------------------------------------
      〈 α ! a , σ 〉 — α ! n ⟶ 〈 skip , σ 〉

    par1 : ∀ {c₀ c₁ c₀' σ σ' ƛ}
      (p : 〈 c₀ , σ 〉 — ƛ ⟶ 〈 c₀' , σ' 〉)
      → ------------------------------
      〈 c₀ ∥ c₁ , σ 〉 — ƛ ⟶ 〈 c₀' ∥ c₁ , σ' 〉

    par2 : ∀ {c₀ c₁ c₁' σ σ' ƛ }
      (p : 〈 c₁ , σ 〉 — ƛ ⟶ 〈 c₁' , σ' 〉)
      → ------------------------------
      〈 c₀ ∥ c₁ , σ 〉 — ƛ ⟶ 〈 c₀ ∥ c₁' , σ' 〉

    sync1 : ∀ {c₀ c₁ c₀' c₁' σ σ' α n }
      (p : 〈 c₀ , σ 〉 — α ⁇ n ⟶ 〈 c₀' , σ' 〉)
      (q : 〈 c₁ , σ 〉 — α ! n ⟶ 〈 c₁' , σ 〉)
      → -------------------------------------------------------------------------
      〈 c₀ ∥ c₁ , σ 〉 — τ ⟶ 〈 c₀' ∥ c₁' , σ' 〉

    sync2 : ∀ {c₀ c₁ c₀' c₁' σ σ' α n }
      (p : 〈 c₀ , σ 〉 — α ! n ⟶ 〈 c₀' , σ 〉)
      (q : 〈 c₁ , σ 〉 — α ⁇ n ⟶ 〈 c₁' , σ' 〉)
      → -------------------------------------------------------------------------
      〈 c₀ ∥ c₁ , σ 〉 — τ ⟶ 〈 c₀' ∥ c₁' , σ' 〉

    restrict : ∀ {c c' σ σ' ƛ} {α : Channel}
      (p : 〈 c , σ 〉 — ƛ ⟶ 〈 c' , σ' 〉)
      (q : α ∉ ƛ)
      → -------------------------------------------------------------------------
      〈 c , σ 〉 — ƛ ⟶ 〈 c' , σ' 〉
