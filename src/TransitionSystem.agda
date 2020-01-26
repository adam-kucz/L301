{-# OPTIONS --exact-split --prop --safe #-}
module TransitionSystem where

open import Universes
open import Type.Sum
open import Type.Subset

record TransitionSystem 𝒰 𝒱 𝒲 : (𝒰 ⊔ 𝒱 ⊔ 𝒲) ⁺ ˙ where
  field
    states : 𝒰 ˙
    init-state : states
    labels : 𝒱 ˙
    tran : subset 𝒲 (states × labels × states)
    
