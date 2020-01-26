{-# OPTIONS --exact-split --prop #-}
module PureCCS.Translation where

import PureCCS.Definition as Pure
import CalculusOfCommunicatingSystems as CCS

open import Universes
open import Type.Sum hiding (_,_)
open import Proposition.Decidable using (if_then_else_)
open import Proposition.Identity
open import Data.Nat
open import Data.Int
open import Data.Bool
open import Data.Collection
open import Data.Collection.Listable.Function
open import Data.List
open import Logic
open import Basic

hat :
  (p : CCS.Process)
  (q : closed p)
  → ----------------------------------
  Pure.Process 𝒰₀ (CCS.Channel × Value) (CCS.ProcessIdentifier × List ℕ)
hat CCS.nil q = Pure.nil
hat (CCS.τ⟶ p) q = Pure.τ Pure.,, hat p q
hat (α CCS.! a ⟶ p) q =
  Pure.compl (α Σ., mk-val (aeval a
    λ { (x , p') → q (x , ⟵ (++-prop {l' = fv p}) (∨left p'))}))
  Pure.,,
  hat p λ { (x , p') → q (x , ⟵ ++-prop (∨right p'))}
hat (α CCS.⁇ x ⟶ p) q =
  Pure.∑ ℤ , λ m →
    Pure.name (α Σ., mk-val m) Pure.,,
    hat (p [[ mk-val m / x ]]) λ { (elem , p) → {!!}}
hat (b CCS.⟶ p) q =  if (b' == true)
    then (hat p λ { (x , p') → q (x , ⟵ ++-prop (∨right p'))})
    else Pure.nil
  where b' = beval b λ { (x , p') → q (x , ⟵ (++-prop {l' = fv p}) (∨left p'))}
hat (p₀ CCS.+ p₁) q = Pure.∑ Bool , λ { true → p₀' ; false → p₁'}
  where p₀' = hat p₀ λ { (x , p') → q (x , ⟵ (++-prop {l' = fv p₁}) (∨left p'))}
        p₁' = hat p₁ λ { (x , p') → q (x , ⟵ (++-prop {l = fv p₀}) (∨right p'))}
hat (p₀ CCS.∥ p₁) q = p₀' Pure.∥ p₁'
  where p₀' = hat p₀ λ { (x , p') → q (x , ⟵ (++-prop {l' = fv p₁}) (∨left p'))}
        p₁' = hat p₁ λ { (x , p') → q (x , ⟵ (++-prop {l = fv p₀}) (∨right p'))}
hat (p CCS.\\ L) q = hat p q Pure.\\ {!!}
hat (p CCS.[ f ]) q = {!!}
hat (P CCS.⟦ a ⟧) q = Pure.Pid (P Σ., {!!})
  where all-a-closed :
          (x : ArithExpr)
          (p : x ∈ a)
          → --------------------
          closed x
        all-a-closed x p (v , q') = {!!}
