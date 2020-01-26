{-# OPTIONS --exact-split --prop #-}
module CalculusOfCommunicatingSystems where

open import PropUniverses
open import Data.Bool
open import Data.Int using (ℤ)
open import Data.Nat hiding (_+_; l)

open import Basic

record Channel : 𝒰₀ ˙ where
  constructor chan
  field
    name : ℕ

open import Proposition.Decidable as Dec hiding (true; false)
open import Proof

instance
  DecidableChannel== : HasDecidableIdentity Channel
  DecidableChannel== {α₀} {α₁} =
    dif Channel.name α₀ == Channel.name α₁
      then (λ p → Dec.true (ap chan p))
      else λ ¬p → Dec.false λ { (Id.refl (chan α₀)) → ¬p (refl α₀) }

infix 140 _⁇_ _!_
data Action : 𝒰₀ ˙ where
  τ : Action
  _⁇_ _!_ : (α : Channel)(n : Value) → Action

open import Logic renaming (⟶ to —>)
open import Data.Collection
open import Data.Collection.Listable.Function

instance
  ActionCollection : Collection 𝒰₀ Action Channel
  _∈_ ⦃ ActionCollection ⦄ _ τ = ⊥
  _∈_ ⦃ ActionCollection ⦄ β (α ⁇ _) = β == α
  _∈_ ⦃ ActionCollection ⦄ β (α ! _) = β == α

data ProcessIdentifier : 𝒰₀ ˙ where
  Pid : (P : ℕ) → ProcessIdentifier

open import Data.List as L
  using (List; []; _∷_; x∈x∷_; x∈tail)
open import Type.Subset

infix 140 τ⟶_ _!_⟶_ _⁇_⟶_ _⟶_ _+_ _∥_ _\\_ _[_] _⟦_⟧
data Process : 𝒰₁ ˙ where
  nil : Process
  τ⟶_ : (p : Process) → Process
  _!_⟶_ : (α : Channel)(a : ArithExpr)(p : Process) → Process
  _⁇_⟶_ : (α : Channel)(x : Variable)(p : Process) → Process
  _⟶_ : (b : BoolExpr)(p : Process) → Process
  _+_ _∥_ : (p₀ p₁ : Process) → Process
  _\\_ : (p : Process)(L : DecSubset 𝒰₀ Channel) → Process
  _[_] : (p : Process)(f : Channel → Channel) → Process
  _⟦_⟧ : (P : ProcessIdentifier)(a : List ArithExpr) → Process

instance
  ProcessVars : WithVariables Process

open import Data.Functor
open import Data.Monad
open import Data.Maybe
open import Data.List.Functor
open import Function hiding (_$_)

open import Axiom.FunctionExtensionality

private
  p-sub : (σ : Substitution)(p : Process) → Process

p-sub σ nil = nil
p-sub σ (τ⟶ e) = τ⟶ p-sub σ e
p-sub σ (α ! a ⟶ e) = α ! sub σ a ⟶ p-sub σ e
p-sub σ (α ⁇ x ⟶ e) =
  α ⁇ x ⟶ p-sub (λ v → if v == x then just (avar v) else σ v) e
p-sub σ (b ⟶ e) = sub σ b ⟶ p-sub σ e
p-sub σ (p₀ + p₁) = p-sub σ p₀ + p-sub σ p₁
p-sub σ (p₀ ∥ p₁) = p-sub σ p₀ ∥ p-sub σ p₁
p-sub σ (p \\ L) = p-sub σ p \\ L
p-sub σ (p [ f ]) = p-sub σ p [ f ]
p-sub σ (P ⟦ a ⟧) = P ⟦ sub σ <$> a ⟧

fv ⦃ ProcessVars ⦄ nil = []
fv ⦃ ProcessVars ⦄ (τ⟶ p) = fv p
fv ⦃ ProcessVars ⦄ (α ! a ⟶ p) = fv a ++ fv p
fv ⦃ ProcessVars ⦄ (α ⁇ x ⟶ p) = remove x (fv p)
fv ⦃ ProcessVars ⦄ (b ⟶ p) = fv b ++ fv p
fv ⦃ ProcessVars ⦄ (p₀ + p₁) = fv p₀ ++ fv p₁
fv ⦃ ProcessVars ⦄ (p₀ ∥ p₁) = fv p₀ ++ fv p₁
fv ⦃ ProcessVars ⦄ (p \\ L) = fv p
fv ⦃ ProcessVars ⦄ (p [ f ]) = fv p
fv ⦃ ProcessVars ⦄ (P ⟦ a ⟧) = a >>= fv
sub ⦃ ProcessVars ⦄ = p-sub
sub-id ⦃ ProcessVars ⦄ nil = refl nil
sub-id ⦃ ProcessVars ⦄ (τ⟶ p) = ap τ⟶_ (sub-id p)
sub-id ⦃ ProcessVars ⦄ (α ! a ⟶ p) = ap2 (α !_⟶_) (sub-id a) (sub-id p)
sub-id ⦃ ProcessVars ⦄ (α ⁇ x ⟶ p) = ap (α ⁇ x ⟶_) (
  proof sub σ p
    === sub (just ∘ avar) p
      :by: ap (λ — → sub — p) $ fun-ext σ~just-avar
    === p   :by: sub-id p
  qed)
  where σ = λ v → if v == x then just (avar v) else just (avar v)
        σ~just-avar : σ ~ just ∘ avar
        σ~just-avar v = (λ x₁ → x₁ == just (avar v)) by-difₚ v == x
          then (λ _ → refl (just (avar v)))
          else (λ _ → refl (just (avar v)))
sub-id ⦃ ProcessVars ⦄ (b ⟶ p) = ap2 _⟶_ (sub-id b) (sub-id p)
sub-id ⦃ ProcessVars ⦄ (p₀ + p₁) = ap2 _+_ (sub-id p₀) (sub-id p₁)
sub-id ⦃ ProcessVars ⦄ (p₀ ∥ p₁) = ap2 _∥_ (sub-id p₀) (sub-id p₁)
sub-id ⦃ ProcessVars ⦄ (p \\ L) = ap (_\\ L) (sub-id p)
sub-id ⦃ ProcessVars ⦄ (p [ f ]) = ap (_[ f ]) (sub-id p)
sub-id ⦃ ProcessVars ⦄ (P ⟦ a ⟧) = ap (P ⟦_⟧) (
  proof sub (just ∘ avar) <$> a
    === id <$> a  :by: ap (_<$> a) $ fun-ext sub-id
    === a         :by: ==→~ fmap-id a
  qed)
-- sub-one ⦃ ProcessVars ⦄ (τ⟶ p) = sub-one p
-- sub-one ⦃ ProcessVars ⦄ (α ! a ⟶ p) v z q
--   with —> (++-prop {l = fv (sub _ a)}{l' = fv (sub _ p)}) q
-- sub-one ProcessVars (α ! a ⟶ p) v z q | ∨left q₁ = sub-one a v z q₁
-- sub-one ProcessVars (α ! a ⟶ p) v z q | ∨right q₁ = sub-one p v z q₁
-- sub-one ⦃ ProcessVars ⦄ (α ⁇ x ⟶ p) v z q with —> insert-valid q
-- sub-one ProcessVars (α ⁇ x ⟶ p) v z q | ∨left q₁ = sub-one p v z q₁
-- sub-one ProcessVars (α ⁇ x ⟶ p) v z q | ∨right q₁
--   with Dec.decide (v == x) ⦃ DecidableVar== ⦄
-- sub-one ProcessVars (α ⁇ x ⟶ p) .x z q | ∨right q₁ | Dec.true (Id.refl .x) = {!!}
-- sub-one ProcessVars (α ⁇ x ⟶ p) v z q | ∨right q₁ | Dec.false ¬p = {!!}
-- sub-one ⦃ ProcessVars ⦄ (b ⟶ p) v z q
--   with —> (++-prop {l = fv (sub _ b)}{l' = fv (sub _ p)}) q
-- sub-one ProcessVars (b ⟶ p) v z q | ∨left q₁ = sub-one b v z q₁
-- sub-one ProcessVars (b ⟶ p) v z q | ∨right q₁ = sub-one p v z q₁
-- sub-one ⦃ ProcessVars ⦄ (p₀ + p₁) v z q
--   with —> (++-prop {l = fv (sub _ p₀)}{l' = fv (sub _ p₁)}) q
-- sub-one ProcessVars (p₀ + p₁) v z q | ∨left q₁ = sub-one p₀ v z q₁
-- sub-one ProcessVars (p₀ + p₁) v z q | ∨right q₁ = sub-one p₁ v z q₁
-- sub-one ⦃ ProcessVars ⦄ (p₀ ∥ p₁) v z q
--   with —> (++-prop {l = fv (sub _ p₀)}{l' = fv (sub _ p₁)}) q
-- sub-one ProcessVars (p₀ ∥ p₁) v z q | ∨left q₁ = sub-one p₀ v z q₁
-- sub-one ProcessVars (p₀ ∥ p₁) v z q | ∨right q₁ = sub-one p₁ v z q₁
-- sub-one ⦃ ProcessVars ⦄ (p \\ L) = sub-one p
-- sub-one ⦃ ProcessVars ⦄ (p [ f ]) = sub-one p
-- sub-one ⦃ ProcessVars ⦄ (P ⟦ a ⟧) = {!!}

instance
  ProcessChannelListable : Listable 𝒰₀ Process Channel

ProcessChannelListable = pure-listable go
  where go : (p : Process) → List Channel
        go nil = []
        go (τ⟶ p) = go p
        go (α ! a ⟶ p) = α ∷ go p
        go (α ⁇ x ⟶ p) = α ∷ go p
        go (b ⟶ p) = go p
        go (p₀ + p₁) = go p₀ ++ go p₁
        go (p₀ ∥ p₁) = go p₀ ++ go p₁
        go (p \\ L) = L.filter (_∉ L)
          ⦃ ¬Decidable ⦃ DecSubset.dec L ⦄ ⦄ (go p)
        go (p [ f ]) = fmap f (go p)
        go (P ⟦ a ⟧) = []

instance
  _ = collection ⦃ ProcessChannelListable ⦄

open import Data.Vec as V using (Vec)

record ProcessDef : 𝒰₁ ˙ where
  constructor _,_,_≝_[_]
  field
    pid : ProcessIdentifier
    arity : ℕ
    args : Vec Variable arity
    proc : Process
    fv-p⊆args : fv proc ⊆ args

open ProcessDef public

infix 35 _—_⟶_
data _—_⟶_ : (p₀ : Process)(ƛ : Action)(p₁ : Process) → 𝒰₁ ᵖ where
  silent : ∀ {p}
    → --------------------
    τ⟶ p — τ ⟶ p

  output : ∀ {a n α p}
    (q₀ : closed a)
    (q₁ : aeval a q₀ == n)
    → ------------------------
    α ! a ⟶ p — α ! n ⟶ p

  input : ∀ {x n α p}
    → ------------------------
    α ⁇ x ⟶ p — α ⁇ n ⟶ p [[ n / x ]]

  boolean : ∀ {b p p' ƛ}
    (q₀ : closed b)
    (q₁ : beval b q₀ == true)
    (q₂ : p — ƛ ⟶ p' )
    → ------------------------
    b ⟶ p — ƛ ⟶ p'

  sum-left : ∀ {p₀ p₁ p₀' ƛ}
    (q : p₀ — ƛ ⟶ p₀' )
    → ------------------------
    p₀ + p₁ — ƛ ⟶ p₀'

  sum-right : ∀ {p₀ p₁ p₁' ƛ}
    (q : p₁ — ƛ ⟶ p₁' )
    → ------------------------
    p₀ + p₁ — ƛ ⟶ p₁'

  pc-left : ∀ {p₀ p₁ p₀' ƛ}
    (q : p₀ — ƛ ⟶ p₀' )
    → ------------------------
    p₀ ∥ p₁ — ƛ ⟶ p₀' ∥ p₁

  pc-right : ∀ {p₀ p₁ p₁' ƛ}
    (q : p₁ — ƛ ⟶ p₁' )
    → ------------------------
    p₀ ∥ p₁ — ƛ ⟶ p₀ ∥ p₁'

  pc-left-in : ∀ {p₀ p₀' p₁ p₁' α n}
    (q₀ : p₀ — α ⁇ n ⟶ p₀' )
    (q₁ : p₁ — α ! n ⟶ p₁' )
    → ------------------------
    p₀ ∥ p₁ — τ ⟶ p₀ ∥ p₁'

  pc-right-in : ∀ {p₀ p₀' p₁ p₁' α n}
    (q₀ : p₀ — α ! n ⟶ p₀' )
    (q₁ : p₁ — α ⁇ n ⟶ p₁' )
    → ------------------------
    p₀ ∥ p₁ — τ ⟶ p₀ ∥ p₁'

  restrict : ∀ {p p' L ƛ}
    (q₀ : ƛ ⊈ L)
    (q₁ : p — ƛ ⟶ p' )
    → ------------------------
    p \\ L — ƛ ⟶ p \\ L

  relabel : ∀ {p p' ƛ f}
    (q : p — ƛ ⟶ p' )
    → ------------------------
    let f' : Action → Action
        f' = λ { τ → τ ; (α ⁇ n) → f α ⁇ n ; (α ! n) → f α ! n}
    in
    p [ f ] — f' ƛ ⟶ p' [ f ]

  identifier : ∀ {P p' ƛ a}
    (q : proc P [ a / args P ] — ƛ ⟶ p' )
    → --------------------------------------------------
    pid P ⟦ to-list a ⟧ — ƛ ⟶ p'

open import Structure.Monoid
-- open import Data.Foldable

private
  MaxMonoid : Monoid ℕ
  MaxMonoid = record { e = 0; _∙_ = max }

fresh : (p : List Process) → Channel
fresh p = chan (mconcat ⦃ M = MaxMonoid ⦄ l +1)
  where l = Channel.name <$> mconcat (to-list <$> p)

open import Relation.Binary
open import Operation.Binary
open import Data.Nat.Proof

fresh-not-stale : (ps : List Process)
  → --------------------------------------
  (p : Process)(q : p ∈ ps) → fresh ps ∉ p
fresh-not-stale ps p q q' = contradiction
  where l : List ℕ
        l = Channel.name <$> mconcat (to-list <$> ps)
        c : Channel
        c = fresh ps
        q″ : c ∈ to-list p
        q″ = —> (to-list-valid {S = p}) q'
        c∈l : Channel.name c ∈ l
        c∈l = ∈fmap Channel.name $
          ⟵ (∈mconcat (to-list <$> ps) c) (to-list p , (∈fmap to-list q , q'))
        instance
          _ = MaxMonoid
        ≤max' : ∀ x y → y ≤ max x y
        ≤max' x y =
          proof y
            〉 _≤_ 〉 max y x  :by: ≤max y x
            〉 _==_ 〉 max x y :by: comm y x
          qed
        name-c≤concat : Channel.name c ≤ mconcat l
        name-c≤concat = mconcat-preserv ≤max ≤max' l (Channel.name c) c∈l
        contradiction : ⊥
        contradiction with go
          where go : ∃ λ x → x +1 ≤ x
                go = mconcat l , (
                  proof mconcat l +1
                    === Channel.name c :by: refl _
                    〉 _≤_ 〉 mconcat l   :by: name-c≤concat
                  qed)
        contradiction | x , ∨right q = irrefl (x +1) (-<s q)
        
_[_]∩_[_] : ∀ p out q in' → Process
p [ out ]∩ q [ in' ] = ((p [ f[ c / out ] ]) ∥ (q [ f[ c / in' ] ])) \\ dec-set (_== c)
  where c = fresh L.[ p ⸴ q ]
        f[_/_] : (new old : Channel) → Channel → Channel
        f[ new / old ] c = if c == old then new else c
