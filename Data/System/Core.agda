{-# OPTIONS --without-K --safe #-}

open import Level using (Level; 0ℓ; suc; _⊔_)

module Data.System.Core {c ℓ : Level} where

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Algebra using (CommutativeMonoid)
open import Data.Setoid using (_⇒ₛ_; ∣_∣)
open import Data.Setoid.Unit using (⊤ₛ)
open import Function using (Func; _⟨$⟩_)
open import Function.Construct.Constant using () renaming (function to Const)
open import Function.Construct.Identity using () renaming (function to Id)
open import Function.Construct.Setoid using (_∙_)
open import Relation.Binary using (Setoid; Reflexive; Transitive)

open Func

-- A dynamical system with a set of states,
-- a state update function,
-- and a readout function

-- Really, the input type should be a cocommutative comonoid,
-- but every setoid is a cocommutative comonoid in a unique way
record System (I : Setoid c ℓ) (O : CommutativeMonoid c ℓ) : Set (c ⊔ suc ℓ) where

  private
    module I = Setoid I
    module O = CommutativeMonoid O

  field
    S : Setoid ℓ ℓ
    fₛ : ∣ I ⇒ₛ S ⇒ₛ S ∣
    fₒ : ∣ S ⇒ₛ O.setoid ∣

  fₛ′ : I.Carrier → ∣ S ∣ → ∣ S ∣
  fₛ′ i = to (to fₛ i)

  fₒ′ : ∣ S ∣ → O.Carrier
  fₒ′ = to fₒ

  module S = Setoid S

open System

module _ where

  open CommutativeMonoid

  -- the discrete system ignores input and outputs default value
  discrete : (I : Setoid c ℓ) (O : CommutativeMonoid c ℓ) → System I O
  discrete _ _ .S = ⊤ₛ
  discrete I _ .fₛ = Const I (⊤ₛ ⇒ₛ ⊤ₛ) (Id ⊤ₛ)
  discrete _ O .fₒ = Const ⊤ₛ (setoid O) (ε O)

module _ {I : Setoid c ℓ} {O : CommutativeMonoid c ℓ} where

  private
    module I = Setoid I
    module O = CommutativeMonoid O

  -- Simulation of systems: a mapping of internal
  -- states which respects i/o behavior
  record _≤_ (A B : System I O) : Set (c ⊔ ℓ) where

    private
      module A = System A
      module B = System B

    field
      ⇒S : ∣ A.S ⇒ₛ B.S ∣
      ≗-fₛ : (i : I.Carrier) (s : ∣ A.S ∣) → ⇒S ⟨$⟩ (A.fₛ′ i s) B.S.≈ B.fₛ′ i (⇒S ⟨$⟩ s)
      ≗-fₒ : (s : ∣ A.S ∣) → A.fₒ′ s O.≈ B.fₒ′ (⇒S ⟨$⟩ s)

  infix 4 _≤_

  open _≤_
  open System

  -- ≤ is reflexive: every system simulates itself
  ≤-refl : Reflexive _≤_
  ⇒S ≤-refl = Id _
  ≗-fₛ (≤-refl {x}) _ _ = S.refl x
  ≗-fₒ ≤-refl _ = O.refl

  -- ≤ is transitive: if B simulates A, and C simulates B, then C simulates A
  ≤-trans : Transitive _≤_
  ⇒S (≤-trans a b) = ⇒S b ∙ ⇒S a
  ≗-fₛ (≤-trans {x} {y} {z} a b) i s = let open ≈-Reasoning (S z) in begin
      ⇒S b ⟨$⟩ (⇒S a ⟨$⟩ (fₛ′ x i s)) ≈⟨ cong (⇒S b) (≗-fₛ a i s) ⟩
      ⇒S b ⟨$⟩ (fₛ′ y i (⇒S a ⟨$⟩ s)) ≈⟨ ≗-fₛ b i (⇒S a ⟨$⟩ s) ⟩
      fₛ′ z i (⇒S b ⟨$⟩ (⇒S a ⟨$⟩ s)) ∎
  ≗-fₒ (≤-trans {x} {y} {z} a b) s = let open ≈-Reasoning O.setoid in begin
      fₒ′ x s                       ≈⟨ ≗-fₒ a s ⟩
      fₒ′ y (⇒S a ⟨$⟩ s)            ≈⟨ ≗-fₒ b (⇒S a ⟨$⟩ s) ⟩
      fₒ′ z (⇒S b ⟨$⟩ (⇒S a ⟨$⟩ s)) ∎
