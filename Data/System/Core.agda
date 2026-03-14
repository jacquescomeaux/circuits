{-# OPTIONS --without-K --safe #-}

open import Level using (Level; 0ℓ; suc)

module Data.System.Core {ℓ : Level} where

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Data.Circuit.Value using (Monoid)
open import Data.Nat using (ℕ)
open import Data.Setoid using (_⇒ₛ_; ∣_∣)
open import Data.Setoid.Unit using (⊤ₛ)
open import Data.Values Monoid using (Values; _≋_; module ≋; <ε>)
open import Function using (Func; _⟨$⟩_)
open import Function.Construct.Constant using () renaming (function to Const)
open import Function.Construct.Identity using () renaming (function to Id)
open import Function.Construct.Setoid using (_∙_)
open import Relation.Binary using (Setoid; Reflexive; Transitive)

open Func

-- A dynamical system with a set of states,
-- a state update function,
-- and a readout function
record System (n m : ℕ) : Set₁ where

  field
    S : Setoid 0ℓ 0ℓ
    fₛ : ∣ Values n ⇒ₛ S ⇒ₛ S ∣
    fₒ : ∣ S ⇒ₛ Values m ∣

  fₛ′ : ∣ Values n ∣ → ∣ S ∣ → ∣ S ∣
  fₛ′ i = to (to fₛ i)

  fₒ′ : ∣ S ∣ → ∣ Values m ∣
  fₒ′ = to fₒ

  module S = Setoid S

open System

-- the discrete system from n nodes to m nodes
discrete : (n m : ℕ) → System n m
discrete _ _ .S = ⊤ₛ
discrete n _ .fₛ = Const (Values n) (⊤ₛ ⇒ₛ ⊤ₛ) (Id ⊤ₛ)
discrete _ m .fₒ = Const ⊤ₛ (Values m) <ε>

module _ {n m : ℕ} where

  -- Simulation of systems: a mapping of internal
  -- states which respects i/o behavior
  record _≤_ (A B : System n m) : Set ℓ where

    private
      module A = System A
      module B = System B

    field
      ⇒S : ∣ A.S ⇒ₛ B.S ∣
      ≗-fₛ : (i : ∣ Values n ∣) (s : ∣ A.S ∣) → ⇒S ⟨$⟩ (A.fₛ′ i s) B.S.≈ B.fₛ′ i (⇒S ⟨$⟩ s)
      ≗-fₒ : (s : ∣ A.S ∣) → A.fₒ′ s ≋ B.fₒ′ (⇒S ⟨$⟩ s)

  infix 4 _≤_

  open _≤_
  open System

  -- ≤ is reflexive: every system simulates itself
  ≤-refl : Reflexive _≤_
  ⇒S ≤-refl = Id _
  ≗-fₛ (≤-refl {x}) _ _ = S.refl x
  ≗-fₒ ≤-refl _ = ≋.refl

  -- ≤ is transitive: if B simulates A, and C simulates B, then C simulates A
  ≤-trans : Transitive _≤_
  ⇒S (≤-trans a b) = ⇒S b ∙ ⇒S a
  ≗-fₛ (≤-trans {x} {y} {z} a b) i s = let open ≈-Reasoning (S z) in begin
      ⇒S b ⟨$⟩ (⇒S a ⟨$⟩ (fₛ′ x i s)) ≈⟨ cong (⇒S b) (≗-fₛ a i s) ⟩
      ⇒S b ⟨$⟩ (fₛ′ y i (⇒S a ⟨$⟩ s)) ≈⟨ ≗-fₛ b i (⇒S a ⟨$⟩ s) ⟩
      fₛ′ z i (⇒S b ⟨$⟩ (⇒S a ⟨$⟩ s)) ∎
  ≗-fₒ (≤-trans {x} {y} {z} a b) s = let open ≈-Reasoning (Values m) in begin
      fₒ′ x s                       ≈⟨ ≗-fₒ a s ⟩
      fₒ′ y (⇒S a ⟨$⟩ s)            ≈⟨ ≗-fₒ b (⇒S a ⟨$⟩ s) ⟩
      fₒ′ z (⇒S b ⟨$⟩ (⇒S a ⟨$⟩ s)) ∎
