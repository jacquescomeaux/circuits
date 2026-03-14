{-# OPTIONS --without-K --safe #-}

open import Level using (Level; 0ℓ; suc)

module Data.System.Category {ℓ : Level} where

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Categories.Category using (Category)
open import Data.Nat using (ℕ)
open import Data.System.Core {ℓ} using (System; _≤_; ≤-trans; ≤-refl)
open import Data.Setoid using (_⇒ₛ_)
open import Function using (Func; _⟨$⟩_; flip)
open import Relation.Binary as Rel using (Setoid; Rel)

open Func
open System
open _≤_

private module ≈ {n m : ℕ} where

  private
    variable
      A B C : System n m

  _≈_ : Rel (A ≤ B) 0ℓ
  _≈_ {A} {B} ≤₁ ≤₂ = ⇒S ≤₁ A⇒B.≈ ⇒S ≤₂
    where
      module A⇒B = Setoid (S A ⇒ₛ S B)

  open Rel.IsEquivalence

  ≈-isEquiv : Rel.IsEquivalence (_≈_ {A} {B})
  ≈-isEquiv {B = B} .refl = S.refl B
  ≈-isEquiv {B = B} .sym a = S.sym B a
  ≈-isEquiv {B = B} .trans a b = S.trans B a b

  ≤-resp-≈ : {f h : B ≤ C} {g i : A ≤ B} → f ≈ h → g ≈ i → ≤-trans g f ≈ ≤-trans i h
  ≤-resp-≈ {_} {C} {_} {f} {h} {g} {i} f≈h g≈i {x} = begin
      ⇒S f ⟨$⟩ (⇒S g ⟨$⟩ x) ≈⟨ f≈h ⟩
      ⇒S h ⟨$⟩ (⇒S g ⟨$⟩ x) ≈⟨ cong (⇒S h) g≈i ⟩
      ⇒S h ⟨$⟩ (⇒S i ⟨$⟩ x) ∎
    where
      open ≈-Reasoning (System.S C)

open ≈ using (_≈_) public
open ≈ using (≈-isEquiv; ≤-resp-≈)

Systems[_,_] : ℕ → ℕ → Category (suc 0ℓ) ℓ 0ℓ
Systems[ n , m ] = record
    { Obj = System n m
    ; _⇒_ = _≤_
    ; _≈_ = _≈_
    ; id = ≤-refl
    ; _∘_ = flip ≤-trans
    ; assoc = λ {D = D} → S.refl D
    ; sym-assoc = λ {D = D} → S.refl D
    ; identityˡ = λ {B = B} → S.refl B
    ; identityʳ = λ {B = B} → S.refl B
    ; identity² = λ {A = A} → S.refl A
    ; equiv = ≈-isEquiv
    ; ∘-resp-≈ = λ {f = f} {h} {g} {i} → ≤-resp-≈ {f = f} {h} {g} {i}
    }
