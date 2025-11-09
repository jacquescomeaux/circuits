{-# OPTIONS --without-K --safe #-}

open import Level using (Level; 0ℓ; suc)

module Data.System {ℓ : Level} where

import Relation.Binary.Properties.Preorder as PreorderProperties
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Categories.Category using (Category)
open import Categories.Category.Instance.SingletonSet using () renaming (SingletonSetoid to ⊤ₛ)
open import Data.Circuit.Value using (Monoid)
open import Data.Nat using (ℕ)
open import Data.Setoid using (_⇒ₛ_; ∣_∣)
open import Data.System.Values Monoid using (Values; _≋_; module ≋; <ε>)
open import Function using (Func; _⟨$⟩_; flip)
open import Function.Construct.Constant using () renaming (function to Const)
open import Function.Construct.Identity using () renaming (function to Id)
open import Function.Construct.Setoid using (_∙_)
open import Level using (Level; 0ℓ; suc)
open import Relation.Binary as Rel using (Reflexive; Transitive; Preorder; Setoid; Rel)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open Func

module _ (n : ℕ) where

  record System : Set₁ where

    field
      S : Setoid 0ℓ 0ℓ
      fₛ : ∣ Values n ⇒ₛ S ⇒ₛ S ∣
      fₒ : ∣ S ⇒ₛ Values n ∣

    fₛ′ : ∣ Values n ∣ → ∣ S ∣ → ∣ S ∣
    fₛ′ i = to (to fₛ i)

    fₒ′ : ∣ S ∣ → ∣ Values n ∣
    fₒ′ = to fₒ

    module S = Setoid S

  open System

  discrete : System
  discrete .S = ⊤ₛ
  discrete .fₛ = Const (Values n) (⊤ₛ ⇒ₛ ⊤ₛ) (Id ⊤ₛ)
  discrete .fₒ = Const ⊤ₛ (Values n) <ε>

module _ {n : ℕ} where

  record _≤_ (a b : System n) : Set ℓ where

    private
      module A = System a
      module B = System b

    open B using (S)

    field
      ⇒S : ∣ A.S ⇒ₛ B.S ∣
      ≗-fₛ : (i : ∣ Values n ∣) (s : ∣ A.S ∣) → ⇒S ⟨$⟩ (A.fₛ′ i s) S.≈ B.fₛ′ i (⇒S ⟨$⟩ s)
      ≗-fₒ : (s : ∣ A.S ∣) → A.fₒ′ s ≋ B.fₒ′ (⇒S ⟨$⟩ s)

  infix 4 _≤_

open System

private

  module _ {n : ℕ} where

    open _≤_

    ≤-refl : Reflexive (_≤_ {n})
    ⇒S ≤-refl = Id _
    ≗-fₛ (≤-refl {x}) _ _ = S.refl x
    ≗-fₒ ≤-refl _ = ≋.refl

    ≡⇒≤ : _≡_ Rel.⇒ _≤_
    ≡⇒≤ ≡.refl = ≤-refl

    ≤-trans : Transitive _≤_
    ⇒S (≤-trans a b) = ⇒S b ∙ ⇒S a
    ≗-fₛ (≤-trans {x} {y} {z} a b) i s = let open ≈-Reasoning (S z) in begin
        ⇒S b ⟨$⟩ (⇒S a ⟨$⟩ (fₛ′ x i s)) ≈⟨ cong (⇒S b) (≗-fₛ a i s) ⟩
        ⇒S b ⟨$⟩ (fₛ′ y i (⇒S a ⟨$⟩ s)) ≈⟨ ≗-fₛ b i (⇒S a ⟨$⟩ s) ⟩
        fₛ′ z i (⇒S b ⟨$⟩ (⇒S a ⟨$⟩ s)) ∎
    ≗-fₒ (≤-trans {x} {y} {z} a b) s = let open ≈-Reasoning (Values n) in begin
        fₒ′ x s                       ≈⟨ ≗-fₒ a s ⟩
        fₒ′ y (⇒S a ⟨$⟩ s)            ≈⟨ ≗-fₒ b (⇒S a ⟨$⟩ s) ⟩
        fₒ′ z (⇒S b ⟨$⟩ (⇒S a ⟨$⟩ s)) ∎

    variable
      A B C : System n

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

System-≤ : ℕ → Preorder (suc 0ℓ) (suc 0ℓ) ℓ
System-≤ n = record
    { _≲_ = _≤_ {n}
    ; isPreorder = record
        { isEquivalence = ≡.isEquivalence
        ; reflexive = ≡⇒≤
        ; trans = ≤-trans
        }
    }

Systemₛ : ℕ → Setoid (suc 0ℓ) ℓ
Systemₛ n = PreorderProperties.InducedEquivalence (System-≤ n)

Systems : ℕ → Category (suc 0ℓ) ℓ 0ℓ
Systems n = record
    { Obj = System n
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
