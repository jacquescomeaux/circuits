{-# OPTIONS --without-K --safe #-}

module Data.Castable where

open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; subst)

record IsCastable {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} (B : A → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where

  field
    cast : {e e′ : A} → .(e ≡ e′) → B e → B e′
    cast-trans
        : {m n o : A}
        → .(eq₁ : m ≡ n)
          .(eq₂ : n ≡ o)
          (x : B m)
        → cast eq₂ (cast eq₁ x) ≡ cast (trans eq₁ eq₂) x
    cast-is-id : {m : A} .(eq : m ≡ m) (x : B m) → cast eq x ≡ x
    subst-is-cast : {m n : A} (eq : m ≡ n) (x : B m) → subst B eq x ≡ cast eq x

record Castable {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  field
    B : A → Set ℓ₂
    isCastable : IsCastable B
