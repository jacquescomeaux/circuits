{-# OPTIONS --without-K --safe #-}

module Data.Fin.Preimage where

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Function.Base using (∣_⟩-_; _∘_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≗_)
open import Data.Subset.Functional using (Subset; foldl; _∪_; ⊥; ⁅_⁆)

private
  variable A B C : ℕ

preimage : (Fin A → Fin B) → Subset B → Subset A
preimage f Y = Y ∘ f

⋃ : Subset A → (Fin A → Subset B) → Subset B
⋃ S f = foldl (∣ _∪_ ⟩- f) ⊥ S

image : (Fin A → Fin B) → Subset A → Subset B
image f X = ⋃ X (⁅_⁆ ∘ f)

preimage-cong₁
    : {f g : Fin A → Fin B}
    → f ≗ g
    → (S : Subset B)
    → preimage f S ≗ preimage g S
preimage-cong₁ f≗g S x = ≡.cong S (f≗g x)

preimage-cong₂
    : (f : Fin A → Fin B)
      {S₁ S₂ : Subset B}
    → S₁ ≗ S₂
    → preimage f S₁ ≗ preimage f S₂
preimage-cong₂ f S₁≗S₂ = S₁≗S₂ ∘ f

preimage-∘
    : (f : Fin A → Fin B)
      (g : Fin B → Fin C)
      (z : Fin C)
    → preimage (g ∘ f) ⁅ z ⁆ ≗ preimage f (preimage g ⁅ z ⁆)
preimage-∘ f g S x = ≡.refl
