{-# OPTIONS --without-K --safe #-}

open import Algebra using (Semiring)
open import Level using (Level; _⊔_)

module Data.Vector.Bisemimodule {c ℓ : Level} (R : Semiring c ℓ) where

module R = Semiring R

import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Algebra using (CommutativeMonoid)
open import Algebra.Module using (Bisemimodule)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; map)
open import Data.Vector.CommutativeMonoid R.+-commutativeMonoid using (Vectorₘ)
open import Data.Vector.Core R.setoid using (Vector; _≊_; module ≊)
open import Data.Vector.Monoid R.*-monoid using () renaming (_⊕_ to _⊗_; ⊕-cong to ⊗-cong)
open import Data.Vector.Monoid R.+-monoid using (sum; sum-cong; _⊕_; ⊕-cong; ⟨ε⟩; ⊕-identityˡ)
open import Function using (flip)

open R
open Vec
open ℕ

open ≈-Reasoning setoid

private
  variable
    n : ℕ

opaque

  unfolding Vector

  -- Scaling a vector from the left
  _⟨_⟩ : Carrier → Vector n → Vector n
  _⟨_⟩ r = map (r *_)

  -⟨-⟩-cong : {r r′ : Carrier} {V V′ : Vector n} → r ≈ r′ → V ≊ V′ → r ⟨ V ⟩ ≊ r′ ⟨ V′ ⟩
  -⟨-⟩-cong ≈r ≊V = PW.map⁺ (*-cong ≈r) ≊V

  -- Scaling a vector from the right
  ⟨_⟩_ : Vector n → Carrier → Vector n
  ⟨_⟩_ v r = map (_* r) v

  ⟨-⟩--cong : {r r′ : Carrier} {V V′ : Vector n} → V ≊ V′ → r ≈ r′ → ⟨ V ⟩ r ≊ ⟨ V′ ⟩ r′
  ⟨-⟩--cong ≊V ≈r = PW.map⁺ (flip *-cong ≈r) ≊V

  -- Scaling by one from the left
  1⟨-⟩ : (V : Vector n) → 1# ⟨ V ⟩ ≊ V
  1⟨-⟩ [] = PW.[]
  1⟨-⟩ (x ∷ V) = *-identityˡ x PW.∷ 1⟨-⟩ V

  -- Scaling by one from the right
  ⟨-⟩1 : (V : Vector n) → ⟨ V ⟩ 1# ≊ V
  ⟨-⟩1 [] = PW.[]
  ⟨-⟩1 (x ∷ V) = *-identityʳ x PW.∷ ⟨-⟩1 V

  -- Associativity from left
  -⟨-⟩-assoc : (r s : Carrier) (V : Vector n) → (r * s) ⟨ V ⟩ ≊ r ⟨ s ⟨ V ⟩ ⟩
  -⟨-⟩-assoc r s [] = PW.[]
  -⟨-⟩-assoc r s (x ∷ V) = *-assoc r s x PW.∷ -⟨-⟩-assoc r s V

  -- Associativity from right
  ⟨-⟩--assoc : (V : Vector n) (r s : Carrier) → ⟨ ⟨ V ⟩ r ⟩ s ≊ ⟨ V ⟩ (r * s)
  ⟨-⟩--assoc [] r s = PW.[]
  ⟨-⟩--assoc (x ∷ V) r s = *-assoc x r s PW.∷ ⟨-⟩--assoc V r s

  -- Scaling by left then right
  ⟨-⟨-⟩⟩--assoc : (r : Carrier) (V : Vector n) (s : Carrier) → ⟨ r ⟨ V ⟩ ⟩ s ≊ r ⟨ ⟨ V ⟩ s ⟩
  ⟨-⟨-⟩⟩--assoc r [] s = PW.[]
  ⟨-⟨-⟩⟩--assoc r (x ∷ V) s = *-assoc r x s PW.∷ ⟨-⟨-⟩⟩--assoc r V s

infix 9 _⟨_⟩ ⟨_⟩_

opaque

  unfolding _⟨_⟩ ⟨_⟩_ ⟨ε⟩

  -- Scaling by zero from the left
  0⟨-⟩ : (V : Vector n) → 0# ⟨ V ⟩ ≊ ⟨ε⟩
  0⟨-⟩ [] = PW.[]
  0⟨-⟩ (x ∷ V) = zeroˡ x PW.∷ 0⟨-⟩ V

  -- Scaling by zero from the right
  ⟨-⟩0 : (V : Vector n) → ⟨ V ⟩ 0# ≊ ⟨ε⟩
  ⟨-⟩0 [] = PW.[]
  ⟨-⟩0 (x ∷ V) = zeroʳ x PW.∷ ⟨-⟩0 V

  -- scaling the zero vector from the left
  -⟨ε⟩ : (r : Carrier) → r ⟨ ⟨ε⟩ ⟩ ≊ ⟨ε⟩ {n}
  -⟨ε⟩ {zero} r = PW.[]
  -⟨ε⟩ {suc n} r = zeroʳ r PW.∷ -⟨ε⟩ r

  -- scaling the zero vector from the right
  ⟨ε⟩- : (r : Carrier) → ⟨ ⟨ε⟩ ⟩ r ≊ ⟨ε⟩ {n}
  ⟨ε⟩- {zero} r = PW.[]
  ⟨ε⟩- {suc n} r = zeroˡ r PW.∷ ⟨ε⟩- r

opaque

  unfolding _⟨_⟩ ⟨_⟩_ _⊕_

  -⟨-⟩-distribʳ : (V : Vector n) (r s : Carrier) → (r + s) ⟨ V ⟩ ≊ r ⟨ V ⟩ ⊕ s ⟨ V ⟩
  -⟨-⟩-distribʳ [] r s = PW.[]
  -⟨-⟩-distribʳ (x ∷ V) r s = distribʳ x r s PW.∷ -⟨-⟩-distribʳ V r s

  -⟨-⟩-distribˡ : (r : Carrier) (V W : Vector n) → r ⟨ V ⊕ W ⟩ ≊ r ⟨ V ⟩ ⊕ r ⟨ W ⟩
  -⟨-⟩-distribˡ r [] [] = PW.[]
  -⟨-⟩-distribˡ r (v ∷ V) (w ∷ W) = distribˡ r v w PW.∷ -⟨-⟩-distribˡ r V W

  ⟨-⟩--distribˡ : (V : Vector n) (r s : Carrier) → ⟨ V ⟩ (r + s) ≊ ⟨ V ⟩ r ⊕ ⟨ V ⟩ s
  ⟨-⟩--distribˡ [] r s = PW.[]
  ⟨-⟩--distribˡ (x ∷ V) r s = distribˡ x r s PW.∷ ⟨-⟩--distribˡ V r s

  ⟨-⟩--distribʳ : (r : Carrier) (V W : Vector n) → ⟨ V ⊕ W ⟩ r ≊ ⟨ V ⟩ r ⊕ ⟨ W ⟩ r
  ⟨-⟩--distribʳ r [] [] = PW.[]
  ⟨-⟩--distribʳ r (v ∷ V) (w ∷ W) = distribʳ r v w PW.∷ ⟨-⟩--distribʳ r V W

opaque

  unfolding sum _⊗_

  -- Dot product of two vectors
  _∙_ : Vector n → Vector n → Carrier
  _∙_ V W = sum (V ⊗ W)

  ∙-cong : {v₁ v₂ w₁ w₂ : Vector n} → v₁ ≊ v₂ → w₁ ≊ w₂ → v₁ ∙ w₁ ≈ v₂ ∙ w₂
  ∙-cong {n} ≊v ≊w = sum-cong (⊗-cong ≊v ≊w)

infix 8 _∙_

opaque

  unfolding _∙_ ⟨ε⟩

  ∙-zeroˡ : (V : Vector n) → ⟨ε⟩ ∙ V ≈ 0#
  ∙-zeroˡ [] = refl
  ∙-zeroˡ (x ∷ V) = begin
      0# * x + ⟨ε⟩ ∙ V  ≈⟨ +-congʳ (zeroˡ x) ⟩
      0# + ⟨ε⟩ ∙ V      ≈⟨ +-congˡ (∙-zeroˡ V) ⟩
      0# + 0#           ≈⟨ +-identityˡ 0# ⟩
      0#                ∎

  ∙-zeroʳ : (V : Vector n) → V ∙ ⟨ε⟩ ≈ 0#
  ∙-zeroʳ [] = refl
  ∙-zeroʳ (x ∷ V) = begin
      x * 0# + V ∙ ⟨ε⟩  ≈⟨ +-congʳ (zeroʳ x) ⟩
      0# + V ∙ ⟨ε⟩      ≈⟨ +-congˡ (∙-zeroʳ V) ⟩
      0# + 0#           ≈⟨ +-identityˡ 0# ⟩
      0#                ∎

opaque

  unfolding _∙_ _⊕_

  ∙-distribʳ : (A B C : Vector n) → (A ⊕ B) ∙ C ≈ A ∙ C + B ∙ C
  ∙-distribʳ [] [] [] = sym (+-identityˡ 0#)
  ∙-distribʳ (a ∷ A) (b ∷ B) (c ∷ C) = begin
      (a + b) * c + ((A ⊕ B) ∙ C)       ≈⟨ +-congˡ (∙-distribʳ A B C) ⟩
      (a + b) * c + (A ∙ C + B ∙ C)     ≈⟨ +-congʳ (distribʳ c a b) ⟩
      a * c + b * c + (A ∙ C + B ∙ C)   ≈⟨ +-assoc _ _ _ ⟩
      a * c + (b * c + (A ∙ C + B ∙ C)) ≈⟨ +-congˡ (+-assoc _ _ _) ⟨
      a * c + (b * c + A ∙ C + B ∙ C)   ≈⟨ +-congˡ (+-congʳ (+-comm _ _)) ⟩
      a * c + (A ∙ C + b * c + B ∙ C)   ≈⟨ +-congˡ (+-assoc _ _ _) ⟩
      a * c + (A ∙ C + (b * c + B ∙ C)) ≈⟨ +-assoc _ _ _ ⟨
      a * c + A ∙ C + (b * c + B ∙ C)   ∎

  ∙-distribˡ : (A B C : Vector n) → A ∙ (B ⊕ C) ≈ A ∙ B + A ∙ C
  ∙-distribˡ [] [] [] = sym (+-identityˡ 0#)
  ∙-distribˡ (a ∷ A) (b ∷ B) (c ∷ C) = begin
      a * (b + c) + A ∙ (B ⊕ C)         ≈⟨ +-congˡ (∙-distribˡ A B C) ⟩
      a * (b + c) + (A ∙ B + A ∙ C)     ≈⟨ +-congʳ (distribˡ a b c) ⟩
      a * b + a * c + (A ∙ B + A ∙ C)   ≈⟨ +-assoc _ _ _ ⟩
      a * b + (a * c + (A ∙ B + A ∙ C)) ≈⟨ +-congˡ (+-assoc _ _ _) ⟨
      a * b + (a * c + A ∙ B + A ∙ C)   ≈⟨ +-congˡ (+-congʳ (+-comm _ _)) ⟩
      a * b + (A ∙ B + a * c + A ∙ C)   ≈⟨ +-congˡ (+-assoc _ _ _) ⟩
      a * b + (A ∙ B + (a * c + A ∙ C)) ≈⟨ +-assoc _ _ _ ⟨
      a * b + A ∙ B + (a * c + A ∙ C)   ∎

opaque

  unfolding _⟨_⟩ _∙_

  *-∙ˡ : (r : Carrier) (A B : Vector n) → r * A ∙ B ≈ r ⟨ A ⟩ ∙ B
  *-∙ˡ r [] [] = zeroʳ r
  *-∙ˡ r (a ∷ A) (b ∷ B) = begin
      r * (a * b + A ∙ B)     ≈⟨ distribˡ r (a * b) (A ∙ B) ⟩
      r * (a * b) + r * A ∙ B ≈⟨ +-congʳ (*-assoc r a b) ⟨
      r * a * b + r * A ∙ B   ≈⟨ +-congˡ (*-∙ˡ r A B )⟩
      r * a * b + r ⟨ A ⟩ ∙ B ∎

  *-∙ʳ : (A B : Vector n) (r : Carrier) → A ∙ B * r ≈ A ∙ ⟨ B ⟩ r
  *-∙ʳ [] [] r = zeroˡ r
  *-∙ʳ (a ∷ A) (b ∷ B) r = begin
      (a * b + A ∙ B) * r       ≈⟨ distribʳ r (a * b) (A ∙ B) ⟩
      a * b * r + (A ∙ B) * r   ≈⟨ +-congʳ (*-assoc a b r) ⟩
      a * (b * r) + (A ∙ B) * r ≈⟨ +-congˡ (*-∙ʳ A B r) ⟩
      a * (b * r) + A ∙ ⟨ B ⟩ r ∎

Vector-Bisemimodule : ℕ → Bisemimodule R R c (c ⊔ ℓ)
Vector-Bisemimodule n = record
    { Carrierᴹ = Vector n
    ; _≈ᴹ_ = _≊_
    ; _+ᴹ_ = _⊕_
    ; _*ₗ_ = _⟨_⟩
    ; _*ᵣ_ = ⟨_⟩_
    ; 0ᴹ = ⟨ε⟩
    ; isBisemimodule = record
        { +ᴹ-isCommutativeMonoid = record { CommutativeMonoid (Vectorₘ n) }
        ; isPreleftSemimodule = record
            { *ₗ-cong = -⟨-⟩-cong
            ; *ₗ-zeroˡ = 0⟨-⟩
            ; *ₗ-distribʳ = -⟨-⟩-distribʳ
            ; *ₗ-identityˡ = 1⟨-⟩
            ; *ₗ-assoc = -⟨-⟩-assoc
            ; *ₗ-zeroʳ = -⟨ε⟩
            ; *ₗ-distribˡ = -⟨-⟩-distribˡ
            }
        ; isPrerightSemimodule = record
            { *ᵣ-cong = ⟨-⟩--cong
            ; *ᵣ-zeroʳ = ⟨-⟩0
            ; *ᵣ-distribˡ = ⟨-⟩--distribˡ
            ; *ᵣ-identityʳ = ⟨-⟩1
            ; *ᵣ-assoc = ⟨-⟩--assoc
            ; *ᵣ-zeroˡ = ⟨ε⟩-
            ; *ᵣ-distribʳ = ⟨-⟩--distribʳ
            }
        ; *ₗ-*ᵣ-assoc = ⟨-⟨-⟩⟩--assoc
        }
    }
