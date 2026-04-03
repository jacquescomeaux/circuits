{-# OPTIONS --without-K --safe #-}

open import Algebra using (CommutativeSemiring)
open import Level using (Level; _⊔_)

module Data.Matrix.FreeSemimodule {c ℓ : Level} (R : CommutativeSemiring c ℓ) where

module R = CommutativeSemiring R

import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Categories.Functor using (Functor)
open import Category.Instance.Semimodules {c} {ℓ} {c} {c ⊔ ℓ} R using (Semimodules; SemimoduleHomomorphism)
open import Data.Matrix.Category R.semiring using (Mat; _·_; ·-[])
open import Data.Matrix.Core R.setoid using (Matrix; module ≋; mapRows)
open import Data.Matrix.Transform R.semiring using (I; _[_]; -[-]-cong; -[-]-cong₁; [_]_; -[⟨0⟩]; I[-]; -[⊕])
open import Data.Nat using (ℕ)
open import Data.Vec using (map)
open import Data.Vec.Properties using (map-∘)
open import Data.Vector.Bisemimodule R.semiring using (_⟨_⟩; ⟨_⟩_; _∙_; *-∙ˡ; *-∙ʳ; ∙-cong)
open import Data.Vector.Core R.setoid using (Vector; Vectorₛ; _≊_; module ≊)
open import Data.Vector.Monoid R.+-monoid using (_⊕_; ⊕-cong; ⟨ε⟩)
open import Data.Vector.Semimodule R using (Vector-Semimodule; ⟨-⟩-comm)

open R

opaque

  unfolding _[_] _⟨_⟩

  -[-⟨-⟩] : {A B : ℕ} (M : Matrix A B) (r : Carrier) (V : Vector A) → M [ r ⟨ V ⟩ ] ≊ r ⟨ M [ V ] ⟩
  -[-⟨-⟩] {A} M r V = begin
      map (λ x → x ∙ r ⟨ V ⟩) M ≈⟨ PW.map⁺ lemma {xs = M} ≋.refl ⟩
      map (λ x → r * x ∙ V) M   ≡⟨ map-∘ (r *_) (_∙ V) M ⟩
      map (r *_) (map (_∙ V) M) ∎
    where
      lemma : {X Y : Vector A} → X ≊ Y → X ∙ r ⟨ V ⟩ ≈ r * Y ∙ V
      lemma {X} {Y} X≊Y = begin
          X ∙ r ⟨ V ⟩ ≈⟨ ∙-cong ≊.refl (⟨-⟩-comm r V) ⟩
          X ∙ ⟨ V ⟩ r ≈⟨ *-∙ʳ X V r ⟨
          X ∙ V * r   ≈⟨ *-comm (X ∙ V) r ⟩
          r * X ∙ V   ≈⟨ *-congˡ (∙-cong X≊Y ≊.refl) ⟩
          r * Y ∙ V   ∎
        where
          open ≈-Reasoning R.setoid
      open ≈-Reasoning (Vectorₛ _)

  -[⟨-⟩-] : {A B : ℕ} (M : Matrix A B) (r : Carrier) (V : Vector A) → M [ ⟨ V ⟩ r ] ≊ ⟨ M [ V ] ⟩ r
  -[⟨-⟩-] {A} {B} M r V = begin
      map (λ x → x ∙ ⟨ V ⟩ r) M ≈⟨ PW.map⁺ (λ {W} ≊W → trans (*-∙ʳ W V r) (∙-cong ≊W ≊.refl)) {xs = M} ≋.refl ⟨
      map (λ x → x ∙ V * r) M   ≡⟨ map-∘ (_* r) (_∙ V) M ⟩
      map (_* r) (map (_∙ V) M) ∎
    where
      open ≈-Reasoning (Vectorₛ _)

F₁  : {A B : ℕ}
    → Matrix A B
    → SemimoduleHomomorphism (Vector-Semimodule A) (Vector-Semimodule B)
F₁ M = record
    { ⟦_⟧ = M [_]
    ; isSemimoduleHomomorphism = record
        { isBisemimoduleHomomorphism = record
            { +ᴹ-isMonoidHomomorphism = record
                { isMagmaHomomorphism = record
                    { isRelHomomorphism = record
                        { cong = -[-]-cong M
                        }
                    ; homo = -[⊕] M
                    }
                ; ε-homo = -[⟨0⟩] M
                }
            ; *ₗ-homo = -[-⟨-⟩] M
            ; *ᵣ-homo = -[⟨-⟩-] M
            }
        }
    }

Free : Functor Mat Semimodules
Free = record
    { F₀ = Vector-Semimodule
    ; F₁ = F₁
    ; identity = I[-]
    ; homomorphism = λ {f = M} {N} V → ·-[] M N V
    ; F-resp-≈ = -[-]-cong₁
    }
