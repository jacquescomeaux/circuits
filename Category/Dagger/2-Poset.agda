{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Category.Dagger.Semiadditive using (IdempotentSemiadditiveDagger)
open import Level using (Level; suc; _⊔_)

module Category.Dagger.2-Poset {o ℓ e : Level} where

import Categories.Category.Monoidal.Reasoning as ⊗-Reasoning

open import Category.Monoidal.Instance.Posets {ℓ} {e} {e} using (Posets-Monoidal)

open import Categories.Category.Dagger using (HasDagger)
open import Categories.Category.Helper using (categoryHelper)
open import Categories.Category.Instance.Posets using (Posets)
open import Categories.Enriched.Category Posets-Monoidal using () renaming (Category to 2-Poset)
open import Data.Product using (_,_)
open import Data.Unit.Polymorphic using (tt)
open import Relation.Binary using (Poset)
open import Relation.Binary.Morphism.Bundles using (PosetHomomorphism; mkPosetHomo)

open PosetHomomorphism using (⟦_⟧; cong)

record Dagger-2-Poset : Set (suc (o ⊔ ℓ ⊔ e)) where

  open Poset using (Carrier; _≈_; isEquivalence)

  field
    2-poset : 2-Poset o

  open 2-Poset 2-poset

  category : Category o ℓ e
  category = categoryHelper record
      { Obj = Obj
      ; _⇒_ = λ A B → Carrier (hom A B)
      ; _≈_ = λ {A B} → _≈_ (hom A B)
      ; id = ⟦ id ⟧ tt
      ; _∘_ = λ f g → ⟦ ⊚ ⟧ (f , g)
      ; assoc = ⊚-assoc
      ; identityˡ = unitˡ
      ; identityʳ = unitʳ
      ; equiv = λ {A B} → isEquivalence (hom A B)
      ; ∘-resp-≈ = λ f≈h g≈i → cong ⊚ (f≈h , g≈i)
      }

  field
    hasDagger : HasDagger category

  private
    module P {A B : Obj} = Poset (hom A B)

  open P using (_≤_) public
  open Category category using (_⇒_) public
  open HasDagger hasDagger using (_†) public

  field
    †-resp-≤ : {A B : Obj} {f g : A ⇒ B} → f ≤ g → f † ≤ g †

dagger-2-poset : {𝒞 : Category o ℓ e} (ISA† : IdempotentSemiadditiveDagger 𝒞) → Dagger-2-Poset
dagger-2-poset {𝒞} ISA† = record
    { 2-poset = record
        { Obj = Obj
        ; hom = λ A B → record
            { Carrier = A ⇒ B
            ; _≈_ = _≈_
            ; _≤_ = ISA†._≤_
            ; isPartialOrder = record
                { isPreorder = record
                    { isEquivalence = equiv
                    ; reflexive = λ x≈y → Equiv.trans (ISA†.+-congʳ x≈y) ISA†.≤-refl
                    ; trans = ISA†.≤-trans
                    }
                ; antisym = ISA†.≤-antisym
                }
            }
        ; id = mkPosetHomo _ _ (λ _ → id) (λ _ → ISA†.≤-refl)
        ; ⊚ = mkPosetHomo _ _ (λ (f , g) → f ∘ g) (λ (≤₁ , ≤₂) → ISA†.≤-resp-∘ ≤₁ ≤₂)
        ; ⊚-assoc = assoc
        ; unitˡ = identityˡ
        ; unitʳ = identityʳ
        }
    ; hasDagger = record
        { _† = ISA†._†
        ; †-identity = ISA†.†-identity
        ; †-homomorphism = ISA†.†-homomorphism
        ; †-resp-≈ = ISA†.⟨_⟩†
        ; †-involutive = ISA†.†-involutive
        }
    ; †-resp-≤ = ISA†.†-resp-≤
    }
  where
    module ISA† = IdempotentSemiadditiveDagger ISA†
    open Category 𝒞
    open ⊗-Reasoning ISA†.+-monoidal
