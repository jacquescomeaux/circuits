{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Category.Dagger.Semiadditive using (IdempotentSemiadditiveDagger)
open import Level using (Level; suc; _⊔_)

module Category.Dagger.2-Poset {o ℓ e : Level} where

import Relation.Binary.Reasoning.PartialOrder as ≤-Reasoning

open import Category.Monoidal.Instance.Posets {ℓ} {e} {e} using (Posets-Monoidal)

open import Categories.Category.Dagger using (HasDagger)
open import Categories.Category.Helper using (categoryHelper)
open import Categories.Category.Instance.Posets using (Posets)
open import Categories.Enriched.Category Posets-Monoidal using () renaming (Category to 2-Poset)
open import Data.Product using (_,_)
open import Data.Unit.Polymorphic using (tt)
open import Relation.Binary using (Poset)
open import Relation.Binary.Morphism.Bundles using (PosetHomomorphism; mkPosetHomo)

open PosetHomomorphism using (⟦_⟧; cong; mono)

record Dagger-2-Poset : Set (suc (o ⊔ ℓ ⊔ e)) where

  open Poset using (Carrier; _≈_; isEquivalence)

  field
    2-poset : 2-Poset o

  open 2-Poset 2-poset hiding (id) public
  open 2-Poset 2-poset using (id)

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
  open Category category hiding (Obj) public
  open HasDagger hasDagger public

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

module _ (S : Dagger-2-Poset) where

  open Dagger-2-Poset S

  record IsMap {A B : Obj} (f : A ⇒ B) : Set e where

    field
      functional : f ∘ f † ≤ id
      entire : id ≤ f † ∘ f

  record Map (A B : Obj) : Set (ℓ ⊔ e) where

    field
      map : A ⇒ B
      isMap : IsMap map

    open IsMap isMap public

  idMap : {A : Obj} → Map A A
  idMap {A} = record
      { map = id
      ; isMap = record
          { functional = begin
              id ∘ id † ≈⟨ identityˡ ⟩
              id †      ≈⟨ †-identity ⟩
              id        ∎
          ; entire = begin
              id        ≈⟨ †-identity ⟨
              id †      ≈⟨ identityʳ ⟨
              id † ∘ id ∎
          }
      }
    where
      open ≤-Reasoning (hom A A)

  _∘-map_ : {A B C : Obj} → Map B C → Map A B → Map A C
  _∘-map_ {A} {B} {C} g f = record
      { map = g.map ∘ f.map
      ; isMap = record
          { functional = func
          ; entire = ent
          }
      }
    where
      module g = Map g
      module f = Map f
      func : (g.map ∘ f.map) ∘ (g.map ∘ f.map) † ≤ id
      func = begin
          (g.map ∘ f.map) ∘ (g.map ∘ f.map) † ≈⟨ refl⟩∘⟨ †-homomorphism ⟩
          (g.map ∘ f.map) ∘ f.map † ∘ g.map † ≈⟨ assoc ⟩
          g.map ∘ f.map ∘ f.map † ∘ g.map †   ≈⟨ refl⟩∘⟨ assoc ⟨
          g.map ∘ (f.map ∘ f.map †) ∘ g.map † ≤⟨ mono ⊚ (Poset.refl (hom B C) , mono ⊚ (f.functional , Poset.refl (hom C B))) ⟩
          g.map ∘ id ∘ g.map †                ≈⟨ refl⟩∘⟨ identityˡ ⟩
          g.map ∘ g.map †                     ≤⟨ g.functional ⟩
          id                                  ∎
        where
          open ≤-Reasoning (hom C C)
          open HomReasoning using (refl⟩∘⟨_)
          open Poset (hom C C)
      ent : id ≤ (g.map ∘ f.map) † ∘ g.map ∘ f.map
      ent = begin
          id                                  ≤⟨ f.entire ⟩
          f.map † ∘ f.map                     ≈⟨ refl⟩∘⟨ identityˡ ⟨
          f.map † ∘ id ∘ f.map                ≤⟨ mono ⊚ (Poset.refl (hom B A) , mono ⊚ (g.entire , Poset.refl (hom A B))) ⟩
          f.map † ∘ (g.map † ∘ g.map) ∘ f.map ≈⟨ refl⟩∘⟨ assoc ⟩
          f.map † ∘ g.map † ∘ g.map ∘ f.map   ≈⟨ assoc ⟨
          (f.map † ∘ g.map †) ∘ g.map ∘ f.map ≈⟨ †-homomorphism ⟩∘⟨refl ⟨
          (g.map ∘ f.map) † ∘ g.map ∘ f.map   ∎
        where
          open ≤-Reasoning (hom A A)
          open HomReasoning using (refl⟩∘⟨_; _⟩∘⟨refl)
          open Poset (hom A A)

  infixr 9 _∘-map_

  open Map

  Maps : Category o (ℓ ⊔ e) e
  Maps = categoryHelper record
      { Obj = Obj
      ; _⇒_ = Map
      ; _≈_ = λ a b → map a ≈ map b
      ; id = idMap
      ; _∘_ = _∘-map_
      ; assoc = assoc
      ; identityˡ = identityˡ
      ; identityʳ = identityʳ
      ; equiv = record
          { refl = Equiv.refl
          ; sym = Equiv.sym
          ; trans = Equiv.trans
          }
      ; ∘-resp-≈ = ∘-resp-≈
      }
