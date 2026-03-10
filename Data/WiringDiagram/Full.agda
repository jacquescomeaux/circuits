{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Level using (Level)

module Data.WiringDiagram.Full {o ℓ e : Level} {𝒞 : Category o ℓ e} (M : Monoidal 𝒞) where

open import Categories.Category.Helper using (categoryHelper)
open import Relation.Binary using (IsEquivalence)

module U = Category 𝒞
module M = Monoidal M
open M

record Box : Set o where

  constructor _□_

  field
    ᵢ : U.Obj
    ₒ : U.Obj

infix 4 _□_

record WiringDiagram (A B : Box) : Set ℓ where

  constructor _⧈_

  private
    module A = Box A
    module B = Box B

  field
    input : A.ₒ ⊗₀ B.ᵢ U.⇒ A.ᵢ
    output : A.ₒ U.⇒ B.ₒ

infix 4 _⧈_

record _≈_ {A B : Box} (f g : WiringDiagram A B) : Set e where

  constructor _⌸_

  private

    module f = WiringDiagram f
    module g = WiringDiagram g

  field
    ≈i : f.input U.≈ g.input
    ≈o : f.output U.≈ g.output

infix 4 _≈_

module _ {A B : Box} where

  ≈-refl : {x : WiringDiagram A B} → x ≈ x
  ≈-refl = U.Equiv.refl ⌸ U.Equiv.refl

  ≈-sym : {x y : WiringDiagram A B} → x ≈ y → y ≈ x
  ≈-sym (≈i ⌸ ≈o) = U.Equiv.sym ≈i ⌸ U.Equiv.sym ≈o

  ≈-trans : {x y z : WiringDiagram A B} → x ≈ y → y ≈ z → x ≈ z
  ≈-trans (≈i₁ ⌸ ≈o₁) (≈i₂ ⌸ ≈o₂) = U.Equiv.trans ≈i₁ ≈i₂ ⌸ U.Equiv.trans ≈o₁ ≈o₂

  ≈-isEquiv : IsEquivalence (_≈_ {A} {B})
  ≈-isEquiv = record
      { refl = ≈-refl
      ; sym = ≈-sym
      ; trans = ≈-trans
      }

open import Categories.Object.Monoid using (IsMonoid)
open import Categories.Category.Monoidal.Properties M using (coherence₁) renaming (monoidal-Op to Mᵒᵖ)

comonoid : {A : U.Obj} → IsMonoid Mᵒᵖ A
comonoid = ?

discard : {A : U.Obj} → A U.⇒ unit
discard = IsMonoid.η comonoid

copy : {A : U.Obj} → A U.⇒ A ⊗₀ A
copy = IsMonoid.μ comonoid

module _ {A B : U.Obj} {f : A U.⇒ B} where

  μ⇒ : copy U.∘ f U.≈ f ⊗₁ f U.∘ copy
  μ⇒ = ?

  η⇒ : discard U.∘ f U.≈ discard
  η⇒ = ?

⊗-snd : {A B : U.Obj} → A ⊗₀ B U.⇒ B
⊗-snd {A} {B} = unitorˡ.from U.∘ discard ⊗₁ U.id

id : {A : Box} → WiringDiagram A A
id {A} = ⊗-snd ⧈ U.id

_∘_ : {A B C : Box} → WiringDiagram B C → WiringDiagram A B → WiringDiagram A C
_∘_ {Aᵢ □ Aₒ} {Bᵢ □ Bₒ} {Cᵢ □ Cₒ} (f′ ⧈ g′) (f ⧈ g) = f″ ⧈ g′ U.∘ g
  where
    f″ : Aₒ ⊗₀ Cᵢ U.⇒ Aᵢ
    f″ = f U.∘ U.id ⊗₁ (f′ U.∘ g ⊗₁ U.id) U.∘ associator.from U.∘ copy ⊗₁ U.id

import Categories.Category.Monoidal.Reasoning as ⊗-Reasoning
open import Categories.Category.Monoidal.Utilities M using (module Shorthands)
open Shorthands using (α⇒; α⇐; λ⇒; λ⇐; ρ⇒; ρ⇐)
import Categories.Morphism.Reasoning as ⇒-Reasoning

∘-resp-≈ : {A B C : Box} {f h : WiringDiagram B C} {g i : WiringDiagram A B} → f ≈ h → g ≈ i → f ∘ g ≈ h ∘ i
∘-resp-≈ {A} {B} {C} {fᵢ ⧈ fₒ} {hᵢ ⧈ hₒ} {gᵢ ⧈ gₒ} {iᵢ ⧈ iₒ} (fᵢ≈hᵢ ⌸ fₒ≈hₒ) (gᵢ≈iᵢ ⌸ gₒ≈iₒ) = ≈ᵢ ⌸ U.∘-resp-≈ fₒ≈hₒ gₒ≈iₒ
  where
    open ⊗-Reasoning M
    ≈ᵢ : gᵢ U.∘ U.id ⊗₁ (fᵢ U.∘ gₒ ⊗₁ U.id) U.∘ α⇒ U.∘ copy {Box.ₒ A} ⊗₁ U.id
       U.≈ iᵢ U.∘ U.id ⊗₁ (hᵢ U.∘ iₒ ⊗₁ U.id) U.∘ α⇒ U.∘ copy ⊗₁ U.id
    ≈ᵢ = gᵢ≈iᵢ ⟩∘⟨ refl⟩⊗⟨ (fᵢ≈hᵢ ⟩∘⟨ gₒ≈iₒ ⟩⊗⟨refl) ⟩∘⟨refl

assoc : {A B C D : Box} {f : WiringDiagram A B} {g : WiringDiagram B C} {h : WiringDiagram C D} → (h ∘ g) ∘ f ≈ h ∘ (g ∘ f)
assoc {Aᵢ □ Aₒ} {Bᵢ □ Bₒ} {Cᵢ □ Cₒ} {Dᵢ □ Dₒ} {fᵢ ⧈ fₒ} {gᵢ ⧈ gₒ} {hᵢ ⧈ hₒ} = ≈ᵢ ⌸ U.assoc
  where
    open ⊗-Reasoning M

    term₁ : Aₒ ⊗₀ Dᵢ U.⇒ Cᵢ
    term₁ = hᵢ U.∘ (gₒ U.∘ fₒ) ⊗₁ U.id

    term₂ : Bₒ ⊗₀ Dᵢ U.⇒ Cᵢ
    term₂ = hᵢ U.∘ gₒ ⊗₁ U.id

    term₃ : Aₒ ⊗₀ Cᵢ U.⇒ Bᵢ
    term₃ = gᵢ U.∘ fₒ ⊗₁ U.id
    open ⇒-Reasoning 𝒞

    lemma₁ : α⇒ {Aₒ ⊗₀ Aₒ} {Aₒ} {Dᵢ} U.∘ (α⇐ U.∘ U.id ⊗₁ copy) ⊗₁ U.id U.∘ copy ⊗₁ U.id U.≈ copy ⊗₁ U.id U.∘ α⇒ U.∘ copy ⊗₁ U.id
    lemma₁ = begin
        α⇒ U.∘ (α⇐ U.∘ U.id ⊗₁ copy) ⊗₁ U.id U.∘ copy ⊗₁ U.id         ≈⟨ refl⟩∘⟨ pushˡ split₁ˡ ⟩
        α⇒ U.∘ α⇐ ⊗₁ U.id U.∘ (U.id ⊗₁ copy) ⊗₁ U.id U.∘ copy ⊗₁ U.id ≈⟨ refl⟩∘⟨ refl⟩∘⟨ merge₁ˡ ⟩
        α⇒ U.∘ α⇐ ⊗₁ U.id U.∘ (U.id ⊗₁ copy U.∘ copy) ⊗₁ U.id         ≈⟨ refl⟩∘⟨ merge₁ˡ ⟩
        α⇒ U.∘ (α⇐ U.∘ U.id ⊗₁ copy U.∘ copy) ⊗₁ U.id                 ≈⟨ refl⟩∘⟨ U.assoc ⟩⊗⟨refl ⟨
        α⇒ U.∘ ((α⇐ U.∘ U.id ⊗₁ copy) U.∘ copy) ⊗₁ U.id               ≈⟨ refl⟩∘⟨ IsMonoid.assoc comonoid ⟩⊗⟨refl ⟨
        α⇒ U.∘ (copy ⊗₁ U.id U.∘ copy) ⊗₁ U.id                        ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
        α⇒ U.∘ (copy ⊗₁ U.id) ⊗₁ U.id U.∘ copy ⊗₁ U.id                ≈⟨ extendʳ assoc-commute-from ⟩
        copy ⊗₁ U.id ⊗₁ U.id U.∘ α⇒ U.∘ copy ⊗₁ U.id                  ≈⟨ refl⟩⊗⟨ ⊗.identity ⟩∘⟨refl ⟩
        copy ⊗₁ U.id U.∘ α⇒ U.∘ copy ⊗₁ U.id                          ∎

    lemma₂ :  copy ⊗₁ U.id U.∘ fₒ ⊗₁ U.id U.≈ (fₒ ⊗₁ fₒ) ⊗₁ U.id U.∘ copy ⊗₁ U.id
    lemma₂ = begin
        copy ⊗₁ U.id U.∘ fₒ ⊗₁ U.id         ≈⟨ merge₁ʳ ⟩
        (copy U.∘ fₒ) ⊗₁ U.id               ≈⟨ μ⇒ ⟩⊗⟨refl ⟩
        (fₒ ⊗₁ fₒ U.∘ copy) ⊗₁ U.id         ≈⟨ split₁ʳ ⟩
        (fₒ ⊗₁ fₒ) ⊗₁ U.id U.∘ copy ⊗₁ U.id ∎

    ≈ᵢ : fᵢ U.∘ U.id ⊗₁ ((gᵢ U.∘ U.id ⊗₁ (hᵢ U.∘ gₒ ⊗₁ U.id) U.∘ α⇒ U.∘ copy ⊗₁ U.id) U.∘ fₒ ⊗₁ U.id) U.∘ α⇒ U.∘ copy ⊗₁ U.id
      U.≈ (fᵢ U.∘ U.id ⊗₁ (gᵢ U.∘ fₒ ⊗₁ U.id) U.∘ α⇒ U.∘ copy ⊗₁ U.id) U.∘ U.id ⊗₁ (hᵢ U.∘ (gₒ U.∘ fₒ) ⊗₁ U.id) U.∘ α⇒ U.∘ copy ⊗₁ U.id
    ≈ᵢ = begin
        fᵢ U.∘ U.id ⊗₁ ((gᵢ U.∘ U.id ⊗₁ term₂ U.∘ α⇒ U.∘ copy ⊗₁ U.id) U.∘ fₒ ⊗₁ U.id) U.∘ α⇒ U.∘ copy ⊗₁ U.id
            ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ extendˡ (extendˡ U.assoc) ⟩∘⟨refl ⟩
        fᵢ U.∘ U.id ⊗₁ ((gᵢ U.∘ U.id ⊗₁ term₂ U.∘ α⇒) U.∘ copy ⊗₁ U.id U.∘ fₒ ⊗₁ U.id) U.∘ α⇒ U.∘ copy ⊗₁ U.id
            ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (refl⟩∘⟨ lemma₂) ⟩∘⟨refl ⟩
        fᵢ U.∘ U.id ⊗₁ ((gᵢ U.∘ U.id ⊗₁ term₂ U.∘ α⇒) U.∘ (fₒ ⊗₁ fₒ) ⊗₁ U.id U.∘ copy ⊗₁ U.id) U.∘ α⇒ U.∘ copy ⊗₁ U.id
            ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ extendˡ U.assoc ⟩∘⟨refl ⟩
        fᵢ U.∘ U.id ⊗₁ ((gᵢ U.∘ U.id ⊗₁ term₂) U.∘ α⇒ U.∘ (fₒ ⊗₁ fₒ) ⊗₁ U.id U.∘ copy ⊗₁ U.id) U.∘ α⇒ U.∘ copy ⊗₁ U.id
            ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (refl⟩∘⟨ extendʳ assoc-commute-from ) ⟩∘⟨refl ⟩
        fᵢ U.∘ U.id ⊗₁ ((gᵢ U.∘ U.id ⊗₁ term₂) U.∘ fₒ ⊗₁ fₒ ⊗₁ U.id U.∘ α⇒ U.∘ copy ⊗₁ U.id) U.∘ α⇒ U.∘ copy ⊗₁ U.id
            ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ U.assoc ⟩∘⟨refl ⟩
        fᵢ U.∘ U.id ⊗₁ (gᵢ U.∘ U.id ⊗₁ term₂ U.∘ fₒ ⊗₁ fₒ ⊗₁ U.id U.∘ α⇒ U.∘ copy ⊗₁ U.id) U.∘ α⇒ U.∘ copy ⊗₁ U.id
            ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (refl⟩∘⟨ pullˡ merge₂ˡ ) ⟩∘⟨refl ⟩
        fᵢ U.∘ U.id ⊗₁ (gᵢ U.∘ fₒ ⊗₁ (term₂ U.∘ fₒ ⊗₁ U.id) U.∘ α⇒ U.∘ copy ⊗₁ U.id) U.∘ α⇒ U.∘ copy ⊗₁ U.id
            ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (refl⟩∘⟨ refl⟩⊗⟨ pullʳ merge₁ʳ ⟩∘⟨refl) ⟩∘⟨refl ⟩
        fᵢ U.∘ U.id ⊗₁ (gᵢ U.∘ fₒ ⊗₁ term₁ U.∘ α⇒ U.∘ copy ⊗₁ U.id) U.∘ α⇒ U.∘ copy ⊗₁ U.id
            ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ U.assoc ⟩∘⟨refl ⟨
        fᵢ U.∘ U.id ⊗₁ ((gᵢ U.∘ fₒ ⊗₁ term₁) U.∘ α⇒ U.∘ copy ⊗₁ U.id) U.∘ α⇒ U.∘ copy ⊗₁ U.id
            ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ extendˡ U.assoc ⟩∘⟨refl ⟨
        fᵢ U.∘ U.id ⊗₁ ((gᵢ U.∘ fₒ ⊗₁ term₁ U.∘ α⇒) U.∘ copy ⊗₁ U.id) U.∘ α⇒ U.∘ copy ⊗₁ U.id
            ≈⟨ refl⟩∘⟨ pushˡ split₂ʳ ⟩
        fᵢ U.∘ U.id ⊗₁ (gᵢ U.∘ fₒ ⊗₁ term₁ U.∘ α⇒) U.∘ U.id ⊗₁ copy ⊗₁ U.id U.∘ α⇒ U.∘ copy ⊗₁ U.id
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟨
        fᵢ U.∘ U.id ⊗₁ (gᵢ U.∘ fₒ ⊗₁ term₁ U.∘ α⇒) U.∘ α⇒ U.∘ (U.id ⊗₁ copy) ⊗₁ U.id U.∘ copy ⊗₁ U.id
            ≈⟨ refl⟩∘⟨ extendʳ (refl⟩⊗⟨ U.assoc ⟩∘⟨refl) ⟨
        fᵢ U.∘ U.id ⊗₁ ((gᵢ U.∘ fₒ ⊗₁ term₁) U.∘ α⇒) U.∘ α⇒ U.∘ (U.id ⊗₁ copy) ⊗₁ U.id U.∘ copy ⊗₁ U.id
            ≈⟨ refl⟩∘⟨ pushˡ split₂ʳ ⟩
        fᵢ U.∘ U.id ⊗₁ (gᵢ U.∘ fₒ ⊗₁ term₁) U.∘ U.id ⊗₁ α⇒ U.∘ α⇒ U.∘ (U.id ⊗₁ copy) ⊗₁ U.id U.∘ copy ⊗₁ U.id
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ insertˡ associator.isoʳ ⟩⊗⟨refl ⟩∘⟨refl ⟩
        fᵢ U.∘ U.id ⊗₁ (gᵢ U.∘ fₒ ⊗₁ term₁) U.∘ U.id ⊗₁ α⇒ U.∘ α⇒ U.∘ (α⇒ U.∘ α⇐ U.∘ U.id ⊗₁ copy) ⊗₁ U.id U.∘ copy ⊗₁ U.id
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₁ʳ ⟩
        fᵢ U.∘ U.id ⊗₁ (gᵢ U.∘ fₒ ⊗₁ term₁) U.∘ U.id ⊗₁ α⇒ U.∘ α⇒ U.∘ α⇒ ⊗₁ U.id U.∘ (α⇐ U.∘ U.id ⊗₁ copy) ⊗₁ U.id U.∘ copy ⊗₁ U.id
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ U.assoc ⟨
        fᵢ U.∘ U.id ⊗₁ (gᵢ U.∘ fₒ ⊗₁ term₁) U.∘ U.id ⊗₁ α⇒ U.∘ (α⇒ U.∘ α⇒ ⊗₁ U.id) U.∘ (α⇐ U.∘ U.id ⊗₁ copy) ⊗₁ U.id U.∘ copy ⊗₁ U.id
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ pentagon ⟩
        fᵢ U.∘ U.id ⊗₁ (gᵢ U.∘ fₒ ⊗₁ term₁) U.∘ α⇒ U.∘ α⇒ U.∘ (α⇐ U.∘ U.id ⊗₁ copy) ⊗₁ U.id U.∘ copy ⊗₁ U.id
            ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ pushʳ serialize₁₂ ⟩∘⟨refl ⟩
        fᵢ U.∘ U.id ⊗₁ (term₃ U.∘ U.id ⊗₁ term₁) U.∘ α⇒ U.∘ α⇒ U.∘ (α⇐ U.∘ U.id ⊗₁ copy) ⊗₁ U.id U.∘ copy ⊗₁ U.id
            ≈⟨ refl⟩∘⟨ pushˡ split₂ʳ ⟩
        fᵢ U.∘ U.id ⊗₁ term₃ U.∘ U.id ⊗₁ U.id ⊗₁ term₁ U.∘ α⇒ U.∘ α⇒ U.∘ (α⇐ U.∘ U.id ⊗₁ copy) ⊗₁ U.id U.∘ copy ⊗₁ U.id
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟨
        fᵢ U.∘ U.id ⊗₁ term₃ U.∘ α⇒ U.∘ (U.id ⊗₁ U.id) ⊗₁ term₁ U.∘ α⇒ U.∘ (α⇐ U.∘ U.id ⊗₁ copy) ⊗₁ U.id U.∘ copy ⊗₁ U.id
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗.identity ⟩⊗⟨refl ⟩∘⟨refl ⟩
        fᵢ U.∘ U.id ⊗₁ term₃ U.∘ α⇒ U.∘ U.id ⊗₁ term₁ U.∘ α⇒ U.∘ (α⇐ U.∘ U.id ⊗₁ copy) ⊗₁ U.id U.∘ copy ⊗₁ U.id
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ lemma₁ ⟩
        fᵢ U.∘ U.id ⊗₁ term₃ U.∘ α⇒ U.∘ U.id ⊗₁ term₁ U.∘ copy ⊗₁ U.id U.∘ α⇒ U.∘ copy ⊗₁ U.id
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (U.Equiv.sym serialize₂₁ ○ serialize₁₂) ⟩
        fᵢ U.∘ U.id ⊗₁ term₃ U.∘ α⇒ U.∘ copy ⊗₁ U.id U.∘ U.id ⊗₁ term₁ U.∘ α⇒ U.∘ copy ⊗₁ U.id
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ U.assoc ⟨
        fᵢ U.∘ U.id ⊗₁ term₃ U.∘ (α⇒ U.∘ copy ⊗₁ U.id) U.∘ U.id ⊗₁ term₁ U.∘ α⇒ U.∘ copy ⊗₁ U.id
            ≈⟨ refl⟩∘⟨ U.assoc ⟨
        fᵢ U.∘ (U.id ⊗₁ term₃ U.∘ α⇒ U.∘ copy ⊗₁ U.id) U.∘ U.id ⊗₁ term₁ U.∘ α⇒ U.∘ copy ⊗₁ U.id
            ≈⟨ U.assoc ⟨
        (fᵢ U.∘ U.id ⊗₁ term₃ U.∘ α⇒ U.∘ copy ⊗₁ U.id) U.∘ U.id ⊗₁ term₁ U.∘ α⇒ U.∘ copy ⊗₁ U.id ∎

identityˡ : {A B : Box} {f : WiringDiagram A B} → id ∘ f ≈ f
identityˡ {Aᵢ □ Aₒ} {Bᵢ □ Bₒ} {fᵢ ⧈ fₒ} = ≈ᵢ ⌸ U.identityˡ
  where
    open ⇒-Reasoning 𝒞
    open ⊗-Reasoning M
    ≈ᵢ : fᵢ U.∘ U.id ⊗₁ ((λ⇒ U.∘ discard ⊗₁ U.id) U.∘ fₒ ⊗₁ U.id) U.∘ α⇒ U.∘ copy ⊗₁ U.id U.≈ fᵢ
    ≈ᵢ = begin
        fᵢ U.∘ U.id ⊗₁ ((λ⇒ U.∘ discard ⊗₁ U.id) U.∘ fₒ ⊗₁ U.id) U.∘ α⇒ U.∘ copy ⊗₁ U.id  ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ pullʳ merge₁ʳ ⟩∘⟨refl ⟩
        fᵢ U.∘ U.id ⊗₁ (λ⇒ U.∘ (discard U.∘ fₒ) ⊗₁ U.id) U.∘ α⇒ U.∘ copy ⊗₁ U.id          ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (refl⟩∘⟨ η⇒ ⟩⊗⟨refl) ⟩∘⟨refl ⟩
        fᵢ U.∘ U.id ⊗₁ (λ⇒ U.∘ discard ⊗₁ U.id) U.∘ α⇒ U.∘ copy ⊗₁ U.id                   ≈⟨ refl⟩∘⟨ pushˡ split₂ʳ ⟩
        fᵢ U.∘ U.id ⊗₁ λ⇒ U.∘ U.id ⊗₁ discard ⊗₁ U.id U.∘ α⇒ U.∘ copy ⊗₁ U.id             ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟨
        fᵢ U.∘ U.id ⊗₁ λ⇒ U.∘ α⇒ U.∘ (U.id ⊗₁ discard) ⊗₁ U.id U.∘ copy ⊗₁ U.id           ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ merge₁ˡ ⟩
        fᵢ U.∘ U.id ⊗₁ λ⇒ U.∘ α⇒ U.∘ (U.id ⊗₁ discard U.∘ copy) ⊗₁ U.id                   ≈⟨ refl⟩∘⟨ pullˡ triangle ⟩
        fᵢ U.∘ ρ⇒ ⊗₁ U.id U.∘ (U.id ⊗₁ discard U.∘ copy) ⊗₁ U.id                          ≈⟨ refl⟩∘⟨ merge₁ʳ ⟩
        fᵢ U.∘ (ρ⇒ U.∘ U.id ⊗₁ discard U.∘ copy) ⊗₁ U.id                                  ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ IsMonoid.identityʳ comonoid) ⟩⊗⟨refl ⟨
        fᵢ U.∘ (ρ⇒ U.∘ ρ⇐) ⊗₁ U.id                                                        ≈⟨ refl⟩∘⟨ unitorʳ.isoʳ ⟩⊗⟨refl  ⟩
        fᵢ U.∘ U.id ⊗₁ U.id                                                               ≈⟨ elimʳ ⊗.identity ⟩
        fᵢ                                                                                ∎

identityʳ : {A B : Box} {f : WiringDiagram A B} → (f ∘ id) ≈ f
identityʳ {Aᵢ □ Aₒ} {Bᵢ □ Bₒ} {fᵢ ⧈ fₒ} = ≈ᵢ ⌸ U.identityʳ
  where
    open ⇒-Reasoning 𝒞
    open ⊗-Reasoning M
    ≈ᵢ : (λ⇒ U.∘ discard ⊗₁ U.id) U.∘ U.id ⊗₁ (fᵢ U.∘ U.id ⊗₁ U.id) U.∘ α⇒ U.∘ copy ⊗₁ U.id U.≈ fᵢ
    ≈ᵢ = begin
        (λ⇒ U.∘ discard ⊗₁ U.id) U.∘ U.id ⊗₁ (fᵢ U.∘ U.id ⊗₁ U.id) U.∘ α⇒ U.∘ copy ⊗₁ U.id  ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ elimʳ ⊗.identity ⟩∘⟨refl ⟩
        (λ⇒ U.∘ discard ⊗₁ U.id) U.∘ U.id ⊗₁ fᵢ U.∘ α⇒ U.∘ copy ⊗₁ U.id                     ≈⟨ pullˡ (pullʳ (U.Equiv.sym serialize₁₂)) ⟩
        (λ⇒ U.∘ discard ⊗₁ fᵢ) U.∘ α⇒ U.∘ copy ⊗₁ U.id                                      ≈⟨ pullʳ (pushˡ serialize₂₁) ⟩
        λ⇒ U.∘ U.id ⊗₁ fᵢ U.∘ discard ⊗₁ U.id U.∘ α⇒ U.∘ copy ⊗₁ U.id                       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ ⊗.identity ⟩∘⟨refl ⟨
        λ⇒ U.∘ U.id ⊗₁ fᵢ U.∘ discard ⊗₁ U.id ⊗₁ U.id U.∘ α⇒ U.∘ copy ⊗₁ U.id               ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟨
        λ⇒ U.∘ U.id ⊗₁ fᵢ U.∘ α⇒ U.∘ (discard ⊗₁ U.id) ⊗₁ U.id U.∘ copy ⊗₁ U.id             ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ merge₁ʳ ⟩
        λ⇒ U.∘ U.id ⊗₁ fᵢ U.∘ α⇒ U.∘ (discard ⊗₁ U.id U.∘ copy) ⊗₁ U.id                     ≈⟨ extendʳ unitorˡ-commute-from ⟩
        fᵢ U.∘ λ⇒ U.∘ α⇒ U.∘ (discard ⊗₁ U.id U.∘ copy) ⊗₁ U.id                             ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ IsMonoid.identityˡ comonoid ⟩⊗⟨refl ⟨
        fᵢ U.∘ λ⇒ U.∘ α⇒ U.∘ λ⇐ ⊗₁ U.id                                                     ≈⟨ refl⟩∘⟨ pullˡ coherence₁ ⟩
        fᵢ U.∘ λ⇒ ⊗₁ U.id U.∘ λ⇐ ⊗₁ U.id                                                    ≈⟨ refl⟩∘⟨ merge₁ʳ ⟩
        fᵢ U.∘ (λ⇒ U.∘ λ⇐) ⊗₁ U.id                                                          ≈⟨ refl⟩∘⟨ unitorˡ.isoʳ ⟩⊗⟨refl ⟩
        fᵢ U.∘ U.id ⊗₁ U.id                                                                 ≈⟨ elimʳ ⊗.identity ⟩
        fᵢ                                                                                  ∎

WD : Category o ℓ e
WD = categoryHelper record
    { Obj = Box
    ; _⇒_ = WiringDiagram
    ; _≈_ = _≈_
    ; id = id
    ; _∘_ = _∘_
    ; assoc = assoc
    ; identityˡ = identityˡ
    ; identityʳ = identityʳ
    ; equiv = ≈-isEquiv
    ; ∘-resp-≈ = ∘-resp-≈
    }
