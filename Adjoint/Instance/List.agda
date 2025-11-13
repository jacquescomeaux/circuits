{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_; suc; 0ℓ)

module Adjoint.Instance.List {c ℓ : Level} where

import Data.List as L
import Data.List.Relation.Binary.Pointwise as PW

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory; SymmetricMonoidalCategory)
open import Category.Instance.Setoids.SymmetricMonoidal using (Setoids-×)

module S = SymmetricMonoidalCategory (Setoids-× {c ⊔ ℓ} {c ⊔ ℓ})

open import Categories.Adjoint using (_⊣_)
open import Categories.Category.Construction.Monoids using (Monoids)
open import Categories.Functor using (Functor; id; _∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.Object.Monoid S.monoidal using (Monoid; Monoid⇒)
open import Data.Monoid using (toMonoid; toMonoid⇒)
open import Data.Opaque.List using ([-]ₛ; Listₛ; mapₛ; foldₛ; ++ₛ; ++ₛ-homo; []ₛ-homo; fold-mapₛ; fold)
open import Data.Product using (_,_; uncurry)
open import Data.Setoid using (∣_∣)
open import Function using (_⟶ₛ_; _⟨$⟩_)
open import Functor.Forgetful.Instance.Monoid {suc (c ⊔ ℓ)} {c ⊔ ℓ} {c ⊔ ℓ} using (Forget)
open import Functor.Free.Instance.Monoid {c ⊔ ℓ} {c ⊔ ℓ} using (Free; Listₘ)
open import Relation.Binary using (Setoid)

open Monoid
open Monoid⇒

S-mc : MonoidalCategory (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
S-mc = record { monoidal = S.monoidal }

opaque

  unfolding [-]ₛ
  unfolding fold

  map-[-]ₛ
      : {X Y : Setoid (c ⊔ ℓ) (c ⊔ ℓ)}
      → (f : X ⟶ₛ Y)
      → (open Setoid (Listₛ Y))
      → {x : ∣ X ∣}
      → [-]ₛ ⟨$⟩ (f ⟨$⟩ x)
      ≈ mapₛ f ⟨$⟩ ([-]ₛ ⟨$⟩ x)
  map-[-]ₛ {X} {Y} f {x} = Setoid.refl (Listₛ Y)

  zig
      : (Aₛ  : Setoid (c ⊔ ℓ) (c ⊔ ℓ))
        {xs : ∣ Listₛ Aₛ ∣}
      → (open Setoid (Listₛ Aₛ))
      → foldₛ (toMonoid (Listₘ Aₛ)) ⟨$⟩ (mapₛ [-]ₛ ⟨$⟩ xs) ≈ xs
  zig Aₛ {xs = L.[]} = Setoid.refl (Listₛ Aₛ)
  zig Aₛ {xs = x L.∷ xs} = Setoid.refl Aₛ PW.∷ zig Aₛ {xs = xs}

  zag
      : (M : Monoid)
        {x : ∣ Carrier M ∣}
      → (open Setoid (Carrier M))
      → fold (toMonoid M) ([-]ₛ ⟨$⟩ x) ≈ x
  zag M {x} = Setoid.sym (Carrier M) (identityʳ M {x , _})

unit : NaturalTransformation id (Forget S-mc ∘F Free)
unit = ntHelper record
    { η = λ X → [-]ₛ {c ⊔ ℓ} {c ⊔ ℓ} {X}
    ; commute = map-[-]ₛ
   }

foldₘ : (X : Monoid) → Monoid⇒ (Listₘ (Carrier X)) X
foldₘ X .arr = foldₛ (toMonoid X)
foldₘ X .preserves-μ {xs , ys} = ++ₛ-homo (toMonoid X) xs ys
foldₘ X .preserves-η {_} = []ₛ-homo (toMonoid X)

counit : NaturalTransformation (Free ∘F Forget S-mc) id
counit = ntHelper record
    { η = foldₘ
    ; commute = λ {X} {Y} f → uncurry (fold-mapₛ (toMonoid X) (toMonoid Y)) (toMonoid⇒ X Y f)
    }

List⊣ : Free ⊣ Forget S-mc
List⊣ = record
    { unit = unit
    ; counit = counit
    ; zig = λ {X} → zig X
    ; zag = λ {M} → zag M
    }
