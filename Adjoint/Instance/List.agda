{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_; suc)

module Adjoint.Instance.List {ℓ : Level} where

import Data.List as L
import Data.List.Relation.Binary.Pointwise as PW

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory; SymmetricMonoidalCategory)
open import Category.Instance.Setoids.SymmetricMonoidal {ℓ} {ℓ} using (Setoids-×)

module S = SymmetricMonoidalCategory Setoids-×

open import Categories.Adjoint using (_⊣_)
open import Categories.Category.Construction.Monoids using (Monoids)
open import Categories.Functor using (Functor; id; _∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.Object.Monoid S.monoidal using (Monoid; IsMonoid; Monoid⇒)
open import Data.Monoid using (toMonoid; toMonoid⇒)
open import Data.Opaque.List using ([-]ₛ; Listₛ; mapₛ; foldₛ; ++ₛ-homo; []ₛ-homo; fold-mapₛ; fold)
open import Data.Product using (_,_; uncurry)
open import Data.Setoid using (∣_∣)
open import Function using (_⟶ₛ_; _⟨$⟩_)
open import Functor.Forgetful.Instance.Monoid {suc ℓ} {ℓ} {ℓ} using () renaming (Forget to Forget′)
open import Functor.Free.Instance.Monoid {ℓ} {ℓ} using (Listₘ; mapₘ; ListMonoid) renaming (Free to Free′)
open import Relation.Binary using (Setoid)

open Monoid
open Monoid⇒

open import Categories.Category using (Category)

Mon[S] : Category (suc ℓ) ℓ ℓ
Mon[S] = Monoids S.monoidal

Free : Functor S.U Mon[S]
Free = Free′

Forget : Functor Mon[S] S.U
Forget = Forget′ S.monoidal

opaque
  unfolding [-]ₛ mapₘ
  map-[-]ₛ
      : {X Y : Setoid ℓ ℓ}
        (f : X ⟶ₛ Y)
        {x : ∣ X ∣}
      → (open Setoid (Listₛ Y))
      → [-]ₛ ⟨$⟩ (f ⟨$⟩ x)
      ≈ arr (mapₘ f) ⟨$⟩ ([-]ₛ ⟨$⟩ x)
  map-[-]ₛ {X} {Y} f {x} = Setoid.refl (Listₛ Y)

unit : NaturalTransformation id (Forget ∘F Free)
unit = ntHelper record
    { η = λ X → [-]ₛ {ℓ} {ℓ} {X}
    ; commute = map-[-]ₛ
    }

opaque
  unfolding toMonoid ListMonoid
  foldₘ : (X : Monoid) → Monoid⇒ (Listₘ (Carrier X)) X
  foldₘ X .arr = foldₛ (toMonoid X)
  foldₘ X .preserves-μ {xs , ys} = ++ₛ-homo (toMonoid X) xs ys
  foldₘ X .preserves-η {_} = []ₛ-homo (toMonoid X)

opaque
  unfolding foldₘ toMonoid⇒ mapₘ
  fold-mapₘ
      : {X Y : Monoid}
        (f : Monoid⇒ X Y)
        {x : ∣ Listₛ (Carrier X) ∣}
      → (open Setoid (Carrier Y))
      → arr (foldₘ Y) ⟨$⟩ (arr (mapₘ (arr f)) ⟨$⟩ x)
      ≈ arr f ⟨$⟩ (arr (foldₘ X) ⟨$⟩ x)
  fold-mapₘ {X} {Y} f = uncurry (fold-mapₛ (toMonoid X) (toMonoid Y)) (toMonoid⇒ X Y f)

counit : NaturalTransformation (Free ∘F Forget) id
counit = ntHelper record
    { η = foldₘ
    ; commute = fold-mapₘ
    }

opaque
  unfolding mapₘ foldₘ fold
  zig : (Aₛ  : Setoid ℓ ℓ)
        {xs : ∣ Listₛ Aₛ ∣}
      → (open Setoid (Listₛ Aₛ))
      → arr (foldₘ (Listₘ Aₛ)) ⟨$⟩ (arr (mapₘ [-]ₛ) ⟨$⟩ xs) ≈ xs
  zig Aₛ {xs = L.[]} = Setoid.refl (Listₛ Aₛ)
  zig Aₛ {xs = x L.∷ xs} = Setoid.refl Aₛ PW.∷ zig Aₛ {xs = xs}

opaque
  unfolding foldₘ fold
  zag : (M : Monoid)
        {x : ∣ Carrier M ∣}
      → (open Setoid (Carrier M))
      → arr (foldₘ M) ⟨$⟩ ([-]ₛ ⟨$⟩ x) ≈ x
  zag M {x} = Setoid.sym (Carrier M) (identityʳ M {x , _})

List⊣ : Free ⊣ Forget
List⊣ = record
    { unit = unit
    ; counit = counit
    ; zig = λ {X} → zig X
    ; zag = λ {M} → zag M
    }
