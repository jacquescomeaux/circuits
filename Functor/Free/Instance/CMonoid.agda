{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)

module Functor.Free.Instance.CMonoid {c ℓ : Level} where

import Categories.Object.Monoid as MonoidObject
import Object.Monoid.Commutative as CMonoidObject

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Category.Construction.CMonoids using (CMonoids)
open import Category.Instance.Setoids.SymmetricMonoidal {c} {c ⊔ ℓ} using (Setoids-×; ×-symmetric′)
open import Data.List.Relation.Binary.Permutation.Setoid.Properties using (++-assoc; ++-identityˡ; ++-identityʳ; ++-comm)
open import Data.Product using (_,_)
open import Data.Setoid using (∣_∣)
open import Data.Opaque.Multiset using ([]ₛ; Multisetₛ; ++ₛ; mapₛ)
open import Function using (_⟶ₛ_; _⟨$⟩_)
open import Functor.Instance.Multiset {c} {ℓ} using (Multiset)
open import NaturalTransformation.Instance.EmptyMultiset {c} {ℓ} using (⊤⇒[])
open import NaturalTransformation.Instance.MultisetAppend {c} {ℓ} using (++)
open import Relation.Binary using (Setoid)

module ++ = NaturalTransformation ++
module ⊤⇒[] = NaturalTransformation ⊤⇒[]

open Functor
open MonoidObject Setoids-×.monoidal using (Monoid; IsMonoid; Monoid⇒)
open CMonoidObject Setoids-×.symmetric using (CommutativeMonoid; IsCommutativeMonoid; CommutativeMonoid⇒)
open IsCommutativeMonoid
open CommutativeMonoid using () renaming (μ to μ′; η to η′)
open IsMonoid
open CommutativeMonoid⇒
open Monoid⇒

module _ (X : Setoid c ℓ) where

  open Setoid (Multiset.₀ X)

  opaque

    unfolding Multisetₛ

    ++ₛ-assoc
        : (x y z : ∣ Multisetₛ X ∣)
        → ++ₛ ⟨$⟩ (++ₛ ⟨$⟩ (x , y) , z)
        ≈ ++ₛ ⟨$⟩ (x , ++ₛ ⟨$⟩ (y , z))
    ++ₛ-assoc x y z = ++-assoc X x y z

    ++ₛ-identityˡ
        : (x : ∣ Multisetₛ X ∣)
        → x ≈ ++ₛ ⟨$⟩ ([]ₛ ⟨$⟩ _ , x)
    ++ₛ-identityˡ x = ++-identityˡ X x

    ++ₛ-identityʳ
        : (x : ∣ Multisetₛ X ∣)
        → x ≈ ++ₛ ⟨$⟩ (x , []ₛ ⟨$⟩ _)
    ++ₛ-identityʳ x = sym (++-identityʳ X x)

    ++ₛ-comm
        : (x y : ∣ Multisetₛ X ∣)
        → ++ₛ ⟨$⟩ (x , y) ≈ ++ₛ ⟨$⟩ (y , x)
    ++ₛ-comm x y = ++-comm X x y

  opaque
    unfolding ×-symmetric′
    MultisetCMonoid : IsCommutativeMonoid (Multiset.₀ X)
    MultisetCMonoid .isMonoid .μ = ++.η X
    MultisetCMonoid .isMonoid .η = ⊤⇒[].η X
    MultisetCMonoid .isMonoid .assoc {(x , y) , z} = ++ₛ-assoc x y z
    MultisetCMonoid .isMonoid .identityˡ {_ , x} = ++ₛ-identityˡ x
    MultisetCMonoid .isMonoid .identityʳ {x , _} = ++ₛ-identityʳ x
    MultisetCMonoid .commutative {x , y} = ++ₛ-comm x y

Multisetₘ : (X : Setoid c ℓ) → CommutativeMonoid
Multisetₘ X = record { isCommutativeMonoid = MultisetCMonoid X }

open Setoids-× using (_⊗₀_; _⊗₁_)
opaque
  unfolding MultisetCMonoid
  mapₛ-++ₛ
      : {A B : Setoid c ℓ}
      → (f : A ⟶ₛ B)
      → {xy : ∣ Multisetₛ A ⊗₀ Multisetₛ A ∣}
      → (open Setoid (Multisetₛ B))
      → mapₛ f ⟨$⟩ (μ′ (Multisetₘ A) ⟨$⟩ xy)
      ≈ μ′ (Multisetₘ B) ⟨$⟩ (mapₛ f ⊗₁ mapₛ f ⟨$⟩ xy)
  mapₛ-++ₛ = ++.sym-commute

opaque
  unfolding MultisetCMonoid mapₛ
  mapₛ-[]ₛ
      : {A B : Setoid c ℓ}
      → (f : A ⟶ₛ B)
      → {x : ∣ Setoids-×.unit ∣}
      → (open Setoid (Multisetₛ B))
      → mapₛ f ⟨$⟩ (η′ (Multisetₘ A) ⟨$⟩ x)
      ≈ η′ (Multisetₘ B) ⟨$⟩ x
  mapₛ-[]ₛ = ⊤⇒[].commute

mapₘ
    : {A B : Setoid c ℓ}
      (f : A ⟶ₛ B)
    → CommutativeMonoid⇒ (Multisetₘ A) (Multisetₘ B)
mapₘ f .monoid⇒ .arr = Multiset.₁ f
mapₘ f .monoid⇒ .preserves-μ = mapₛ-++ₛ f
mapₘ f .monoid⇒ .preserves-η = mapₛ-[]ₛ f

Free : Functor (Setoids c ℓ) (CMonoids Setoids-×.symmetric)
Free .F₀ = Multisetₘ
Free .F₁ = mapₘ
Free .identity {X} = Multiset.identity {X}
Free .homomorphism {X} {Y} {Z} {f} {g} = Multiset.homomorphism {X} {Y} {Z} {f} {g}
Free .F-resp-≈ {A} {B} {f} {g} = Multiset.F-resp-≈ {A} {B} {f} {g}
