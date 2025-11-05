{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)

module Functor.Instance.FreeCMonoid {c ℓ : Level} where

import Categories.Object.Monoid as MonoidObject
import Object.Monoid.Commutative as CMonoidObject

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Category.Construction.CMonoids using (CMonoids)
open import Category.Instance.Setoids.SymmetricMonoidal {c} {c ⊔ ℓ} using (Setoids-×)
open import Data.List.Relation.Binary.Permutation.Setoid.Properties using (++-assoc; ++-identityˡ; ++-identityʳ; ++-comm)
open import Data.Product using (_,_)
open import Function using (_⟶ₛ_)
open import Functor.Instance.Multiset {c} {ℓ} using (Multiset)
open import NaturalTransformation.Instance.EmptyMultiset {c} {ℓ} using (⊤⇒[])
open import NaturalTransformation.Instance.MultisetAppend {c} {ℓ} using (++)
open import Relation.Binary using (Setoid)

module Multiset = Functor Multiset
module Setoids-× = SymmetricMonoidalCategory Setoids-×
module ++ = NaturalTransformation ++
module ⊤⇒[] = NaturalTransformation ⊤⇒[]

open Functor
open MonoidObject Setoids-×.monoidal using (Monoid; IsMonoid; Monoid⇒)
open CMonoidObject Setoids-×.symmetric using (CommutativeMonoid; IsCommutativeMonoid; CommutativeMonoid⇒)
open IsCommutativeMonoid
open IsMonoid
open CommutativeMonoid⇒
open Monoid⇒

module _ (X : Setoid c ℓ) where

  private
    module X = Setoid X
    module MultisetX = Setoid (Multiset.₀ X)

  MultisetCMonoid : IsCommutativeMonoid (Multiset.₀ X)
  MultisetCMonoid .isMonoid .μ = ++.η X
  MultisetCMonoid .isMonoid .η = ⊤⇒[].η X
  MultisetCMonoid .isMonoid .assoc {(x , y) , z} = ++-assoc X x y z
  MultisetCMonoid .isMonoid .identityˡ {_ , x} = ++-identityˡ X x
  MultisetCMonoid .isMonoid .identityʳ {x , _} = MultisetX.sym (++-identityʳ X x)
  MultisetCMonoid .commutative {x , y} = ++-comm X x y

FreeCMonoid₀ : (X : Setoid c ℓ) → CommutativeMonoid
FreeCMonoid₀ X = record { isCommutativeMonoid = MultisetCMonoid X }

FreeCMonoid₁
    : {A B : Setoid c ℓ}
      (f : A ⟶ₛ B)
    → CommutativeMonoid⇒ (FreeCMonoid₀ A) (FreeCMonoid₀ B)
FreeCMonoid₁ f .monoid⇒ .arr = Multiset.₁ f
FreeCMonoid₁ f .monoid⇒ .preserves-μ {xy} = ++.sym-commute f {xy}
FreeCMonoid₁ f .monoid⇒ .preserves-η = ⊤⇒[].commute f

FreeCMonoid : Functor (Setoids c ℓ) (CMonoids Setoids-×.symmetric)
FreeCMonoid .F₀ = FreeCMonoid₀
FreeCMonoid .F₁ = FreeCMonoid₁
FreeCMonoid .identity {X} = Multiset.identity {X}
FreeCMonoid .homomorphism {X} {Y} {Z} {f} {g} = Multiset.homomorphism {X} {Y} {Z} {f} {g}
FreeCMonoid .F-resp-≈ {A} {B} {f} {g} = Multiset.F-resp-≈ {A} {B} {f} {g}
