{-# OPTIONS --without-K --safe #-}

module NaturalTransformation.Instance.CircuitSemantics where

open import Level using (0ℓ; suc)
open import Category.Instance.Setoids.SymmetricMonoidal {suc 0ℓ} {suc 0ℓ} using (Setoids-×)

import Functor.Forgetful.Instance.CMonoid Setoids-×.symmetric as CMonoid
import Functor.Forgetful.Instance.Monoid Setoids-×.monoidal as Monoid

open import Adjoint.Instance.Multiset {suc 0ℓ} using (Multiset⊣; Forget)
open import Categories.Adjoint using (Adjoint)
open import Categories.Category.Instance.Nat using (Nat-Cocartesian)
open import Categories.Functor using () renaming (_∘F_ to _∙_; id to Id)
open import Categories.Functor.Monoidal.Symmetric using () renaming (module Lax to Lax₁)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ˡ_; _∘ʳ_; _∘ᵥ_; id∘F⇒F)
open import Categories.NaturalTransformation.Monoidal.Symmetric using () renaming (module Lax to Lax₂)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)
open import Categories.NaturalTransformation.NaturalIsomorphism using (associator)
open import Category.Monoidal.Instance.Nat using (Nat,+,0)
open import Data.Circuit.Gate using (Gates)
open import Functor.Free.Instance.CMonoid using (Free)
open import Functor.Instance.CMonoidalize Nat-Cocartesian Setoids-× using (CMonoidalize)
open import Functor.Instance.Nat.Circ {suc 0ℓ} using (Circ; Edges≃Circ)
open import Functor.Instance.Nat.Edge {suc 0ℓ} Gates using (Edge)
open import Functor.Instance.Nat.System using (module NatCMon)
open import NaturalTransformation.Instance.GateSemantics using (semantics)

open Lax₁ using (SymmetricMonoidalFunctor)
open Lax₂ using (SymmetricMonoidalNaturalTransformation)
open NatCMon using (Sys)
open Adjoint Multiset⊣ using (counit)

module assoc = NaturalIsomorphism (associator Sys Forget Free)
module Edges≃Circ = NaturalIsomorphism Edges≃Circ

circuitSemantics : NaturalTransformation Circ Sys
circuitSemantics = id∘F⇒F ∘ᵥ (counit ∘ʳ Sys) ∘ᵥ assoc.F⇐G ∘ᵥ (Free ∘ˡ semantics) ∘ᵥ Edges≃Circ.F⇐G

Circ-SMF : SymmetricMonoidalFunctor Nat,+,0 Setoids-×
Circ-SMF = CMonoidalize.₀ Circ

Sys-SMF : SymmetricMonoidalFunctor Nat,+,0 Setoids-×
Sys-SMF = CMonoidalize.₀ Sys

semantics-SM : SymmetricMonoidalNaturalTransformation Circ-SMF Sys-SMF
semantics-SM = CMonoidalize.₁ circuitSemantics
