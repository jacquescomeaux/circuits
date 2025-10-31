{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_; 0ℓ)

module Functor.Instance.Nat.Circ {c ℓ : Level} where

open import Data.Circuit {c} {ℓ} using (Circuitₛ; mapₛ; mkCircuitₛ)
open import Data.Nat using (ℕ)
open import Relation.Binary using (Setoid)
open import Function using (Func)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Instance.Nat using (Nat)
open import Data.Fin using (Fin)
open import Data.Circuit.Gate using (Gates)
open import Functor.Instance.Nat.Edge Gates using (Edge)
open import Functor.Instance.List using (List)

List∘Edge : Functor Nat (Setoids 0ℓ 0ℓ)
List∘Edge = List ∘F Edge

module List∘Edge = Functor List∘Edge

open Func
open Functor

Circ : Functor Nat (Setoids c (c ⊔ ℓ))
Circ .F₀ = Circuitₛ
Circ .F₁ = mapₛ
Circ .identity = cong mkCircuitₛ List∘Edge.identity
Circ .homomorphism = cong mkCircuitₛ List∘Edge.homomorphism
Circ .F-resp-≈ f≗g = cong mkCircuitₛ (List∘Edge.F-resp-≈ f≗g)
