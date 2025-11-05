{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_; 0ℓ)

module Functor.Instance.Nat.Circ {ℓ : Level} where

open import Data.Circuit {ℓ} using (Circuitₛ; mapₛ; mkCircuitₛ)
open import Data.Nat using (ℕ)
open import Relation.Binary using (Setoid)
open import Function using (Func)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Instance.Nat using (Nat)
open import Data.Fin using (Fin)
open import Data.Circuit.Gate using (Gates)
open import Functor.Instance.Nat.Edge {ℓ} Gates using (Edge)
open import Functor.Instance.Multiset using (Multiset)

Multiset∘Edge : Functor Nat (Setoids ℓ ℓ)
Multiset∘Edge = Multiset ∘F Edge

module Multiset∘Edge = Functor Multiset∘Edge

open Func
open Functor

Circ : Functor Nat (Setoids ℓ ℓ)
Circ .F₀ = Circuitₛ
Circ .F₁ = mapₛ
Circ .identity = cong mkCircuitₛ Multiset∘Edge.identity
Circ .homomorphism = cong mkCircuitₛ Multiset∘Edge.homomorphism
Circ .F-resp-≈ f≗g = cong mkCircuitₛ (Multiset∘Edge.F-resp-≈ f≗g)
