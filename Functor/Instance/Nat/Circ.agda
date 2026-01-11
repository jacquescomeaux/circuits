{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module Functor.Instance.Nat.Circ {ℓ : Level} where

import Data.List.Relation.Binary.Permutation.Setoid as ↭

open import Categories.Category.Instance.Nat using (Nat)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Morphism.Notation using (_[_≅_])
open import Category.Instance.Setoids.SymmetricMonoidal {ℓ} {ℓ} using (Setoids-×)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_)
open import Data.Circuit using (mk≈)
open import Data.Circuit {ℓ} using (Circuitₛ; mkCircuitₛ; edgesₛ)
open import Data.Circuit.Gate using (Gates)
open import Data.Nat using (ℕ)
open import Data.Opaque.Multiset using (Multisetₛ)
open import Data.Product using (proj₁; proj₂; Σ-syntax)
open import Functor.Free.Instance.CMonoid using (Free)
open import Functor.Instance.Nat.Edge {ℓ} Gates using (Edge)
open import Functor.Properties using (define-by-pw-iso)

open import Category.Construction.CMonoids Setoids-×.symmetric using (CMonoids)
open import Category.Construction.CMonoids.Properties Setoids-×.symmetric using (transport-by-iso)
open import Object.Monoid.Commutative Setoids-×.symmetric using (CommutativeMonoid)

Edges : Functor Nat CMonoids
Edges = Free ∘F Edge

module Edges = Functor Edges
module Edge = Functor Edge

opaque
  unfolding Multisetₛ
  Edges≅Circₛ : (n : ℕ) → Setoids-×.U [ Multisetₛ (Edge.₀ n) ≅ Circuitₛ n ]
  Edges≅Circₛ n = record
      { from = mkCircuitₛ
      ; to = edgesₛ
      ; iso = record
          { isoˡ = ↭.↭-refl (Edge.₀ n)
          ; isoʳ = mk≈ (↭.↭-refl (Edge.₀ n))
          }
      }

private
  Edges≅ : (n : ℕ) → Σ[ M ∈ CommutativeMonoid ] CMonoids [ Edges.₀ n ≅ M ]
  Edges≅ n = transport-by-iso (Edges.₀ n) (Edges≅Circₛ n)

Circuitₘ : ℕ → CommutativeMonoid
Circuitₘ n = proj₁ (Edges≅ n)

Edges≅Circₘ : (n : ℕ) → CMonoids [ Edges.₀ n ≅ Circuitₘ n ]
Edges≅Circₘ n = proj₂ (Edges≅ n)

Circ : Functor Nat CMonoids
Circ = proj₁ (define-by-pw-iso Edges Circuitₘ Edges≅Circₘ)

Edges≃Circ : Edges ≃ Circ
Edges≃Circ = proj₂ (define-by-pw-iso Edges Circuitₘ Edges≅Circₘ)
