{-# OPTIONS --without-K --safe #-}

open import Data.Hypergraph.Label using (HypergraphLabel)

module Data.Hypergraph.Setoid (HL : HypergraphLabel) where

open import Data.Hypergraph.Edge HL using (decTotalOrder)
open import Data.Hypergraph.Base HL using (Hypergraph; sortHypergraph)
open import Data.Nat.Base using (ℕ)
open import Level using (0ℓ)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

record ≈-Hypergraph {v : ℕ} (H H′ : Hypergraph v) : Set where
  module H = Hypergraph H
  module H′ = Hypergraph H′
  field
    ≡sorted : sortHypergraph H ≡ sortHypergraph H′
  open Hypergraph using (edges)
  ≡edges : edges (sortHypergraph H) ≡ edges (sortHypergraph H′)
  ≡edges = ≡.cong edges ≡sorted
  open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-reflexive; ↭-sym; ↭-trans)
  open import Data.List.Sort decTotalOrder using (sort-↭)
  ↭edges : H.edges ↭ H′.edges
  ↭edges = ↭-trans (↭-sym (sort-↭ H.edges)) (↭-trans (↭-reflexive ≡edges) (sort-↭ H′.edges))

≈-refl : {v : ℕ} {H : Hypergraph v} → ≈-Hypergraph H H
≈-refl = record { ≡sorted = ≡.refl }

≈-sym : {v : ℕ} {H H′ : Hypergraph v} → ≈-Hypergraph H H′ → ≈-Hypergraph H′ H
≈-sym ≈H = record { ≡sorted = ≡.sym ≡sorted }
  where
    open ≈-Hypergraph ≈H 

≈-trans : {v : ℕ} {H H′ H″ : Hypergraph v} → ≈-Hypergraph H H′ → ≈-Hypergraph H′ H″ → ≈-Hypergraph H H″
≈-trans ≈H₁ ≈H₂ = record { ≡sorted = ≡.trans ≈H₁.≡sorted ≈H₂.≡sorted }
  where
    module ≈H₁ = ≈-Hypergraph ≈H₁
    module ≈H₂ = ≈-Hypergraph ≈H₂

Hypergraph-Setoid : (v : ℕ) → Setoid 0ℓ 0ℓ
Hypergraph-Setoid v = record
    { Carrier = Hypergraph v
    ; _≈_ = ≈-Hypergraph
    ; isEquivalence = record
        { refl = ≈-refl
        ; sym = ≈-sym
        ; trans = ≈-trans
        }
    }
