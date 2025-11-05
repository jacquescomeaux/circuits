{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module Data.Circuit {ℓ : Level} where

open import Data.Circuit.Gate using (Gates)

import Data.List as List
import Data.Hypergraph {ℓ} Gates as Hypergraph

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.List.Relation.Binary.Permutation.Setoid.Properties using (map⁺)
open import Function using (Func; _⟶ₛ_; _∘_)
open import Relation.Binary using (Setoid)

open Func

open Hypergraph using (Multiset∘Edgeₛ)
open Hypergraph
  using (_≈_ ; mk≈ ; module Edge)
  renaming
    ( Hypergraph to Circuit
    ; Hypergraphₛ to Circuitₛ
    ; mkHypergraph to mkCircuit
    ; mkHypergraphₛ to mkCircuitₛ
    )
  public
open List using ([])

map : {n m : ℕ} → (Fin n → Fin m) → Circuit n → Circuit m
map f (mkCircuit edges) = mkCircuit (List.map (Edge.map f) edges)

discrete : (n : ℕ) → Circuit n
discrete n = mkCircuit []

open Edge using (Edgeₛ)

mapₛ : {n m : ℕ} → (Fin n → Fin m) → Circuitₛ n ⟶ₛ Circuitₛ m
mapₛ f .to = map f
mapₛ {n} {m} f .cong (mk≈ x≈y) = mk≈ (map⁺ (Edgeₛ n) (Edgeₛ m) (cong (Edge.mapₛ f)) x≈y)
