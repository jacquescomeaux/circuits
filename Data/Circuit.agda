{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)

module Data.Circuit {c ℓ : Level} where

import Data.List as List

open import Data.Circuit.Gate using (Gates)

open import Data.Fin using (Fin)
open import Data.Hypergraph {c} {ℓ} Gates
  using
    ( Hypergraph
    ; mkHypergraph
    ; Hypergraphₛ
    ; module Edge
    ; normalize
    ; _≈_
    ; mk≈
    )
open import Data.Nat using (ℕ)
open import Relation.Binary using (Rel; Setoid)
open import Function.Bundles using (Func; _⟶ₛ_)

open List using (List)
open Edge using (Edge; ≈-Edge⇒≡)

Circuit : ℕ → Set c
Circuit = Hypergraph

map : {n m : ℕ} → (Fin n → Fin m) → Circuit n → Circuit m
map f (mkHypergraph edges) = mkHypergraph (List.map (Edge.map f) edges)

Circuitₛ : ℕ → Setoid c (c ⊔ ℓ)
Circuitₛ = Hypergraphₛ

open Func
open Edge.Sort using (sort)

open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭⇒↭ₛ′)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (map⁺)
open import Data.List.Relation.Binary.Pointwise as PW using (Pointwise; Pointwise-≡⇒≡)
open import Data.List.Relation.Binary.Permutation.Homogeneous using (Permutation)

import Data.Permutation.Sort as ↭-Sort

mapₛ : {n m : ℕ} → (Fin n → Fin m) → Circuitₛ n ⟶ₛ Circuitₛ m
mapₛ {n} {m} f .to = map f
mapₛ {n} {m} f .cong {mkHypergraph xs} {mkHypergraph ys} x≈y = mk≈ ≡-norm
  where
    open _≈_ x≈y using (↭-edges)
    open ↭-Sort (Edge.decTotalOrder {m}) using (sorted-≋)
    open import Function.Reasoning
    xs′ ys′ : List (Edge m)
    xs′ = List.map (Edge.map f) xs
    ys′ = List.map (Edge.map f) ys
    ≡-norm : mkHypergraph (sort xs′) ≡ mkHypergraph (sort ys′)
    ≡-norm = ↭-edges                        ∶ xs ↭ ys
        |> map⁺ (Edge.map f)                ∶ xs′ ↭ ys′
        |> ↭⇒↭ₛ′ Edge.≈-Edge-IsEquivalence  ∶ Permutation Edge.≈-Edge xs′ ys′
        |> sorted-≋                         ∶ Pointwise Edge.≈-Edge (sort xs′) (sort ys′)
        |> PW.map ≈-Edge⇒≡                  ∶ Pointwise _≡_ (sort xs′) (sort ys′)
        |> Pointwise-≡⇒≡                    ∶ sort xs′ ≡ sort ys′
        |> ≡.cong mkHypergraph              ∶ mkHypergraph (sort xs′) ≡ mkHypergraph (sort ys′)
