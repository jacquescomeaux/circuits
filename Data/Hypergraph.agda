{-# OPTIONS --without-K --safe #-}

open import Data.Hypergraph.Label using (HypergraphLabel)
open import Level using (Level; 0ℓ)

module Data.Hypergraph {ℓ : Level} (HL : HypergraphLabel) where

import Data.List.Relation.Binary.Pointwise as PW
import Function.Reasoning as →-Reasoning
import Relation.Binary.PropositionalEquality as ≡
import Data.Hypergraph.Edge {ℓ} HL as Hyperedge
import Data.List.Relation.Binary.Permutation.Propositional as List-↭
import Data.List.Relation.Binary.Permutation.Setoid as ↭

open HypergraphLabel HL using (Label) public

open import Data.List using (List; map)
open import Data.Nat using (ℕ)
open import Data.String using (String; unlines)
open import Function using (_∘_; _⟶ₛ_; Func)
open import Relation.Binary using (Setoid)

module Edge = Hyperedge
open Edge using (Edge; Edgeₛ)

-- A hypergraph is a list of edges
record Hypergraph (v : ℕ) : Set ℓ where
  constructor mkHypergraph
  field
    edges : List (Edge v)

module _ {v : ℕ} where

  open ↭ (Edgeₛ v) using (_↭_; ↭-refl; ↭-sym; ↭-trans)

  show : Hypergraph v → String
  show (mkHypergraph e) = unlines (map Edge.show e)

  -- an equivalence relation on hypergraphs
  record _≈_ (H H′ : Hypergraph v) : Set ℓ where

    constructor mk≈

    module H = Hypergraph H
    module H′ = Hypergraph H′

    field
      ↭-edges : H.edges ↭ H′.edges

  infixr 4 _≈_

  ≈-refl : {H : Hypergraph v} → H ≈ H
  ≈-refl = mk≈ ↭-refl

  ≈-sym : {H H′ : Hypergraph v} → H ≈ H′ → H′ ≈ H
  ≈-sym (mk≈ ≡n) = mk≈ (↭-sym ≡n)

  ≈-trans : {H H′ H″ : Hypergraph v} → H ≈ H′ → H′ ≈ H″ → H ≈ H″
  ≈-trans (mk≈ ≡n₁) (mk≈ ≡n₂) = mk≈ (↭-trans ≡n₁ ≡n₂)

-- The setoid of labeled hypergraphs with v nodes
Hypergraphₛ : ℕ → Setoid ℓ ℓ
Hypergraphₛ v = record
    { Carrier = Hypergraph v
    ; _≈_ = _≈_
    ; isEquivalence = record
        { refl = ≈-refl
        ; sym = ≈-sym
        ; trans = ≈-trans
        }
    }

open Func

open ↭ using (↭-setoid)

Multiset∘Edgeₛ : (n : ℕ) → Setoid ℓ ℓ
Multiset∘Edgeₛ = ↭-setoid ∘ Edgeₛ

mkHypergraphₛ : {n : ℕ} → Multiset∘Edgeₛ n ⟶ₛ Hypergraphₛ n
mkHypergraphₛ .to = mkHypergraph
mkHypergraphₛ .cong = mk≈

edgesₛ : {n : ℕ} → Hypergraphₛ n ⟶ₛ Multiset∘Edgeₛ n
edgesₛ .to = Hypergraph.edges
edgesₛ .cong = _≈_.↭-edges
