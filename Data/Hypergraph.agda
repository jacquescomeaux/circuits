{-# OPTIONS --without-K --safe #-}

open import Level using (Level; 0ℓ)
open import Data.Hypergraph.Label using (HypergraphLabel)

module Data.Hypergraph {c ℓ : Level} (HL : HypergraphLabel) where

import Data.List.Relation.Binary.Pointwise as PW
import Function.Reasoning as →-Reasoning
import Relation.Binary.PropositionalEquality as ≡
import Data.Hypergraph.Edge HL as Hyperedge
import Data.List.Relation.Binary.Permutation.Propositional as List-↭

open import Data.List using (List; map)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-refl; ↭-sym; ↭-trans)
open import Data.Nat using (ℕ)
open import Data.String using (String; unlines)
open import Function using (_∘_; _⟶ₛ_; Func)
open import Relation.Binary using (Setoid)

module Edge = Hyperedge
open Edge using (Edge; Edgeₛ)

-- A hypergraph is a list of edges
record Hypergraph (v : ℕ) : Set c where
  constructor mkHypergraph
  field
    edges : List (Edge v)

module _ {v : ℕ} where

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
Hypergraphₛ : ℕ → Setoid c ℓ
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

List∘Edgeₛ : (n : ℕ) → Setoid 0ℓ 0ℓ
List∘Edgeₛ = PW.setoid ∘ Edgeₛ

mkHypergraphₛ : {n : ℕ} → List∘Edgeₛ n ⟶ₛ Hypergraphₛ n
mkHypergraphₛ .to = mkHypergraph
mkHypergraphₛ {n} .cong ≋-edges = ≋-edges
    |> PW.map Edge.≈⇒≡
    |> PW.Pointwise-≡⇒≡
    |> ≡.cong mkHypergraph
    |> Setoid.reflexive (Hypergraphₛ n)
  where
    open →-Reasoning
