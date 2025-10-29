{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)
open import Data.Hypergraph.Label using (HypergraphLabel)

module Data.Hypergraph.Setoid {c ℓ : Level} (HL : HypergraphLabel) where

import Data.List.Relation.Binary.Permutation.Propositional as List-↭

open import Data.Hypergraph.Edge HL using (module Sort)
open import Data.Hypergraph.Base {c} HL using (Hypergraph; normalize)
open import Data.Nat using (ℕ)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

-- an equivalence relation on hypergraphs
record _≈_ {v : ℕ} (H H′ : Hypergraph v) : Set (c ⊔ ℓ) where

  constructor mk≈

  module H = Hypergraph H
  module H′ = Hypergraph H′

  field
    ≡-normalized : normalize H ≡ normalize H′

  open Hypergraph using (edges)

  ≡-edges : edges (normalize H) ≡ edges (normalize H′)
  ≡-edges = ≡.cong edges ≡-normalized

  open List-↭ using (_↭_; ↭-reflexive; ↭-sym; ↭-trans)
  open Sort using (sort-↭)

  ↭-edges : H.edges ↭ H′.edges
  ↭-edges = ↭-trans (↭-sym (sort-↭ H.edges)) (↭-trans (↭-reflexive ≡-edges) (sort-↭ H′.edges))

infixr 4 _≈_

≈-refl : {v : ℕ} {H : Hypergraph v} → H ≈ H
≈-refl = mk≈ ≡.refl

≈-sym : {v : ℕ} {H H′ : Hypergraph v} → H ≈ H′ → H′ ≈ H
≈-sym (mk≈ ≡n) = mk≈ (≡.sym ≡n)

≈-trans : {v : ℕ} {H H′ H″ : Hypergraph v} → H ≈ H′ → H′ ≈ H″ → H ≈ H″
≈-trans (mk≈ ≡n₁) (mk≈ ≡n₂) = mk≈ (≡.trans ≡n₁ ≡n₂)

-- The setoid of labeled hypergraphs with v nodes
Hypergraphₛ : ℕ → Setoid c (c ⊔ ℓ)
Hypergraphₛ v = record
    { Carrier = Hypergraph v
    ; _≈_ = _≈_
    ; isEquivalence = record
        { refl = ≈-refl
        ; sym = ≈-sym
        ; trans = ≈-trans
        }
    }
