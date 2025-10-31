{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

open import Data.Hypergraph.Label using (HypergraphLabel)

module Data.Hypergraph {c ℓ : Level} (HL : HypergraphLabel) where

import Data.List.Relation.Binary.Pointwise as PW
import Data.Hypergraph.Edge HL as HypergraphEdge
import Function.Reasoning as →-Reasoning
import Relation.Binary.PropositionalEquality as ≡

open import Data.Hypergraph.Base {c} HL public
open import Data.Hypergraph.Setoid {c} {ℓ} HL public
open import Data.Nat using (ℕ)
open import Function using (_∘_; _⟶ₛ_; Func)
open import Level using (0ℓ)
open import Relation.Binary using (Setoid)

module Edge = HypergraphEdge

open Edge using (Edgeₛ; ≈-Edge⇒≡)
open Func

List∘Edgeₛ : (n : ℕ) → Setoid 0ℓ 0ℓ
List∘Edgeₛ = PW.setoid ∘ Edgeₛ

mkHypergraphₛ : {n : ℕ} → List∘Edgeₛ n ⟶ₛ Hypergraphₛ n
mkHypergraphₛ .to = mkHypergraph
mkHypergraphₛ {n} .cong ≋-edges = ≋-edges
    |> PW.map ≈-Edge⇒≡
    |> PW.Pointwise-≡⇒≡
    |> ≡.cong mkHypergraph
    |> Setoid.reflexive (Hypergraphₛ n)
  where
    open →-Reasoning
