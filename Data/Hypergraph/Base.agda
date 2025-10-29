{-# OPTIONS --without-K --safe #-}

open import Level using (Level)
open import Data.Hypergraph.Label using (HypergraphLabel)

module Data.Hypergraph.Base {ℓ : Level} (HL : HypergraphLabel) where

import Data.Hypergraph.Edge HL as Edge

open import Data.List using (List; map)
open import Data.Nat.Base using (ℕ)
open import Data.String using (String; unlines)

open Edge using (Edge)

record Hypergraph (v : ℕ) : Set ℓ where
  constructor mkHypergraph
  field
    edges : List (Edge v)

normalize : {v : ℕ} → Hypergraph v → Hypergraph v
normalize (mkHypergraph e) = mkHypergraph (Edge.sort e)

show : {v : ℕ} → Hypergraph v → String
show (mkHypergraph e) = unlines (map Edge.show e)
