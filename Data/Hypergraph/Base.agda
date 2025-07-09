{-# OPTIONS --without-K --safe #-}

open import Data.Hypergraph.Label using (HypergraphLabel)

module Data.Hypergraph.Base (HL : HypergraphLabel) where

open import Data.Hypergraph.Edge HL using (Edge; decTotalOrder; showEdge)
open import Data.List.Base using (List; map)
open import Data.Nat.Base using (ℕ)
open import Data.String using (String; unlines)

import Data.List.Sort.MergeSort as MergeSort

record Hypergraph (v : ℕ) : Set where
  field
    edges : List (Edge v)

sortHypergraph : {v : ℕ} → Hypergraph v → Hypergraph v
sortHypergraph {v} H = record { edges = sort edges }
  where
    open Hypergraph H
    open MergeSort decTotalOrder using (sort)

showHypergraph : {v : ℕ} → Hypergraph v → String
showHypergraph record { edges = e} = unlines (map showEdge e)
