{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

open import Data.Hypergraph.Label using (HypergraphLabel)

module Data.Hypergraph {c ℓ : Level} (HL : HypergraphLabel) where

open import Data.Hypergraph.Base {c} HL public
open import Data.Hypergraph.Setoid {c} {ℓ} HL public

import Data.Hypergraph.Edge HL as HypergraphEdge

module Edge = HypergraphEdge
