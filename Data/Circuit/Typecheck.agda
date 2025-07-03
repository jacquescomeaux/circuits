{-# OPTIONS --without-K --safe #-}

module Data.Circuit.Typecheck where

open import Data.SExp using (SExp)
open import Data.Hypergraph.Base using (HypergraphLabel; module Edge; module HypergraphList)
open import Data.Circuit.Gate using (GateLabel; Gate)
open Edge GateLabel using (Edge)
open HypergraphList GateLabel using (Hypergraph)

open import Data.List using (List; length) renaming (map to mapL)
open import Data.List.Effectful using () renaming (module TraversableA to ListTraversable)
open import Data.Maybe using (Maybe) renaming (map to mapM)
open import Data.Nat using (ℕ; _<?_; _≟_)
open import Data.String using (String)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Vec using (Vec; []; _∷_; fromList) renaming (map to mapV)
open import Data.Vec.Effectful using () renaming (module TraversableA to VecTraversable)
open import Data.Maybe.Effectful using (applicative)
open import Data.Fin using (Fin; #_; fromℕ<)
open import Level using (0ℓ)

import Relation.Binary.PropositionalEquality as ≡

open List
open SExp
open Gate
open Maybe

gate : {n a : ℕ} (g : Gate a) → Vec (Fin n) a → Edge n
gate g p = record { label = g; ports = p }

typeCheckGateLabel : SExp → Maybe (Σ ℕ Gate)
typeCheckGateLabel (Atom "one")  = just (1 , ONE)
typeCheckGateLabel (Atom "zero") = just (1 , ZERO)
typeCheckGateLabel (Atom "not")  = just (2 , NOT)
typeCheckGateLabel (Atom "id")   = just (2 , ID)
typeCheckGateLabel (Atom "and")  = just (3 , AND)
typeCheckGateLabel (Atom "or")   = just (3 , OR)
typeCheckGateLabel (Atom "xor")  = just (3 , XOR)
typeCheckGateLabel (Atom "nand") = just (3 , NAND)
typeCheckGateLabel (Atom "nor")  = just (3 , NOR)
typeCheckGateLabel (Atom "xnor") = just (3 , XNOR)
typeCheckGateLabel _ = nothing

open import Relation.Nullary.Decidable using (Dec; yes; no)
open Dec
open VecTraversable {0ℓ} applicative using () renaming (sequenceA to vecSequenceA)
open ListTraversable {0ℓ} applicative using () renaming (sequenceA to listSequenceA)

typeCheckPort : (v : ℕ) → SExp → Maybe (Fin v)
typeCheckPort v (Nat n) with n <? v
... | yes n<v = just (fromℕ< n<v)
... | no _ = nothing
typeCheckPort _ _ = nothing

typeCheckPorts : (v n : ℕ) → List SExp → Maybe (Vec (Fin v) n)
typeCheckPorts v n xs with length xs ≟ n
... | yes ≡.refl = vecSequenceA (mapV (typeCheckPort v) (fromList xs))
... | no _ = nothing

typeCheckGate : (v : ℕ) → SExp → Maybe (Edge v)
typeCheckGate v (SExps (labelString ∷ ports)) with typeCheckGateLabel labelString
... | just (n , label) = mapM (gate label) (typeCheckPorts v n ports)
... | nothing = nothing
typeCheckGate v _ = nothing

typeCheckHeader : SExp → Maybe ℕ
typeCheckHeader (SExps (Atom "hypergraph" ∷ Nat n ∷ [])) = just n
typeCheckHeader _ = nothing

typeCheckHypergraph : SExp → Maybe (Σ ℕ Hypergraph)
typeCheckHypergraph (SExps (x ∷ xs)) with typeCheckHeader x
... | nothing = nothing
... | just n with listSequenceA (mapL (typeCheckGate n) xs)
...   | just e = just (n , record { edges = e })
...   | nothing = nothing
typeCheckHypergraph _ = nothing
