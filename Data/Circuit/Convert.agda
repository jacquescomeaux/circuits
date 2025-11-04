{-# OPTIONS --without-K --safe #-}

module Data.Circuit.Convert where

open import Level using (0ℓ)

import Data.Vec as Vec
import Data.Vec.Relation.Binary.Equality.Cast as VecCast
import Data.List.Relation.Binary.Permutation.Propositional as L
import Data.Vec.Functional.Relation.Binary.Permutation as V
import DecorationFunctor.Hypergraph.Labeled {0ℓ} {0ℓ} as LabeledHypergraph

open import Data.Nat.Base using (ℕ)
open import Data.Circuit.Gate using (Gate; Gates; cast-gate; cast-gate-is-id; subst-is-cast-gate)
open import Data.Circuit {0ℓ} {0ℓ} using (Circuit; Circuitₛ; _≈_; mkCircuit; module Edge; mk≈)
open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (_,_)
open import Data.Permutation using (fromList-↭; toList-↭)
open import Data.List using (length)
open import Data.Vec.Functional using (toVec; fromVec; toList; fromList)
open import Function.Bundles using (Equivalence; _↔_)
open import Function.Base using (_∘_; id)
open import Data.Vec.Properties using (tabulate-cong; tabulate-∘; map-cast)
open import Data.Fin.Base using () renaming (cast to fincast)
open import Data.Fin.Properties using () renaming (cast-trans to fincast-trans; cast-is-id to fincast-is-id)
open import Data.List.Relation.Binary.Permutation.Homogeneous using (Permutation)
open import Data.Product.Base using (proj₁; proj₂; _×_)
open import Data.Fin.Permutation using (flip; _⟨$⟩ˡ_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_)

open LabeledHypergraph using (Hypergraph-same) renaming (Hypergraph to Hypergraph′; Hypergraph-setoid to Hypergraph-Setoid′)

to : {v : ℕ} → Circuit v → Hypergraph′ v
to C = record
    { h = length edges
    ; a = arity ∘ fromList edges
    ; j = fromVec ∘ ports ∘ fromList edges
    ; l = label ∘ fromList edges
    }
  where
    open Edge.Edge using (arity; ports; label)
    open Circuit C

from : {v : ℕ} → Hypergraph′ v → Circuit v
from {v} H = record
    { edges = toList asEdge
    }
  where
    open Hypergraph′ H
    asEdge : Fin h → Edge.Edge v
    asEdge e = record { label = l e ; ports = toVec (j e) }

to-cong : {v : ℕ} {H H′ : Circuit v} → H ≈ H′ → Hypergraph-same (to H) (to H′)
to-cong {v} {H} {H′} ≈H = record
    { ↔h = flip ρ
    ; ≗a = ≗a
    ; ≗j = ≗j
    ; ≗l = ≗l
    }
  where
    open Edge.Edge using (arity; ports; label)
    open _≈_ ≈H
    open import Data.Fin.Permutation using (_⟨$⟩ʳ_; _⟨$⟩ˡ_; Permutation′; inverseʳ)
    open import Data.Fin.Base using (cast)
    open import Data.Fin.Properties using (cast-is-id)
    ρ : Fin (length H′.edges) ↔ Fin (length H.edges)
    ρ = proj₁ (fromList-↭ ↭-edges)

    open ≡.≡-Reasoning
    edges≗ρ∘edges′ : (i : Fin (length H.edges)) → fromList H.edges i ≡ fromList H′.edges (ρ ⟨$⟩ˡ i)
    edges≗ρ∘edges′ i = begin
        fromList H.edges i                    ≡⟨ ≡.cong (fromList H.edges) (inverseʳ ρ) ⟨
        fromList H.edges (ρ ⟨$⟩ʳ (ρ ⟨$⟩ˡ i))  ≡⟨ proj₂ (fromList-↭ ↭-edges) (ρ ⟨$⟩ˡ i) ⟩
        fromList H′.edges (ρ ⟨$⟩ˡ i)          ∎

    ≗a : (e : Fin (Hypergraph′.h (to H)))
        → Hypergraph′.a (to H) e
        ≡ arity (fromList H′.edges (ρ ⟨$⟩ˡ e))
    ≗a = ≡.cong arity ∘ edges≗ρ∘edges′

    ≗j : (e : Fin (Hypergraph′.h (to H)))
          (i : Fin (Hypergraph′.a (to H) e))
        → fromVec (ports (fromList H.edges e)) i
        ≡ fromVec (ports (fromList H′.edges (ρ ⟨$⟩ˡ e))) (cast (≗a e) i)
    ≗j e i
      rewrite edges≗ρ∘edges′ e
      rewrite cast-is-id ≡.refl i = ≡.refl

    ≗l : (e : Fin (Hypergraph′.h (to H)))
        → label (fromList H.edges e)
        ≡ cast-gate (≡.sym (≗a e)) (label (fromList H′.edges (ρ ⟨$⟩ˡ e)))
    ≗l e
      rewrite edges≗ρ∘edges′ e
      rewrite cast-gate-is-id ≡.refl (label (fromList H′.edges (ρ ⟨$⟩ˡ e))) =
          ≡.refl

module _ {v : ℕ} where
  open import Data.Hypergraph.Label using (HypergraphLabel)
  open HypergraphLabel Gates using (isCastable)
  open import Data.Castable using (IsCastable)
  open IsCastable isCastable using (≈-reflexive; ≈-sym; ≈-trans)
  from-cong
      : {H H′ : Hypergraph′ v}
      → Hypergraph-same H H′
      → from H ≈ from H′
  from-cong {H} {H′} ≈H = mk≈ (toList-↭ (flip ↔h , H∘ρ≗H′))
    where
 
      module H = Hypergraph′ H
      module H′ = Hypergraph′ H′
      open Hypergraph′
      open Hypergraph-same ≈H using (↔h; ≗a; ≗l; ≗j; inverseˡ) renaming (from to f; to to t)
      asEdge : (H : Hypergraph′ v) → Fin (h H) → Edge.Edge v
      asEdge H e = record { label = l H e ; ports = toVec (j H e) }

      to-from : (e : Fin H′.h) → t (f e) ≡ e
      to-from e = inverseˡ ≡.refl

      a∘to-from : (e : Fin H′.h) → H′.a (t (f e)) ≡ H′.a e
      a∘to-from = ≡.cong H′.a ∘ to-from

      ≗a′ : (e : Fin H′.h) → H.a (f e) ≡ H′.a e
      ≗a′ e = ≡.trans (≗a (f e)) (a∘to-from e)

      l≗ : (e : Fin H.h) → cast-gate (≗a e) (H.l e) ≡ H′.l (t e)
      l≗ e = ≈-sym (≡.sym (≗l e))

      l∘to-from : (e : Fin H′.h) → cast-gate (a∘to-from e) (H′.l (t (f e))) ≡ H′.l e
      l∘to-from e rewrite to-from e = ≈-reflexive ≡.refl

      ≗l′ : (e : Fin H′.h) → cast-gate (≗a′ e) (H.l (f e)) ≡ H′.l e
      ≗l′ e = ≈-trans {H.a _} (l≗ (f e)) (l∘to-from e)

      j∘to-from
          : (e : Fin H′.h) (i : Fin (H′.a (t (f e))))
          → H′.j (t (f e)) i
          ≡ H′.j e (fincast (a∘to-from e) i)
      j∘to-from e i rewrite to-from e = ≡.cong (H′.j e) (≡.sym (fincast-is-id ≡.refl i))

      open ≡.≡-Reasoning

      ≗j′ : (e : Fin H′.h) (i : Fin (H.a (f e))) → H.j (f e) i ≡ H′.j e (fincast (≗a′ e) i)
      ≗j′ e i = begin
          H.j (f e) i                                   ≡⟨ ≗j (f e) i ⟩
          H′.j (t (f e)) (fincast _ i)                  ≡⟨ j∘to-from e (fincast _ i) ⟩
          H′.j e (fincast (a∘to-from e) (fincast _ i))  ≡⟨ ≡.cong (H′.j e) (fincast-trans (≗a (f e)) _ i) ⟩
          H′.j e (fincast (≗a′ e) i)                    ∎

      cast-toVec
          : {n m : ℕ}
            {A : Set}
            (m≡n : m ≡ n)
            (f : Fin n → A)
          → Vec.cast m≡n (toVec (f ∘ fincast m≡n)) ≡ toVec f
      cast-toVec m≡n f rewrite m≡n = begin
          Vec.cast _ (toVec (f ∘ (fincast _)))  ≡⟨ VecCast.cast-is-id ≡.refl (toVec (f ∘ fincast ≡.refl)) ⟩
          toVec (f ∘ fincast _)             ≡⟨ tabulate-∘ f (fincast ≡.refl) ⟩
          Vec.map f (toVec (fincast _))     ≡⟨ ≡.cong (Vec.map f) (tabulate-cong (fincast-is-id ≡.refl)) ⟩
          Vec.map f (toVec id)              ≡⟨ tabulate-∘ f id ⟨
          toVec f                           ∎

      ≗p′ : (e : Fin H′.h) → Vec.cast (≗a′ e) (toVec (H.j (f e))) ≡ toVec (H′.j e)
      ≗p′ e = begin
          Vec.cast (≗a′ e) (toVec (H.j (f e)))    ≡⟨ ≡.cong (Vec.cast (≗a′ e)) (tabulate-cong (≗j′ e)) ⟩
          Vec.cast _ (toVec (H′.j e ∘ fincast _)) ≡⟨ cast-toVec (≗a′ e) (H′.j e) ⟩
          toVec (H′.j e)                      ∎

      H∘ρ≗H′ : (e : Fin H′.h) → asEdge H (↔h ⟨$⟩ˡ e) ≡ asEdge H′ e
      H∘ρ≗H′ e = Edge.≈⇒≡ record
          { ≡arity = ≗a′ e
          ; ≡label = ≗l′ e
          ; ≡ports = ≗p′ e
          }

equiv : (v : ℕ) → Equivalence (Circuitₛ v) (Hypergraph-Setoid′ v)
equiv v = record
    { to = to
    ; from = from
    ; to-cong = to-cong
    ; from-cong = from-cong
    }
