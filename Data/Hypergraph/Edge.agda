{-# OPTIONS --without-K --safe #-}

open import Data.Hypergraph.Label using (HypergraphLabel)

open import Level using (Level; 0ℓ)
module Data.Hypergraph.Edge {ℓ : Level} (HL : HypergraphLabel) where

import Data.Vec.Functional as Vec
import Data.Vec.Functional.Relation.Binary.Equality.Setoid as PW
import Data.Fin.Properties as FinProp

open import Data.Fin as Fin using (Fin)
open import Data.Fin.Show using () renaming (show to showFin)
open import Data.Nat using (ℕ)
open import Data.String using (String; _<+>_)
open import Data.Vec.Show using () renaming (show to showVec)
open import Level using (0ℓ)
open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; module ≡-Reasoning)
open import Function using (_⟶ₛ_; Func; _∘_)

module HL = HypergraphLabel HL

open HL using (Label)
open Vec using (Vector)
open Func

record Edge (v : ℕ) : Set ℓ where
  constructor mkEdge
  field
    {arity} : ℕ
    label : Label arity
    ports : Fin arity → Fin v

map : {n m : ℕ} → (Fin n → Fin m) → Edge n → Edge m
map f edge = record
    { label = label
    ; ports = Vec.map f ports
    }
  where
    open Edge edge

module _ {v : ℕ} where

  open PW (≡.setoid (Fin v)) using (_≋_)

  -- an equivalence relation on edges with v nodes
  record _≈_ (E E′ : Edge v) : Set ℓ where
    constructor mk≈
    module E = Edge E
    module E′ = Edge E′
    field
      ≡arity : E.arity ≡ E′.arity
      ≡label : HL.cast ≡arity E.label ≡ E′.label
      ≡ports : E.ports ≋ E′.ports ∘ Fin.cast ≡arity

  ≈-refl : {x : Edge v} → x ≈ x
  ≈-refl {x} = record
      { ≡arity = ≡.refl
      ; ≡label = HL.≈-reflexive ≡.refl
      ; ≡ports = ≡.cong (Edge.ports x) ∘ ≡.sym ∘ FinProp.cast-is-id _
      }

  ≈-sym : {x y : Edge v} → x ≈ y → y ≈ x
  ≈-sym x≈y = record
      { ≡arity = ≡.sym ≡arity
      ; ≡label = HL.≈-sym ≡label
      ; ≡ports = ≡.sym ∘ ≡ports-sym
      }
    where
      open _≈_ x≈y
      open ≡-Reasoning
      ≡ports-sym : (i : Fin E′.arity) → E.ports (Fin.cast _ i) ≡ E′.ports i
      ≡ports-sym i = begin
          E.ports (Fin.cast _ i)                    ≡⟨ ≡ports (Fin.cast _ i) ⟩
          E′.ports (Fin.cast ≡arity (Fin.cast _ i))
            ≡⟨ ≡.cong E′.ports (FinProp.cast-involutive ≡arity _ i) ⟩
          E′.ports i                                ∎

  ≈-trans : {x y z : Edge v} → x ≈ y → y ≈ z → x ≈ z
  ≈-trans {x} {y} {z} x≈y y≈z = record
      { ≡arity = ≡.trans x≈y.≡arity y≈z.≡arity
      ; ≡label = HL.≈-trans x≈y.≡label y≈z.≡label
      ; ≡ports = ≡-ports
      }
    where
      module x≈y = _≈_ x≈y
      module y≈z = _≈_ y≈z
      open ≡-Reasoning
      ≡-ports : (i : Fin x≈y.E.arity) → x≈y.E.ports i ≡ y≈z.E′.ports (Fin.cast _ i)
      ≡-ports i = begin
          x≈y.E.ports i               ≡⟨ x≈y.≡ports i ⟩
          y≈z.E.ports (Fin.cast _ i)  ≡⟨ y≈z.≡ports (Fin.cast _ i) ⟩
          y≈z.E′.ports (Fin.cast y≈z.≡arity (Fin.cast _ i)) 
            ≡⟨ ≡.cong y≈z.E′.ports (FinProp.cast-trans _ y≈z.≡arity i) ⟩
          y≈z.E′.ports (Fin.cast _ i) ∎

  ≈-IsEquivalence : IsEquivalence _≈_
  ≈-IsEquivalence = record
      { refl = ≈-refl
      ; sym = ≈-sym
      ; trans = ≈-trans
      }

  show : Edge v → String
  show (mkEdge {a} l p) = HL.showLabel a l <+> showVec showFin (Vec.toVec p)

Edgeₛ : (v : ℕ) → Setoid ℓ ℓ
Edgeₛ v = record { isEquivalence = ≈-IsEquivalence {v} }

mapₛ : {n m : ℕ} → (Fin n → Fin m) → Edgeₛ n ⟶ₛ Edgeₛ m
mapₛ f .to = map f
mapₛ f .cong (mk≈ ≡a ≡l ≡p) = mk≈ ≡a ≡l (≡.cong f ∘ ≡p)
