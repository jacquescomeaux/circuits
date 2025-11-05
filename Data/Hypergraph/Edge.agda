{-# OPTIONS --without-K --safe #-}

open import Data.Hypergraph.Label using (HypergraphLabel)

open import Level using (Level; 0ℓ)
module Data.Hypergraph.Edge {ℓ : Level} (HL : HypergraphLabel) where

import Data.Vec as Vec
import Data.Vec.Relation.Binary.Equality.Cast as VecCast
import Relation.Binary.PropositionalEquality as ≡

open import Data.Fin using (Fin)
open import Data.Fin.Show using () renaming (show to showFin)
open import Data.Nat using (ℕ)
open import Data.String using (String; _<+>_)
open import Data.Vec.Show using () renaming (show to showVec)
open import Level using (0ℓ)
open import Relation.Binary using (Setoid; IsEquivalence)
open import Function using (_⟶ₛ_; Func)

module HL = HypergraphLabel HL

open HL using (Label; cast; cast-is-id)
open Vec using (Vec)
open Func

record Edge (v : ℕ) : Set ℓ where
  constructor mkEdge
  field
    {arity} : ℕ
    label : Label arity
    ports : Vec (Fin v) arity

map : {n m : ℕ} → (Fin n → Fin m) → Edge n → Edge m
map f edge = record
    { label = label
    ; ports = Vec.map f ports
    }
  where
    open Edge edge

open ≡ using (_≡_)
open VecCast using (_≈[_]_)

module _ {v : ℕ} where

  -- an equivalence relation on edges with v nodes
  record _≈_ (E E′ : Edge v) : Set ℓ where
    constructor mk≈
    module E = Edge E
    module E′ = Edge E′
    field
      ≡arity : E.arity ≡ E′.arity
      ≡label : cast ≡arity E.label ≡ E′.label
      ≡ports : E.ports ≈[ ≡arity ] E′.ports

  ≈-refl : {x : Edge v} → x ≈ x
  ≈-refl = record
      { ≡arity = ≡.refl
      ; ≡label = HL.≈-reflexive ≡.refl
      ; ≡ports = VecCast.≈-reflexive ≡.refl
      }

  ≈-sym : {x y : Edge v} → x ≈ y → y ≈ x
  ≈-sym x≈y = record
      { ≡arity = ≡.sym ≡arity
      ; ≡label = HL.≈-sym ≡label
      ; ≡ports = VecCast.≈-sym ≡ports
      }
    where
      open _≈_ x≈y

  ≈-trans : {i j k : Edge v} → i ≈ j → j ≈ k → i ≈ k
  ≈-trans {i} {j} {k} i≈j j≈k = record
      { ≡arity = ≡.trans i≈j.≡arity j≈k.≡arity
      ; ≡label = HL.≈-trans i≈j.≡label j≈k.≡label
      ; ≡ports = VecCast.≈-trans i≈j.≡ports j≈k.≡ports
      }
    where
      module i≈j = _≈_ i≈j
      module j≈k = _≈_ j≈k

  ≈-IsEquivalence : IsEquivalence _≈_
  ≈-IsEquivalence = record
      { refl = ≈-refl
      ; sym = ≈-sym
      ; trans = ≈-trans
      }

  show : Edge v → String
  show (mkEdge {a} l p) = HL.showLabel a l <+> showVec showFin p

  ≈⇒≡ : {x y : Edge v} → x ≈ y → x ≡ y
  ≈⇒≡ {mkEdge l p} (mk≈ ≡.refl ≡.refl ≡.refl)
    rewrite cast-is-id ≡.refl l
    rewrite VecCast.cast-is-id ≡.refl p = ≡.refl

Edgeₛ : (v : ℕ) → Setoid ℓ ℓ
Edgeₛ v = record { isEquivalence = ≈-IsEquivalence {v} }

mapₛ : {n m : ℕ} → (Fin n → Fin m) → Edgeₛ n ⟶ₛ Edgeₛ m
mapₛ f .to = map f
mapₛ f .cong (mk≈ ≡a ≡l ≡p) = mk≈ ≡a ≡l (VecCast.≈-cong′ (Vec.map f) ≡p)
