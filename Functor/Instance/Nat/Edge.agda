{-# OPTIONS --without-K --safe #-}

open import Data.Hypergraph.Label using (HypergraphLabel)

module Functor.Instance.Nat.Edge (HL : HypergraphLabel) where

import Data.Vec as Vec
import Data.Vec.Properties as VecProps

open import Categories.Category.Instance.Nat using (Nat)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)
open import Data.Fin using (Fin)
open import Data.Hypergraph.Edge HL as Edge using (≈-Edge-IsEquivalence; map; ≈-Edge; Edgeₛ)
open import Data.Nat using (ℕ)
open import Data.Vec.Relation.Binary.Equality.Cast using (≈-cong′; ≈-reflexive)
open import Level using (0ℓ)
open import Function using (id; _∘_; Func; _⟶ₛ_)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_)

module HL = HypergraphLabel HL

open Edge.Edge
open Func
open Functor
open Setoid
open ≈-Edge

Edge₁ : {n m : ℕ} → (Fin n → Fin m) → Edgeₛ n ⟶ₛ Edgeₛ m
Edge₁ f .to = map f
Edge₁ f .cong x≈y = record
    { ≡arity = ≡arity x≈y
    ; ≡label = ≡label x≈y
    ; ≡ports = ≈-cong′ (Vec.map f) (≡ports x≈y)
    }

map-id : {v : ℕ} {e : Edge.Edge v} → ≈-Edge (map id e) e
map-id .≡arity = ≡.refl
map-id .≡label = HL.≈-reflexive ≡.refl
map-id {_} {e} .≡ports = ≈-reflexive (VecProps.map-id (ports e))

map-∘
    : {n m o : ℕ}
      (f : Fin n → Fin m)
      (g : Fin m → Fin o)
      {e : Edge.Edge n}
    → ≈-Edge (map (g ∘ f) e) (map g (map f e))
map-∘ f g .≡arity = ≡.refl
map-∘ f g .≡label = HL.≈-reflexive ≡.refl
map-∘ f g {e} .≡ports = ≈-reflexive (VecProps.map-∘ g f (ports e))

map-resp-≗
    : {n m : ℕ}
      {f g : Fin n → Fin m}
    → f ≗ g
    → {e : Edge.Edge n}
    → ≈-Edge (map f e) (map g e)
map-resp-≗ f≗g .≡arity = ≡.refl
map-resp-≗ f≗g .≡label = HL.≈-reflexive ≡.refl
map-resp-≗ f≗g {e} .≡ports = ≈-reflexive (VecProps.map-cong f≗g (ports e))

Edge : Functor Nat (Setoids 0ℓ 0ℓ)
Edge .F₀ = Edgeₛ
Edge .F₁ = Edge₁
Edge .identity = map-id
Edge .homomorphism = map-∘ _ _
Edge .F-resp-≈ = map-resp-≗
