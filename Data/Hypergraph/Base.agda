{-# OPTIONS --without-K --safe #-}

module Data.Hypergraph.Base where

open import Data.Castable using (IsCastable)
open import Data.Fin using (Fin)

open import Relation.Binary
  using
    ( Rel
    ; IsDecTotalOrder
    ; IsStrictTotalOrder
    ; Tri
    ; Trichotomous
    ; _Respectsˡ_
    ; _Respectsʳ_
    ; _Respects_
    )
open import Relation.Binary.Bundles using (DecTotalOrder; StrictTotalOrder)
open import Relation.Nullary using (¬_)
open import Data.Nat.Base using (ℕ; _<_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Nat.Properties using (<-irrefl; <-trans; <-resp₂-≡; <-cmp)
open import Level using (Level; suc; _⊔_)

import Data.Vec.Base as VecBase
import Data.Vec.Relation.Binary.Equality.Cast as VecCast
import Relation.Binary.PropositionalEquality as ≡
import Relation.Binary.Properties.DecTotalOrder as DTOP

record HypergraphLabel {ℓ : Level} : Set (suc ℓ) where
  field
    Label : ℕ → Set ℓ
    isCastable : IsCastable Label
    -- _[_≈_] : (n : ℕ) → Rel (Label n) ℓ
    _[_≤_] : (n : ℕ) → Rel (Label n) ℓ
    isDecTotalOrder : (n : ℕ) → IsDecTotalOrder ≡._≡_ (n [_≤_])
  decTotalOrder : (n : ℕ) → DecTotalOrder ℓ ℓ ℓ
  decTotalOrder n = record
      { Carrier = Label n
      ; _≈_ = ≡._≡_
      ; _≤_ = n [_≤_]
      ; isDecTotalOrder = isDecTotalOrder n
      }

  open DTOP using (<-strictTotalOrder) renaming (_<_ to <)
  _[_<_] : (n : ℕ) → Rel (Label n) ℓ
  _[_<_] n =  < (decTotalOrder n)
  strictTotalOrder : (n : ℕ) → StrictTotalOrder ℓ ℓ ℓ
  strictTotalOrder n = <-strictTotalOrder (decTotalOrder n)
  open IsCastable isCastable public

module Edge (HL : HypergraphLabel) where

  module HL = HypergraphLabel HL
  open HL using (Label; cast; cast-is-id; cast-trans)
  open VecBase using (Vec)

  record Edge (v : ℕ) : Set where
    field
      {arity} : ℕ
      label : Label arity
      ports : Vec (Fin v) arity

  open ≡ using (_≡_)
  open VecCast using (_≈[_]_)

  record ≈-Edge {n : ℕ} (E E′ : Edge n) : Set where
    eta-equality
    module E = Edge E
    module E′ = Edge E′
    field
      ≡arity : E.arity ≡ E′.arity
      ≡label : cast ≡arity E.label ≡ E′.label
      ≡ports : E.ports ≈[ ≡arity ] E′.ports

  ≈-Edge-refl : {v : ℕ} {x : Edge v} → ≈-Edge x x
  ≈-Edge-refl {_} {x} = record
      { ≡arity = ≡.refl
      ; ≡label = HL.≈-reflexive ≡.refl
      ; ≡ports = VecCast.≈-reflexive ≡.refl
      }
    where
      open Edge x using (arity; label)
      open DecTotalOrder (HL.decTotalOrder arity) using (module Eq)

  ≈-Edge-sym : {v : ℕ} {x y : Edge v} → ≈-Edge x y → ≈-Edge y x
  ≈-Edge-sym {_} {x} {y} x≈y = record
      { ≡arity = ≡.sym ≡arity
      ; ≡label = HL.≈-sym ≡label
      ; ≡ports = VecCast.≈-sym ≡ports
      }
    where
      open ≈-Edge x≈y
      open DecTotalOrder (HL.decTotalOrder E.arity) using (module Eq)

  ≈-Edge-trans : {v : ℕ} {i j k : Edge v} → ≈-Edge i j → ≈-Edge j k → ≈-Edge i k
  ≈-Edge-trans {_} {i} {j} {k} i≈j j≈k = record
      { ≡arity = ≡.trans i≈j.≡arity j≈k.≡arity
      ; ≡label = HL.≈-trans i≈j.≡label j≈k.≡label
      ; ≡ports = VecCast.≈-trans i≈j.≡ports j≈k.≡ports
      }
    where
      module i≈j = ≈-Edge i≈j
      module j≈k = ≈-Edge j≈k

  open HL using (_[_<_])
  data <-Edge {v : ℕ} : Edge v → Edge v → Set where
    <-arity
        : {x y : Edge v}
        → Edge.arity x < Edge.arity y
        → <-Edge x y
    <-label
        : {x y : Edge v}
          (≡a : Edge.arity x ≡ Edge.arity y)
        → Edge.arity y [ cast ≡a (Edge.label x) < Edge.label y ]
        → <-Edge x y

  <-Edge-irrefl : {v : ℕ} {x y : Edge v} → ≈-Edge x y → ¬ <-Edge x y
  <-Edge-irrefl record { ≡arity = ≡a } (<-arity n<m) = <-irrefl ≡a n<m
  <-Edge-irrefl record { ≡label = ≡l } (<-label _ (_ , x≉y)) = x≉y ≡l

  <-Edge-trans : {v : ℕ} {i j k : Edge v} → <-Edge i j → <-Edge j k → <-Edge i k
  <-Edge-trans (<-arity i<j) (<-arity j<k) = <-arity (<-trans i<j j<k)
  <-Edge-trans (<-arity i<j) (<-label ≡.refl j<k) = <-arity i<j
  <-Edge-trans (<-label ≡.refl i<j) (<-arity j<k) = <-arity j<k
  <-Edge-trans {_} {i} (<-label ≡.refl i<j) (<-label ≡.refl j<k)
      = <-label ≡.refl (<-label-trans i<j (<-respˡ-≈ (HL.≈-reflexive ≡.refl) j<k))
    where
      open DTOP (HL.decTotalOrder (Edge.arity i)) using (<-respˡ-≈) renaming (<-trans to <-label-trans)

  <-Edge-respˡ-≈ : {v : ℕ} {y : Edge v} → (λ x → <-Edge x y) Respects ≈-Edge
  <-Edge-respˡ-≈ ≈x (<-arity x₁<y) = <-arity (proj₂ <-resp₂-≡ ≡arity x₁<y)
    where
      open ≈-Edge ≈x using (≡arity)
  <-Edge-respˡ-≈ {_} {y} record { ≡arity = ≡.refl ; ≡label = ≡.refl } (<-label ≡.refl x₁<y)
      = <-label ≡.refl (<-respˡ-≈ (≡.sym (HL.≈-reflexive ≡.refl)) x₁<y)
    where
      module y = Edge y
      open DTOP (HL.decTotalOrder y.arity) using (<-respˡ-≈)
  <-Edge-respʳ-≈ : {v : ℕ} {x : Edge v} → <-Edge x Respects ≈-Edge
  <-Edge-respʳ-≈ record { ≡arity = ≡a } (<-arity x<y₁) = <-arity (proj₁ <-resp₂-≡ ≡a x<y₁)
  <-Edge-respʳ-≈ {_} {x} record { ≡arity = ≡.refl ; ≡label = ≡.refl } (<-label ≡.refl x<y₁)
      = <-label ≡.refl (<-respʳ-≈ (≡.sym (HL.≈-reflexive ≡.refl)) x<y₁)
    where
      module x = Edge x
      open DTOP (HL.decTotalOrder x.arity) using (<-respʳ-≈)

  open Tri
  open ≈-Edge
  tri : {v : ℕ} → Trichotomous (≈-Edge {v}) (<-Edge {v})
  tri x y with <-cmp x.arity y.arity
    where
      module x = Edge x
      module y = Edge y
  tri x y | tri< x<y x≢y y≮x = tri< (<-arity x<y) (λ x≡y → x≢y (≡arity x≡y)) ¬y<x
    where
      ¬y<x :  ¬ <-Edge y x
      ¬y<x (<-arity y<x) = y≮x y<x
      ¬y<x (<-label ≡a y<x) = x≢y (≡.sym ≡a)
  tri x y | tri≈ x≮y ≡.refl y≮x = compare-label
    where
      module x = Edge x
      module y = Edge y
      open StrictTotalOrder (HL.strictTotalOrder x.arity) using (compare)
      import Relation.Binary.Properties.DecTotalOrder
      open DTOP (HL.decTotalOrder x.arity) using (<-respˡ-≈)
      compare-label : Tri (<-Edge x y) (≈-Edge x y) (<-Edge y x)
      compare-label with compare x.label y.label
      ... | tri< x<y x≢y y≮x′ = tri<
              (<-label ≡.refl (<-respˡ-≈ (≡.sym (HL.≈-reflexive ≡.refl)) x<y))
              (λ x≡y → x≢y (≡.trans (≡.sym (HL.≈-reflexive ≡.refl)) (≡label x≡y)))
              ¬y<x
        where
          ¬y<x :  ¬ <-Edge y x
          ¬y<x (<-arity y<x) = y≮x y<x
          ¬y<x (<-label ≡a y<x) = y≮x′ (<-respˡ-≈ (HL.≈-reflexive ≡.refl) y<x)
      ... | tri≈ x≮y x≡y y≮x = compare-ports
        where
          compare-ports : Tri (<-Edge x y) (≈-Edge x y) (<-Edge y x)
          compare-ports = ?
      ... | tri> x≮y′ x≢y y<x = tri>
              ¬x<y
              (λ x≡y → x≢y (≡.trans (≡.sym (HL.≈-reflexive ≡.refl)) (≡label x≡y)))
              (<-label ≡.refl (<-respˡ-≈ (≡.sym (HL.≈-reflexive ≡.refl)) y<x))
        where
          ¬x<y : ¬ <-Edge x y
          ¬x<y (<-arity x<y) = x≮y x<y
          ¬x<y (<-label ≡a x<y) = x≮y′ (<-respˡ-≈ (HL.≈-reflexive ≡.refl) x<y)
  tri x y | tri> x≮y x≢y y<x = tri> ¬x<y (λ x≡y → x≢y (≡arity x≡y)) (<-arity y<x)
    where
      ¬x<y :  ¬ <-Edge x y
      ¬x<y (<-arity x<y) = x≮y x<y
      ¬x<y (<-label ≡a x<y) = x≢y ≡a

  isStrictTotalOrder : {v : ℕ} → IsStrictTotalOrder (≈-Edge {v}) (<-Edge {v})
  isStrictTotalOrder = record
      { isStrictPartialOrder = record
          { isEquivalence = record
              { refl = ≈-Edge-refl
              ; sym = ≈-Edge-sym
              ; trans = ≈-Edge-trans
              }
          ; irrefl = <-Edge-irrefl
          ; trans = <-Edge-trans
          ; <-resp-≈ = <-Edge-respʳ-≈ , <-Edge-respˡ-≈
          }
      ; compare = tri
      }

module HypergraphList (HL : HypergraphLabel) where

  open import Data.List.Base using (List)
  open Edge HL using (Edge)

  record Hypergraph (v : ℕ) : Set where
    field
      edges : List (Edge v)
