{-# OPTIONS --without-K --safe #-}

open import Data.Hypergraph.Label using (HypergraphLabel)

module Data.Hypergraph.Edge.Order (HL : HypergraphLabel) where

import Data.List.Sort as ListSort
import Data.Fin as Fin
import Data.Fin.Properties as FinProp
import Data.Vec as Vec
import Data.Vec.Relation.Binary.Equality.Cast as VecCast
import Data.Vec.Relation.Binary.Lex.Strict as Lex
import Relation.Binary.PropositionalEquality as ≡
import Relation.Binary.Properties.DecTotalOrder as DTOP
import Relation.Binary.Properties.StrictTotalOrder as STOP

open import Data.Hypergraph.Edge HL using (Edge; ≈-Edge; ≈-Edge-IsEquivalence)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Properties using (<-irrefl; <-trans; <-resp₂-≡; <-cmp)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise-≡⇒≡)
open import Level using (0ℓ)
open import Relation.Binary
  using
    ( Rel
    ; Tri ; Trichotomous
    ; IsStrictTotalOrder ; IsEquivalence
    ; _Respects_
    ; DecTotalOrder ; StrictTotalOrder
    )
open import Relation.Nullary using (¬_)

module HL = HypergraphLabel HL
open HL using (Label; cast; cast-is-id)
open Vec using (Vec)

open ≡ using (_≡_)

open HL using (_[_<_])
_<<_ : {v a : ℕ} → Rel (Vec (Fin v) a) 0ℓ
_<<_ {v} = Lex.Lex-< _≡_ (Fin._<_ {v})

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
  <-ports
      : {x y : Edge v}
        (≡a : Edge.arity x ≡ Edge.arity y)
        (≡l : Edge.label x HL.≈[ ≡a ] Edge.label y)
      → Vec.cast ≡a (Edge.ports x) << Edge.ports y
      → <-Edge x y

<-Edge-irrefl : {v : ℕ} {x y : Edge v} → ≈-Edge x y → ¬ <-Edge x y
<-Edge-irrefl record { ≡arity = ≡a } (<-arity n<m) = <-irrefl ≡a n<m
<-Edge-irrefl record { ≡label = ≡l } (<-label _ (_ , x≉y)) = x≉y ≡l
<-Edge-irrefl record { ≡ports = ≡p } (<-ports ≡.refl ≡l x<y)
    = Lex.<-irrefl FinProp.<-irrefl (≡⇒Pointwise-≡ ≡p) x<y

<-Edge-trans : {v : ℕ} {i j k : Edge v} → <-Edge i j → <-Edge j k → <-Edge i k
<-Edge-trans (<-arity i<j) (<-arity j<k) = <-arity (<-trans i<j j<k)
<-Edge-trans (<-arity i<j) (<-label ≡.refl j<k) = <-arity i<j
<-Edge-trans (<-arity i<j) (<-ports ≡.refl _ j<k) = <-arity i<j
<-Edge-trans (<-label ≡.refl i<j) (<-arity j<k) = <-arity j<k
<-Edge-trans {_} {i} (<-label ≡.refl i<j) (<-label ≡.refl j<k)
    = <-label ≡.refl (<-label-trans i<j (<-respˡ-≈ (HL.≈-reflexive ≡.refl) j<k))
  where
    open DTOP (HL.decTotalOrder (Edge.arity i)) using (<-respˡ-≈) renaming (<-trans to <-label-trans)
<-Edge-trans {k = k} (<-label ≡.refl i<j) (<-ports ≡.refl ≡.refl _)
    = <-label ≡.refl (<-respʳ-≈ (≡.sym (HL.≈-reflexive ≡.refl)) i<j)
  where
    open DTOP (HL.decTotalOrder (Edge.arity k)) using (<-respʳ-≈)
<-Edge-trans (<-ports ≡.refl _ _) (<-arity j<k) = <-arity j<k
<-Edge-trans {k = k} (<-ports ≡.refl ≡.refl _) (<-label ≡.refl j<k)
    = <-label ≡.refl (<-respˡ-≈ (≡.cong (cast _) (HL.≈-reflexive ≡.refl)) j<k)
  where
    open DTOP (HL.decTotalOrder (Edge.arity k)) using (<-respˡ-≈)
<-Edge-trans {j = j} (<-ports ≡.refl ≡l₁ i<j) (<-ports ≡.refl ≡l₂ j<k)
  rewrite (VecCast.cast-is-id ≡.refl (Edge.ports j))
    = <-ports ≡.refl
        (HL.≈-trans ≡l₁ ≡l₂)
        (Lex.<-trans ≡-isPartialEquivalence FinProp.<-resp₂-≡ FinProp.<-trans i<j j<k)
  where
    open IsEquivalence ≡.isEquivalence using () renaming (isPartialEquivalence to ≡-isPartialEquivalence)

<-Edge-respˡ-≈ : {v : ℕ} {y : Edge v} → (λ x → <-Edge x y) Respects ≈-Edge
<-Edge-respˡ-≈ ≈x (<-arity x₁<y) = <-arity (proj₂ <-resp₂-≡ ≡arity x₁<y)
  where
    open ≈-Edge ≈x using (≡arity)
<-Edge-respˡ-≈ {_} {y} record { ≡arity = ≡.refl ; ≡label = ≡.refl } (<-label ≡.refl x₁<y)
    = <-label ≡.refl (<-respˡ-≈ (≡.sym (HL.≈-reflexive ≡.refl)) x₁<y)
  where
    module y = Edge y
    open DTOP (HL.decTotalOrder y.arity) using (<-respˡ-≈)
<-Edge-respˡ-≈ record { ≡arity = ≡.refl ; ≡label = ≡.refl; ≡ports = ≡.refl} (<-ports ≡.refl ≡.refl x₁<y)
    = <-ports
        ≡.refl
        (≡.cong (cast _) (HL.≈-reflexive ≡.refl))
        (Lex.<-respectsˡ
            ≡-isPartialEquivalence
            FinProp.<-respˡ-≡
            (≡⇒Pointwise-≡ (≡.sym (VecCast.≈-reflexive ≡.refl)))
            x₁<y)
  where
    open IsEquivalence ≡.isEquivalence using () renaming (isPartialEquivalence to ≡-isPartialEquivalence)

<-Edge-respʳ-≈ : {v : ℕ} {x : Edge v} → <-Edge x Respects ≈-Edge
<-Edge-respʳ-≈ record { ≡arity = ≡a } (<-arity x<y₁) = <-arity (proj₁ <-resp₂-≡ ≡a x<y₁)
<-Edge-respʳ-≈ {_} {x} record { ≡arity = ≡.refl ; ≡label = ≡.refl } (<-label ≡.refl x<y₁)
    = <-label ≡.refl (<-respʳ-≈ (≡.sym (HL.≈-reflexive ≡.refl)) x<y₁)
  where
    module x = Edge x
    open DTOP (HL.decTotalOrder x.arity) using (<-respʳ-≈)
<-Edge-respʳ-≈ record { ≡arity = ≡.refl ; ≡label = ≡.refl; ≡ports = ≡.refl} (<-ports ≡.refl ≡.refl x<y₁)
    = <-ports
        ≡.refl
        (≡.cong (cast _) (≡.sym (HL.≈-reflexive ≡.refl)))
        (Lex.<-respectsʳ
            ≡-isPartialEquivalence
            FinProp.<-respʳ-≡
            (≡⇒Pointwise-≡ (≡.sym (VecCast.≈-reflexive ≡.refl)))
            x<y₁)
  where
    open IsEquivalence ≡.isEquivalence using () renaming (isPartialEquivalence to ≡-isPartialEquivalence)

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
    ¬y<x (<-label ≡a _) = x≢y (≡.sym ≡a)
    ¬y<x (<-ports ≡a _ _) = x≢y (≡.sym ≡a)
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
        ¬y<x (<-label _ y<x) = y≮x′ (<-respˡ-≈ (HL.≈-reflexive ≡.refl) y<x)
        ¬y<x (<-ports _ ≡l _) = x≢y (≡.trans (≡.sym ≡l) (cast-is-id ≡.refl y.label))
    ... | tri≈ x≮y′ x≡y′ y≮x′ = compare-ports
      where
        compare-ports : Tri (<-Edge x y) (≈-Edge x y) (<-Edge y x)
        compare-ports with Lex.<-cmp ≡.sym FinProp.<-cmp x.ports y.ports
        ... | tri< x<y x≢y y≮x″ =
                tri<
                  (<-ports ≡.refl
                    (HL.≈-reflexive x≡y′)
                    (Lex.<-respectsˡ
                      ≡-isPartialEquivalence
                      FinProp.<-respˡ-≡
                      (≡⇒Pointwise-≡ (≡.sym (VecCast.≈-reflexive ≡.refl)))
                      x<y))
                  (λ x≡y → x≢y (≡⇒Pointwise-≡ (≡.trans (≡.sym (VecCast.≈-reflexive ≡.refl)) (≡ports x≡y))))
                  ¬y<x
          where
            open IsEquivalence ≡.isEquivalence using () renaming (isPartialEquivalence to ≡-isPartialEquivalence)
            ¬y<x :  ¬ <-Edge y x
            ¬y<x (<-arity y<x) = y≮x y<x
            ¬y<x (<-label _ y<x) = y≮x′ (<-respˡ-≈ (HL.≈-reflexive ≡.refl) y<x)
            ¬y<x (<-ports _ _ y<x) =
                y≮x″
                  (Lex.<-respectsˡ
                    ≡-isPartialEquivalence
                    FinProp.<-respˡ-≡
                    (≡⇒Pointwise-≡ (VecCast.≈-reflexive ≡.refl))
                    y<x)
        ... | tri≈ x≮y″ x≡y″ y≮x″ = tri≈
                ¬x<y
                (record { ≡arity = ≡.refl ; ≡label = HL.≈-reflexive x≡y′ ; ≡ports = VecCast.≈-reflexive (Pointwise-≡⇒≡ x≡y″) })
                ¬y<x
          where
            open IsEquivalence ≡.isEquivalence using () renaming (isPartialEquivalence to ≡-isPartialEquivalence)
            ¬x<y : ¬ <-Edge x y
            ¬x<y (<-arity x<y) = x≮y x<y
            ¬x<y (<-label _ x<y) = x≮y′ (<-respˡ-≈ (HL.≈-reflexive ≡.refl) x<y)
            ¬x<y (<-ports _ _ x<y) =
                x≮y″
                  (Lex.<-respectsˡ
                    ≡-isPartialEquivalence
                    FinProp.<-respˡ-≡
                    (≡⇒Pointwise-≡ (VecCast.≈-reflexive ≡.refl))
                    x<y)
            ¬y<x : ¬ <-Edge y x
            ¬y<x (<-arity y<x) = y≮x y<x
            ¬y<x (<-label _ y<x) = y≮x′ (<-respˡ-≈ (HL.≈-reflexive ≡.refl) y<x)
            ¬y<x (<-ports _ _ y<x) =
                y≮x″
                  (Lex.<-respectsˡ
                    ≡-isPartialEquivalence
                    FinProp.<-respˡ-≡
                    (≡⇒Pointwise-≡ (VecCast.≈-reflexive ≡.refl))
                    y<x)

        ... | tri> x≮y″ x≢y y<x =
                tri>
                  ¬x<y
                  (λ x≡y → x≢y (≡⇒Pointwise-≡ (≡.trans (≡.sym (VecCast.≈-reflexive ≡.refl)) (≡ports x≡y))))
                  (<-ports
                    ≡.refl
                    (HL.≈-sym (HL.≈-reflexive x≡y′))
                    (Lex.<-respectsˡ
                      ≡-isPartialEquivalence
                      FinProp.<-respˡ-≡
                      (≡⇒Pointwise-≡ (≡.sym (VecCast.≈-reflexive ≡.refl)))
                      y<x))
          where
            open IsEquivalence ≡.isEquivalence using () renaming (isPartialEquivalence to ≡-isPartialEquivalence)
            ¬x<y : ¬ <-Edge x y
            ¬x<y (<-arity x<y) = x≮y x<y
            ¬x<y (<-label _ x<y) = x≮y′ (<-respˡ-≈ (HL.≈-reflexive ≡.refl) x<y)
            ¬x<y (<-ports _ _ x<y) =
                x≮y″
                  (Lex.<-respectsˡ
                    ≡-isPartialEquivalence
                    FinProp.<-respˡ-≡
                    (≡⇒Pointwise-≡ (VecCast.≈-reflexive ≡.refl))
                    x<y)
    ... | tri> x≮y′ x≢y y<x = tri>
            ¬x<y
            (λ x≡y → x≢y (≡.trans (≡.sym (HL.≈-reflexive ≡.refl)) (≡label x≡y)))
            (<-label ≡.refl (<-respˡ-≈ (≡.sym (HL.≈-reflexive ≡.refl)) y<x))
      where
        ¬x<y : ¬ <-Edge x y
        ¬x<y (<-arity x<y) = x≮y x<y
        ¬x<y (<-label ≡a x<y) = x≮y′ (<-respˡ-≈ (HL.≈-reflexive ≡.refl) x<y)
        ¬x<y (<-ports _ ≡l _) = x≢y (≡.trans (≡.sym (HL.≈-reflexive ≡.refl)) ≡l)
tri x y | tri> x≮y x≢y y<x = tri> ¬x<y (λ x≡y → x≢y (≡arity x≡y)) (<-arity y<x)
  where
    ¬x<y :  ¬ <-Edge x y
    ¬x<y (<-arity x<y) = x≮y x<y
    ¬x<y (<-label ≡a x<y) = x≢y ≡a
    ¬x<y (<-ports ≡a _ _) = x≢y ≡a

isStrictTotalOrder : {v : ℕ} → IsStrictTotalOrder (≈-Edge {v}) (<-Edge {v})
isStrictTotalOrder = record
    { isStrictPartialOrder = record
        { isEquivalence = ≈-Edge-IsEquivalence
        ; irrefl = <-Edge-irrefl
        ; trans = <-Edge-trans
        ; <-resp-≈ = <-Edge-respʳ-≈ , <-Edge-respˡ-≈
        }
    ; compare = tri
    }

strictTotalOrder : {v : ℕ} → StrictTotalOrder 0ℓ 0ℓ 0ℓ
strictTotalOrder {v} = record
    { Carrier = Edge v
    ; _≈_ = ≈-Edge {v}
    ; _<_ = <-Edge {v}
    ; isStrictTotalOrder = isStrictTotalOrder {v}
    }

open module STOP′ {v} = STOP (strictTotalOrder {v}) using (decTotalOrder) public

module Sort {v} = ListSort (decTotalOrder {v})
open Sort using (sort) public
