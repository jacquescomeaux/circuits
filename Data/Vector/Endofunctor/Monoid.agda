{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)
open import Level using (Level; _⊔_)

-- The endofunctor in monoids sending A to Vectorₘ A n for a fixed n
module Data.Vector.Endofunctor.Monoid (n : ℕ) {c ℓ : Level} where

import Data.Vec as Vec
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Algebra using (Monoid)
open import Categories.Category using (Category; _[_∘_]; _[_≈_])
open import Categories.Functor using (Functor)
open import Category.Instance.Monoids using (Monoids; MonoidHomomorphism; mk-⇒)
open import Data.Monoid using (toMonoid)
open import Data.Vec.Properties using (map-replicate)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (map⁺)
open import Data.Vector.Core as Core using (Vector; Vectorₛ; module ≊; replicate-cong)
open import Data.Vector.Endofunctor.Setoid as Endo using (mapₛ; zipWith-cong)
open import Data.Vector.Monoid as Mon using (Vectorₘ; ⟨ε⟩) renaming (_⊕_ to _[_⊕_])
open import Data.Vector.Vec using (map-zipWith; zipWith-map-map)
open import Function using (Func; _⟶ₛ_; _⟨$⟩_)

open Func
open MonoidHomomorphism

private module _ {M N : Monoid c ℓ} (f : MonoidHomomorphism c ℓ M N) where

  private
    module M = Monoid M
    module N = Monoid N

  open Core N.setoid using (_≊_)
  open ≈-Reasoning (Vectorₛ N.setoid n)

  opaque
    unfolding _[_⊕_]
    map-⊕
        : (W V : Vector M.setoid n)
        → mapₛ n (func f) ⟨$⟩ (M [ W ⊕ V ])
        ≊ N [ mapₛ n (func f) ⟨$⟩ W ⊕ mapₛ n (func f) ⟨$⟩ V ]
    map-⊕ W V = begin
        Vec.map ⟦ f ⟧ (Vec.zipWith M._∙_ W V)                 ≡⟨ map-zipWith ⟦ f ⟧ M._∙_ W V ⟩
        Vec.zipWith (λ x y → ⟦ f ⟧ (x M.∙ y)) W V             ≈⟨ zipWith-cong n N.setoid (homo f) W V ⟩
        Vec.zipWith (λ x y → ⟦ f ⟧ x N.∙ ⟦ f ⟧ y) W V         ≡⟨ zipWith-map-map ⟦ f ⟧ ⟦ f ⟧ N._∙_ W V ⟩
        Vec.zipWith N._∙_ (Vec.map ⟦ f ⟧ W) (Vec.map ⟦ f ⟧ V) ∎

  opaque
    unfolding ⟨ε⟩
    map-⟨ε⟩ : mapₛ n (func f) ⟨$⟩ (Mon.⟨ε⟩ M) ≊ Mon.⟨ε⟩ N
    map-⟨ε⟩ = begin
        Vec.map (to (func f)) (Vec.replicate n M.ε) ≡⟨ map-replicate (to (func f)) M.ε n ⟩
        Vec.replicate n (func f ⟨$⟩ M.ε)            ≈⟨ replicate-cong N.setoid (ε-homo f) ⟩
        Vec.replicate n N.ε ∎

mapₘ : {M N : Monoid c ℓ} → MonoidHomomorphism c ℓ M N → MonoidHomomorphism c (c ⊔ ℓ) (Vectorₘ M n) (Vectorₘ N n)
mapₘ {M} {N} f = mk-⇒ record
    { ⟦_⟧ = to (mapₛ n (func f))
    ; isMonoidHomomorphism = record
        { isMagmaHomomorphism = record
            { isRelHomomorphism = record
                { cong = map⁺ (⟦⟧-cong f)
                }
            ; homo = map-⊕ f
            }
        ; ε-homo = map-⟨ε⟩ f
        }
    }

open Category using (id)

abstract

  identity
      : {A : Monoid c ℓ}
      → Monoids c (c ⊔ ℓ) [ mapₘ (id (Monoids c ℓ) {A}) ≈ id (Monoids c (c ⊔ ℓ)) ]
  identity {A} V = Endo.identity n {c} {ℓ} {Monoid.setoid A}

  homomorphism
      : {X Y Z : Monoid c ℓ}
        {f : MonoidHomomorphism c ℓ X Y}
        {g : MonoidHomomorphism c ℓ Y Z}
      → Monoids c (c ⊔ ℓ) [ mapₘ (Monoids c ℓ [ g ∘ f ]) ≈ Monoids c (c ⊔ ℓ) [ mapₘ g ∘ mapₘ f ] ]
  homomorphism {X} {Y} {Z} {f} {g} V = Endo.homomorphism n {c} {ℓ} {setoid X} {setoid Y} {setoid Z} {func f} {func g} {V}
    where
      open Monoid using (setoid)

  F-resp-≈
      : {A B : Monoid c ℓ}
        {f g : MonoidHomomorphism c ℓ A B}
      → Monoids c ℓ [ f ≈ g ]
      → Monoids c (c ⊔ ℓ) [ mapₘ f ≈ mapₘ g ]
  F-resp-≈ {A} {B} {f} {g} f≈g V = Endo.F-resp-≈ n {c} {ℓ} {setoid A} {setoid B} {func f} {func g} (λ {x} → f≈g x)
    where
      open Monoid using (setoid)

-- only a true endofunctor when c ≤ ℓ
Vec : Functor (Monoids c ℓ) (Monoids c (c ⊔ ℓ))
Vec = record
    { F₀ = λ M → Vectorₘ M n
    ; F₁ = mapₘ
    ; identity = λ {M} → identity {M}
    ; homomorphism = λ {f = f} {g} → homomorphism {f = f} {g}
    ; F-resp-≈ = λ {f = f} {g} → F-resp-≈ {f = f} {g}
    }
