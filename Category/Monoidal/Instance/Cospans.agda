{-# OPTIONS --without-K --safe #-}

open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)

module Category.Monoidal.Instance.Cospans {o ℓ e} (𝒞 : FinitelyCocompleteCategory o ℓ e) where

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning.Iso as IsoReasoning

open import Categories.Category using (_[_,_]; _[_≈_]; _[_∘_]; Category)
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
open import Categories.Category.Cocartesian using (module CocartesianMonoidal)
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Functor using (Functor)
open import Categories.Functor.Properties using ([_]-resp-≅)
open import Category.Instance.Cospans 𝒞 using (Cospans)
open import Category.Instance.Properties.FinitelyCocompletes {o} {ℓ} {e} using (FinitelyCocompletes-CC)
open import Category.Monoidal.Instance.Cospans.Newsquare {o} {ℓ} {e} using (module NewSquare)
open import Data.Product.Base using (_,_)
open import Functor.Instance.Cospan.Stack 𝒞 using (⊗)
open import Functor.Instance.Cospan.Embed 𝒞 using (L; L-resp-⊗)

module 𝒞 = FinitelyCocompleteCategory 𝒞
open CocartesianMonoidal 𝒞.U 𝒞.cocartesian using (⊥+--id; -+⊥-id; ⊥+A≅A; A+⊥≅A; +-monoidal)

open Monoidal +-monoidal using () renaming (triangle to tri; pentagon to pent)
open import Categories.Category.Monoidal.Utilities +-monoidal using (associator-naturalIsomorphism)

module _ where

  open CartesianCategory FinitelyCocompletes-CC using (products)
  open BinaryProducts products using (_×_)

  [𝒞×𝒞]×𝒞 : FinitelyCocompleteCategory o ℓ e
  [𝒞×𝒞]×𝒞 = (𝒞 × 𝒞) × 𝒞

CospansMonoidal : Monoidal Cospans
CospansMonoidal = record
    { ⊗ = ⊗
    ; unit = ⊥
    ; unitorˡ = [ L ]-resp-≅ ⊥+A≅A
    ; unitorʳ = [ L ]-resp-≅ A+⊥≅A
    ; associator = [ L ]-resp-≅ (≅.sym +-assoc)
    ; unitorˡ-commute-from = λ { {X} {Y} {f} → Unitorˡ.from f }
    ; unitorˡ-commute-to = λ { {X} {Y} {f} → Unitorˡ.to f }
    ; unitorʳ-commute-from = λ { {X} {Y} {f} → Unitorʳ.from f }
    ; unitorʳ-commute-to = λ { {X} {Y} {f} → Unitorʳ.to f }
    ; assoc-commute-from = Associator.from _
    ; assoc-commute-to = Associator.to _
    ; triangle = triangle
    ; pentagon = pentagon
    }
  where
    module ⊗ = Functor ⊗
    module Cospans = Category Cospans
    module Unitorˡ = NewSquare ⊥+--id
    module Unitorʳ = NewSquare -+⊥-id
    module Associator = NewSquare {[𝒞×𝒞]×𝒞} {𝒞} associator-naturalIsomorphism
    open Cospans.HomReasoning
    open Cospans using (id)
    open Cospans.Equiv
    open Functor L renaming (F-resp-≈ to L-resp-≈)
    open 𝒞 using (⊥; Obj; U; +-assoc)
    open Morphism U using (module ≅)
    λ⇒ = Unitorˡ.FX≅GX′.from
    ρ⇒ = Unitorʳ.FX≅GX′.from
    α⇒ = Associator.FX≅GX′.from
    triangle : {X Y : Obj} → Cospans [ Cospans [ ⊗.₁ (id {X} , λ⇒) ∘ α⇒ ] ≈ ⊗.₁ (ρ⇒ , id {Y}) ]
    triangle = sym L-resp-⊗ ⟩∘⟨refl ○ sym homomorphism ○ L-resp-≈ tri ○ L-resp-⊗
    pentagon : {W X Y Z : Obj} → Cospans [ Cospans [ ⊗.₁ (id {W} , α⇒ {(X , Y) , Z}) ∘ Cospans [ α⇒ ∘ ⊗.₁ (α⇒ , id) ] ] ≈ Cospans [ α⇒ ∘ α⇒ ] ]
    pentagon = sym L-resp-⊗ ⟩∘⟨ refl ⟩∘⟨ sym L-resp-⊗ ○ refl⟩∘⟨ sym homomorphism ○ sym homomorphism ○ L-resp-≈ pent ○ homomorphism
