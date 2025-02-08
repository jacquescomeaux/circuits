{-# OPTIONS --without-K --safe #-}

open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)

module Category.Monoidal.Instance.Cospans {o ℓ e} (𝒞 : FinitelyCocompleteCategory o ℓ e) where

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning.Iso as IsoReasoning

open import Categories.Category using (_[_,_]; _[_≈_]; _[_∘_]; Category)
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
open import Categories.Category.Cocartesian using (module CocartesianMonoidal; module CocartesianSymmetricMonoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Functor using (Functor)
open import Categories.Functor.Properties using ([_]-resp-≅)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)
open import Category.Instance.Cospans 𝒞 using (Cospans; Cospan)
open import Category.Instance.Properties.FinitelyCocompletes {o} {ℓ} {e} using (FinitelyCocompletes-CC)
open import Category.Monoidal.Instance.Cospans.Lift {o} {ℓ} {e} using (module Square)
open import Data.Product.Base using (_,_)
open import Functor.Instance.Cospan.Stack 𝒞 using (⊗)
open import Functor.Instance.Cospan.Embed 𝒞 using (L; L-resp-⊗)

module 𝒞 = FinitelyCocompleteCategory 𝒞
open CocartesianMonoidal 𝒞.U 𝒞.cocartesian using (⊥+--id; -+⊥-id; ⊥+A≅A; A+⊥≅A; +-monoidal)
open CocartesianSymmetricMonoidal 𝒞.U 𝒞.cocartesian using (+-symmetric)

open Monoidal +-monoidal using () renaming (triangle to tri; pentagon to pent)
open Symmetric +-symmetric using (braiding) renaming (hexagon₁ to hex₁; hexagon₂ to hex₂; commutative to comm)
open import Categories.Category.Monoidal.Utilities +-monoidal using (associator-naturalIsomorphism)

module _ where

  open CartesianCategory FinitelyCocompletes-CC using (products)
  open BinaryProducts products using (_×_)

  𝒞×𝒞 : FinitelyCocompleteCategory o ℓ e
  𝒞×𝒞 = 𝒞 × 𝒞

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
    module Unitorˡ = Square ⊥+--id
    module Unitorʳ = Square -+⊥-id
    module Associator = Square {[𝒞×𝒞]×𝒞} {𝒞} associator-naturalIsomorphism
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

CospansBraided : Braided CospansMonoidal
CospansBraided = record
    { braiding = niHelper record
        { η = λ { (X , Y) → Braiding.FX≅GX′.from {X , Y} }
        ; η⁻¹ = λ { (Y , X) → Braiding.FX≅GX′.to {Y , X} }
        ; commute = λ { {X , Y} {X′ , Y′} (f , g) → Braiding.from (record { f₁ = f₁ f , f₁ g ; f₂ = f₂ f , f₂ g }) }
        ; iso = λ { (X , Y) → Braiding.FX≅GX′.iso {X , Y} }
        }
    ; hexagon₁ = sym L-resp-⊗ ⟩∘⟨ refl ⟩∘⟨ sym L-resp-⊗ ○ refl⟩∘⟨ sym homomorphism ○ sym homomorphism ○ L-resp-≈ hex₁ ○ homomorphism ○ refl⟩∘⟨ homomorphism
    ; hexagon₂ = sym L-resp-⊗ ⟩∘⟨refl ⟩∘⟨ sym L-resp-⊗ ○ sym homomorphism ⟩∘⟨refl ○ sym homomorphism ○ L-resp-≈ hex₂ ○ homomorphism ○ homomorphism ⟩∘⟨refl
    }
  where
    open Cospan
    module Cospans = Category Cospans
    open Cospans.Equiv
    open Cospans.HomReasoning
    module Braiding = Square {𝒞×𝒞} {𝒞} braiding
    open Functor L renaming (F-resp-≈ to L-resp-≈)

CospansSymmetric : Symmetric CospansMonoidal
CospansSymmetric = record
    { braided = CospansBraided
    ; commutative = sym homomorphism ○ L-resp-≈ comm ○ identity
    }
  where
    module Cospans = Category Cospans
    open Cospans.Equiv
    open Cospans.HomReasoning
    open Functor L renaming (F-resp-≈ to L-resp-≈)
