{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --hidden-argument-puns #-}

module Data.Opaque.Multiset where

import Data.List as L
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
import Data.Opaque.List as List

open import Algebra.Bundles using (CommutativeMonoid)
open import Data.List.Effectful.Foldable using (foldable; ++-homo)
open import Data.List.Relation.Binary.Permutation.Setoid as ↭ using (↭-setoid; ↭-refl)
open import Data.List.Relation.Binary.Permutation.Setoid.Properties using (map⁺; ++⁺; ++-comm)
open import Algebra.Morphism using (IsMonoidHomomorphism)
open import Data.Product using (_,_; uncurry′)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Setoid using (∣_∣)
open import Data.Setoid.Unit using (⊤ₛ)
open import Effect.Foldable using (RawFoldable)
open import Function using (_⟶ₛ_; Func; _⟨$⟩_; id)
open import Function.Construct.Constant using () renaming (function to Const)
open import Level using (Level; _⊔_)
open import Relation.Binary using (Setoid)

open Func

private

  variable
    a c ℓ : Level
    A B : Set a
    Aₛ Bₛ : Setoid c ℓ

opaque

  Multiset : Set a → Set a
  Multiset = L.List

  [] : Multiset A
  [] = L.[]

  _∷_ : A → Multiset A → Multiset A
  _∷_ = L._∷_

  map : (A → B) → Multiset A → Multiset B
  map = L.map

  _++_ : Multiset A → Multiset A → Multiset A
  _++_ = L._++_

  Multisetₛ : Setoid c ℓ → Setoid c (c ⊔ ℓ)
  Multisetₛ = ↭-setoid

  []ₛ : ⊤ₛ {c} {c ⊔ ℓ} ⟶ₛ Multisetₛ {c} {ℓ} Aₛ
  []ₛ {Aₛ} = Const ⊤ₛ (Multisetₛ Aₛ) []

  ∷ₛ : Aₛ ×ₛ Multisetₛ Aₛ ⟶ₛ Multisetₛ Aₛ
  ∷ₛ .to = uncurry′ _∷_
  ∷ₛ .cong = uncurry′ ↭.prep

  [-]ₛ : Aₛ ⟶ₛ Multisetₛ Aₛ
  [-]ₛ .to = L.[_]
  [-]ₛ {Aₛ} .cong y = ↭.prep y (↭-refl Aₛ)

  mapₛ : (Aₛ ⟶ₛ Bₛ) → Multisetₛ Aₛ ⟶ₛ Multisetₛ Bₛ
  mapₛ f .to = map (to f)
  mapₛ {Aₛ} {Bₛ} f .cong xs≈ys = map⁺ Aₛ Bₛ (cong f) xs≈ys

  ++ₛ : Multisetₛ Aₛ ×ₛ Multisetₛ Aₛ ⟶ₛ Multisetₛ Aₛ
  ++ₛ .to = uncurry′ _++_
  ++ₛ {Aₛ} .cong = uncurry′ (++⁺ Aₛ)

  ++ₛ-comm
      : (open Setoid (Multisetₛ Aₛ))
      → (xs ys : Carrier)
      → ++ₛ ⟨$⟩ (xs , ys) ≈ ++ₛ ⟨$⟩ (ys , xs)
  ++ₛ-comm {Aₛ} xs ys = ++-comm Aₛ xs ys

module _ (M : CommutativeMonoid c ℓ) where

  open CommutativeMonoid M renaming (setoid to Mₛ)

  opaque
    unfolding Multiset List.fold-cong
    fold : ∣ Multisetₛ Mₛ ∣ → ∣ Mₛ ∣
    fold = List.fold monoid -- RawFoldable.fold foldable rawMonoid

    fold-cong
        : {xs ys : ∣ Multisetₛ Mₛ ∣}
        → (let module [M]ₛ = Setoid (Multisetₛ Mₛ))
        → (xs [M]ₛ.≈ ys)
        → fold xs ≈ fold ys
    fold-cong (↭.refl x) = cong (List.foldₛ monoid) x
    fold-cong (↭.prep x≈y xs↭ys) = ∙-cong x≈y (fold-cong xs↭ys)
    fold-cong
        {x₀ L.∷ x₁ L.∷ xs}
        {y₀ L.∷ y₁ L.∷ ys}
        (↭.swap x₀≈y₁ x₁≈y₀ xs↭ys) = trans
            (sym (assoc x₀ x₁ (fold xs))) (trans 
            (∙-cong (trans (∙-cong x₀≈y₁ x₁≈y₀) (comm y₁ y₀)) (fold-cong xs↭ys))
            (assoc y₀ y₁ (fold ys)))
    fold-cong {xs} {ys} (↭.trans xs↭zs zs↭ys) = trans (fold-cong xs↭zs) (fold-cong zs↭ys)

  foldₛ : Multisetₛ Mₛ ⟶ₛ Mₛ
  foldₛ .to = fold
  foldₛ .cong = fold-cong

  opaque
    unfolding fold
    ++ₛ-homo
        : (xs ys : ∣ Multisetₛ Mₛ ∣)
        → foldₛ ⟨$⟩ (++ₛ ⟨$⟩ (xs , ys)) ≈ (foldₛ ⟨$⟩ xs) ∙ (foldₛ ⟨$⟩ ys)
    ++ₛ-homo xs ys = ++-homo monoid id xs

    []ₛ-homo : foldₛ ⟨$⟩ ([]ₛ ⟨$⟩ _) ≈ ε
    []ₛ-homo = refl

module _ (M N : CommutativeMonoid c ℓ) where

  module M = CommutativeMonoid M
  module N = CommutativeMonoid N

  opaque
    unfolding fold

    fold-mapₛ
        : (f : M.setoid ⟶ₛ N.setoid)
        → IsMonoidHomomorphism M.rawMonoid N.rawMonoid (to f)
        → {xs : ∣ Multisetₛ M.setoid ∣}
        → foldₛ N ⟨$⟩ (mapₛ f ⟨$⟩ xs) N.≈ f ⟨$⟩ (foldₛ M ⟨$⟩ xs)
    fold-mapₛ = List.fold-mapₛ M.monoid N.monoid
