{-# OPTIONS --without-K --safe #-}

module Data.Opaque.List where

import Data.List as L
import Function.Construct.Constant as Const
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Algebra.Bundles using (Monoid)
open import Algebra.Morphism using (IsMonoidHomomorphism)
open import Data.List.Effectful.Foldable using (foldable; ++-homo)
open import Data.List.Relation.Binary.Pointwise as PW using (++⁺; map⁺)
open import Data.Product using (_,_; curry′; uncurry′)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Setoid using (∣_∣)
open import Data.Unit.Polymorphic using (⊤)
open import Effect.Foldable using (RawFoldable)
open import Function using (_⟶ₛ_; Func; _⟨$⟩_; id)
open import Level using (Level; _⊔_)
open import Relation.Binary using (Setoid)

open Func

private

  variable
    a c ℓ : Level
    A B : Set a
    Aₛ Bₛ : Setoid c ℓ

  ⊤ₛ : Setoid c ℓ
  ⊤ₛ = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

opaque

  List : Set a → Set a
  List = L.List

  [] : List A
  [] = L.[]

  _∷_ : A → List A → List A
  _∷_ = L._∷_

  map : (A → B) → List A → List B
  map = L.map

  _++_ : List A → List A → List A
  _++_ = L._++_

  Listₛ : Setoid c ℓ → Setoid c (c ⊔ ℓ)
  Listₛ = PW.setoid

  []ₛ : ⊤ₛ {c} {c ⊔ ℓ} ⟶ₛ Listₛ {c} {ℓ} Aₛ
  []ₛ = Const.function ⊤ₛ (Listₛ _) []

  ∷ₛ : Aₛ ×ₛ Listₛ Aₛ ⟶ₛ Listₛ Aₛ
  ∷ₛ .to = uncurry′ _∷_
  ∷ₛ .cong = uncurry′ PW._∷_

  [-]ₛ : Aₛ ⟶ₛ Listₛ Aₛ
  [-]ₛ .to = L.[_]
  [-]ₛ .cong y = y PW.∷ PW.[]

  mapₛ : (Aₛ ⟶ₛ Bₛ) → Listₛ Aₛ ⟶ₛ Listₛ Bₛ
  mapₛ f .to = map (to f)
  mapₛ f .cong xs≈ys = map⁺ (to f) (to f) (PW.map (cong f) xs≈ys)

  cartesianProduct : ∣ Listₛ Aₛ ∣ → ∣ Listₛ Bₛ ∣ → ∣ Listₛ (Aₛ ×ₛ Bₛ) ∣
  cartesianProduct = L.cartesianProduct

  cartesian-product-cong
    : {xs xs′ : ∣ Listₛ Aₛ ∣}
      {ys ys′ : ∣ Listₛ Bₛ ∣}
    → (let open Setoid (Listₛ Aₛ) in xs ≈ xs′)
    → (let open Setoid (Listₛ Bₛ) in ys ≈ ys′)
    → (let open Setoid (Listₛ (Aₛ ×ₛ Bₛ)) in cartesianProduct xs ys ≈ cartesianProduct xs′ ys′)
  cartesian-product-cong PW.[] ys≋ys′ = PW.[]
  cartesian-product-cong {Aₛ = Aₛ} {Bₛ = Bₛ} {xs = x₀ L.∷ xs} {xs′ = x₀′ L.∷ xs′} (x₀≈x₀′ PW.∷ xs≋xs′) ys≋ys′ =
      ++⁺
          (map⁺ (x₀ ,_) (x₀′ ,_) (PW.map (x₀≈x₀′ ,_) ys≋ys′))
          (cartesian-product-cong {Aₛ = Aₛ} {Bₛ = Bₛ} xs≋xs′ ys≋ys′)

  pairsₛ : Listₛ Aₛ ×ₛ Listₛ Bₛ ⟶ₛ Listₛ (Aₛ ×ₛ Bₛ)
  pairsₛ .to = uncurry′ L.cartesianProduct
  pairsₛ {Aₛ = Aₛ} {Bₛ = Bₛ} .cong = uncurry′ (cartesian-product-cong {Aₛ = Aₛ} {Bₛ = Bₛ})

  ++ₛ : Listₛ Aₛ ×ₛ Listₛ Aₛ ⟶ₛ Listₛ Aₛ
  ++ₛ .to = uncurry′ _++_
  ++ₛ .cong = uncurry′ ++⁺

  foldr : (Aₛ ×ₛ Bₛ ⟶ₛ Bₛ) → ∣ Bₛ ∣ → ∣ Listₛ Aₛ ∣ → ∣ Bₛ ∣
  foldr f = L.foldr (curry′ (to f))

  foldr-cong
      : (f : Aₛ ×ₛ Bₛ ⟶ₛ Bₛ)
      → (e : ∣ Bₛ ∣)
      → (let module [A]ₛ = Setoid (Listₛ Aₛ))
      → {xs ys : ∣ Listₛ Aₛ ∣}
      → (xs [A]ₛ.≈ ys)
      → (open Setoid Bₛ)
      → foldr f e xs ≈ foldr f e ys
  foldr-cong {Bₛ = Bₛ} f e PW.[] = Setoid.refl Bₛ
  foldr-cong f e (x≈y PW.∷ xs≋ys) = cong f (x≈y , foldr-cong f e xs≋ys)

  foldrₛ : (Aₛ ×ₛ Bₛ ⟶ₛ Bₛ) → ∣ Bₛ ∣ → Listₛ Aₛ ⟶ₛ Bₛ
  foldrₛ f e .to = foldr f e
  foldrₛ {Bₛ = Bₛ} f e .cong = foldr-cong f e

module _ (M : Monoid c ℓ) where

  open Monoid M renaming (setoid to Mₛ)

  opaque
    unfolding List
    fold : ∣ Listₛ Mₛ ∣ → ∣ Mₛ ∣
    fold = RawFoldable.fold foldable rawMonoid

    fold-cong
        : {xs ys : ∣ Listₛ Mₛ ∣}
        → (let module [M]ₛ = Setoid (Listₛ Mₛ))
        → (xs [M]ₛ.≈ ys)
        → fold xs ≈ fold ys
    fold-cong = PW.rec (λ {xs} {ys} _ → fold xs ≈ fold ys) ∙-cong refl

  foldₛ : Listₛ Mₛ ⟶ₛ Mₛ
  foldₛ .to = fold
  foldₛ .cong = fold-cong

  opaque
    unfolding fold
    ++ₛ-homo
        : (xs ys : ∣ Listₛ Mₛ ∣)
        → foldₛ ⟨$⟩ (++ₛ ⟨$⟩ (xs , ys)) ≈ (foldₛ ⟨$⟩ xs) ∙ (foldₛ ⟨$⟩ ys)
    ++ₛ-homo xs ys = ++-homo M id xs

    []ₛ-homo : foldₛ ⟨$⟩ ([]ₛ ⟨$⟩ _) ≈ ε
    []ₛ-homo = refl

module _ (M N : Monoid c ℓ) where

  module M = Monoid M
  module N = Monoid N

  open IsMonoidHomomorphism

  opaque
    unfolding fold

    fold-mapₛ
        : (f : M.setoid ⟶ₛ N.setoid)
        → IsMonoidHomomorphism M.rawMonoid N.rawMonoid (to f)
        → {xs : ∣ Listₛ M.setoid ∣}
        → foldₛ N ⟨$⟩ (mapₛ f ⟨$⟩ xs) N.≈ f ⟨$⟩ (foldₛ M ⟨$⟩ xs)
    fold-mapₛ f isMH {L.[]} = N.sym (ε-homo isMH)
    fold-mapₛ f isMH {x L.∷ xs} = begin
        f′ x ∙ fold N (map f′ xs) ≈⟨ N.∙-cong N.refl (fold-mapₛ f isMH {xs}) ⟩
        f′ x ∙ f′ (fold M xs)     ≈⟨ homo isMH x (fold M xs) ⟨
        f′ (x ∘ fold M xs)        ∎
      where
        open N using (_∙_)
        open M using () renaming (_∙_ to _∘_)
        open ≈-Reasoning N.setoid
        f′ : M.Carrier → N.Carrier
        f′ = to f
