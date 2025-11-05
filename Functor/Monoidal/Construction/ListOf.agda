{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Cocartesian.Bundle using (CocartesianCategory)
open import Categories.Category.Construction.Monoids using (Monoids)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
open import Categories.Functor using (Functor) renaming (_∘F_ to _∙_)
open import Level using (Level)

module Functor.Monoidal.Construction.ListOf
    {o o′ ℓ ℓ′ e e′ : Level}
    {𝒞 : CocartesianCategory o ℓ e}
    {S : MonoidalCategory o′ ℓ′ e′}
    (let module 𝒞 = CocartesianCategory 𝒞)
    (let module S = MonoidalCategory S)
    (G : Functor 𝒞.U S.U)
    (M : Functor S.U (Monoids S.monoidal))
  where

import Categories.Category.Monoidal.Reasoning as ⊗-Reasoning
import Categories.Category.Monoidal.Utilities as ⊗-Util
import Categories.Morphism.Reasoning as ⇒-Reasoning
import Categories.Object.Monoid as MonoidObject

open import Categories.Category.Cocartesian using (module CocartesianMonoidal)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor.Monoidal using (MonoidalFunctor; IsMonoidalFunctor)
open import Categories.Functor.Properties using ([_]-resp-square; [_]-resp-∘)
open import Categories.Morphism using (_≅_)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Data.Product using (_,_)

module G = Functor G
module M = Functor M
module 𝒞-M = CocartesianMonoidal 𝒞.U 𝒞.cocartesian

open 𝒞 using (⊥; -+-; _+_; _+₁_; i₁; i₂; inject₁; inject₂)
module +-assoc {n} {m} {o} = _≅_ (𝒞.+-assoc {n} {m} {o})
module +-λ {n} = _≅_ (𝒞-M.⊥+A≅A {n})
module +-ρ {n} = _≅_ (𝒞-M.A+⊥≅A {n})

module _ where

  open 𝒞
  open ⇒-Reasoning U
  open ⊗-Reasoning 𝒞-M.+-monoidal

  module _ {n m o : Obj} where

    private

      +-α : (n + m) + o 𝒞.⇒ n + (m + o)
      +-α = +-assoc.to {n} {m} {o}

    +-α∘i₂ : +-α ∘ i₂ ≈ i₂ ∘ i₂
    +-α∘i₂ = inject₂

    +-α∘i₁∘i₁ : (+-α ∘ i₁) ∘ i₁ ≈ i₁
    +-α∘i₁∘i₁ = inject₁ ⟩∘⟨refl ○ inject₁

    +-α∘i₁∘i₂ : (+-α ∘ i₁) ∘ i₂ ≈ i₂ ∘ i₁
    +-α∘i₁∘i₂ = inject₁ ⟩∘⟨refl ○ inject₂

  module _ {n : Obj} where

    +-ρ∘i₁ : +-ρ.from {n} ∘ i₁ ≈ id
    +-ρ∘i₁ = inject₁

    +-λ∘i₂ : +-λ.from {n} ∘ i₂ ≈ id
    +-λ∘i₂ = inject₂

open S
open Functor
open MonoidalFunctor
open MonoidObject S.monoidal using (Monoid; Monoid⇒)
open Monoid renaming (assoc to μ-assoc; identityˡ to μ-identityˡ; identityʳ to μ-identityʳ)
open Monoid⇒

Forget : Functor (Monoids monoidal) U
Forget .F₀ = Carrier
Forget .F₁ = arr
Forget .identity = Equiv.refl
Forget .homomorphism = Equiv.refl
Forget .F-resp-≈ x = x

𝒞-MC : MonoidalCategory o ℓ e
𝒞-MC = record { monoidal = 𝒞-M.+-monoidal }

List : Functor U U
List = Forget ∙ M

module List = Functor List

List∘G : Functor 𝒞.U U
List∘G = List ∙ G

module LG = Functor List∘G

[] : {A : Obj} → unit ⇒ List.₀ A
[] {A} = η (M.₀ A)

++ : {A : Obj} → List.₀ A ⊗₀ List.₀ A ⇒ List.₀ A
++ {A} = μ (M.₀ A)

++⇒ : {A B : Obj} (f : A ⇒ B) → List.₁ f ∘ ++ ≈ ++ ∘ List.₁ f ⊗₁ List.₁ f
++⇒ f = preserves-μ (M.₁ f)

[]⇒ : {A B : Obj} (f : A ⇒ B) → List.₁ f ∘ [] ≈ []
[]⇒ f = preserves-η (M.₁ f)

++-⊗ : {n m : 𝒞.Obj} → LG.₀ n ⊗₀ LG.₀ m ⇒ LG.₀ (n + m)
++-⊗ = ++ ∘ LG.₁ i₁ ⊗₁ LG.₁ i₂

open ⇒-Reasoning U
open ⊗-Reasoning monoidal

module _ {n n′ m m′ : 𝒞.Obj} (f : n 𝒞.⇒ n′) (g : m 𝒞.⇒ m′) where

  LG[+₁∘i₁] : LG.₁ (f +₁ g) ∘ LG.₁ i₁ ≈ LG.₁ i₁ ∘ LG.₁ f
  LG[+₁∘i₁] = [ List∘G ]-resp-square inject₁

  LG[+₁∘i₂] : LG.₁ (f +₁ g) ∘ LG.₁ i₂ ≈ LG.₁ i₂ ∘ LG.₁ g
  LG[+₁∘i₂] = [ List∘G ]-resp-square inject₂

  ++-⊗-commute : ++-⊗ ∘ LG.₁ f ⊗₁ LG.₁ g ≈ LG.₁ (f +₁ g) ∘ ++-⊗
  ++-⊗-commute = begin
      (++ ∘ LG.₁ i₁ ⊗₁ LG.₁ i₂) ∘ LG.₁ f ⊗₁ LG.₁ g                  ≈⟨ pushʳ (parallel LG[+₁∘i₁] LG[+₁∘i₂]) ⟨
      ++ ∘ (LG.₁ (f +₁ g) ⊗₁ LG.₁ (f +₁ g)) ∘ (LG.₁ i₁ ⊗₁ LG.₁ i₂)  ≈⟨ extendʳ (++⇒ (G.₁ (f +₁ g))) ⟨
      LG.₁ (f +₁ g) ∘ ++ ∘ LG.₁ i₁ ⊗₁ LG.₁ i₂                       ∎

open ⊗-Util.Shorthands monoidal

++-homo : NaturalTransformation (⊗ ∙ (List∘G ⁂ List∘G)) (List∘G ∙ -+-)
++-homo = ntHelper record
    { η = λ (n , m) → ++-⊗ {n} {m}
    ; commute = λ { {n , m} {n′ , m′} (f , g) → ++-⊗-commute f g }
    }

α-++-⊗
    : {n m o : 𝒞.Obj}
    → LG.₁ (+-assoc.to {n} {m} {o})
    ∘ (++ ∘ LG.₁ i₁ ⊗₁ LG.₁ i₂)
    ∘ (++ ∘ LG.₁ i₁ ⊗₁ LG.₁ i₂) ⊗₁ id
    ≈ (++ ∘ LG.₁ i₁ ⊗₁ LG.₁ i₂)
    ∘ id ⊗₁ (++ ∘ LG.₁ i₁ ⊗₁ LG.₁ i₂)
    ∘ α⇒
α-++-⊗ {n} {m} {o} = begin
    LG.₁ +-α ∘ (++ ∘ LG.₁ i₁ ⊗₁ LG.₁ i₂) ∘ (++ ∘ LG.₁ i₁ ⊗₁ LG.₁ i₂) ⊗₁ id          ≈⟨ refl⟩∘⟨ pullʳ merge₁ʳ ⟩
    LG.₁ +-α ∘ ++ ∘ (LG.₁ i₁ ∘ ++ ∘ LG.₁ i₁ ⊗₁ LG.₁ i₂) ⊗₁ LG.₁ i₂                  ≈⟨ extendʳ (++⇒ (G.₁ +-α)) ⟩
    ++ ∘ LG.₁ +-α ⊗₁ LG.₁ +-α ∘ (LG.₁ i₁ ∘ ++ ∘ LG.₁ i₁ ⊗₁ LG.₁ i₂) ⊗₁ LG.₁ i₂      ≈⟨ refl⟩∘⟨ ⊗-distrib-over-∘ ⟨
    ++ ∘ (LG.₁ +-α ∘ LG.₁ i₁ ∘ ++ ∘ LG.₁ i₁ ⊗₁ LG.₁ i₂) ⊗₁ (LG.₁ +-α ∘ LG.₁ i₂)     ≈⟨ refl⟩∘⟨ pullˡ (Equiv.sym LG.homomorphism) ⟩⊗⟨ [ List∘G ]-resp-square +-α∘i₂ ⟩
    ++ ∘ (LG.₁ (+-α 𝒞.∘ i₁) ∘ ++ ∘ LG.₁ i₁ ⊗₁ LG.₁ i₂) ⊗₁ (LG.₁ i₂ ∘ LG.₁ i₂)       ≈⟨ refl⟩∘⟨ extendʳ (++⇒ (G.₁ (+-α 𝒞.∘ i₁))) ⟩⊗⟨refl ⟩
    ++ ∘ (++ ∘ LG.₁ (+-α 𝒞.∘ i₁) ⊗₁ LG.₁ (+-α 𝒞.∘ i₁) ∘ _) ⊗₁ (LG.₁ i₂ ∘ LG.₁ i₂)   ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ ⊗-distrib-over-∘) ⟩⊗⟨refl ⟨
    ++ ∘ (++ ∘ _ ⊗₁ (LG.₁ (+-α 𝒞.∘ i₁) ∘ LG.₁ i₂)) ⊗₁ (LG.₁ i₂ ∘ LG.₁ i₂)           ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ [ List∘G ]-resp-∘ +-α∘i₁∘i₁ ⟩⊗⟨ [ List∘G ]-resp-square +-α∘i₁∘i₂) ⟩⊗⟨refl ⟩
    ++ ∘ (++ ∘ LG.₁ i₁ ⊗₁ (LG.₁ i₂ ∘ LG.₁ i₁)) ⊗₁ (LG.₁ i₂ ∘ LG.₁ i₂)               ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
    ++ ∘ ++ ⊗₁ id ∘ (LG.₁ i₁ ⊗₁ (LG.₁ i₂ ∘ LG.₁ i₁)) ⊗₁ (LG.₁ i₂ ∘ LG.₁ i₂)         ≈⟨ extendʳ (μ-assoc (M.₀ (G.₀ (n + (m + o))))) ⟩
    ++ ∘ (id ⊗₁ ++ ∘ α⇒) ∘ (LG.₁ i₁ ⊗₁ (LG.₁ i₂ ∘ LG.₁ i₁)) ⊗₁ (LG.₁ i₂ ∘ LG.₁ i₂)  ≈⟨ refl⟩∘⟨ assoc ⟩
    ++ ∘ id ⊗₁ ++ ∘ α⇒ ∘ (LG.₁ i₁ ⊗₁ (LG.₁ i₂ ∘ LG.₁ i₁)) ⊗₁ (LG.₁ i₂ ∘ LG.₁ i₂)    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-commute-from ⟩
    ++ ∘ id ⊗₁ ++ ∘ LG.₁ i₁ ⊗₁ ((LG.₁ i₂ ∘ LG.₁ i₁) ⊗₁ (LG.₁ i₂ ∘ LG.₁ i₂)) ∘ α⇒    ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
    ++ ∘ LG.₁ i₁ ⊗₁ (++ ∘ (LG.₁ i₂ ∘ LG.₁ i₁) ⊗₁ (LG.₁ i₂ ∘ LG.₁ i₂)) ∘ α⇒          ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (refl⟩∘⟨ ⊗-distrib-over-∘) ⟩∘⟨refl ⟩
    ++ ∘ LG.₁ i₁ ⊗₁ (++ ∘ LG.₁ i₂ ⊗₁ LG.₁ i₂ ∘ LG.₁ i₁ ⊗₁ LG.₁ i₂) ∘ α⇒             ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (extendʳ (++⇒ (G.₁ i₂))) ⟩∘⟨refl ⟨
    ++ ∘ LG.₁ i₁ ⊗₁ (LG.₁ i₂ ∘ ++ ∘ LG.₁ i₁ ⊗₁ LG.₁ i₂) ∘ α⇒                        ≈⟨ pushʳ (pushˡ split₂ʳ) ⟩
    (++ ∘ LG.₁ i₁ ⊗₁ LG.₁ i₂) ∘ id ⊗₁ (++ ∘ LG.₁ i₁ ⊗₁ LG.₁ i₂) ∘ α⇒                ∎
  where
    +-α : (n + m) + o 𝒞.⇒ n + (m + o)
    +-α = +-assoc.to {n} {m} {o}


module _ {n : 𝒞.Obj} where

  ++-[]ʳ : {A B : Obj} (f : A ⇒ B) → ++ ∘ List.₁ f ⊗₁ [] ≈ List.₁ f ∘ ρ⇒
  ++-[]ʳ {A} {B} f = begin
      ++ ∘ List.₁ f ⊗₁ []             ≈⟨ refl⟩∘⟨ serialize₂₁ ⟩
      ++ ∘ id ⊗₁ [] ∘ List.₁ f ⊗₁ id  ≈⟨ pullˡ (Equiv.sym (μ-identityʳ (M.₀ B))) ⟩
      ρ⇒ ∘ List.₁ f ⊗₁ id             ≈⟨ unitorʳ-commute-from ⟩
      List.₁ f ∘ ρ⇒                   ∎

  ++-[]ˡ : {A B : Obj} (f : A ⇒ B) → ++ ∘ [] ⊗₁ List.₁ f ≈ List.₁ f ∘ λ⇒
  ++-[]ˡ {A} {B} f = begin
      ++ ∘ [] ⊗₁ List.₁ f             ≈⟨ refl⟩∘⟨ serialize₁₂ ⟩
      ++ ∘ [] ⊗₁ id ∘ id ⊗₁ List.₁ f  ≈⟨ pullˡ (Equiv.sym (μ-identityˡ (M.₀ B))) ⟩
      λ⇒ ∘ id ⊗₁ List.₁ f             ≈⟨ unitorˡ-commute-from ⟩
      List.₁ f ∘ λ⇒                   ∎

  ++-⊗-λ
      : LG.₁ +-λ.from ∘ (++ ∘ LG.₁ (i₁ {⊥} {n}) ⊗₁ LG.₁ i₂) ∘ [] ⊗₁ id
      ≈ λ⇒
  ++-⊗-λ = begin
      LG.₁ +-λ.from ∘ (++ ∘ LG.₁ i₁ ⊗₁ LG.₁ i₂) ∘ [] ⊗₁ id  ≈⟨ refl⟩∘⟨ pullʳ merge₁ʳ ⟩
      LG.₁ +-λ.from ∘ ++ ∘ (LG.₁ i₁ ∘ []) ⊗₁ LG.₁ i₂        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ []⇒ (G.₁ i₁) ⟩⊗⟨refl ⟩
      LG.₁ +-λ.from ∘ ++ ∘ [] ⊗₁ LG.₁ i₂                    ≈⟨ refl⟩∘⟨ ++-[]ˡ (G.₁ i₂) ⟩
      LG.₁ +-λ.from ∘ LG.₁ i₂ ∘ λ⇒                          ≈⟨ cancelˡ ([ List∘G ]-resp-∘ +-λ∘i₂ ○ LG.identity) ⟩
      λ⇒                                                    ∎

  ++-⊗-ρ
      : LG.₁ +-ρ.from ∘ (++ ∘ LG.₁ (i₁ {n}) ⊗₁ LG.₁ i₂) ∘ id ⊗₁ []
      ≈ ρ⇒
  ++-⊗-ρ = begin
      LG.₁ +-ρ.from ∘ (++ ∘ LG.₁ i₁ ⊗₁ LG.₁ i₂) ∘ id ⊗₁ []  ≈⟨ refl⟩∘⟨ pullʳ merge₂ʳ ⟩
      LG.₁ +-ρ.from ∘ ++ ∘ LG.₁ i₁ ⊗₁ (LG.₁ i₂ ∘ [])        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ []⇒ (G.₁ i₂) ⟩
      LG.₁ +-ρ.from ∘ ++ ∘ LG.₁ i₁ ⊗₁ []                    ≈⟨ refl⟩∘⟨ ++-[]ʳ (G.₁ i₁) ⟩
      LG.₁ +-ρ.from ∘ LG.₁ i₁ ∘ ρ⇒                          ≈⟨ cancelˡ ([ List∘G ]-resp-∘ +-ρ∘i₁ ○ LG.identity) ⟩
      ρ⇒                                                    ∎

open IsMonoidalFunctor

ListOf,++,[] : MonoidalFunctor 𝒞-MC S
ListOf,++,[] .F = List∘G
ListOf,++,[] .isMonoidal .ε = []
ListOf,++,[] .isMonoidal .⊗-homo = ++-homo
ListOf,++,[] .isMonoidal .associativity = α-++-⊗
ListOf,++,[] .isMonoidal .unitaryˡ = ++-⊗-λ
ListOf,++,[] .isMonoidal .unitaryʳ = ++-⊗-ρ
