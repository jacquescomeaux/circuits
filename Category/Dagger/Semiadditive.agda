{-# OPTIONS --without-K --safe #-}

open import Level using (Level; suc; _⊔_)
open import Categories.Category using (Category)

module Category.Dagger.Semiadditive
    {o ℓ e : Level}
    (𝒞 : Category o ℓ e)
  where

import Categories.Category.Monoidal.Reasoning as ⊗-Reasoning
import Categories.Morphism.Reasoning as ⇒-Reasoning

open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Cocartesian 𝒞 using (Cocartesian; module CocartesianMonoidal; module CocartesianSymmetricMonoidal)
open import Categories.Category.Dagger using (HasDagger)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (module Symmetric)
open import Categories.Category.Monoidal.Symmetric.Properties using () renaming (module Shorthands to σ-Shorthands)
open import Categories.Category.Monoidal.Utilities using (module Shorthands)
open import Categories.Object.Duality using (Coproduct⇒coProduct)

record DaggerCocartesianMonoidal : Set (suc (o ⊔ ℓ ⊔ e)) where

  field
    cocartesian : Cocartesian
    dagger : HasDagger 𝒞

  open Cocartesian cocartesian using (i₁; i₂)
  open CocartesianMonoidal cocartesian using (+-monoidal; _⊗₀_; _⊗₁_)
  open CocartesianSymmetricMonoidal cocartesian using (+-symmetric)
  open HasDagger dagger using (_†; isUnitary; isSelfAdjoint)
  open Shorthands +-monoidal using (λ⇒; λ⇐; ρ⇒; ρ⇐; α⇒; α⇐)
  open σ-Shorthands +-symmetric using (σ⇒)
  open Category 𝒞

  -- dagger and cocartesian monoidal structure are compatible
  field
    λ≅† : {A : Obj} → λ⇒ {A} † ≈ λ⇐
    ρ≅† : {A : Obj} → ρ⇒ {A} † ≈ ρ⇐
    α≅† : {A B C : Obj} → α⇒ {A} {B} {C} † ≈ α⇐
    σ≅† : {A B : Obj} → σ⇒ {A} {B} † ≈ σ⇒
    †-resp-⊗ : {A B C D : Obj} {f : A ⇒ B} {g : C ⇒ D} → (f ⊗₁ g) † ≈ (f †) ⊗₁ (g †)

record SemiadditiveDagger : Set (suc (o ⊔ ℓ ⊔ e)) where

  field
    daggerCocartesianMonoidal : DaggerCocartesianMonoidal

  open DaggerCocartesianMonoidal daggerCocartesianMonoidal public
  open CocartesianMonoidal cocartesian using (+-monoidal) renaming (_⊗₀_ to _⊕₀_; _⊗₁_ to _⊕₁_; ⊗ to ⊕) public

  open Cocartesian cocartesian using (⊥; i₁; i₂; [_,_]; ¡; ∘[]; []∘+₁; []-cong₂; coproduct; ¡-unique; inject₁; inject₂; +-unique; +-g-η)
  open CocartesianSymmetricMonoidal cocartesian using (+-symmetric)
  open HasDagger dagger using (_†; †-involutive; †-resp-≈; †-identity; †-homomorphism)
  open Monoidal +-monoidal using (unitorˡ-commute-from; unitorʳ-commute-from; assoc-commute-from; module unitorˡ; module unitorʳ; module associator)
  open σ-Shorthands +-symmetric using (σ⇒)
  open Symmetric +-symmetric using (module braiding)
  open Shorthands +-monoidal using (λ⇒; λ⇐; ρ⇒; ρ⇐; α⇒; α⇐)
  open Category 𝒞

  -- projection maps
  p₁ : {A B : Obj} → A ⊕₀ B ⇒ A
  p₁ = i₁ †

  p₂ : {A B : Obj} → A ⊕₀ B ⇒ B
  p₂ = i₂ †

  -- codiagonal
  ▽ : {A : Obj} → A ⊕₀ A ⇒ A
  ▽ = [ id , id ]

  -- diagonal
  △ : {A : Obj} → A ⇒ A ⊕₀ A
  △ = ▽ †

  private
    op-binaryProducts : BinaryProducts op
    op-binaryProducts = record { product = Coproduct⇒coProduct 𝒞 coproduct }
    open BinaryProducts op-binaryProducts using () renaming (assocʳ∘⟨⟩ to []-assoc; swap∘⟨⟩ to []∘swap)

  open ⊗-Reasoning +-monoidal
  open ⇒-Reasoning 𝒞

  ▽-assoc : {A : Obj} → ▽ {A} ∘ ▽ ⊕₁ id ≈ ▽ ∘ id ⊕₁ ▽ ∘ α⇒
  ▽-assoc = begin
      [ id , id ] ∘ [ id , id ] ⊕₁ id       ≈⟨ []∘+₁ ⟩
      [ id ∘ [ id , id ] , id ∘ id ]        ≈⟨ []-cong₂ identityˡ identityˡ ⟩
      [ [ id , id ] , id ]                  ≈⟨ []-assoc ⟨
      [ id , [ id , id ] ] ∘ α⇒             ≈⟨ []-cong₂ identityˡ identityˡ ⟩∘⟨refl ⟨
      [ id ∘ id , id ∘ [ id , id ] ] ∘ α⇒   ≈⟨ pushˡ (Equiv.sym []∘+₁) ⟩
      [ id , id ] ∘ id ⊕₁ [ id , id ] ∘ α⇒  ∎

  △-assoc : {A : Obj} → id ⊕₁ △ ∘ △ {A} ≈ α⇒ ∘ △ ⊕₁ id ∘ △
  △-assoc = begin
      id ⊕₁ △ ∘ △                 ≈⟨ †-involutive (id ⊕₁ △ ∘ △) ⟨
      (id ⊕₁ △ ∘ △) † †           ≈⟨ †-resp-≈ †-homomorphism ⟩
      (△ † ∘ (id ⊕₁ △) †) †       ≈⟨ †-resp-≈ (†-involutive ▽ ⟩∘⟨ †-resp-⊗) ⟩
      (▽ ∘ (id †) ⊕₁ (△ †)) †     ≈⟨ †-resp-≈ (refl⟩∘⟨ †-identity ⟩⊗⟨ †-involutive ▽)⟩
      (▽ ∘ id ⊕₁ ▽) †             ≈⟨ †-resp-≈ (refl⟩∘⟨ introʳ associator.isoʳ) ⟩
      (▽ ∘ id ⊕₁ ▽ ∘ α⇒ ∘ α⇐) †   ≈⟨ †-resp-≈ (refl⟩∘⟨ assoc ) ⟨
      (▽ ∘ (id ⊕₁ ▽ ∘ α⇒) ∘ α⇐) † ≈⟨ †-resp-≈ (extendʳ ▽-assoc) ⟨
      (▽ ∘ ▽ ⊕₁ id ∘ α⇐) †        ≈⟨ †-homomorphism ⟩
      (▽ ⊕₁ id ∘ α⇐) † ∘ ▽ †      ≈⟨ pushˡ †-homomorphism ⟩
      α⇐ † ∘ (▽ ⊕₁ id) † ∘ △      ≈⟨ †-resp-≈ α≅† ⟩∘⟨refl ⟨
      α⇒ † † ∘ (▽ ⊕₁ id) † ∘ △    ≈⟨ †-involutive α⇒ ⟩∘⟨refl ⟩
      α⇒ ∘ (▽ ⊕₁ id) † ∘ △        ≈⟨ refl⟩∘⟨ †-resp-⊗ ⟩∘⟨refl ⟩
      α⇒ ∘ (▽ †) ⊕₁ (id †) ∘ △    ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ †-identity ⟩∘⟨refl ⟩
      α⇒ ∘ △ ⊕₁ id ∘ △            ∎

  ! : {A : Obj} → A ⇒ ⊥
  ! = ¡ †

  ▽-identityˡ : {A : Obj} → ▽ {A} ∘ ¡ ⊕₁ id ≈ λ⇒
  ▽-identityˡ = begin
      [ id , id ] ∘ ¡ ⊕₁ id ≈⟨ []∘+₁ ⟩
      [ id ∘ ¡ , id ∘ id ]  ≈⟨ []-cong₂ identityˡ identity² ⟩
      [ ¡ , id ]            ∎

  △-identityˡ : {A : Obj} → ! {A} ⊕₁ id ∘ △ ≈ λ⇐
  △-identityˡ = begin
      ! ⊕₁ id ∘ △           ≈⟨ refl⟩⊗⟨ †-identity ⟩∘⟨refl ⟨
      (¡ †) ⊕₁ (id †) ∘ ▽ † ≈⟨ †-resp-⊗ ⟩∘⟨refl ⟨
      (¡ ⊕₁ id) † ∘ ▽ †     ≈⟨ †-homomorphism ⟨
      (▽ ∘ ¡ ⊕₁ id) †       ≈⟨ †-resp-≈ ▽-identityˡ ⟩
      λ⇒ †                  ≈⟨ λ≅† ⟩
      λ⇐ ∎

  ▽-identityʳ : {A : Obj} → ▽ {A} ∘ id ⊕₁ ¡ ≈ ρ⇒
  ▽-identityʳ = begin
      [ id , id ] ∘ id ⊕₁ ¡ ≈⟨ []∘+₁ ⟩
      [ id ∘ id , id ∘ ¡ ]  ≈⟨ []-cong₂ identity² identityˡ ⟩
      [ id , ¡ ]            ∎

  △-identityʳ : {A : Obj} → id {A} ⊕₁ ! ∘ △ ≈ ρ⇐
  △-identityʳ = begin
      id ⊕₁ (¡ †) ∘ ▽ †     ≈⟨ †-identity ⟩⊗⟨refl ⟩∘⟨refl ⟨
      (id †) ⊕₁ (¡ †) ∘ ▽ † ≈⟨ †-resp-⊗ ⟩∘⟨refl ⟨
      (id ⊕₁ ¡) † ∘ ▽ †     ≈⟨ †-homomorphism ⟨
      (▽ ∘ id ⊕₁ ¡) †       ≈⟨ †-resp-≈ ▽-identityʳ ⟩
      ρ⇒ †                  ≈⟨ ρ≅† ⟩
      ρ⇐                    ∎

  ▽-comm : {A : Obj} → ▽ {A} ∘ σ⇒ ≈ ▽
  ▽-comm = []∘swap

  △-comm : {A : Obj} → σ⇒ ∘ △ {A} ≈ △
  △-comm = begin
      σ⇒ ∘ ▽ †    ≈⟨ σ≅† ⟩∘⟨refl ⟨
      σ⇒ † ∘ ▽ †  ≈⟨ †-homomorphism ⟨
      (▽ ∘ σ⇒) †  ≈⟨ †-resp-≈ ▽-comm ⟩
      ▽ †         ∎

  ⇒▽ : {A B : Obj} {f : A ⇒ B} → f ∘ ▽ ≈ ▽ ∘ f ⊕₁ f
  ⇒▽ {A} {B} {f} = begin
      f ∘ [ id , id ]       ≈⟨ ∘[] ⟩
      [ f ∘ id , f ∘ id ]   ≈⟨ []-cong₂ identityʳ identityʳ ⟩
      [ f , f ]             ≈⟨ []-cong₂ identityˡ identityˡ ⟨
      [ id ∘ f , id ∘ f ]   ≈⟨ []∘+₁ ⟨
      [ id , id ] ∘ f ⊕₁ f  ∎

  ⇒△ : {A B : Obj} {f : A ⇒ B} → △ ∘ f ≈ f ⊕₁ f ∘ △
  ⇒△ {A} {B} {f} = begin
      ▽ † ∘ f                   ≈⟨ refl⟩∘⟨ †-involutive f ⟨
      ▽ † ∘ f † †               ≈⟨ †-homomorphism ⟨
      (f † ∘ ▽) †               ≈⟨ †-resp-≈ ⇒▽ ⟩
      (▽ ∘ (f †) ⊕₁ (f †)) †    ≈⟨ †-homomorphism ⟩
      ((f †) ⊕₁ (f †)) † ∘ ▽ †  ≈⟨ †-resp-⊗ ⟩∘⟨refl ⟩
      (f † †) ⊕₁ (f † †) ∘ ▽ †  ≈⟨ †-involutive f ⟩⊗⟨ †-involutive f ⟩∘⟨refl ⟩
      f ⊕₁ f ∘ ▽ †              ∎

  ⇒¡ : {A B : Obj} {f : A ⇒ B} → f ∘ ¡ ≈ ¡
  ⇒¡ {A} {B} {f} = Equiv.sym (¡-unique (f ∘ ¡))

  ⇒! : {A B : Obj} {f : A ⇒ B} → ! ∘ f ≈ !
  ⇒! {A} {B} {f} = begin
      ¡ † ∘ f     ≈⟨ refl⟩∘⟨ †-involutive f ⟨
      ¡ † ∘ f † † ≈⟨ †-homomorphism ⟨
      (f † ∘ ¡) † ≈⟨ †-resp-≈ ⇒¡ ⟩
      ¡ †         ∎

  ρ⇐≈i₁ : {A : Obj} → ρ⇐ {A} ≈ i₁
  ρ⇐≈i₁ = Equiv.refl

  λ⇐≈i₂ : {A : Obj} → λ⇐ {A} ≈ i₂
  λ⇐≈i₂ = Equiv.refl

  λ⇒≈p₂ : {A : Obj} → λ⇒ {A} ≈ p₂
  λ⇒≈p₂ = begin
      λ⇒      ≈⟨ †-involutive λ⇒ ⟨
      λ⇒ † †  ≈⟨ †-resp-≈ λ≅† ⟩
      λ⇐ †    ≈⟨ †-resp-≈ λ⇐≈i₂ ⟩
      i₂ †    ∎

  ρ⇒≈p₁ : {A : Obj} → ρ⇒ {A} ≈ p₁
  ρ⇒≈p₁ = begin
      ρ⇒      ≈⟨ †-involutive ρ⇒ ⟨
      ρ⇒ † †  ≈⟨ †-resp-≈ ρ≅† ⟩
      ρ⇐ †    ≈⟨ †-resp-≈ ρ⇐≈i₁ ⟩
      i₁ †    ∎

  i₁-⊕ : {A B : Obj} → i₁ {A} {B} ≈ id ⊕₁ ¡ ∘ ρ⇐
  i₁-⊕ = begin
      i₁            ≈⟨ identityʳ ⟨
      i₁ ∘ id       ≈⟨ inject₁ ⟨
      id ⊕₁ ¡ ∘ i₁  ≈⟨ refl⟩∘⟨ ρ⇐≈i₁ ⟨
      id ⊕₁ ¡ ∘ ρ⇐  ∎

  i₂-⊕ : {A B : Obj} → i₂ {A} {B} ≈ ¡ ⊕₁ id ∘ λ⇐
  i₂-⊕ = begin
      i₂            ≈⟨ identityʳ ⟨
      i₂ ∘ id       ≈⟨ inject₂ ⟨
      ¡ ⊕₁ id ∘ i₂  ≈⟨ refl⟩∘⟨ λ⇐≈i₂ ⟨
      ¡ ⊕₁ id ∘ λ⇐  ∎

  p₁-⊕ : {A B : Obj} → p₁ {A} {B} ≈ ρ⇒ ∘ id ⊕₁ !
  p₁-⊕ {A} {B} = begin
      i₁ †                      ≈⟨ †-resp-≈ i₁-⊕ ⟩
      (id ⊕₁ ¡ ∘ ρ⇐) †          ≈⟨ †-homomorphism ⟩
      ρ⇐ † ∘ (id ⊕₁ ¡) †        ≈⟨ refl⟩∘⟨ †-resp-⊗ ⟩
      ρ⇐ † ∘ (id †) ⊕₁ (¡ †)    ≈⟨ †-resp-≈ ρ≅† ⟩∘⟨refl ⟨
      ρ⇒ † † ∘ (id †) ⊕₁ (¡ †)  ≈⟨ †-involutive ρ⇒ ⟩∘⟨ †-identity ⟩⊗⟨refl ⟩
      ρ⇒ ∘ id ⊕₁ (¡ †)          ∎

  p₂-⊕ : {A B : Obj} → p₂ {A} {B} ≈ λ⇒ ∘ ! ⊕₁ id
  p₂-⊕ {A} {B} = begin
      i₂ †                      ≈⟨ †-resp-≈ i₂-⊕ ⟩
      (¡ ⊕₁ id ∘ λ⇐) †          ≈⟨ †-homomorphism ⟩
      λ⇐ † ∘ (¡ ⊕₁ id) †        ≈⟨ refl⟩∘⟨ †-resp-⊗ ⟩
      λ⇐ † ∘ (¡ †) ⊕₁ (id †)    ≈⟨ †-resp-≈ λ≅† ⟩∘⟨refl ⟨
      λ⇒ † † ∘ (¡ †) ⊕₁ (id †)  ≈⟨ †-involutive λ⇒ ⟩∘⟨ refl⟩⊗⟨ †-identity ⟩
      λ⇒ ∘ (¡ †) ⊕₁ id          ∎

  -- zero arrows
  z : {A B : Obj} → A ⇒ B
  z = ¡ ∘ !

  field
    -- orthogonality conditions: pᵢiⱼ ≈ δᵢⱼ
    p₁-i₁ : {A B : Obj} → p₁ {A} {B} ∘ i₁ ≈ id {A}
    p₂-i₂ : {A B : Obj} → p₂ {A} {B} ∘ i₂ ≈ id {B}
    p₂-i₁ : {A B : Obj} → p₂ {A} {B} ∘ i₁ ≈ z {A} {B}
    p₁-i₂ : {A B : Obj} → p₁ {A} {B} ∘ i₂ ≈ z {B} {A}

  -- commutative monoid structure on homs
  module _ {A B : Obj} where

    _+_ : A ⇒ B → A ⇒ B → A ⇒ B
    _+_ f g = ▽ ∘ f ⊕₁ g ∘ △

    +-associative : {f g h : A ⇒ B} → (f + g) + h ≈ f + (g + h)
    +-associative {f} {g} {h} = begin
        ▽ ∘ (▽ ∘ f ⊕₁ g ∘ △) ⊕₁ h ∘ △                     ≈⟨ refl⟩∘⟨ pushˡ split₁ˡ ⟩
        ▽ ∘ ▽ ⊕₁ id ∘ (f ⊕₁ g ∘ △) ⊕₁ h ∘ △               ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₁ʳ ⟩
        ▽ ∘ ▽ ⊕₁ id ∘ (f ⊕₁ g) ⊕₁ h ∘ △ ⊕₁ id ∘ △         ≈⟨ extendʳ ▽-assoc ⟩
        ▽ ∘ (id ⊕₁ ▽ ∘ α⇒) ∘ (f ⊕₁ g) ⊕₁ h ∘ △ ⊕₁ id ∘ △  ≈⟨ refl⟩∘⟨ pullʳ (extendʳ assoc-commute-from) ⟩
        ▽ ∘ id ⊕₁ ▽ ∘ f ⊕₁ g ⊕₁ h ∘ α⇒ ∘ △ ⊕₁ id ∘ △      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ △-assoc ⟨
        ▽ ∘ id ⊕₁ ▽ ∘ f ⊕₁ g ⊕₁ h ∘ id ⊕₁ △ ∘ △           ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ merge₂ʳ ⟩
        ▽ ∘ id ⊕₁ ▽ ∘ f ⊕₁ (g ⊕₁ h ∘ △) ∘ △               ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
        ▽ ∘ f ⊕₁ (▽ ∘ g ⊕₁ h ∘ △) ∘ △                     ∎

    +-identityˡ : {f : A ⇒ B} → z + f ≈ f
    +-identityˡ {f} = begin
        ▽ ∘ (¡ ∘ !) ⊕₁ f ∘ △        ≈⟨ refl⟩∘⟨ pushˡ split₁ˡ ⟩
        ▽ ∘ ¡ ⊕₁ id ∘ ! ⊕₁ f ∘ △    ≈⟨ pullˡ ▽-identityˡ ⟩
        λ⇒ ∘ ! ⊕₁ f ∘ △             ≈⟨ refl⟩∘⟨ pushˡ serialize₂₁ ⟩
        λ⇒ ∘ id ⊕₁ f ∘ ! ⊕₁ id ∘ △  ≈⟨ extendʳ unitorˡ-commute-from ⟩
        f ∘ λ⇒ ∘ ! ⊕₁ id ∘ △        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ △-identityˡ ⟩
        f ∘ λ⇒ ∘ λ⇐                 ≈⟨ elimʳ unitorˡ.isoʳ ⟩
        f                           ∎

    +-identityʳ : {f : A ⇒ B} → f + z ≈ f
    +-identityʳ {f} = begin
        ▽ ∘ f ⊕₁ (¡ ∘ !) ∘ △        ≈⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
        ▽ ∘ id ⊕₁ ¡ ∘ (f ⊕₁ !) ∘ △  ≈⟨ pullˡ ▽-identityʳ ⟩
        ρ⇒ ∘ f ⊕₁ ! ∘ △             ≈⟨ refl⟩∘⟨ pushˡ serialize₁₂ ⟩
        ρ⇒ ∘ f ⊕₁ id ∘ id ⊕₁ ! ∘ △  ≈⟨ extendʳ unitorʳ-commute-from ⟩
        f ∘ ρ⇒ ∘ id ⊕₁ ! ∘ △        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ △-identityʳ ⟩
        f ∘ ρ⇒ ∘ ρ⇐                 ≈⟨ elimʳ unitorʳ.isoʳ ⟩
        f ∎

    +-commutative : {f g : A ⇒ B} → f + g ≈ g + f
    +-commutative {f} {g} = begin
        ▽ ∘ f ⊕₁ g ∘ △      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ △-comm ⟨
        ▽ ∘ f ⊕₁ g ∘ σ⇒ ∘ △ ≈⟨ refl⟩∘⟨ extendʳ (braiding.⇒.sym-commute _) ⟩
        ▽ ∘ σ⇒ ∘ g ⊕₁ f ∘ △ ≈⟨ pullˡ ▽-comm ⟩
        ▽ ∘ g ⊕₁ f ∘ △      ∎
