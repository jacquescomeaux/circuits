{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Functor.Monoidal.Symmetric using (module Strong)
open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)

open Strong using (SymmetricMonoidalFunctor)
open FinitelyCocompleteCategory
  using ()
  renaming (symmetricMonoidalCategory to smc)

module Category.Instance.DecoratedCospans
    {o ℓ e}
    (𝒞 : FinitelyCocompleteCategory o ℓ e)
    {𝒟 : SymmetricMonoidalCategory o ℓ e}
    (F : SymmetricMonoidalFunctor (smc 𝒞) 𝒟) where

import Category.Instance.Cospans 𝒞 as Cospans

open import Categories.Category
  using (Category; _[_∘_]; _[_≈_])
open import Categories.Morphism.Reasoning using (switch-fromtoˡ; glueTrianglesˡ)
open import Cospan.Decorated 𝒞 F using (DecoratedCospan)
open import Data.Product using (_,_)
open import Level using (_⊔_)
open import Categories.Functor.Properties using ([_]-resp-≅)

import Categories.Morphism as Morphism


module 𝒞 = FinitelyCocompleteCategory 𝒞
module 𝒟 = SymmetricMonoidalCategory 𝒟

open Morphism 𝒞.U using (module ≅)
open Morphism using () renaming (_≅_ to _[_≅_])
open SymmetricMonoidalFunctor F
  using (F₀; F₁; ⊗-homo; ε; homomorphism)
  renaming (identity to F-identity; F to F′)

private

  variable
    A B C : 𝒞.Obj

compose : DecoratedCospan A B → DecoratedCospan B C → DecoratedCospan A C
compose c₁ c₂ = record
    { cospan = Cospans.compose C₁.cospan C₂.cospan
    ; decoration = F₁ [ i₁ , i₂ ] ∘ φ ∘ s⊗t
    }
  where
    module C₁ = DecoratedCospan c₁
    module C₂ = DecoratedCospan c₂
    open 𝒞 using ([_,_]; _+_)
    open 𝒟 using (_⊗₀_; _⊗₁_; _∘_; unitorˡ; _⇒_; unit)
    module p = 𝒞.pushout C₁.f₂ C₂.f₁
    open p using (i₁; i₂)
    φ : F₀ C₁.N ⊗₀ F₀ C₂.N ⇒ F₀ (C₁.N + C₂.N)
    φ = ⊗-homo.⇒.η (C₁.N , C₂.N)
    s⊗t : unit ⇒ F₀ C₁.N ⊗₀ F₀ C₂.N
    s⊗t = C₁.decoration ⊗₁ C₂.decoration ∘ unitorˡ.to

identity : DecoratedCospan A A
identity = record
    { cospan = Cospans.identity
    ; decoration = 𝒟.U [ F₁ 𝒞.initial.! ∘ ε.from ]
    }

record Same (C₁ C₂ : DecoratedCospan A B) : Set (ℓ ⊔ e) where

  module C₁ = DecoratedCospan C₁
  module C₂ = DecoratedCospan C₂

  field
    ≅N : 𝒞.U [ C₁.N ≅ C₂.N ]

  module ≅N = _[_≅_] ≅N

  field
    from∘f₁≈f₁′ : 𝒞.U [ 𝒞.U [ ≅N.from ∘ C₁.f₁ ] ≈ C₂.f₁ ]
    from∘f₂≈f₂′ : 𝒞.U [ 𝒞.U [ ≅N.from ∘ C₁.f₂ ] ≈ C₂.f₂ ]
    same-deco : 𝒟.U [ 𝒟.U [ F₁ ≅N.from ∘ C₁.decoration ] ≈ C₂.decoration ]

  ≅F[N] : 𝒟.U [ F₀ C₁.N ≅ F₀ C₂.N ]
  ≅F[N] = [ F′ ]-resp-≅ ≅N

same-refl : {C : DecoratedCospan A B} → Same C C
same-refl = record
    { ≅N = ≅.refl
    ; from∘f₁≈f₁′ = 𝒞.identityˡ
    ; from∘f₂≈f₂′ = 𝒞.identityˡ
    ; same-deco = F-identity ⟩∘⟨refl ○ 𝒟.identityˡ
    }
  where
    open 𝒟.HomReasoning

same-sym : {C C′ : DecoratedCospan A B} → Same C C′ → Same C′ C
same-sym C≅C′ = record
    { ≅N = ≅.sym ≅N
    ; from∘f₁≈f₁′ = 𝒞.Equiv.sym (switch-fromtoˡ 𝒞.U ≅N from∘f₁≈f₁′)
    ; from∘f₂≈f₂′ = 𝒞.Equiv.sym (switch-fromtoˡ 𝒞.U ≅N from∘f₂≈f₂′)
    ; same-deco = 𝒟.Equiv.sym (switch-fromtoˡ 𝒟.U ≅F[N] same-deco)
    }
  where
    open Same C≅C′

same-trans : {C C′ C″ : DecoratedCospan A B} → Same C C′ → Same C′ C″ → Same C C″
same-trans C≈C′ C′≈C″ = record
    { ≅N = ≅.trans C≈C′.≅N C′≈C″.≅N
    ; from∘f₁≈f₁′ = glueTrianglesˡ 𝒞.U C′≈C″.from∘f₁≈f₁′ C≈C′.from∘f₁≈f₁′
    ; from∘f₂≈f₂′ = glueTrianglesˡ 𝒞.U C′≈C″.from∘f₂≈f₂′ C≈C′.from∘f₂≈f₂′
    ; same-deco = homomorphism ⟩∘⟨refl ○ glueTrianglesˡ 𝒟.U C′≈C″.same-deco C≈C′.same-deco
    }
  where
    module C≈C′ = Same C≈C′
    module C′≈C″ = Same C′≈C″
    open 𝒟.HomReasoning
