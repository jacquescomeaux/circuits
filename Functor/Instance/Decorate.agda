{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --hidden-argument-puns #-}

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory; SymmetricMonoidalCategory)
open import Categories.Functor.Monoidal.Symmetric using (module Lax)
open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)
open import Data.Product.Base using (_,_)

open Lax using (SymmetricMonoidalFunctor)
open FinitelyCocompleteCategory
  using ()
  renaming (symmetricMonoidalCategory to smc)

module Functor.Instance.Decorate
    {o o′ ℓ ℓ′ e e′}
    (𝒞 : FinitelyCocompleteCategory o ℓ e)
    {𝒟 : SymmetricMonoidalCategory o′ ℓ′ e′}
    (F : SymmetricMonoidalFunctor (smc 𝒞) 𝒟) where

import Categories.Category.Monoidal.Reasoning as ⊗-Reasoning
import Categories.Diagram.Pushout as DiagramPushout
import Categories.Morphism.Reasoning as ⇒-Reasoning
import Category.Diagram.Cospan 𝒞 as Cospan

open import Categories.Category using (Category; _[_,_]; _[_≈_]; _[_∘_])
open import Categories.Category.Monoidal using (module Monoidal)
open import Categories.Category.Cocartesian.Monoidal using (module CocartesianMonoidal)
open import Categories.Category.Monoidal.Properties using (coherence-inv₃)
open import Categories.Category.Monoidal.Utilities using (module Shorthands)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor.Properties using ([_]-resp-≅)
open import Function.Base using () renaming (id to idf)
open import Category.Instance.Cospans 𝒞 using (Cospans)
open import Category.Instance.DecoratedCospans 𝒞 F using (DecoratedCospans)
open import Functor.Instance.Cospan.Stack 𝒞 using (module ⊗)
open import Functor.Instance.DecoratedCospan.Stack 𝒞 F using () renaming (module ⊗ to ⊗′)

module 𝒞 = FinitelyCocompleteCategory 𝒞
module 𝒟 = SymmetricMonoidalCategory 𝒟
module F = SymmetricMonoidalFunctor F
module Cospans = Category Cospans
module DecoratedCospans = Category DecoratedCospans
module mc𝒞 = CocartesianMonoidal 𝒞.cocartesian

-- For every cospan there exists a free decorated cospan
-- i.e. the original cospan with the discrete decoration

private
  variable
    A A′ B B′ C C′ D : 𝒞.Obj
    f : Cospans [ A , B ]
    g : Cospans [ C , D ]

decorate : Cospans [ A , B ] → DecoratedCospans [ A , B ]
decorate f = record
    { cospan = f
    ; decoration = F₁ ¡ ∘ ε
    }
  where
    open 𝒞 using (¡)
    open 𝒟 using (_∘_)
    open F using (ε; F₁)

identity : DecoratedCospans [ decorate (Cospans.id {A}) ≈ DecoratedCospans.id ]
identity = record
    { cospans-≈ = Cospans.Equiv.refl
    ; same-deco = elimˡ F.identity
    }
  where
    open ⇒-Reasoning 𝒟.U

homomorphism : DecoratedCospans [ decorate (Cospans [ g ∘ f ]) ≈ DecoratedCospans [ decorate g ∘ decorate f ] ]
homomorphism {g} {f} = record
    { cospans-≈ = Cospans.Equiv.refl
    ; same-deco = same-deco
    }
  where

    open Cospan.Cospan f using (N; f₂)
    open Cospan.Cospan g using () renaming (N to M; f₁ to g₁)

    open 𝒟 using (U; monoidal; _⊗₁_; unitorˡ-commute-from) renaming (module unitorˡ to λ-)
    open 𝒞 using (¡; ⊥; ¡-unique; pushout) renaming ([_,_] to [_,_]′; _+₁_ to infixr 10 _+₁_ )
    open Category U
    open Equiv
    open ⇒-Reasoning U
    open ⊗-Reasoning monoidal
    open F.⊗-homo using () renaming (η to φ; commute to φ-commute)
    open F using (F₁; ε)
    open Shorthands monoidal

    open DiagramPushout 𝒞.U using (Pushout)
    open Pushout (pushout f₂ g₁) using (i₁; i₂)
    open Monoidal mc𝒞.+-monoidal using (unitorˡ)
    open unitorˡ using () renaming (to to λ⇐′)

    same-deco : F₁ 𝒞.id ∘ F₁ ¡ ∘ F.ε ≈ F₁ [ i₁ , i₂ ]′ ∘ φ (N , M) ∘ (F₁ ¡ ∘ ε) ⊗₁ (F₁ ¡ ∘ ε) ∘ ρ⇐
    same-deco = begin
        F₁ 𝒞.id ∘ F₁ ¡ ∘ ε                                                  ≈⟨ elimˡ F.identity ⟩
        F₁ ¡ ∘ ε                                                            ≈⟨ F.F-resp-≈ (¡-unique _) ⟩∘⟨refl ⟩
        F₁ ([ i₁ , i₂ ]′ 𝒞.∘ ¡ +₁ ¡ 𝒞.∘ λ⇐′) ∘ ε                            ≈⟨ refl⟩∘⟨ introʳ λ-.isoʳ ⟩
        F₁ ([ i₁ , i₂ ]′ 𝒞.∘ ¡ +₁ ¡ 𝒞.∘ λ⇐′) ∘ ε ∘ λ⇒ ∘ λ⇐                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ coherence-inv₃ monoidal ⟩
        F₁ ([ i₁ , i₂ ]′ 𝒞.∘ ¡ +₁ ¡ 𝒞.∘ λ⇐′) ∘ ε ∘ λ⇒ ∘ ρ⇐                  ≈⟨ refl⟩∘⟨ extendʳ unitorˡ-commute-from ⟨
        F₁ ([ i₁ , i₂ ]′ 𝒞.∘ ¡ +₁ ¡ 𝒞.∘ λ⇐′) ∘ λ⇒ ∘ id ⊗₁ ε ∘ ρ⇐            ≈⟨ pushˡ F.homomorphism ⟩
        F₁ [ i₁ , i₂ ]′ ∘ F₁ (¡ +₁ ¡ 𝒞.∘ λ⇐′) ∘ λ⇒ ∘ id ⊗₁ ε ∘ ρ⇐           ≈⟨ push-center F.homomorphism ⟩
        F₁ [ i₁ , i₂ ]′ ∘ F₁ (¡ +₁ ¡) ∘ F₁ λ⇐′ ∘ λ⇒ ∘ id ⊗₁ ε ∘ ρ⇐          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (switch-fromtoˡ ([ F.F ]-resp-≅ unitorˡ) F.unitaryˡ) ⟨
        F₁ [ i₁ , i₂ ]′ ∘ F₁ (¡ +₁ ¡) ∘ φ (⊥ , ⊥) ∘ ε ⊗₁ id ∘ id ⊗₁ ε ∘ ρ⇐  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (sym serialize₁₂) ⟩
        F₁ [ i₁ , i₂ ]′ ∘ F₁ (¡ +₁ ¡) ∘ φ (⊥ , ⊥) ∘ ε ⊗₁ ε ∘ ρ⇐             ≈⟨ refl⟩∘⟨ extendʳ (φ-commute (¡ , ¡)) ⟨
        F₁ [ i₁ , i₂ ]′ ∘ φ (N , M) ∘ F₁ ¡ ⊗₁ F₁ ¡ ∘ ε ⊗₁ ε ∘ ρ⇐            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (sym ⊗-distrib-over-∘) ⟩
        F₁ [ i₁ , i₂ ]′ ∘ φ (N , M) ∘ (F₁ ¡ ∘ ε) ⊗₁ (F₁ ¡ ∘ ε) ∘ ρ⇐         ∎

F-resp-≈ : Cospans [ f ≈ g ] → DecoratedCospans [ decorate f ≈ decorate g ]
F-resp-≈ f≈g = record
    { cospans-≈ = f≈g
    ; same-deco = pullˡ (sym F.homomorphism) ○ sym (F.F-resp-≈ (¡-unique _)) ⟩∘⟨refl
    }
  where
    open ⇒-Reasoning 𝒟.U
    open 𝒟.Equiv
    open 𝒟.HomReasoning
    open 𝒞 using (¡-unique)

Decorate : Functor Cospans DecoratedCospans
Decorate = record
    { F₀ = idf
    ; F₁ = decorate
    ; identity = identity
    ; homomorphism = homomorphism
    ; F-resp-≈ = F-resp-≈
    }

Decorate-resp-⊗ : DecoratedCospans [ decorate (⊗.₁ (f , g)) ≈ ⊗′.₁ (decorate f , decorate g) ]
Decorate-resp-⊗ {f} {g} = record
    { cospans-≈ = Cospan.≈-refl
    ; same-deco = same-deco
    }
  where

    open Cospan.Cospan f using (N)
    open Cospan.Cospan g using () renaming (N to M)

    open 𝒟 using (U; monoidal; _⊗₁_; unitorˡ-commute-from) renaming (module unitorˡ to λ-)
    open 𝒞 using (¡; ⊥; ¡-unique; pushout) renaming ([_,_] to [_,_]′; _+₁_ to infixr 10 _+₁_ )
    open Category U
    open Equiv
    open ⇒-Reasoning U
    open ⊗-Reasoning monoidal
    open F.⊗-homo using () renaming (η to φ; commute to φ-commute)
    open F using (F₁; ε)
    open Shorthands monoidal
    open Monoidal mc𝒞.+-monoidal using (unitorˡ)
    open unitorˡ using () renaming (to to λ⇐′)

    same-deco : F₁ 𝒞.id ∘ F₁ ¡ ∘ ε ≈ φ (N , M) ∘ (F₁ ¡ ∘ ε) ⊗₁ (F₁ ¡ ∘ ε) ∘ ρ⇐
    same-deco = begin
        F₁ 𝒞.id ∘ F₁ ¡ ∘ ε                                ≈⟨ elimˡ F.identity ⟩
        F₁ ¡ ∘ ε                                          ≈⟨ F.F-resp-≈ (¡-unique _) ⟩∘⟨refl ⟩
        F₁ (¡ +₁ ¡ 𝒞.∘ λ⇐′) ∘ ε                           ≈⟨ refl⟩∘⟨ introʳ λ-.isoʳ ⟩
        F₁ (¡ +₁ ¡ 𝒞.∘ λ⇐′) ∘ ε ∘ λ⇒ ∘ λ⇐                 ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ coherence-inv₃ monoidal ⟩
        F₁ (¡ +₁ ¡ 𝒞.∘ λ⇐′) ∘ ε ∘ λ⇒ ∘ ρ⇐                 ≈⟨ refl⟩∘⟨ extendʳ unitorˡ-commute-from ⟨
        F₁ (¡ +₁ ¡ 𝒞.∘ λ⇐′) ∘ λ⇒ ∘ id ⊗₁ ε ∘ ρ⇐           ≈⟨ pushˡ F.homomorphism ⟩
        F₁ (¡ +₁ ¡) ∘ F₁ λ⇐′ ∘ λ⇒ ∘ id ⊗₁ ε ∘ ρ⇐          ≈⟨ refl⟩∘⟨ extendʳ (switch-fromtoˡ ([ F.F ]-resp-≅ unitorˡ) F.unitaryˡ) ⟨
        F₁ (¡ +₁ ¡) ∘ φ (⊥ , ⊥) ∘ ε ⊗₁ id ∘ id ⊗₁ ε ∘ ρ⇐  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (sym serialize₁₂) ⟩
        F₁ (¡ +₁ ¡) ∘ φ (⊥ , ⊥) ∘ ε ⊗₁ ε ∘ ρ⇐             ≈⟨ extendʳ (φ-commute (¡ , ¡)) ⟨
        φ (N , M) ∘ F₁ ¡ ⊗₁ F₁ ¡ ∘ ε ⊗₁ ε ∘ ρ⇐            ≈⟨ refl⟩∘⟨ pullˡ (sym ⊗-distrib-over-∘) ⟩
        φ (N , M) ∘ (F₁ ¡ ∘ ε) ⊗₁ (F₁ ¡ ∘ ε) ∘ ρ⇐         ∎
