{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory; SymmetricMonoidalCategory)
open import Categories.Functor.Monoidal.Symmetric using (module Lax)
open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)

open Lax using (SymmetricMonoidalFunctor)
open FinitelyCocompleteCategory
  using ()
  renaming (symmetricMonoidalCategory to smc)

module Functor.Instance.DecoratedCospan.Embed
    {o o′ ℓ ℓ′ e e′}
    (𝒞 : FinitelyCocompleteCategory o ℓ e)
    {𝒟 : SymmetricMonoidalCategory o′ ℓ′ e′}
    (F : SymmetricMonoidalFunctor (smc 𝒞) 𝒟) where

import Categories.Category.Monoidal.Reasoning as ⊗-Reasoning
import Categories.Diagram.Pushout.Properties as PushoutProperties
import Categories.Morphism.Reasoning as ⇒-Reasoning
import Category.Diagram.Pushout as Pushout′
import Category.Diagram.Cospan as Cospan
import Functor.Instance.Cospan.Embed 𝒞 as Embed

open import Categories.Category using (Category; _[_,_]; _[_≈_]; _[_∘_])
open import Categories.Category.Monoidal.Properties using (coherence-inv₃)
open import Categories.Functor.Properties using ([_]-resp-≅)
open import Category.Instance.Cospans 𝒞 using (Cospans)
open import Category.Instance.DecoratedCospans 𝒞 F using (DecoratedCospans)

import Categories.Diagram.Pushout as DiagramPushout
import Categories.Diagram.Pushout.Properties as PushoutProperties
import Categories.Morphism as Morphism

open import Categories.Category.Monoidal using (module Monoidal)
open import Categories.Category.Cocartesian.Monoidal using (module CocartesianMonoidal)
open import Categories.Category.Monoidal.Utilities using (module Shorthands)
open import Categories.Functor using (Functor; _∘F_)
open import Data.Product using (_,_)
open import Function using () renaming (id to idf)
open import Functor.Instance.DecoratedCospan.Stack 𝒞 F using (⊗)

module 𝒞 = FinitelyCocompleteCategory 𝒞
module 𝒟 = SymmetricMonoidalCategory 𝒟
module F = SymmetricMonoidalFunctor F
module Cospans = Category Cospans
module DecoratedCospans = Category DecoratedCospans
module mc𝒞 = CocartesianMonoidal 𝒞.cocartesian

open import Functor.Instance.Decorate 𝒞 F using (Decorate; Decorate-resp-⊗)

private
  variable
    A B C D E H : 𝒞.Obj
    f : 𝒞.U [ A , B ]
    g : 𝒞.U [ C , D ]
    h : 𝒞.U [ E , H ]

L : Functor 𝒞.U DecoratedCospans
L = Decorate ∘F Embed.L

R : Functor 𝒞.op DecoratedCospans
R = Decorate ∘F Embed.R

B₁ : 𝒞.U [ A , C ] → 𝒞.U [ B , C ] → 𝒟.U [ 𝒟.unit , F.F₀ C ] → DecoratedCospans [ A , B ]
B₁ f g s = record
    { cospan = Cospan.cospan f g
    ; decoration = s
    }

module _ where

  module L = Functor L
  module R = Functor R

  module Codiagonal where

    open mc𝒞 using (+-monoidal) public
    open Monoidal +-monoidal using (unitorˡ; unitorʳ) public
    open unitorˡ using () renaming (to to λ⇐′) public
    open unitorʳ using () renaming (to to ρ⇐′) public
    open 𝒞 using (U; _+_; []-cong₂; []∘+₁; ∘-distribˡ-[]; inject₁; inject₂; ¡)
      renaming ([_,_] to [_,_]′; _+₁_ to infixr 10 _+₁_ )
    open Category U
    open Equiv
    open HomReasoning
    open ⇒-Reasoning 𝒞.U

    μ : {X : Obj} → X + X ⇒ X
    μ = [ id , id ]′

    μ∘+ : {X Y Z : Obj} {f : X ⇒ Z} {g : Y ⇒ Z} → [ f , g ]′ ≈ μ ∘ f +₁ g
    μ∘+ = []-cong₂ (sym identityˡ) (sym identityˡ) ○ sym []∘+₁

    μ∘¡ˡ : {X : Obj} → μ ∘ ¡ +₁ id ∘ λ⇐′ ≈ id {X}
    μ∘¡ˡ = begin
        μ ∘ ¡ +₁ id ∘ λ⇐′ ≈⟨ pullˡ (sym μ∘+) ⟩
        [ ¡ , id ]′ ∘ λ⇐′ ≈⟨ inject₂ ⟩
        id                ∎

    μ∘¡ʳ : {X : Obj} → μ ∘ id +₁ ¡ ∘ ρ⇐′ ≈ id {X}
    μ∘¡ʳ = begin
        μ ∘ id +₁ ¡ ∘ ρ⇐′ ≈⟨ pullˡ (sym μ∘+) ⟩
        [ id , ¡ ]′ ∘ ρ⇐′ ≈⟨ inject₁ ⟩
        id                ∎


    μ-natural : {X Y : Obj} {f : X ⇒ Y} → f ∘ μ ≈ μ ∘ f +₁ f
    μ-natural = ∘-distribˡ-[] ○ []-cong₂ (identityʳ ○ sym identityˡ) (identityʳ ○ sym identityˡ) ○ sym []∘+₁

  B∘L : {A B M C : 𝒞.Obj}
      → {f : 𝒞.U [ A , B ]}
      → {g : 𝒞.U [ B , M ]}
      → {h : 𝒞.U [ C , M ]}
      → {s : 𝒟.U [ 𝒟.unit , F.₀ M ]}
      → DecoratedCospans [ DecoratedCospans [ B₁ g h s ∘ L.₁ f ] ≈ B₁ (𝒞.U [ g ∘ f ]) h s ]
  B∘L {A} {B} {M} {C} {f} {g} {h} {s} = record
      { cospans-≈ = Embed.B∘L
      ; same-deco = same-deco
      }
    where

      module _ where
        open 𝒞 using (¡; ⊥; ¡-unique; pushout) renaming ([_,_] to [_,_]′; _+₁_ to infixr 10 _+₁_ )
        open 𝒞 using (U)
        open Category U
        open mc𝒞 using (+-monoidal) public
        open Monoidal +-monoidal using (unitorˡ; unitorˡ-commute-to) public
        open unitorˡ using () renaming (to to λ⇐′) public
        open ⊗-Reasoning +-monoidal
        open ⇒-Reasoning 𝒞.U
        open Equiv

        open Pushout′ 𝒞.U using (pushout-id-g)
        open PushoutProperties 𝒞.U using (up-to-iso)
        open DiagramPushout 𝒞.U using (Pushout)
        P P′ : Pushout 𝒞.id g
        P = pushout 𝒞.id g
        P′ = pushout-id-g
        module P = Pushout P
        module P′ = Pushout P′
        open Morphism 𝒞.U using (_≅_)
        open _≅_ using (from)
        open P using (i₁ ; i₂; universal∘i₂≈h₂) public

        open Codiagonal using (μ; μ-natural; μ∘+; μ∘¡ˡ)

        ≅ : P.Q ⇒ M
        ≅ = up-to-iso P P′ .from

        ≅∘[]∘¡+id : ((≅ ∘ [ i₁ , i₂ ]′) ∘ ¡ +₁ id) ∘ λ⇐′ ≈ id
        ≅∘[]∘¡+id = begin
          ((≅ ∘ [ i₁ , i₂ ]′) ∘ ¡ +₁ id) ∘ λ⇐′  ≈⟨ assoc²αε ⟩
          ≅ ∘ [ i₁ , i₂ ]′ ∘ ¡ +₁ id ∘ λ⇐′      ≈⟨ refl⟩∘⟨ pushˡ μ∘+ ⟩
          ≅ ∘ μ ∘ i₁ +₁ i₂ ∘ ¡ +₁ id ∘ λ⇐′      ≈⟨ refl⟩∘⟨ pull-center (sym split₁ʳ) ⟩
          ≅ ∘ μ ∘ (i₁ ∘ ¡) +₁ i₂ ∘ λ⇐′          ≈⟨ extendʳ μ-natural ⟩
          μ ∘ ≅ +₁ ≅ ∘ (i₁ ∘ ¡) +₁ i₂ ∘ λ⇐′     ≈⟨ pull-center (sym ⊗-distrib-over-∘) ⟩
          μ ∘ (≅ ∘ i₁ ∘ ¡) +₁ (≅ ∘ i₂) ∘ λ⇐′    ≈⟨ refl⟩∘⟨ sym (¡-unique (≅ ∘ i₁ ∘ ¡)) ⟩⊗⟨ universal∘i₂≈h₂ ⟩∘⟨refl ⟩
          μ ∘ ¡ +₁ id ∘ λ⇐′                     ≈⟨ μ∘¡ˡ ⟩
          id                                    ∎

      open 𝒟 using (U; monoidal; _⊗₁_; unitorˡ-commute-from) renaming (module unitorˡ to λ-)
      open 𝒞 using (¡; ⊥; ¡-unique; pushout) renaming ([_,_] to [_,_]′; _+₁_ to infixr 10 _+₁_ )
      open Category U
      open Equiv
      open ⇒-Reasoning U
      open ⊗-Reasoning monoidal
      open F.⊗-homo using () renaming (η to φ; commute to φ-commute)
      open F using (F₁; ε)
      open Shorthands monoidal

      same-deco : F₁ ≅ ∘ F₁ [ i₁ , i₂ ]′ ∘ φ (B , M) ∘ (F₁ ¡ ∘ ε) ⊗₁ s ∘ ρ⇐ ≈ s
      same-deco = begin
          F₁ ≅ ∘ F₁ [ i₁ , i₂ ]′ ∘ φ (B , M) ∘ (F₁ ¡ ∘ ε) ⊗₁ s ∘ ρ⇐                     ≈⟨ pullˡ (sym F.homomorphism) ⟩
          F₁ (≅ 𝒞.∘ [ i₁ , i₂ ]′) ∘ φ (B , M) ∘ (F₁ ¡ ∘ ε) ⊗₁ s ∘ ρ⇐                    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₁ˡ ⟩
          F₁ (≅ 𝒞.∘ [ i₁ , i₂ ]′) ∘ φ (B , M) ∘ F₁ ¡ ⊗₁ id ∘ ε ⊗₁ s ∘ ρ⇐                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ sym F.identity ⟩∘⟨refl ⟩
          F₁ (≅ 𝒞.∘ [ i₁ , i₂ ]′) ∘ φ (B , M) ∘ F₁ ¡ ⊗₁ F₁ 𝒞.id ∘ ε ⊗₁ s ∘ ρ⇐           ≈⟨ refl⟩∘⟨ extendʳ (φ-commute (¡ , 𝒞.id)) ⟩
          F₁ (≅ 𝒞.∘ [ i₁ , i₂ ]′) ∘ F₁ (¡ +₁ 𝒞.id) ∘ φ (⊥ , M) ∘ ε ⊗₁ s ∘ ρ⇐            ≈⟨ pullˡ (sym F.homomorphism) ⟩
          F₁ ((≅ 𝒞.∘ [ i₁ , i₂ ]′) 𝒞.∘ ¡ +₁ 𝒞.id) ∘ φ (⊥ , M) ∘ ε ⊗₁ s ∘ ρ⇐             ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ serialize₁₂ ⟩
          F₁ ((≅ 𝒞.∘ [ i₁ , i₂ ]′) 𝒞.∘ ¡ +₁ 𝒞.id) ∘ φ (⊥ , M) ∘ ε ⊗₁ id ∘ id ⊗₁ s ∘ ρ⇐  ≈⟨ refl⟩∘⟨ extendʳ (switch-fromtoˡ ([ F.F ]-resp-≅ unitorˡ) F.unitaryˡ) ⟩
          F₁ ((≅ 𝒞.∘ [ i₁ , i₂ ]′) 𝒞.∘ ¡ +₁ 𝒞.id) ∘ F₁ λ⇐′ ∘ λ⇒ ∘ id ⊗₁ s ∘ ρ⇐          ≈⟨ pullˡ (sym F.homomorphism) ⟩
          F₁ (((≅ 𝒞.∘ [ i₁ , i₂ ]′) 𝒞.∘ ¡ +₁ 𝒞.id) 𝒞.∘ λ⇐′) ∘ λ⇒ ∘ id ⊗₁ s ∘ ρ⇐         ≈⟨ refl⟩∘⟨ extendʳ unitorˡ-commute-from ⟩
          F₁ (((≅ 𝒞.∘ [ i₁ , i₂ ]′) 𝒞.∘ ¡ +₁ 𝒞.id) 𝒞.∘ λ⇐′) ∘ s ∘ λ⇒ ∘ ρ⇐               ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ coherence-inv₃ monoidal ⟨
          F₁ (((≅ 𝒞.∘ [ i₁ , i₂ ]′) 𝒞.∘ ¡ +₁ 𝒞.id) 𝒞.∘ λ⇐′) ∘ s ∘ λ⇒ ∘ λ⇐               ≈⟨ refl⟩∘⟨ (sym-assoc ○ cancelʳ λ-.isoʳ) ⟩
          F₁ (((≅ 𝒞.∘ [ i₁ , i₂ ]′) 𝒞.∘ ¡ +₁ 𝒞.id) 𝒞.∘ λ⇐′) ∘ s                         ≈⟨ elimˡ (F.F-resp-≈ ≅∘[]∘¡+id ○ F.identity) ⟩
          s                                                                             ∎

  R∘B : {A N B C : 𝒞.Obj}
      → {f : 𝒞.U [ A , N ]}
      → {g : 𝒞.U [ B , N ]}
      → {h : 𝒞.U [ C , B ]}
      → {s : 𝒟.U [ 𝒟.unit , F.₀ N ]}
      → DecoratedCospans [ DecoratedCospans [ R.₁ h ∘ B₁ f g s ] ≈ B₁ f (𝒞.U [ g ∘ h ]) s ]
  R∘B {A} {N} {B} {C} {f} {g} {h} {s} = record
      { cospans-≈ = Embed.R∘B
      ; same-deco = same-deco
      }
    where

      module _ where
        open 𝒞 using (¡; ⊥; ¡-unique; pushout) renaming ([_,_] to [_,_]′; _+₁_ to infixr 10 _+₁_ )
        open 𝒞 using (U)
        open Category U
        open mc𝒞 using (+-monoidal) public
        open Monoidal +-monoidal using (unitorʳ; unitorˡ; unitorˡ-commute-to) public
        open unitorˡ using () renaming (to to λ⇐′) public
        open unitorʳ using () renaming (to to ρ⇐′) public
        open ⊗-Reasoning +-monoidal
        open ⇒-Reasoning 𝒞.U
        open Equiv

        open Pushout′ 𝒞.U using (pushout-f-id)
        open PushoutProperties 𝒞.U using (up-to-iso)
        open DiagramPushout 𝒞.U using (Pushout)
        P P′ : Pushout g 𝒞.id
        P = pushout g 𝒞.id
        P′ = pushout-f-id
        module P = Pushout P
        module P′ = Pushout P′
        open Morphism 𝒞.U using (_≅_)
        open _≅_ using (from)
        open P using (i₁ ; i₂; universal∘i₁≈h₁) public

        open Codiagonal using (μ; μ-natural; μ∘+; μ∘¡ʳ)

        ≅ : P.Q ⇒ N
        ≅ = up-to-iso P P′ .from

        ≅∘[]∘id+¡ : ((≅ ∘ [ i₁ , i₂ ]′) ∘ id +₁ ¡) ∘ ρ⇐′ ≈ id
        ≅∘[]∘id+¡ = begin
          ((≅ ∘ [ i₁ , i₂ ]′) ∘ id +₁ ¡) ∘ ρ⇐′  ≈⟨ assoc²αε ⟩
          ≅ ∘ [ i₁ , i₂ ]′ ∘ id +₁ ¡ ∘ ρ⇐′      ≈⟨ refl⟩∘⟨ pushˡ μ∘+ ⟩
          ≅ ∘ μ ∘ i₁ +₁ i₂ ∘ id +₁ ¡ ∘ ρ⇐′      ≈⟨ refl⟩∘⟨ pull-center merge₂ʳ ⟩
          ≅ ∘ μ ∘ i₁ +₁ (i₂ ∘ ¡) ∘ ρ⇐′          ≈⟨ extendʳ μ-natural ⟩
          μ ∘ ≅ +₁ ≅ ∘ i₁ +₁ (i₂ ∘ ¡) ∘ ρ⇐′     ≈⟨ pull-center (sym ⊗-distrib-over-∘) ⟩
          μ ∘ (≅ ∘ i₁) +₁ (≅ ∘ i₂ ∘ ¡) ∘ ρ⇐′    ≈⟨ refl⟩∘⟨ universal∘i₁≈h₁ ⟩⊗⟨ sym (¡-unique (≅ ∘ i₂ ∘ ¡)) ⟩∘⟨refl ⟩
          μ ∘ id +₁ ¡ ∘ ρ⇐′                     ≈⟨ μ∘¡ʳ ⟩
          id                                    ∎

      open 𝒟 using (U; monoidal; _⊗₁_; unitorʳ-commute-from) renaming (module unitorˡ to λ-; module unitorʳ to ρ)
      open 𝒞 using (¡; ⊥; ¡-unique; pushout) renaming ([_,_] to [_,_]′; _+₁_ to infixr 10 _+₁_ )
      open Category U
      open Equiv
      open ⇒-Reasoning U
      open ⊗-Reasoning monoidal
      open F.⊗-homo using () renaming (η to φ; commute to φ-commute)
      open F using (F₁; ε)
      open Shorthands monoidal

      same-deco : F₁ ≅ ∘ F₁ [ i₁ , i₂ ]′ ∘ φ (N , B) ∘ s ⊗₁ (F₁ ¡ ∘ ε) ∘ ρ⇐ ≈ s
      same-deco = begin
          F₁ ≅ ∘ F₁ [ i₁ , i₂ ]′ ∘ φ (N , B) ∘ s ⊗₁ (F₁ ¡ ∘ ε) ∘ ρ⇐                        ≈⟨ pullˡ (sym F.homomorphism) ⟩
          F₁ (≅ 𝒞.∘ [ i₁ , i₂ ]′) ∘ φ (N , B) ∘ s ⊗₁ (F₁ ¡ ∘ ε) ∘ ρ⇐                       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
          F₁ (≅ 𝒞.∘ [ i₁ , i₂ ]′) ∘ φ (N , B) ∘ id ⊗₁ F₁ ¡ ∘ s ⊗₁ ε ∘ ρ⇐                   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym F.identity ⟩⊗⟨refl ⟩∘⟨refl ⟩
          F₁ (≅ 𝒞.∘ [ i₁ , i₂ ]′) ∘ φ (N , B) ∘ F₁ 𝒞.id ⊗₁ F₁ ¡ ∘ s ⊗₁ ε ∘ ρ⇐              ≈⟨ refl⟩∘⟨ extendʳ (φ-commute (𝒞.id , ¡)) ⟩
          F₁ (≅ 𝒞.∘ [ i₁ , i₂ ]′) ∘ F₁ (𝒞.id +₁ ¡) ∘ φ (N , ⊥) ∘ s ⊗₁ ε ∘ ρ⇐               ≈⟨ pullˡ (sym F.homomorphism) ⟩
          F₁ ((≅ 𝒞.∘ [ i₁ , i₂ ]′) 𝒞.∘ 𝒞.id +₁ ¡) ∘ φ (N , ⊥) ∘ s ⊗₁ ε ∘ ρ⇐                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ serialize₂₁ ⟩
          F₁ ((≅ 𝒞.∘ [ i₁ , i₂ ]′) 𝒞.∘ 𝒞.id +₁ ¡) ∘ φ (N , ⊥) ∘ id ⊗₁ ε ∘ s ⊗₁ id ∘ ρ⇐     ≈⟨ refl⟩∘⟨ extendʳ (switch-fromtoˡ ([ F.F ]-resp-≅ unitorʳ) F.unitaryʳ) ⟩
          F₁ ((≅ 𝒞.∘ [ i₁ , i₂ ]′) 𝒞.∘ 𝒞.id +₁ ¡) ∘ F₁ ρ⇐′ ∘ ρ⇒ ∘ s ⊗₁ id ∘ ρ⇐             ≈⟨ pullˡ (sym F.homomorphism) ⟩
          F₁ (((≅ 𝒞.∘ [ i₁ , i₂ ]′) 𝒞.∘ 𝒞.id +₁ ¡) 𝒞.∘ ρ⇐′) ∘ ρ⇒ ∘ s ⊗₁ id ∘ ρ⇐            ≈⟨ refl⟩∘⟨ extendʳ unitorʳ-commute-from ⟩
          F₁ (((≅ 𝒞.∘ [ i₁ , i₂ ]′) 𝒞.∘ 𝒞.id +₁ ¡) 𝒞.∘ ρ⇐′) ∘ s ∘ ρ⇒ ∘ ρ⇐                  ≈⟨ refl⟩∘⟨ (sym-assoc ○ cancelʳ ρ.isoʳ) ⟩
          F₁ (((≅ 𝒞.∘ [ i₁ , i₂ ]′) 𝒞.∘ 𝒞.id +₁ ¡) 𝒞.∘ ρ⇐′) ∘ s                            ≈⟨ elimˡ (F.F-resp-≈ ≅∘[]∘id+¡ ○ F.identity) ⟩
          s                                                                                ∎

  open Morphism 𝒞.U using (_≅_)
  open _≅_

  ≅-L-R : (X≅Y : A ≅ B) → DecoratedCospans [ L.₁ (to X≅Y) ≈ R.₁ (from X≅Y) ]
  ≅-L-R X≅Y = Decorate.F-resp-≈ (Embed.≅-L-R X≅Y)
    where
      module Decorate = Functor Decorate

  open 𝒞 using (_+₁_)

  L-resp-⊗ : DecoratedCospans [ L.₁ (f +₁ g) ≈ ⊗.₁ (L.₁ f , L.₁ g) ]
  L-resp-⊗ = Decorate.F-resp-≈ Embed.L-resp-⊗ ○ Decorate-resp-⊗
    where
      module Decorate = Functor Decorate
      open DecoratedCospans.HomReasoning
