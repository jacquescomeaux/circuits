{-# OPTIONS --without-K --safe #-}

module Category.Monoidal.Instance.DecoratedCospans.Lift {o ℓ e o′ ℓ′ e′} where

import Categories.Diagram.Pushout as PushoutDiagram
import Categories.Diagram.Pushout.Properties as PushoutProperties
import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as ⇒-Reasoning
import Category.Diagram.Pushout as PushoutDiagram′
import Functor.Instance.DecoratedCospan.Embed as CospanEmbed

open import Categories.Category using (Category; _[_,_]; _[_≈_]; _[_∘_]; module Definitions)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Hom using (Hom[_][_,-])
open import Categories.Functor.Properties using ([_]-resp-≅)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ᵥ_)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; _≃_; _ⓘˡ_)
open import Categories.NaturalTransformation.Equivalence using () renaming (_≃_ to _≋_)
open import Function.Bundles using (_⟨$⟩_)
open import Function.Construct.Composition using () renaming (function to _∘′_)
open import Functor.Exact using (RightExactFunctor; IsPushout⇒Pushout)

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory; SymmetricMonoidalCategory)
open import Categories.Functor.Monoidal.Symmetric using (module Lax)
open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)
open import Category.Instance.Cospans using (Cospans; Cospan)
open import Category.Instance.DecoratedCospans using (DecoratedCospans)
open import Category.Monoidal.Instance.Cospans.Lift {o} {ℓ} {e} using () renaming (module Square to Square′)
open import Cospan.Decorated using (DecoratedCospan)

open Lax using (SymmetricMonoidalFunctor)
open FinitelyCocompleteCategory
  using ()
  renaming (symmetricMonoidalCategory to smc)

module _
  {𝒞 : FinitelyCocompleteCategory o ℓ e}
  {𝒟 : FinitelyCocompleteCategory o ℓ e}
  {𝒥 : SymmetricMonoidalCategory o′ ℓ′ e′}
  {𝒦 : SymmetricMonoidalCategory o′ ℓ′ e′}
  {H : SymmetricMonoidalFunctor (smc 𝒞) 𝒥}
  {I : SymmetricMonoidalFunctor (smc 𝒟) 𝒦} where

  module 𝒞 = FinitelyCocompleteCategory 𝒞
  module 𝒟 = FinitelyCocompleteCategory 𝒟
  module 𝒥 = SymmetricMonoidalCategory 𝒥
  module 𝒦 = SymmetricMonoidalCategory 𝒦
  module H = SymmetricMonoidalFunctor H
  module I = SymmetricMonoidalFunctor I

  open CospanEmbed 𝒟 I using (L; B₁; B∘L; R∘B; ≅-L-R)
  open NaturalIsomorphism using (F⇐G)

  module Square
    {F G : Functor 𝒞.U 𝒟.U}
    (F≃G : F ≃ G)
    (⇒H≃I∘F : NaturalTransformation (Hom[ 𝒥.U ][ 𝒥.unit ,-] ∘F H.F) (Hom[ 𝒦.U ][ 𝒦.unit ,-] ∘F I.F ∘F F))
    (⇒H≃I∘G : NaturalTransformation (Hom[ 𝒥.U ][ 𝒥.unit ,-] ∘F H.F) (Hom[ 𝒦.U ][ 𝒦.unit ,-] ∘F I.F ∘F G))
    (≋ : (F⇐G (Hom[ 𝒦.U ][ 𝒦.unit ,-] ⓘˡ (I.F ⓘˡ F≃G))) ∘ᵥ ⇒H≃I∘G ≋ ⇒H≃I∘F)
    where

    module F = Functor F
    module G = Functor G
    module ⇒H≃I∘F = NaturalTransformation ⇒H≃I∘F
    module ⇒H≃I∘G = NaturalTransformation ⇒H≃I∘G

    open NaturalIsomorphism F≃G

    IF≃IG : I.F ∘F F ≃ I.F ∘F G
    IF≃IG = I.F ⓘˡ F≃G

    open Morphism using (module ≅) renaming (_≅_ to _[_≅_])
    FX≅GX′ : ∀ {Z : 𝒞.Obj} → DecoratedCospans 𝒟 I [ F.₀ Z ≅ G.₀ Z ]
    FX≅GX′ = [ L ]-resp-≅ FX≅GX
    module FX≅GX {Z} = _[_≅_] (FX≅GX {Z})
    module FX≅GX′ {Z} = _[_≅_] (FX≅GX′ {Z})

    module _ {X Y : 𝒞.Obj} (fg : DecoratedCospans 𝒞 H [ X , Y ]) where

      open DecoratedCospan fg renaming (f₁ to f; f₂ to g; decoration to s)
      open 𝒟 using (_∘_)

      squares⇒cospan
          : DecoratedCospans 𝒟 I
              [ B₁ (G.₁ f ∘ FX≅GX.from) (G.₁ g ∘ FX≅GX.from) (⇒H≃I∘G.η N ⟨$⟩ s)
              ≈ B₁ (F.₁ f) (F.₁ g) (⇒H≃I∘F.η N ⟨$⟩ s)
              ]
      squares⇒cospan = record
          { cospans-≈ = Square′.squares⇒cospan F≃G cospan
          ; same-deco = refl⟩∘⟨ sym 𝒦.identityʳ ○ ≋
          }
        where
          open 𝒦.HomReasoning
          open 𝒦.Equiv

      module Cospans = Category (DecoratedCospans 𝒟 I)

      from : DecoratedCospans 𝒟 I
          [ DecoratedCospans 𝒟 I [ L.₁ (⇒.η Y) ∘ B₁ (F.₁ f) (F.₁ g) (⇒H≃I∘F.η N ⟨$⟩ s) ]
          ≈ DecoratedCospans 𝒟 I [ B₁ (G.₁ f) (G.₁ g) (⇒H≃I∘G.η N ⟨$⟩ s) ∘ L.₁ (⇒.η X) ]
          ]
      from = sym (switch-tofromˡ FX≅GX′ (refl⟩∘⟨ B∘L ○ ≅-L-R FX≅GX ⟩∘⟨refl ○ R∘B ○ squares⇒cospan))
        where
          open Cospans.Equiv using (sym)
          open ⇒-Reasoning (DecoratedCospans 𝒟 I) using (switch-tofromˡ)
          open Cospans.HomReasoning using (refl⟩∘⟨_; _○_; _⟩∘⟨refl)

      to : DecoratedCospans 𝒟 I
          [ DecoratedCospans 𝒟 I [ L.₁ (⇐.η Y) ∘ B₁ (G.₁ f) (G.₁ g) (⇒H≃I∘G.η N ⟨$⟩ s) ] ≈ DecoratedCospans 𝒟 I [ B₁ (F.₁ f) (F.₁ g) (⇒H≃I∘F.η N ⟨$⟩ s) ∘ L.₁ (⇐.η X) ]
          ]
      to = switch-fromtoʳ FX≅GX′ (pullʳ B∘L ○ ≅-L-R FX≅GX ⟩∘⟨refl ○ R∘B ○ squares⇒cospan)
        where
          open ⇒-Reasoning (DecoratedCospans 𝒟 I) using (pullʳ; switch-fromtoʳ)
          open Cospans.HomReasoning using (refl⟩∘⟨_; _○_; _⟩∘⟨refl)
