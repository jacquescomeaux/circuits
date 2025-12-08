{-# OPTIONS --without-K --safe #-}

open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)

module Category.Monoidal.Instance.Cospans.Lift {o ℓ e} where

open import Category.Instance.Cospans using (Cospans)

open import Categories.Category.Core using (Category)

import Categories.Diagram.Pushout as PushoutDiagram
import Categories.Diagram.Pushout.Properties as PushoutProperties
import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as ⇒-Reasoning
import Category.Diagram.Pushout as PushoutDiagram′
import Functor.Instance.Cospan.Embed as CospanEmbed

open import Categories.Category using (_[_,_]; _[_≈_]; _[_∘_]; module Definitions)
open import Category.Diagram.Cospan using (Cospan; cospan)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor.Properties using ([_]-resp-≅)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; _≃_)
open import Functor.Exact using (RightExactFunctor; IsPushout⇒Pushout)

module _ {𝒞 : FinitelyCocompleteCategory o ℓ e} {𝒟 : FinitelyCocompleteCategory o ℓ e} where

  module 𝒞 = FinitelyCocompleteCategory 𝒞
  module 𝒟 = FinitelyCocompleteCategory 𝒟

  open CospanEmbed 𝒟 using (L; B∘L; R∘B; ≅-L-R)

  module Square {F G : Functor 𝒞.U 𝒟.U} (F≃G : F ≃ G) where

    module L = Functor L
    module F = Functor F
    module G = Functor G

    open NaturalIsomorphism F≃G

    open Morphism using (module ≅) renaming (_≅_ to _[_≅_])
    FX≅GX′ : ∀ {Z : 𝒞.Obj} → Cospans 𝒟 [ F.₀ Z ≅ G.₀ Z ]
    FX≅GX′ = [ L ]-resp-≅ FX≅GX
    module FX≅GX {Z} = _[_≅_] (FX≅GX {Z})
    module FX≅GX′ {Z} = _[_≅_] (FX≅GX′ {Z})

    module _ {X Y : 𝒞.Obj} (fg : Cospans 𝒞 [ X , Y ]) where

      open ⇒-Reasoning (Cospans 𝒟) using (switch-tofromˡ; switch-fromtoʳ)
      open ⇒-Reasoning 𝒟.U using (switch-fromtoˡ)
      module Cospans = Category (Cospans 𝒟)
      open Cospans.HomReasoning using (refl⟩∘⟨_; _○_; _⟩∘⟨refl)
      open Cospan fg renaming (f₁ to f; f₂ to g)
      open 𝒟 using (_∘_)

      squares⇒cospan : Cospans 𝒟 [ cospan (G.₁ f ∘ FX≅GX.from) (G.₁ g ∘ FX≅GX.from) ≈ cospan (F.₁ f) (F.₁ g) ]
      squares⇒cospan = record
          { ≅N = ≅.sym 𝒟.U FX≅GX
          ; from∘f₁≈f₁ = sym (switch-fromtoˡ FX≅GX (⇒.commute f))
          ; from∘f₂≈f₂ = sym (switch-fromtoˡ FX≅GX (⇒.commute g))
          }
        where
          open 𝒟.Equiv using (sym)

      from : Cospans 𝒟 [ Cospans 𝒟 [ L.₁ (⇒.η Y) ∘ cospan (F.₁ f) (F.₁ g) ] ≈ Cospans 𝒟 [ cospan (G.₁ f) (G.₁ g) ∘ L.₁ (⇒.η X) ] ]
      from = sym (switch-tofromˡ FX≅GX′ (refl⟩∘⟨ B∘L ○ ≅-L-R FX≅GX ⟩∘⟨refl ○ R∘B ○ squares⇒cospan))
        where
          open Cospans.Equiv using (sym)

      to : Cospans 𝒟 [ Cospans 𝒟 [ L.₁ (⇐.η Y) ∘ cospan (G.₁ f) (G.₁ g) ] ≈ Cospans 𝒟 [ cospan (F.₁ f) (F.₁ g) ∘ L.₁ (⇐.η X) ] ]
      to = switch-fromtoʳ FX≅GX′ (pullʳ B∘L ○ ≅-L-R FX≅GX ⟩∘⟨refl ○ R∘B ○ squares⇒cospan)
        where
          open ⇒-Reasoning (Cospans 𝒟) using (pullʳ)
