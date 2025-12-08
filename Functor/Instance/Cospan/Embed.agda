{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --hidden-argument-puns #-}

open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)

module Functor.Instance.Cospan.Embed {o ℓ e} (𝒞 : FinitelyCocompleteCategory o ℓ e) where

import Categories.Diagram.Pushout as DiagramPushout
import Categories.Diagram.Pushout.Properties as PushoutProperties
import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as ⇒-Reasoning
import Category.Diagram.Pushout as Pushout′

open import Categories.Category using (_[_,_]; _[_∘_]; _[_≈_])
open import Categories.Category.Core using (Category)
open import Categories.Functor.Core using (Functor)
open import Category.Instance.Cospans 𝒞 using (Cospans)
open import Category.Diagram.Cospan 𝒞 using (cospan)
open import Data.Product.Base using (_,_)
open import Function.Base using (id)
open import Functor.Instance.Cospan.Stack 𝒞 using (⊗)

module 𝒞 = FinitelyCocompleteCategory 𝒞
module Cospans = Category Cospans

open 𝒞 using (U; pushout; _+₁_)
open Cospans using (_≈_)
open DiagramPushout U using (Pushout)
open Morphism U using (module ≅; _≅_)
open PushoutProperties U using (up-to-iso)
open Pushout′ U using (pushout-id-g; pushout-f-id)

private
  variable
    A B C : 𝒞.Obj
    W X Y Z : 𝒞.Obj

L₁ : U [ A , B ] → Cospans [ A , B ]
L₁ f = cospan f 𝒞.id

L-identity : L₁ 𝒞.id ≈ Cospans.id {A}
L-identity = record
    { ≅N = ≅.refl
    ; from∘f₁≈f₁ = 𝒞.identity²
    ; from∘f₂≈f₂ = 𝒞.identity²
    }

L-homomorphism : {f : U [ X , Y ]} {g : U [ Y , Z ]} → L₁ (U [ g ∘ f ]) ≈ Cospans [ L₁ g ∘ L₁ f ]
L-homomorphism {X} {Y} {Z} {f} {g} = record
    { ≅N = up-to-iso P′ P
    ; from∘f₁≈f₁ = pullˡ (P′.universal∘i₁≈h₁ {eq = P.commute})
    ; from∘f₂≈f₂ = P′.universal∘i₂≈h₂ {eq = P.commute} ○ sym 𝒞.identityʳ
    }
  where
    open ⇒-Reasoning U
    open 𝒞.HomReasoning
    open 𝒞.Equiv
    P P′ : Pushout 𝒞.id g
    P = pushout 𝒞.id g
    P′ = pushout-id-g
    module P = Pushout P
    module P′ = Pushout P′

L-resp-≈ : {f g : U [ A , B ]} → U [ f ≈ g ] → Cospans [ L₁ f ≈ L₁ g ]
L-resp-≈ {A} {B} {f} {g} f≈g = record
    { ≅N = ≅.refl
    ; from∘f₁≈f₁ = 𝒞.identityˡ ○ f≈g
    ; from∘f₂≈f₂ = 𝒞.identity²
    }
  where
    open 𝒞.HomReasoning

L : Functor U Cospans
L = record
    { F₀ = id
    ; F₁ = L₁
    ; identity = L-identity
    ; homomorphism = L-homomorphism
    ; F-resp-≈ = L-resp-≈
    }

R₁ : U [ B , A ] → Cospans [ A , B ]
R₁ g = cospan 𝒞.id g

R-identity : R₁ 𝒞.id ≈ Cospans.id {A}
R-identity = record
    { ≅N = ≅.refl
    ; from∘f₁≈f₁ = 𝒞.identity²
    ; from∘f₂≈f₂ = 𝒞.identity²
    }

R-homomorphism : {f : U [ Y , X ]} {g : U [ Z , Y ]} → R₁ (U [ f ∘ g ]) ≈ Cospans [ R₁ g ∘ R₁ f ]
R-homomorphism {f} {g} = record
    { ≅N = up-to-iso P′ P
    ; from∘f₁≈f₁ = P′.universal∘i₁≈h₁ {eq = P.commute} ○ sym 𝒞.identityʳ
    ; from∘f₂≈f₂ = pullˡ (P′.universal∘i₂≈h₂ {eq = P.commute})
    }
  where
    open ⇒-Reasoning U
    open 𝒞.HomReasoning
    open 𝒞.Equiv
    P P′ : Pushout f 𝒞.id
    P = pushout f 𝒞.id
    P′ = pushout-f-id
    module P = Pushout P
    module P′ = Pushout P′

R-resp-≈ : {f g : U [ A , B ]} → U [ f ≈ g ] → Cospans [ R₁ f ≈ R₁ g ]
R-resp-≈ {f} {g} f≈g = record
    { ≅N = ≅.refl
    ; from∘f₁≈f₁ = 𝒞.identity²
    ; from∘f₂≈f₂ = 𝒞.identityˡ ○ f≈g
    }
  where
    open 𝒞.HomReasoning

R : Functor 𝒞.op Cospans
R = record
    { F₀ = id
    ; F₁ = R₁
    ; identity = R-identity
    ; homomorphism = R-homomorphism
    ; F-resp-≈ = R-resp-≈
    }

B∘L : {f : U [ W , X ]} {g : U [ X , Y ]} {h : U [ Z , Y ]} → Cospans [ cospan g h ∘ L₁ f ] ≈ cospan (U [ g ∘ f ]) h
B∘L {f} {g} {h} = record
    { ≅N = up-to-iso P P′
    ; from∘f₁≈f₁ = pullˡ (P.universal∘i₁≈h₁ {eq = P′.commute})
    ; from∘f₂≈f₂ = pullˡ (P.universal∘i₂≈h₂ {eq = P′.commute}) ○ 𝒞.identityˡ
    }
  where
    open ⇒-Reasoning U
    open 𝒞.HomReasoning
    open 𝒞.Equiv
    P P′ : Pushout 𝒞.id g
    P = pushout 𝒞.id g
    P′ = pushout-id-g
    module P = Pushout P
    module P′ = Pushout P′

R∘B : {f : U [ W , X ]} {g : U [ Y , X ]} {h : U [ Z , Y ]} → Cospans [ R₁ h ∘ cospan f g ] ≈ cospan f (U [ g ∘ h ])
R∘B {f} {g} {h} = record
    { ≅N = up-to-iso P P′
    ; from∘f₁≈f₁ = pullˡ (P.universal∘i₁≈h₁ {eq = P′.commute}) ○ 𝒞.identityˡ
    ; from∘f₂≈f₂ = pullˡ (P.universal∘i₂≈h₂ {eq = P′.commute})
    }
  where
    open ⇒-Reasoning U
    open 𝒞.HomReasoning
    open 𝒞.Equiv
    P P′ : Pushout g 𝒞.id
    P = pushout g 𝒞.id
    P′ = pushout-f-id
    module P = Pushout P
    module P′ = Pushout P′

module _ where

  open _≅_

  ≅-L-R : (X≅Y : X ≅ Y) → L₁ (to X≅Y) ≈ R₁ (from X≅Y)
  ≅-L-R X≅Y = record
      { ≅N = X≅Y
      ; from∘f₁≈f₁ = isoʳ X≅Y
      ; from∘f₂≈f₂ = 𝒞.identityʳ
      }

L-resp-⊗ : {a : U [ W , X ]} {b : U [ Y , Z ]} → L₁ (a +₁ b) ≈ ⊗.₁ (L₁ a , L₁ b)
L-resp-⊗ {a} {b} = record
    { ≅N = ≅.refl
    ; from∘f₁≈f₁ = 𝒞.identityˡ
    ; from∘f₂≈f₂ = 𝒞.identityˡ ○ sym +-η ○ sym ([]-cong₂ identityʳ identityʳ)
    }
  where
    open 𝒞.HomReasoning
    open 𝒞.Equiv
    open 𝒞 using (+-η; []-cong₂; identityˡ; identityʳ)
