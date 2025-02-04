{-# OPTIONS --without-K --safe #-}

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
open import Data.Product.Base using (_,_)
open import Function.Base using (id)
open import Functor.Instance.Cospan.Stack using (⊗)

module 𝒞 = FinitelyCocompleteCategory 𝒞
module Cospans = Category Cospans

open 𝒞 using (U; pushout; _+₁_)
open Cospans using (_≈_)
open DiagramPushout U using (Pushout)
open Morphism U using (module ≅; _≅_)
open PushoutProperties U using (up-to-iso)
open Pushout′ U using (pushout-id-g; pushout-f-id)

L₁ : {A B : 𝒞.Obj} → U [ A , B ] → Cospans [ A , B ]
L₁ f = record
    { f₁ = f
    ; f₂ = 𝒞.id
    }

L-identity : {A : 𝒞.Obj} → L₁ 𝒞.id ≈ Cospans.id {A}
L-identity = record
    { ≅N = ≅.refl
    ; from∘f₁≈f₁′ = 𝒞.identity²
    ; from∘f₂≈f₂′ = 𝒞.identity²
    }

L-homomorphism : {X Y Z : 𝒞.Obj} {f : U [ X , Y ]} {g : U [ Y , Z ]} → L₁ (U [ g ∘ f ]) ≈ Cospans [ L₁ g ∘ L₁ f ]
L-homomorphism {X} {Y} {Z} {f} {g} = record
    { ≅N = up-to-iso P′ P
    ; from∘f₁≈f₁′ = pullˡ (P′.universal∘i₁≈h₁ {eq = P.commute})
    ; from∘f₂≈f₂′ = P′.universal∘i₂≈h₂ {eq = P.commute} ○ sym 𝒞.identityʳ
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

L-resp-≈ : {A B : 𝒞.Obj} {f g : U [ A , B ]} → U [ f ≈ g ] → Cospans [ L₁ f ≈ L₁ g ]
L-resp-≈ {A} {B} {f} {g} f≈g = record
    { ≅N = ≅.refl
    ; from∘f₁≈f₁′ = 𝒞.identityˡ ○ f≈g
    ; from∘f₂≈f₂′ = 𝒞.identity²
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

R₁ : {A B : 𝒞.Obj} → U [ B , A ] → Cospans [ A , B ]
R₁ g = record
    { f₁ = 𝒞.id
    ; f₂ = g
    }

R-identity : {A : 𝒞.Obj} → R₁ 𝒞.id ≈ Cospans.id {A}
R-identity = record
    { ≅N = ≅.refl
    ; from∘f₁≈f₁′ = 𝒞.identity²
    ; from∘f₂≈f₂′ = 𝒞.identity²
    }

R-homomorphism : {X Y Z : 𝒞.Obj} {f : U [ Y , X ]} {g : U [ Z , Y ]} → R₁ (U [ f ∘ g ]) ≈ Cospans [ R₁ g ∘ R₁ f ]
R-homomorphism {X} {Y} {Z} {f} {g} = record
    { ≅N = up-to-iso P′ P
    ; from∘f₁≈f₁′ = P′.universal∘i₁≈h₁ {eq = P.commute} ○ sym 𝒞.identityʳ
    ; from∘f₂≈f₂′ = pullˡ (P′.universal∘i₂≈h₂ {eq = P.commute})
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

R-resp-≈ : {A B : 𝒞.Obj} {f g : U [ A , B ]} → U [ f ≈ g ] → Cospans [ R₁ f ≈ R₁ g ]
R-resp-≈ {A} {B} {f} {g} f≈g = record
    { ≅N = ≅.refl
    ; from∘f₁≈f₁′ = 𝒞.identity²
    ; from∘f₂≈f₂′ = 𝒞.identityˡ ○ f≈g
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

B₁ : {A B C : 𝒞.Obj} → U [ A , C ] → U [ B , C ] → Cospans [ A , B ]
B₁ f g = record
    { f₁ = f
    ; f₂ = g
    }

B∘L : {W X Y Z : 𝒞.Obj} {f : U [ W , X ]} {g : U [ X , Y ]} {h : U [ Z , Y ]} → Cospans [ B₁ g h ∘ L₁ f ] ≈ B₁ (U [ g ∘ f ]) h
B∘L {W} {X} {Y} {Z} {f} {g} {h} = record
    { ≅N = up-to-iso P P′
    ; from∘f₁≈f₁′ = pullˡ (P.universal∘i₁≈h₁ {eq = P′.commute})
    ; from∘f₂≈f₂′ = pullˡ (P.universal∘i₂≈h₂ {eq = P′.commute}) ○ 𝒞.identityˡ
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

R∘B : {W X Y Z : 𝒞.Obj} {f : U [ W , X ]} {g : U [ Y , X ]} {h : U [ Z , Y ]} → Cospans [ R₁ h ∘ B₁ f g ] ≈ B₁ f (U [ g ∘ h ])
R∘B {W} {X} {Y} {Z} {f} {g} {h} = record
    { ≅N = up-to-iso P P′
    ; from∘f₁≈f₁′ = pullˡ (P.universal∘i₁≈h₁ {eq = P′.commute}) ○ 𝒞.identityˡ
    ; from∘f₂≈f₂′ = pullˡ (P.universal∘i₂≈h₂ {eq = P′.commute})
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

  ≅-L-R : ∀ {X Y : 𝒞.Obj} (X≅Y : X ≅ Y) → L₁ (to X≅Y) ≈ R₁ (from X≅Y)
  ≅-L-R {X} {Y} X≅Y = record
      { ≅N = X≅Y
      ; from∘f₁≈f₁′ = isoʳ X≅Y
      ; from∘f₂≈f₂′ = 𝒞.identityʳ
      }

module ⊗ = Functor (⊗ 𝒞)

L-resp-⊗ : {X Y X′ Y′ : 𝒞.Obj} {a : U [ X , X′ ]} {b : U [ Y , Y′ ]} → L₁ (a +₁ b) ≈ ⊗.₁ (L₁ a , L₁ b)
L-resp-⊗ {X} {Y} {X′} {Y′} {a} {b} = record
    { ≅N = ≅.refl
    ; from∘f₁≈f₁′ = 𝒞.identityˡ
    ; from∘f₂≈f₂′ = 𝒞.identityˡ ○ sym +-η ○ sym ([]-cong₂ identityʳ identityʳ)
    }
  where
    open 𝒞.HomReasoning
    open 𝒞.Equiv
    open 𝒞 using (+-η; []-cong₂; identityˡ; identityʳ)
