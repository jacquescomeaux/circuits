{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Functor.Monoidal.Symmetric using (module Lax)
open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)

open Lax using (SymmetricMonoidalFunctor)
open FinitelyCocompleteCategory
  using ()
  renaming (symmetricMonoidalCategory to smc)

module Functor.Instance.DecoratedCospan.Stack
    {o o′ ℓ ℓ′ e e′}
    (𝒞 : FinitelyCocompleteCategory o ℓ e)
    {𝒟 : SymmetricMonoidalCategory o′ ℓ′ e′}
    (F : SymmetricMonoidalFunctor (smc 𝒞) 𝒟) where

import Categories.Diagram.Pushout as DiagramPushout
import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as ⇒-Reasoning
import Categories.Category.Monoidal.Reasoning as ⊗-Reasoning

import Functor.Instance.Cospan.Stack 𝒞 as Stack

open import Categories.Category using (Category; _[_,_]; _[_≈_]; _[_∘_])
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Monoidal.Utilities using (module Shorthands)
open import Categories.Category.Monoidal.Properties using (coherence-inv₃)
open import Categories.Category.Monoidal.Braided.Properties using (braiding-coherence-inv)
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Functor.Properties using ([_]-resp-≅)
open import Categories.Category.Cocartesian using (module CocartesianMonoidal; module CocartesianSymmetricMonoidal)
open import Categories.Object.Initial using (Initial)
open import Categories.Object.Duality using (Coproduct⇒coProduct)
open import Category.Instance.DecoratedCospans 𝒞 F using () renaming (DecoratedCospans to Cospans; _≈_ to _≈_′)

import Category.Diagram.Cospan 𝒞 as Cospan

open import Cospan.Decorated 𝒞 F using (DecoratedCospan)
open import Data.Product.Base using (_,_)

module 𝒞 = FinitelyCocompleteCategory 𝒞
module 𝒟 = SymmetricMonoidalCategory 𝒟
module F = SymmetricMonoidalFunctor F
module Cospans = Category Cospans

open 𝒞 using (Obj; _+_; cocartesian)

module mc𝒞 = CocartesianMonoidal 𝒞.U cocartesian
module smc𝒞 = CocartesianSymmetricMonoidal 𝒞.U cocartesian

open DiagramPushout 𝒞.U using (Pushout)

private
  variable
    A A′ B B′ C C′ : Obj

together : Cospans [ A , B ] → Cospans [ A′ , B′ ] → Cospans [ A + A′ , B + B′ ]
together A⇒B A⇒B′ = record
    { cospan = A⇒B.cospan Cospan.⊗ A⇒B′.cospan
    ; decoration = ⊗-homo.η (A⇒B.N , A⇒B′.N) ∘ A⇒B.decoration ⊗₁ A⇒B′.decoration ∘ unitorʳ.to
    }
  where
    module A⇒B = DecoratedCospan A⇒B
    module A⇒B′ = DecoratedCospan A⇒B′
    open 𝒟 using (_∘_; _⊗₁_; module unitorʳ)
    open F using (module ⊗-homo)

id⊗id≈id : Cospans [ together (Cospans.id {A}) (Cospans.id {B}) ≈ Cospans.id ]
id⊗id≈id {A} {B} = record
    { cospans-≈ = Stack.id⊗id≈id
    ; same-deco = F.identity ⟩∘⟨refl
        ○ identityˡ
        ○ refl⟩∘⟨ ⊗-distrib-over-∘ ⟩∘⟨refl
        ○ extendʳ (extendʳ (⊗-homo.commute (! , !)))
        ○ refl⟩∘⟨ pullʳ (pushˡ serialize₂₁ ○ refl⟩∘⟨ sym unitorʳ-commute-to)
        ○ pushˡ (F-resp-≈ !+!≈! ○ homomorphism)
        ○ refl⟩∘⟨ (refl⟩∘⟨ sym-assoc ○ pullˡ unitaryʳ ○ cancelˡ unitorʳ.isoʳ)
    }
  where
    open 𝒞 using (_+₁_; ¡-unique)
    open 𝒟 using (identityˡ; U; monoidal; module unitorʳ; unitorʳ-commute-to; assoc; sym-assoc)
    open 𝒟.Equiv
    open ⇒-Reasoning U
    open ⇒-Reasoning 𝒞.U using () renaming (flip-iso to flip-iso′)
    open ⊗-Reasoning monoidal
    open F using (module ⊗-homo; F-resp-≈; homomorphism; unitaryʳ)
    open 𝒞 using (initial)
    open Initial initial using (!; !-unique₂)
    open Morphism using (_≅_; module ≅)
    open mc𝒞 using (A+⊥≅A)
    module A+⊥≅A = _≅_ A+⊥≅A
    !+!≈! : 𝒞.U [ (! {A} +₁ ! {B}) ≈ ! {A + B} 𝒞.∘ A+⊥≅A.from  ]
    !+!≈! = 𝒞.Equiv.sym (flip-iso′ (≅.sym 𝒞.U A+⊥≅A) (¡-unique ((! +₁ !) 𝒞.∘ A+⊥≅A.to)))

homomorphism
    : (A⇒B : Cospans [ A , B ])
    → (B⇒C : Cospans [ B , C ])
    → (A⇒B′ : Cospans [ A′ ,  B′ ])
    → (B⇒C′ : Cospans [ B′ , C′ ])
    → Cospans
        [ together (Cospans [ B⇒C ∘ A⇒B ]) (Cospans [ B⇒C′ ∘  A⇒B′ ])
        ≈ Cospans [ together B⇒C B⇒C′ ∘ together A⇒B A⇒B′  ]
        ]
homomorphism {A} {B} {C} {A′} {B′} {C′} f g f′ g′ = record
    { cospans-≈ = cospans-≈
    ; same-deco = same-deco
    }
  where

    module _ where
      open DecoratedCospan using (cospan)
      cospans-≈ : _ Cospan.⊗ _ Cospan.≈ Cospan.compose (_ Cospan.⊗ _) (_ Cospan.⊗ _)
      cospans-≈ = Stack.homomorphism (f .cospan) (g .cospan) (f′ .cospan) (g′ .cospan)
      open Cospan._≈_ cospans-≈ using () renaming (≅N to Q+Q′≅Q″) public

    module DecorationNames where
      open DecoratedCospan f using (N) renaming (decoration to s) public
      open DecoratedCospan g using () renaming (decoration to t; N to M) public
      open DecoratedCospan f′ using () renaming (decoration to s′; N to N′) public
      open DecoratedCospan g′ using () renaming (decoration to t′; N to M′) public

    module PushoutNames where
      open DecoratedCospan using (f₁; f₂)
      open 𝒞 using (pushout)
      open Pushout (pushout (f .f₂) (g .f₁)) using (i₁; i₂; Q) public
      open Pushout (pushout (f′ .f₂) (g′ .f₁)) using () renaming (i₁ to i₁′; i₂ to i₂′; Q to Q′) public
      open Pushout (pushout (together f f′ .f₂) (together g g′ .f₁))
        using (universal∘i₁≈h₁; universal∘i₂≈h₂)
        renaming (i₁ to i₁″; i₂ to i₂″; Q to Q″) public

    module _ where

      open DecorationNames
      open PushoutNames
      open F.⊗-homo using () renaming (η to φ; commute to φ-commute)

      open 𝒞 using () renaming ([_,_] to [_,_]′)

      module _ where

        open 𝒞
          using (U; +-swap; inject₁; inject₂; +-η)
          renaming (i₁ to ι₁; i₂ to ι₂; _+₁_ to infixr 10 _+₁_)
        open Category U hiding (Obj)
        open Equiv
        open Shorthands mc𝒞.+-monoidal
        open ⊗-Reasoning mc𝒞.+-monoidal
        open ⇒-Reasoning U
        open mc𝒞 using (assoc-commute-from; assoc-commute-to; module ⊗; associator)
        open smc𝒞 using () renaming (module braiding to σ)

        module Codiagonal where

          open 𝒞 using (coproduct; +-unique; []-cong₂; []∘+₁; ∘-distribˡ-[])
          μ : {X : Obj} → X + X ⇒ X
          μ = [ id , id ]′

          μ∘+ : {X Y Z : Obj} {f : X ⇒ Z} {g : Y ⇒ Z} → [ f , g ]′ ≈ μ ∘ f +₁ g
          μ∘+ = []-cong₂ (sym identityˡ) (sym identityˡ) ○ sym []∘+₁

          μ∘σ : {X : Obj} → μ ∘ +-swap ≈ μ {X}
          μ∘σ = sym (+-unique (pullʳ inject₁ ○ inject₂) (pullʳ inject₂ ○ inject₁) )

          op-binaryProducts : BinaryProducts op
          op-binaryProducts = record { product = Coproduct⇒coProduct U coproduct }

          module op-binaryProducts = BinaryProducts op-binaryProducts
          open op-binaryProducts using () renaming (assocʳ∘⟨⟩ to []∘assocˡ)

          μ-assoc : {X : Obj} → μ {X} ∘ μ +₁ (id {X}) ≈ μ ∘ (id {X}) +₁ μ ∘ α⇒
          μ-assoc = begin
              μ ∘ μ +₁ id                   ≈⟨ μ∘+ ⟨
              [ [ id , id ]′ , id ]′        ≈⟨ []∘assocˡ ⟨
              [ id , [ id , id ]′ ]′ ∘ α⇒   ≈⟨ pushˡ μ∘+ ⟩
              μ ∘ id +₁ μ  ∘ α⇒             ∎

          μ-natural : {X Y : Obj} {f : X ⇒ Y} → f ∘ μ ≈ μ ∘ f +₁ f
          μ-natural = ∘-distribˡ-[] ○ []-cong₂ (identityʳ ○ sym identityˡ) (identityʳ ○ sym identityˡ) ○ sym []∘+₁

        open Codiagonal

        ≅ : Q + Q′ ⇒ Q″
        ≅ = Q+Q′≅Q″.from

        ≅∘[]+[]≈μ∘μ+μ : ≅ ∘ [ i₁ , i₂ ]′ +₁ [ i₁′ , i₂′ ]′ ≈ (μ ∘ (μ +₁ μ)) ∘ ((i₁″ ∘ ι₁) +₁ (i₂″ ∘ ι₁)) +₁ ((i₁″ ∘ ι₂) +₁ (i₂″ ∘ ι₂))
        ≅∘[]+[]≈μ∘μ+μ = begin
            ≅ ∘ [ i₁ , i₂ ]′ +₁ [ i₁′ , i₂′ ]′                                                  ≈⟨ refl⟩∘⟨ μ∘+ ⟩⊗⟨ μ∘+ ⟩
            ≅ ∘ (μ ∘ i₁ +₁ i₂) +₁ (μ ∘ i₁′ +₁ i₂′)                                              ≈⟨ refl⟩∘⟨ introˡ +-η ⟩
            ≅ ∘ [ ι₁ , ι₂ ]′ ∘ (μ ∘ i₁ +₁ i₂) +₁ (μ ∘ i₁′ +₁ i₂′)                               ≈⟨ push-center μ∘+ ⟩
            ≅ ∘ μ ∘ (ι₁ +₁ ι₂) ∘ (μ ∘ i₁ +₁ i₂) +₁ (μ ∘ i₁′ +₁ i₂′)                             ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym ⊗-distrib-over-∘ ⟩
            ≅ ∘ μ ∘ (ι₁ ∘ μ ∘ i₁ +₁ i₂) +₁ (ι₂ ∘ μ ∘ i₁′ +₁ i₂′)                                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (extendʳ μ-natural) ⟩⊗⟨ (extendʳ μ-natural) ⟩
            ≅ ∘ μ ∘ (μ ∘ ι₁ +₁ ι₁ ∘ i₁ +₁ i₂) +₁ (μ ∘ ι₂ +₁ ι₂ ∘ i₁′ +₁ i₂′)                    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩∘⟨ sym ⊗-distrib-over-∘) ⟩⊗⟨ (refl⟩∘⟨ sym ⊗-distrib-over-∘) ⟩
            ≅ ∘ μ ∘ (μ ∘ (ι₁ ∘ i₁) +₁ (ι₁ ∘ i₂)) +₁ (μ ∘ (ι₂ ∘ i₁′) +₁ (ι₂ ∘ i₂′))              ≈⟨ extendʳ μ-natural ⟩
            μ ∘ ≅ +₁ ≅ ∘ (μ ∘ _) +₁ (μ ∘ _)                                                     ≈⟨ refl⟩∘⟨ sym ⊗-distrib-over-∘ ⟩
            μ ∘ (≅ ∘ μ ∘ _) +₁ (≅ ∘ μ ∘ _)                                                      ≈⟨ refl⟩∘⟨ extendʳ μ-natural ⟩⊗⟨ extendʳ μ-natural  ⟩
            μ ∘ (μ ∘ ≅ +₁ ≅ ∘ _) +₁ (μ ∘ ≅ +₁ ≅ ∘ _)                                            ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ sym ⊗-distrib-over-∘) ⟩⊗⟨ (refl⟩∘⟨ sym ⊗-distrib-over-∘) ⟩
            μ ∘ (μ ∘ (≅ ∘ ι₁ ∘ i₁) +₁ (≅ ∘ ι₁ ∘ i₂)) +₁ (μ ∘ (≅ ∘ ι₂ ∘ i₁′) +₁ (≅ ∘ ι₂ ∘ i₂′))  ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ eq₁ ⟩⊗⟨ eq₂ ) ⟩⊗⟨ (refl⟩∘⟨ eq₃ ⟩⊗⟨ eq₄ ) ⟩
            μ ∘ (μ ∘ (i₁″ ∘ ι₁) +₁ (i₂″ ∘ ι₁)) +₁ (μ ∘ (i₁″ ∘ ι₂) +₁ (i₂″ ∘ ι₂))                ≈⟨ refl⟩∘⟨ ⊗-distrib-over-∘ ⟩
            μ ∘ (μ +₁ μ) ∘ ((i₁″ ∘ ι₁) +₁ (i₂″ ∘ ι₁)) +₁ ((i₁″ ∘ ι₂) +₁ (i₂″ ∘ ι₂))             ≈⟨ sym-assoc ⟩
            (μ ∘ (μ +₁ μ)) ∘ ((i₁″ ∘ ι₁) +₁ (i₂″ ∘ ι₁)) +₁ ((i₁″ ∘ ι₂) +₁ (i₂″ ∘ ι₂))           ∎
          where
            eq₁ : ≅ ∘ ι₁ ∘ i₁ ≈ i₁″ ∘ ι₁
            eq₁ = refl⟩∘⟨ sym inject₁ ○ pullˡ (sym (switch-tofromˡ Q+Q′≅Q″ universal∘i₁≈h₁))
            eq₂ : ≅ ∘ ι₁ ∘ i₂ ≈ i₂″ ∘ ι₁
            eq₂ = refl⟩∘⟨ sym inject₁ ○ pullˡ (sym (switch-tofromˡ Q+Q′≅Q″ universal∘i₂≈h₂))
            eq₃ : ≅ ∘ ι₂ ∘ i₁′ ≈ i₁″ ∘ ι₂
            eq₃ = refl⟩∘⟨ sym inject₂ ○ pullˡ (sym (switch-tofromˡ Q+Q′≅Q″ universal∘i₁≈h₁))
            eq₄ : ≅ ∘ ι₂ ∘ i₂′ ≈ i₂″ ∘ ι₂
            eq₄ = refl⟩∘⟨ sym inject₂ ○ pullˡ (sym (switch-tofromˡ Q+Q′≅Q″ universal∘i₂≈h₂))

        swap-inner : {W X Y Z : Obj} → (W + X) + (Y + Z) ⇒ (W + Y) + (X + Z)
        swap-inner = α⇐ ∘ id +₁ (α⇒ ∘ +-swap +₁ id ∘ α⇐) ∘ α⇒

        swap-inner-natural
            : {W X Y Z W′ X′ Y′ Z′ : Obj}
              {w : W ⇒ W′} {x : X ⇒ X′} {y : Y ⇒ Y′} {z : Z ⇒ Z′}
            → (w +₁ x) +₁ (y +₁ z) ∘ swap-inner
            ≈ swap-inner ∘ (w +₁ y) +₁ (x +₁ z)
        swap-inner-natural {w = w} {x = x} {y = y} {z = z} = begin
           (w +₁ x) +₁ (y +₁ z) ∘ α⇐ ∘ _                                    ≈⟨ extendʳ assoc-commute-to ⟨
           α⇐ ∘ w +₁ (x +₁ _) ∘ id +₁ _ ∘ α⇒                                ≈⟨ pull-center merge₂ʳ ⟩
           α⇐ ∘ w +₁ (x +₁ _ ∘ α⇒ ∘ _) ∘ α⇒                                 ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ extendʳ assoc-commute-from ⟩∘⟨refl ⟨
           α⇐ ∘ w +₁ (α⇒ ∘ (x +₁ y) +₁ z ∘ +-swap +₁ id ∘ α⇐) ∘ α⇒          ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (refl⟩∘⟨ pushˡ split₁ʳ) ⟩∘⟨refl ⟨
           α⇐ ∘ w +₁ (α⇒ ∘ (x +₁ y ∘ +-swap) +₁ z ∘ α⇐) ∘ α⇒                ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (refl⟩∘⟨ σ.⇒.sym-commute _ ⟩⊗⟨refl ⟩∘⟨refl) ⟩∘⟨refl ⟩
           α⇐ ∘ w +₁ (α⇒ ∘ (+-swap ∘ y +₁ x) +₁ z ∘ α⇐) ∘ α⇒                ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ push-center split₁ˡ ⟩∘⟨refl ⟩
           α⇐ ∘ w +₁ (α⇒ ∘ +-swap +₁ id ∘ (y +₁ x) +₁ z ∘ α⇐) ∘ α⇒          ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (refl⟩∘⟨ refl⟩∘⟨ assoc-commute-to) ⟩∘⟨refl ⟨
           α⇐ ∘ w +₁ (α⇒ ∘ +-swap +₁ id ∘ α⇐ ∘ y +₁ (x +₁ z))   ∘ α⇒        ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ assoc²εβ ⟩∘⟨refl ⟩
           α⇐ ∘ w +₁ ((α⇒ ∘ +-swap +₁ id ∘ α⇐) ∘ y +₁ (x +₁ z)) ∘ α⇒        ≈⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
           α⇐ ∘ id +₁ (α⇒ ∘ +-swap +₁ id ∘ α⇐) ∘ w +₁ (y +₁ (x +₁ z)) ∘ α⇒  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-commute-from ⟨
           α⇐ ∘ id +₁ (α⇒ ∘ +-swap +₁ id ∘ α⇐) ∘ α⇒ ∘ (w +₁ y) +₁ (x +₁ z)  ≈⟨ assoc²εβ ⟩
           swap-inner ∘ (w +₁ y) +₁ (x +₁ z)                                ∎

        μ∘μ+μ∘swap-inner : {X : Obj} → μ {X} ∘ μ +₁ μ ∘ swap-inner ≈ μ ∘ μ +₁ μ {X}
        μ∘μ+μ∘swap-inner = begin
          μ ∘ μ +₁ μ ∘ α⇐ ∘ id +₁ (α⇒ ∘ +-swap +₁ id ∘ α⇐) ∘ α⇒                           ≈⟨ push-center serialize₁₂ ⟩
          μ ∘ μ +₁ id ∘ id +₁ μ ∘ α⇐ ∘ id +₁ (α⇒ ∘ +-swap +₁ id ∘ α⇐) ∘ α⇒                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗.identity ⟩⊗⟨refl ⟩∘⟨refl ⟨
          μ ∘ μ +₁ id ∘ (id +₁ id) +₁ μ ∘ α⇐ ∘ id +₁ (α⇒ ∘ +-swap +₁ id ∘ α⇐) ∘ α⇒        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-to ⟨
          μ ∘ μ +₁ id ∘ α⇐ ∘ id +₁ (id +₁ μ) ∘ id +₁ (α⇒ ∘ +-swap +₁ id ∘ α⇐) ∘ α⇒        ≈⟨ pullˡ μ-assoc ⟩
          (μ ∘ id +₁ μ ∘ α⇒) ∘ α⇐ ∘ id +₁ (id +₁ μ) ∘ id +₁ (α⇒ ∘ +-swap +₁ id ∘ α⇐) ∘ α⇒ ≈⟨ extendʳ (pullʳ (cancelʳ associator.isoʳ)) ⟩
          μ ∘ id +₁ μ ∘ id +₁ (id +₁ μ) ∘ id +₁ (α⇒ ∘ +-swap +₁ id ∘ α⇐) ∘ α⇒             ≈⟨ refl⟩∘⟨ pull-center merge₂ˡ ⟩
          μ ∘ id +₁ μ ∘ id +₁ (id +₁ μ ∘ α⇒ ∘ +-swap +₁ id ∘ α⇐) ∘ α⇒                     ≈⟨ pull-center merge₂ʳ ⟩
          μ ∘ id +₁ (μ ∘ id +₁ μ ∘ α⇒ ∘ +-swap +₁ id ∘ α⇐) ∘ α⇒                           ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ pull-center refl ⟩∘⟨refl ⟩
          μ ∘ id +₁ (μ ∘ (id +₁ μ ∘ α⇒) ∘ +-swap +₁ id ∘ α⇐) ∘ α⇒                         ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ extendʳ μ-assoc ⟩∘⟨refl ⟨
          μ ∘ id +₁ (μ ∘ μ +₁ id ∘ +-swap +₁ id ∘ α⇐) ∘ α⇒                                ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ pull-center (sym split₁ˡ) ⟩∘⟨refl ⟩
          μ ∘ id +₁ (μ ∘ (μ ∘ +-swap) +₁ id ∘ α⇐) ∘ α⇒                                    ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (refl⟩∘⟨ μ∘σ ⟩⊗⟨refl ⟩∘⟨refl) ⟩∘⟨refl ⟩
          μ ∘ id +₁ (μ ∘ μ +₁ id ∘ α⇐) ∘ α⇒                                               ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (sym-assoc ○ flip-iso associator (μ-assoc ○ sym-assoc))  ⟩∘⟨refl ⟩
          μ ∘ id +₁ (μ ∘ id +₁ μ) ∘ α⇒                                                    ≈⟨ push-center split₂ʳ ⟩
          μ ∘ id +₁ μ ∘ id +₁ (id +₁ μ) ∘ α⇒                                              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-commute-from ⟨
          μ ∘ id +₁ μ ∘ α⇒ ∘ (id +₁ id) +₁ μ                                              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗.identity ⟩⊗⟨refl  ⟩
          μ ∘ id +₁ μ ∘ α⇒ ∘ id +₁ μ                                                      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
          μ ∘ (id +₁ μ ∘ α⇒) ∘ id +₁ μ                                                    ≈⟨ extendʳ μ-assoc ⟨
          μ ∘ μ +₁ id ∘ id +₁ μ                                                           ≈⟨ refl⟩∘⟨ serialize₁₂ ⟨
          μ ∘ μ +₁ μ                                                                      ∎

        ≅∘[]+[]∘σ₄ : (Q+Q′≅Q″.from ∘ [ i₁ , i₂ ]′ +₁ [ i₁′ , i₂′ ]′) ∘ swap-inner ≈ [ i₁″ , i₂″ ]′
        ≅∘[]+[]∘σ₄ = begin
          (≅ ∘ [ i₁ , i₂ ]′ +₁ [ i₁′ , i₂′ ]′) ∘ _                                              ≈⟨ pushˡ ≅∘[]+[]≈μ∘μ+μ ⟩
          (μ ∘ (μ +₁ μ)) ∘ ((i₁″ ∘ ι₁) +₁ (i₂″ ∘ ι₁)) +₁ ((i₁″ ∘ ι₂) +₁ (i₂″ ∘ ι₂)) ∘ (α⇐ ∘ _)  ≈⟨ refl⟩∘⟨ swap-inner-natural ⟩
          (μ ∘ (μ +₁ μ)) ∘ swap-inner ∘ _                                                       ≈⟨ pullˡ assoc  ⟩
          (μ ∘ (μ +₁ μ) ∘ swap-inner) ∘ _                                                       ≈⟨ pushˡ μ∘μ+μ∘swap-inner  ⟩
          μ ∘ (μ +₁ μ) ∘ ((i₁″ ∘ ι₁) +₁ (i₁″ ∘ ι₂)) +₁ ((i₂″ ∘ ι₁) +₁ (i₂″ ∘ ι₂))               ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗-distrib-over-∘ ⟩⊗⟨ ⊗-distrib-over-∘ ⟩
          μ ∘ (μ +₁ μ) ∘ (i₁″ +₁ i₁″ ∘ ι₁ +₁ ι₂) +₁ (i₂″ +₁ i₂″ ∘ ι₁ +₁ ι₂)                     ≈⟨ refl⟩∘⟨ ⊗-distrib-over-∘ ⟨
          μ ∘ (μ ∘ i₁″ +₁ i₁″ ∘ ι₁ +₁ ι₂) +₁ (μ ∘ i₂″ +₁ i₂″ ∘ ι₁ +₁ ι₂)                        ≈⟨ refl⟩∘⟨ extendʳ μ-natural ⟩⊗⟨ extendʳ μ-natural ⟨
          μ ∘ (i₁″ ∘ μ ∘ ι₁ +₁ ι₂) +₁ (i₂″ ∘ μ ∘ ι₁ +₁ ι₂)                                      ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ μ∘+) ⟩⊗⟨ (refl⟩∘⟨ μ∘+) ⟨
          μ ∘ (i₁″ ∘ [ ι₁ , ι₂ ]′) +₁ (i₂″ ∘ [ ι₁ , ι₂ ]′)                                      ≈⟨ refl⟩∘⟨ elimʳ +-η ⟩⊗⟨ elimʳ +-η ⟩
          μ ∘ i₁″ +₁ i₂″                                                                        ≈⟨ μ∘+ ⟨
          [ i₁″ , i₂″ ]′                                                                        ∎

      module _ where

        open 𝒟 using (U; _⊗₁_; module ⊗; module unitorˡ; module unitorʳ; monoidal; assoc-commute-from; assoc-commute-to)
        open Category U
        open ⇒-Reasoning U
        open Equiv
        open ⊗-Reasoning monoidal
        open smc𝒞 using () renaming (associator to α)
        open 𝒟 using () renaming (associator to α′)
        open Morphism._≅_

        swap-unit : 𝒟.braiding.⇐.η (𝒟.unit , 𝒟.unit) ≈ 𝒟.id
        swap-unit = cancel-toʳ 𝒟.unitorˡ
            ( braiding-coherence-inv 𝒟.braided
            ○ sym (coherence-inv₃ monoidal)
            ○ sym 𝒟.identityˡ)

        φ-swap-inner : φ (N + M , N′ + M′) ∘ (φ (N , M) ∘ s ⊗₁ t) ⊗₁ (φ (N′ , M′) ∘ s′ ⊗₁ t′)
             ≈ F.F₁ swap-inner ∘ φ (N + N′ , M + M′) ∘ (φ (N , N′) ∘ s ⊗₁ s′) ⊗₁ (φ (M , M′) ∘ t ⊗₁ t′)
        φ-swap-inner = refl⟩∘⟨ ⊗-distrib-over-∘
            ○ extendʳ
              ( insertˡ ([ F.F ]-resp-≅ α .isoˡ) ⟩∘⟨ serialize₁₂
              ○ center (assoc ○ F.associativity)
              ○ refl⟩∘⟨
                  (extendˡ
                    ( refl⟩∘⟨ sym ⊗.identity ⟩⊗⟨refl
                    ○ extendˡ assoc-commute-from
                    ○ ( merge₂ʳ
                      ○ sym F.identity ⟩⊗⟨
                        ( switch-fromtoʳ α′ (assoc ○ (sym F.associativity))
                        ○ ( refl⟩∘⟨
                              ( refl⟩∘⟨
                                  ( switch-fromtoʳ 𝒟.braiding.FX≅GX (sym F.braiding-compat) ⟩⊗⟨refl
                                  ○ assoc ⟩⊗⟨refl
                                  ○ split₁ʳ
                                  ○ refl⟩⊗⟨ sym F.identity ⟩∘⟨refl)
                              ○ extendʳ (φ-commute (_ , 𝒞.id))
                              ○ refl⟩∘⟨
                                  ( refl⟩∘⟨ split₁ˡ
                                  ○ extendʳ (switch-fromtoˡ ([ F.F ]-resp-≅ α) F.associativity))
                              ○ pullˡ (sym F.homomorphism))
                          ○ pullˡ (sym F.homomorphism)) ⟩∘⟨refl
                        ○ assoc)
                      ○ split₂ʳ) ⟩∘⟨refl)
                    ○ ( extendʳ (φ-commute (𝒞.id , _))
                      ○ refl⟩∘⟨
                        ( refl⟩∘⟨ split₂ʳ
                        ○ extendʳ
                          ( refl⟩∘⟨ (refl⟩⊗⟨ assoc ○ split₂ʳ)
                          ○ extendʳ (switch-fromtoʳ α′ (assoc ○ (sym F.associativity)))
                          ○ refl⟩∘⟨
                              ( refl⟩∘⟨ (refl⟩⊗⟨ assoc ○ split₂ʳ)
                              ○ extendʳ assoc-commute-to
                              ○ ⊗.identity ⟩⊗⟨refl ⟩∘⟨refl)
                          ○ extendʳ (assoc ○ refl⟩∘⟨ (assoc ○ refl⟩∘⟨ sym serialize₁₂))))
                      ○ pullˡ (sym F.homomorphism)
                      ○ refl⟩∘⟨ (assoc ○ refl⟩∘⟨ pullʳ merge₂ʳ) ) ⟩∘⟨refl )
              ○ center⁻¹ (sym F.homomorphism) assoc)
            ○ refl⟩∘⟨
              ( pullʳ
                  ( extendˡ assoc-commute-from
                  ○ ( pullʳ
                        ( merge₂ˡ
                        ○ refl⟩⊗⟨
                          ( extendˡ assoc-commute-to
                          ○ ( pullʳ (sym split₁ˡ ○ (𝒟.braiding.⇐.commute (s′ , t) ○ elimʳ swap-unit) ⟩⊗⟨refl)
                            ○ assoc-commute-from ) ⟩∘⟨refl
                          ○ cancelʳ 𝒟.associator.isoʳ))
                    ○ assoc-commute-to) ⟩∘⟨refl
                  ○ cancelʳ 𝒟.associator.isoˡ)
              ○ pullʳ (sym ⊗-distrib-over-∘))

        open Shorthands monoidal

        same-deco
            : (F.₁ Q+Q′≅Q″.from ∘ φ (Q , Q′) ∘ (F.₁ [ i₁ , i₂ ]′ ∘ φ (N , M) ∘ s ⊗₁ t ∘ ρ⇐) ⊗₁ (F.₁ [ i₁′ , i₂′ ]′ ∘ φ (N′ , M′) ∘ s′ ⊗₁ t′ ∘ ρ⇐) ∘ ρ⇐)
            ≈ (F.₁ [ i₁″ , i₂″ ]′ ∘ φ (N + N′ , M + M′) ∘ (φ (N , N′) ∘ s ⊗₁ s′ ∘ ρ⇐) ⊗₁ (φ (M , M′) ∘ t ⊗₁ t′ ∘ ρ⇐) ∘ ρ⇐)
        same-deco =
          refl⟩∘⟨
            ( refl⟩∘⟨ pushˡ ⊗-distrib-over-∘
            ○ extendʳ (φ-commute ([ i₁ , i₂ ]′ , [ i₁′ , i₂′ ]′))
            ○ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩⊗⟨ sym-assoc ⟩∘⟨refl
            ○ refl⟩∘⟨ refl⟩∘⟨ pushˡ ⊗-distrib-over-∘
            ○ refl⟩∘⟨ sym-assoc)
          ○ pullˡ (sym F.homomorphism)
          ○ extendʳ (pushʳ φ-swap-inner)
          ○ (sym F.homomorphism ○ F.F-resp-≈ ≅∘[]+[]∘σ₄) ⟩∘⟨refl
          ○ refl⟩∘⟨
            ( assoc
            ○ refl⟩∘⟨ pullˡ (sym ⊗-distrib-over-∘)
            ○ refl⟩∘⟨ assoc ⟩⊗⟨ assoc ⟩∘⟨refl)

⊗-resp-≈
    : {A A′ B B′ : Obj}
      {f f′ : Cospans [ A , B ]}
      {g g′ : Cospans [ A′ , B′ ]}
    → Cospans [ f ≈ f′ ]
    → Cospans [ g ≈ g′ ]
    → Cospans [ together f g ≈ together f′ g′ ]
⊗-resp-≈ {_} {_} {_} {_} {f} {f′} {g} {g′} ≈f ≈g = record
    { cospans-≈ = Stack.⊗-resp-≈ (≈f .cospans-≈) (≈g .cospans-≈)
    ; same-deco = same-deco
    }
  where

    open _≈_′ using (cospans-≈)

    module SameNames where
      open _≈_′ ≈f using () renaming (same-deco to ≅∘s≈t) public
      open _≈_′ ≈g using () renaming (same-deco to ≅∘s≈t′) public
      open Cospan._≈_ (≈f .cospans-≈) using (module ≅N) public
      open Cospan._≈_ (≈g .cospans-≈) using () renaming (module ≅N to ≅N′) public

    open SameNames

    module DecorationNames where
      open DecoratedCospan f using (N) renaming (decoration to s) public
      open DecoratedCospan f′ using () renaming (decoration to t; N to M) public
      open DecoratedCospan g using () renaming (decoration to s′; N to N′) public
      open DecoratedCospan g′ using () renaming (decoration to t′; N to M′) public

    open DecorationNames

    module _ where
      open 𝒞 using (_⇒_)
      ≅ : N ⇒ M
      ≅ = ≅N.from
      ≅′ : N′ ⇒ M′
      ≅′ = ≅N′.from

    open 𝒞 using (_+₁_)

    module _ where

      open 𝒟 using (U; monoidal; _⊗₁_)
      open Category U
      open Equiv
      open ⇒-Reasoning U
      open ⊗-Reasoning monoidal
      open F.⊗-homo using () renaming (η to φ; commute to φ-commute)
      open F using (F₁)
      open Shorthands monoidal

      same-deco : F₁ (≅ +₁ ≅′) ∘ φ (N , N′) ∘ s ⊗₁ s′ ∘ ρ⇐ ≈ φ (M , M′) ∘ t ⊗₁ t′ ∘ ρ⇐
      same-deco = begin
          F₁ (≅ +₁ ≅′) ∘ φ (N , N′) ∘ s ⊗₁ s′ ∘ ρ⇐      ≈⟨ extendʳ (φ-commute (_ , _)) ⟨
          φ (M , M′) ∘ F₁ ≅ ⊗₁ F₁ ≅′ ∘ s ⊗₁ s′ ∘ ρ⇐     ≈⟨ pull-center (sym ⊗-distrib-over-∘) ⟩
          φ (M , M′) ∘ (F₁ ≅ ∘ s) ⊗₁ (F₁ ≅′ ∘ s′) ∘ ρ⇐  ≈⟨ refl⟩∘⟨ ≅∘s≈t ⟩⊗⟨ ≅∘s≈t′ ⟩∘⟨refl ⟩
          φ (M , M′) ∘ t ⊗₁ t′ ∘ ρ⇐                     ∎

⊗ : Bifunctor Cospans Cospans Cospans
⊗ = record
    { F₀ = λ (A , A′) → A + A′
    ; F₁ = λ (f , g) → together f g
    ; identity = λ { {x , y} → id⊗id≈id {x} {y} }
    ; homomorphism = λ { {_} {_} {_} {A⇒B , A⇒B′} {B⇒C , B⇒C′} → homomorphism A⇒B B⇒C A⇒B′ B⇒C′ }
    ; F-resp-≈ = λ (≈f , ≈g) → ⊗-resp-≈ ≈f ≈g
    }

module ⊗ = Functor ⊗
