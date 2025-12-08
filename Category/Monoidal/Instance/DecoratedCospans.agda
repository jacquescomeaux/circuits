{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --lossy-unification #-}

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory; SymmetricMonoidalCategory)
open import Categories.Functor.Monoidal.Symmetric using (module Lax)
open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)

open Lax using (SymmetricMonoidalFunctor)
open FinitelyCocompleteCategory
  using ()
  renaming (symmetricMonoidalCategory to smc)

module Category.Monoidal.Instance.DecoratedCospans
    {o o′ ℓ ℓ′ e e′}
    (𝒞 : FinitelyCocompleteCategory o ℓ e)
    {𝒟 : SymmetricMonoidalCategory o′ ℓ′ e′}
    (F : SymmetricMonoidalFunctor (smc 𝒞) 𝒟) where

open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)


import Categories.Category.Monoidal.Reasoning as ⊗-Reasoning
import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as ⇒-Reasoning
import Categories.Category.Monoidal.Properties as ⊗-Properties
import Categories.Category.Monoidal.Braided.Properties as σ-Properties

open import Categories.Category using (_[_,_]; _[_≈_]; _[_∘_]; Category)
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
open import Categories.Category.Cocartesian using (module CocartesianMonoidal; module CocartesianSymmetricMonoidal)
open import Categories.Category.Monoidal.Braided using (Braided)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Monoidal.Utilities using (module Shorthands)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Hom using (Hom[_][_,-])
open import Categories.Functor.Properties using ([_]-resp-≅)
open import Categories.Functor.Monoidal.Construction.Product using (⁂-SymmetricMonoidalFunctor)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; _ⓘˡ_; niHelper)
open import Categories.NaturalTransformation.Core using (NaturalTransformation; _∘ᵥ_; ntHelper)
open import Categories.NaturalTransformation.Equivalence using () renaming (_≃_ to _≋_)
open import Category.Instance.DecoratedCospans 𝒞 F using (DecoratedCospans)
open import Category.Cartesian.Instance.FinitelyCocompletes {o} {ℓ} {e} using (module x+y; module y+x; [x+y]+z; x+[y+z]; assoc-≃)
open import Category.Monoidal.Instance.DecoratedCospans.Lift {o} {ℓ} {e} {o′} {ℓ′} {e′} using (module Square)
open import Cospan.Decorated 𝒞 F using (DecoratedCospan)
open import Data.Product.Base using (_,_)
open import Function.Base using () renaming (id to idf)
open import Functor.Instance.DecoratedCospan.Stack 𝒞 F using (⊗)
open import Functor.Instance.DecoratedCospan.Embed 𝒞 F using (L; L-resp-⊗; B₁)

open import Category.Monoidal.Instance.DecoratedCospans.Products 𝒞 F
open CocartesianMonoidal 𝒞.U 𝒞.cocartesian using (⊥+--id; -+⊥-id; ⊥+A≅A; A+⊥≅A; +-monoidal)
open import Categories.Category.Monoidal.Utilities +-monoidal using (associator-naturalIsomorphism)

module LiftUnitorˡ where
    module F = SymmetricMonoidalFunctor F
    open 𝒞 using (⊥; _+-; i₂; _+_; _+₁_; ¡; +₁-cong₂; ¡-unique; -+-)
    open Shorthands 𝒟.monoidal using (ρ⇒; ρ⇐; λ⇒)
    ≃₁ : NaturalTransformation (Hom[ 𝒟.U ][ 𝒟.unit ,-] ∘F F.F) (Hom[ 𝒟.U ][ 𝒟.unit ,-] ∘F F.F ∘F (⊥ +-))
    ≃₁ = ntHelper record
        { η = λ { X → record
            { to = λ { f → 𝒟.U [ F.⊗-homo.η (⊥ , X) ∘ 𝒟.U [ 𝒟.⊗.₁ (𝒟.U [ F.₁ 𝒞.initial.! ∘ F.ε ] , f) ∘ ρ⇐ ] ] }
            ; cong = λ { x → refl⟩∘⟨ refl⟩⊗⟨ x ⟩∘⟨refl } }
            }
        ; commute = ned
        }
      where
        open 𝒟.Equiv
        open 𝒟 using (sym-assoc; _∘_; id; _⊗₁_; identityʳ)
        open ⊗-Reasoning 𝒟.monoidal
        open ⇒-Reasoning 𝒟.U
        ned : {X Y : 𝒞.Obj} (f : X 𝒞.⇒ Y) {x : 𝒟.unit 𝒟.⇒ F.₀ X}
            → F.⊗-homo.η (⊥ , Y) ∘ (F.₁ ¡ 𝒟.∘ F.ε) ⊗₁ (F.F₁ f ∘ x ∘ id) ∘ ρ⇐
            𝒟.≈ F.₁ (𝒞.id +₁ f) ∘ (F.⊗-homo.η (𝒞.⊥ , X) ∘ (F.₁ ¡ ∘ F.ε) ⊗₁ x ∘ ρ⇐) ∘ id
        ned {X} {Y} f {x} = begin
              F.⊗-homo.η (⊥ , Y) ∘ (F.₁ ¡ ∘ F.ε) ⊗₁ (F.₁ f ∘ x ∘ id) ∘ ρ⇐            ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (refl⟩∘⟨ identityʳ) ⟩∘⟨refl ⟩
              F.⊗-homo.η (⊥ , Y) ∘ (F.₁ ¡ ∘ F.ε) ⊗₁ (F.₁ f ∘ x) ∘ ρ⇐                 ≈⟨ push-center split₂ˡ ⟩
              F.⊗-homo.η (⊥ , Y) ∘ id ⊗₁ F.₁ f ∘ (F.₁ ¡ ∘ F.ε) ⊗₁ x ∘ ρ⇐             ≈⟨ refl⟩∘⟨ F.identity ⟩⊗⟨refl ⟩∘⟨refl ⟨
              F.⊗-homo.η (⊥ , Y) ∘ F.₁ 𝒞.id ⊗₁ F.₁ f ∘ (F.₁ ¡ ∘ F.ε) ⊗₁ x ∘ ρ⇐       ≈⟨ extendʳ (F.⊗-homo.commute (𝒞.id , f)) ⟩
              F.₁ (𝒞.id +₁ f) ∘ F.⊗-homo.η (⊥ , X) ∘ (F.₁ ¡ ∘ F.ε) ⊗₁ x ∘ ρ⇐         ≈⟨ refl⟩∘⟨ identityʳ ⟨
              F.₁ (𝒞.id +₁ f) ∘ (F.⊗-homo.η (⊥ , X) ∘ (F.₁ ¡ ∘ F.ε) ⊗₁ x ∘ ρ⇐) ∘ id  ∎
    ≃₂ : NaturalTransformation (Hom[ 𝒟.U ][ 𝒟.unit ,-] ∘F F.F) (Hom[ 𝒟.U ][ 𝒟.unit ,-] ∘F F.F ∘F idF)
    ≃₂ = ntHelper record
        { η = λ { X → record { to = idf ; cong = idf } }
        ; commute = λ { f → refl }
        }
      where
        open 𝒟.Equiv
    open NaturalIsomorphism using (F⇐G)
    ≃₂≋≃₁ : (F⇐G (Hom[ 𝒟.U ][ 𝒟.unit ,-] ⓘˡ (F.F ⓘˡ ⊥+--id))) ∘ᵥ ≃₂ ≋ ≃₁
    ≃₂≋≃₁ {X} {f} = begin
        F.₁ λ⇐ ∘ f ∘ id                                                 ≈⟨ refl⟩∘⟨ refl⟩∘⟨ 𝒟.unitorʳ.isoʳ ⟨
        F.₁ λ⇐ ∘ f ∘ ρ⇒ ∘ ρ⇐                                            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ coherence₃ ⟩∘⟨refl ⟨
        F.₁ λ⇐ ∘ f ∘ λ⇒ ∘ ρ⇐                                            ≈⟨ refl⟩∘⟨ extendʳ 𝒟.unitorˡ-commute-from ⟨
        F.₁ λ⇐ ∘ λ⇒ ∘ id ⊗₁ f ∘ ρ⇐                                      ≈⟨ pushˡ (introˡ F.identity) ⟩
        F.₁ 𝒞.id ∘ F.₁ λ⇐ ∘ λ⇒ ∘ id ⊗₁ f ∘ ρ⇐                           ≈⟨ F.F-resp-≈ (-+-.identity) ⟩∘⟨refl ⟨
        F.₁ (𝒞.id +₁ 𝒞.id) ∘ F.₁ λ⇐ ∘ λ⇒ ∘ id ⊗₁ f ∘ ρ⇐                 ≈⟨ F.F-resp-≈ (+₁-cong₂ (¡-unique 𝒞.id) 𝒞.Equiv.refl) ⟩∘⟨refl ⟨
        F.₁ (¡ +₁ 𝒞.id) ∘ F.₁ λ⇐ ∘ λ⇒ ∘ id ⊗₁ f ∘ ρ⇐                    ≈⟨ refl⟩∘⟨ extendʳ (switch-fromtoˡ ([ F.F ]-resp-≅ unitorˡ) F.unitaryˡ)  ⟨
        F.₁ (¡ +₁ 𝒞.id) ∘ F.⊗-homo.η (⊥ , X) ∘ F.ε ⊗₁ id ∘ id ⊗₁ f ∘ ρ⇐ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (sym serialize₁₂) ⟩
        F.₁ (¡ +₁ 𝒞.id) ∘ F.⊗-homo.η (⊥ , X) ∘ F.ε ⊗₁ f ∘ ρ⇐            ≈⟨ extendʳ (F.⊗-homo.commute (¡ , 𝒞.id)) ⟨
        F.⊗-homo.η (⊥ , X) ∘ (F.₁ ¡ ⊗₁ F.₁ 𝒞.id) ∘ F.ε ⊗₁ f ∘ ρ⇐        ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ F.identity ⟩∘⟨refl ⟩
        F.⊗-homo.η (⊥ , X) ∘ (F.₁ ¡ ⊗₁ id) ∘ F.ε ⊗₁ f ∘ ρ⇐              ≈⟨ pull-center (sym split₁ˡ) ⟩
        F.⊗-homo.η (⊥ , X) ∘ (F.₁ ¡ ∘ F.ε) ⊗₁ f ∘ ρ⇐                    ∎
      where
        open Shorthands 𝒞.monoidal using (λ⇐)
        open CocartesianMonoidal 𝒞.U 𝒞.cocartesian using (unitorˡ)
        open 𝒟.Equiv
        open 𝒟 using (sym-assoc; _∘_; id; _⊗₁_; identityʳ)
        open ⊗-Reasoning 𝒟.monoidal
        open ⊗-Properties 𝒟.monoidal using (coherence₃)
        open ⇒-Reasoning 𝒟.U
        module -+- = Functor -+-
    module Unitorˡ = Square {𝒞} {𝒞} {𝒟} {𝒟} {F} {F} ⊥+--id ≃₁ ≃₂ ≃₂≋≃₁
open LiftUnitorˡ using (module Unitorˡ)

module LiftUnitorʳ where
    module F = SymmetricMonoidalFunctor F
    open 𝒞 using (⊥; -+_; i₁; _+_; _+₁_; ¡; +₁-cong₂; ¡-unique; -+-)
    open Shorthands 𝒟.monoidal using (ρ⇒; ρ⇐)
    ≃₁ : NaturalTransformation (Hom[ 𝒟.U ][ 𝒟.unit ,-] ∘F F.F) (Hom[ 𝒟.U ][ 𝒟.unit ,-] ∘F F.F ∘F (-+ ⊥))
    ≃₁ = ntHelper record
        { η = λ { X → record
            { to = λ { f → 𝒟.U [ F.⊗-homo.η (X , ⊥) ∘ 𝒟.U [ 𝒟.⊗.₁ (f , 𝒟.U [ F.₁ 𝒞.initial.! ∘ F.ε ]) ∘ ρ⇐ ] ] }
            ; cong = λ { x → refl⟩∘⟨ x ⟩⊗⟨refl ⟩∘⟨refl } }
            }
        ; commute = ned
        }
      where
        open 𝒟.Equiv
        open 𝒟 using (sym-assoc; _∘_; id; _⊗₁_; identityʳ)
        open ⊗-Reasoning 𝒟.monoidal
        open ⇒-Reasoning 𝒟.U
        ned : {X Y : 𝒞.Obj} (f : X 𝒞.⇒ Y) {x : 𝒟.unit 𝒟.⇒ F.₀ X}
            → F.⊗-homo.η (Y , ⊥) ∘ (F.F₁ f ∘ x ∘ id) ⊗₁ (F.₁ ¡ ∘ F.ε) ∘ ρ⇐
            𝒟.≈ F.₁ (f +₁ 𝒞.id) ∘ (F.⊗-homo.η (X , ⊥) ∘ x ⊗₁ (F.₁ ¡ ∘ F.ε) ∘ ρ⇐) ∘ id
        ned {X} {Y} f {x} = begin
              F.⊗-homo.η (Y , ⊥) ∘ (F.₁ f ∘ x ∘ id) ⊗₁ (F.₁ ¡ ∘ F.ε) ∘ ρ⇐             ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ identityʳ) ⟩⊗⟨refl ⟩∘⟨refl ⟩
              F.⊗-homo.η (Y , ⊥) ∘ (F.₁ f ∘ x) ⊗₁ (F.₁ ¡ ∘ F.ε) ∘ ρ⇐                  ≈⟨ push-center split₁ˡ ⟩
              F.⊗-homo.η (Y , ⊥) ∘ F.₁ f ⊗₁ id ∘ x ⊗₁ (F.₁ ¡ ∘ F.ε) ∘ ρ⇐              ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ F.identity ⟩∘⟨refl ⟨
              F.⊗-homo.η (Y , ⊥) ∘ F.₁ f ⊗₁ F.₁ 𝒞.id ∘ x ⊗₁ (F.₁ ¡ ∘ F.ε) ∘ ρ⇐        ≈⟨ extendʳ (F.⊗-homo.commute (f , 𝒞.id)) ⟩
              F.₁ (f +₁ 𝒞.id) ∘ F.⊗-homo.η (X , ⊥) ∘ x ⊗₁ (F.₁ ¡ ∘ F.ε) ∘ ρ⇐          ≈⟨ refl⟩∘⟨ identityʳ ⟨
              F.₁ (f +₁ 𝒞.id) ∘ (F.⊗-homo.η (X , ⊥) ∘ x ⊗₁ (F.₁ ¡ ∘ F.ε) ∘ ρ⇐) ∘ id   ∎
    ≃₂ : NaturalTransformation (Hom[ 𝒟.U ][ 𝒟.unit ,-] ∘F F.F) (Hom[ 𝒟.U ][ 𝒟.unit ,-] ∘F F.F ∘F idF)
    ≃₂ = ntHelper record
        { η = λ { X → record { to = idf ; cong = idf } }
        ; commute = λ { f → refl }
        }
      where
        open 𝒟.Equiv
    open NaturalIsomorphism using (F⇐G)
    ≃₂≋≃₁ : (F⇐G (Hom[ 𝒟.U ][ 𝒟.unit ,-] ⓘˡ (F.F ⓘˡ -+⊥-id))) ∘ᵥ ≃₂ ≋ ≃₁
    ≃₂≋≃₁ {X} {f} = begin
        F.₁ i₁ ∘ f ∘ id                                                 ≈⟨ refl⟩∘⟨ refl⟩∘⟨ 𝒟.unitorʳ.isoʳ ⟨
        F.₁ ρ⇐′ ∘ f ∘ ρ⇒ ∘ ρ⇐                                           ≈⟨ refl⟩∘⟨ extendʳ 𝒟.unitorʳ-commute-from ⟨
        F.₁ ρ⇐′ ∘ ρ⇒ ∘ f ⊗₁ id ∘ ρ⇐                                     ≈⟨ pushˡ (introˡ F.identity) ⟩
        F.₁ 𝒞.id ∘ F.₁ ρ⇐′ ∘ ρ⇒ ∘ f ⊗₁ id ∘ ρ⇐                          ≈⟨ F.F-resp-≈ (-+-.identity) ⟩∘⟨refl ⟨
        F.₁ (𝒞.id +₁ 𝒞.id) ∘ F.₁ ρ⇐′ ∘ ρ⇒ ∘ f ⊗₁ id ∘ ρ⇐                ≈⟨ F.F-resp-≈ (+₁-cong₂ 𝒞.Equiv.refl (¡-unique 𝒞.id)) ⟩∘⟨refl ⟨
        F.₁ (𝒞.id +₁ ¡) ∘ F.₁ ρ⇐′ ∘ ρ⇒ ∘ f ⊗₁ id ∘ ρ⇐                   ≈⟨ refl⟩∘⟨ extendʳ (switch-fromtoˡ ([ F.F ]-resp-≅ unitorʳ) F.unitaryʳ)  ⟨
        F.₁ (𝒞.id +₁ ¡) ∘ F.⊗-homo.η (X , ⊥) ∘ id ⊗₁ F.ε ∘ f ⊗₁ id ∘ ρ⇐ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (sym serialize₂₁) ⟩
        F.₁ (𝒞.id +₁ ¡) ∘ F.⊗-homo.η (X , ⊥) ∘ f ⊗₁ F.ε ∘ ρ⇐            ≈⟨ extendʳ (F.⊗-homo.commute (𝒞.id , ¡)) ⟨
        F.⊗-homo.η (X , ⊥) ∘ (F.₁ 𝒞.id ⊗₁ F.₁ ¡) ∘ f ⊗₁ F.ε ∘ ρ⇐        ≈⟨ refl⟩∘⟨ F.identity ⟩⊗⟨refl ⟩∘⟨refl ⟩
        F.⊗-homo.η (X , ⊥) ∘ (id ⊗₁ F.₁ ¡) ∘ f ⊗₁ F.ε ∘ ρ⇐              ≈⟨ pull-center (sym split₂ˡ) ⟩
        F.⊗-homo.η (X , ⊥) ∘ f ⊗₁ (F.₁ ¡ ∘ F.ε) ∘ ρ⇐                    ∎
      where
        open Shorthands 𝒞.monoidal using () renaming (ρ⇐ to ρ⇐′)
        open CocartesianMonoidal 𝒞.U 𝒞.cocartesian using (unitorʳ)
        open 𝒟.Equiv
        open 𝒟 using (sym-assoc; _∘_; id; _⊗₁_; identityʳ)
        open ⊗-Reasoning 𝒟.monoidal
        open ⇒-Reasoning 𝒟.U
        module -+- = Functor -+-
    module Unitorʳ = Square {𝒞} {𝒞} {𝒟} {𝒟} {F} {F} -+⊥-id ≃₁ ≃₂ ≃₂≋≃₁
open LiftUnitorʳ using (module Unitorʳ)

module LiftAssociator where
    module F = SymmetricMonoidalFunctor F
    open 𝒞 using (⊥; -+_; i₁; _+_; _+₁_; ¡; +₁-cong₂; ¡-unique; -+-)
    open Shorthands 𝒟.monoidal using (ρ⇒; ρ⇐)
    ≃₁ : NaturalTransformation (Hom[ [𝒟×𝒟]×𝒟.U ][ [𝒟×𝒟]×𝒟.unit ,-] ∘F [F×F]×F.F) (Hom[ 𝒟.U ][ 𝒟.unit ,-] ∘F F.F ∘F ([x+y]+z.F {𝒞}))
    ≃₁ = ntHelper record
        { η = λ { ((X , Y) , Z) → record
            { to = λ { ((f , g) , h) → F.⊗-homo.η (X + Y , Z) ∘ ((F.⊗-homo.η (X , Y) ∘ f ⊗₁ g ∘ ρ⇐) ⊗₁ h) ∘ ρ⇐ }
            ; cong = λ { {(f , g) , h} {(f′ , g′) , h′} ((x , y) , z) → refl⟩∘⟨ (refl⟩∘⟨ x ⟩⊗⟨ y ⟩∘⟨refl) ⟩⊗⟨ z ⟩∘⟨refl }
            } }
        ; commute = λ { {(X , Y) , Z} {(X′ , Y′) , Z′} ((x , y) , z) {(f , g) , h} → commute x y z f g h }
        }
      where
        open 𝒟.Equiv
        open 𝒟 using (sym-assoc; _∘_; id; _⊗₁_; identityʳ; _≈_)
        open ⊗-Reasoning 𝒟.monoidal
        open ⇒-Reasoning 𝒟.U
        commute
            : {X Y Z X′ Y′ Z′ : 𝒞.Obj}
              (x : 𝒞.U [ X , X′ ])
              (y : 𝒞.U [ Y , Y′ ])
              (z : 𝒞.U [ Z , Z′ ])
              (f : 𝒟.U [ 𝒟.unit , F.₀ X ])
              (g : 𝒟.U [ 𝒟.unit , F.₀ Y ])
              (h : 𝒟.U [ 𝒟.unit , F.₀ Z ])
            → F.⊗-homo.η (X′ + Y′ , Z′) ∘ (F.⊗-homo.η (X′ , Y′) ∘ (F.₁ x ∘ f ∘ id) ⊗₁ (F.₁ y ∘ g ∘ id) ∘ ρ⇐) ⊗₁ (F.₁ z ∘ h ∘ id) ∘ ρ⇐
            ≈ F.₁ ((x +₁ y) +₁ z) ∘ (F.⊗-homo.η (X + Y , Z) ∘ (F.⊗-homo.η (X , Y) ∘ f ⊗₁ g ∘ ρ⇐) ⊗₁ h ∘ ρ⇐) ∘ id
        commute {X} {Y} {Z} {X′} {Y′} {Z′} x y z f g h = begin
            F.⊗-homo.η (X′ + Y′ , Z′) ∘ (F.⊗-homo.η (X′ , Y′) ∘ (F.₁ x ∘ f ∘ id) ⊗₁ (F.₁ y ∘ g ∘ id) ∘ ρ⇐) ⊗₁ (F.₁ z ∘ h ∘ id) ∘ ρ⇐
                ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨ identityʳ) ⟩⊗⟨ (refl⟩∘⟨ identityʳ) ⟩∘⟨refl) ⟩⊗⟨ (refl⟩∘⟨ identityʳ) ⟩∘⟨refl ⟩
            F.⊗-homo.η (X′ + Y′ , Z′) ∘ (F.⊗-homo.η (X′ , Y′) ∘ (F.₁ x ∘ f) ⊗₁ (F.₁ y ∘ g) ∘ ρ⇐) ⊗₁ (F.₁ z ∘ h) ∘ ρ⇐
                ≈⟨ refl⟩∘⟨ push-center ⊗-distrib-over-∘ ⟩⊗⟨refl ⟩∘⟨refl ⟩
            F.⊗-homo.η (X′ + Y′ , Z′) ∘ (F.⊗-homo.η (X′ , Y′) ∘ F.₁ x ⊗₁ F.₁ y ∘ f ⊗₁ g ∘ ρ⇐) ⊗₁ (F.₁ z ∘ h) ∘ ρ⇐
                ≈⟨ refl⟩∘⟨ extendʳ (F.⊗-homo.commute (x , y)) ⟩⊗⟨refl ⟩∘⟨refl ⟩
            F.⊗-homo.η (X′ + Y′ , Z′) ∘ (F.₁ (x +₁ y) ∘ F.⊗-homo.η (X , Y) ∘ f ⊗₁ g ∘ ρ⇐) ⊗₁ (F.₁ z ∘ h) ∘ ρ⇐
                ≈⟨ push-center ⊗-distrib-over-∘ ⟩
            F.⊗-homo.η (X′ + Y′ , Z′) ∘ F.₁ (x +₁ y) ⊗₁ F.₁ z ∘ (F.⊗-homo.η (X , Y) ∘ f ⊗₁ g ∘ ρ⇐) ⊗₁ h ∘ ρ⇐
                ≈⟨ extendʳ (F.⊗-homo.commute (x +₁ y , z)) ⟩
            F.₁ ((x +₁ y) +₁ z) ∘ F.⊗-homo.η (X + Y , Z) ∘ (F.⊗-homo.η (X , Y) ∘ f ⊗₁ g ∘ ρ⇐) ⊗₁ h ∘ ρ⇐
                ≈⟨ refl⟩∘⟨ identityʳ ⟨
            F.₁ ((x +₁ y) +₁ z) ∘ (F.⊗-homo.η (X + Y , Z) ∘ (F.⊗-homo.η (X , Y) ∘ f ⊗₁ g ∘ ρ⇐) ⊗₁ h ∘ ρ⇐) ∘ id
                ∎
    ≃₂ : NaturalTransformation (Hom[ [𝒟×𝒟]×𝒟.U ][ [𝒟×𝒟]×𝒟.unit ,-] ∘F [F×F]×F.F) (Hom[ 𝒟.U ][ 𝒟.unit ,-] ∘F F.F ∘F (x+[y+z].F {𝒞}))
    ≃₂ = ntHelper record
        { η = λ { ((X , Y) , Z) → record
            { to = λ { ((f , g) , h) → F.⊗-homo.η (X , Y + Z) ∘ (f ⊗₁ (F.⊗-homo.η (Y , Z) ∘ g ⊗₁ h ∘ ρ⇐)) ∘ ρ⇐ }
            ; cong = λ { {(f , g) , h} {(f′ , g′) , h′} ((x , y) , z) → refl⟩∘⟨ x ⟩⊗⟨ (refl⟩∘⟨ y ⟩⊗⟨ z ⟩∘⟨refl) ⟩∘⟨refl }
            } }
        ; commute = λ { {(X , Y) , Z} {(X′ , Y′) , Z′} ((x , y) , z) {(f , g) , h} → commute x y z f g h }
        }
      where
        open 𝒟.Equiv
        open 𝒟 using (sym-assoc; _∘_; id; _⊗₁_; identityʳ; _≈_)
        open ⊗-Reasoning 𝒟.monoidal
        open ⇒-Reasoning 𝒟.U
        commute
            : {X Y Z X′ Y′ Z′ : 𝒞.Obj}
              (x : 𝒞.U [ X , X′ ])
              (y : 𝒞.U [ Y , Y′ ])
              (z : 𝒞.U [ Z , Z′ ])
              (f : 𝒟.U [ 𝒟.unit , F.₀ X ])
              (g : 𝒟.U [ 𝒟.unit , F.₀ Y ])
              (h : 𝒟.U [ 𝒟.unit , F.₀ Z ])
            → F.⊗-homo.η (X′ , Y′ + Z′) ∘ (F.₁ x ∘ f ∘ id) ⊗₁ (F.⊗-homo.η (Y′ , Z′) ∘ (F.₁ y ∘ g ∘ id) ⊗₁ (F.₁ z ∘ h ∘ id) ∘ ρ⇐) ∘ ρ⇐
            ≈ F.₁ (x +₁ (y +₁ z)) ∘ (F.⊗-homo.η (X , Y + Z) ∘ f ⊗₁ (F.⊗-homo.η (Y , Z) ∘ g ⊗₁ h ∘ ρ⇐) ∘ ρ⇐) ∘ id
        commute {X} {Y} {Z} {X′} {Y′} {Z′} x y z f g h = begin
            F.⊗-homo.η (X′ , Y′ + Z′) ∘ (F.₁ x ∘ f ∘ id) ⊗₁ (F.⊗-homo.η (Y′ , Z′) ∘ (F.₁ y ∘ g ∘ id) ⊗₁ (F.₁ z ∘ h ∘ id) ∘ ρ⇐) ∘ ρ⇐
                ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ identityʳ) ⟩⊗⟨ (refl⟩∘⟨ (refl⟩∘⟨ identityʳ) ⟩⊗⟨ (refl⟩∘⟨ identityʳ) ⟩∘⟨refl) ⟩∘⟨refl ⟩
            F.⊗-homo.η (X′ , Y′ + Z′) ∘ (F.₁ x ∘ f) ⊗₁ (F.⊗-homo.η (Y′ , Z′) ∘ (F.₁ y ∘ g) ⊗₁ (F.₁ z ∘ h) ∘ ρ⇐) ∘ ρ⇐
                ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ push-center ⊗-distrib-over-∘ ⟩∘⟨refl ⟩
            F.⊗-homo.η (X′ , Y′ + Z′) ∘ (F.₁ x ∘ f) ⊗₁ (F.⊗-homo.η (Y′ , Z′) ∘ F.₁ y ⊗₁ F.₁ z ∘ g ⊗₁ h ∘ ρ⇐) ∘ ρ⇐
                ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ extendʳ (F.⊗-homo.commute (y , z)) ⟩∘⟨refl ⟩
            F.⊗-homo.η (X′ , Y′ + Z′) ∘ (F.₁ x ∘ f) ⊗₁ (F.₁ (y +₁ z) ∘ F.⊗-homo.η (Y , Z) ∘ g ⊗₁ h ∘ ρ⇐) ∘ ρ⇐
                ≈⟨ push-center ⊗-distrib-over-∘ ⟩
            F.⊗-homo.η (X′ , Y′ + Z′) ∘ F.₁ x ⊗₁ F.₁ (y +₁ z) ∘ f ⊗₁ (F.⊗-homo.η (Y , Z) ∘ g ⊗₁ h ∘ ρ⇐) ∘ ρ⇐
                ≈⟨ extendʳ (F.⊗-homo.commute (x , y +₁ z)) ⟩
            F.₁ (x +₁ (y +₁ z)) ∘ F.⊗-homo.η (X , Y + Z) ∘ f ⊗₁ (F.⊗-homo.η (Y , Z) ∘ g ⊗₁ h ∘ ρ⇐) ∘ ρ⇐
                ≈⟨ refl⟩∘⟨ identityʳ ⟨
            F.₁ (x +₁ (y +₁ z)) ∘ (F.⊗-homo.η (X , Y + Z) ∘ f ⊗₁ (F.⊗-homo.η (Y , Z) ∘ g ⊗₁ h ∘ ρ⇐) ∘ ρ⇐) ∘ id
                ∎
    open NaturalIsomorphism using (F⇐G)
    ≃₂≋≃₁ : (F⇐G (Hom[ 𝒟.U ][ 𝒟.unit ,-] ⓘˡ (F.F ⓘˡ assoc-≃))) ∘ᵥ ≃₂ ≋ ≃₁
    ≃₂≋≃₁ {(X , Y) , Z} {(f , g) , h} = begin
        F.₁ α⇐′ ∘ (F.⊗-homo.η (X , Y + Z) ∘ (f ⊗₁ _) ∘ ρ⇐) ∘ id                                               ≈⟨ refl⟩∘⟨ identityʳ ⟩
        F.₁ α⇐′ ∘ F.⊗-homo.η (X , Y + Z) ∘ f ⊗₁ (F.⊗-homo.η (Y , Z) ∘ g ⊗₁ h ∘ ρ⇐) ∘ ρ⇐                       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ sym-assoc ⟩∘⟨refl ⟩
        F.₁ α⇐′ ∘ F.⊗-homo.η (X , Y + Z) ∘ f ⊗₁ ((F.⊗-homo.η (Y , Z) ∘ g ⊗₁ h) ∘ ρ⇐) ∘ ρ⇐                     ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₂ʳ ⟩
        F.₁ α⇐′ ∘ F.⊗-homo.η (X , Y + Z) ∘ f ⊗₁ (F.⊗-homo.η (Y , Z) ∘ g ⊗₁ h) ∘ id ⊗₁ ρ⇐ ∘ ρ⇐                 ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ coherence-inv₃ ⟨
        F.₁ α⇐′ ∘ F.⊗-homo.η (X , Y + Z) ∘ f ⊗₁ (F.⊗-homo.η (Y , Z) ∘ g ⊗₁ h) ∘ id ⊗₁ ρ⇐ ∘ λ⇐                 ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ unitorˡ-commute-to ⟨
        F.₁ α⇐′ ∘ F.⊗-homo.η (X , Y + Z) ∘ f ⊗₁ (F.⊗-homo.η (Y , Z) ∘ g ⊗₁ h) ∘ λ⇐ ∘ ρ⇐                       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (switch-tofromˡ α coherence-inv₁) ⟩
        F.₁ α⇐′ ∘ F.⊗-homo.η (X , Y + Z) ∘ f ⊗₁ (F.⊗-homo.η (Y , Z) ∘ g ⊗₁ h) ∘ α⇒ ∘ λ⇐ ⊗₁ id ∘ ρ⇐            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
        F.₁ α⇐′ ∘ F.⊗-homo.η (X , Y + Z) ∘ id ⊗₁ F.⊗-homo.η (Y , Z) ∘ f ⊗₁ (g ⊗₁ h) ∘ α⇒ ∘ λ⇐ ⊗₁ id ∘ ρ⇐      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ coherence-inv₃ ⟩⊗⟨refl ⟩∘⟨refl ⟩
        F.₁ α⇐′ ∘ F.⊗-homo.η (X , Y + Z) ∘ id ⊗₁ F.⊗-homo.η (Y , Z) ∘ f ⊗₁ (g ⊗₁ h) ∘ α⇒ ∘ ρ⇐ ⊗₁ id ∘ ρ⇐      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟨
        F.₁ α⇐′ ∘ F.⊗-homo.η (X , Y + Z) ∘ id ⊗₁ F.⊗-homo.η (Y , Z) ∘ α⇒ ∘ (f ⊗₁ g) ⊗₁ h ∘ ρ⇐ ⊗₁ id ∘ ρ⇐      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (sym split₁ʳ) ⟩
        F.₁ α⇐′ ∘ F.⊗-homo.η (X , Y + Z) ∘ id ⊗₁ F.⊗-homo.η (Y , Z) ∘ α⇒ ∘ (f ⊗₁ g ∘ ρ⇐) ⊗₁ h ∘ ρ⇐            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
        F.₁ α⇐′ ∘ F.⊗-homo.η (X , Y + Z) ∘ (id ⊗₁ F.⊗-homo.η (Y , Z) ∘ α⇒) ∘ (f ⊗₁ g ∘ ρ⇐) ⊗₁ h ∘ ρ⇐          ≈⟨ refl⟩∘⟨ sym-assoc ⟩
        F.₁ α⇐′ ∘ (F.⊗-homo.η (X , Y + Z) ∘ id ⊗₁ F.⊗-homo.η (Y , Z) ∘ α⇒) ∘ (f ⊗₁ g ∘ ρ⇐) ⊗₁ h ∘ ρ⇐          ≈⟨ extendʳ (switch-fromtoˡ ([ F.F ]-resp-≅ α′) F.associativity) ⟨
        F.⊗-homo.η (X + Y , Z) ∘ F.⊗-homo.η (X , Y) ⊗₁ id ∘ (f ⊗₁ g ∘ ρ⇐) ⊗₁ h ∘ ρ⇐                           ≈⟨ refl⟩∘⟨ pullˡ (sym split₁ˡ) ⟩
        F.⊗-homo.η (X + Y , Z) ∘ (F.⊗-homo.η (X , Y) ∘ (f ⊗₁ g) ∘ ρ⇐) ⊗₁ h ∘ ρ⇐                               ∎
      where
        open Shorthands 𝒞.monoidal using () renaming (α⇐ to α⇐′)
        open Shorthands 𝒟.monoidal using (α⇒; λ⇐)
        open 𝒟.Equiv
        open 𝒟 using (sym-assoc; _∘_; id; _⊗₁_; identityʳ; assoc-commute-from; unitorˡ-commute-to) renaming (unitorˡ to ƛ; associator to α)
        open ⊗-Reasoning 𝒟.monoidal
        open ⇒-Reasoning 𝒟.U
        open CocartesianMonoidal 𝒞.U 𝒞.cocartesian using () renaming (associator to α′)
        open ⊗-Properties 𝒟.monoidal using (coherence-inv₁; coherence-inv₃)
    module Associator = Square {[𝒞×𝒞]×𝒞} {𝒞} {[𝒟×𝒟]×𝒟} {𝒟} {[F×F]×F} {F} {[x+y]+z.F {𝒞}} {x+[y+z].F {𝒞}} (assoc-≃ {𝒞}) ≃₁ ≃₂ ≃₂≋≃₁
open LiftAssociator using (module Associator)

module LiftBraiding where
    module F = SymmetricMonoidalFunctor F
    open 𝒞 using (⊥; -+_; i₁; _+_; _+₁_; ¡; +₁-cong₂; ¡-unique; -+-)
    open Shorthands 𝒟.monoidal using (ρ⇒; ρ⇐)
    ≃₁ : NaturalTransformation (Hom[ 𝒟×𝒟.U ][ 𝒟×𝒟.unit ,-] ∘F F×F.F) (Hom[ 𝒟.U ][ 𝒟.unit ,-] ∘F F.F ∘F (x+y.F {𝒞}))
    ≃₁ = ntHelper record
        { η = λ { (X , Y) → record
            { to = λ { (x , y) → F.⊗-homo.η (X , Y) ∘ x ⊗₁ y ∘ ρ⇐}
            ; cong = λ { {x , y} {x′ , y′} (≈x , ≈y) → refl⟩∘⟨ ≈x ⟩⊗⟨ ≈y ⟩∘⟨refl }
            } }
        ; commute = λ { {X , Y} {X′ , Y′} (x , y) {f , g} →
            (extendʳ
                (refl⟩∘⟨ (refl⟩∘⟨ identityʳ) ⟩⊗⟨ (refl⟩∘⟨ identityʳ)
                ○ refl⟩∘⟨ ⊗-distrib-over-∘
                ○ extendʳ (F.⊗-homo.commute (x , y))))
            ○ refl⟩∘⟨ extendˡ (sym identityʳ) }
        }
      where
        open 𝒟.Equiv
        open 𝒟 using (sym-assoc; _∘_; id; _⊗₁_; identityʳ; _≈_; assoc)
        open ⊗-Reasoning 𝒟.monoidal
        open ⇒-Reasoning 𝒟.U
    ≃₂ : NaturalTransformation (Hom[ 𝒟×𝒟.U ][ 𝒟×𝒟.unit ,-] ∘F F×F.F) (Hom[ 𝒟.U ][ 𝒟.unit ,-] ∘F F.F ∘F (y+x.F {𝒞}))
    ≃₂ = ntHelper record
        { η = λ { (X , Y) → record
            { to = λ { (x , y) → F.⊗-homo.η (Y , X) ∘ y ⊗₁ x ∘ ρ⇐}
            ; cong = λ { {x , y} {x′ , y′} (≈x , ≈y) → refl⟩∘⟨ ≈y ⟩⊗⟨ ≈x ⟩∘⟨refl }
            } }
        ; commute = λ { {X , Y} {X′ , Y′} (x , y) {f , g} →
            (extendʳ
                (refl⟩∘⟨ (refl⟩∘⟨ identityʳ) ⟩⊗⟨ (refl⟩∘⟨ identityʳ)
                ○ refl⟩∘⟨ ⊗-distrib-over-∘
                ○ extendʳ (F.⊗-homo.commute (y , x))))
            ○ refl⟩∘⟨ extendˡ (sym identityʳ) }
        }
      where
        open 𝒟.Equiv
        open 𝒟 using (sym-assoc; _∘_; id; _⊗₁_; identityʳ; _≈_; assoc)
        open ⊗-Reasoning 𝒟.monoidal
        open ⇒-Reasoning 𝒟.U
    open NaturalIsomorphism using (F⇐G)
    open Symmetric 𝒞.symmetric using (braiding)
    ≃₂≋≃₁ : (F⇐G (Hom[ 𝒟.U ][ 𝒟.unit ,-] ⓘˡ F.F ⓘˡ braiding)) ∘ᵥ ≃₂ ≋ ≃₁
    ≃₂≋≃₁ {X , Y} {f , g} =
        refl⟩∘⟨ (identityʳ ○ sym-assoc)
        ○ extendʳ
            (extendʳ F.braiding-compat
            ○ refl⟩∘⟨ (𝒟.braiding.⇒.commute (g , f)))
        ○ refl⟩∘⟨ pullʳ (sym (switch-tofromˡ 𝒟.braiding.FX≅GX braiding-coherence-inv) ○ coherence-inv₃)
      where
        open σ-Properties 𝒟.braided using (braiding-coherence-inv)
        open 𝒟.Equiv
        open 𝒟 using (sym-assoc; identityʳ)
        open ⊗-Reasoning 𝒟.monoidal
        open ⊗-Properties 𝒟.monoidal using (coherence-inv₃)
        open ⇒-Reasoning 𝒟.U
    module Braiding = Square {𝒞×𝒞} {𝒞} {𝒟×𝒟} {𝒟} {F×F} {F} {x+y.F {𝒞}} {y+x.F {𝒞}} braiding ≃₁ ≃₂ ≃₂≋≃₁
open LiftBraiding using (module Braiding)

CospansMonoidal : Monoidal DecoratedCospans
CospansMonoidal = record
    { ⊗ = ⊗
    ; unit = ⊥
    ; unitorˡ = [ L ]-resp-≅ ⊥+A≅A
    ; unitorʳ = [ L ]-resp-≅ A+⊥≅A
    ; associator = [ L ]-resp-≅ (≅.sym +-assoc)
    ; unitorˡ-commute-from = λ { {X} {Y} {f} → Unitorˡ.from f }
    ; unitorˡ-commute-to = λ { {X} {Y} {f} → Unitorˡ.to f }
    ; unitorʳ-commute-from = λ { {X} {Y} {f} → Unitorʳ.from f }
    ; unitorʳ-commute-to = λ { {X} {Y} {f} → Unitorʳ.to f }
    ; assoc-commute-from = λ { {X} {X′} {f} {Y} {Y′} {g} {Z} {Z′} {h} → Associator.from _ }
    ; assoc-commute-to = λ { {X} {X′} {f} {Y} {Y′} {g} {Z} {Z′} {h} → Associator.to _ }
    ; triangle = triangle
    ; pentagon = pentagon
    }
  where
    open Category DecoratedCospans using (id; module Equiv; module HomReasoning)
    open Equiv
    open HomReasoning
    open 𝒞 using (⊥; Obj; U; +-assoc)
    λ⇒ = Unitorˡ.FX≅GX′.from
    ρ⇒ = Unitorʳ.FX≅GX′.from
    α⇒ = Associator.FX≅GX′.from
    open Morphism U using (module ≅)
    open Monoidal +-monoidal using () renaming (triangle to tri; pentagon to pent)
    triangle : {X Y : Obj} → DecoratedCospans [ DecoratedCospans [ ⊗.₁ (id {X} , λ⇒) ∘ α⇒ ] ≈ ⊗.₁ (ρ⇒ , id {Y}) ]
    triangle = sym L-resp-⊗ ⟩∘⟨refl ○ sym L.homomorphism ○ L.F-resp-≈ tri ○ L-resp-⊗
    pentagon
        : {W X Y Z : Obj}
        → DecoratedCospans
            [ DecoratedCospans [ ⊗.₁ (id {W} , α⇒ {(X , Y) , Z}) ∘ DecoratedCospans [ α⇒ ∘ ⊗.₁ (α⇒ , id) ] ]
            ≈ DecoratedCospans [ α⇒ ∘ α⇒ ] ]
    pentagon = sym L-resp-⊗ ⟩∘⟨ refl ⟩∘⟨ sym L-resp-⊗ ○ refl⟩∘⟨ sym L.homomorphism ○ sym L.homomorphism ○ L.F-resp-≈ pent ○ L.homomorphism

CospansBraided : Braided CospansMonoidal
CospansBraided = record
    { braiding = niHelper record
        { η = λ { (X , Y) → Braiding.FX≅GX′.from {X , Y} }
        ; η⁻¹ = λ { (Y , X) → Braiding.FX≅GX′.to {Y , X} }
        ; commute = λ { {X , Y} {X′ , Y′} (f , g) → Braiding.from (record { cospan = record { f₁ = f₁ f , f₁ g ; f₂ = f₂ f , f₂ g } ; decoration = decoration f , decoration g}) }
        ; iso = λ { (X , Y) → Braiding.FX≅GX′.iso {X , Y} }
        }
    ; hexagon₁ = sym L-resp-⊗ ⟩∘⟨ refl ⟩∘⟨ sym L-resp-⊗ ○ refl⟩∘⟨ sym L.homomorphism ○ sym L.homomorphism ○ L-resp-≈ hex₁ ○ L.homomorphism ○ refl⟩∘⟨ L.homomorphism
    ; hexagon₂ = sym L-resp-⊗ ⟩∘⟨refl ⟩∘⟨ sym L-resp-⊗ ○ sym L.homomorphism ⟩∘⟨refl ○ sym L.homomorphism ○ L-resp-≈ hex₂ ○ L.homomorphism ○ L.homomorphism ⟩∘⟨refl
    }
  where
    open Symmetric 𝒞.symmetric renaming (hexagon₁ to hex₁; hexagon₂ to hex₂)
    open DecoratedCospan
    module Cospans = Category DecoratedCospans
    open Cospans.Equiv
    open Cospans.HomReasoning
    open Functor L renaming (F-resp-≈ to L-resp-≈)

CospansSymmetric : Symmetric CospansMonoidal
CospansSymmetric = record
    { braided = CospansBraided
    ; commutative = sym homomorphism ○ L-resp-≈ comm ○ identity
    }
  where
    open Symmetric 𝒞.symmetric renaming (commutative to comm)
    module Cospans = Category DecoratedCospans
    open Cospans.Equiv
    open Cospans.HomReasoning
    open Functor L renaming (F-resp-≈ to L-resp-≈)
