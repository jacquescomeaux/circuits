{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --no-require-unique-meta-solutions #-}

open import Level using (Level)
module Functor.Instance.Underlying.SymmetricMonoidal.FinitelyCocomplete {o ℓ e : Level} where

import Categories.Morphism.Reasoning as ⇒-Reasoning
import Categories.Object.Coproduct as Coproduct
import Categories.Object.Initial as Initial

open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Properties using ([_]-resp-square; [_]-resp-∘)
open import Categories.Functor.Monoidal using (IsMonoidalFunctor)
open import Categories.Functor.Monoidal.Braided using (module Lax)
open import Categories.Functor.Monoidal.Properties using (idF-SymmetricMonoidal; ∘-SymmetricMonoidal)
open import Categories.Functor.Monoidal.Symmetric using (module Lax)
open import Categories.Category using (Category; _[_,_]; _[_≈_]; _[_∘_])
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory; BraidedMonoidalCategory; MonoidalCategory)
open import Categories.Category.Product using (_⁂_)
open import Categories.Morphism using (_≅_)
open import Categories.Morphism.Notation using (_[_≅_])
open import Categories.NaturalTransformation.Core using (NaturalTransformation; ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; niHelper) renaming (refl to ≃-refl)
open import Categories.NaturalTransformation.NaturalIsomorphism.Monoidal.Symmetric using (module Lax)
open import Data.Product.Base using (_,_)

open import Category.Instance.FinitelyCocompletes {o} {ℓ} {e} using (FinitelyCocompletes)
open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)
open import Category.Instance.SymMonCat {o} {ℓ} {e} using (SymMonCat)
open import Functor.Exact using (RightExactFunctor; idREF; ∘-RightExactFunctor)

open FinitelyCocompleteCategory using () renaming (symmetricMonoidalCategory to smc)
open SymmetricMonoidalCategory using (unit) renaming (braidedMonoidalCategory to bmc)
open BraidedMonoidalCategory using () renaming (monoidalCategory to mc)

private
  variable
    A B C : FinitelyCocompleteCategory o ℓ e

F₀ : FinitelyCocompleteCategory o ℓ e → SymmetricMonoidalCategory o ℓ e
F₀ C = smc C
{-# INJECTIVE_FOR_INFERENCE F₀ #-}

F₁ : RightExactFunctor A B → Lax.SymmetricMonoidalFunctor (F₀ A) (F₀ B)
F₁ {A} {B} F = record
    { F = F.F
    ; isBraidedMonoidal = record
        { isMonoidal = record
            { ε = ε-iso.from
            ; ⊗-homo = ⊗-homo
            ; associativity = assoc
            ; unitaryˡ = unitaryˡ
            ; unitaryʳ = unitaryʳ
            }
        ; braiding-compat = braiding-compat
        }
    }
  where
    module F = RightExactFunctor F
    module A = SymmetricMonoidalCategory (F₀ A)
    module B = SymmetricMonoidalCategory (F₀ B)
    module A′ = FinitelyCocompleteCategory A
    module B′ = FinitelyCocompleteCategory B
    ε-iso : B.U [ B.unit ≅ F.₀ A.unit ]
    ε-iso = Initial.up-to-iso B.U B′.initial (record { ⊥ = F.₀ A′.⊥ ; ⊥-is-initial = F.F-resp-⊥ A′.⊥-is-initial })
    module ε-iso = _≅_ ε-iso
    +-iso : ∀ {X Y} → B.U [ F.₀ X B′.+ F.₀ Y ≅ F.₀ (X A′.+ Y) ]
    +-iso = Coproduct.up-to-iso B.U B′.coproduct (Coproduct.IsCoproduct⇒Coproduct B.U (F.F-resp-+ (Coproduct.Coproduct⇒IsCoproduct A.U A′.coproduct)))
    module +-iso {X Y} = _≅_ (+-iso {X} {Y})
    module B-proofs where
      open ⇒-Reasoning B.U
      open B.HomReasoning
      open B.Equiv
      open B using (_∘_; _≈_)
      open B′ using (_+₁_; []-congˡ; []-congʳ; []-cong₂)
      open A′ using (_+_; i₁; i₂)
      ⊗-homo : NaturalTransformation (B.⊗ ∘F (F.F ⁂ F.F)) (F.F ∘F A.⊗)
      ⊗-homo = ntHelper record
          { η = λ { (X , Y) → +-iso.from {X} {Y} }
          ; commute = λ { {X , Y} {X′ , Y′} (f , g) →
              B′.coproduct.∘-distribˡ-[]
              ○ B′.coproduct.[]-cong₂
                  (pullˡ B′.coproduct.inject₁ ○ [ F.F ]-resp-square (A.Equiv.sym A′.coproduct.inject₁))
                  (pullˡ B′.coproduct.inject₂ ○ [ F.F ]-resp-square (A.Equiv.sym A′.coproduct.inject₂))
              ○ sym B′.coproduct.∘-distribˡ-[] }
          }
      assoc
          : {X Y Z : A.Obj}
          → F.₁ A′.+-assocˡ
          ∘ +-iso.from {X + Y} {Z}
          ∘ (+-iso.from {X} {Y} +₁ B.id {F.₀ Z})
          ≈ +-iso.from {X} {Y + Z}
          ∘ (B.id {F.₀ X} +₁ +-iso.from {Y} {Z})
          ∘ B′.+-assocˡ
      assoc {X} {Y} {Z} = begin
          F.₁ A′.+-assocˡ ∘ +-iso.from ∘ (+-iso.from +₁ B.id)                               ≈⟨ refl⟩∘⟨ B′.[]∘+₁ ⟩
          F.₁ A′.+-assocˡ ∘ B′.[ F.₁ i₁ ∘ +-iso.from , F.₁ i₂ ∘ B.id ]                      ≈⟨ refl⟩∘⟨ []-congʳ B′.coproduct.∘-distribˡ-[] ⟩
          F.₁ A′.+-assocˡ ∘ B′.[ B′.[ F.₁ i₁ ∘ F.₁ i₁ , F.₁ i₁ ∘ F.₁ i₂ ] , F.₁ i₂ ∘ B.id ] ≈⟨ B′.coproduct.∘-distribˡ-[] ⟩
          B′.[ F.₁ A′.+-assocˡ ∘ B′.[ F.₁ i₁ ∘ F.₁ i₁ , F.₁ i₁ ∘ F.₁ i₂ ] , _ ]             ≈⟨ []-congʳ B′.coproduct.∘-distribˡ-[] ⟩
          B′.[ B′.[ F.₁ A′.+-assocˡ ∘ F.₁ i₁ ∘ F.₁ i₁ , F.₁ A′.+-assocˡ ∘ _ ] , _ ]         ≈⟨ []-congʳ ([]-congʳ (pullˡ ([ F.F ]-resp-∘ A′.coproduct.inject₁))) ⟩
          B′.[ B′.[ F.₁ A′.[ i₁ , i₂ A′.∘ i₁ ] ∘ F.₁ i₁ , F.₁ A′.+-assocˡ ∘ _ ] , _ ]       ≈⟨ []-congʳ ([]-congʳ ([ F.F ]-resp-∘ A′.coproduct.inject₁)) ⟩
          B′.[ B′.[ F.₁ i₁ , F.₁ A′.+-assocˡ ∘ F.₁ i₁ ∘ F.₁ i₂ ] , _ ]                      ≈⟨ []-congʳ ([]-congˡ (pullˡ ([ F.F ]-resp-∘ A′.coproduct.inject₁))) ⟩
          B′.[ B′.[ F.₁ i₁ , F.₁ A′.[ i₁ , i₂ A′.∘ i₁ ] ∘ F.₁ i₂ ] , _ ]                    ≈⟨ []-congʳ ([]-congˡ ([ F.F ]-resp-∘ A′.coproduct.inject₂)) ⟩
          B′.[ B′.[ F.₁ i₁ , F.₁ (i₂ A′.∘ i₁) ] , F.₁ A′.+-assocˡ ∘ F.₁ i₂ ∘ B.id ]         ≈⟨ []-congˡ (pullˡ ([ F.F ]-resp-∘ A′.coproduct.inject₂)) ⟩
          B′.[ B′.[ F.₁ i₁ , F.₁ (i₂ A′.∘ i₁) ] , F.₁ (i₂ A′.∘ i₂) ∘ B.id ]                 ≈⟨ []-cong₂ ([]-congˡ F.homomorphism) (B.identityʳ ○ F.homomorphism) ⟩
          B′.[ B′.[ F.₁ i₁ , F.₁ i₂ B′.∘ F.₁ i₁ ] , F.₁ i₂ ∘ F.₁ i₂ ]                       ≈⟨ []-congʳ ([]-congˡ B′.coproduct.inject₁) ⟨
          B′.[ B′.[ F.₁ i₁ , B′.[ F.₁ i₂ B′.∘ F.₁ i₁  , _ ] ∘ B′.i₁ ] , _ ]                 ≈⟨ []-congʳ ([]-cong₂ (sym B′.coproduct.inject₁) (pushˡ (sym B′.coproduct.inject₂))) ⟩
          B′.[ B′.[ B′.[ F.₁ i₁ , _ ] ∘ B′.i₁ , B′.[ F.₁ i₁ , _ ] ∘ B′.i₂ ∘ B′.i₁ ] , _ ]   ≈⟨ []-congʳ B′.coproduct.∘-distribˡ-[] ⟨
          B′.[ B′.[ F.₁ i₁ , _ ] ∘ B′.[ B′.i₁ , B′.i₂ ∘ B′.i₁ ] , F.₁ i₂ ∘ F.₁ i₂ ]         ≈⟨ []-congˡ B′.coproduct.inject₂ ⟨
          B′.[ B′.[ F.₁ i₁ , _ ] ∘ B′.[ _ , _ ] , B′.[ _ , F.₁ i₂ ∘ F.₁ i₂ ] ∘ B′.i₂ ]      ≈⟨ []-congˡ (pushˡ (sym B′.coproduct.inject₂)) ⟩
          B′.[ B′.[ F.₁ i₁ , _ ] ∘ B′.[ _ , _ ] , B′.[ F.₁ i₁ , _ ] ∘ B′.i₂ ∘ B′.i₂ ]       ≈⟨ B′.coproduct.∘-distribˡ-[] ⟨
          B′.[ F.₁ i₁ ,  B′.[ F.₁ i₂ ∘ F.₁ i₁ , F.₁ i₂ ∘ F.₁ i₂ ] ] ∘ B′.+-assocˡ           ≈⟨ []-cong₂ B.identityʳ (B′.coproduct.∘-distribˡ-[]) ⟩∘⟨refl ⟨
          B′.[ F.₁ i₁ B′.∘ B′.id , F.₁ i₂ ∘ B′.[ F.₁ i₁ , F.₁ i₂ ] ] ∘ B′.+-assocˡ          ≈⟨ pushˡ (sym B′.[]∘+₁) ⟩
          +-iso.from ∘ (B.id +₁ +-iso.from) ∘ B′.+-assocˡ                                   ∎
      unitaryˡ
          : {X : A.Obj}
          → F.₁ A′.[ A′.initial.! , A.id {X} ]
          ∘ B′.[ F.₁ i₁ , F.₁ i₂ ]
          ∘ B′.[ B′.i₁ ∘ B′.initial.! , B′.i₂ ∘ B.id ]
          ≈ B′.[ B′.initial.! , B.id ]
      unitaryˡ {X} = begin
          F.₁ A′.[ A′.initial.! , A.id ] ∘ B′.[ F.₁ i₁ , F.₁ i₂ ] ∘ B′.[ _ , B′.i₂ ∘ B.id ]   ≈⟨ refl⟩∘⟨ B′.coproduct.∘-distribˡ-[] ⟩
          _ ∘ B′.[ _ ∘ B′.i₁ ∘ B′.initial.! , B′.[ F.₁ i₁ , F.₁ i₂ ] ∘ B′.i₂ ∘ B.id ]         ≈⟨ refl⟩∘⟨ []-cong₂ (sym (B′.¡-unique _)) (pullˡ B′.coproduct.inject₂) ⟩
          F.₁ A′.[ A′.initial.! , A.id ] ∘ B′.[ B′.initial.! , F.₁ i₂ ∘  B.id ]               ≈⟨ B′.coproduct.∘-distribˡ-[] ⟩
          B′.[ _ ∘ B′.initial.! , F.₁ A′.[ A′.initial.! , A.id ] ∘ F.₁ i₂ ∘  B.id ]           ≈⟨ []-cong₂ (sym (B′.¡-unique _)) (pullˡ ([ F.F ]-resp-∘ A′.coproduct.inject₂)) ⟩
          B′.[ B′.initial.! , F.₁ A.id ∘  B.id ]                                              ≈⟨ []-congˡ (elimˡ F.identity) ⟩
          B′.[ B′.initial.! , B.id ]                                                          ∎
      unitaryʳ
          : {X : A.Obj}
          → F.₁ A′.[ A′.id {X} , A′.initial.! ]
          ∘ B′.[ F.₁ i₁ , F.₁ i₂ ]
          ∘ B′.[ B′.i₁ ∘ B.id , B′.i₂ ∘ B′.initial.! ]
          ≈ B′.[ B.id , B′.initial.! ]
      unitaryʳ {X} = begin
          F.₁ A′.[ A.id , A′.initial.! ] ∘ B′.[ F.₁ i₁ , F.₁ i₂ ] ∘ B′.[ B′.i₁ ∘ B.id , _ ]   ≈⟨ refl⟩∘⟨ B′.coproduct.∘-distribˡ-[] ⟩
          _ ∘ B′.[ B′.[ F.₁ i₁ , F.₁ i₂ ] ∘ B′.i₁ ∘ B.id , _ ∘ B′.i₂ ∘ B′.initial.! ]         ≈⟨ refl⟩∘⟨ []-cong₂ (pullˡ B′.coproduct.inject₁) (sym (B′.¡-unique _)) ⟩
          F.₁ A′.[ A.id , A′.initial.! ] ∘ B′.[ F.₁ i₁ ∘  B.id , B′.initial.! ]               ≈⟨ B′.coproduct.∘-distribˡ-[] ⟩
          B′.[ F.₁ A′.[ A.id , A′.initial.! ] ∘ F.₁ i₁ ∘  B.id , _ ∘ B′.initial.! ]           ≈⟨ []-cong₂ (pullˡ ([ F.F ]-resp-∘ A′.coproduct.inject₁)) (sym (B′.¡-unique _)) ⟩
          B′.[ F.₁ A.id ∘  B.id , B′.initial.! ]                                              ≈⟨ []-congʳ (elimˡ F.identity) ⟩
          B′.[ B.id , B′.initial.! ]                                                          ∎
      braiding-compat
          : {X Y : A.Obj}
          → F.₁ A′.[ i₂ {X} {Y} , i₁ ] ∘ B′.[ F.₁ i₁ , F.₁ i₂ ]
          ≈ B′.[ F.F₁ i₁ , F.F₁ i₂ ] ∘ B′.[ B′.i₂ , B′.i₁ ]
      braiding-compat = begin
          F.₁ A′.[ i₂ , i₁ ] ∘ B′.[ F.₁ i₁ , F.₁ i₂ ]                             ≈⟨ B′.coproduct.∘-distribˡ-[] ⟩
          B′.[ F.₁ A′.[ i₂ , i₁ ] ∘ F.₁ i₁ , F.₁ A′.[ i₂ , i₁ ] ∘ F.₁ i₂ ]        ≈⟨ []-cong₂ ([ F.F ]-resp-∘ A′.coproduct.inject₁) ([ F.F ]-resp-∘ A′.coproduct.inject₂) ⟩
          B′.[ F.₁ i₂ , F.₁ i₁ ]                                                  ≈⟨ []-cong₂ B′.coproduct.inject₂ B′.coproduct.inject₁ ⟨
          B′.[ B′.[ F.₁ i₁ , F.₁ i₂ ] ∘ B′.i₂ , B′.[ F.₁ i₁ , F.₁ i₂ ] ∘ B′.i₁ ]  ≈⟨ B′.coproduct.∘-distribˡ-[] ⟨
          B′.[ F.₁ i₁ , F.₁ i₂ ] ∘ B′.[ B′.i₂ , B′.i₁ ]   ∎
    open B-proofs

identity : Lax.SymmetricMonoidalNaturalIsomorphism (F₁ (Functor.Exact.idREF {o} {ℓ} {e} {A})) (idF-SymmetricMonoidal (F₀ A))
identity {A} = record
    { U = ≃-refl
    ; F⇒G-isMonoidal = record
        { ε-compat = ¡-unique₂ (id ∘ ¡) id
        ; ⊗-homo-compat = refl⟩∘⟨ sym ([]-cong₂ identityʳ identityʳ)
        }
    }
  where
    open FinitelyCocompleteCategory A
    open HomReasoning
    open Equiv

homomorphism
    : {F : RightExactFunctor A B}
      {G : RightExactFunctor B C}
    → Lax.SymmetricMonoidalNaturalIsomorphism
        (F₁ {A} {C} (∘-RightExactFunctor G F))
        (∘-SymmetricMonoidal (F₁ {B} {C} G) (F₁ {A} {B} F))
homomorphism {A} {B} {C} {F} {G} = record
    { U = ≃-refl
    ; F⇒G-isMonoidal = record
        { ε-compat = ¡-unique₂ (id ∘ ¡) (G.₁ B.¡ ∘ ¡)
        ; ⊗-homo-compat =
            identityˡ
            ○ sym
                ([]-cong₂
                    ([ G.F ]-resp-∘ B.coproducts.inject₁)
                    ([ G.F ]-resp-∘ B.coproducts.inject₂))
            ○ sym ∘-distribˡ-[]
            ○ pushʳ (introʳ C.⊗.identity)
        }
    }
  where
    module A = FinitelyCocompleteCategory A
    module B = FinitelyCocompleteCategory B
    open FinitelyCocompleteCategory C
    module C = SymmetricMonoidalCategory (F₀ C)
    open HomReasoning
    open Equiv
    open ⇒-Reasoning U
    module F = RightExactFunctor F
    module G = RightExactFunctor G

module _ {F G : RightExactFunctor A B} where

  module F = RightExactFunctor F
  module G = RightExactFunctor G

  F-resp-≈
      : NaturalIsomorphism F.F G.F
      → Lax.SymmetricMonoidalNaturalIsomorphism (F₁ {A} {B} F) (F₁ {A} {B} G)
  F-resp-≈ F≃G = record
      { U = F≃G
      ; F⇒G-isMonoidal = record
          { ε-compat = sym (¡-unique (⇒.η A.⊥ ∘ ¡))
          ; ⊗-homo-compat =
              ∘-distribˡ-[]
              ○ []-cong₂ (⇒.commute A.i₁) (⇒.commute A.i₂)
              ○ sym []∘+₁
          }
      }
    where
      module A = FinitelyCocompleteCategory A
      open NaturalIsomorphism F≃G
      open FinitelyCocompleteCategory B
      open HomReasoning
      open Equiv

Underlying : Functor FinitelyCocompletes SymMonCat
Underlying = record
    { F₀ = F₀
    ; F₁ = F₁
    ; identity = λ { {X} → identity {X} }
    ; homomorphism = λ { {X} {Y} {Z} {F} {G} → homomorphism {X} {Y} {Z} {F} {G} }
    ; F-resp-≈ = λ { {X} {Y} {F} {G} → F-resp-≈ {X} {Y} {F} {G} }
    }
