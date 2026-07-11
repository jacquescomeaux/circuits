{-# OPTIONS --without-K --safe #-}

open import Level using (Level; suc; _⊔_)

module Category.Cartesian.Instance.FinitelyCocompletes {o ℓ e : Level} where

import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as ⇒-Reasoning

open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
open import Categories.Diagram.Coequalizer using (IsCoequalizer)
open import Categories.Functor.Bifunctor using (flip-bifunctor)
open import Categories.Functor.Core using (Functor)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; niHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties using (pointwise-iso)
open import Categories.Object.Coproduct using (IsCoproduct; IsCoproduct⇒Coproduct; Coproduct)
open import Categories.Object.Initial using (IsInitial)
open import Data.Product using (_,_; swap) renaming (_×_ to _×′_)
open import Function using () renaming (_∘_ to _∘′_)
open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)
open import Category.Instance.FinitelyCocompletes {o} {ℓ} {e} using (FinitelyCocompletes; FinitelyCocompletes-Cartesian; _×₁_)
open import Functor.Exact using (IsRightExact; RightExactFunctor)
open import Functor.Exact.Instance.Swap using (Swap)

FinitelyCocompletes-CC : CartesianCategory (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
FinitelyCocompletes-CC = record
    { U = FinitelyCocompletes
    ; cartesian = FinitelyCocompletes-Cartesian
    }

module FinCoCom = CartesianCategory FinitelyCocompletes-CC
open FinCoCom using (_×_; π₁; π₂; assocˡ)

module _ (𝒞 : FinitelyCocompleteCategory o ℓ e) where

  private
    module 𝒞 = FinitelyCocompleteCategory 𝒞
    module 𝒞×𝒞 = FinitelyCocompleteCategory (𝒞 × 𝒞)

  open 𝒞 using ([_,_]; +-unique; i₁; i₂; _∘_; _+_; module Equiv; _⇒_; _+₁_; -+-)
  open Equiv

  private
    module -+- = Functor -+-

  flip-IsInitial
      : {(A , B) : 𝒞×𝒞.Obj}
      → IsInitial 𝒞×𝒞.U (A , B)
      → IsInitial 𝒞×𝒞.U (B , A)
  flip-IsInitial isInitial = let open IsInitial isInitial in record
      { ¡ = swap ¡
      ; ¡-unique = swap ∘′ ¡-unique ∘′ swap
      }

  flip-IsCoproduct
      : {(A₁ , A₂) (B₁ , B₂) (C₁ , C₂) : 𝒞×𝒞.Obj}
        {(i₁-₁ , i₁-₂) : (A₁ ⇒ C₁) ×′ (A₂ ⇒ C₂)}
        {(i₂-₁ , i₂-₂) : (B₁ ⇒ C₁) ×′ (B₂ ⇒ C₂)}
      → IsCoproduct 𝒞×𝒞.U (i₁-₁ , i₁-₂) (i₂-₁ , i₂-₂)
      → IsCoproduct 𝒞×𝒞.U (i₁-₂ , i₁-₁) (i₂-₂ , i₂-₁)
  flip-IsCoproduct isCoproduct = let module + = IsCoproduct isCoproduct in record
      { [_,_] = λ x y → swap (+.[ swap x , swap y ])
      ; inject₁ = swap +.inject₁
      ; inject₂ = swap +.inject₂
      ; unique = λ x y → swap (+.unique (swap x) (swap y))
      }

  flip-IsCoequalizer
      : {(A₁ , A₂) (B₁ , B₂) (C₁ , C₂) : 𝒞×𝒞.Obj}
        {(f₁ , f₂) (g₁ , g₂) : (A₁ ⇒ B₁) ×′ (A₂ ⇒ B₂)}
        {(h₁ , h₂) : (B₁ ⇒ C₁) ×′ (B₂ ⇒ C₂)}
      → IsCoequalizer 𝒞×𝒞.U (f₁ , f₂) (g₁ , g₂) (h₁ , h₂)
      → IsCoequalizer 𝒞×𝒞.U (f₂ , f₁) (g₂ , g₁) (h₂ , h₁)
  flip-IsCoequalizer isCoeq = let open IsCoequalizer isCoeq in record
      { equality = swap equality
      ; coequalize = swap ∘′ coequalize ∘′ swap
      ; universal = swap universal
      ; unique = swap ∘′ unique ∘′ swap
      }

  +-resp-⊥
      : {(A , B) : 𝒞×𝒞.Obj}
      → IsInitial 𝒞×𝒞.U (A , B)
      → IsInitial 𝒞.U (A + B)
  +-resp-⊥ {A , B} A,B-isInitial = record
      { ¡ = [ A-isInitial.¡ , B-isInitial.¡ ]
      ; ¡-unique = λ f → +-unique (sym (A-isInitial.¡-unique (f ∘ i₁))) (sym (B-isInitial.¡-unique (f ∘ i₂)))
      }
    where
      open IsRightExact
      open RightExactFunctor
      module A-isInitial = IsInitial (F-resp-⊥ (isRightExact (π₁ {𝒞} {𝒞})) A,B-isInitial)
      module B-isInitial = IsInitial (F-resp-⊥ (isRightExact (π₂ {𝒞} {𝒞})) A,B-isInitial)

  +-resp-+
      : {(A₁ , A₂) (B₁ , B₂) (C₁ , C₂) : 𝒞×𝒞.Obj}
        {(i₁-₁ , i₁-₂) : (A₁ ⇒ C₁) ×′ (A₂ ⇒ C₂)}
        {(i₂-₁ , i₂-₂) : (B₁ ⇒ C₁) ×′ (B₂ ⇒ C₂)}
      → IsCoproduct 𝒞×𝒞.U (i₁-₁ , i₁-₂) (i₂-₁ , i₂-₂)
      → IsCoproduct 𝒞.U (i₁-₁ +₁ i₁-₂) (i₂-₁ +₁ i₂-₂)
  +-resp-+ {A₁ , A₂} {B₁ , B₂} {C₁ , C₂} {i₁-₁ , i₁-₂} {i₂-₁ , i₂-₂} isCoproduct = record
      { [_,_] = λ { h₁ h₂ → [ Coprod₁.[ h₁ ∘ i₁ , h₂ ∘ i₁ ] , Coprod₂.[ h₁ ∘ i₂  , h₂ ∘ i₂ ] ] }
      ; inject₁ = inject₁
      ; inject₂ = inject₂
      ; unique = unique
      }
    where
      open IsRightExact
      open RightExactFunctor
      module Coprod₁ = Coproduct (IsCoproduct⇒Coproduct 𝒞.U (F-resp-+ (isRightExact (π₁ {𝒞} {𝒞})) isCoproduct))
      module Coprod₂ = Coproduct (IsCoproduct⇒Coproduct 𝒞.U (F-resp-+ (isRightExact (π₂ {𝒞} {𝒞})) isCoproduct))
      open 𝒞 using ([]-cong₂; []∘+₁; +-g-η; +₁∘i₁; +₁∘i₂)
      open 𝒞 using (Obj; _≈_; module HomReasoning; assoc)
      open HomReasoning
      open ⇒-Reasoning 𝒞.U
      inject₁
          : {X : Obj}
            {h₁ : A₁ + A₂ ⇒ X}
            {h₂ : B₁ + B₂ ⇒ X}
          → [ Coprod₁.[ h₁ ∘ i₁ , h₂ ∘ i₁ ] , Coprod₂.[ h₁ ∘ i₂ , h₂ ∘ i₂ ] ] ∘ (i₁-₁ +₁ i₁-₂) ≈ h₁
      inject₁ {_} {h₁} {h₂} = begin
          [ Coprod₁.[ h₁ ∘ i₁ , h₂ ∘ i₁ ] , Coprod₂.[ h₁ ∘ i₂ , h₂ ∘ i₂ ] ] ∘ (i₁-₁ +₁ i₁-₂)  ≈⟨ []∘+₁ ⟩
          [ Coprod₁.[ h₁ ∘ i₁ , h₂ ∘ i₁ ] ∘ i₁-₁ , Coprod₂.[ h₁ ∘ i₂ , h₂ ∘ i₂ ] ∘ i₁-₂ ]     ≈⟨ []-cong₂ Coprod₁.inject₁ Coprod₂.inject₁ ⟩
          [ h₁ ∘ i₁ , h₁ ∘ i₂ ]                                                               ≈⟨ +-g-η ⟩
          h₁                                                                                  ∎
      inject₂
          : {X : Obj}
            {h₁ : A₁ + A₂ ⇒ X}
            {h₂ : B₁ + B₂ ⇒ X}
          → [ Coprod₁.[ h₁ ∘ i₁ , h₂ ∘ i₁ ] , Coprod₂.[ h₁ ∘ i₂ , h₂ ∘ i₂ ] ] ∘ (i₂-₁ +₁ i₂-₂) ≈ h₂
      inject₂ {_} {h₁} {h₂} = begin
          [ Coprod₁.[ h₁ ∘ i₁ , h₂ ∘ i₁ ] , Coprod₂.[ h₁ ∘ i₂ , h₂ ∘ i₂ ] ] ∘ (i₂-₁ +₁ i₂-₂)  ≈⟨ []∘+₁ ⟩
          [ Coprod₁.[ h₁ ∘ i₁ , h₂ ∘ i₁ ] ∘ i₂-₁ , Coprod₂.[ h₁ ∘ i₂ , h₂ ∘ i₂ ] ∘ i₂-₂ ]     ≈⟨ []-cong₂ Coprod₁.inject₂ Coprod₂.inject₂ ⟩
          [ h₂ ∘ i₁ , h₂ ∘ i₂ ]                                                               ≈⟨ +-g-η ⟩
          h₂                                                                                  ∎
      unique
          : {X : Obj}
            {i : C₁ + C₂ ⇒ X}
            {h₁ : A₁ + A₂ ⇒ X}
            {h₂ : B₁ + B₂ ⇒ X}
            (eq₁ : i ∘ (i₁-₁ +₁ i₁-₂) ≈ h₁)
            (eq₂ : i ∘ (i₂-₁ +₁ i₂-₂) ≈ h₂)
          → [ Coprod₁.[ h₁ ∘ i₁ , h₂ ∘ i₁ ] , Coprod₂.[ h₁ ∘ i₂ , h₂ ∘ i₂ ] ] ≈ i
      unique {X} {i} {h₁} {h₂} eq₁ eq₂ = begin
          [ Coprod₁.[ h₁ ∘ i₁ , h₂ ∘ i₁ ] , Coprod₂.[ h₁ ∘ i₂ , h₂ ∘ i₂ ] ] ≈⟨ []-cong₂ (Coprod₁.unique eq₁-₁ eq₂-₁) (Coprod₂.unique eq₁-₂ eq₂-₂) ⟩
          [ i ∘ i₁ , i ∘ i₂ ]                                               ≈⟨ +-g-η ⟩
          i                                                                 ∎
        where
          eq₁-₁ : (i ∘ i₁) ∘ i₁-₁ ≈ h₁ ∘ i₁
          eq₁-₁ = begin
              (i ∘ i₁) ∘ i₁-₁         ≈⟨ pushʳ +₁∘i₁ ⟨
              i ∘ (i₁-₁ +₁ i₁-₂) ∘ i₁ ≈⟨ pullˡ eq₁ ⟩
              h₁ ∘ i₁                 ∎
          eq₂-₁ : (i ∘ i₁) ∘ i₂-₁ ≈ h₂ ∘ i₁
          eq₂-₁ = begin
              (i ∘ i₁) ∘ i₂-₁         ≈⟨ pushʳ +₁∘i₁ ⟨
              i ∘ (i₂-₁ +₁ i₂-₂) ∘ i₁ ≈⟨ pullˡ eq₂ ⟩
              h₂ ∘ i₁                 ∎
          eq₁-₂ : (i ∘ i₂) ∘ i₁-₂ ≈ h₁ ∘ i₂
          eq₁-₂ = begin
              (i ∘ i₂) ∘ i₁-₂         ≈⟨ pushʳ +₁∘i₂ ⟨
              i ∘ (i₁-₁ +₁ i₁-₂) ∘ i₂ ≈⟨ pullˡ eq₁ ⟩
              h₁ ∘ i₂                 ∎
          eq₂-₂ : (i ∘ i₂) ∘ i₂-₂ ≈ h₂ ∘ i₂
          eq₂-₂ = begin
              (i ∘ i₂) ∘ i₂-₂         ≈⟨ pushʳ +₁∘i₂ ⟨
              i ∘ (i₂-₁ +₁ i₂-₂) ∘ i₂ ≈⟨ pullˡ eq₂ ⟩
              h₂ ∘ i₂                 ∎

  +-resp-coeq
      : {(A₁ , A₂) (B₁ , B₂) (C₁ , C₂) : 𝒞×𝒞.Obj}
        {(f₁ , f₂) (g₁ , g₂) : (A₁ ⇒ B₁) ×′ (A₂ ⇒ B₂)}
        {(h₁ , h₂) : (B₁ ⇒ C₁) ×′ (B₂ ⇒ C₂)}
      → IsCoequalizer 𝒞×𝒞.U (f₁ , f₂) (g₁ , g₂) (h₁ , h₂)
      → IsCoequalizer 𝒞.U (f₁ +₁ f₂) (g₁ +₁ g₂) (h₁ +₁ h₂)
  +-resp-coeq {A₁ , A₂} {B₁ , B₂} {C₁ , C₂} {f₁ , f₂} {g₁ , g₂} {h₁ , h₂} isCoeq = record
      { equality = sym -+-.homomorphism ○ []-cong₂ (refl⟩∘⟨ Coeq₁.equality) (refl⟩∘⟨ Coeq₂.equality) ○ -+-.homomorphism
      ; coequalize = coequalize
      ; universal = universal _
      ; unique = uniq _
      }
    where
      open IsRightExact
      open RightExactFunctor
      module Coeq₁ = IsCoequalizer (F-resp-coeq (isRightExact (π₁ {𝒞} {𝒞})) isCoeq)
      module Coeq₂ = IsCoequalizer (F-resp-coeq (isRightExact (π₂ {𝒞} {𝒞})) isCoeq)
      open 𝒞 using ([]-cong₂; +₁∘i₁; +₁∘i₂; []∘+₁; +-g-η)
      open 𝒞 using (Obj; _≈_; module HomReasoning; assoc; sym-assoc)
      open 𝒞.HomReasoning
      open ⇒-Reasoning 𝒞.U

      module _ {X : Obj} {k : B₁ + B₂ ⇒ X} (eq : k ∘ (f₁ +₁ f₂) ≈ k ∘ (g₁ +₁ g₂)) where

        eq₁ : (k ∘ i₁) ∘ f₁ ≈ (k ∘ i₁) ∘ g₁
        eq₁ = begin
            (k ∘ i₁) ∘ f₁       ≈⟨ pushʳ +₁∘i₁ ⟨
            k ∘ (f₁ +₁ f₂) ∘ i₁ ≈⟨ extendʳ eq ⟩
            k ∘ (g₁ +₁ g₂) ∘ i₁ ≈⟨ pushʳ +₁∘i₁ ⟩
            (k ∘ i₁) ∘ g₁       ∎

        eq₂ : (k ∘ i₂) ∘ f₂ ≈ (k ∘ i₂) ∘ g₂
        eq₂ = begin
            (k ∘ i₂) ∘ f₂       ≈⟨ pushʳ +₁∘i₂ ⟨
            k ∘ (f₁ +₁ f₂) ∘ i₂ ≈⟨ extendʳ eq ⟩
            k ∘ (g₁ +₁ g₂) ∘ i₂ ≈⟨ pushʳ +₁∘i₂ ⟩
            (k ∘ i₂) ∘ g₂       ∎

        coequalize : C₁ + C₂ ⇒ X
        coequalize = [ Coeq₁.coequalize eq₁ , Coeq₂.coequalize eq₂ ]

        universal : k ≈ coequalize ∘ (h₁ +₁ h₂)
        universal = begin
            k                                                         ≈⟨ +-g-η ⟨
            [ k ∘ i₁ , k ∘ i₂ ]                                       ≈⟨ []-cong₂ Coeq₁.universal Coeq₂.universal ⟩
            [ Coeq₁.coequalize eq₁ ∘ h₁ , Coeq₂.coequalize eq₂ ∘ h₂ ] ≈⟨ []∘+₁ ⟨
            coequalize ∘ (h₁ +₁ h₂)                                   ∎

        uniq : {i : C₁ + C₂ ⇒ X} → k ≈ i ∘ (h₁ +₁ h₂) → i ≈ coequalize
        uniq {i} eq′ = begin
            i                   ≈⟨ +-g-η ⟨
            [ i ∘ i₁ , i ∘ i₂ ] ≈⟨ []-cong₂ (Coeq₁.unique eq₁′) (Coeq₂.unique eq₂′) ⟩
            [ Coeq₁.coequalize eq₁ , Coeq₂.coequalize eq₂ ] ∎
          where
            eq₁′ : k ∘ i₁ ≈ (i ∘ i₁) ∘ h₁
            eq₁′ = eq′ ⟩∘⟨refl ○ extendˡ +₁∘i₁
            eq₂′ : k ∘ i₂ ≈ (i ∘ i₂) ∘ h₂
            eq₂′ = eq′ ⟩∘⟨refl ○ extendˡ +₁∘i₂

module _ {𝒞 : FinitelyCocompleteCategory o ℓ e} where

  open FinCoCom using (_⇒_; _∘_; id)
  module 𝒞 = FinitelyCocompleteCategory 𝒞

  -+- : 𝒞 × 𝒞 ⇒ 𝒞
  -+- = record
      { F = 𝒞.-+-
      ; isRightExact = record
          { F-resp-⊥ = +-resp-⊥ 𝒞
          ; F-resp-+ = +-resp-+ 𝒞
          ; F-resp-coeq = +-resp-coeq 𝒞
          }
      }
  module x+y = RightExactFunctor -+-

  ↔-+- : 𝒞 × 𝒞 ⇒ 𝒞
  ↔-+- = record
      { F = flip-bifunctor 𝒞.-+-
      ; isRightExact = record
          { F-resp-⊥ = λ x → +-resp-⊥ 𝒞 (flip-IsInitial 𝒞 x)
          ; F-resp-+ = λ x → +-resp-+ 𝒞 (flip-IsCoproduct 𝒞 x)
          ; F-resp-coeq = λ x → (+-resp-coeq 𝒞 (flip-IsCoequalizer 𝒞 x))
          }
      }
  module y+x = RightExactFunctor ↔-+-

  [x+y]+z : (𝒞 × 𝒞) × 𝒞 ⇒ 𝒞
  [x+y]+z = -+- ∘ (-+- ×₁ id)
  module [x+y]+z = RightExactFunctor [x+y]+z

  x+[y+z] : (𝒞 × 𝒞) × 𝒞 ⇒ 𝒞
  x+[y+z] = -+- ∘ (id ×₁ -+-) ∘ assocˡ
  module x+[y+z] = RightExactFunctor x+[y+z]

  assoc-≃ : [x+y]+z.F ≃ x+[y+z].F
  assoc-≃ = pointwise-iso (λ { ((X , Y) , Z) → ≅.sym (𝒞.+-assoc {X} {Y} {Z})}) commute
    where
      open 𝒞
      module 𝒞×𝒞×𝒞 = FinitelyCocompleteCategory ((𝒞 × 𝒞) × 𝒞)
      open Morphism U using (_≅_; module ≅)
      module +-assoc {X} {Y} {Z} = _≅_ (≅.sym (+-assoc {X} {Y} {Z}))
      open Equiv
      commute
          : {((X , Y) , Z) : 𝒞×𝒞×𝒞.Obj}
            {((X′ , Y′) , Z′) : 𝒞×𝒞×𝒞.Obj}
          → (F : ((X , Y) , Z) 𝒞×𝒞×𝒞.⇒ ((X′ , Y′) , Z′))
          → (+-assoc.from 𝒞.∘ [x+y]+z.₁ F)
          ≈ (x+[y+z].₁ F 𝒞.∘ +-assoc.from)
      commute {(X , Y) , Z} {(X′ , Y′) , Z′} ((F , G) , H) = sym +₁∘+-assocʳ
