{-# OPTIONS --without-K --safe #-}

open import Level using (Level)
open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)

module Functor.Exact.Instance.Swap {o ℓ e : Level} (𝒞 𝒟 : FinitelyCocompleteCategory o ℓ e) where

open import Categories.Category using (_[_,_])
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Product using (Product) renaming (Swap to Swap′)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Diagram.Coequalizer using (IsCoequalizer)
open import Categories.Object.Initial using (IsInitial)
open import Categories.Object.Coproduct using (IsCoproduct)
open import Data.Product.Base using (_,_; proj₁; proj₂; swap)

open import Category.Instance.FinitelyCocompletes {o} {ℓ} {e} using (FinitelyCocompletes-Cartesian)
open import Functor.Exact using (RightExactFunctor)

module FCC = Cartesian FinitelyCocompletes-Cartesian
open BinaryProducts (FCC.products) using (_×_) -- ; π₁; π₂; _⁂_; assocˡ)


module 𝒞 = FinitelyCocompleteCategory 𝒞
module 𝒟 = FinitelyCocompleteCategory 𝒟

swap-resp-⊥ : {A : 𝒞.Obj} {B : 𝒟.Obj} → IsInitial (Product 𝒞.U 𝒟.U) (A , B) → IsInitial (Product 𝒟.U 𝒞.U) (B , A)
swap-resp-⊥ {A} {B} isInitial = record
    { ! = swap !
    ; !-unique = λ { (f , g) → swap (!-unique (g , f)) }
    }
  where
    open IsInitial isInitial

swap-resp-+
    : {A₁ B₁ A+B₁ : 𝒞.Obj}
    → {A₂ B₂ A+B₂ : 𝒟.Obj}
    → {i₁₁ : 𝒞.U [ A₁ , A+B₁ ]}
    → {i₂₁ : 𝒞.U [ B₁ , A+B₁ ]}
    → {i₁₂ : 𝒟.U [ A₂ , A+B₂ ]}
    → {i₂₂ : 𝒟.U [ B₂ , A+B₂ ]}
    → IsCoproduct (Product 𝒞.U 𝒟.U) (i₁₁ , i₁₂) (i₂₁ , i₂₂)
    → IsCoproduct (Product 𝒟.U 𝒞.U) (i₁₂ , i₁₁) (i₂₂ , i₂₁)
swap-resp-+ {A₁} {B₁} {A+B₁} {A₂} {B₂} {A+B₂} {i₁₁} {i₂₁} {i₁₂} {i₂₂} isCoproduct = record
    { [_,_] = λ { X Y → swap ([ swap X , swap Y ]) }
    ; inject₁ = swap inject₁
    ; inject₂ = swap inject₂
    ; unique = λ { ≈₁ ≈₂ → swap (unique (swap ≈₁) (swap ≈₂)) }
    }
  where
    open IsCoproduct isCoproduct

swap-resp-coeq
    : {A₁ B₁ C₁ : 𝒞.Obj} 
      {A₂ B₂ C₂ : 𝒟.Obj}
      {f₁ g₁ : 𝒞.U [ A₁ , B₁ ]}
      {h₁ : 𝒞.U [ B₁ , C₁ ]}
      {f₂ g₂ : 𝒟.U [ A₂ , B₂ ]}
      {h₂ : 𝒟.U [ B₂ , C₂ ]}
    → IsCoequalizer (Product 𝒞.U 𝒟.U) (f₁ , f₂) (g₁ , g₂) (h₁ , h₂)
    → IsCoequalizer (Product 𝒟.U 𝒞.U) (f₂ , f₁) (g₂ , g₁) (h₂ , h₁)
swap-resp-coeq isCoequalizer = record
    { equality = swap equality
    ; coequalize = λ { x → swap (coequalize (swap x)) }
    ; universal = swap universal
    ; unique = λ { x → swap (unique (swap x)) }
    }
  where
    open IsCoequalizer isCoequalizer

Swap : RightExactFunctor (𝒞 × 𝒟) (𝒟 × 𝒞)
Swap = record
    { F = Swap′
    ; isRightExact = record
        { F-resp-⊥ = swap-resp-⊥
        ; F-resp-+ = swap-resp-+
        ; F-resp-coeq = swap-resp-coeq
        }
    }
