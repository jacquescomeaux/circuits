{-# OPTIONS --without-K --safe #-}

module Data.Vector.Vec where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; tabulate; zipWith; replicate)
open import Function using (_∘_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open Vec
open ℕ
open Fin

zipWith-tabulate
    : {a : Level}
      {A : Set a}
      {n : ℕ}
      (_⊕_ : A → A → A)
      (f g : Fin n → A)
    → zipWith _⊕_ (tabulate f) (tabulate g) ≡ tabulate (λ i → f i ⊕ g i)
zipWith-tabulate {n = zero} _⊕_ f g = ≡.refl
zipWith-tabulate {n = suc n} _⊕_ f g = ≡.cong (f zero ⊕ g zero ∷_) (zipWith-tabulate _⊕_ (f ∘ suc) (g ∘ suc))

replicate-tabulate
    : {a : Level}
      {A : Set a}
      {n : ℕ}
      (x : A)
    → replicate n x ≡ tabulate (λ _ → x)
replicate-tabulate {n = zero} x = ≡.refl
replicate-tabulate {n = suc n} x = ≡.cong (x ∷_) (replicate-tabulate x)
