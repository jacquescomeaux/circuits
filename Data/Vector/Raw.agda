{-# OPTIONS --without-K --safe #-}

module Data.Vector.Raw where

open import Data.Nat using (ℕ; _+_)
open import Data.Vec using (Vec; head; tail; map; _++_; replicate; zipWith)
open import Data.Vec.Properties using (map-replicate)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise)
open import Level using (Level)
open import Relation.Binary using (REL)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

private
  variable
    n m : ℕ
    a ℓ ℓ₁ ℓ₂ : Level
    A B C D E F : Set a

open ℕ
open Vec

⟨⟩ : Vec A 0
⟨⟩ = []

⟨⟩-! : (V : Vec A 0) → V ≡ ⟨⟩
⟨⟩-! [] = ≡.refl

⟨⟩-++ : {n : ℕ} (V : Vec A n) → ⟨⟩ ++ V ≡ V
⟨⟩-++ V = ≡.refl

module Natural {n : ℕ} (f : A → B) where

  α-head : (V : Vec A (suc n)) → f (head V) ≡ head (map f V)
  α-head (x ∷ _) = ≡.erefl (f x)

  α-tail : (V : Vec A (suc n)) → map f (tail V) ≡ tail (map f V)
  α-tail (_ ∷ V) = ≡.erefl (map f V)

  α-replicate : {x : A} → map f (replicate n x) ≡ replicate n (f x)
  α-replicate {x} = map-replicate f x n

open Natural public

open Pointwise

module Relation {R : REL A B ℓ} where

  R-head
      : {V₁ : Vec A (suc n)}
        {V₂ : Vec B (suc n)}
      → Pointwise R V₁ V₂
      → R (head V₁) (head V₂)
  R-head (R-x ∷ _) = R-x

  R-tail
      : {V₁ : Vec A (suc n)}
        {V₂ : Vec B (suc n)}
      → Pointwise R V₁ V₂
      → Pointwise R (tail V₁) (tail V₂)
  R-tail (_ ∷ R-V) = R-V

  R-++
      : {R : REL A B ℓ}
        {V₁ : Vec A m}
        {V₂ : Vec B m}
        {W₁ : Vec A n}
        {W₂ : Vec B n}
      → Pointwise R V₁ V₂
      → Pointwise R W₁ W₂
      → Pointwise R (V₁ ++ W₁) (V₂ ++ W₂)
  R-++ [] R-W = R-W
  R-++ (R-v ∷ R-V) R-W = R-v ∷ R-++ R-V R-W

  R-replicate : {x : A} {y : B} → R x y → Pointwise R (replicate n x) (replicate n y)
  R-replicate {n = zero} _ = []
  R-replicate {n = suc n} xRy = xRy ∷ R-replicate xRy

R-zipWith
    : {W : Vec A n}
      {X : Vec B n}
      {Y : Vec C n}
      {Z : Vec D n}
      {R : REL A B ℓ₁}
      {S : REL C D ℓ₂}
      {T : REL E F ℓ}
      {f : A → C → E}
      {g : B → D → F}
    → (∀ {w x y z} → R w x → S y z → T (f w y) (g x z))
    → Pointwise R W X
    → Pointwise S Y Z
    → Pointwise T (zipWith f W Y) (zipWith g X Z)
R-zipWith cong [] [] = []
R-zipWith cong (wRx ∷ WRX) (ySz ∷ YSZ) = cong wRx ySz ∷ R-zipWith cong WRX YSZ

open Relation public
