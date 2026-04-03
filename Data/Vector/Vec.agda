{-# OPTIONS --without-K --safe #-}

module Data.Vector.Vec where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; _+_)
open import Data.Vec using (Vec; tabulate; zipWith; replicate; map; _++_)
open import Function using (_∘_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open Vec
open ℕ
open Fin

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e
    n : ℕ

zipWith-tabulate
    : {n : ℕ}
      (_⊕_ : A → A → A)
      (f g : Fin n → A)
    → zipWith _⊕_ (tabulate f) (tabulate g) ≡ tabulate (λ i → f i ⊕ g i)
zipWith-tabulate {n = zero} _⊕_ f g = ≡.refl
zipWith-tabulate {n = suc n} _⊕_ f g = ≡.cong (f zero ⊕ g zero ∷_) (zipWith-tabulate _⊕_ (f ∘ suc) (g ∘ suc))

replicate-tabulate
    : {n : ℕ}
      (x : A)
    → replicate n x ≡ tabulate (λ _ → x)
replicate-tabulate {n = zero} x = ≡.refl
replicate-tabulate {n = suc n} x = ≡.cong (x ∷_) (replicate-tabulate x)

zipWith-map
    : {n : ℕ}
      (f : A → B)
      (g : A → C)
      (_⊕_ : B → C → D)
      (v : Vec A n)
    → zipWith _⊕_ (map f v) (map g v) ≡ map (λ x → f x ⊕ g x) v
zipWith-map f g _⊕_ [] = ≡.refl
zipWith-map f g _⊕_ (x ∷ v) = ≡.cong (f x ⊕ g x ∷_) (zipWith-map f g _⊕_ v)

replicate-++ : (n m : ℕ) (x : A) → replicate n x ++ replicate m x ≡ replicate (n + m) x
replicate-++ zero _ x = ≡.refl
replicate-++ (suc n) m x = ≡.cong (x ∷_) (replicate-++ n m x)

map-zipWith
    : (f : C → D)
      (_⊕_ : A → B → C)
      {n : ℕ}
      (v : Vec A n)
      (w : Vec B n)
    → map f (zipWith _⊕_ v w) ≡ zipWith (λ x y → f (x ⊕ y)) v w
map-zipWith f _⊕_ [] [] = ≡.refl
map-zipWith f _⊕_ (x ∷ v) (y ∷ w) = ≡.cong (f (x ⊕ y) ∷_) (map-zipWith f _⊕_ v w)

zipWith-map-map
    : (f : A → C)
      (g : B → D)
      (_⊕_ : C → D → E)
      (v : Vec A n)
      (w : Vec B n)
    → zipWith (λ x y → f x ⊕ g y) v w ≡ zipWith _⊕_ (map f v) (map g w)
zipWith-map-map f g _⊕_ [] [] = ≡.refl
zipWith-map-map f g _⊕_ (x ∷ v) (y ∷ w) = ≡.cong (f x ⊕ g y ∷_) (zipWith-map-map f g _⊕_ v w)
