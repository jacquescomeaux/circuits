{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --hidden-argument-puns #-}

module Data.Mat.Util where

import Data.Vec.Relation.Binary.Equality.Setoid as ≋
import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Data.Nat using (ℕ)
open import Data.Setoid using (∣_∣)
open import Data.Vec using (Vec; zipWith; foldr; map; replicate)
open import Level using (Level)
open import Relation.Binary using (Rel; Setoid; Monotonic₂)
open import Relation.Binary.PropositionalEquality as ≡ using (_≗_; _≡_; module ≡-Reasoning)

open ℕ
open Vec

private
  variable
    n m o p : ℕ
    ℓ : Level
    A B C D E : Set ℓ

transpose : Vec (Vec A n) m → Vec (Vec A m) n
transpose [] = replicate _ []
transpose (row ∷ mat) = zipWith _∷_ row (transpose mat)

transpose-empty : (m : ℕ) → transpose (replicate {A = Vec A zero} m []) ≡ []
transpose-empty zero = ≡.refl
transpose-empty (suc m) = ≡.cong (zipWith _∷_ []) (transpose-empty m)

transpose-zipWith : (V : Vec A m) (M : Vec (Vec A n) m) → transpose (zipWith _∷_ V M) ≡ V ∷ transpose M
transpose-zipWith [] [] = ≡.refl
transpose-zipWith (x ∷ V) (M₀ ∷ M) = ≡.cong (zipWith _∷_ (x ∷ M₀)) (transpose-zipWith V M)

transpose-involutive : (M : Vec (Vec A n) m) → transpose (transpose M) ≡ M
transpose-involutive {n} [] = transpose-empty n
transpose-involutive (V ∷ M) = begin
    transpose (zipWith _∷_ V (transpose M)) ≡⟨ transpose-zipWith V (transpose M) ⟩
    V ∷ transpose (transpose M)             ≡⟨ ≡.cong (V ∷_) (transpose-involutive M) ⟩
    V ∷ M ∎
  where
    open ≡.≡-Reasoning

map-replicate : (x : A) (v : Vec B n) → map (λ _ → x) v ≡ replicate n x
map-replicate x [] = ≡.refl
map-replicate x (y ∷ v) = ≡.cong (x ∷_) (map-replicate x v)

zipWith-map-map
    : (f : A → C)
      (g : B → D)
      (_⊕_ : C → D → E)
      (v : Vec A n)
      (w : Vec B n)
    → zipWith (λ x y → f x ⊕ g y) v w ≡ zipWith _⊕_ (map f v) (map g w)
zipWith-map-map f g _⊕_ [] [] = ≡.refl
zipWith-map-map f g _⊕_ (x ∷ v) (y ∷ w) = ≡.cong (f x ⊕ g y ∷_) (zipWith-map-map f g _⊕_ v w)

zipWith-map
    : (f : A → B)
      (g : A → C)
      (_⊕_ : B → C → D)
      (v : Vec A n)
    → zipWith _⊕_ (map f v) (map g v) ≡ map (λ x → f x ⊕ g x) v
zipWith-map f g _⊕_ [] = ≡.refl
zipWith-map f g _⊕_ (x ∷ v) = ≡.cong (f x ⊕ g x ∷_) (zipWith-map f g _⊕_ v)

map-zipWith
    : (f : C → D)
      (_⊕_ : A → B → C)
      (v : Vec A n)
      (w : Vec B n)
    → map f (zipWith _⊕_ v w) ≡ zipWith (λ x y → f (x ⊕ y)) v w
map-zipWith f _⊕_ [] [] = ≡.refl
map-zipWith f _⊕_ (x ∷ v) (y ∷ w) = ≡.cong (f (x ⊕ y) ∷_) (map-zipWith f _⊕_ v w)

module _ {c₁ c₂ ℓ₁ ℓ₂ : Level} {A : Setoid c₁ ℓ₁} (B : ℕ → Setoid c₂ ℓ₂) where

  private
    module A = Setoid A
    module B {n : ℕ} = Setoid (B n)
    module V = ≋ A

  foldr-cong
      : {f g : {k : ℕ} → ∣ A ∣ → ∣ B k ∣ → ∣ B (suc k) ∣}
      → ({k : ℕ} {w x : ∣ A ∣} {y z : ∣ B k ∣} → w A.≈ x → y B.≈ z → f w y B.≈ g x z)
      → {d e : ∣ B zero ∣}
      → d B.≈ e
      → {n : ℕ}
        {xs ys : Vec ∣ A ∣ n}
      → (xs V.≋ ys)
      → foldr (λ k → ∣ B k ∣) f d xs B.≈ foldr (λ k → ∣ B k ∣) g e ys
  foldr-cong _ d≈e PW.[] = d≈e
  foldr-cong cong d≈e (≈v₀ PW.∷ ≋v) = cong ≈v₀ (foldr-cong cong d≈e ≋v)

module _
    {a b c ℓ₁ ℓ₂ ℓ₃ : Level}
    {A : Set a} {B : Set b} {C : Set c}
    {f : A → B → C}
    {_∼₁_ : Rel A ℓ₁}
    {_∼₂_ : Rel B ℓ₂}
    {_∼₃_ : Rel C ℓ₃}
  where
  zipWith-cong
      : {n : ℕ}
        {ws xs : Vec A n}
        {ys zs : Vec B n}
      → Monotonic₂ _∼₁_ _∼₂_ _∼₃_ f
      → PW.Pointwise _∼₁_ ws xs
      → PW.Pointwise _∼₂_ ys zs
      → PW.Pointwise _∼₃_ (zipWith f ws ys) (zipWith f xs zs)
  zipWith-cong cong PW.[] PW.[] = PW.[]
  zipWith-cong cong (x∼y PW.∷ xs) (a∼b PW.∷ ys) = cong x∼y a∼b PW.∷ zipWith-cong cong xs ys

module _ {c ℓ : Level} (A : Setoid c ℓ) where

  private
    module A = Setoid A
    module V = ≋ A
    module M {n} = ≋ (V.≋-setoid n)

  transpose-cong
      : {n m : ℕ}
      → {M₁ M₂ : Vec (Vec ∣ A ∣ n) m}
      → M₁ M.≋ M₂
      → transpose M₁ M.≋ transpose M₂
  transpose-cong PW.[] = M.≋-refl
  transpose-cong (R₁≋R₂ PW.∷ M₁≋M₂) = zipWith-cong PW._∷_ R₁≋R₂ (transpose-cong M₁≋M₂)
