{-# OPTIONS --without-K --safe #-}
module FinMerge where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; fromℕ<; toℕ; #_)
open import Data.Fin.Properties using (¬Fin0)
open import Data.Nat using (ℕ; _+_; _≤_; z≤n; s≤s; _<_ ; z<s)
open import Data.Nat.Properties using (≤-trans)
open import Data.Sum.Base using (_⊎_)
open import Data.Product using (_×_; _,_; Σ-syntax; map₂; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Function using (id ; _∘_ ; _$_)
open import Data.Maybe.Base using (Maybe; just; nothing; fromMaybe)

open import Util using (_<_<_; _<_≤_; toℕ<; Ordering; less; equal; greater; compare)


private
  variable
    m n : ℕ

-- Send the specified m to nothing
pluck : m ≤ n → Fin (ℕ.suc n) → Maybe (Fin n)
pluck z≤n Fin.zero = nothing
pluck z≤n (Fin.suc x) = just x
pluck (s≤s m) Fin.zero = just Fin.zero
pluck (s≤s m) (Fin.suc x) = Data.Maybe.Base.map Fin.suc (pluck m x)

-- Send nothing to the specified m
unpluck : m ≤ n → Maybe (Fin n) → Fin (ℕ.suc n)
unpluck z≤n nothing = Fin.zero
unpluck z≤n (just x) = Fin.suc x
unpluck (s≤s m) nothing = Fin.suc (unpluck m nothing)
unpluck (s≤s m) (just Fin.zero) = Fin.zero
unpluck (s≤s m) (just (Fin.suc x)) = Fin.suc (unpluck m (just x))

-- Merge two elements of a finite set
merge : {i j : ℕ} → i < j ≤ n → Fin (ℕ.suc n) → Fin n
merge (lt , le) x = fromMaybe (fromℕ< (≤-trans lt le)) (pluck le x)

-- Merge two elements of a finite set
unmerge : {i j : ℕ} → i < j ≤ n → Fin n → Fin (ℕ.suc n)
unmerge (lt , le) x = unpluck le (just x)

glue-once : {i j : Fin (ℕ.suc n)} → Ordering i j → Σ[ x ∈ ℕ ] (Fin (ℕ.suc n) → Fin x)
glue-once {n} (less (i<j , s≤s j≤n)) = n , merge (i<j , j≤n)
glue-once {n} (equal i≡j) = ℕ.suc n , id
glue-once {n} (greater (j<i , s≤s i≤n)) = n , merge (j<i , i≤n)

glue-unglue-once
    : {i j : Fin (ℕ.suc n)}
    → Ordering i j
    → Σ[ x ∈ ℕ ] ((Fin (ℕ.suc n) → Fin x) × (Fin x → Fin (ℕ.suc n)))
glue-unglue-once {n} (less (i<j , s≤s j≤n)) = n , merge (i<j , j≤n) , unmerge (i<j , j≤n)
glue-unglue-once {n} (equal i≡j) = ℕ.suc n , id , id
glue-unglue-once {n} (greater (j<i , s≤s i≤n)) = n , merge (j<i , i≤n) , unmerge (j<i , i≤n)

-- Glue together the image of two finite-set functions
glue : (Fin m → Fin n) → (Fin m → Fin n) → Σ[ x ∈ ℕ ] (Fin n → Fin x)
glue {ℕ.zero} {n} _ _ = n , id
glue {ℕ.suc _} {ℕ.zero} f _ = ⊥-elim (¬Fin0 (f (# 0)))
glue {ℕ.suc _} {ℕ.suc _} f g with glue (f ∘ Fin.suc) (g ∘ Fin.suc)
... | ℕ.zero , h = ⊥-elim (¬Fin0 (h (# 0)))
... | ℕ.suc _ , h = map₂ (_∘ h) (glue-once (compare (h (f (# 0))) (h (g (# 0)))))

-- Glue together the image of two finite-set functions, iterative
glue-iter
    : {y : ℕ}
    → (Fin m → Fin y)
    → (Fin m → Fin y)
    → (Fin n → Fin y)
    → Σ[ x ∈ ℕ ] (Fin n → Fin x)
glue-iter {ℕ.zero} {n} {y} f g h = y , h
glue-iter {ℕ.suc m} {n} {ℕ.zero} f g h = ⊥-elim (¬Fin0 (f (# 0)))
glue-iter {ℕ.suc m} {n} {ℕ.suc y} f g h =
    let p = proj₁ (proj₂ (glue-unglue-once (compare (f (# 0)) (g (# 0))))) in
    glue-iter (p ∘ f ∘ Fin.suc) (p ∘ g ∘ Fin.suc) (p ∘ h)
