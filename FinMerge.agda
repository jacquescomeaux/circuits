module FinMerge where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; fromℕ<; toℕ; #_)
open import Data.Fin.Properties using (¬Fin0)
open import Data.Nat using (ℕ; _+_; _≤_; _<_ ; z<s; s≤s)
open import Data.Nat.Properties using (≤-trans)
open import Data.Sum.Base using (_⊎_)
open import Data.Product using (_×_; _,_; Σ-syntax; map₂)
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
pluck _≤_.z≤n Fin.zero = nothing
pluck _≤_.z≤n (Fin.suc x) = just x
pluck (_≤_.s≤s m) Fin.zero = just Fin.zero
pluck (_≤_.s≤s m) (Fin.suc x) = Data.Maybe.Base.map Fin.suc (pluck m x)

-- Merge two elements of a finite set
merge : {i j : ℕ} → i < j ≤ n → Fin (ℕ.suc n) → Fin n
merge (lt , le) x = fromMaybe (fromℕ< (≤-trans lt le)) (pluck le x)

-- Glue together the image of two finite-set functions
glue : (Fin m → Fin n) → (Fin m → Fin n) → Σ[ x ∈ ℕ ] (Fin n → Fin x)
glue {ℕ.zero} {n} _ _ = n , id
glue {ℕ.suc _} {ℕ.zero} f _ = ⊥-elim (¬Fin0 (f (# 0)))
glue {ℕ.suc _} {ℕ.suc _} f g with glue (f ∘ Fin.suc) (g ∘ Fin.suc)
... | ℕ.zero , h = ⊥-elim (¬Fin0 (h (# 0)))
... | ℕ.suc x , h with compare (h (f (# 0))) (h (g (# 0)))
...     | less (f0<g0 , s≤s g0<n) = x , merge (f0<g0 , g0<n) ∘ h
...     | equal f0≡g0 = ℕ.suc x , h
...     | greater (g0<f0 , s≤s f0<n) = x , merge (g0<f0 , f0<n) ∘ h

-- Glue together the image of two finite-set functions, iterative
glue-iter
    : {y : ℕ}
    → (Fin m → Fin y)
    → (Fin m → Fin y)
    → (Fin n → Fin y)
    → Σ[ x ∈ ℕ ] (Fin n → Fin x)
glue-iter {ℕ.zero} {n} {y} f g h = y , h
glue-iter {ℕ.suc m} {n} {y} f g h with compare (f (# 0)) (g (# 0))
... | less (f0<g0 , s≤s g0≤n) =
        let p = merge (f0<g0 , g0≤n) in
        glue-iter (p ∘ f ∘ Fin.suc) (p ∘ g ∘ Fin.suc) (p ∘ h)
... | equal _ = glue-iter (f ∘ Fin.suc) (g ∘ Fin.suc) h
... | greater (g0<f0 , s≤s f0≤n) =
        let p = merge (g0<f0 , f0≤n) in
        glue-iter (p ∘ f ∘ Fin.suc) (p ∘ g ∘ Fin.suc) (p ∘ h)
