module FinMerge where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; fromℕ<; toℕ; #_)
open import Data.Fin.Properties using (¬Fin0)
open import Data.Nat using (ℕ; _+_; _≤_; _<_ ; z<s)
open import Data.Nat.Properties using (≤-trans)
open import Data.Sum.Base using (_⊎_)
open import Data.Product using (_×_; _,_; Σ-syntax; map₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Function using (id ; _∘_ ; _$_)
open import Data.Maybe.Base using (Maybe; just; nothing; fromMaybe)


_<_≤_ : ℕ → ℕ → ℕ → Set
_<_≤_ i j k = (i < j) × (j ≤ k)

_<_<_ : ℕ → ℕ → ℕ → Set
_<_<_ i j k = (i < j) × (j < k)

toℕ< : {n : ℕ} → (i : Fin n) → toℕ i < n
toℕ< Fin.zero = z<s
toℕ< (Fin.suc i) = _≤_.s≤s (toℕ< i)

data Ordering {n : ℕ} : Fin n → Fin n → Set where
  less : ∀ {i j} → toℕ i < toℕ j < n → Ordering i j
  equal : ∀ {i j} → toℕ i ≡ toℕ j → Ordering i j
  greater : ∀ {i j} → toℕ j < toℕ i < n → Ordering i j

compare : ∀ {n : ℕ} (i j : Fin n) → Ordering i j
compare Fin.zero Fin.zero = equal refl
compare Fin.zero j@(Fin.suc _) = less (z<s , toℕ< j)
compare i@(Fin.suc _) Fin.zero = greater (z<s , toℕ< i)
compare (Fin.suc i) (Fin.suc j) with compare i j
... | less (i<j , j<n) = less (_≤_.s≤s i<j , _≤_.s≤s j<n)
... | equal i≡j = equal (cong ℕ.suc i≡j)
... | greater (j<i , i<n) = greater (_≤_.s≤s j<i , _≤_.s≤s i<n)

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
...     | less (f0<g0 , _≤_.s≤s g0<n) = x , merge (f0<g0 , g0<n) ∘ h
...     | equal f0≡g0 = ℕ.suc x , h
...     | greater (g0<f0 , _≤_.s≤s f0<n) = x , merge (g0<f0 , f0<n) ∘ h
