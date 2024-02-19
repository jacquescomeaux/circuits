module FinMerge where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; splitAt; join; fromℕ<; cast; toℕ; #_) renaming (_<_ to _<′_)
open import Data.Fin.Properties using (¬Fin0)
open import Data.Nat using (ℕ; _+_; _≤_; _<_ ; z<s)
open import Data.Nat.Properties using (+-comm; <⇒≤)
open import Data.Sum.Base using (_⊎_)
open import Data.Product using (_×_; _,_; Σ-syntax; map₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Function using (id ; _∘_ ; _$_)


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

-- Send the 0th index of the right set to the specified index of the left
merge0 : (i : Fin m) → Fin m ⊎ Fin (ℕ.suc n) → Fin m ⊎ Fin n
merge0 i (_⊎_.inj₁ x) = _⊎_.inj₁ x
merge0 i (_⊎_.inj₂ Fin.zero) = _⊎_.inj₁ i
merge0 i (_⊎_.inj₂ (Fin.suc y)) = _⊎_.inj₂ y

-- Split a natural number into two parts
splitℕ : m ≤ n → Σ[ m′ ∈ ℕ ] n ≡ m + m′
splitℕ  _≤_.z≤n = _ , refl
splitℕ (_≤_.s≤s le) = map₂ (cong ℕ.suc) (splitℕ le)

-- Merge two elements of a finite set
merge : {i j : ℕ} → i < j ≤ n → Fin (ℕ.suc n) → Fin n
merge {n} {i} {j} (lt , le) x with splitℕ le
... | j′ , n≡j+j′ =
    cast (sym n≡j+j′) $
    join j j′ $
    merge0 (fromℕ< lt) $
    splitAt j $
    cast Sn≡j+Sj′ x
  where
    open ≡-Reasoning
    Sn≡j+Sj′ : ℕ.suc n ≡ j + ℕ.suc j′
    Sn≡j+Sj′ = begin
        ℕ.suc n         ≡⟨ cong ℕ.suc (n≡j+j′) ⟩
        ℕ.suc (j + j′)  ≡⟨ cong ℕ.suc (+-comm j j′) ⟩
        ℕ.suc (j′ + j)  ≡⟨⟩
        ℕ.suc j′ + j    ≡⟨ +-comm (ℕ.suc j′) j ⟩
        j + ℕ.suc j′ ∎

-- Glue together the image of two finite-set functions
glue : (Fin m → Fin n) → (Fin m → Fin n) → Σ[ x ∈ ℕ ] (Fin n → Fin x)
glue {ℕ.zero} {n} _ _ = n , id
glue {ℕ.suc _} {ℕ.zero} f _ = ⊥-elim (¬Fin0 (f (# 0)))
glue {ℕ.suc _} {ℕ.suc n} f g with glue (f ∘ Fin.suc) (g ∘ Fin.suc)
... | ℕ.zero , h = ⊥-elim (¬Fin0 (h (# 0)))
... | ℕ.suc x , h with compare (h (f (# 0))) (h (g (# 0)))
...     | less (f0<g0 , _≤_.s≤s g0<n) = x , merge (f0<g0 , g0<n) ∘ h
...     | equal f0≡g0 = ℕ.suc x , h
...     | greater (g0<f0 , _≤_.s≤s f0<n) = x , merge (g0<f0 , f0<n) ∘ h
