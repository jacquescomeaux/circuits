module FinMerge where

open import Data.Fin using (Fin; splitAt; join; fromℕ<; cast)
open import Data.Nat using (ℕ; _+_; _≤_; _<_)
open import Data.Nat.Properties using (+-comm)
open import Data.Sum.Base using (_⊎_)
open import Data.Product using (_×_; _,_; Σ-syntax; map₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Function using (_$_)


_<_≤_ : ℕ → ℕ → ℕ → Set
_<_≤_ i j k = (i < j) × (j ≤ k)

_<_<_ : ℕ → ℕ → ℕ → Set
_<_<_ i j k = (i < j) × (j < k)

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
merge : (i j : ℕ) → i < j ≤ n → Fin (ℕ.suc n) → Fin n
merge {n} i j (lt , le) x with splitℕ le
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
