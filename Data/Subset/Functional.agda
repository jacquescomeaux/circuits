{-# OPTIONS --without-K --safe #-}

module Data.Subset.Functional where

open import Data.Bool.Base using (Bool; _∨_; _∧_; if_then_else_)
open import Data.Bool.Properties using (if-float)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Permutation using (Permutation′; _⟨$⟩ʳ_; _⟨$⟩ˡ_; inverseˡ; inverseʳ)
open import Data.Fin.Properties using (suc-injective; 0≢1+n)
open import Data.Nat.Base using (ℕ)
open import Function.Base using (∣_⟩-_; _∘_)
open import Function.Definitions using (Injective)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_; _≢_)
open import Data.Vector as V using (Vector; head; tail)

open Bool
open Fin
open ℕ

Subset : ℕ → Set
Subset = Vector Bool

private
  variable n A : ℕ
  variable B C : Set

⊥ : Subset n
⊥ _ = false

_∪_ : Subset n → Subset n → Subset n
(A ∪ B) k = A k ∨ B k

_∩_ : Subset n → Subset n → Subset n
(A ∩ B) k = A k ∧ B k

⁅_⁆ : Fin n → Subset n
⁅_⁆ zero zero = true
⁅_⁆ zero (suc _) = false
⁅_⁆ (suc k) zero = false
⁅_⁆ (suc k) (suc i) = ⁅ k ⁆ i

⁅⁆-refl : (k : Fin n) → ⁅ k ⁆ k ≡ true
⁅⁆-refl zero = ≡.refl
⁅⁆-refl (suc k) = ⁅⁆-refl k

⁅x⁆y≡true
    : (x y : Fin n)
    → .(⁅ x ⁆ y ≡ true)
    → x ≡ y
⁅x⁆y≡true zero zero prf = ≡.refl
⁅x⁆y≡true (suc x) (suc y) prf = ≡.cong suc (⁅x⁆y≡true x y prf)

⁅x⁆y≡false
    : (x y : Fin n)
    → .(⁅ x ⁆ y ≡ false)
    → x ≢ y
⁅x⁆y≡false zero (suc y) prf = 0≢1+n
⁅x⁆y≡false (suc x) zero prf = 0≢1+n ∘ ≡.sym
⁅x⁆y≡false (suc x) (suc y) prf = ⁅x⁆y≡false x y prf ∘ suc-injective

f-⁅⁆
    : {n m : ℕ}
      (f : Fin n → Fin m)
    → Injective _≡_ _≡_ f
    → (x y : Fin n)
    → ⁅ x ⁆ y ≡ ⁅ f x ⁆ (f y)
f-⁅⁆ f f-inj zero zero = ≡.sym (⁅⁆-refl (f zero))
f-⁅⁆ f f-inj zero (suc y) with ⁅ f zero ⁆ (f (suc y)) in eq
... | true with () ← f-inj (⁅x⁆y≡true (f zero) (f (suc y)) eq)
... | false = ≡.refl
f-⁅⁆ f f-inj (suc x) zero with ⁅ f (suc x) ⁆ (f zero) in eq
... | true with () ← f-inj (⁅x⁆y≡true (f (suc x)) (f zero) eq)
... | false = ≡.refl
f-⁅⁆ f f-inj (suc x) (suc y) = f-⁅⁆ (f ∘ suc) (suc-injective ∘ f-inj) x y

⁅⁆∘ρ
    : (ρ : Permutation′ (suc n))
      (x : Fin (suc n))
    → ⁅ ρ ⟨$⟩ʳ x ⁆ ≗ ⁅ x ⁆ ∘ (ρ ⟨$⟩ˡ_)
⁅⁆∘ρ {n} ρ x y = begin
    ⁅ ρ ⟨$⟩ʳ x ⁆ y                    ≡⟨ f-⁅⁆ (ρ ⟨$⟩ˡ_) ρˡ-inj (ρ ⟨$⟩ʳ x) y ⟩
    ⁅ ρ ⟨$⟩ˡ (ρ ⟨$⟩ʳ x) ⁆ (ρ ⟨$⟩ˡ y)  ≡⟨ ≡.cong (λ h → ⁅ h ⁆ (ρ ⟨$⟩ˡ y)) (inverseˡ ρ) ⟩
    ⁅ x ⁆ (ρ ⟨$⟩ˡ y)                  ∎
  where
    open ≡.≡-Reasoning
    ρˡ-inj : {x y : Fin (suc n)} → ρ ⟨$⟩ˡ x ≡ ρ ⟨$⟩ˡ y → x ≡ y
    ρˡ-inj {x} {y} ρˡx≡ρˡy = begin
        x                 ≡⟨ inverseʳ ρ ⟨
        ρ ⟨$⟩ʳ (ρ ⟨$⟩ˡ x) ≡⟨ ≡.cong (ρ ⟨$⟩ʳ_) ρˡx≡ρˡy ⟩
        ρ ⟨$⟩ʳ (ρ ⟨$⟩ˡ y) ≡⟨ inverseʳ ρ ⟩
        y                 ∎

opaque
  -- TODO dependent fold
  foldl : (B → Fin A → B) → B → Subset A → B
  foldl {B = B} f = V.foldl (λ _ → B) (λ { {k} acc b → if b then f acc k else acc })

  foldl-cong₁
      : {f g : B → Fin A → B}
      → (∀ x y → f x y ≡ g x y)
      → (e : B)
      → (S : Subset A)
      → foldl f e S ≡ foldl g e S
  foldl-cong₁ {B = B} f≗g e S = V.foldl-cong (λ _ → B) (λ { {k} x y → ≡.cong (if y then_else x) (f≗g x k) }) e S

  foldl-cong₂
      : (f : B → Fin A → B)
        (e : B)
        {S₁ S₂ : Subset A}
      → (S₁ ≗ S₂)
      → foldl f e S₁ ≡ foldl f e S₂
  foldl-cong₂ {B = B} f e S₁≗S₂ = V.foldl-cong-arg (λ _ → B) (λ {n} acc b → if b then f acc n else acc) e S₁≗S₂

  foldl-suc
      : (f : B → Fin (suc A) → B)
      → (e : B)
      → (S : Subset (suc A))
      → foldl f e S ≡ foldl (∣ f ⟩- suc) (if head S then f e zero else e) (tail S)
  foldl-suc f e S = ≡.refl

  foldl-⊥
      : {A : ℕ}
        {B : Set}
        (f : B → Fin A → B)
        (e : B)
      → foldl f e ⊥ ≡ e
  foldl-⊥ {zero} _ _ = ≡.refl
  foldl-⊥ {suc A} f e = foldl-⊥ (∣ f ⟩- suc) e

  foldl-⁅⁆
      : (f : B → Fin A → B)
        (e : B)
        (k : Fin A)
      → foldl f e ⁅ k ⁆ ≡ f e k
  foldl-⁅⁆ f e zero = foldl-⊥ f (f e zero)
  foldl-⁅⁆ f e (suc k) = foldl-⁅⁆ (∣ f ⟩- suc) e k

  foldl-fusion
      : (h : C → B)
        {f : C → Fin A → C}
        {g : B → Fin A → B}
      → (∀ x n → h (f x n) ≡ g (h x) n)
      → (e : C)
      → h ∘ foldl f e ≗ foldl g (h e)
  foldl-fusion {C = C} {A = A} h {f} {g} fuse e = V.foldl-fusion h ≡.refl fuse′
    where
      open ≡.≡-Reasoning
      fuse′
          : {k : Fin A}
            (acc : C)
            (b : Bool)
          → h (if b then f acc k else acc) ≡ (if b then g (h acc) k else h acc)
      fuse′ {k} acc b = begin
          h (if b then f acc k else acc)      ≡⟨ if-float h b ⟩
          (if b then h (f acc k) else h acc)  ≡⟨ ≡.cong (if b then_else h acc) (fuse acc k) ⟩
          (if b then g (h acc) k else h acc)  ∎

Subset0≗⊥ : (S : Subset 0) → S ≗ ⊥
Subset0≗⊥ S ()

foldl-[] : (f : B → Fin 0 → B) (e : B) (S : Subset 0) → foldl f e S ≡ e
foldl-[] f e S = ≡.trans (foldl-cong₂ f e (Subset0≗⊥ S)) (foldl-⊥ f e)
