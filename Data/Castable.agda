{-# OPTIONS --without-K --safe #-}

module Data.Castable where

open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; module ≡-Reasoning)
open import Relation.Binary using (Sym; Trans; _⇒_)

record IsCastable {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} (B : A → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where

  field
    cast : {e e′ : A} → .(e ≡ e′) → B e → B e′
    cast-trans
        : {m n o : A}
        → .(eq₁ : m ≡ n)
          .(eq₂ : n ≡ o)
          (x : B m)
        → cast eq₂ (cast eq₁ x) ≡ cast (trans eq₁ eq₂) x
    cast-is-id : {m : A} .(eq : m ≡ m) (x : B m) → cast eq x ≡ x
    subst-is-cast : {m n : A} (eq : m ≡ n) (x : B m) → subst B eq x ≡ cast eq x

  infix 3 _≈[_]_
  _≈[_]_ : {n m : A} → B n → .(eq : n ≡ m) → B m → Set ℓ₂
  _≈[_]_ x eq y = cast eq x ≡ y

  ≈-reflexive : {n : A} → _≡_ ⇒ (λ xs ys → _≈[_]_ {n} xs refl ys)
  ≈-reflexive {n} {x} {y} eq = trans (cast-is-id refl x) eq

  ≈-sym : {m n : A} .{m≡n : m ≡ n} → Sym _≈[ m≡n ]_ _≈[ sym m≡n ]_
  ≈-sym {m} {n} {m≡n} {x} {y} x≡y = begin
      cast (sym m≡n) y             ≡⟨ cong (cast (sym m≡n)) x≡y ⟨
      cast (sym m≡n) (cast m≡n x)  ≡⟨ cast-trans m≡n (sym m≡n) x ⟩
      cast (trans m≡n (sym m≡n)) x ≡⟨ cast-is-id (trans m≡n (sym m≡n)) x ⟩
      x ∎
    where
      open ≡-Reasoning

  ≈-trans : {m n o : A} .{m≡n : m ≡ n} .{n≡o : n ≡ o} → Trans _≈[ m≡n ]_ _≈[ n≡o ]_ _≈[ trans m≡n n≡o ]_
  ≈-trans {m} {n} {o} {m≡n} {n≡o} {x} {y} {z} x≡y y≡z = begin
      cast (trans m≡n n≡o) x  ≡⟨ cast-trans m≡n n≡o x ⟨
      cast n≡o (cast m≡n x)   ≡⟨ cong (cast n≡o) x≡y ⟩
      cast n≡o y              ≡⟨ y≡z ⟩
      z ∎
    where
      open ≡-Reasoning

record Castable {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  field
    B : A → Set ℓ₂
    isCastable : IsCastable B
