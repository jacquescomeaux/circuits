{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (CommutativeSemiring)
open import Level using (Level)

module Data.Matrix.SemiadditiveDagger {c ℓ : Level} (R : CommutativeSemiring c ℓ) where

module R = CommutativeSemiring R

import Data.Nat as ℕ
import Data.Nat.Properties as ℕ-Props
import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Dagger using (HasDagger)
open import Categories.Object.Biproduct using (Biproduct)
open import Categories.Object.Coproduct using (IsCoproduct)
open import Categories.Object.Initial using (IsInitial)
open import Categories.Object.Product using (IsProduct)
open import Categories.Object.Terminal using (IsTerminal)
open import Categories.Object.Zero using (Zero)
open import Category.Dagger.Semiadditive using (SemiadditiveDagger)
open import Category.Semiadditive using (Semiadditive)
open import Data.Matrix.Category R.semiring using (Mat; _·_; ≑-·; ·-Iˡ; ·-Iʳ; ·-𝟎ˡ; ·-𝟎ʳ; ·-∥; ∥-·-≑; ·-resp-≋; ·-assoc)
open import Data.Matrix.Core R.setoid using (Matrix; Matrixₛ; _≋_; module ≋; ∥-cong; ≑-cong; ᵀ-cong)
open import Data.Matrix.Monoid R.+-monoid using (𝟎; 𝟎ᵀ; 𝟎≑𝟎; 𝟎∥𝟎; _[+]_; [+]-cong; [+]-𝟎ˡ; [+]-𝟎ʳ)
open import Data.Matrix.Raw using (_ᵀ; _ᵀᵀ; mapRows; []ᵥ; []ᵥ-∥; []ₕ; []ₕ-!; []ₕ-≑; _∷ᵥ_; _∷ₕ_; ∷ᵥ-ᵀ; _∥_; _≑_; ∷ₕ-ᵀ; ∷ₕ-≑; []ᵥ-ᵀ; head-∷-tailₕ; headₕ; tailₕ; ∷ₕ-∥; ∷ᵥ-≑; []ᵥ-!)
open import Data.Matrix.Transform R.semiring using (I; Iᵀ; [_]_; _[_]; -[-]ᵀ; [-]--cong; [-]-[]ᵥ; [⟨⟩]-[]ₕ)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; Σ-syntax)
open import Data.Vec using (Vec; map; replicate; _++_)
open import Data.Vec.Properties using (map-cong; map-const)
open import Data.Vector.Bisemimodule R.semiring using (_∙_ ; ∙-cong)
open import Data.Vector.Core R.setoid using (Vector; Vectorₛ; module ≊; _≊_)
open import Data.Vector.Monoid R.+-monoid using () renaming (⟨ε⟩ to ⟨0⟩)
open import Data.Vector.Raw using (⟨⟩)
open import Data.Vector.Vec using (replicate-++)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; module ≡-Reasoning)

open R
open Vec
open ℕ.ℕ

private
  variable
    A B C D E F : ℕ

opaque
  unfolding _∙_
  ∙-comm : (V W : Vector A) → V ∙ W ≈ W ∙ V
  ∙-comm [] [] = refl
  ∙-comm (x ∷ V) (w ∷ W) = +-cong (*-comm x w) (∙-comm V W)

opaque
  unfolding _[_] [_]_ _ᵀ []ᵥ _∷ₕ_ _≋_ _∷ᵥ_
  [-]-ᵀ : (M : Matrix A B) (V : Vector A) →  M [ V ] ≊ [ V ] (M ᵀ)
  [-]-ᵀ [] V = ≊.sym (≊.reflexive ([-]-[]ᵥ V))
  [-]-ᵀ (M₀ ∷ M) V = begin
      M₀ ∙ V ∷ map (_∙ V) M         ≈⟨ ∙-comm M₀ V PW.∷ (PW.map⁺ (λ {x} ≊V → trans (∙-comm x V) (∙-cong ≊.refl ≊V)) ≋.refl) ⟩
      V ∙ M₀ ∷ map (V ∙_) M         ≡⟨⟩
      map (V ∙_) (M₀ ∷ᵥ M)          ≡⟨ ≡.cong (map (V ∙_) ∘ (M₀ ∷ᵥ_)) (M ᵀᵀ) ⟨
      map (V ∙_) (M₀ ∷ᵥ M ᵀ ᵀ)      ≡⟨ ≡.cong (map (V ∙_)) (∷ₕ-ᵀ M₀ (M ᵀ)) ⟨
      map (V ∙_) ((M₀ ∷ₕ (M ᵀ)) ᵀ)  ∎
    where
      open ≈-Reasoning (Vectorₛ _)

opaque
  unfolding []ᵥ mapRows _∷ₕ_ _∷ᵥ_ _ᵀ _≋_
  ·-ᵀ
      : {A B C : ℕ}
        (M : Matrix A B)
        (N : Matrix B C)
      → (N · M) ᵀ ≋ M ᵀ · N ᵀ
  ·-ᵀ {A} {B} {zero} M [] = begin
      []ᵥ                   ≡⟨ map-const (M ᵀ) ⟨⟩ ⟨
      map (λ _ → ⟨⟩) (M ᵀ)  ≡⟨ map-cong [-]-[]ᵥ (M ᵀ) ⟨
      map ([_] []ᵥ) (M ᵀ)   ∎
    where
      open ≈-Reasoning (Matrixₛ 0 A)
  ·-ᵀ {A} {B} {suc C} M (N₀ ∷ N) = begin
      map ([_] M) (N₀ ∷ N) ᵀ        ≡⟨ -[-]ᵀ (N₀ ∷ N) M ⟨
      map ((N₀ ∷ N) [_]) (M ᵀ)      ≈⟨ PW.map⁺ (λ {V} ≋V → ≊.trans ([-]-ᵀ (N₀ ∷ N) V) ([-]--cong {A = (N₀ ∷ᵥ N) ᵀ} ≋V ≋.refl)) ≋.refl ⟩
      map ([_] ((N₀ ∷ N) ᵀ)) (M ᵀ)  ≡⟨ map-cong (λ V → ≡.cong ([ V ]_) (∷ᵥ-ᵀ N₀ N)) (M ᵀ) ⟩
      map ([_] (N₀ ∷ₕ N ᵀ)) (M ᵀ)   ∎
    where
      open ≈-Reasoning (Matrixₛ (suc C) A)

opaque
  unfolding _≋_
  ᵀ-involutive : (M : Matrix A B) → (M ᵀ) ᵀ ≋ M
  ᵀ-involutive M = ≋.reflexive (M ᵀᵀ)

opaque
  unfolding Matrix _∥_ _ᵀ _≑_ _∷ₕ_
  ∥-ᵀ : (M : Matrix A C) (N : Matrix B C) → (M ∥ N) ᵀ ≡ M ᵀ ≑ N ᵀ
  ∥-ᵀ {A} {zero} {B} [] [] = ≡.sym (replicate-++ A B [])
  ∥-ᵀ (M₀ ∷ M) (N₀ ∷ N) = begin
      (M₀ ++ N₀) ∷ₕ ((M ∥ N) ᵀ) ≡⟨ ≡.cong ((M₀ ++ N₀) ∷ₕ_) (∥-ᵀ M N) ⟩
      (M₀ ++ N₀) ∷ₕ (M ᵀ ≑ N ᵀ) ≡⟨ ∷ₕ-≑ M₀ N₀ (M ᵀ) (N ᵀ) ⟩
      (M₀ ∷ₕ M ᵀ) ≑ (N₀ ∷ₕ N ᵀ) ∎
    where
      open ≡-Reasoning

≑-ᵀ : (M : Matrix A B) (N : Matrix A C) → (M ≑ N) ᵀ ≡ M ᵀ ∥ N ᵀ
≑-ᵀ M N = begin
    (M ≑ N) ᵀ           ≡⟨ ≡.cong₂ (λ h₁ h₂ → (h₁ ≑ h₂) ᵀ) (M ᵀᵀ) (N ᵀᵀ) ⟨
    (M ᵀ ᵀ ≑ N ᵀ ᵀ ) ᵀ  ≡⟨ ≡.cong (_ᵀ) (∥-ᵀ (M ᵀ) (N ᵀ)) ⟨
    (M ᵀ ∥ N ᵀ ) ᵀ ᵀ    ≡⟨ (M ᵀ ∥ N ᵀ ) ᵀᵀ ⟩
    M ᵀ ∥ N ᵀ           ∎
  where
    open ≡-Reasoning

inj₁ : (M : Matrix A C) (N : Matrix B C) → (M ∥ N) · (I ≑ 𝟎) ≋ M
inj₁ {A} {C} M N = begin
    (M ∥ N) · (I ≑ 𝟎)   ≈⟨ ∥-·-≑ M N I 𝟎 ⟩
    (M · I) [+] (N · 𝟎) ≈⟨ [+]-cong ·-Iʳ (·-𝟎ʳ N) ⟩
    M [+] 𝟎             ≈⟨ [+]-𝟎ʳ M ⟩
    M ∎
  where
    open ≈-Reasoning (Matrixₛ A C)

inj₂ : (M : Matrix A C) (N : Matrix B C) → (M ∥ N) · (𝟎 ≑ I) ≋ N
inj₂ {A} {C} {B} M N = begin
    (M ∥ N) · (𝟎 ≑ I)   ≈⟨ ∥-·-≑ M N 𝟎 I ⟩
    (M · 𝟎) [+] (N · I) ≈⟨ [+]-cong (·-𝟎ʳ M) ·-Iʳ ⟩
    𝟎 [+] N             ≈⟨ [+]-𝟎ˡ N ⟩
    N ∎
  where
    open ≈-Reasoning (Matrixₛ B C)

opaque

  unfolding Matrix _∷ᵥ_

  split-∥ : (A : ℕ) (M : Matrix (A ℕ.+ B) C) → Σ[ M₁ ∈ Matrix A C ] Σ[ M₂ ∈ Matrix B C ] M₁ ∥ M₂ ≡ M
  split-∥ zero M = []ᵥ , M , []ᵥ-∥ M
  split-∥ (suc A) M′
    rewrite ≡.sym (head-∷-tailₕ M′)
    using M₀ ← headₕ M′
    using M ← tailₕ M′
    with split-∥ A M
  ... | M₁ , M₂ , M₁∥M₂≡M = M₀ ∷ₕ M₁ , M₂ , (begin
      (M₀ ∷ₕ M₁) ∥ M₂ ≡⟨ ∷ₕ-∥ M₀ M₁ M₂ ⟨
      M₀ ∷ₕ M₁ ∥ M₂   ≡⟨ ≡.cong (M₀ ∷ₕ_) M₁∥M₂≡M ⟩
      M₀ ∷ₕ M ∎)
    where
      open ≡-Reasoning

  split-≑ : (B : ℕ) (M : Matrix A (B ℕ.+ C)) → Σ[ M₁ ∈ Matrix A B ] Σ[ M₂ ∈ Matrix A C ] M₁ ≑ M₂ ≡ M
  split-≑ zero M = []ₕ , M , []ₕ-≑ M
  split-≑ (suc B) (M₀ ∷ M) with split-≑ B M
  ... | M₁ , M₂ , M₁≑M₂≡M = M₀ ∷ᵥ M₁ , M₂ , (begin
      (M₀ ∷ᵥ M₁) ≑ M₂ ≡⟨ ∷ᵥ-≑ M₀ M₁ M₂ ⟨
      M₀ ∷ᵥ M₁ ≑ M₂   ≡⟨ ≡.cong (M₀ ∷ᵥ_) M₁≑M₂≡M ⟩
      M₀ ∷ᵥ M ∎)
    where
      open ≡-Reasoning

∥-uniq
    : (H : Matrix (A ℕ.+ B) C)
      (M : Matrix A C)
      (N : Matrix B C)
    → H · (I ≑ 𝟎) ≋ M
    → H · (𝟎 ≑ I) ≋ N
    → M ∥ N ≋ H
∥-uniq {A} {B} {C} H M N eq₁ eq₂
  with (H₁ , H₂ , H₁∥H₂≡H) ← split-∥ A H
  rewrite ≡.sym H₁∥H₂≡H = begin
    M ∥ N                                         ≈⟨ ∥-cong eq₁ eq₂ ⟨
    (H₁ ∥ H₂) · (I {A} ≑ 𝟎) ∥ (H₁ ∥ H₂) · (𝟎 ≑ I) ≈⟨ ∥-cong (inj₁ H₁ H₂) (inj₂ H₁ H₂) ⟩
    (H₁ ∥ H₂) ∎
  where
    open ≈-Reasoning (Matrixₛ (A ℕ.+ B) C)

proj₁ : (M : Matrix A B) (N : Matrix A C) → (I ∥ 𝟎) · (M ≑ N) ≋ M
proj₁ {A} {B} M N = begin
    (I ∥ 𝟎) · (M ≑ N)   ≈⟨ ∥-·-≑ I 𝟎 M N ⟩
    (I · M) [+] (𝟎 · N) ≈⟨ [+]-cong ·-Iˡ (·-𝟎ˡ N) ⟩
    M [+] 𝟎             ≈⟨ [+]-𝟎ʳ M ⟩
    M ∎
  where
    open ≈-Reasoning (Matrixₛ A B)

proj₂ : (M : Matrix A B) (N : Matrix A C) → (𝟎 ∥ I) · (M ≑ N) ≋ N
proj₂ {A} {_} {C} M N = begin
    (𝟎 ∥ I) · (M ≑ N)   ≈⟨ ∥-·-≑ 𝟎 I M N ⟩
    (𝟎 · M) [+] (I · N) ≈⟨ [+]-cong (·-𝟎ˡ M) ·-Iˡ ⟩
    𝟎 [+] N             ≈⟨ [+]-𝟎ˡ N ⟩
    N ∎
  where
    open ≈-Reasoning (Matrixₛ A C)

≑-uniq
    : (H : Matrix A (B ℕ.+ C))
      (M : Matrix A B)
      (N : Matrix A C)
    → (I ∥ 𝟎) · H ≋ M
    → (𝟎 ∥ I) · H ≋ N
    → M ≑ N ≋ H
≑-uniq {A} {B} {C} H M N eq₁ eq₂
  with (H₁ , H₂ , H₁≑H₂≡H) ← split-≑ B H
  rewrite ≡.sym H₁≑H₂≡H = begin
      M ≑ N                                         ≈⟨ ≑-cong eq₁ eq₂ ⟨
      (I {B} ∥ 𝟎) · (H₁ ≑ H₂) ≑ (𝟎 ∥ I) · (H₁ ≑ H₂) ≈⟨ ≑-cong (proj₁ H₁ H₂) (proj₂ H₁ H₂) ⟩
      H₁ ≑ H₂                                       ∎
  where
    open ≈-Reasoning (Matrixₛ A (B ℕ.+ C))


isCoproduct : IsCoproduct Mat (I {A} ≑ 𝟎) (𝟎 ≑ I {B})
isCoproduct {A} {B} = record
    { [_,_] = _∥_
    ; inject₁ = λ {a} {b} {c} → inj₁ b c
    ; inject₂ = λ {a} {b} {c} → inj₂ b c
    ; unique = λ eq₁ eq₂ → ∥-uniq _ _ _ eq₁ eq₂
    }

isProduct : IsProduct Mat (I {A} ∥ 𝟎) (𝟎 ∥ I {B})
isProduct {A} {B} = record
    { ⟨_,_⟩ = _≑_
    ; project₁ = λ {a} {b} {c} → proj₁ b c
    ; project₂ = λ {a} {b} {c} → proj₂ b c
    ; unique = λ eq₁ eq₂ → ≑-uniq _ _ _ eq₁ eq₂
    }

opaque

  unfolding Matrix

  π₁∘i₁ : (I {A} ∥ 𝟎 {B}) · (I ≑ 𝟎) ≋ I
  π₁∘i₁ {A} = begin
      (I ∥ 𝟎) · (I ≑ 𝟎)   ≈⟨ ∥-·-≑ I 𝟎 I 𝟎 ⟩
      (I · I) [+] (𝟎 · 𝟎) ≈⟨ [+]-cong ·-Iˡ (·-𝟎ˡ 𝟎) ⟩
      I [+] 𝟎             ≈⟨ [+]-𝟎ʳ I ⟩
      I                   ∎
    where
      open ≈-Reasoning (Matrixₛ A A)

  π₂∘i₂ : (𝟎 {A} {B} ∥ I) · (𝟎 ≑ I) ≋ I
  π₂∘i₂ {A} {B} = begin
      (𝟎 ∥ I) · (𝟎 ≑ I)   ≈⟨ ∥-·-≑ 𝟎 I 𝟎 I ⟩
      (𝟎 · 𝟎) [+] (I · I) ≈⟨ [+]-cong (·-𝟎ˡ 𝟎) ·-Iˡ  ⟩
      𝟎 [+] I             ≈⟨ [+]-𝟎ˡ I ⟩
      I                   ∎
    where
      open ≈-Reasoning (Matrixₛ B B)

  π₁∘i₂ : (I {A} ∥ 𝟎 {B}) · (𝟎 ≑ I) ≋ 𝟎 {B} {A}
  π₁∘i₂ {A} {B} = begin
      (I ∥ 𝟎) · (𝟎 ≑ I)   ≈⟨ ∥-·-≑ I 𝟎 𝟎 I ⟩
      (I · 𝟎) [+] (𝟎 · I) ≈⟨ [+]-cong (·-𝟎ʳ I) (·-𝟎ˡ I) ⟩
      𝟎 [+] 𝟎             ≈⟨ [+]-𝟎ʳ 𝟎 ⟩
      𝟎                   ∎
    where
      open ≈-Reasoning (Matrixₛ B A)

  π₂∘i₁ : (𝟎 {A} {B} ∥ I) · (I ≑ 𝟎) ≋ 𝟎 {A} {B}
  π₂∘i₁ {A} {B} = begin
      (𝟎 ∥ I) · (I ≑ 𝟎)   ≈⟨ ∥-·-≑ 𝟎 I I 𝟎 ⟩
      (𝟎 · I) [+] (I · 𝟎) ≈⟨ [+]-cong (·-𝟎ˡ I) (·-𝟎ʳ I) ⟩
      𝟎 [+] 𝟎             ≈⟨ [+]-𝟎ʳ 𝟎 ⟩
      𝟎                   ∎
    where
      open ≈-Reasoning (Matrixₛ A B)

  permute
      : (I ≑ 𝟎 {A} {B}) · (I ∥ 𝟎 {B} {A}) · (𝟎 {B} {A} ≑ I) · (𝟎 {A} {B} ∥ I)
      ≋ (𝟎 {B} {A} ≑ I) · (𝟎 {A} {B} ∥ I) · (I ≑ 𝟎 {A} {B}) · (I ∥ 𝟎 {B} {A})
  permute {A} {B} = begin
      (I ≑ 𝟎) · (I ∥ 𝟎 {B} {A}) · (𝟎 {B} {A} ≑ I) · (𝟎 {A} {B} ∥ I)   ≈⟨ ·-resp-≋ ≋.refl ·-assoc ⟨
      (I ≑ 𝟎) · ((I ∥ 𝟎 {B} {A}) · (𝟎 {B} {A} ≑ I)) · (𝟎 {A} {B} ∥ I) ≈⟨ ·-resp-≋ ≋.refl (·-resp-≋ π₁∘i₂ ≋.refl) ⟩
      (I ≑ 𝟎) · 𝟎 {B} {A} · (𝟎 {A} {B} ∥ I)                           ≈⟨ ·-resp-≋ ≋.refl (·-𝟎ˡ (𝟎 ∥ I)) ⟩
      (I ≑ 𝟎 {A} {B}) · 𝟎                                             ≈⟨ ·-𝟎ʳ (I ≑ 𝟎) ⟩
      𝟎                                                               ≈⟨ ·-𝟎ʳ (𝟎 ≑ I) ⟨
      (𝟎 {B} {A} ≑ I) · 𝟎                                             ≈⟨ ·-resp-≋ ≋.refl (·-𝟎ˡ (I ∥ 𝟎)) ⟨
      (𝟎 ≑ I) · 𝟎 {A} {B} · (I ∥ 𝟎 {B} {A})                           ≈⟨ ·-resp-≋ ≋.refl (·-resp-≋ π₂∘i₁ ≋.refl) ⟨
      (𝟎 {B} {A} ≑ I) · ((𝟎 ∥ I) · (I ≑ 𝟎 {A} {B})) · (I ∥ 𝟎 {B} {A}) ≈⟨ ·-resp-≋ ≋.refl ·-assoc ⟩
      (𝟎 {B} {A} ≑ I) · (𝟎 {A} {B} ∥ I) · (I ≑ 𝟎 {A} {B}) · (I ∥ 𝟎)   ∎
    where
      open ≈-Reasoning (Matrixₛ (A ℕ.+ B) (A ℕ.+ B))

biproduct : Biproduct Mat A B
biproduct {A} {B} = record
    { A⊕B = A ℕ.+ B
    ; π₁ = I ∥ 𝟎
    ; π₂ = 𝟎 ∥ I
    ; i₁ = I ≑ 𝟎
    ; i₂ = 𝟎 ≑ I
    ; isBiproduct = record
        { isCoproduct = isCoproduct
        ; isProduct = isProduct
        ; π₁∘i₁≈id = π₁∘i₁
        ; π₂∘i₂≈id = π₂∘i₂
        ; permute = permute
        }
    }

[I∥𝟎]ᵀ : (I ∥ 𝟎 {B} {A}) ᵀ ≋ I ≑ 𝟎
[I∥𝟎]ᵀ {B} {A} = begin
    (I ∥ 𝟎) ᵀ ≡⟨ ∥-ᵀ I 𝟎 ⟩
    I ᵀ ≑ 𝟎 ᵀ ≡⟨ ≡.cong₂ _≑_ Iᵀ 𝟎ᵀ ⟩
    I ≑ 𝟎     ∎
  where
    open ≈-Reasoning (Matrixₛ A (A ℕ.+ B))

[𝟎∥I]ᵀ : (𝟎 {A} {B} ∥ I) ᵀ ≋ 𝟎 ≑ I
[𝟎∥I]ᵀ {A} {B} = begin
    (𝟎 ∥ I) ᵀ ≡⟨ ∥-ᵀ 𝟎 I ⟩
    𝟎 ᵀ ≑ I ᵀ ≡⟨ ≡.cong₂ _≑_ 𝟎ᵀ Iᵀ ⟩
    𝟎 ≑ I     ∎
  where
    open ≈-Reasoning (Matrixₛ B (A ℕ.+ B))

opaque

  unfolding _≋_

  ¡-unique : (E : Matrix 0 B) → []ᵥ ≋ E
  ¡-unique E = ≋.reflexive (≡.sym ([]ᵥ-! E))

  !-unique : (E : Matrix A 0) → []ₕ ≋ E
  !-unique E = ≋.reflexive (≡.sym ([]ₕ-! E))

isInitial : IsInitial Mat 0
isInitial = record
    { ¡ = []ᵥ
    ; ¡-unique = ¡-unique
    }

isTerminal : IsTerminal Mat 0
isTerminal = record
    { ! = []ₕ
    ; !-unique = !-unique
    }

zeroObj : Zero Mat
zeroObj = record
    { 𝟘 = 0
    ; isZero = record
        { isInitial = isInitial
        ; isTerminal = isTerminal
        }
    }

Mat-Semiadditive : Semiadditive Mat
Mat-Semiadditive = record
    { zero = zeroObj
    ; biproducts = record
        { biproduct = biproduct
        }
    }

Mat-HasDagger : HasDagger Mat
Mat-HasDagger = record
    { _† = λ M → M ᵀ
    ; †-identity = ≋.reflexive Iᵀ
    ; †-homomorphism = λ {f = f} {g} → ·-ᵀ f g
    ; †-resp-≈ = ᵀ-cong
    ; †-involutive = ᵀ-involutive
    }

Mat-SemiadditiveDagger : SemiadditiveDagger Mat
Mat-SemiadditiveDagger = record
    { semiadditive = Mat-Semiadditive
    ; dagger = Mat-HasDagger
    ; π₁† = [I∥𝟎]ᵀ
    ; π₂† = [𝟎∥I]ᵀ
    ; ⟨⟩-† = λ {f = M} {N} → ≋.reflexive (≑-ᵀ M N)
    }
