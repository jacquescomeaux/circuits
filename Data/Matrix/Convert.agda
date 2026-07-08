{-# OPTIONS --without-K --safe #-}

open import Level using (Level)
open import Algebra using (Semiring)

module Data.Matrix.Convert {c ℓ : Level} (R : Semiring c ℓ) where

open Semiring R

import Data.Vec as Vec
import Data.Vec.Properties as VecProp

open import Data.Bool using (if_then_else_)
open import Data.Fin using (Fin; _≟_)
open import Data.Matrix.Category R using (_·_)
open import Data.Matrix.Core setoid using (_≋_) renaming (Matrix to Mat)
open import Data.Matrix.Functional R as Functional using (Matrix; identity)
open import Data.Matrix.Monoid +-monoid using (_[+]_)
open import Data.Matrix.Raw using (_∷ₕ_; _∷ᵥ_; _ᵀ)
open import Data.Matrix.Transform R using (I; [_]_)
open import Data.Nat using (ℕ)
open import Data.Vec.Functional using (Vector; head; tail)
open import Data.Vector.Bisemimodule R using (_∙_)
open import Data.Vector.Monoid +-monoid using (⟨ε⟩; _⊕_)
open import Data.Vector.Vec using (zipWith-tabulate; replicate-tabulate)
open import Function using (flip)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; module ≡-Reasoning)
open import Relation.Nullary.Decidable using (⌊⌋-map′)

open Vec.Vec
open ℕ
open ≡-Reasoning

opaque

  unfolding Mat

  tabulate : {n m : ℕ} → Matrix n m → Mat n m
  tabulate M = Vec.tabulate (λ j → Vec.tabulate (λ i → M i j))

  lookup : {n m : ℕ} → Mat n m → Matrix n m
  lookup M i j = Vec.lookup (Vec.lookup M j) i

opaque

  unfolding tabulate

  tabulate-cong : {n m : ℕ} {M N : Matrix n m} → (∀ i j → M i j ≡ N i j) → tabulate M ≡ tabulate N
  tabulate-cong {n} {m} {M} {N} M≗N = VecProp.tabulate-cong (λ j → VecProp.tabulate-cong (λ i → M≗N i j))

  opaque
    unfolding I ⟨ε⟩
    tabulate-I : {n : ℕ} → tabulate identity ≡ I {n}
    tabulate-I {zero} = ≡.refl
    tabulate-I {suc n} = begin
        (1# ∷ Vec.tabulate (λ _ → 0#)) ∷ᵥ tabulate (λ i → tail (identity i))  ≡⟨ ≡.cong₂ _∷ᵥ_ (≡.cong (1# ∷_) (≡.sym (replicate-tabulate 0#))) rest ⟩
        (1# ∷ ⟨ε⟩) ∷ᵥ ⟨ε⟩ ∷ₕ I                                                ∎
      where
        rest : Vec.tabulate (λ j → 0# ∷ Vec.tabulate (λ i → identity (Fin.suc i) (Fin.suc j))) ≡ Vec.zipWith _∷_ ⟨ε⟩ (I {n})
        rest = begin
            Vec.tabulate (λ j → 0# ∷ Vec.tabulate (λ i → identity (Fin.suc i) (Fin.suc j)))   ≡⟨ zipWith-tabulate _∷_ (λ _ → 0#) (λ j → _) ⟨
            Vec.tabulate (λ _ → 0#) ∷ₕ (tabulate (λ i j → identity (Fin.suc i) (Fin.suc j)))  ≡⟨ ≡.cong₂ _∷ₕ_ (replicate-tabulate 0#) ≡.refl ⟨
            Vec.replicate n 0# ∷ₕ (tabulate (λ i j → identity (Fin.suc i) (Fin.suc j)))
              ≡⟨ ≡.cong₂ _∷ₕ_ ≡.refl (tabulate-cong (λ i j → ≡.cong (if_then 1# else 0#) (⌊⌋-map′ _ _ (i ≟ j)))) ⟩
            Vec.replicate n 0# ∷ₕ (tabulate (λ i j → identity i j))                           ≡⟨ ≡.cong₂ _∷ₕ_ ≡.refl tabulate-I ⟩
            ⟨ε⟩ ∷ₕ I ∎

  opaque
    unfolding _ᵀ
    tabulate-flip : {n m : ℕ} (M : Matrix n m) → tabulate (flip M) ≡ tabulate M ᵀ
    tabulate-flip {n} {zero} M = ≡.sym (replicate-tabulate [])
    tabulate-flip {n} {suc m} M = begin
        Vec.tabulate (λ j → head (M j) ∷ Vec.tabulate (λ x → M j (Fin.suc x)))    ≡⟨ zipWith-tabulate _∷_ (λ j → M j Fin.zero) _ ⟨
        Vec.tabulate (λ i → head (M i)) ∷ₕ (tabulate (λ j i → M i (Fin.suc j)))   ≡⟨ ≡.cong (Vec.tabulate (λ i → head (M i)) ∷ₕ_) (tabulate-flip (λ i → tail (M i))) ⟩
        Vec.tabulate (λ i → head (M i)) ∷ₕ (tabulate (λ i j → M i (Fin.suc j))) ᵀ ∎

  opaque
    unfolding _∙_
    tabulate-∙ : {n : ℕ} (V W : Vector Carrier n) → Vec.tabulate V ∙ Vec.tabulate W ≡ Functional.sum (λ k → V k * W k)
    tabulate-∙ {zero} _ _ = ≡.refl
    tabulate-∙ {suc n} V W = ≡.cong (head V * head W +_) (tabulate-∙ (tail V) (tail W))

  opaque
    unfolding [_]_
    tabulate-· : {A B C : ℕ} (M : Matrix B C) (N : Matrix A B) → tabulate M · tabulate N ≡ tabulate (M Functional.· N)
    tabulate-· M N = begin
        Vec.map ([_] Vec.tabulate (λ j → Vec.tabulate (λ i → N i j))) (Vec.tabulate (λ j → Vec.tabulate (λ i → M i j)))
            ≡⟨ VecProp.tabulate-∘ ([_] Vec.tabulate (λ j → Vec.tabulate (λ i → N i j))) (λ j → Vec.tabulate (λ i → M i j)) ⟨
        Vec.tabulate (λ j → Vec.map (Vec.tabulate (flip M j) ∙_) (Vec.tabulate (λ j₁ → Vec.tabulate (flip N j₁)) ᵀ))
            ≡⟨ VecProp.tabulate-cong (λ j → ≡.cong (Vec.map (Vec.tabulate (flip M j) ∙_)) (tabulate-flip N)) ⟨
        Vec.tabulate (λ j → Vec.map (Vec.tabulate (λ i → M i j) ∙_) (Vec.tabulate (λ j₁ → Vec.tabulate (λ i → N j₁ i))))
            ≡⟨ VecProp.tabulate-cong (λ j → VecProp.tabulate-∘ ((Vec.tabulate (λ i → M i j)) ∙_) (λ j₁ → Vec.tabulate (λ i → N j₁ i))) ⟨
        Vec.tabulate (λ j → Vec.tabulate (λ i → Vec.tabulate (flip M j) ∙ Vec.tabulate (N i)))
            ≡⟨ tabulate-cong (λ i j → tabulate-∙ (flip M j) (N i)) ⟩
        Vec.tabulate (λ j → Vec.tabulate (λ i → Functional.sum (λ k → M k j * N i k))) ∎

  opaque
    unfolding _[+]_ _⊕_
    tabulate-[+] : {n m : ℕ} (M N : Matrix n m) → tabulate M [+] tabulate N ≡ tabulate (M Functional.[+] N)
    tabulate-[+] M N = begin
        Vec.zipWith _⊕_ (tabulate M) (tabulate N)
            ≡⟨ zipWith-tabulate _⊕_ _ _ ⟩
        Vec.tabulate (λ j → Vec.tabulate (λ i → M i j) ⊕ Vec.tabulate (λ i → N i j))
            ≡⟨ VecProp.tabulate-cong (λ j → zipWith-tabulate _+_ _ _) ⟩
        Vec.tabulate (λ j → Vec.tabulate (λ i → M i j + N i j)) ∎
