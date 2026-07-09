{-# OPTIONS --without-K --safe #-}

open import Level using (Level; suc; _⊔_)

module Category.Equivalence.Instance.Nat (c ℓ : Level) where

import Data.Matrix.Dagger-2-Poset as Mat-D2P
import Data.Matrix.Monoid as MM
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Algebra using (Semiring)
open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.Category.Instance.Nat using (Nat)
open import Categories.Functor using (Functor; _∘F_) renaming (id to Id)
open import Category.Dagger.2-Poset using (Dagger-2-Poset; IsMap; Map; Maps)
open import Category.Dagger.Semiadditive using (IdempotentSemiadditiveDagger)
open import Data.Bool using (Bool; _∧_; _∨_)
open import Data.Bool.Properties using (∨-idem; ∧-comm)
open import Data.Boolean.BoundedDistributiveLattice using (𝔹)
open import Data.Fin using (Fin; _≟_)
open import Data.Matrix.Category 𝔹.semiring using (_·_)
open import Data.Matrix.Convert 𝔹.semiring
  using (tabulate; tabulate-cong; tabulate-I; tabulate-flip; tabulate-·; tabulate-[+]; lookup)
open import Data.Matrix.Core 𝔹.setoid using (Matrix; _≋_; Matrixₛ; module ≋)
open import Data.Matrix.Functional 𝔹.semiring as Func using (sum; sum-cong; identity)
open import Data.Matrix.Raw using (_ᵀ)
open import Data.Matrix.Transform 𝔹.semiring using (I; [_]_)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Product.Properties using (≡-dec)
open import Data.Vec using (Vec)
open import Data.Vec.Functional using (tail)
open import Function using (Func; _⟨$⟩_; flip; _∘_; _⇔_; mk⇔) renaming (id to idf)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_; module ≡-Reasoning)
open import Relation.Nullary.Decidable using (⌊_⌋; Dec; yes; no; _×-dec_; isYes≗does; dec-true; dec-false; does-⇔)
open import Relation.Unary using (Pred; Decidable)

module 𝔹-rig = Semiring 𝔹.semiring

open Mat-D2P 𝔹.commutativeSemiring ∨-idem
  using (Mat-IdempotentSemiadditiveDagger; +-[+])
  renaming (Mat-Dagger-2-Poset to Mat𝔹)

open Bool
open Dagger-2-Poset Mat𝔹 hiding (_∘_)
open Fin
open IdempotentSemiadditiveDagger Mat-IdempotentSemiadditiveDagger using (_+_)
open MM 𝔹-rig.+-monoid using (_[+]_)
open ℕ

A→B⇒A∨B≡B : {A B : Set} {p : Dec A} {q : Dec B} → (A → B) → ⌊ p ⌋ ∨ ⌊ q ⌋ ≡ ⌊ q ⌋
A→B⇒A∨B≡B {p = yes p} {yes q} f = ≡.refl
A→B⇒A∨B≡B {p = yes p} {no ¬q} f with () ← ¬q (f p)
A→B⇒A∨B≡B {p = no ¬p} {q} f = ≡.refl

Σ? : {ℓ : Level} {n : ℕ} {P : Pred (Fin n) ℓ} → Decidable P → Dec (Σ (Fin n) P)
Σ? {ℓ} {zero} _ = no λ ()
Σ? {ℓ} {suc n} {P} P? with (P? zero)
... | yes P0 = yes (zero , P0)
... | no ¬P0 with Σ? {ℓ} {n} {tail P} (λ i → P? (Fin.suc i))
...   | yes (i , Pi) = yes (Fin.suc i , Pi)
...   | no ¬ΣP = no λ { (zero , P0) → ¬P0 P0 ; (suc i , Pi) → ¬ΣP (i , Pi) }

open Dec

⌊Σ?⌋ : {ℓ : Level} {n : ℕ} {P : Pred (Fin n) ℓ} (P? : Decidable P) → ⌊ Σ? P? ⌋ ≡ sum (λ i → ⌊ P? i ⌋)
⌊Σ?⌋ {_} {zero} {P} _ = ≡.refl
⌊Σ?⌋ {_} {suc n} {P} P? with P? zero
... | yes _ = ≡.refl
... | no ¬P0 with Σ? (λ i → P? (Fin.suc i))
...   | yes ΣP = begin
          true                              ≡⟨ dec-true (Σ? (λ i → P? (Fin.suc i))) ΣP ⟨
          does (Σ? (λ i → P? (Fin.suc i)))  ≡⟨ isYes≗does (Σ? (λ i → P? (Fin.suc i))) ⟨
          ⌊ Σ? (λ i → P? (Fin.suc i)) ⌋     ≡⟨ ⌊Σ?⌋ (λ i → P? (Fin.suc i)) ⟩
          sum (λ i → ⌊ (P? (Fin.suc i)) ⌋)  ∎
        where
          open ≡-Reasoning
...   | no ¬ΣP = begin
          false                             ≡⟨ dec-false (Σ? (λ i → P? (Fin.suc i))) ¬ΣP ⟨
          does (Σ? (λ i → P? (Fin.suc i)))  ≡⟨ isYes≗does (Σ? (λ i → P? (Fin.suc i))) ⟨
          ⌊ Σ? (λ i → P? (Fin.suc i)) ⌋     ≡⟨ ⌊Σ?⌋ (λ i → P? (Fin.suc i)) ⟩
          sum (λ x → ⌊ (P? (Fin.suc x)) ⌋)  ∎
        where
          open ≡-Reasoning

⌊A×B⌋ : {A B : Set} (A? : Dec A) (B? : Dec B) → ⌊ A? ⌋ ∧ ⌊ B? ⌋ ≡ ⌊ A? ×-dec B? ⌋
⌊A×B⌋ (yes a) (yes b) = ≡.refl
⌊A×B⌋ (yes a) (no ¬b) = ≡.refl
⌊A×B⌋ (no ¬a) B? = ≡.refl

graph : {n m : ℕ} (f : Fin n → Fin m) → Func.Matrix n m
graph f i j = ⌊ f i ≟ j ⌋

graph-id : {n : ℕ} (i j : Fin n) → ⌊ i ≟ j ⌋ ≡ identity i j
graph-id i j with ⌊ i ≟ j ⌋
... | true = ≡.refl
... | false = ≡.refl

func
    : {n m : ℕ}
      (f : Fin n → Fin m)
      {i₁ i₂ : Fin m}
    → Σ (Fin n) (λ k → f k ≡ i₁ × f k ≡ i₂) → i₁ ≡ i₂
func f (k , fk≡i₁ , fk≡i₂) = ≡.trans (≡.sym fk≡i₁) fk≡i₂

enti
    : {n m : ℕ}
      (f : Fin n → Fin m)
      {i₁ i₂ : Fin n}
    → i₁ ≡ i₂
    → Σ (Fin m) (λ k → f i₁ ≡ k × f i₂ ≡ k)
enti f {i₁} i₁≡i₂ = f i₁ , ≡.refl , ≡.cong f (≡.sym i₁≡i₂)

functional-index
    : {n m : ℕ}
      (f : Fin n → Fin m)
      (i j : Fin m)
    → sum (λ k → graph f k j ∧ graph f k i) ∨ identity i j ≡ identity i j
functional-index f i j = begin
    sum (λ k → ⌊ f k ≟ j ⌋ ∧ ⌊ f k ≟ i ⌋) ∨ identity i j  ≡⟨ ≡.cong (_∨ identity i j) (sum-cong (λ k → ∧-comm (⌊ f k ≟ j ⌋) (⌊ f k ≟ i ⌋))) ⟩
    sum (λ k → ⌊ f k ≟ i ⌋ ∧ ⌊ f k ≟ j ⌋) ∨ identity i j  ≡⟨ ≡.cong₂ _∨_ (sum-cong (λ k → ⌊A×B⌋ (f k ≟ i) (f k ≟ j))) (≡.sym (graph-id i j)) ⟩
    sum (λ k → ⌊ f k ≟ i ×-dec f k ≟ j ⌋) ∨ ⌊ i ≟ j ⌋     ≡⟨ ≡.cong (_∨ ⌊ i ≟ j ⌋) (⌊Σ?⌋ (λ k → f k ≟ i ×-dec f k ≟ j)) ⟨
    ⌊ Σ? (λ k → f k ≟ i ×-dec f k ≟ j) ⌋ ∨ ⌊ i ≟ j ⌋      ≡⟨ A→B⇒A∨B≡B (func f) ⟩
    ⌊ i ≟ j ⌋                                             ≡⟨ graph-id i j ⟩
    identity i j                                          ∎
  where
    open ≡-Reasoning

entire-index
    : {n m : ℕ}
      (f : Fin n → Fin m)
      (i j : Fin n)
    → identity i j ∨ sum (λ k → graph f j k ∧ graph f i k) ≡ sum (λ k → graph f j k ∧ graph f i k)
entire-index {n} {m} f i j = begin
    identity i j ∨ sum (λ k → ⌊ f j ≟ k ⌋ ∧ ⌊ f i ≟ k ⌋)  ≡⟨ ≡.cong (identity i j ∨_) (sum-cong (λ k → ∧-comm (⌊ f j ≟ k ⌋) (⌊ f i ≟ k ⌋))) ⟩
    identity i j ∨ sum (λ k → ⌊ f i ≟ k ⌋ ∧ ⌊ f j ≟ k ⌋)  ≡⟨ ≡.cong (_∨ sum (λ k → ⌊ f i ≟ k ⌋ ∧ ⌊ f j ≟ k ⌋)) (graph-id i j) ⟨
    ⌊ i ≟ j ⌋ ∨ sum (λ k → ⌊ f i ≟ k ⌋ ∧ ⌊ f j ≟ k ⌋)     ≡⟨ ≡.cong (⌊ i ≟ j ⌋ ∨_) (sum-cong (λ k → ⌊A×B⌋ (f i ≟ k) (f j ≟ k))) ⟩
    ⌊ i ≟ j ⌋ ∨ sum (λ k → ⌊ f i ≟ k ×-dec f j ≟ k ⌋)     ≡⟨ ≡.cong (⌊ i ≟ j ⌋ ∨_) (⌊Σ?⌋ (λ k → f i ≟ k ×-dec f j ≟ k)) ⟨
    ⌊ i ≟ j ⌋ ∨ ⌊ Σ? (λ k → f i ≟ k ×-dec f j ≟ k) ⌋      ≡⟨ A→B⇒A∨B≡B (enti f) ⟩
    ⌊ Σ? (λ k → f i ≟ k ×-dec f j ≟ k) ⌋                  ≡⟨ ⌊Σ?⌋ (λ k → f i ≟ k ×-dec f j ≟ k) ⟩
    sum (λ k → ⌊ f i ≟ k ×-dec f j ≟ k ⌋)                 ≡⟨ sum-cong (λ k → ⌊A×B⌋ (f i ≟ k) (f j ≟ k)) ⟨
    sum (λ k → ⌊ f i ≟ k ⌋ ∧ ⌊ f j ≟ k ⌋)                 ≡⟨ sum-cong (λ k → ∧-comm (⌊ f i ≟ k ⌋) (⌊ f j ≟ k ⌋)) ⟩
    sum (λ k → ⌊ f j ≟ k ⌋ ∧ ⌊ f i ≟ k ⌋)                 ∎
  where
    open ≡-Reasoning

functional : {n m : ℕ} (f : Fin n → Fin m) → tabulate (graph f) · tabulate (graph f) ᵀ ≤ I {m}
functional {n} {m} f = begin
    (tabulate (graph f) · tabulate (graph f) ᵀ) + I                 ≈⟨ +-[+] (tabulate (graph f) · tabulate (graph f) ᵀ) I ⟩
    (tabulate (graph f) · tabulate (graph f) ᵀ) [+] I               ≡⟨ ≡.cong (λ h → (tabulate (graph f) · h) [+] I) (tabulate-flip (graph f)) ⟨
    (tabulate (graph f) · tabulate (flip (graph f))) [+] I          ≡⟨ ≡.cong₂ _[+]_ (tabulate-· (graph f) (flip (graph f))) (≡.sym tabulate-I) ⟩
    tabulate (graph f Func.· flip (graph f)) [+] tabulate identity  ≡⟨ tabulate-[+] (graph f Func.· flip (graph f)) identity ⟩
    tabulate ((graph f Func.· flip (graph f)) Func.[+] identity)    ≡⟨ tabulate-cong (functional-index f) ⟩
    tabulate identity                                               ≡⟨ tabulate-I ⟩
    I                                                               ∎
  where
    open ≈-Reasoning (Matrixₛ m m)

entire : {n m : ℕ} (f : Fin n → Fin m) → I {n} ≤ tabulate (graph f) ᵀ · tabulate (graph f)
entire {n} {m} f = begin
    I + (tabulate (graph f) ᵀ · tabulate (graph f))                 ≈⟨ +-[+] I (tabulate (graph f) ᵀ · tabulate (graph f)) ⟩
    I [+] (tabulate (graph f) ᵀ · tabulate (graph f))               ≡⟨ ≡.cong (λ h → I [+] (h · tabulate (graph f))) (tabulate-flip (graph f)) ⟨
    I [+] (tabulate (flip (graph f)) · tabulate (graph f))          ≡⟨ ≡.cong (I [+]_) (tabulate-· (flip (graph f)) (graph f)) ⟩
    I [+] tabulate (flip (graph f) Func.· graph f)                  ≡⟨ ≡.cong (_[+] (tabulate (flip (graph f) Func.· graph f))) tabulate-I ⟨
    tabulate identity [+] tabulate (flip (graph f) Func.· graph f)  ≡⟨ tabulate-[+] identity (flip (graph f) Func.· graph f) ⟩
    tabulate (identity Func.[+] (flip (graph f) Func.· graph f))    ≡⟨ tabulate-cong (entire-index f) ⟩
    tabulate (flip (graph f) Func.· graph f)                        ≡⟨ tabulate-· (flip (graph f)) (graph f) ⟨
    tabulate (flip (graph f)) · tabulate (graph f)                  ≡⟨ ≡.cong (_· tabulate (graph f)) (tabulate-flip (graph f)) ⟩
    tabulate (graph f) ᵀ · tabulate (graph f)                       ∎
  where
    open ≈-Reasoning (Matrixₛ n n)

toMap
    : {n m : ℕ}
    → (Fin n → Fin m)
    → Map Mat𝔹 n m
toMap {n} {m} f = record
    { map = tabulate (graph f)
    ; isMap = record
        { functional = functional f
        ; entire = entire f
        }
    }

open Map

tabulate-id : {n : ℕ} → tabulate (graph idf) ≋ I {n}
tabulate-id {n} = begin
    tabulate (λ i j → ⌊ i ≟ j ⌋)  ≡⟨ tabulate-cong graph-id ⟩
    tabulate identity             ≡⟨ tabulate-I ⟩
    I                             ∎
  where
    open ≈-Reasoning (Matrixₛ n n)

homo
    : {X Y Z : ℕ}
      (f : Fin X → Fin Y)
      (g : Fin Y → Fin Z)
      (i : Fin X)
      (j : Fin Z)
    → g (f i) ≡ j ⇔ Σ (Fin Y) (λ k → g k ≡ j × f i ≡ k)
homo f g i j = mk⇔ (λ gfi≡j → f i , gfi≡j , ≡.refl) (λ (k , gk≡j , fi≡k) → ≡.trans (≡.cong g fi≡k) gk≡j )

homomorphism-index
    : {X Y Z : ℕ}
      (f : Fin X → Fin Y)
      (g : Fin Y → Fin Z)
      (i : Fin X)
      (j : Fin Z)
    → ⌊ (g (f i) ≟ j) ⌋ ≡ sum (λ k → ⌊ g k ≟ j ⌋ ∧ ⌊ f i ≟ k ⌋)
homomorphism-index f g i j = begin
    ⌊ g (f i) ≟ j ⌋                         ≡⟨ isYes≗does (g (f i) ≟ j) ⟩
    does (g (f i) ≟ j)                      ≡⟨ does-⇔ (homo f g i j) (g (f i) ≟ j) (Σ? (λ k → g k ≟ j ×-dec f i ≟ k)) ⟩
    does (Σ? (λ k → g k ≟ j ×-dec f i ≟ k)) ≡⟨ isYes≗does (Σ? (λ k → g k ≟ j ×-dec f i ≟ k)) ⟨
    ⌊ Σ? (λ k → g k ≟ j ×-dec f i ≟ k) ⌋    ≡⟨ ⌊Σ?⌋ (λ k → g k ≟ j ×-dec f i ≟ k) ⟩
    sum (λ k → ⌊ g k ≟ j ×-dec f i ≟ k ⌋)   ≡⟨ sum-cong (λ k → ⌊A×B⌋ (g k ≟ j) (f i ≟ k)) ⟨
    sum (λ k → ⌊ g k ≟ j ⌋ ∧ ⌊ f i ≟ k ⌋)   ∎
  where
    open ≡-Reasoning

homomorphism
    : {X Y Z : ℕ}
    → {f : Fin X → Fin Y}
    → {g : Fin Y → Fin Z}
    → tabulate (graph (g ∘ f)) ≋ tabulate (graph g) · tabulate (graph f)
homomorphism {X} {Y} {Z} {f} {g} = begin
    tabulate (graph (g ∘ f))                ≡⟨ tabulate-cong (homomorphism-index f g) ⟩
    tabulate (graph g Func.· graph f)       ≡⟨ tabulate-· (graph g) (graph f) ⟨
    tabulate (graph g) · tabulate (graph f) ∎
  where
    open ≈-Reasoning (Matrixₛ X Z)

From-resp-≈
    : {A B : ℕ}
      {f g : Fin A → Fin B}
    → f ≗ g
    → tabulate (graph f) ≋ tabulate (graph g)
From-resp-≈ {A} {B} {f} {g} f≗g = ≋.reflexive (tabulate-cong (λ i j → ≡.cong (λ h → ⌊ h ≟ j ⌋) (f≗g i)))

From : Functor Nat (Maps Mat𝔹)
From = record
    { F₀ = idf
    ; F₁ = toMap
    ; identity = tabulate-id
    ; homomorphism = homomorphism
    ; F-resp-≈ = From-resp-≈
    }
