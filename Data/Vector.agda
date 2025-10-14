{-# OPTIONS --without-K --safe #-}

module Data.Vector where

open import Data.Nat.Base using (ℕ)
open import Data.Vec.Functional using (Vector; head; tail; []; removeAt; map) public
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_)
open import Function.Base using (∣_⟩-_; _∘_)
open import Data.Fin.Base using (Fin; toℕ)
open ℕ
open Fin

foldl
    : ∀ {n : ℕ} {A : Set} (B : ℕ → Set)
    → (∀ {k : Fin n} → B (toℕ k) → A → B (suc (toℕ k)))
    → B zero
    → Vector A n
    → B n
foldl {zero} B ⊕ e v = e
foldl {suc n} B ⊕ e v = foldl (B ∘ suc) ⊕ (⊕ e (head v)) (tail v)

foldl-cong
    : {n : ℕ} {A : Set}
      (B : ℕ → Set)
      {f g : ∀ {k : Fin n} → B (toℕ k) → A → B (suc (toℕ k))}
    → (∀ {k} → ∀ x y → f {k} x y ≡ g {k} x y)
    → (e : B zero)
    → (v : Vector A n)
    → foldl B f e v ≡ foldl B g e v
foldl-cong {zero} B f≗g e v = ≡.refl
foldl-cong {suc n} B {g = g} f≗g e v rewrite (f≗g e (head v)) = foldl-cong (B ∘ suc) f≗g (g e (head v)) (tail v)

foldl-cong-arg
    : {n : ℕ} {A : Set}
      (B : ℕ → Set)
      (f : ∀ {k : Fin n} → B (toℕ k) → A → B (suc (toℕ k)))
    → (e : B zero)
    → {v w : Vector A n}
    → v ≗ w
    → foldl B f e v ≡ foldl B f e w
foldl-cong-arg {zero} B f e v≗w = ≡.refl
foldl-cong-arg {suc n} B f e {w = w} v≗w rewrite v≗w zero = foldl-cong-arg (B ∘ suc) f (f e (head w)) (v≗w ∘ suc)

foldl-map
    : {n : ℕ} {A : ℕ → Set} {B C : Set}
      (f : ∀ {k : Fin n} → A (toℕ k) → B → A (suc (toℕ k)))
      (g : C → B)
      (x : A zero)
      (xs : Vector C n)
    → foldl A f x (map g xs)
    ≡ foldl A (∣ f ⟩- g) x xs
foldl-map {zero} f g e xs = ≡.refl
foldl-map {suc n} f g e xs = foldl-map f g (f e (g (head xs))) (tail xs)

foldl-fusion
    : {n : ℕ}
      {A : Set} {B C : ℕ → Set}
      (h : {k : ℕ} → B k → C k)
    → {f : {k : Fin n} → B (toℕ k) → A → B (suc (toℕ k))} {d : B zero}
    → {g : {k : Fin n} → C (toℕ k) → A → C (suc (toℕ k))} {e : C zero}
    → (h d ≡ e)
    → ({k : Fin n} (b : B (toℕ k)) (x : A) → h (f {k} b x) ≡ g (h b) x)
    → h ∘ foldl B f d ≗ foldl C g e
foldl-fusion {zero} _ base _ _ = base
foldl-fusion {suc n} {A} h {f} {d} {g} {e} base fuse xs = foldl-fusion h eq fuse (tail xs)
  where
    x₀ : A
    x₀ = head xs
    open ≡.≡-Reasoning
    eq : h (f d x₀) ≡ g e x₀
    eq = begin
        h (f d x₀)  ≡⟨ fuse d x₀ ⟩
        g (h d) x₀  ≡⟨ ≡.cong-app (≡.cong g base) x₀ ⟩
        g e x₀      ∎

foldl-[]
    : {A : Set}
      (B : ℕ → Set)
      (f : {k : Fin 0} → B (toℕ k) → A → B (suc (toℕ k)))
      {e : B 0}
    → foldl B f e [] ≡ e
foldl-[] _ _ = ≡.refl
