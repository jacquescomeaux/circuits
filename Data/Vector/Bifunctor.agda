{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module Data.Vector.Bifunctor {c : Level} where

open import Categories.Category.Instance.Nat using (Natop)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Function using (_∘_)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (_,_)
open import Data.Vec using (Vec; map; tabulate; lookup)
open import Data.Vec.Properties using (map-id; map-∘; map-cong; tabulate∘lookup; lookup∘tabulate; tabulate-cong; lookup-map; tabulate-∘)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; module ≡-Reasoning)

naturality
    : {A B : Set c} {f : A → B} {n m : ℕ} {g : Fin m → Fin n} (v : Vec A n)
    → map f (tabulate (λ i → lookup v (g i))) ≡ tabulate (λ i → lookup (map f v) (g i))
naturality {A} {B} {f} {n} {m} {g} v = begin
    map f (tabulate (λ i → lookup v (g i))) ≡⟨ tabulate-∘ f (λ i → lookup v (g i)) ⟨
    tabulate (λ i → f (lookup v (g i)))     ≡⟨ tabulate-cong (λ i → (lookup-map (g i) f v)) ⟨
    tabulate (λ i → lookup (map f v) (g i)) ∎
  where
    open ≡-Reasoning

bimap : {A B : Set c} {n m : ℕ} (f : A → B) (g : Fin m → Fin n) → Vec A n → Vec B m
bimap f g v = map f (tabulate (λ i → lookup v (g i)))

Vec₂ : Bifunctor (Sets c) Natop (Sets c)
Vec₂ = record
    { F₀ = λ (A , n) → Vec A n
    ; F₁ = λ (f , g) v → bimap f g v
    ; identity = λ v → ≡.trans (map-id (tabulate (λ i → lookup v i))) (tabulate∘lookup v)
    ; homomorphism = λ {_ _ _} {(f , f′)} {(g , g′)} → homomorphism f g f′ g′
    ; F-resp-≈ = λ (f≗g , f′≗g′) v → ≡.trans (map-cong f≗g (tabulate (λ i → lookup v _))) (≡.cong (map _) (tabulate-cong (λ i → (≡.cong (lookup v) (f′≗g′ i)))))
    }
  where
    homomorphism
        : {X Y Z : Set c}
          (f : X → Y)
          (g : Y → Z)
          {x y z : ℕ}
          (f′ : Fin y → Fin x)
          (g′ : Fin z → Fin y)
          (v : Vec X x)
        → bimap (g ∘ f) (f′ ∘ g′) v ≡ bimap g g′ (bimap f f′ v)
    homomorphism f g f′ g′ v = begin
        map (g ∘ f) (tabulate (λ i → lookup v (f′ (g′ i))))   ≡⟨ map-∘ g f (tabulate (λ i → lookup v (f′ (g′ i)))) ⟩
        map g (map f (tabulate (λ i → lookup v (f′ (g′ i))))) ≡⟨ ≡.cong (map g) (naturality v) ⟩
        map g (tabulate (λ i → lookup (map f v) (f′ (g′ i)))) ≡⟨ ≡.cong (map g) (tabulate-cong (λ i → (lookup∘tabulate (λ i₁ → lookup (map f v) (f′ i₁)) (g′ i)))) ⟨
        map g (tabulate (λ i → lookup (tabulate (λ i₁ → lookup (map f v) (f′ i₁))) (g′ i)))
            ≡⟨ ≡.cong (map g) (tabulate-cong (λ i → ≡.cong (λ h → lookup h (g′ i)) (naturality v))) ⟨
        map g (tabulate (λ i → lookup (map f (tabulate (λ i₁ → lookup v (f′ i₁)))) (g′ i))) ∎
      where
        open ≡-Reasoning
