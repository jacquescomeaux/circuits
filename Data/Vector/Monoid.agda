{-# OPTIONS --without-K --safe #-}

open import Algebra using (Monoid)
open import Level using (Level; _⊔_)

module Data.Vector.Monoid {c ℓ : Level} (M : Monoid c ℓ) where

module M = Monoid M

import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Vec using (Vec; foldr′; zipWith; replicate)
open import Data.Vector.Core M.setoid as S using (Vector; _≊_; module ≊; pull; Vectorₛ)

open M
open Vec

private
  variable
    n A B C : ℕ

opaque

  unfolding Vector

  -- Sum the elements of a vector
  sum : Vector n → M.Carrier
  sum = foldr′ _∙_ ε

  sum-cong : {V V′ : Vector n} → V ≊ V′ → sum V ≈ sum V′
  sum-cong PW.[] = refl
  sum-cong (≈x PW.∷ ≊V) = ∙-cong ≈x (sum-cong ≊V)

opaque

  unfolding Vector

  -- Pointwise sum of two vectors
  _⊕_ : Vector n → Vector n → Vector n
  _⊕_ = zipWith _∙_

  ⊕-cong : {V₁ V₂ W₁ W₂ : Vector n} → V₁ ≊ V₂ → W₁ ≊ W₂ → V₁ ⊕ W₁ ≊ V₂ ⊕ W₂
  ⊕-cong PW.[] PW.[] = PW.[]
  ⊕-cong (≈v PW.∷ ≊V) (≈w PW.∷ ≊W) = ∙-cong ≈v ≈w PW.∷ ⊕-cong ≊V ≊W

  ⊕-assoc : (x y z : Vector n) → x ⊕ y ⊕ z ≊ x ⊕ (y ⊕ z)
  ⊕-assoc [] [] [] = PW.[]
  ⊕-assoc (x₀ ∷ x) (y₀ ∷ y) (z₀ ∷ z) = assoc x₀ y₀ z₀ PW.∷ ⊕-assoc x y z

infixl 6 _⊕_

opaque

  unfolding Vector

  -- The identity vector
  ⟨ε⟩ : Vector n
  ⟨ε⟩ {n} = replicate n ε

opaque

  unfolding _⊕_ ⟨ε⟩

  ⊕-identityˡ : (V : Vector n) → ⟨ε⟩ ⊕ V ≊ V
  ⊕-identityˡ [] = PW.[]
  ⊕-identityˡ (x ∷ V) = identityˡ x PW.∷ ⊕-identityˡ V

  ⊕-identityʳ : (V : Vector n) → V ⊕ ⟨ε⟩ ≊ V
  ⊕-identityʳ [] = PW.[]
  ⊕-identityʳ (x ∷ V) = identityʳ x PW.∷ ⊕-identityʳ V

-- A monoid of vectors for each natural number
Vectorₘ : ℕ → Monoid c (c ⊔ ℓ)
Vectorₘ n = record
    { Carrier = Vector n
    ; _≈_ = _≊_
    ; _∙_ = _⊕_
    ; ε = ⟨ε⟩
    ; isMonoid = record
        { isSemigroup = record
            { isMagma = record
                { isEquivalence = ≊.isEquivalence
                ; ∙-cong = ⊕-cong
                }
            ; assoc = ⊕-assoc
            }
        ; identity = ⊕-identityˡ , ⊕-identityʳ
        }
    }

open import Category.Instance.Setoids.SymmetricMonoidal {c} {c ⊔ ℓ} using (Setoids-×; ×-monoidal′)

open import Categories.Category.Construction.Monoids Setoids-×.monoidal using (Monoids)
open import Categories.Category.Instance.Nat using (Natop)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)
open import Categories.Object.Monoid Setoids-×.monoidal as Obj using (Monoid⇒)
open import Data.Fin using (Fin)
open import Data.Monoid using (module FromMonoid)
open import Data.Monoid {c} {c ⊔ ℓ} using (fromMonoid)
open import Data.Vec using (tabulate; lookup)
open import Data.Vec.Properties using (tabulate-cong; lookup-zipWith; lookup-replicate)
open import Data.Vector.Vec using (zipWith-tabulate; replicate-tabulate)
open import Function using (Func; _⟨$⟩_; _∘_; id)
open import Relation.Binary.PropositionalEquality as ≡ using (module ≡-Reasoning; _≡_; _≗_)

open Functor
open Monoid⇒

Vector′ : ℕ → Obj.Monoid
Vector′ n = fromMonoid (Vectorₘ n)

open ℕ
open Fin
open ≡-Reasoning

opaque

  unfolding pull _⊕_

  pull-⊕ : {f : Fin A → Fin B} (V W : Vector B) → pull f ⟨$⟩ (V ⊕ W) ≡ (pull f ⟨$⟩ V) ⊕ (pull f ⟨$⟩ W)
  pull-⊕ {A} {B} {f} V W = begin
      tabulate (λ i → lookup (zipWith _∙_ V W) (f i))
          ≡⟨ tabulate-cong (λ i → lookup-zipWith _∙_ (f i) V W) ⟩
      tabulate (λ i → lookup V (f i) ∙ lookup W (f i))
          ≡⟨ zipWith-tabulate _∙_ (lookup V ∘ f) (lookup W ∘ f) ⟨
      zipWith _∙_ (tabulate (lookup V ∘ f)) (tabulate (lookup W ∘ f))
          ∎

opaque

  unfolding pull ⟨ε⟩

  pull-⟨ε⟩ : {f : Fin A → Fin B} → pull f ⟨$⟩ ⟨ε⟩ ≡ ⟨ε⟩
  pull-⟨ε⟩ {f = f} = begin
      tabulate (λ i → lookup (replicate _ ε) (f i)) ≡⟨ tabulate-cong (λ i → lookup-replicate (f i) ε) ⟩
      tabulate (λ _ → ε)                            ≡⟨ replicate-tabulate ε ⟨
      replicate _ ε                                 ∎

opaque

  unfolding FromMonoid.μ

  pullₘ : (Fin A → Fin B) → Monoid⇒ (Vector′ B) (Vector′ A)
  pullₘ f .arr = S.pull f
  pullₘ f .preserves-μ {V , W} = ≊.reflexive (pull-⊕ V W)
  pullₘ f .preserves-η = ≊.reflexive pull-⟨ε⟩

  pullₘ-id : {V : Vector n} → arr (pullₘ id) ⟨$⟩ V ≊ V
  pullₘ-id = S.pull-id

  pullₘ-∘
      : {f : Fin B → Fin A}
        {g : Fin C → Fin B}
        {v : Vector A}
      → arr (pullₘ (f ∘ g)) ⟨$⟩ v ≊ arr (pullₘ g) ⟨$⟩ (arr (pullₘ f) ⟨$⟩ v)
  pullₘ-∘ = S.pull-∘

  pullₘ-cong
      : {f g : Fin B → Fin A}
      → f ≗ g
      → {v : Vector A}
      → arr (pullₘ f) ⟨$⟩ v ≊ arr (pullₘ g) ⟨$⟩ v
  pullₘ-cong = S.pull-cong

-- Contravariant functor from Nat to Monoids
Pullₘ : Functor Natop Monoids
Pullₘ .F₀ = Vector′
Pullₘ .F₁ = pullₘ
Pullₘ .identity = pullₘ-id
Pullₘ .homomorphism = pullₘ-∘
Pullₘ .F-resp-≈ = pullₘ-cong
