{-# OPTIONS --without-K --safe #-}

open import Level using (Level; 0ℓ; suc)

module Data.System.Looped {ℓ : Level} where

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Categories.Category using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Categories.Functor using (Functor)
open import Data.Nat using (ℕ)
open import Data.System.Category {ℓ} using (Systems[_,_])
open import Data.System.Core {ℓ} using (System; _≤_)
open import Categories.Functor using (Functor)
open import Data.Circuit.Value using (Monoid)
open import Data.Values Monoid using (_⊕_; ⊕-cong; module ≋)
open import Relation.Binary using (Setoid)
open import Function using (Func; _⟨$⟩_) renaming (id to idf)

open Func
open System

private

  loop : {n : ℕ} → System n n → System n n
  loop X = record
      { S = X.S
      ; fₛ = record
          { to = λ i → record
              { to = λ s → X.fₛ′ (i ⊕ X.fₒ′ s) s
              ; cong = λ {s} {s′} ≈s → X.S.trans
                  (cong X.fₛ (⊕-cong ≋.refl (cong X.fₒ ≈s))) (cong (X.fₛ ⟨$⟩ (i ⊕ X.fₒ′ s′)) ≈s)
              }
          ; cong = λ ≋v → cong X.fₛ (⊕-cong ≋v ≋.refl)
          }
      ; fₒ = X.fₒ
      }
    where
      module X = System X

  loop-≤ : {n : ℕ} {A B : System n n} → A ≤ B → loop A ≤ loop B
  loop-≤ {_} {A} {B} A≤B = record
      { ⇒S = A≤B.⇒S
      ; ≗-fₛ = λ i s → begin
          A≤B.⇒S ⟨$⟩ (fₛ′ (loop A) i s)                   ≈⟨ A≤B.≗-fₛ (i ⊕ A.fₒ′ s) s ⟩
          B.fₛ′ (i ⊕ A.fₒ′ s) (A≤B.⇒S ⟨$⟩ s)              ≈⟨ cong B.fₛ (⊕-cong ≋.refl (A≤B.≗-fₒ s)) ⟩
          B.fₛ′ (i ⊕ B.fₒ′ (A≤B.⇒S ⟨$⟩ s)) (A≤B.⇒S ⟨$⟩ s) ∎
      ; ≗-fₒ = A≤B.≗-fₒ
      }
    where
      module A = System A
      module B = System B
      open ≈-Reasoning B.S
      module A≤B = _≤_ A≤B

Loop : (n : ℕ) → Functor Systems[ n , n ] Systems[ n , n ]
Loop n = record
    { F₀ = loop
    ; F₁ = loop-≤
    ; identity = λ {A} → Setoid.refl (S A)
    ; homomorphism = λ {Z = Z} → Setoid.refl (S Z)
    ; F-resp-≈ = idf
    }

module _ (n : ℕ) where

  open Category Systems[ n , n ]
  open Functor (Loop n)

  Systems[_] : Category (suc 0ℓ) ℓ 0ℓ
  Systems[_] = categoryHelper record
      { Obj = Obj
      ; _⇒_ = _⇒_
      ; _≈_ = λ f g → F₁ f ≈ F₁ g
      ; id = id
      ; _∘_ = _∘_
      ; assoc = λ {f = f} {g h} → assoc {f = f} {g} {h}
      ; identityˡ = λ {A B f} → identityˡ {A} {B} {f}
      ; identityʳ = λ {A B f} → identityʳ {A} {B} {f}
      ; equiv = equiv
      ; ∘-resp-≈ = λ {f = f} {g h i} f≈g h≈i → ∘-resp-≈ {f = f} {g} {h} {i} f≈g h≈i
      }
