{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)
open import Level using (Level; suc; 0ℓ)

module Data.System.Monoidal {ℓ : Level} (n : ℕ) where

open import Data.System {ℓ} using (System; Systems; _≤_; ≤-refl; ≤-trans; _≈_; discrete)

open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory; SymmetricMonoidalCategory)
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (Bifunctor; flip-bifunctor)
open import Categories.Morphism (Systems n) using (_≅_; Iso)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; niHelper)
open import Data.Circuit.Value using (Monoid)
open import Data.Product using (_,_; _×_; uncurry′)
open import Data.Product.Function.NonDependent.Setoid using (_×-function_; proj₁ₛ; proj₂ₛ; swapₛ)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Setoid using (_⇒ₛ_; _×-⇒_; assocₛ⇒; assocₛ⇐)
open import Data.Values Monoid using (Values; _⊕_; ⊕-cong; ⊕-identityˡ; ⊕-identityʳ; ⊕-assoc; ⊕-comm; module ≋)
open import Function using (Func; _⟶ₛ_)
open import Function.Construct.Setoid using (_∙_)
open import Relation.Binary using (Setoid)

open _≤_
open Setoid

module _ where

  open Func

  δₛ : Values n ⟶ₛ Values n ×ₛ Values n
  δₛ .to v = v , v
  δₛ .cong v≋w = v≋w , v≋w

  ⊕ₛ : Values n ×ₛ Values n ⟶ₛ Values n
  ⊕ₛ .to (v , w) = v ⊕ w
  ⊕ₛ .cong (v₁≋v₂ , w₁≋w₂) = ⊕-cong v₁≋v₂ w₁≋w₂

_⊗₀_ : System n → System n → System n
_⊗₀_ X Y = let open System in record
    { S = S X ×ₛ S Y
    ; fₛ = fₛ X ×-⇒ fₛ Y ∙ δₛ
    ; fₒ = ⊕ₛ ∙ fₒ X ×-function fₒ Y
    }

_⊗₁_
    : {A A′ B B′ : System n}
      (f : A ≤ A′)
      (g : B ≤ B′)
    → A ⊗₀ B ≤ A′ ⊗₀ B′
_⊗₁_ f g .⇒S = ⇒S f ×-function ⇒S g
_⊗₁_ f g .≗-fₛ i (s₁ , s₂) = ≗-fₛ f i s₁ , ≗-fₛ g i s₂
_⊗₁_ f g .≗-fₒ (s₁ , s₂) = ⊕-cong (≗-fₒ f s₁) (≗-fₒ g s₂)

module _ where

  open Functor
  open System

  ⊗ : Bifunctor (Systems n) (Systems n) (Systems n)
  ⊗ .F₀ = uncurry′ _⊗₀_
  ⊗ .F₁ = uncurry′ _⊗₁_
  ⊗ .identity {X , Y} = refl (S X) , refl (S Y)
  ⊗ .homomorphism {_} {_} {X″ , Y″} = refl (S X″) , refl (S Y″)
  ⊗ .F-resp-≈ (f≈f′ , g≈g′) = f≈f′ , g≈g′

module Unitors {X : System n} where

  open System X

  ⊗-discreteˡ-≤ : discrete n ⊗₀ X ≤ X
  ⊗-discreteˡ-≤ .⇒S = proj₂ₛ
  ⊗-discreteˡ-≤ .≗-fₛ i s = S.refl
  ⊗-discreteˡ-≤ .≗-fₒ (_ , s) = ⊕-identityˡ (fₒ′ s)

  ⊗-discreteˡ-≥ : X ≤ discrete n ⊗₀ X
  ⊗-discreteˡ-≥ .⇒S = record { to = λ s → _ , s ; cong = λ s≈s′ → _ , s≈s′ }
  ⊗-discreteˡ-≥ .≗-fₛ i s = _ , S.refl
  ⊗-discreteˡ-≥ .≗-fₒ s = ≋.sym (⊕-identityˡ (fₒ′ s))

  ⊗-discreteʳ-≤ : X ⊗₀ discrete n ≤ X
  ⊗-discreteʳ-≤ .⇒S = proj₁ₛ
  ⊗-discreteʳ-≤ .≗-fₛ i s = S.refl
  ⊗-discreteʳ-≤ .≗-fₒ (s , _) = ⊕-identityʳ (fₒ′ s)

  ⊗-discreteʳ-≥ : X ≤ X ⊗₀ discrete n
  ⊗-discreteʳ-≥ .⇒S = record { to = λ s → s , _ ; cong = λ s≈s′ → s≈s′ , _ }
  ⊗-discreteʳ-≥ .≗-fₛ i s = S.refl , _
  ⊗-discreteʳ-≥ .≗-fₒ s = ≋.sym (⊕-identityʳ (fₒ′ s))

  open _≅_
  open Iso

  unitorˡ : discrete n ⊗₀ X ≅ X
  unitorˡ .from = ⊗-discreteˡ-≤
  unitorˡ .to = ⊗-discreteˡ-≥
  unitorˡ .iso .isoˡ = _ , S.refl
  unitorˡ .iso .isoʳ = S.refl

  unitorʳ : X ⊗₀ discrete n ≅ X
  unitorʳ .from = ⊗-discreteʳ-≤
  unitorʳ .to = ⊗-discreteʳ-≥
  unitorʳ .iso .isoˡ = S.refl , _
  unitorʳ .iso .isoʳ = S.refl

open Unitors using (unitorˡ; unitorʳ) public

module Associator {X Y Z : System n} where

  module X = System X
  module Y = System Y
  module Z = System Z

  assoc-≤ : (X ⊗₀ Y) ⊗₀ Z ≤ X ⊗₀ (Y ⊗₀ Z)
  assoc-≤ .⇒S = assocₛ⇒
  assoc-≤ .≗-fₛ i ((s₁ , s₂) , s₃) = X.S.refl , Y.S.refl , Z.S.refl
  assoc-≤ .≗-fₒ ((s₁ , s₂) , s₃) = ⊕-assoc (X.fₒ′ s₁) (Y.fₒ′ s₂) (Z.fₒ′ s₃)

  assoc-≥ : X ⊗₀ (Y ⊗₀ Z) ≤ (X ⊗₀ Y) ⊗₀ Z
  assoc-≥ .⇒S = assocₛ⇐
  assoc-≥ .≗-fₛ i (s₁ , (s₂ , s₃)) = (X.S.refl , Y.S.refl) , Z.S.refl
  assoc-≥ .≗-fₒ (s₁ , (s₂ , s₃)) = ≋.sym (⊕-assoc (X.fₒ′ s₁) (Y.fₒ′ s₂) (Z.fₒ′ s₃) )

  open _≅_
  open Iso

  associator : (X ⊗₀ Y) ⊗₀ Z ≅ X ⊗₀ (Y ⊗₀ Z)
  associator .from = assoc-≤
  associator .to = assoc-≥
  associator .iso .isoˡ = (X.S.refl , Y.S.refl) , Z.S.refl
  associator .iso .isoʳ = X.S.refl , Y.S.refl , Z.S.refl

open Associator using (associator) public

Systems-Monoidal : Monoidal (Systems n)
Systems-Monoidal = let open System in record
    { ⊗ = ⊗
    ; unit = discrete n
    ; unitorˡ = unitorˡ
    ; unitorʳ = unitorʳ
    ; associator = associator
    ; unitorˡ-commute-from = λ {_} {Y} → refl (S Y)
    ; unitorˡ-commute-to = λ {_} {Y} → _ , refl (S Y)
    ; unitorʳ-commute-from = λ {_} {Y} → refl (S Y)
    ; unitorʳ-commute-to = λ {_} {Y} → refl (S Y) , _
    ; assoc-commute-from = λ {_} {X′} {_} {_} {Y′} {_} {_} {Z′} → refl (S X′) , refl (S Y′) , refl (S Z′)
    ; assoc-commute-to = λ {_} {X′} {_} {_} {Y′} {_} {_} {Z′} → (refl (S X′) , refl (S Y′)) , refl (S Z′)
    ; triangle = λ {X} {Y} → refl (S X) , refl (S Y)
    ; pentagon = λ {W} {X} {Y} {Z} → refl (S W) , refl (S X) , refl (S Y) , refl (S Z)
    }

open System

⊗-swap-≤ : {X Y : System n} → Y ⊗₀ X ≤ X ⊗₀ Y
⊗-swap-≤ .⇒S = swapₛ
⊗-swap-≤ {X} {Y} .≗-fₛ i (s₁ , s₂) = refl (S X) , refl (S Y)
⊗-swap-≤ {X} {Y} .≗-fₒ (s₁ , s₂) = ⊕-comm (fₒ′ Y s₁) (fₒ′ X s₂)

braiding : ⊗ ≃ flip-bifunctor ⊗
braiding = niHelper record
    { η = λ (X , Y) → ⊗-swap-≤
    ; η⁻¹ = λ (X , Y) → ⊗-swap-≤
    ; commute = λ { {X , Y} {X′ , Y′} (f , g) → refl (S Y′) , refl (S X′) }
    ; iso = λ (X , Y) → record
        { isoˡ = refl (S X) , refl (S Y)
        ; isoʳ = refl (S Y) , refl (S X)
        }
    }

Systems-Symmetric : Symmetric Systems-Monoidal
Systems-Symmetric = record
    { braided = record
        { braiding = braiding
        ; hexagon₁ = λ {X} {Y} {Z} → refl (S Y) , refl (S Z) , refl (S X)
        ; hexagon₂ = λ {X} {Y} {Z} → (refl (S Z) , refl (S X)) , refl (S Y)
        }
    ; commutative = λ {X} {Y} → refl (S Y) , refl (S X)
    }

Systems-MC : MonoidalCategory (suc 0ℓ) ℓ 0ℓ
Systems-MC = record { monoidal = Systems-Monoidal }

Systems-SMC : SymmetricMonoidalCategory (suc 0ℓ) ℓ 0ℓ
Systems-SMC = record { symmetric = Systems-Symmetric }
