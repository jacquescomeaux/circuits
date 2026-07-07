{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (Semiring)
open import Algebra.Morphism.Bundles using (SemiringHomomorphism)
open import Level using (Level)

module Data.Matrix.BaseChange
    {c ℓ : Level}
    (R S : Semiring c ℓ)
    (open Semiring using (rawSemiring))
    (f : SemiringHomomorphism (rawSemiring R) (rawSemiring S))
  where

module R = Semiring R
module S = Semiring S

import Data.Matrix.Category as MCat
import Data.Matrix.Core as MC
import Data.Matrix.Endofunctor as Endo
import Data.Matrix.Monoid as MM
import Data.Matrix.Raw as MR
import Data.Matrix.Transform as MT
import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
import Data.Vector.Bisemimodule as VB
import Data.Vector.Core as VC
import Data.Vector.Endofunctor.Monoid as MonEndo
import Data.Vector.Endofunctor.Setoid as VecEndo
import Data.Vector.Monoid as VM
import Relation.Binary.PropositionalEquality as ≡
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Categories.Functor using (Functor)
open import Category.Instance.Monoids using (MonoidHomomorphism; mk-⇒)
open import Data.Matrix.Category using (Mat)
open import Data.Matrix.Transform using (I)
open import Data.Nat using (ℕ)
open import Data.Vec using (map; []; _∷_; zipWith; replicate)
open import Data.Vec.Properties using (map-∘; map-replicate)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (map⁺)
open import Data.Vector.Core S.setoid using (_≊_)
open import Data.Vector.Core using (Vector)
open import Data.Vector.Monoid using (⟨ε⟩)
open import Data.Vector.Raw using (module Relation)
open import Function using (id; Func; _⟶ₛ_; _⟨$⟩_; _∘_)
open import Level using (0ℓ)

open Func
open Functor
open MC using (Matrix)
open SemiringHomomorphism f
open ℕ
private module Mat {A B : ℕ} = Functor (Endo.Mat A B {c} {ℓ})

open MR hiding (map; Matrix)

module MatR where
  open MC R.setoid public
  open MM R.+-monoid public
  open MT R public
  open MCat R using (_·_) public

module MatS where
  open MC S.setoid public
  open MM S.+-monoid public
  open MT S public
  open MCat S using (_·_) public

module VecR where
  open VC R.setoid public
  open VM R.+-monoid public
  open VB R public

module VecS where
  open VC S.setoid public
  open VM S.+-monoid public
  open VB S public

func : R.setoid ⟶ₛ S.setoid
func .to = ⟦_⟧
func .cong = ⟦⟧-cong

change
    : {A B : ℕ}
    → Matrix R.setoid A B
    → Matrix S.setoid A B
change = to (Mat.₁ func)

resp
    : {A B : ℕ}
      {M M′ : MatR.Matrix A B}
    → M MatR.≋ M′
    → change M MatS.≋ change M′
resp = cong (Mat.₁ func)

opaque
  unfolding I _ᵀ _∷ₕ_ Endo.mapₛ
  ident : {A : ℕ} → change (I R) MatS.≋ I S {A}
  ident {zero} = PW.[]
  ident {suc A} = (1#-homo PW.∷ ⟨ε⟩-homo) PW.∷ map-⟨ε⟩∷ₕI
    where
      ⟨ε⟩-homo : (map ⟦_⟧) VecR.⟨ε⟩ ≊ VecS.⟨ε⟩ {A}
      ⟨ε⟩-homo = MonoidHomomorphism.ε-homo (MonEndo.mapₘ A (mk-⇒ +-monoidHomomorphism))
      map-⟨ε⟩∷ₕI : map (map ⟦_⟧) (VecR.⟨ε⟩ ∷ₕ MatR.I) MatS.≋ VecS.⟨ε⟩ ∷ₕ MatS.I {A}
      map-⟨ε⟩∷ₕI = begin
          map (map ⟦_⟧) (VecR.⟨ε⟩ ∷ₕ MatR.I)            ≡⟨ ≡.cong (λ h → map (map ⟦_⟧) (VecR.⟨ε⟩ ∷ₕ h)) MatR.Iᵀ ⟨
          map (map ⟦_⟧) (VecR.⟨ε⟩ ∷ₕ MatR.I ᵀ)          ≡⟨ ≡.cong (map (map ⟦_⟧)) (∷ᵥ-ᵀ VecR.⟨ε⟩ MatR.I) ⟨
          map (map ⟦_⟧) ((VecR.⟨ε⟩ ∷ᵥ MatR.I) ᵀ)        ≡⟨ Natural.α-ᵀ ⟦_⟧ (VecR.⟨ε⟩ ∷ᵥ MatR.I) ⟩
          map (map ⟦_⟧) (VecR.⟨ε⟩ ∷ᵥ MatR.I) ᵀ          ≡⟨⟩
          (map ⟦_⟧ VecR.⟨ε⟩ ∷ᵥ map (map ⟦_⟧) MatR.I) ᵀ  ≡⟨ ∷ᵥ-ᵀ (map ⟦_⟧ VecR.⟨ε⟩) (map (map ⟦_⟧) MatR.I) ⟩
          map ⟦_⟧ VecR.⟨ε⟩ ∷ₕ (map (map ⟦_⟧) MatR.I ᵀ)  ≡⟨ ≡.cong (map ⟦_⟧ VecR.⟨ε⟩ ∷ₕ_) (Natural.α-ᵀ ⟦_⟧ MatR.I) ⟨
          map ⟦_⟧ VecR.⟨ε⟩ ∷ₕ map (map ⟦_⟧) (MatR.I ᵀ)  ≡⟨ ≡.cong (λ h → map ⟦_⟧ VecR.⟨ε⟩ ∷ₕ map (map ⟦_⟧) h) MatR.Iᵀ ⟩
          map ⟦_⟧ VecR.⟨ε⟩ ∷ₕ map (map ⟦_⟧) MatR.I      ≈⟨ MatS.∷ₕ-cong ⟨ε⟩-homo ident ⟩
          VecS.⟨ε⟩ ∷ₕ MatS.I                            ∎
        where
          open ≈-Reasoning (MatS.Matrixₛ (suc A) A)

opaque
  unfolding VecR._∙_
  ⟦⟧-∙ : {n : ℕ} (V W : VecR.Vector n) → ⟦ V VecR.∙ W ⟧ S.≈ map ⟦_⟧ V VecS.∙ map ⟦_⟧ W
  ⟦⟧-∙ {zero} [] [] = 0#-homo
  ⟦⟧-∙ {suc n} (x ∷ V) (y ∷ W) = begin
      ⟦ x VecR.R.* y VecR.R.+ V VecR.∙ W ⟧                  ≈⟨ +-homo (x VecR.R.* y) (V VecR.∙ W) ⟩
      ⟦ x VecR.R.* y ⟧ S.+ ⟦ V VecR.∙ W ⟧                   ≈⟨ S.+-cong (*-homo x y) (⟦⟧-∙ V W) ⟩
      ⟦ x ⟧ VecS.R.* ⟦ y ⟧ S.+ (map ⟦_⟧ V VecS.∙ map ⟦_⟧ W) ∎
    where
      open ≈-Reasoning S.setoid

opaque
  unfolding VecR.⟨ε⟩
  ⟦⟧-⟨ε⟩ : {n : ℕ} → map ⟦_⟧ (VecR.⟨ε⟩ {n}) VecS.≊ VecS.⟨ε⟩
  ⟦⟧-⟨ε⟩ {n} = begin
      map ⟦_⟧ (replicate n R.0#)  ≡⟨ map-replicate ⟦_⟧ R.0# n ⟩
      replicate n ⟦ R.0# ⟧        ≈⟨ VecS.replicate-cong 0#-homo ⟩
      replicate n VecS.R.0#       ∎
    where
      open ≈-Reasoning (VecS.Vectorₛ n)

opaque
  unfolding MatR.[_]_ Endo.mapₛ
  ⟦⟧-[-]-
      : {n m : ℕ}
        (V : VecR.Vector n)
        (M : MatR.Matrix m n)
      → map ⟦_⟧ (MatR.[ V ] M) VecS.≊ MatS.[ map ⟦_⟧ V ] (change M)
  ⟦⟧-[-]- {n} {m} V M = begin
      map ⟦_⟧ (map (V VecR.∙_) (M ᵀ))                 ≡⟨ map-∘ ⟦_⟧ (V VecR.∙_) (M ᵀ) ⟨
      map (λ x → ⟦ V VecR.∙ x ⟧) (M ᵀ)                ≈⟨ PW.map⁺ (λ {x y} ≈xy → S.trans (⟦⟧-cong (VecR.∙-cong VecR.≊.refl ≈xy)) (⟦⟧-∙ V y)) MatR.≋.refl ⟩
      map (λ x → map ⟦_⟧ V VecS.∙ map ⟦_⟧ x) (M ᵀ)    ≡⟨ map-∘ ((map ⟦_⟧ V) VecS.∙_) (map ⟦_⟧) (M ᵀ) ⟩
      map ((map ⟦_⟧ V) VecS.∙_) (map (map ⟦_⟧) (M ᵀ)) ≡⟨ ≡.cong ( map ((map ⟦_⟧ V) VecS.∙_)) (Natural.α-ᵀ ⟦_⟧ M) ⟩
      map ((map ⟦_⟧ V) VecS.∙_) (map (map ⟦_⟧) M ᵀ)   ∎
    where
      open ≈-Reasoning (VecS.Vectorₛ m)

opaque
  unfolding Endo.mapₛ MatR.[_]_
  homo
      : {X Y Z : ℕ}
        {M : MatR.Matrix X Y}
        {N : MatR.Matrix Y Z}
      → change (N MatR.· M) MatS.≋ change N MatS.· change M
  homo {X} {Y} {Z} {M} {[]} = PW.[]
  homo {X} {Y} {suc Z} {M} {N₀ ∷ N} = ⟦⟧-[-]- N₀ M PW.∷ homo {X} {Y} {Z} {M} {N}

ChangeBase : Functor (Mat R) (Mat S)
ChangeBase = record
    { F₀ = id
    ; F₁ = change
    ; identity = ident
    ; homomorphism = homo
    ; F-resp-≈ = resp
    }
