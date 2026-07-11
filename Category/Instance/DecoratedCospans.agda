{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Functor.Monoidal.Symmetric using (module Lax)
open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)

open Lax using (SymmetricMonoidalFunctor)
open FinitelyCocompleteCategory
  using ()
  renaming (symmetricMonoidalCategory to smc)

module Category.Instance.DecoratedCospans
    {o o′ ℓ ℓ′ e e′}
    (𝒞 : FinitelyCocompleteCategory o ℓ e)
    {𝒟 : SymmetricMonoidalCategory o′ ℓ′ e′}
    (F : SymmetricMonoidalFunctor (smc 𝒞) 𝒟) where

module 𝒞 = FinitelyCocompleteCategory 𝒞
module 𝒟 = SymmetricMonoidalCategory 𝒟

import Categories.Category.Monoidal.Utilities as ⊗-Util
import Category.Instance.Cospans 𝒞 as Cospans
import Category.Diagram.Cospan 𝒞 as Cospan

open import Categories.Category using (Category; _[_∘_])
open import Categories.Category.Cocartesian.Monoidal using (module CocartesianMonoidal)
open import Categories.Diagram.Pushout using (Pushout)
open import Categories.Diagram.Pushout.Properties 𝒞.U using (up-to-iso)
open import Categories.Functor.Properties using ([_]-resp-≅; [_]-resp-square)
open import Categories.Morphism.Reasoning using (switch-fromtoˡ; glueTrianglesˡ)
open import Cospan.Decorated 𝒞 F using (DecoratedCospan)
open import Relation.Binary using (IsEquivalence)
open import Data.Product using (_,_)
open import Function using (flip)
open import Level using (_⊔_)

open import Category.Diagram.Pushout 𝒞.U using (glue-i₁; glue-i₂; pushout-id-g; pushout-f-id)

import Category.Monoidal.Coherence as Coherence

import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as ⇒-Reasoning
import Categories.Category.Monoidal.Reasoning as ⊗-Reasoning


open SymmetricMonoidalFunctor F
  renaming (identity to F-identity; F to F′)

private

  variable
    A B C D : 𝒞.Obj

compose : DecoratedCospan A B → DecoratedCospan B C → DecoratedCospan A C
compose c₁ c₂ = record
    { cospan = Cospan.compose C₁.cospan C₂.cospan
    ; decoration = F₁ [ i₁ , i₂ ] ∘ φ ∘ s⊗t
    }
  where
    module C₁ = DecoratedCospan c₁
    module C₂ = DecoratedCospan c₂
    open 𝒞 using ([_,_]; _+_)
    open 𝒟 using (_⊗₀_; _⊗₁_; _∘_; unitorʳ; _⇒_; unit)
    module p = 𝒞.pushout C₁.f₂ C₂.f₁
    open p using (i₁; i₂)
    φ : F₀ C₁.N ⊗₀ F₀ C₂.N ⇒ F₀ (C₁.N + C₂.N)
    φ = ⊗-homo.η (C₁.N , C₂.N)
    s⊗t : unit ⇒ F₀ C₁.N ⊗₀ F₀ C₂.N
    s⊗t = C₁.decoration ⊗₁ C₂.decoration ∘ unitorʳ.to

identity : DecoratedCospan A A
identity = record
    { cospan = Cospan.identity
    ; decoration = 𝒟.U [ F₁ 𝒞.¡ ∘ ε ]
    }

record _≈_ (C₁ C₂ : DecoratedCospan A B) : Set (ℓ ⊔ e ⊔ e′) where

  private
    module C₁ = DecoratedCospan C₁
    module C₂ = DecoratedCospan C₂

  field
    cospans-≈ : C₁.cospan Cospan.≈ C₂.cospan

  open Cospan._≈_ cospans-≈ public
  open Morphism 𝒟.U using (_≅_)

  field
    same-deco : F₁ ≅N.from 𝒟.∘ C₁.decoration 𝒟.≈ C₂.decoration

  ≅F[N] : F₀ C₁.N ≅ F₀ C₂.N
  ≅F[N] = [ F′ ]-resp-≅ ≅N

infix 4 _≈_

module _ where

  open 𝒟.HomReasoning
  open 𝒟.Equiv
  open 𝒟 using (identityˡ)

  private
    variable
      f g h : DecoratedCospan A B

  abstract

    ≈-refl : f ≈ f
    ≈-refl = record
        { cospans-≈ = Cospan.≈-refl
        ; same-deco = F-identity ⟩∘⟨refl ○ identityˡ
        }

    ≈-sym : f ≈ g → g ≈ f
    ≈-sym f≈g = record
        { cospans-≈ = Cospan.≈-sym cospans-≈
        ; same-deco = sym (switch-fromtoˡ 𝒟.U ≅F[N] same-deco)
        }
      where
        open _≈_ f≈g

    ≈-trans : f ≈ g → g ≈ h → f ≈ h
    ≈-trans f≈g g≈h = record
        { cospans-≈ = Cospan.≈-trans f≈g.cospans-≈ g≈h.cospans-≈
        ; same-deco =
              homomorphism ⟩∘⟨refl ○
              glueTrianglesˡ 𝒟.U g≈h.same-deco f≈g.same-deco
        }
      where
        module f≈g = _≈_ f≈g
        module g≈h = _≈_ g≈h

  ≈-equiv : {A B : 𝒞.Obj} → IsEquivalence (_≈_ {A} {B})
  ≈-equiv = record
      { refl = ≈-refl
      ; sym = ≈-sym
      ; trans = ≈-trans
      }

compose-assoc
    : {c₁ : DecoratedCospan A B}
      {c₂ : DecoratedCospan B C}
      {c₃ : DecoratedCospan C D}
    → compose c₁ (compose c₂ c₃) ≈ compose (compose c₁ c₂) c₃
compose-assoc {A} {B} {C} {D} {c₁} {c₂} {c₃} = record
    { cospans-≈ = Cospans.compose-assoc
    ; same-deco = deco-assoc
    }
  where
    module C₁ = DecoratedCospan c₁
    module C₂ = DecoratedCospan c₂
    module C₃ = DecoratedCospan c₃
    open 𝒞 using (+-assoc; pushout; [_,_]; _+₁_; _+_) renaming (_∘_ to _∘′_; id to id′)
    p₁ : Pushout 𝒞.U C₁.f₂ C₂.f₁
    p₁ = pushout C₁.f₂ C₂.f₁
    p₂ : Pushout 𝒞.U C₂.f₂ C₃.f₁
    p₂ = pushout C₂.f₂ C₃.f₁
    module P₁ = Pushout p₁
    module P₂ = Pushout p₂
    p₃ : Pushout 𝒞.U P₁.i₂ P₂.i₁
    p₃ = pushout P₁.i₂ P₂.i₁
    p₁₃ p₄ : Pushout 𝒞.U C₁.f₂ (P₂.i₁ ∘′ C₂.f₁)
    p₁₃ = glue-i₂ p₁ p₃
    p₄ = pushout C₁.f₂ (P₂.i₁ ∘′ C₂.f₁)
    p₂₃ p₅ : Pushout 𝒞.U (P₁.i₂ ∘′ C₂.f₂) C₃.f₁
    p₂₃ = glue-i₁ p₂ p₃
    p₅ = pushout (P₁.i₂ ∘′ C₂.f₂) C₃.f₁
    module P₃ = Pushout p₃
    module P₄ = Pushout p₄
    module P₅ = Pushout p₅
    module P₁₃ = Pushout p₁₃
    module P₂₃ = Pushout p₂₃
    open Morphism 𝒞.U using (_≅_)
    module P₄≅P₁₃ = _≅_ (up-to-iso p₄ p₁₃)
    module P₅≅P₂₃ = _≅_ (up-to-iso p₅ p₂₃)

    N M P Q R : 𝒞.Obj
    N = C₁.N
    M = C₂.N
    P = C₃.N
    Q = P₁.Q
    R = P₂.Q

    f : N 𝒞.⇒ Q
    f = P₁.i₁

    g : M 𝒞.⇒ Q
    g = P₁.i₂

    h : M 𝒞.⇒ R
    h = P₂.i₁

    i : P 𝒞.⇒ R
    i = P₂.i₂

    j : Q 𝒞.⇒ P₃.Q
    j = P₃.i₁

    k : R 𝒞.⇒ P₃.Q
    k = P₃.i₂

    w : N 𝒞.⇒ P₄.Q
    w = P₄.i₁

    x : R 𝒞.⇒ P₄.Q
    x = P₄.i₂

    y : Q 𝒞.⇒ P₅.Q
    y = P₅.i₁

    z : P 𝒞.⇒ P₅.Q
    z = P₅.i₂

    l : P₂₃.Q 𝒞.⇒ P₅.Q
    l = P₅≅P₂₃.to

    m : P₄.Q 𝒞.⇒ P₁₃.Q
    m = P₄≅P₁₃.from

    module +-assoc {m} {n} {o} = _≅_ (+-assoc {m} {n} {o})

    module _ where

      open 𝒞 using (∘[]; []-congʳ; []-congˡ; []∘+₁; []∘+-assocˡ; []-cong₂)

      open ⇒-Reasoning 𝒞.U
      open 𝒞 using (id; _∘_; _≈_; assoc; identityʳ)
      open 𝒞.HomReasoning
      open 𝒞.Equiv

      copairings : ((l ∘ m) ∘ [ w , x ]) ∘ (id +₁ [ h , i ]) 𝒞.≈ [ y , z ] ∘ ([ f , g ] +₁ id) ∘ +-assoc.from
      copairings = begin
          ((l ∘ m) ∘ [ w , x ]) ∘ (id +₁ [ h , i ])         ≈⟨ ∘[] ⟩∘⟨refl ⟩
          [(l ∘ m) ∘ w , (l ∘ m) ∘ x ] ∘ (id +₁ [ h , i ])  ≈⟨ []-cong₂ (pullʳ P₄.universal∘i₁≈h₁) (pullʳ P₄.universal∘i₂≈h₂) ⟩∘⟨refl ⟩
          [ l ∘ j ∘ f , l ∘ k ] ∘ (id +₁ [ h , i ])         ≈⟨ []-congʳ (pullˡ P₂₃.universal∘i₁≈h₁) ⟩∘⟨refl ⟩
          [ y ∘ f , l ∘ k ] ∘ (id +₁ [ h , i ])             ≈⟨ []∘+₁ ⟩
          [ (y ∘ f) ∘ id , (l ∘ k) ∘ [ h , i ] ]            ≈⟨ []-cong₂ identityʳ ∘[] ⟩
          [ y ∘ f , [ (l ∘ k) ∘ h , (l ∘ k) ∘ i ] ]         ≈⟨ []-congˡ ([]-cong₂ (pullʳ (sym P₃.commute)) (assoc ○ P₂₃.universal∘i₂≈h₂)) ⟩
          [ y ∘ f , [ l ∘ j ∘ g , z ] ]                     ≈⟨ []-congˡ ([]-congʳ (pullˡ P₂₃.universal∘i₁≈h₁)) ⟩
          [ y ∘ f , [ y ∘ g , z ] ]                         ≈⟨ []∘+-assocˡ ⟨
          [ [ y ∘ f , y ∘ g ] , z ] ∘ +-assoc.from          ≈⟨ []-cong₂ ∘[] identityʳ ⟩∘⟨refl ⟨
          [ y ∘ [ f ,  g ] , z ∘ id ] ∘ +-assoc.from        ≈⟨ pullˡ []∘+₁ ⟨
          [ y , z ] ∘ ([ f , g ] +₁ id) ∘ +-assoc.from      ∎

    module _ where

      open ⊗-Reasoning 𝒟.monoidal
      open ⇒-Reasoning 𝒟.U
      open 𝒟 using (_⊗₀_; _⊗₁_; id; _∘_; _≈_; assoc; sym-assoc; identityʳ; ⊗; identityˡ; triangle; assoc-commute-to; assoc-commute-from)
      open 𝒟 using (_⇒_; unit)

      open ⊗-Util 𝒟.monoidal using (module Shorthands)
      open Shorthands using (α⇒; α⇐; λ⇒; λ⇐; ρ⇒; ρ⇐)

      open Coherence 𝒟.monoidal using (λ₁≅ρ₁⇐)
      open 𝒟.Equiv

      +-α⇒ : {m n o : 𝒞.Obj} → m + (n + o) 𝒞.⇒ (m + n) + o
      +-α⇒ = +-assoc.from
      +-α⇐ : {m n o : 𝒞.Obj} → (m + n) + o 𝒞.⇒ m + (n + o)
      +-α⇐ = +-assoc.to

      s : unit ⇒ F₀ N
      s = C₁.decoration

      t : unit ⇒ F₀ M
      t = C₂.decoration

      u : unit ⇒ F₀ P
      u = C₃.decoration

      F[l∘m] : F₀ P₄.Q ⇒ F₀ P₅.Q
      F[l∘m] = F₁ (l ∘′ m)

      F[w,x] : F₀ (N + R) ⇒ F₀ P₄.Q
      F[w,x] = F₁ [ w , x ]

      F[h,i] : F₀ (M + P) ⇒ F₀ R
      F[h,i] = F₁ [ h , i ]

      F[y,z] : F₀ (Q + P) ⇒ F₀ P₅.Q
      F[y,z] = F₁ [ y , z ]

      F[f,g] : F₀ (N + M) ⇒ F₀ Q
      F[f,g] = F₁ [ f , g ]

      F[[f,g]+id] : F₀ ((N + M) + P) ⇒ F₀ (Q + P)
      F[[f,g]+id] = F₁ ([ f , g ] +₁ id′)

      F[id+[h,i]] : F₀ (N + (M + P)) ⇒ F₀ (N + R)
      F[id+[h,i]] = F₁ (id′ +₁ [ h , i ])

      φ[N,R] : F₀ N ⊗₀ F₀ R 𝒟.⇒ F₀ (N + R)
      φ[N,R] = ⊗-homo.η (N , R)

      φ[M,P] : F₀ M ⊗₀ F₀ P 𝒟.⇒ F₀ (M + P)
      φ[M,P] = ⊗-homo.η (M , P)

      φ[N+M,P] : F₀ (N + M) ⊗₀ F₀ P 𝒟.⇒ F₀ ((N + M) + P)
      φ[N+M,P] = ⊗-homo.η (N + M , P)

      φ[N,M] : F₀ N ⊗₀ F₀ M 𝒟.⇒ F₀ (N + M)
      φ[N,M] = ⊗-homo.η (N , M)

      φ[N,M+P] : F₀ N ⊗₀ F₀ (M + P) 𝒟.⇒ F₀ (N + (M + P))
      φ[N,M+P] = ⊗-homo.η (N , M + P)

      φ[Q,P] : F₀ Q ⊗₀ F₀ P 𝒟.⇒ F₀ (Q + P)
      φ[Q,P] = ⊗-homo.η (Q , P)

      s⊗[t⊗u] : unit 𝒟.⇒ F₀ N ⊗₀ (F₀ M ⊗₀ F₀ P)
      s⊗[t⊗u] = s ⊗₁ (t ⊗₁ u ∘ ρ⇐) ∘ ρ⇐

      [s⊗t]⊗u : unit 𝒟.⇒ (F₀ N ⊗₀ F₀ M) ⊗₀ F₀ P
      [s⊗t]⊗u = (s ⊗₁ t ∘ ρ⇐) ⊗₁ u ∘ ρ⇐

      abstract
        F-copairings : F[l∘m] ∘ F[w,x] ∘ F[id+[h,i]] 𝒟.≈ F[y,z] ∘ F[[f,g]+id] ∘ F₁ +-assoc.from
        F-copairings = begin
            F[l∘m] ∘ F[w,x] ∘ F[id+[h,i]]                     ≈⟨ pushˡ homomorphism ⟨
            F₁ ((l ∘′ m) ∘′ [ w , x ]) ∘ F[id+[h,i]]          ≈⟨ [ F′ ]-resp-square copairings ⟩
            F[y,z] ∘ F₁ (([ f , g ] +₁ id′) ∘′ +-assoc.from)  ≈⟨ refl⟩∘⟨ homomorphism ⟩
            F[y,z] ∘ F[[f,g]+id] ∘ F₁ +-assoc.from            ∎

        coherences : φ[N,M+P] ∘ id ⊗₁ φ[M,P] 𝒟.≈ F₁ +-assoc.to ∘ φ[N+M,P] ∘ φ[N,M] ⊗₁ id ∘ α⇐
        coherences = begin
            φ[N,M+P] ∘ id ⊗₁ φ[M,P]                         ≈⟨ refl⟩∘⟨ insertʳ 𝒟.associator.isoʳ ⟩
            φ[N,M+P] ∘ (id ⊗₁ φ[M,P] ∘ α⇒) ∘ α⇐             ≈⟨ extendʳ associativity ⟨
            F₁ +-assoc.to ∘ (φ[N+M,P] ∘ φ[N,M] ⊗₁ id) ∘ α⇐  ≈⟨ refl⟩∘⟨ assoc ⟩
            F₁ +-assoc.to ∘ φ[N+M,P] ∘ φ[N,M] ⊗₁ id ∘ α⇐    ∎

        triangle-to : α⇒ {𝒟.unit} {𝒟.unit} {𝒟.unit} ∘ ρ⇐ ⊗₁ id 𝒟.≈ id ⊗₁ λ⇐
        triangle-to = begin
            α⇒ ∘ ρ⇐ ⊗₁ id                          ≈⟨ pullˡ identityˡ ⟨
            id ∘ α⇒ ∘ ρ⇐ ⊗₁ id                     ≈⟨ ⊗.identity ⟩∘⟨refl ⟨
            id ⊗₁ id ∘ α⇒ ∘ ρ⇐ ⊗₁ id               ≈⟨ refl⟩⊗⟨ 𝒟.unitorˡ.isoˡ ⟩∘⟨refl ⟨
            id ⊗₁ (λ⇐ ∘ λ⇒) ∘ α⇒ ∘ ρ⇐ ⊗₁ id        ≈⟨ identityʳ ⟩⊗⟨refl ⟩∘⟨refl ⟨
            (id ∘ id) ⊗₁ (λ⇐ ∘ λ⇒) ∘ α⇒ ∘ ρ⇐ ⊗₁ id ≈⟨ pushˡ ⊗-distrib-over-∘ ⟩
            id ⊗₁ λ⇐ ∘ id ⊗₁ λ⇒ ∘ α⇒ ∘ ρ⇐ ⊗₁ id    ≈⟨ refl⟩∘⟨ pullˡ triangle ⟩
            id ⊗₁ λ⇐ ∘ ρ⇒ ⊗₁ id ∘ ρ⇐ ⊗₁ id         ≈⟨ refl⟩∘⟨ ⊗-distrib-over-∘ ⟨
            id ⊗₁ λ⇐ ∘ (ρ⇒ ∘ ρ⇐) ⊗₁ (id ∘ id)      ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ identityˡ ⟩
            id ⊗₁ λ⇐ ∘ (ρ⇒ ∘ ρ⇐) ⊗₁ id             ≈⟨ refl⟩∘⟨ 𝒟.unitorʳ.isoʳ ⟩⊗⟨refl ⟩
            id ⊗₁ λ⇐ ∘ id ⊗₁ id                    ≈⟨ refl⟩∘⟨ ⊗.identity ⟩
            id ⊗₁ λ⇐ ∘ id                          ≈⟨ identityʳ ⟩
            id ⊗₁ λ⇐                               ∎

        unitors : s ⊗₁ (t ⊗₁ u ∘ ρ⇐) ∘ ρ⇐ 𝒟.≈ α⇒ ∘ (s ⊗₁ t ∘ ρ⇐) ⊗₁ u ∘ ρ⇐
        unitors = begin
            s ⊗₁ (t ⊗₁ u ∘ ρ⇐) ∘ ρ⇐               ≈⟨ pushˡ split₂ʳ ⟩
            s ⊗₁ t ⊗₁ u ∘ id ⊗₁ ρ⇐ ∘ ρ⇐           ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ λ₁≅ρ₁⇐ ⟩∘⟨refl ⟨
            s ⊗₁ t ⊗₁ u ∘ id ⊗₁ λ⇐ ∘ ρ⇐           ≈⟨ refl⟩∘⟨ pullˡ triangle-to ⟨
            s ⊗₁ t ⊗₁ u ∘ α⇒ ∘ ρ⇐ ⊗₁ id ∘ ρ⇐      ≈⟨ extendʳ assoc-commute-from ⟨
            α⇒ ∘ (s ⊗₁ t) ⊗₁ u ∘ ρ⇐ ⊗₁ id ∘ ρ⇐    ≈⟨ refl⟩∘⟨ pushˡ split₁ʳ ⟨
            α⇒ ∘ (s ⊗₁ t ∘ ρ⇐) ⊗₁ u ∘ ρ⇐          ∎

        deco-assoc
            : F[l∘m] ∘ (F[w,x] ∘ φ[N,R] ∘ s ⊗₁ (F[h,i] ∘ φ[M,P] ∘ t ⊗₁ u ∘ ρ⇐) ∘ ρ⇐)
            𝒟.≈ F[y,z] ∘ φ[Q,P] ∘ (F[f,g] ∘ φ[N,M] ∘ s ⊗₁ t ∘ ρ⇐) ⊗₁ u ∘ ρ⇐
        deco-assoc = begin
            F[l∘m] ∘ F[w,x] ∘ φ[N,R] ∘ s ⊗₁ (F[h,i] ∘ φ[M,P] ∘ t ⊗₁ u ∘ ρ⇐) ∘ ρ⇐                          ≈⟨ pullˡ refl ⟩
            (F[l∘m] ∘ F[w,x]) ∘ φ[N,R] ∘ s ⊗₁ (F[h,i] ∘ φ[M,P] ∘ t ⊗₁ u ∘ ρ⇐) ∘ ρ⇐                        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₂ˡ ⟩∘⟨refl ⟩
            (F[l∘m] ∘ F[w,x]) ∘ φ[N,R] ∘ (id ⊗₁ F[h,i] ∘ s ⊗₁ (φ[M,P] ∘ t ⊗₁ u ∘ ρ⇐)) ∘ ρ⇐                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩∘⟨ split₂ˡ) ⟩∘⟨refl ⟩
            (F[l∘m] ∘ F[w,x]) ∘ φ[N,R] ∘ (id ⊗₁ F[h,i] ∘ id ⊗₁ φ[M,P] ∘ s ⊗₁ (t ⊗₁ u ∘ ρ⇐)) ∘ ρ⇐          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
            (F[l∘m] ∘ F[w,x]) ∘ φ[N,R] ∘ id ⊗₁ F[h,i] ∘ (id ⊗₁ φ[M,P] ∘ s ⊗₁ (t ⊗₁ u ∘ ρ⇐)) ∘ ρ⇐          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ F-identity ⟩⊗⟨refl ⟩∘⟨refl ⟨
            (F[l∘m] ∘ F[w,x]) ∘ φ[N,R] ∘ F₁ id′ ⊗₁ F[h,i] ∘ (id ⊗₁ φ[M,P] ∘ s ⊗₁ (t ⊗₁ u ∘ ρ⇐)) ∘ ρ⇐      ≈⟨ refl⟩∘⟨ extendʳ (⊗-homo.commute (id′ , [ h  , i ])) ⟩
            (F[l∘m] ∘ F[w,x]) ∘ F[id+[h,i]] ∘ φ[N,M+P] ∘ (id ⊗₁ φ[M,P] ∘ s ⊗₁ (t ⊗₁ u ∘ ρ⇐)) ∘ ρ⇐         ≈⟨ pullˡ assoc ⟩
            (F[l∘m] ∘ F[w,x] ∘ F[id+[h,i]]) ∘ φ[N,M+P] ∘ (id ⊗₁ φ[M,P] ∘ s ⊗₁ (t ⊗₁ u ∘ ρ⇐)) ∘ ρ⇐         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
            (F[l∘m] ∘ F[w,x] ∘ F[id+[h,i]]) ∘ φ[N,M+P] ∘ id ⊗₁ φ[M,P] ∘ s⊗[t⊗u]                           ≈⟨ refl⟩∘⟨ sym-assoc ⟩
            (F[l∘m] ∘ F[w,x] ∘ F[id+[h,i]]) ∘ (φ[N,M+P] ∘ id ⊗₁ φ[M,P]) ∘ s⊗[t⊗u]                         ≈⟨ F-copairings ⟩∘⟨ coherences ⟩∘⟨ unitors ⟩
            (F[y,z] ∘ F[[f,g]+id] ∘ F₁ +-α⇒) ∘ (F₁ +-α⇐ ∘ φ[N+M,P] ∘ φ[N,M] ⊗₁ id ∘ α⇐) ∘ α⇒ ∘ [s⊗t]⊗u    ≈⟨ sym-assoc ⟩∘⟨ assoc ⟩
            ((F[y,z] ∘ F[[f,g]+id]) ∘ F₁ +-α⇒) ∘ F₁ +-α⇐ ∘ (φ[N+M,P] ∘ φ[N,M] ⊗₁ id ∘ α⇐) ∘ α⇒ ∘ [s⊗t]⊗u  ≈⟨ assoc ⟩
            (F[y,z] ∘ F[[f,g]+id]) ∘ F₁ +-α⇒ ∘ F₁ +-α⇐ ∘ (φ[N+M,P] ∘ φ[N,M] ⊗₁ id ∘ α⇐) ∘ α⇒ ∘ [s⊗t]⊗u    ≈⟨ refl⟩∘⟨ pushˡ homomorphism ⟨
            (F[y,z] ∘ F[[f,g]+id]) ∘ F₁ (+-α⇒ ∘′ +-α⇐) ∘ (φ[N+M,P] ∘ φ[N,M] ⊗₁ id ∘ α⇐) ∘ α⇒ ∘ [s⊗t]⊗u    ≈⟨ refl⟩∘⟨ F-resp-≈ +-assoc.isoʳ ⟩∘⟨refl ⟩
            (F[y,z] ∘ F[[f,g]+id]) ∘ F₁ id′ ∘ (φ[N+M,P] ∘ φ[N,M] ⊗₁ id ∘ α⇐) ∘ α⇒ ∘ [s⊗t]⊗u               ≈⟨ refl⟩∘⟨ F-identity ⟩∘⟨refl ⟩
            (F[y,z] ∘ F[[f,g]+id]) ∘ id ∘ (φ[N+M,P] ∘ φ[N,M] ⊗₁ id ∘ α⇐) ∘ α⇒ ∘ [s⊗t]⊗u                   ≈⟨ refl⟩∘⟨ identityˡ ⟩
            (F[y,z] ∘ F[[f,g]+id]) ∘ (φ[N+M,P] ∘ φ[N,M] ⊗₁ id ∘ α⇐) ∘ α⇒ ∘ [s⊗t]⊗u                        ≈⟨ refl⟩∘⟨ sym-assoc ⟩∘⟨refl ⟩
            (F[y,z] ∘ F[[f,g]+id]) ∘ ((φ[N+M,P] ∘ φ[N,M] ⊗₁ id) ∘ α⇐) ∘ α⇒ ∘ [s⊗t]⊗u                      ≈⟨ refl⟩∘⟨ cancelInner 𝒟.associator.isoˡ ⟩
            (F[y,z] ∘ F[[f,g]+id]) ∘ (φ[N+M,P] ∘ φ[N,M] ⊗₁ id) ∘ [s⊗t]⊗u                                  ≈⟨ refl⟩∘⟨ assoc ⟩
            (F[y,z] ∘ F[[f,g]+id]) ∘ φ[N+M,P] ∘ φ[N,M] ⊗₁ id ∘ [s⊗t]⊗u                                    ≈⟨ assoc ⟩
            F[y,z] ∘ F[[f,g]+id] ∘ φ[N+M,P] ∘ φ[N,M] ⊗₁ id ∘ [s⊗t]⊗u                                      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₁ˡ ⟨
            F[y,z] ∘ F[[f,g]+id] ∘ φ[N+M,P] ∘ (φ[N,M] ∘ s ⊗₁ t ∘ ρ⇐) ⊗₁ u ∘ ρ⇐                            ≈⟨ refl⟩∘⟨ extendʳ (⊗-homo.commute ([ f  , g ] , id′)) ⟨
            F[y,z] ∘ φ[Q,P] ∘ F[f,g] ⊗₁ F₁ id′ ∘ (φ[N,M] ∘ s ⊗₁ t ∘ ρ⇐) ⊗₁ u ∘ ρ⇐                         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ F-identity ⟩∘⟨refl ⟩
            F[y,z] ∘ φ[Q,P] ∘ F[f,g] ⊗₁ id ∘ (φ[N,M] ∘ s ⊗₁ t ∘ ρ⇐) ⊗₁ u ∘ ρ⇐                             ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₁ˡ ⟨
            F[y,z] ∘ φ[Q,P] ∘ (F[f,g] ∘ φ[N,M] ∘ s ⊗₁ t ∘ ρ⇐) ⊗₁ u ∘ ρ⇐                                   ∎

compose-idʳ : {C : DecoratedCospan A B} → compose identity C ≈ C
compose-idʳ {A} {_} {C} = record
    { cospans-≈ = Cospans.compose-idʳ
    ; same-deco = deco-id
    }
  where
    open DecoratedCospan C
    open 𝒞 using (pushout; [_,_]; ⊥; _+₁_; ¡; _+_)
    P = pushout 𝒞.id f₁
    P′ = pushout-id-g {g = f₁}
    ≅P = up-to-iso P P′
    open Morphism 𝒞.U using (_≅_)
    module ≅P = _≅_ ≅P
    open Pushout P
    open 𝒞
      using (cocartesian)
      renaming (id to id′; _∘_ to _∘′_)
    open CocartesianMonoidal cocartesian using (⊥+A≅A)
    module ⊥+A≅A {a} = _≅_ (⊥+A≅A {a})
    module _ where
      open 𝒞
        using
          ( _⇒_ ; _∘_ ; _≈_ ; id ; U
          ; identity²
          ; cocartesian ; initial ; ¡-unique
          ; ∘[] ; []∘+₁ ; inject₂ ; assoc ; []-cong₂
          ; module HomReasoning ; module Equiv
          )
      open Equiv
      open ⇒-Reasoning U
      open HomReasoning
      copairing-id : ((≅P.from ∘ [ i₁ , i₂ ]) ∘ (¡ +₁ id)) ∘ ⊥+A≅A.to 𝒞.≈ id
      copairing-id = begin
        ((≅P.from ∘ [ i₁ , i₂ ]) ∘ (¡ +₁ id)) ∘ ⊥+A≅A.to        ≈⟨ assoc ⟩
        (≅P.from ∘ [ i₁ , i₂ ]) ∘ (¡ +₁ id) ∘ ⊥+A≅A.to          ≈⟨ assoc ⟩
        ≅P.from ∘ [ i₁ , i₂ ] ∘ (¡ +₁ id) ∘ ⊥+A≅A.to            ≈⟨ pullˡ ∘[] ⟩
        [ ≅P.from ∘ i₁ , ≅P.from ∘ i₂ ] ∘ (¡ +₁ id) ∘ ⊥+A≅A.to  ≈⟨ pullˡ []∘+₁ ⟩
        [ (≅P.from ∘ i₁) ∘ ¡ , (≅P.from ∘ i₂) ∘ id ] ∘ ⊥+A≅A.to ≈⟨ []-cong₂ (universal∘i₁≈h₁ ⟩∘⟨refl) (universal∘i₂≈h₂ ⟩∘⟨refl) ⟩∘⟨refl ⟩
        [ f₁ ∘ ¡ , id ∘ id ] ∘ ⊥+A≅A.to                         ≈⟨ []-cong₂ (sym (¡-unique (f₁ ∘ ¡))) identity² ⟩∘⟨refl ⟩
        [ ¡ , id ] ∘ ⊥+A≅A.to                                   ≈⟨ inject₂ ⟩
        id                                                      ∎
    module _ where
      open 𝒟
        using
          ( id ; _∘_ ; _≈_ ; _⇒_ ; U
          ; assoc ; sym-assoc; identityˡ
          ; monoidal ; _⊗₀_; _⊗₁_ ; unit ; unitorˡ ; unitorʳ
          )
      open ⊗-Reasoning monoidal
      open ⇒-Reasoning U
      open ⊗-Util 𝒟.monoidal using (module Shorthands)
      open Shorthands using (λ⇒; λ⇐; ρ⇐)
      open Coherence 𝒟.monoidal using (λ₁≅ρ₁⇐)
      open 𝒟.Equiv
      s : unit ⇒ F₀ N
      s = decoration
      φ[⊥,N] : F₀ ⊥ ⊗₀ F₀ N ⇒ F₀ (⊥ + N)
      φ[⊥,N] = ⊗-homo.η (⊥ , N)
      φ[A,N] : F₀ A ⊗₀ F₀ N ⇒ F₀ (A + N)
      φ[A,N] = ⊗-homo.η (A , N)
      abstract
        cohere-s : φ[⊥,N] ∘ ε ⊗₁ s ∘ ρ⇐ 𝒟.≈ F₁ ⊥+A≅A.to ∘ s
        cohere-s = begin
            φ[⊥,N] ∘ ε ⊗₁ s ∘ ρ⇐                                            ≈⟨ identityˡ ⟨
            id ∘ φ[⊥,N] ∘ ε ⊗₁ s ∘ ρ⇐                                       ≈⟨ F-identity ⟩∘⟨refl ⟨
            F₁ id′ ∘ φ[⊥,N] ∘ ε ⊗₁ s ∘ ρ⇐                                   ≈⟨ F-resp-≈ ⊥+A≅A.isoˡ ⟩∘⟨refl ⟨
            F₁ (⊥+A≅A.to ∘′ ⊥+A≅A.from) ∘ φ[⊥,N] ∘ ε ⊗₁ s ∘ ρ⇐              ≈⟨ pushˡ homomorphism ⟩
            F₁ ⊥+A≅A.to ∘ F₁ ⊥+A≅A.from ∘ φ[⊥,N] ∘ ε ⊗₁ s ∘ ρ⇐              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ serialize₁₂ ⟩
            F₁ ⊥+A≅A.to ∘ F₁ ⊥+A≅A.from ∘ φ[⊥,N] ∘ ε ⊗₁ id ∘ id ⊗₁ s ∘ ρ⇐   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
            F₁ ⊥+A≅A.to ∘ F₁ ⊥+A≅A.from ∘ (φ[⊥,N] ∘ ε ⊗₁ id) ∘ id ⊗₁ s ∘ ρ⇐ ≈⟨ refl⟩∘⟨ pullˡ unitaryˡ ⟩
            F₁ ⊥+A≅A.to ∘ λ⇒ ∘ id ⊗₁ s ∘ ρ⇐                                 ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ λ₁≅ρ₁⇐ ⟨
            F₁ ⊥+A≅A.to ∘ λ⇒ ∘ id ⊗₁ s ∘ λ⇐                                 ≈⟨ refl⟩∘⟨ refl⟩∘⟨ 𝒟.unitorˡ-commute-to ⟨
            F₁ ⊥+A≅A.to ∘ λ⇒ ∘ λ⇐ ∘ s                                       ≈⟨ refl⟩∘⟨ cancelˡ 𝒟.unitorˡ.isoʳ ⟩
            F₁ ⊥+A≅A.to ∘ s                                                 ∎
        deco-id : F₁ ≅P.from ∘ F₁ [ i₁ , i₂ ] ∘ φ[A,N] ∘ (F₁ ¡ ∘ ε) ⊗₁ s ∘ ρ⇐ 𝒟.≈ s
        deco-id = begin
            F₁ ≅P.from ∘ F₁ [ i₁ , i₂ ] ∘ φ[A,N] ∘ (F₁ ¡ ∘ ε) ⊗₁ s ∘ ρ⇐             ≈⟨ pushˡ homomorphism ⟨
            F₁ (≅P.from ∘′ [ i₁ , i₂ ]) ∘ φ[A,N] ∘ (F₁ ¡ ∘ ε) ⊗₁ s ∘ ρ⇐             ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₁ˡ ⟩
            F₁ (≅P.from ∘′ [ i₁ , i₂ ]) ∘ φ[A,N] ∘ (F₁ ¡ ⊗₁ id) ∘ (ε ⊗₁ s) ∘ ρ⇐     ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ F-identity ⟩∘⟨refl ⟨
            F₁ (≅P.from ∘′ [ i₁ , i₂ ]) ∘ φ[A,N] ∘ (F₁ ¡ ⊗₁ F₁ id′) ∘ (ε ⊗₁ s) ∘ ρ⇐ ≈⟨ refl⟩∘⟨ extendʳ (⊗-homo.commute (¡ , id′)) ⟩
            F₁ (≅P.from ∘′ [ i₁ , i₂ ]) ∘ F₁ (¡ +₁ id′) ∘ φ[⊥,N] ∘ (ε ⊗₁ s) ∘ ρ⇐    ≈⟨ pushˡ homomorphism ⟨
            F₁ ((≅P.from ∘′ [ i₁ , i₂ ]) ∘′ (¡ +₁ id′)) ∘ φ[⊥,N] ∘ (ε ⊗₁ s) ∘ ρ⇐    ≈⟨ refl⟩∘⟨ cohere-s ⟩
            F₁ ((≅P.from ∘′ [ i₁ , i₂ ]) ∘′ (¡ +₁ id′)) ∘ F₁ ⊥+A≅A.to ∘ s           ≈⟨ pushˡ homomorphism ⟨
            F₁ (((≅P.from ∘′ [ i₁ , i₂ ]) ∘′ (¡ +₁ id′)) ∘′ ⊥+A≅A.to) ∘ s           ≈⟨ F-resp-≈ copairing-id ⟩∘⟨refl ⟩
            F₁ id′ ∘ s                                                              ≈⟨ F-identity ⟩∘⟨refl ⟩
            id ∘ s                                                                  ≈⟨ identityˡ ⟩
            s                                                                       ∎

compose-idˡ : {C : DecoratedCospan A B} → compose C identity ≈ C
compose-idˡ {_} {B} {C} = record
    { cospans-≈ = Cospans.compose-idˡ
    ; same-deco = deco-id
    }
  where

    open DecoratedCospan C

    open 𝒞 using (pushout; [_,_]; ⊥; _+₁_; ¡)

    P = pushout f₂ 𝒞.id
    P′ = pushout-f-id {f = f₂}
    ≅P = up-to-iso P P′

    open Morphism 𝒞.U using (_≅_)
    module ≅P = _≅_ ≅P

    open Pushout P

    open 𝒞
      using (cocartesian)
      renaming (id to id′; _∘_ to _∘′_)

    open CocartesianMonoidal cocartesian using (A+⊥≅A)

    module A+⊥≅A {a} = _≅_ (A+⊥≅A {a})

    module _ where

      open 𝒞
        using
          ( _⇒_ ; _∘_ ; _≈_ ; id ; U
          ; identity²
          ; cocartesian ; initial ; ¡-unique
          ; ∘[] ; []∘+₁ ; inject₁ ; assoc ; []-cong₂
          ; module HomReasoning ; module Equiv
          )

      open Equiv

      open ⇒-Reasoning U
      open HomReasoning

      copairing-id : ((≅P.from ∘ [ i₁ , i₂ ]) ∘ (id +₁ ¡)) ∘ A+⊥≅A.to 𝒞.≈ id
      copairing-id = begin
        ((≅P.from ∘ [ i₁ , i₂ ]) ∘ (id +₁ ¡)) ∘ A+⊥≅A.to        ≈⟨ assoc ⟩
        (≅P.from ∘ [ i₁ , i₂ ]) ∘ (id +₁ ¡) ∘ A+⊥≅A.to          ≈⟨ assoc ⟩
        ≅P.from ∘ [ i₁ , i₂ ] ∘ (id +₁ ¡) ∘ A+⊥≅A.to            ≈⟨ pullˡ ∘[] ⟩
        [ ≅P.from ∘ i₁ , ≅P.from ∘ i₂ ] ∘ (id +₁ ¡) ∘ A+⊥≅A.to  ≈⟨ pullˡ []∘+₁ ⟩
        [ (≅P.from ∘ i₁) ∘ id , (≅P.from ∘ i₂) ∘ ¡ ] ∘ A+⊥≅A.to ≈⟨ []-cong₂ (universal∘i₁≈h₁ ⟩∘⟨refl) (universal∘i₂≈h₂ ⟩∘⟨refl) ⟩∘⟨refl ⟩
        [ id ∘ id , f₂ ∘ ¡ ] ∘ A+⊥≅A.to                         ≈⟨ []-cong₂ identity² (sym (¡-unique (f₂ ∘ ¡))) ⟩∘⟨refl ⟩
        [ id , ¡ ] ∘ A+⊥≅A.to                                   ≈⟨ inject₁ ⟩
        id                                                      ∎

    module _ where

      open 𝒞 using (_+_)
      open 𝒟
        using
          ( id ; _∘_ ; _≈_ ; _⇒_ ; U
          ; assoc ; sym-assoc; identityˡ
          ; monoidal ; _⊗₀_; _⊗₁_ ; unit ; unitorˡ ; unitorʳ
          ; unitorʳ-commute-to
          ; module Equiv
          )

      open Equiv
      open ⊗-Reasoning monoidal
      open ⇒-Reasoning U

      φ[N,⊥] : F₀ N ⊗₀ F₀ ⊥ 𝒟.⇒ F₀ (N + ⊥)
      φ[N,⊥] = ⊗-homo.η (N , ⊥)

      φ[N,B] : F₀ N ⊗₀ F₀ B 𝒟.⇒ F₀ (N + B)
      φ[N,B] = ⊗-homo.η (N , B)

      s : unit ⇒ F₀ N
      s = decoration

      open ⊗-Util 𝒟.monoidal using (module Shorthands)
      open Shorthands using (α⇒; α⇐; λ⇒; λ⇐; ρ⇒; ρ⇐)

      abstract
        cohere-s : φ[N,⊥] ∘ s ⊗₁ ε ∘ ρ⇐ 𝒟.≈ F₁ A+⊥≅A.to ∘ s
        cohere-s = begin
            φ[N,⊥] ∘ s ⊗₁ ε ∘ ρ⇐                                            ≈⟨ identityˡ ⟨
            id ∘ φ[N,⊥] ∘ s ⊗₁ ε ∘ ρ⇐                                       ≈⟨ F-identity ⟩∘⟨refl ⟨
            F₁ id′ ∘ φ[N,⊥] ∘ (s ⊗₁ ε) ∘ ρ⇐                                 ≈⟨ F-resp-≈ A+⊥≅A.isoˡ ⟩∘⟨refl ⟨
            F₁ (A+⊥≅A.to ∘′ A+⊥≅A.from) ∘ φ[N,⊥] ∘ s ⊗₁ ε ∘ ρ⇐              ≈⟨ pushˡ homomorphism ⟩
            F₁ A+⊥≅A.to ∘ F₁ A+⊥≅A.from ∘ φ[N,⊥] ∘ s ⊗₁ ε ∘ ρ⇐              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ serialize₂₁ ⟩
            F₁ A+⊥≅A.to ∘ F₁ A+⊥≅A.from ∘ φ[N,⊥] ∘ id ⊗₁ ε ∘ s ⊗₁ id ∘ ρ⇐   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
            F₁ A+⊥≅A.to ∘ F₁ A+⊥≅A.from ∘ (φ[N,⊥] ∘ id ⊗₁ ε) ∘ s ⊗₁ id ∘ ρ⇐ ≈⟨ refl⟩∘⟨ pullˡ unitaryʳ ⟩
            F₁ A+⊥≅A.to ∘ ρ⇒ ∘ s ⊗₁ id ∘ ρ⇐                                 ≈⟨ refl⟩∘⟨ refl⟩∘⟨ unitorʳ-commute-to ⟨
            F₁ A+⊥≅A.to ∘ ρ⇒ ∘ ρ⇐ ∘ s                                       ≈⟨ refl⟩∘⟨ cancelˡ unitorʳ.isoʳ ⟩
            F₁ A+⊥≅A.to ∘ s                                                 ∎

        deco-id : F₁ ≅P.from ∘ F₁ [ i₁ , i₂ ] ∘ φ[N,B] ∘ s ⊗₁ (F₁ ¡ ∘ ε) ∘ ρ⇐ 𝒟.≈ s
        deco-id = begin
            F₁ ≅P.from ∘ F₁ [ i₁ , i₂ ] ∘ φ[N,B] ∘ s ⊗₁ (F₁ ¡ ∘ ε) ∘ ρ⇐         ≈⟨ pushˡ homomorphism ⟨
            F₁ (≅P.from ∘′ [ i₁ , i₂ ]) ∘ φ[N,B] ∘ s ⊗₁ (F₁ ¡ ∘ ε) ∘ ρ⇐         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
            F₁ (≅P.from ∘′ [ i₁ , i₂ ]) ∘ φ[N,B] ∘ id ⊗₁ F₁ ¡ ∘ s ⊗₁ ε ∘ ρ⇐     ≈⟨ refl⟩∘⟨ refl⟩∘⟨ F-identity ⟩⊗⟨refl ⟩∘⟨refl ⟨
            F₁ (≅P.from ∘′ [ i₁ , i₂ ]) ∘ φ[N,B] ∘ F₁ id′ ⊗₁ F₁ ¡ ∘ s ⊗₁ ε ∘ ρ⇐ ≈⟨ refl⟩∘⟨ extendʳ (⊗-homo.commute (id′ , ¡)) ⟩
            F₁ (≅P.from ∘′ [ i₁ , i₂ ]) ∘ F₁ (id′ +₁ ¡) ∘ φ[N,⊥] ∘ s ⊗₁ ε ∘ ρ⇐  ≈⟨ pushˡ homomorphism ⟨
            F₁ ((≅P.from ∘′ [ i₁ , i₂ ]) ∘′ (id′ +₁ ¡)) ∘ φ[N,⊥] ∘ s ⊗₁ ε ∘ ρ⇐  ≈⟨ refl⟩∘⟨ cohere-s ⟩
            F₁ ((≅P.from ∘′ [ i₁ , i₂ ]) ∘′ (id′ +₁ ¡)) ∘ F₁ A+⊥≅A.to ∘ s       ≈⟨ pushˡ homomorphism ⟨
            F₁ (((≅P.from ∘′ [ i₁ , i₂ ]) ∘′ (id′ +₁ ¡)) ∘′ A+⊥≅A.to) ∘ s       ≈⟨ F-resp-≈ copairing-id ⟩∘⟨refl ⟩
            F₁ id′ ∘ s                                                          ≈⟨ F-identity ⟩∘⟨refl ⟩
            id ∘ s                                                              ≈⟨ identityˡ ⟩
            s                                                                   ∎

compose-id² : compose identity identity ≈ identity {A}
compose-id² = compose-idˡ

compose-equiv
    : {c₂ c₂′ : DecoratedCospan B C}
      {c₁ c₁′ : DecoratedCospan A B}
    → c₂ ≈ c₂′
    → c₁ ≈ c₁′
    → compose c₁ c₂ ≈ (compose c₁′ c₂′)
compose-equiv {_} {_} {_} {c₂} {c₂′} {c₁} {c₁′} ≅C₂ ≅C₁ = record
    { cospans-≈ = ≅C₂∘C₁
    ; same-deco = F≅N∘C₂∘C₁≈C₂′∘C₁′
    }
  where
    module ≅C₁ = _≈_ ≅C₁
    module ≅C₂ = _≈_ ≅C₂
    module C₁ = DecoratedCospan c₁
    module C₁′ = DecoratedCospan c₁′
    module C₂ = DecoratedCospan c₂
    module C₂′ = DecoratedCospan c₂′
    ≅C₂∘C₁ = Cospans.compose-equiv ≅C₂.cospans-≈ ≅C₁.cospans-≈
    module ≅C₂∘C₁ = Cospan._≈_ ≅C₂∘C₁
    P = 𝒞.pushout C₁.f₂ C₂.f₁
    P′ = 𝒞.pushout C₁′.f₂ C₂′.f₁
    module P = Pushout P
    module P′ = Pushout P′

    N M N′ M′ : 𝒞.Obj
    N = C₁.N
    M = C₂.N
    N′ = C₁′.N
    M′ = C₂′.N

    s : 𝒟.unit 𝒟.⇒ F₀ N
    s = C₁.decoration

    t : 𝒟.unit 𝒟.⇒ F₀ M
    t = C₂.decoration

    s′ : 𝒟.unit 𝒟.⇒ F₀ N′
    s′ = C₁′.decoration

    t′ : 𝒟.unit 𝒟.⇒ F₀ M′
    t′ = C₂′.decoration

    Q⇒ : ≅C₂∘C₁.C.N 𝒞.⇒ ≅C₂∘C₁.D.N
    Q⇒ = ≅C₂∘C₁.≅N.from

    N⇒ : ≅C₁.C.N 𝒞.⇒ ≅C₁.D.N
    N⇒ = ≅C₁.≅N.from

    M⇒ : ≅C₂.C.N 𝒞.⇒ ≅C₂.D.N
    M⇒ = ≅C₂.≅N.from

    module _ where

      open ⊗-Util 𝒟.monoidal using (module Shorthands)
      open Shorthands using (ρ⇒; ρ⇐)

      open 𝒞 using ([_,_]; ∘[]; _+_; _+₁_; []∘+₁; []-cong₂) renaming (_∘_ to _∘′_)
      open 𝒟

      φ[N,M] : F₀ N ⊗₀ F₀ M 𝒟.⇒ F₀ (N + M)
      φ[N,M] = ⊗-homo.η (N , M)

      φ[N′,M′] : F₀ N′ ⊗₀ F₀ M′ 𝒟.⇒ F₀ (N′ + M′)
      φ[N′,M′] = ⊗-homo.η (N′ , M′)

      open ⊗-Reasoning monoidal
      open ⇒-Reasoning U

      abstract
        F≅N∘C₂∘C₁≈C₂′∘C₁′ : F₁ Q⇒ ∘ F₁ [ P.i₁ , P.i₂ ] ∘ φ[N,M] ∘ s ⊗₁ t ∘ ρ⇐ 𝒟.≈ F₁ [ P′.i₁ , P′.i₂ ] ∘ φ[N′,M′] ∘ s′ ⊗₁ t′ ∘ ρ⇐
        F≅N∘C₂∘C₁≈C₂′∘C₁′ = begin
            F₁ Q⇒ ∘ F₁ [ P.i₁ , P.i₂ ] ∘ φ[N,M] ∘ s ⊗₁ t ∘ ρ⇐                  ≈⟨ pushˡ homomorphism ⟨
            F₁ (Q⇒ ∘′ [ P.i₁ , P.i₂ ]) ∘ φ[N,M] ∘ s ⊗₁ t ∘ ρ⇐                  ≈⟨ F-resp-≈ ∘[] ⟩∘⟨refl ⟩
            F₁ ([ Q⇒ ∘′ P.i₁ , Q⇒ ∘′ P.i₂ ]) ∘ φ[N,M] ∘ s ⊗₁ t ∘ ρ⇐            ≈⟨ F-resp-≈ ([]-cong₂ P.universal∘i₁≈h₁ P.universal∘i₂≈h₂) ⟩∘⟨refl ⟩
            F₁ ([ P′.i₁ ∘′ N⇒ , P′.i₂ ∘′ M⇒ ]) ∘ φ[N,M] ∘ s ⊗₁ t ∘ ρ⇐          ≈⟨ F-resp-≈ []∘+₁ ⟩∘⟨refl ⟨
            F₁ ([ P′.i₁ , P′.i₂ ] ∘′ (N⇒ +₁ M⇒)) ∘ φ[N,M] ∘ s ⊗₁ t ∘ ρ⇐        ≈⟨ pushˡ homomorphism ⟩
            F₁ [ P′.i₁ , P′.i₂ ] ∘ F₁ (N⇒ +₁ M⇒) ∘ φ[N,M] ∘ s ⊗₁ t ∘ ρ⇐        ≈⟨ refl⟩∘⟨ extendʳ (⊗-homo.commute (N⇒ , M⇒)) ⟨
            F₁ [ P′.i₁ , P′.i₂ ] ∘ φ[N′,M′] ∘ F₁ N⇒ ⊗₁ F₁ M⇒ ∘ s ⊗₁ t ∘ ρ⇐     ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ ⊗-distrib-over-∘ ⟨
            F₁ [ P′.i₁ , P′.i₂ ] ∘ φ[N′,M′] ∘ (F₁ N⇒ ∘ s) ⊗₁ (F₁ M⇒ ∘ t) ∘ ρ⇐  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ≅C₁.same-deco ⟩⊗⟨ ≅C₂.same-deco ⟩∘⟨refl ⟩
            F₁ [ P′.i₁ , P′.i₂ ] ∘ φ[N′,M′] ∘ s′ ⊗₁ t′ ∘ ρ⇐                    ∎

DecoratedCospans : Category o (o ⊔ ℓ ⊔ ℓ′) (ℓ ⊔ e ⊔ e′)
DecoratedCospans = record
    { Obj = 𝒞.Obj
    ; _⇒_ = DecoratedCospan
    ; _≈_ = _≈_
    ; id = identity
    ; _∘_ = flip compose
    ; assoc = compose-assoc
    ; sym-assoc = ≈-sym compose-assoc
    ; identityˡ = compose-idˡ
    ; identityʳ = compose-idʳ
    ; identity² = compose-id²
    ; equiv = ≈-equiv
    ; ∘-resp-≈ = compose-equiv
    }
