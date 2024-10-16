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

import Category.Instance.Cospans 𝒞 as Cospans

open import Categories.Category using (Category; _[_∘_])
open import Categories.Category.Cocartesian using (module CocartesianMonoidal)
open import Categories.Diagram.Pushout using (Pushout)
open import Categories.Functor.Properties using ([_]-resp-≅)
open import Categories.Morphism.Reasoning using (switch-fromtoˡ; glueTrianglesˡ)
open import Cospan.Decorated 𝒞 F using (DecoratedCospan)
open import Data.Product using (_,_)
open import Function using (flip)
open import Level using (_⊔_)

open import Category.Diagram.Pushout 𝒞.U using (glue-i₁; glue-i₂; pushout-id-g; pushout-f-id; up-to-iso)

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
    { cospan = Cospans.compose C₁.cospan C₂.cospan
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
    { cospan = Cospans.identity
    ; decoration = 𝒟.U [ F₁ 𝒞.initial.! ∘ ε ]
    }

record Same (C₁ C₂ : DecoratedCospan A B) : Set (ℓ ⊔ e ⊔ e′) where

  module C₁ = DecoratedCospan C₁
  module C₂ = DecoratedCospan C₂

  field
    cospans-≈ : Cospans.Same C₁.cospan C₂.cospan

  open Cospans.Same cospans-≈ public
  open 𝒟
  open Morphism U using (_≅_)

  field
    same-deco : F₁ ≅N.from ∘ C₁.decoration ≈ C₂.decoration

  ≅F[N] : F₀ C₁.N ≅ F₀ C₂.N
  ≅F[N] = [ F′ ]-resp-≅ ≅N

same-refl : {C : DecoratedCospan A B} → Same C C
same-refl = record
    { cospans-≈ = Cospans.same-refl
    ; same-deco = F-identity ⟩∘⟨refl ○ identityˡ
    }
  where
    open 𝒟
    open HomReasoning

same-sym : {C C′ : DecoratedCospan A B} → Same C C′ → Same C′ C
same-sym C≅C′ = record
    { cospans-≈ = Cospans.same-sym cospans-≈
    ; same-deco = sym (switch-fromtoˡ 𝒟.U ≅F[N] same-deco)
    }
  where
    open Same C≅C′
    open 𝒟.Equiv

same-trans : {C C′ C″ : DecoratedCospan A B} → Same C C′ → Same C′ C″ → Same C C″
same-trans C≈C′ C′≈C″ = record
    { cospans-≈ = Cospans.same-trans C≈C′.cospans-≈ C′≈C″.cospans-≈
    ; same-deco =
          homomorphism ⟩∘⟨refl ○
          glueTrianglesˡ 𝒟.U C′≈C″.same-deco C≈C′.same-deco
    }
  where
    module C≈C′ = Same C≈C′
    module C′≈C″ = Same C′≈C″
    open 𝒟.HomReasoning

compose-assoc
    : {c₁ : DecoratedCospan A B}
      {c₂ : DecoratedCospan B C}
      {c₃ : DecoratedCospan C D}
    → Same (compose c₁ (compose c₂ c₃)) (compose (compose c₁ c₂) c₃)
compose-assoc {_} {_} {_} {_} {c₁} {c₂} {c₃} = record
    { cospans-≈ = Cospans.compose-assoc
    ; same-deco = deco-assoc
    }
  where
    module C₁ = DecoratedCospan c₁
    module C₂ = DecoratedCospan c₂
    module C₃ = DecoratedCospan c₃
    open 𝒞 using (+-assoc; pushout; [_,_]; _+₁_; _+_) renaming (_∘_ to _∘′_; id to id′)
    p₁ = pushout C₁.f₂ C₂.f₁
    p₂ = pushout C₂.f₂ C₃.f₁
    module P₁ = Pushout p₁
    module P₂ = Pushout p₂
    p₃ = pushout P₁.i₂ P₂.i₁
    p₁₃ = glue-i₂ p₁ p₃
    p₂₃ = glue-i₁ p₂ p₃
    p₄ = pushout C₁.f₂ (P₂.i₁ ∘′ C₂.f₁)
    p₅ = pushout (P₁.i₂ ∘′ C₂.f₂) C₃.f₁
    module P₃ = Pushout p₃
    module P₄ = Pushout p₄
    module P₅ = Pushout p₅
    module P₁₃ = Pushout p₁₃
    module P₂₃ = Pushout p₂₃
    open Morphism 𝒞.U using (_≅_)
    module P₄≅P₁₃ = _≅_ (up-to-iso p₄ p₁₃)
    module P₅≅P₂₃ = _≅_ (up-to-iso p₅ p₂₃)

    N = C₁.N
    M = C₂.N
    P = C₃.N
    Q = P₁.Q
    R = P₂.Q
    φ = ⊗-homo.η
    φ-commute = ⊗-homo.commute

    a = C₁.f₂
    b = C₂.f₁
    c = C₂.f₂
    d = C₂.f₁

    f = P₁.i₁
    g = P₁.i₂
    h = P₂.i₁
    i = P₂.i₂

    j = P₃.i₁
    k = P₃.i₂

    w = P₄.i₁
    x = P₄.i₂
    y = P₅.i₁
    z = P₅.i₂

    l = P₅≅P₂₃.to
    m = P₄≅P₁₃.from

    module +-assoc = _≅_ +-assoc

    module _ where

      open 𝒞 using (∘[]; []-congʳ; []-congˡ; []∘+₁)
      open 𝒞.Dual.op-binaryProducts 𝒞.cocartesian
          using ()
          renaming (⟨⟩-cong₂ to []-cong₂; assocˡ∘⟨⟩ to []∘assocˡ)

      open ⇒-Reasoning 𝒞.U
      open 𝒞 using (id; _∘_; _≈_; assoc; identityʳ)
      open 𝒞.HomReasoning
      open 𝒞.Equiv

      copairings : ((l ∘ m) ∘ [ w , x ]) ∘ (id +₁ [ h , i ]) ≈ [ y , z ] ∘ ([ f , g ] +₁ id) ∘ +-assoc.from
      copairings = begin
          ((l ∘ m) ∘ [ w , x ]) ∘ (id +₁ [ h , i ])     ≈⟨ pushˡ assoc ⟩
          l ∘ (m ∘ [ w , x ]) ∘ (id +₁ [ h , i ])       ≈⟨ refl⟩∘⟨ ∘[] ⟩∘⟨refl ⟩
          l ∘ [ m ∘ w , m ∘ x ] ∘ (id +₁ [ h , i ])     ≈⟨ refl⟩∘⟨ []-cong₂ (P₄.universal∘i₁≈h₁) (P₄.universal∘i₂≈h₂) ⟩∘⟨refl ⟩
          l ∘ [ j ∘ f , k ] ∘ (id +₁ [ h , i ])         ≈⟨ pullˡ ∘[] ⟩
          [ l ∘ j ∘ f , l ∘ k ] ∘ (id +₁ [ h , i ])     ≈⟨ []-congʳ (pullˡ P₂₃.universal∘i₁≈h₁) ⟩∘⟨refl ⟩
          [ y ∘ f , l ∘ k ] ∘ (id +₁ [ h , i ])         ≈⟨ []∘+₁ ⟩
          [ (y ∘ f) ∘ id , (l ∘ k) ∘ [ h , i ] ]        ≈⟨ []-cong₂ identityʳ (pullʳ ∘[]) ⟩
          [ y ∘ f , l ∘ [ k ∘ h , k ∘ i ] ]             ≈⟨ []-congˡ (refl⟩∘⟨ []-congʳ P₃.commute) ⟨
          [ y ∘ f , l ∘ [ j ∘ g , k ∘ i ] ]             ≈⟨ []-congˡ ∘[] ⟩
          [ y ∘ f , [ l ∘ j ∘ g , l ∘ k ∘ i ] ]         ≈⟨ []-congˡ ([]-congˡ P₂₃.universal∘i₂≈h₂) ⟩
          [ y ∘ f , [ l ∘ j ∘ g , z ] ]                 ≈⟨ []-congˡ ([]-congʳ (pullˡ P₂₃.universal∘i₁≈h₁)) ⟩
          [ y ∘ f , [ y ∘ g , z ] ]                     ≈⟨ []∘assocˡ ⟨
          [ [ y ∘ f , y ∘ g ] , z ] ∘ +-assoc.from      ≈⟨ []-cong₂ ∘[] identityʳ ⟩∘⟨refl ⟨
          [ y ∘ [ f ,  g ] , z ∘ id ] ∘ +-assoc.from    ≈⟨ pullˡ []∘+₁ ⟨
          [ y , z ] ∘ ([ f , g ] +₁ id) ∘ +-assoc.from  ∎

    module _ where

      open ⊗-Reasoning 𝒟.monoidal
      open ⇒-Reasoning 𝒟.U
      open 𝒟 using (_⊗₀_; _⊗₁_; id; _∘_; _≈_; assoc; sym-assoc; identityʳ; ⊗; identityˡ; triangle; assoc-commute-to; assoc-commute-from)
      open 𝒟 using (_⇒_; unit)

      α⇒ = 𝒟.associator.from
      α⇐ = 𝒟.associator.to

      λ⇒ = 𝒟.unitorˡ.from
      λ⇐ = 𝒟.unitorˡ.to

      ρ⇒ = 𝒟.unitorʳ.from
      ρ⇐ = 𝒟.unitorʳ.to

      module α≅ = 𝒟.associator
      module λ≅ = 𝒟.unitorˡ
      module ρ≅ = 𝒟.unitorʳ

      open Coherence 𝒟.monoidal using (λ₁≅ρ₁⇐)
      open 𝒟.Equiv

      +-α⇒ = +-assoc.from
      +-α⇐ = +-assoc.to

      s : unit ⇒ F₀ C₁.N
      s = C₁.decoration

      t : unit ⇒ F₀ C₂.N
      t = C₂.decoration

      u : unit ⇒ F₀ C₃.N
      u = C₃.decoration

      F-copairings : F₁ (l ∘′ m) ∘ F₁ [ w , x ] ∘ F₁ (id′ +₁ [ h , i ]) ≈ F₁ [ y , z ] ∘ F₁ ([ f , g ] +₁ id′) ∘ F₁ (+-assoc.from)
      F-copairings = begin
          F₁ (l ∘′ m) ∘ F₁ [ w , x ] ∘ F₁ (id′ +₁ [ h , i ])      ≈⟨ pushˡ homomorphism ⟨
          F₁ ((l ∘′ m) ∘′ [ w , x ]) ∘ F₁ (id′ +₁ [ h , i ])      ≈⟨ homomorphism ⟨
          F₁ (((l ∘′ m) ∘′ [ w , x ]) ∘′ (id′ +₁ [ h , i ]))      ≈⟨ F-resp-≈ copairings ⟩
          F₁ ([ y , z ] ∘′ ([ f , g ] +₁ id′) ∘′ +-assoc.from)     ≈⟨ homomorphism ⟩
          F₁ [ y , z ] ∘ F₁ (([ f , g ] +₁ id′) ∘′ +-assoc.from)  ≈⟨ refl⟩∘⟨ homomorphism ⟩
          F₁ [ y , z ] ∘ F₁ ([ f , g ] +₁ id′) ∘ F₁ +-assoc.from  ∎

      coherences : φ (N , M + P) ∘ id ⊗₁ φ (M , P) ≈ F₁ +-assoc.to ∘ φ (N + M , P) ∘ φ (N , M) ⊗₁ id ∘ α⇐
      coherences = begin
          φ (N , M + P) ∘ id ⊗₁ φ (M , P)                         ≈⟨ insertʳ α≅.isoʳ ⟩
          ((φ (N , M + P) ∘ id ⊗₁ φ (M , P)) ∘ α⇒) ∘ α⇐           ≈⟨ assoc ⟩∘⟨refl ⟩
          (φ (N , M + P) ∘ id ⊗₁ φ (M , P) ∘ α⇒) ∘ α⇐             ≈⟨ assoc ⟩
          φ (N , M + P) ∘ (id ⊗₁ φ (M , P) ∘ α⇒) ∘ α⇐             ≈⟨ extendʳ associativity ⟨
          F₁ +-assoc.to ∘ (φ (N + M , P) ∘ φ (N , M) ⊗₁ id) ∘ α⇐  ≈⟨ refl⟩∘⟨ assoc ⟩
          F₁ +-assoc.to ∘ φ (N + M , P) ∘ φ (N , M) ⊗₁ id ∘ α⇐    ∎

      triangle-to : α⇒ ∘ ρ⇐ ⊗₁ id ≈ id ⊗₁ λ⇐
      triangle-to = begin
          α⇒ ∘ ρ⇐ ⊗₁ id                          ≈⟨ pullˡ identityˡ ⟨
          id ∘ α⇒ ∘ ρ⇐ ⊗₁ id                     ≈⟨ ⊗.identity ⟩∘⟨refl ⟨
          id ⊗₁ id ∘ α⇒ ∘ ρ⇐ ⊗₁ id               ≈⟨ refl⟩⊗⟨ λ≅.isoˡ ⟩∘⟨refl ⟨
          id ⊗₁ (λ⇐ ∘ λ⇒) ∘ α⇒ ∘ ρ⇐ ⊗₁ id        ≈⟨ identityʳ ⟩⊗⟨refl ⟩∘⟨refl ⟨
          (id ∘ id) ⊗₁ (λ⇐ ∘ λ⇒) ∘ α⇒ ∘ ρ⇐ ⊗₁ id ≈⟨ pushˡ ⊗-distrib-over-∘ ⟩
          id ⊗₁ λ⇐ ∘ id ⊗₁ λ⇒ ∘ α⇒ ∘ ρ⇐ ⊗₁ id    ≈⟨ refl⟩∘⟨ pullˡ triangle ⟩
          id ⊗₁ λ⇐ ∘ ρ⇒ ⊗₁ id ∘ ρ⇐ ⊗₁ id         ≈⟨ refl⟩∘⟨ ⊗-distrib-over-∘ ⟨
          id ⊗₁ λ⇐ ∘ (ρ⇒ ∘ ρ⇐) ⊗₁ (id ∘ id)      ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ identityˡ ⟩
          id ⊗₁ λ⇐ ∘ (ρ⇒ ∘ ρ⇐) ⊗₁ id             ≈⟨ refl⟩∘⟨ ρ≅.isoʳ ⟩⊗⟨refl ⟩
          id ⊗₁ λ⇐ ∘ id ⊗₁ id                    ≈⟨ refl⟩∘⟨ ⊗.identity ⟩
          id ⊗₁ λ⇐ ∘ id                          ≈⟨ identityʳ ⟩
          id ⊗₁ λ⇐                               ∎

      unitors : s ⊗₁ (t ⊗₁ u ∘ ρ⇐) ∘ ρ⇐ ≈ α⇒ ∘ (s ⊗₁ t ∘ ρ⇐) ⊗₁ u ∘ ρ⇐
      unitors = begin
          s ⊗₁ (t ⊗₁ u ∘ ρ⇐) ∘ ρ⇐               ≈⟨ pushˡ split₂ʳ ⟩
          s ⊗₁ t ⊗₁ u ∘ id ⊗₁ ρ⇐ ∘ ρ⇐           ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ λ₁≅ρ₁⇐ ⟩∘⟨refl ⟨
          s ⊗₁ t ⊗₁ u ∘ id ⊗₁ λ⇐ ∘ ρ⇐           ≈⟨ refl⟩∘⟨ pullˡ triangle-to ⟨
          s ⊗₁ t ⊗₁ u ∘ α⇒ ∘ ρ⇐ ⊗₁ id ∘ ρ⇐      ≈⟨ extendʳ assoc-commute-from ⟨
          α⇒ ∘ (s ⊗₁ t) ⊗₁ u ∘ ρ⇐ ⊗₁ id ∘ ρ⇐    ≈⟨ refl⟩∘⟨ pushˡ split₁ʳ ⟨
          α⇒ ∘ (s ⊗₁ t ∘ ρ⇐) ⊗₁ u ∘ ρ⇐          ∎

      F-l∘m = F₁ (l ∘′ m)
      F[w,x] = F₁ [ w , x ]
      F[h,i] = F₁ [ h , i ]
      F[y,z] = F₁ [ y , z ]
      F[f,g] = F₁ [ f , g ]
      F-[f,g]+id = F₁ ([ f , g ] +₁ id′)
      F-id+[h,i] = F₁ (id′ +₁ [ h , i ])
      φ-N,R = φ (N , R)
      φ-M,P = φ (M , P)
      φ-N+M,P = φ (N + M , P)
      φ-N+M = φ (N , M)
      φ-N,M+P = φ (N , M + P)
      φ-N,M = φ (N , M)
      φ-Q,P = φ (Q , P)
      s⊗[t⊗u] = s ⊗₁ (t ⊗₁ u ∘ ρ⇐) ∘ ρ⇐
      [s⊗t]⊗u = (s ⊗₁ t ∘ ρ⇐) ⊗₁ u ∘ ρ⇐

      deco-assoc
          : F-l∘m ∘ F[w,x] ∘ φ-N,R ∘ s ⊗₁ (F[h,i] ∘ φ-M,P ∘ t ⊗₁ u ∘ ρ⇐) ∘ ρ⇐
          ≈ F[y,z] ∘ φ-Q,P ∘ (F[f,g] ∘ φ-N,M ∘ s ⊗₁ t ∘ ρ⇐) ⊗₁ u ∘ ρ⇐
      deco-assoc = begin
          F-l∘m ∘ F[w,x] ∘ φ-N,R ∘ s ⊗₁ (F[h,i] ∘ φ-M,P ∘ t ⊗₁ u ∘ ρ⇐) ∘ ρ⇐                           ≈⟨ pullˡ refl ⟩
          (F-l∘m ∘ F[w,x]) ∘ φ-N,R ∘ s ⊗₁ (F[h,i] ∘ φ-M,P ∘ t ⊗₁ u ∘ ρ⇐) ∘ ρ⇐                         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₂ˡ ⟩∘⟨refl ⟩
          (F-l∘m ∘ F[w,x]) ∘ φ-N,R ∘ (id ⊗₁ F[h,i] ∘ s ⊗₁ (φ-M,P ∘ t ⊗₁ u ∘ ρ⇐)) ∘ ρ⇐                 ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩∘⟨ split₂ˡ) ⟩∘⟨refl ⟩
          (F-l∘m ∘ F[w,x]) ∘ φ-N,R ∘ (id ⊗₁ F[h,i] ∘ id ⊗₁ φ-M,P ∘ s ⊗₁ (t ⊗₁ u ∘ ρ⇐)) ∘ ρ⇐           ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc    ⟩
          (F-l∘m ∘ F[w,x]) ∘ φ-N,R ∘ id ⊗₁ F[h,i] ∘ (id ⊗₁ φ-M,P ∘ s ⊗₁ (t ⊗₁ u ∘ ρ⇐)) ∘ ρ⇐           ≈⟨ refl⟩∘⟨ refl⟩∘⟨ F-identity ⟩⊗⟨refl ⟩∘⟨ refl ⟨
          (F-l∘m ∘ F[w,x]) ∘ φ-N,R ∘ F₁ id′ ⊗₁ F[h,i] ∘ (id ⊗₁ φ-M,P ∘ s ⊗₁ (t ⊗₁ u ∘ ρ⇐)) ∘ ρ⇐       ≈⟨ refl⟩∘⟨ extendʳ (φ-commute (id′ , [ h  , i ])) ⟩
          (F-l∘m ∘ F[w,x]) ∘ F-id+[h,i] ∘ φ-N,M+P ∘ (id ⊗₁ φ-M,P ∘ s ⊗₁ (t ⊗₁ u ∘ ρ⇐)) ∘ ρ⇐           ≈⟨ pullˡ assoc ⟩
          (F-l∘m ∘ F[w,x] ∘ F-id+[h,i]) ∘ φ-N,M+P ∘ (id ⊗₁ φ-M,P ∘ s ⊗₁ (t ⊗₁ u ∘ ρ⇐)) ∘ ρ⇐           ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
          (F-l∘m ∘ F[w,x] ∘ F-id+[h,i]) ∘ φ-N,M+P ∘ id ⊗₁ φ-M,P ∘ s⊗[t⊗u]                             ≈⟨ refl⟩∘⟨ sym-assoc ⟩
          (F-l∘m ∘ F[w,x] ∘ F-id+[h,i]) ∘ (φ-N,M+P ∘ id ⊗₁ φ-M,P) ∘ s⊗[t⊗u]                           ≈⟨ F-copairings ⟩∘⟨ coherences ⟩∘⟨ unitors ⟩
          (F[y,z] ∘ F-[f,g]+id ∘ F₁ +-α⇒) ∘ (F₁ +-α⇐ ∘ φ-N+M,P ∘ φ-N,M ⊗₁ id ∘ α⇐) ∘ α⇒ ∘ [s⊗t]⊗u     ≈⟨ sym-assoc ⟩∘⟨ assoc ⟩
          ((F[y,z] ∘ F-[f,g]+id) ∘ F₁ +-α⇒) ∘ F₁ +-α⇐ ∘ (φ-N+M,P ∘ φ-N,M ⊗₁ id ∘ α⇐) ∘ α⇒ ∘ [s⊗t]⊗u   ≈⟨ assoc ⟩
          (F[y,z] ∘ F-[f,g]+id) ∘ F₁ +-α⇒ ∘ F₁ +-α⇐ ∘ (φ-N+M,P ∘ φ-N,M ⊗₁ id ∘ α⇐) ∘ α⇒ ∘ [s⊗t]⊗u     ≈⟨ refl⟩∘⟨ pushˡ homomorphism ⟨
          (F[y,z] ∘ F-[f,g]+id) ∘ F₁ (+-α⇒ ∘′ +-α⇐) ∘ (φ-N+M,P ∘ φ-N,M ⊗₁ id ∘ α⇐) ∘ α⇒ ∘ [s⊗t]⊗u     ≈⟨ refl⟩∘⟨ F-resp-≈ +-assoc.isoʳ ⟩∘⟨refl ⟩
          (F[y,z] ∘ F-[f,g]+id) ∘ F₁ id′ ∘ (φ-N+M,P ∘ φ-N,M ⊗₁ id ∘ α⇐) ∘ α⇒ ∘ [s⊗t]⊗u                ≈⟨ refl⟩∘⟨ F-identity ⟩∘⟨refl ⟩
          (F[y,z] ∘ F-[f,g]+id) ∘ id ∘ (φ-N+M,P ∘ φ-N,M ⊗₁ id ∘ α⇐) ∘ α⇒ ∘ [s⊗t]⊗u                    ≈⟨ refl⟩∘⟨ identityˡ ⟩
          (F[y,z] ∘ F-[f,g]+id) ∘ (φ-N+M,P ∘ φ-N,M ⊗₁ id ∘ α⇐) ∘ α⇒ ∘ [s⊗t]⊗u                         ≈⟨ refl⟩∘⟨ sym-assoc ⟩∘⟨refl ⟩
          (F[y,z] ∘ F-[f,g]+id) ∘ ((φ-N+M,P ∘ φ-N,M ⊗₁ id) ∘ α⇐) ∘ α⇒ ∘ [s⊗t]⊗u                       ≈⟨ refl⟩∘⟨ cancelInner α≅.isoˡ ⟩
          (F[y,z] ∘ F-[f,g]+id) ∘ (φ-N+M,P ∘ φ-N,M ⊗₁ id) ∘ [s⊗t]⊗u                                   ≈⟨ refl⟩∘⟨ assoc ⟩
          (F[y,z] ∘ F-[f,g]+id) ∘ φ-N+M,P ∘ φ-N,M ⊗₁ id ∘ [s⊗t]⊗u                                     ≈⟨ assoc ⟩
          F[y,z] ∘ F-[f,g]+id ∘ φ-N+M,P ∘ φ-N,M ⊗₁ id ∘ [s⊗t]⊗u                                       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₁ˡ ⟨
          F[y,z] ∘ F-[f,g]+id ∘ φ-N+M,P ∘ (φ-N,M ∘ s ⊗₁ t ∘ ρ⇐) ⊗₁ u ∘ ρ⇐                             ≈⟨ refl⟩∘⟨ extendʳ (φ-commute ([ f  , g ] , id′)) ⟨
          F[y,z] ∘ φ-Q,P ∘ F[f,g] ⊗₁ F₁ id′ ∘ (φ-N,M ∘ s ⊗₁ t ∘ ρ⇐) ⊗₁ u ∘ ρ⇐                         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ F-identity ⟩∘⟨ refl ⟩
          F[y,z] ∘ φ-Q,P ∘ F[f,g] ⊗₁ id ∘ (φ-N,M ∘ s ⊗₁ t ∘ ρ⇐) ⊗₁ u ∘ ρ⇐                             ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₁ˡ ⟨
          F[y,z] ∘ φ-Q,P ∘ (F[f,g] ∘ φ-N,M ∘ s ⊗₁ t ∘ ρ⇐) ⊗₁ u ∘ ρ⇐                                   ∎

compose-idʳ : {C : DecoratedCospan A B} → Same (compose identity C) C
compose-idʳ {A} {_} {C} = record
    { cospans-≈ = Cospans.compose-idʳ
    ; same-deco = deco-id
    }
  where

    open DecoratedCospan C

    open 𝒞 using (pushout; [_,_]; ⊥; _+₁_; ¡)

    P = pushout 𝒞.id f₁
    P′ = pushout-id-g {g = f₁}
    ≅P = up-to-iso P P′

    open Morphism 𝒞.U using (_≅_)
    module ≅P = _≅_ ≅P

    open Pushout P

    open 𝒞
      using (cocartesian)
      renaming (id to id′; _∘_ to _∘′_)

    open CocartesianMonoidal 𝒞.U cocartesian using (⊥+A≅A)

    module ⊥+A≅A {a} = _≅_ (⊥+A≅A {a})

    module _ where

      open 𝒞
        using
          ( _⇒_ ; _∘_ ; _≈_ ; id ; U
          ; identity²
          ; cocartesian ; initial ; ¡-unique
          ; ∘[] ; []∘+₁ ; inject₂ ; assoc
          ; module HomReasoning ; module Dual ; module Equiv
          )

      open Equiv

      open Dual.op-binaryProducts cocartesian
        using ()
        renaming (⟨⟩-cong₂ to []-cong₂)

      open ⇒-Reasoning U
      open HomReasoning

      copairing-id : ((≅P.from ∘ [ i₁ , i₂ ]) ∘ (¡ +₁ id)) ∘ ⊥+A≅A.to ≈ id
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
          ; monoidal ; _⊗₁_ ; unit ; unitorˡ ; unitorʳ
          )

      open ⊗-Reasoning monoidal
      open ⇒-Reasoning U

      φ = ⊗-homo.η
      φ-commute = ⊗-homo.commute

      module λ≅ = unitorˡ
      λ⇒ = λ≅.from
      λ⇐ = unitorˡ.to
      ρ⇐ = unitorʳ.to

      open Coherence monoidal using (λ₁≅ρ₁⇐)
      open 𝒟.Equiv

      s : unit ⇒ F₀ N
      s = decoration

      cohere-s : φ (⊥ , N) ∘ (ε ⊗₁ s) ∘ ρ⇐ ≈ F₁ ⊥+A≅A.to ∘ s
      cohere-s = begin
          φ (⊥ , N) ∘ (ε ⊗₁ s) ∘ ρ⇐                                               ≈⟨ identityˡ ⟨
          id ∘ φ (⊥ , N) ∘ (ε ⊗₁ s) ∘ ρ⇐                                          ≈⟨ F-identity ⟩∘⟨refl ⟨
          F₁ id′ ∘ φ (⊥ , N) ∘ (ε ⊗₁ s) ∘ ρ⇐                                      ≈⟨ F-resp-≈ ⊥+A≅A.isoˡ ⟩∘⟨refl ⟨
          F₁ (⊥+A≅A.to ∘′ ⊥+A≅A.from) ∘ φ (⊥ , N) ∘ (ε ⊗₁ s) ∘ ρ⇐                 ≈⟨ pushˡ homomorphism ⟩
          F₁ ⊥+A≅A.to ∘ F₁ ⊥+A≅A.from ∘ φ (⊥ , N) ∘ (ε ⊗₁ s) ∘ ρ⇐                 ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ serialize₁₂ ⟩
          F₁ ⊥+A≅A.to ∘ F₁ ⊥+A≅A.from ∘ φ (⊥ , N) ∘ (ε ⊗₁ id) ∘ (id ⊗₁ s) ∘ ρ⇐    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
          F₁ ⊥+A≅A.to ∘ F₁ ⊥+A≅A.from ∘ (φ (⊥ , N) ∘ (ε ⊗₁ id)) ∘ (id ⊗₁ s) ∘ ρ⇐  ≈⟨ refl⟩∘⟨ pullˡ unitaryˡ ⟩
          F₁ ⊥+A≅A.to ∘ λ⇒ ∘ (id ⊗₁ s) ∘ ρ⇐                                       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ λ₁≅ρ₁⇐ ⟨
          F₁ ⊥+A≅A.to ∘ λ⇒ ∘ (id ⊗₁ s) ∘ λ⇐                                       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ 𝒟.unitorˡ-commute-to ⟨
          F₁ ⊥+A≅A.to ∘ λ⇒ ∘ λ⇐ ∘ s                                               ≈⟨ refl⟩∘⟨ cancelˡ λ≅.isoʳ ⟩
          F₁ ⊥+A≅A.to ∘ s                                                         ∎

      deco-id : F₁ ≅P.from ∘ F₁ [ i₁ , i₂ ] ∘ φ (A , N) ∘ (F₁ ¡ ∘ ε) ⊗₁ s ∘ ρ⇐ ≈ s
      deco-id = begin
          F₁ ≅P.from ∘ F₁ [ i₁ , i₂ ] ∘ φ (A , N) ∘ (F₁ ¡ ∘ ε) ⊗₁ s ∘ ρ⇐             ≈⟨ pushˡ homomorphism ⟨
          F₁ (≅P.from ∘′ [ i₁ , i₂ ]) ∘ φ (A , N) ∘ (F₁ ¡ ∘ ε) ⊗₁ s ∘ ρ⇐             ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₁ˡ ⟩
          F₁ (≅P.from ∘′ [ i₁ , i₂ ]) ∘ φ (A , N) ∘ (F₁ ¡ ⊗₁ id) ∘ (ε ⊗₁ s) ∘ ρ⇐     ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ F-identity ⟩∘⟨refl ⟨
          F₁ (≅P.from ∘′ [ i₁ , i₂ ]) ∘ φ (A , N) ∘ (F₁ ¡ ⊗₁ F₁ id′) ∘ (ε ⊗₁ s) ∘ ρ⇐ ≈⟨ refl⟩∘⟨ extendʳ (φ-commute (¡ , id′)) ⟩
          F₁ (≅P.from ∘′ [ i₁ , i₂ ]) ∘ F₁ (¡ +₁ id′) ∘ φ (⊥ , N) ∘ (ε ⊗₁ s) ∘ ρ⇐    ≈⟨ pushˡ homomorphism ⟨
          F₁ ((≅P.from ∘′ [ i₁ , i₂ ]) ∘′ (¡ +₁ id′)) ∘ φ (⊥ , N) ∘ (ε ⊗₁ s) ∘ ρ⇐    ≈⟨ refl⟩∘⟨ cohere-s ⟩
          F₁ ((≅P.from ∘′ [ i₁ , i₂ ]) ∘′ (¡ +₁ id′)) ∘ F₁ ⊥+A≅A.to ∘ s              ≈⟨ pushˡ homomorphism ⟨
          F₁ (((≅P.from ∘′ [ i₁ , i₂ ]) ∘′ (¡ +₁ id′)) ∘′ ⊥+A≅A.to) ∘ s              ≈⟨ F-resp-≈ copairing-id ⟩∘⟨refl ⟩
          F₁ id′ ∘ s                                                                 ≈⟨ F-identity ⟩∘⟨refl ⟩
          id ∘ s                                                                     ≈⟨ identityˡ ⟩
          s                                                                          ∎

compose-idˡ : {C : DecoratedCospan A B} → Same (compose C identity) C
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

    open CocartesianMonoidal 𝒞.U cocartesian using (A+⊥≅A)

    module A+⊥≅A {a} = _≅_ (A+⊥≅A {a})

    module _ where

      open 𝒞
        using
          ( _⇒_ ; _∘_ ; _≈_ ; id ; U
          ; identity²
          ; cocartesian ; initial ; ¡-unique
          ; ∘[] ; []∘+₁ ; inject₁ ; assoc
          ; module HomReasoning ; module Dual ; module Equiv
          )

      open Equiv

      open Dual.op-binaryProducts cocartesian
        using ()
        renaming (⟨⟩-cong₂ to []-cong₂)

      open ⇒-Reasoning U
      open HomReasoning

      copairing-id : ((≅P.from ∘ [ i₁ , i₂ ]) ∘ (id +₁ ¡)) ∘ A+⊥≅A.to ≈ id
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

      open 𝒟
        using
          ( id ; _∘_ ; _≈_ ; _⇒_ ; U
          ; assoc ; sym-assoc; identityˡ
          ; monoidal ; _⊗₁_ ; unit ; unitorˡ ; unitorʳ
          ; unitorʳ-commute-to
          ; module Equiv
          )

      open Equiv
      open ⊗-Reasoning monoidal
      open ⇒-Reasoning U

      φ = ⊗-homo.η
      φ-commute = ⊗-homo.commute

      module ρ≅ = unitorʳ
      ρ⇒ = ρ≅.from
      ρ⇐ = ρ≅.to

      s : unit ⇒ F₀ N
      s = decoration

      cohere-s : φ (N , ⊥) ∘ (s ⊗₁ ε) ∘ ρ⇐ ≈ F₁ A+⊥≅A.to ∘ s
      cohere-s = begin
          φ (N , ⊥) ∘ (s ⊗₁ ε) ∘ ρ⇐                                               ≈⟨ identityˡ ⟨
          id ∘ φ (N , ⊥) ∘ (s ⊗₁ ε) ∘ ρ⇐                                          ≈⟨ F-identity ⟩∘⟨refl ⟨
          F₁ id′ ∘ φ (N , ⊥) ∘ (s ⊗₁ ε) ∘ ρ⇐                                      ≈⟨ F-resp-≈ A+⊥≅A.isoˡ ⟩∘⟨refl ⟨
          F₁ (A+⊥≅A.to ∘′ A+⊥≅A.from) ∘ φ (N , ⊥) ∘ (s ⊗₁ ε) ∘ ρ⇐                 ≈⟨ pushˡ homomorphism ⟩
          F₁ A+⊥≅A.to ∘ F₁ A+⊥≅A.from ∘ φ (N , ⊥) ∘ (s ⊗₁ ε) ∘ ρ⇐                 ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ serialize₂₁ ⟩
          F₁ A+⊥≅A.to ∘ F₁ A+⊥≅A.from ∘ φ (N , ⊥) ∘ (id ⊗₁ ε) ∘ (s ⊗₁ id) ∘ ρ⇐    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
          F₁ A+⊥≅A.to ∘ F₁ A+⊥≅A.from ∘ (φ (N , ⊥) ∘ (id ⊗₁ ε)) ∘ (s ⊗₁ id) ∘ ρ⇐  ≈⟨ refl⟩∘⟨ pullˡ unitaryʳ ⟩
          F₁ A+⊥≅A.to ∘ ρ⇒ ∘ (s ⊗₁ id) ∘ ρ⇐                                       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ unitorʳ-commute-to ⟨
          F₁ A+⊥≅A.to ∘ ρ⇒ ∘ ρ⇐ ∘ s                                               ≈⟨ refl⟩∘⟨ cancelˡ ρ≅.isoʳ ⟩
          F₁ A+⊥≅A.to ∘ s                                                         ∎

      deco-id : F₁ ≅P.from ∘ F₁ [ i₁ , i₂ ] ∘ φ (N , B) ∘ s ⊗₁ (F₁ ¡ ∘ ε) ∘ ρ⇐ ≈ s
      deco-id = begin
          F₁ ≅P.from ∘ F₁ [ i₁ , i₂ ] ∘ φ (N , B) ∘ s ⊗₁ (F₁ ¡ ∘ ε) ∘ ρ⇐             ≈⟨ pushˡ homomorphism ⟨
          F₁ (≅P.from ∘′ [ i₁ , i₂ ]) ∘ φ (N , B) ∘ s ⊗₁ (F₁ ¡ ∘ ε) ∘ ρ⇐             ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
          F₁ (≅P.from ∘′ [ i₁ , i₂ ]) ∘ φ (N , B) ∘ (id ⊗₁ F₁ ¡) ∘ (s ⊗₁ ε) ∘ ρ⇐     ≈⟨ refl⟩∘⟨ refl⟩∘⟨ F-identity ⟩⊗⟨refl ⟩∘⟨refl ⟨
          F₁ (≅P.from ∘′ [ i₁ , i₂ ]) ∘ φ (N , B) ∘ (F₁ id′ ⊗₁ F₁ ¡) ∘ (s ⊗₁ ε) ∘ ρ⇐ ≈⟨ refl⟩∘⟨ extendʳ (φ-commute (id′ , ¡)) ⟩
          F₁ (≅P.from ∘′ [ i₁ , i₂ ]) ∘ F₁ (id′ +₁ ¡) ∘ φ (N , ⊥) ∘ (s ⊗₁ ε) ∘ ρ⇐    ≈⟨ pushˡ homomorphism ⟨
          F₁ ((≅P.from ∘′ [ i₁ , i₂ ]) ∘′ (id′ +₁ ¡)) ∘ φ (N , ⊥) ∘ (s ⊗₁ ε) ∘ ρ⇐    ≈⟨ refl⟩∘⟨ cohere-s ⟩
          F₁ ((≅P.from ∘′ [ i₁ , i₂ ]) ∘′ (id′ +₁ ¡)) ∘ F₁ A+⊥≅A.to ∘ s              ≈⟨ pushˡ homomorphism ⟨
          F₁ (((≅P.from ∘′ [ i₁ , i₂ ]) ∘′ (id′ +₁ ¡)) ∘′ A+⊥≅A.to) ∘ s              ≈⟨ F-resp-≈ copairing-id ⟩∘⟨refl ⟩
          F₁ id′ ∘ s                                                                 ≈⟨ F-identity ⟩∘⟨refl ⟩
          id ∘ s                                                                     ≈⟨ identityˡ ⟩
          s                                                                          ∎

compose-id² : Same {A} (compose identity identity) identity
compose-id² = compose-idˡ

compose-equiv
    : {c₂ c₂′ : DecoratedCospan B C}
      {c₁ c₁′ : DecoratedCospan A B}
    → Same c₂ c₂′
    → Same c₁ c₁′
    → Same (compose c₁ c₂) (compose c₁′ c₂′)
compose-equiv {_} {_} {_} {c₂} {c₂′} {c₁} {c₁′} ≅C₂ ≅C₁ = record
    { cospans-≈ = ≅C₂∘C₁
    ; same-deco = F≅N∘C₂∘C₁≈C₂′∘C₁′
    }
  where
    module ≅C₁ = Same ≅C₁
    module ≅C₂ = Same ≅C₂
    module C₁ = DecoratedCospan c₁
    module C₁′ = DecoratedCospan c₁′
    module C₂ = DecoratedCospan c₂
    module C₂′ = DecoratedCospan c₂′
    ≅C₂∘C₁ = Cospans.compose-equiv ≅C₂.cospans-≈ ≅C₁.cospans-≈
    module ≅C₂∘C₁ = Cospans.Same ≅C₂∘C₁
    P = 𝒞.pushout C₁.f₂ C₂.f₁
    P′ = 𝒞.pushout C₁′.f₂ C₂′.f₁
    module P = Pushout P
    module P′ = Pushout P′

    s = C₁.decoration
    t = C₂.decoration
    s′ = C₁′.decoration
    t′ = C₂′.decoration
    N = C₁.N
    M = C₂.N
    N′ = C₁′.N
    M′ = C₂′.N

    φ = ⊗-homo.η
    φ-commute = ⊗-homo.commute

    Q⇒ = ≅C₂∘C₁.≅N.from
    N⇒ = ≅C₁.≅N.from
    M⇒ = ≅C₂.≅N.from

    module _ where

      ρ⇒ = 𝒟.unitorʳ.from
      ρ⇐ = 𝒟.unitorʳ.to

      open 𝒞 using ([_,_]; ∘[]; _+₁_; []∘+₁) renaming (_∘_ to _∘′_)
      open 𝒞.Dual.op-binaryProducts 𝒞.cocartesian
          using ()
          renaming (⟨⟩-cong₂ to []-cong₂)

      open 𝒟

      open ⊗-Reasoning monoidal
      open ⇒-Reasoning U

      F≅N∘C₂∘C₁≈C₂′∘C₁′ : F₁ Q⇒ ∘ F₁ [ P.i₁ , P.i₂ ] ∘ φ (N , M) ∘ s ⊗₁ t ∘ ρ⇐ ≈ F₁ [ P′.i₁ , P′.i₂ ] ∘ φ (N′ , M′) ∘ s′ ⊗₁ t′ ∘ ρ⇐
      F≅N∘C₂∘C₁≈C₂′∘C₁′ = begin
          F₁ Q⇒ ∘ F₁ [ P.i₁ , P.i₂ ] ∘ φ (N , M) ∘ s ⊗₁ t ∘ ρ⇐                  ≈⟨ pushˡ homomorphism ⟨
          F₁ (Q⇒ ∘′ [ P.i₁ , P.i₂ ]) ∘ φ (N , M) ∘ s ⊗₁ t ∘ ρ⇐                  ≈⟨ F-resp-≈ ∘[] ⟩∘⟨refl ⟩
          F₁ ([ Q⇒ ∘′ P.i₁ , Q⇒ ∘′ P.i₂ ]) ∘ φ (N , M) ∘ s ⊗₁ t ∘ ρ⇐            ≈⟨ F-resp-≈ ([]-cong₂ P.universal∘i₁≈h₁ P.universal∘i₂≈h₂) ⟩∘⟨refl ⟩
          F₁ ([ P′.i₁ ∘′ N⇒ , P′.i₂ ∘′ M⇒ ]) ∘ φ (N , M) ∘ s ⊗₁ t ∘ ρ⇐          ≈⟨ F-resp-≈ []∘+₁ ⟩∘⟨refl ⟨
          F₁ ([ P′.i₁ , P′.i₂ ] ∘′ (N⇒ +₁ M⇒)) ∘ φ (N , M) ∘ s ⊗₁ t ∘ ρ⇐        ≈⟨ pushˡ homomorphism ⟩
          F₁ [ P′.i₁ , P′.i₂ ] ∘ F₁ (N⇒ +₁ M⇒) ∘ φ (N , M) ∘ s ⊗₁ t ∘ ρ⇐        ≈⟨ refl⟩∘⟨ extendʳ (φ-commute (N⇒ , M⇒)) ⟨
          F₁ [ P′.i₁ , P′.i₂ ] ∘ φ (N′ , M′) ∘ F₁ N⇒ ⊗₁ F₁ M⇒ ∘ s ⊗₁ t ∘ ρ⇐     ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ ⊗-distrib-over-∘ ⟨
          F₁ [ P′.i₁ , P′.i₂ ] ∘ φ (N′ , M′) ∘ (F₁ N⇒ ∘ s) ⊗₁ (F₁ M⇒ ∘ t) ∘ ρ⇐  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ≅C₁.same-deco ⟩⊗⟨ ≅C₂.same-deco ⟩∘⟨refl ⟩
          F₁ [ P′.i₁ , P′.i₂ ] ∘ φ (N′ , M′) ∘ s′ ⊗₁ t′ ∘ ρ⇐                    ∎

Cospans : Category o (o ⊔ ℓ ⊔ ℓ′) (ℓ ⊔ e ⊔ e′)
Cospans = record
    { Obj = 𝒞.Obj
    ; _⇒_ = DecoratedCospan
    ; _≈_ = Same
    ; id = identity
    ; _∘_ = flip compose
    ; assoc = compose-assoc
    ; sym-assoc = same-sym (compose-assoc)
    ; identityˡ = compose-idˡ
    ; identityʳ = compose-idʳ
    ; identity² = compose-id²
    ; equiv = record
        { refl = same-refl
        ; sym = same-sym
        ; trans = same-trans
        }
    ; ∘-resp-≈ = compose-equiv
    }
