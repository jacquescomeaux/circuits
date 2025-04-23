{-# OPTIONS --without-K --safe #-}

open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)

module Functor.Instance.Cospan.Stack {o ℓ e} (𝒞 : FinitelyCocompleteCategory o ℓ e) where

import Categories.Diagram.Pushout as DiagramPushout
import Categories.Diagram.Pushout.Properties as PushoutProperties
import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as ⇒-Reasoning

open import Categories.Category.Core using (Category)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Category.Instance.Cospans 𝒞 using (Cospan; Cospans; Same; id-Cospan; compose)
open import Category.Instance.FinitelyCocompletes {o} {ℓ} {e} using () renaming (_×_ to _×′_)
open import Category.Cartesian.Instance.FinitelyCocompletes {o} {ℓ} {e} using (-+-; FinitelyCocompletes-CC)
open import Data.Product.Base using (Σ; _,_; _×_; proj₁; proj₂)
open import Functor.Exact using (RightExactFunctor; IsPushout⇒Pushout)
open import Level using (Level; _⊔_; suc)

module 𝒞 = FinitelyCocompleteCategory 𝒞
module Cospans = Category Cospans

open 𝒞 using (U; _+_; _+₁_; pushout; coproduct; [_,_]; ⊥; cocartesianCategory; monoidal)
open Category U
open DiagramPushout U using (Pushout)
open PushoutProperties U using (up-to-iso)

module 𝒞×𝒞 = FinitelyCocompleteCategory (𝒞 ×′ 𝒞)
open 𝒞×𝒞 using () renaming (pushout to pushout′; U to U×U)
open DiagramPushout U×U using () renaming (Pushout to Pushout′)

open import Categories.Category.Monoidal.Utilities monoidal using (_⊗ᵢ_)

together :  {A A′ B B′ : Obj} → Cospan A B → Cospan A′ B′ → Cospan (A + A′) (B + B′)
together A⇒B A⇒B′ = record
    { f₁ = f₁ A⇒B +₁ f₁ A⇒B′
    ; f₂ = f₂ A⇒B +₁ f₂ A⇒B′
    }
  where
    open Cospan

id⊗id≈id : {A B : Obj} → Same (together (id-Cospan {A}) (id-Cospan {B})) (id-Cospan {A + B})
id⊗id≈id {A} {B} = record
    { ≅N = ≅.refl
    ; from∘f₁≈f₁′ = from∘f≈f′
    ; from∘f₂≈f₂′ = from∘f≈f′
    }
  where
    open Morphism U using (module ≅)
    open HomReasoning
    open 𝒞 using (+-η; []-cong₂)
    open coproduct {A} {B} using (i₁; i₂)
    from∘f≈f′ : id ∘ [ i₁ ∘ id , i₂ ∘ id ] 𝒞.≈ id
    from∘f≈f′ = begin
        id ∘ [ i₁ ∘ id , i₂ ∘ id ]  ≈⟨ identityˡ ⟩
        [ i₁ ∘ id , i₂ ∘ id ]       ≈⟨ []-cong₂ identityʳ identityʳ ⟩
        [ i₁ , i₂ ]                 ≈⟨ +-η ⟩
        id                          ∎

homomorphism
    : {A A′ B B′ C C′ : Obj}
    → (A⇒B : Cospan A B)
    → (B⇒C : Cospan B C)
    → (A⇒B′ : Cospan A′ B′)
    → (B⇒C′ : Cospan B′ C′)
    → Same (together (compose A⇒B B⇒C) (compose A⇒B′ B⇒C′)) (compose (together A⇒B A⇒B′) (together B⇒C B⇒C′) )
homomorphism A⇒B B⇒C A⇒B′ B⇒C′ = record
    { ≅N = ≅N
    ; from∘f₁≈f₁′ = from∘f₁≈f₁′
    ; from∘f₂≈f₂′ = from∘f₂≈f₂′
    }
  where
    open Cospan
    open Pushout
    open HomReasoning
    open ⇒-Reasoning U
    open Morphism U using (_≅_)
    open _≅_
    open 𝒞 using (+₁∘+₁)
    module -+- = RightExactFunctor (-+- {𝒞})
    P₁ = pushout (f₂ A⇒B) (f₁ B⇒C)
    P₂ = pushout (f₂ A⇒B′) (f₁ B⇒C′)
    module P₁ = Pushout P₁
    module P₂ = Pushout P₂
    P₁×P₂ = pushout′ (f₂ A⇒B , f₂ A⇒B′) (f₁ B⇒C , f₁ B⇒C′)
    module P₁×P₂ = Pushout′ P₁×P₂
    P₃ = pushout (f₂ A⇒B +₁ f₂ A⇒B′) (f₁ B⇒C +₁ f₁ B⇒C′)
    P₃′ = IsPushout⇒Pushout (-+-.F-resp-pushout P₁×P₂.isPushout)
    ≅N : Q P₃′ ≅ Q P₃
    ≅N = up-to-iso P₃′ P₃
    from∘f₁≈f₁′ : from ≅N ∘ (f₁ (compose A⇒B B⇒C) +₁ f₁ (compose A⇒B′ B⇒C′)) ≈ f₁ (compose (together A⇒B A⇒B′) (together B⇒C B⇒C′))
    from∘f₁≈f₁′ = begin
        from ≅N ∘ (f₁ (compose A⇒B B⇒C) +₁ f₁ (compose A⇒B′ B⇒C′))  ≈⟨ Equiv.refl ⟩
        from ≅N ∘ ((i₁ P₁ ∘ f₁ A⇒B) +₁ (i₁ P₂ ∘ f₁ A⇒B′))           ≈⟨ refl⟩∘⟨ +₁∘+₁ ⟨
        from ≅N ∘ (i₁ P₁ +₁ i₁ P₂) ∘ (f₁ A⇒B +₁ f₁ A⇒B′)            ≈⟨ Equiv.refl ⟩
        from ≅N ∘ i₁ P₃′ ∘ f₁ (together A⇒B A⇒B′)                   ≈⟨ pullˡ (universal∘i₁≈h₁ P₃′) ⟩
        i₁ P₃ ∘ f₁ (together A⇒B A⇒B′)                              ∎
    from∘f₂≈f₂′ : from ≅N ∘ (f₂ (compose A⇒B B⇒C) +₁ f₂ (compose A⇒B′ B⇒C′)) ≈ f₂ (compose (together A⇒B A⇒B′) (together B⇒C B⇒C′))
    from∘f₂≈f₂′ = begin
        from ≅N ∘ (f₂ (compose A⇒B B⇒C) +₁ f₂ (compose A⇒B′ B⇒C′))  ≈⟨ Equiv.refl ⟩
        from ≅N ∘ ((i₂ P₁ ∘ f₂ B⇒C) +₁ (i₂ P₂ ∘ f₂ B⇒C′))           ≈⟨ refl⟩∘⟨ +₁∘+₁ ⟨
        from ≅N ∘ (i₂ P₁ +₁ i₂ P₂) ∘ (f₂ B⇒C +₁ f₂ B⇒C′)            ≈⟨ Equiv.refl ⟩
        from ≅N ∘ i₂ P₃′ ∘ f₂ (together B⇒C B⇒C′)                   ≈⟨ pullˡ (universal∘i₂≈h₂ P₃′) ⟩
        i₂ P₃ ∘ f₂ (together B⇒C B⇒C′)                              ∎

⊗-resp-≈
    : {A A′ B B′ : Obj}
      {f f′ : Cospan A B}
      {g g′ : Cospan A′ B′}
    → Same f f′
    → Same g g′
    → Same (together f g) (together f′ g′)
⊗-resp-≈ {_} {_} {_} {_} {f} {f′} {g} {g′} ≈f ≈g = record
    { ≅N = ≈f.≅N ⊗ᵢ ≈g.≅N
    ; from∘f₁≈f₁′ = from∘f₁≈f₁′
    ; from∘f₂≈f₂′ = from∘f₂≈f₂′
    }
  where
    open 𝒞 using (-+-)
    module ≈f = Same ≈f
    module ≈g = Same ≈g
    open HomReasoning
    open Cospan
    open 𝒞 using (+₁-cong₂; +₁∘+₁)
    from∘f₁≈f₁′ : (≈f.from +₁ ≈g.from) ∘ (f₁ f +₁ f₁ g) ≈ f₁ f′ +₁ f₁ g′
    from∘f₁≈f₁′ = begin 
        (≈f.from +₁ ≈g.from) ∘ (f₁ f +₁ f₁ g) ≈⟨ +₁∘+₁ ⟩
        (≈f.from ∘ f₁ f) +₁ (≈g.from ∘ f₁ g)  ≈⟨ +₁-cong₂ (≈f.from∘f₁≈f₁′) (≈g.from∘f₁≈f₁′) ⟩
        f₁ f′ +₁ f₁ g′                        ∎
    from∘f₂≈f₂′ : (≈f.from +₁ ≈g.from) ∘ (f₂ f +₁ f₂ g) ≈ f₂ f′ +₁ f₂ g′
    from∘f₂≈f₂′ = begin 
        (≈f.from +₁ ≈g.from) ∘ (f₂ f +₁ f₂ g) ≈⟨ +₁∘+₁ ⟩
        (≈f.from ∘ f₂ f) +₁ (≈g.from ∘ f₂ g)  ≈⟨ +₁-cong₂ (≈f.from∘f₂≈f₂′) (≈g.from∘f₂≈f₂′) ⟩
        f₂ f′ +₁ f₂ g′                        ∎

⊗ : Bifunctor Cospans Cospans Cospans
⊗ = record
    { F₀ = λ { (A , A′) → A + A′ }
    ; F₁ = λ { (f , g) → together f g }
    ; identity = λ { {x , y} → id⊗id≈id {x} {y} }
    ; homomorphism = λ { {_} {_} {_} {A⇒B , A⇒B′} {B⇒C , B⇒C′} → homomorphism A⇒B B⇒C A⇒B′ B⇒C′ }
    ; F-resp-≈ = λ { (≈f , ≈g) → ⊗-resp-≈ ≈f ≈g }
    }
