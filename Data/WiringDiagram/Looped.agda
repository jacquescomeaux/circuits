{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; _∘F_)
open import Category.Dagger.Semiadditive using (IdempotentSemiadditiveDagger)
open import Category.KaroubiComplete using (KaroubiComplete)
open import Data.WiringDiagram.Balanced using (BWD)
open import Level using (Level)

module Data.WiringDiagram.Looped
    {o ℓ e o′ ℓ′ e′ : Level}
    {𝒞 : Category o ℓ e}
    {𝒟 : Category o′ ℓ′ e′}
    {S : IdempotentSemiadditiveDagger 𝒞}
    (karoubiComplete : KaroubiComplete 𝒟)
    (F : Functor (BWD S) 𝒟)
  where

import Categories.Morphism.Idempotent as Idempotent
import Categories.Morphism.Reasoning as ⇒-Reasoning

open import Categories.Category using (Category)
open import Categories.Functor.Properties using ([_]-resp-∘)
open import Category.Dagger.2-Poset using (Dagger-2-Poset; dagger-2-poset; Maps; Map)
open import Data.WiringDiagram.Balanced S using (Include; Push; Pull)
open import Data.WiringDiagram.Core S using (loop; id-⧈; _□_)
open import Data.WiringDiagram.Equalities S using (loop∘loop; loop∘push∘loop; loop∘pull∘loop)

module BWD = Category (BWD S)
module F = Functor F
module 𝒞 = Category 𝒞
module 𝒟 = Category 𝒟

open Category using (op)
open Idempotent 𝒟 using (IsSplitIdempotent)

module _ (A : 𝒞.Obj) where

  open KaroubiComplete karoubiComplete using (split)
  open IsSplitIdempotent (split ([ F ]-resp-∘ (loop∘loop {A})))

  Unlooped Looped : 𝒟.Obj
  Unlooped = F.₀ A
  Looped = obj

  L : Unlooped 𝒟.⇒ Unlooped
  L = F.₁ loop

  π : Unlooped 𝒟.⇒ Looped
  π = retract

  forget : Looped 𝒟.⇒ Unlooped
  forget = section

  forget∘π : forget 𝒟.∘ π 𝒟.≈ L
  forget∘π = splits

  π∘forget : π 𝒟.∘ forget 𝒟.≈ 𝒟.id
  π∘forget = retracts

  π∘l : π 𝒟.∘ L 𝒟.≈ π
  π∘l = retract-absorb

  l∘forget : L 𝒟.∘ forget 𝒟.≈ forget
  l∘forget = section-absorb

module Push = Functor Push
module Pull = Functor Pull

S′ : Dagger-2-Poset
S′ = dagger-2-poset S

Merge : Functor (Maps S′) 𝒟
Merge = record
    { F₀ = Looped
    ; F₁ = λ {A} {B} f → π B ∘ F.₁ (Push.₁ (map f)) ∘ forget A
    ; identity = iden
    ; homomorphism = λ {f = f} {g} → homo {f = f} {g}
    ; F-resp-≈ = resp
    }
  where
    open Map
    open Category 𝒟 using (_∘_)
    open 𝒟.HomReasoning
    open ⇒-Reasoning 𝒟
    iden : {A : 𝒞.Obj} → π A ∘ F.₁ (Push.₁ 𝒞.id) ∘ forget A 𝒟.≈ 𝒟.id
    iden {A} = begin
        π A ∘ F.₁ (Push.₁ 𝒞.id) ∘ forget A  ≈⟨ refl⟩∘⟨ F.F-resp-≈ Push.identity ⟩∘⟨refl ⟩
        π A ∘ F.₁ BWD.id ∘ forget A         ≈⟨ refl⟩∘⟨ elimˡ F.identity ⟩
        π A ∘ forget A                      ≈⟨ π∘forget A ⟩
        𝒟.id                                ∎
    homo
        : {X Y Z : 𝒞.Obj}
          {f : Map S′ X Y}
          {g : Map S′ Y Z}
        → π Z ∘ F.₁ (Push.₁ (map g 𝒞.∘ map f)) ∘ forget X 𝒟.≈ (π Z ∘ F.₁ (Push.₁ (map g)) ∘ forget Y) ∘ π Y ∘ F.₁ (Push.₁ (map f)) ∘ forget X
    homo {X} {Y} {Z} {f′} {g′} = begin
        π Z ∘ F.₁ (Push.₁ (g 𝒞.∘ f)) ∘ forget X                                 ≈⟨ refl⟩∘⟨ F.F-resp-≈ Push.homomorphism ⟩∘⟨refl ⟩
        π Z ∘ F.₁ (Push.₁ g BWD.∘ Push.₁ f) ∘ forget X                          ≈⟨ refl⟩∘⟨ pushˡ F.homomorphism ⟩
        π Z ∘ F.₁ (Push.₁ g) ∘ F.₁ (Push.₁ f) ∘ forget X                        ≈⟨ pushˡ (𝒟.Equiv.sym (π∘l Z)) ⟩
        π Z ∘ L Z ∘ F.₁ (Push.₁ g) ∘ F.₁ (Push.₁ f) ∘ forget X                  ≈⟨ refl⟩∘⟨ pullˡ (𝒟.Equiv.sym F.homomorphism) ⟩
        π Z ∘ F.₁ (loop BWD.∘ Push.₁ g) ∘ F.₁ (Push.₁ f) ∘ forget X             ≈⟨ refl⟩∘⟨ F.F-resp-≈ (loop∘push∘loop g (entire g′)) ⟩∘⟨refl ⟨
        π Z ∘ F.₁ (loop BWD.∘ Push.₁ g BWD.∘ loop) ∘ F.₁ (Push.₁ f) ∘ forget X  ≈⟨ refl⟩∘⟨ pushˡ F.homomorphism ⟩
        π Z ∘ L Z ∘ F.₁ (Push.₁ g BWD.∘ loop) ∘ F.₁ (Push.₁ f) ∘ forget X       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ F.homomorphism ⟩
        π Z ∘ L Z ∘ F.₁ (Push.₁ g) ∘ L Y ∘ F.₁ (Push.₁ f) ∘ forget X            ≈⟨ pullˡ (π∘l Z) ⟩
        π Z ∘ F.₁ (Push.₁ g) ∘ L Y ∘ F.₁ (Push.₁ f) ∘ forget X                  ≈⟨ pushʳ (pushʳ (pushˡ (𝒟.Equiv.sym (forget∘π Y)))) ⟩
        (π Z ∘ F.₁ (Push.₁ g) ∘ forget Y) ∘ π Y ∘ F.₁ (Push.₁ f) ∘ forget X     ∎
      where
        f : X 𝒞.⇒ Y
        f = map f′
        g : Y 𝒞.⇒ Z
        g = map g′
    resp : {A B : 𝒞.Obj} {f g : A 𝒞.⇒ B} → f 𝒞.≈ g → π B ∘ F.₁ (Push.₁ f) ∘ forget A 𝒟.≈ π B ∘ F.₁ (Push.₁ g) ∘ forget A
    resp {A} {B} {f} {g} f≈g = refl⟩∘⟨ F.F-resp-≈ (Push.F-resp-≈ f≈g) ⟩∘⟨refl

Split : Functor (op (Maps S′)) 𝒟
Split = record
    { F₀ = Looped
    ; F₁ = λ {A} {B} f → π B ∘ F.₁ (Pull.₁ (map f)) ∘ forget A
    ; identity = iden
    ; homomorphism = λ {f = f} {g} → homo {f = f} {g}
    ; F-resp-≈ = resp
    }
  where
    open Map
    open Category 𝒟 using (_∘_)
    open 𝒟.HomReasoning
    open ⇒-Reasoning 𝒟
    iden : {A : 𝒞.Obj} → π A ∘ F.₁ (Pull.₁ 𝒞.id) ∘ forget A 𝒟.≈ 𝒟.id
    iden {A} = begin
        π A ∘ F.₁ (Pull.₁ 𝒞.id) ∘ forget A  ≈⟨ refl⟩∘⟨ F.F-resp-≈ Pull.identity ⟩∘⟨refl ⟩
        π A ∘ F.₁ BWD.id ∘ forget A         ≈⟨ refl⟩∘⟨ elimˡ F.identity ⟩
        π A ∘ forget A                      ≈⟨ π∘forget A ⟩
        𝒟.id                                ∎
    homo
        : {X Y Z : 𝒞.Obj}
          {f : Map S′ Y X}
          {g : Map S′ Z Y}
        → π Z ∘ F.₁ (Pull.₁ (map f 𝒞.∘ map g)) ∘ forget X 𝒟.≈ (π Z ∘ F.₁ (Pull.₁ (map g)) ∘ forget Y) ∘ π Y ∘ F.₁ (Pull.₁ (map f)) ∘ forget X
    homo {X} {Y} {Z} {f′} {g′} = begin
        π Z ∘ F.₁ (Pull.₁ (f 𝒞.∘ g)) ∘ forget X                                 ≈⟨ refl⟩∘⟨ F.F-resp-≈ Pull.homomorphism ⟩∘⟨refl ⟩
        π Z ∘ F.₁ (Pull.₁ g BWD.∘ Pull.₁ f) ∘ forget X                          ≈⟨ refl⟩∘⟨ pushˡ F.homomorphism ⟩
        π Z ∘ F.₁ (Pull.₁ g) ∘ F.₁ (Pull.₁ f) ∘ forget X                        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ l∘forget X ⟨
        π Z ∘ F.₁ (Pull.₁ g) ∘ F.₁ (Pull.₁ f) ∘ L X ∘ forget X                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (𝒟.Equiv.sym F.homomorphism) ⟩
        π Z ∘ F.₁ (Pull.₁ g) ∘ F.₁ (Pull.₁ f BWD.∘ loop) ∘ forget X             ≈⟨ refl⟩∘⟨ refl⟩∘⟨ F.F-resp-≈ (loop∘pull∘loop f (functional f′)) ⟩∘⟨refl ⟨
        π Z ∘ F.₁ (Pull.₁ g) ∘ F.₁ (loop BWD.∘ Pull.₁ f BWD.∘ loop) ∘ forget X  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ F.homomorphism ⟩
        π Z ∘ F.₁ (Pull.₁ g) ∘ L Y ∘ F.₁ (Pull.₁ f BWD.∘ loop) ∘ forget X       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ F.homomorphism ⟩
        π Z ∘ F.₁ (Pull.₁ g) ∘ L Y ∘ F.₁ (Pull.₁ f) ∘ L X ∘ forget X            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ l∘forget X ⟩
        π Z ∘ F.₁ (Pull.₁ g) ∘ L Y ∘ F.₁ (Pull.₁ f) ∘ forget X                  ≈⟨ pushʳ (pushʳ (pushˡ (𝒟.Equiv.sym (forget∘π Y)))) ⟩
        (π Z ∘ F.₁ (Pull.₁ g) ∘ forget Y) ∘ π Y ∘ F.₁ (Pull.₁ f) ∘ forget X     ∎
      where
        f : Y 𝒞.⇒ X
        f = map f′
        g : Z 𝒞.⇒ Y
        g = map g′
    resp : {A B : 𝒞.Obj} {f g : B 𝒞.⇒ A} → f 𝒞.≈ g → π B ∘ F.₁ (Pull.₁ f) ∘ forget A 𝒟.≈ π B ∘ F.₁ (Pull.₁ g) ∘ forget A
    resp {A} {B} {f} {g} f≈g = refl⟩∘⟨ F.F-resp-≈ (Pull.F-resp-≈ f≈g) ⟩∘⟨refl
