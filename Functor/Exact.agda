{-# OPTIONS --without-K --safe #-}

module Functor.Exact where

import Function.Base as Function

open import Categories.Category.Core using (Category)
open import Categories.Category.Cocomplete.Finitely using (FinitelyCocomplete)
open import Categories.Diagram.Coequalizer using (Coequalizer; IsCoequalizer; IsCoequalizer⇒Coequalizer)
open import Categories.Diagram.Pushout using (IsPushout; Pushout)
open import Categories.Diagram.Pushout.Properties using (Coproduct×Coequalizer⇒Pushout; up-to-iso)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Properties using ([_]-resp-square; [_]-resp-≅)
open import Categories.Object.Coproduct using (IsCoproduct; Coproduct; IsCoproduct⇒Coproduct; Coproduct⇒IsCoproduct)
open import Categories.Object.Initial using (IsInitial)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_)
open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)
open import Function.Base using (id)
open import Level

module _ {o ℓ e : Level} {𝒞 : Category o ℓ e} where

  open Category 𝒞

  Coequalizer-resp-≈
      : {A B C : Obj}
        {f f′ g g′ : A ⇒ B}
        {arr : B ⇒ C}
      → f ≈ f′
      → g ≈ g′
      → IsCoequalizer 𝒞 f g arr
      → IsCoequalizer 𝒞 f′ g′ arr
  Coequalizer-resp-≈ ≈f ≈g ce = record
      { equality = refl⟩∘⟨ sym ≈f ○ equality ○ refl⟩∘⟨ ≈g
      ; coequalize = λ { eq → coequalize (refl⟩∘⟨ ≈f ○ eq ○ refl⟩∘⟨ sym ≈g) }
      ; universal = universal
      ; unique = unique
      }
    where
      open HomReasoning
      open Equiv
      open IsCoequalizer ce

  IsPushout⇒Pushout
      : {A B C D : Obj}
        {f : A ⇒ B} {g : A ⇒ C} {i₁ : B ⇒ D} {i₂ : C ⇒ D}
      → IsPushout 𝒞 f g i₁ i₂
      → Pushout 𝒞 f g
  IsPushout⇒Pushout isP = record { i₁ = _ ; i₂ = _ ; isPushout = isP }

module _ {o ℓ e : Level} {𝒞 𝒟 : Category o ℓ e} (F : Functor 𝒞 𝒟) where

  open Functor F
  open Category 𝒞

  PreservesCoequalizer : Set (o ⊔ ℓ ⊔ e)
  PreservesCoequalizer = {A B C : Obj} {f g : A ⇒ B} {h : B ⇒ C} → IsCoequalizer 𝒞 f g h → IsCoequalizer 𝒟 (F₁ f) (F₁ g) (F₁ h)

  PreservesCoproduct : Set (o ⊔ ℓ ⊔ e)
  PreservesCoproduct = {A B C : Obj} {i₁ : A ⇒ C} {i₂ : B ⇒ C} → IsCoproduct 𝒞 i₁ i₂ → IsCoproduct 𝒟 (F₁ i₁) (F₁ i₂)

  PreservesInitial : Set (o ⊔ ℓ ⊔ e)
  PreservesInitial = {A : Obj} → IsInitial 𝒞 A → IsInitial 𝒟 (F₀ A)

  PreservesPushouts : Set (o ⊔ ℓ ⊔ e)
  PreservesPushouts = {A B C D : Obj} {f : A ⇒ B} {g : A ⇒ C} {i₁ : B ⇒ D} {i₂ : C ⇒ D} → IsPushout 𝒞 f g i₁ i₂ → IsPushout 𝒟 (F₁ f) (F₁ g) (F₁ i₁) (F₁ i₂)

module _ {o ℓ e : Level} (𝒞 𝒟 : FinitelyCocompleteCategory o ℓ e) where

  open FinitelyCocompleteCategory using (U)

  record IsRightExact (F : Functor (U 𝒞) (U 𝒟)) : Set (o ⊔ ℓ ⊔ e) where

    field
      F-resp-⊥ : PreservesInitial F
      F-resp-+ : PreservesCoproduct F
      F-resp-coeq : PreservesCoequalizer F

    open FinitelyCocompleteCategory 𝒞 hiding (U)
    open Functor F

    F-resp-pushout : PreservesPushouts F
    F-resp-pushout {A} {B} {C} {D} {f} {g} {i₁} {i₂} P = record
        { commute = [ F ]-resp-square P.commute
        ; universal = λ { eq → F-P′.universal eq ∘′ F-≅D.from }
        ; universal∘i₁≈h₁ = assoc′ ○′ refl⟩∘⟨′ [ F ]-resp-square P.universal∘i₁≈h₁ ○′ F-P′.universal∘i₁≈h₁
        ; universal∘i₂≈h₂ = assoc′ ○′ refl⟩∘⟨′ [ F ]-resp-square P.universal∘i₂≈h₂ ○′ F-P′.universal∘i₂≈h₂
        ; unique-diagram = λ { eq₁ eq₂ →
            insertʳ′ F-≅D.isoˡ ○′
            F-P′.unique-diagram
                (assoc′ ○′
                  refl⟩∘⟨′ (Equiv′.sym (insertˡ′ F-≅D.isoˡ ○′ (refl⟩∘⟨′ [ F ]-resp-square P.universal∘i₁≈h₁))) ○′
                  eq₁ ○′
                  refl⟩∘⟨′ (insertˡ′ F-≅D.isoˡ ○′ (refl⟩∘⟨′ [ F ]-resp-square P.universal∘i₁≈h₁)) ○′
                  sym-assoc′)
                (assoc′ ○′
                  refl⟩∘⟨′ (Equiv′.sym (insertˡ′ F-≅D.isoˡ ○′ (refl⟩∘⟨′ [ F ]-resp-square P.universal∘i₂≈h₂))) ○′
                  eq₂ ○′
                  refl⟩∘⟨′ (insertˡ′ F-≅D.isoˡ ○′ (refl⟩∘⟨′ [ F ]-resp-square P.universal∘i₂≈h₂)) ○′
                  sym-assoc′) ⟩∘⟨refl′ ○′
            cancelʳ′ F-≅D.isoˡ }
        }
      where
        module P = IsPushout P
        cp : Coproduct (U 𝒞) B C
        cp = coproduct
        open Coproduct cp using (inject₁; inject₂; [_,_]; g-η; []-cong₂) renaming (i₁ to ι₁; i₂ to ι₂; A+B to B+C)
        ce : Coequalizer (U 𝒞) (ι₁ ∘ f) (ι₂ ∘ g)
        ce = coequalizer (ι₁ ∘ f) (ι₂ ∘ g)
        open Coequalizer ce using (equality; coequalize) renaming (arr to i₁-i₂; obj to D′; universal to univ; unique to uniq)
        open HomReasoning
        open import Categories.Morphism.Reasoning (U 𝒞)
        open import Categories.Morphism.Reasoning (U 𝒟) using () renaming (pullʳ to pullʳ′; insertʳ to insertʳ′; cancelʳ to cancelʳ′; insertˡ to insertˡ′; extendˡ to extendˡ′)
        import Categories.Morphism as Morphism
        open Morphism (U 𝒞) using (_≅_)
        open Morphism (U 𝒟) using () renaming (_≅_ to _≅′_)
        P′ : IsPushout (U 𝒞) f g (i₁-i₂ ∘ ι₁) (i₁-i₂ ∘ ι₂)
        P′ = Pushout.isPushout (Coproduct×Coequalizer⇒Pushout (U 𝒞) cp ce)
        open Category (U 𝒟) using () renaming (_∘_ to _∘′_; module HomReasoning to 𝒟-Reasoning; assoc to assoc′; sym-assoc to sym-assoc′; module Equiv to Equiv′)
        open 𝒟-Reasoning using () renaming (_○_ to _○′_; refl⟩∘⟨_ to refl⟩∘⟨′_; _⟩∘⟨refl to _⟩∘⟨refl′)
        ≅D : D ≅ D′
        ≅D = up-to-iso (U 𝒞) (IsPushout⇒Pushout P) (IsPushout⇒Pushout P′)
        F-≅D : F₀ D ≅′ F₀ D′
        F-≅D = [ F ]-resp-≅ ≅D
        module F-≅D = _≅′_ F-≅D
        F-cp : IsCoproduct (U 𝒟) (F₁ ι₁) (F₁ ι₂)
        F-cp = F-resp-+ (Coproduct⇒IsCoproduct (U 𝒞) cp)
        F-ce : IsCoequalizer (U 𝒟) (F₁ ι₁ ∘′ F₁ f) (F₁ ι₂ ∘′ F₁ g) (F₁ i₁-i₂)
        F-ce = Coequalizer-resp-≈ homomorphism homomorphism (F-resp-coeq (Coequalizer.isCoequalizer ce))
        F-P′ : IsPushout (U 𝒟) (F₁ f) (F₁ g) (F₁ i₁-i₂ ∘′ F₁ ι₁) (F₁ i₁-i₂ ∘′ F₁ ι₂)
        F-P′ = Pushout.isPushout (Coproduct×Coequalizer⇒Pushout (U 𝒟) (IsCoproduct⇒Coproduct (U 𝒟) F-cp) (IsCoequalizer⇒Coequalizer (U 𝒟) F-ce))
        module F-P′ = IsPushout F-P′

  record RightExactFunctor : Set (o ⊔ ℓ ⊔ e) where

    constructor rightexact

    field
      F : Functor (U 𝒞) (U 𝒟)
      isRightExact : IsRightExact F

    open Functor F public
    open IsRightExact isRightExact public

module _ where

  open FinitelyCocompleteCategory using (U)

  ∘-resp-IsRightExact
      : {o ℓ e : Level}
        {𝒞 𝒟 ℰ : FinitelyCocompleteCategory o ℓ e}
        {F : Functor (U 𝒞) (U 𝒟)}
        {G : Functor (U 𝒟) (U ℰ)}
      → IsRightExact 𝒞 𝒟 F
      → IsRightExact 𝒟 ℰ G
      → IsRightExact 𝒞 ℰ (G ∘F F)
  ∘-resp-IsRightExact F-isRightExact G-isRightExact = record
      { F-resp-⊥ = G.F-resp-⊥ ∘ F.F-resp-⊥
      ; F-resp-+ = G.F-resp-+ ∘ F.F-resp-+
      ; F-resp-coeq = G.F-resp-coeq ∘ F.F-resp-coeq
      }
    where
      open Function using (_∘_)
      module F = IsRightExact F-isRightExact
      module G = IsRightExact G-isRightExact

∘-RightExactFunctor
    : {o ℓ e : Level}
    → {A B C : FinitelyCocompleteCategory o ℓ e}
    → RightExactFunctor B C → RightExactFunctor A B → RightExactFunctor A C
∘-RightExactFunctor F G = record
    { F = F.F ∘F G.F
    ; isRightExact = ∘-resp-IsRightExact G.isRightExact F.isRightExact
    }
  where
    module F = RightExactFunctor F
    module G = RightExactFunctor G

idF-RightExact : {o ℓ e : Level} → {𝒞 : FinitelyCocompleteCategory o ℓ e} → IsRightExact 𝒞 𝒞 idF
idF-RightExact = record
    { F-resp-⊥ = id
    ; F-resp-+ = id
    ; F-resp-coeq = id
    }

idREF : {o ℓ e : Level} → {𝒞 : FinitelyCocompleteCategory o ℓ e} → RightExactFunctor 𝒞 𝒞
idREF = record
    { F = idF
    ; isRightExact = idF-RightExact
    }
