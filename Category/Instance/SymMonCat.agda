{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --lossy-unification #-}

open import Level using (Level; suc; _⊔_)
module Category.Instance.SymMonCat {o ℓ e : Level} where

import Categories.Category.Monoidal.Reasoning as ⊗-Reasoning
import Categories.Functor.Monoidal.Symmetric as SMF
import Categories.Morphism.Reasoning as ⇒-Reasoning
import Categories.Morphism as Morphism
import Categories.NaturalTransformation.NaturalIsomorphism.Monoidal.Symmetric as SMNI
import Categories.Category.Monoidal.Utilities as MonoidalUtil
import Categories.Category.Monoidal.Braided.Properties as BraidedProperties
open import Relation.Binary.Core using (Rel)

open import Categories.Category using (Category; _[_,_]; _[_∘_])
open import Categories.Category.Helper using (categoryHelper)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Functor.Monoidal.Properties using (idF-SymmetricMonoidal; ∘-SymmetricMonoidal)

open SMF.Lax using (SymmetricMonoidalFunctor)
open SMNI.Lax using (SymmetricMonoidalNaturalIsomorphism; id; isEquivalence)

assoc
    : {A B C D : SymmetricMonoidalCategory o ℓ e}
      {F : SymmetricMonoidalFunctor A B}
      {G : SymmetricMonoidalFunctor B C}
      {H : SymmetricMonoidalFunctor C D}
    → SymmetricMonoidalNaturalIsomorphism
        (∘-SymmetricMonoidal (∘-SymmetricMonoidal H G) F)
        (∘-SymmetricMonoidal H (∘-SymmetricMonoidal G F))
assoc {A} {B} {C} {D} {F} {G} {H} = SMNI.Lax.associator {o} {ℓ} {e} {o} {ℓ} {e} {o} {ℓ} {e} {o} {ℓ} {e} {A} {B} {C} {D} {F} {G} {H}

identityˡ
    : {A B : SymmetricMonoidalCategory o ℓ e}
      {F : SymmetricMonoidalFunctor A B}
    → SymmetricMonoidalNaturalIsomorphism (∘-SymmetricMonoidal (idF-SymmetricMonoidal B) F) F
identityˡ {A} {B} {F} = SMNI.Lax.unitorˡ {o} {ℓ} {e} {o} {ℓ} {e} {A} {B} {F}

identityʳ
    : {A B : SymmetricMonoidalCategory o ℓ e}
      {F : SymmetricMonoidalFunctor A B}
    → SymmetricMonoidalNaturalIsomorphism (∘-SymmetricMonoidal F (idF-SymmetricMonoidal A)) F
identityʳ {A} {B} {F} = SMNI.Lax.unitorʳ {o} {ℓ} {e} {o} {ℓ} {e} {A} {B} {F}

Compose
    : {A B C : SymmetricMonoidalCategory o ℓ e}
    → SymmetricMonoidalFunctor B C
    → SymmetricMonoidalFunctor A B
    → SymmetricMonoidalFunctor A C
Compose {A} {B} {C} F G = ∘-SymmetricMonoidal {o} {ℓ} {e} {o} {ℓ} {e} {o} {ℓ} {e} {A} {B} {C} F G

∘-resp-≈
    : {A B C : SymmetricMonoidalCategory o ℓ e}
      {f h : SymmetricMonoidalFunctor B C}
      {g i : SymmetricMonoidalFunctor A B}
    → SymmetricMonoidalNaturalIsomorphism f h
    → SymmetricMonoidalNaturalIsomorphism g i
    → SymmetricMonoidalNaturalIsomorphism (∘-SymmetricMonoidal f g) (∘-SymmetricMonoidal h i)
∘-resp-≈ {A} {B} {C} {F} {F′} {G} {G′} F≃F′ G≃G′ = SMNI.Lax._ⓘₕ_ {o} {ℓ} {e} {o} {ℓ} {e} {o} {ℓ} {e} {A} {B} {C} {G} {G′} {F} {F′} F≃F′ G≃G′

SymMonCat : Category (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
SymMonCat = categoryHelper record
    { Obj = SymmetricMonoidalCategory o ℓ e
    ; _⇒_ = SymmetricMonoidalFunctor {o} {o} {ℓ} {ℓ} {e} {e}
    ; _≈_ = λ { {A} {B} → SymmetricMonoidalNaturalIsomorphism {o} {ℓ} {e} {o} {ℓ} {e} {A} {B} }
    ; id = λ { {X} → idF-SymmetricMonoidal X }
    ; _∘_ = λ { {A} {B} {C} F G → Compose {A} {B} {C} F G }
    ; assoc = λ { {A} {B} {C} {D} {F} {G} {H} → assoc {A} {B} {C} {D} {F} {G} {H} }
    ; identityˡ = λ { {A} {B} {F} → identityˡ {A} {B} {F} }
    ; identityʳ = λ { {A} {B} {F} → identityʳ {A} {B} {F} }
    ; equiv = isEquivalence
    ; ∘-resp-≈ = λ { {A} {B} {C} {f} {h} {g} {i} f≈h g≈i → ∘-resp-≈ {A} {B} {C} {f} {h} {g} {i} f≈h g≈i }
    }
