{-# OPTIONS --without-K --safe #-}

open import Level using (Level; suc; _⊔_)

module Category.Equivalence.Instance.Monoids (c ℓ : Level) where

open import Category.Instance.Monoids c ℓ using (Monoids; MonoidHomomorphism; mk-⇒; _≗_)

import Algebra as Alg
import Algebra.Morphism.Bundles as Raw

open import Category.Instance.Setoids.SymmetricMonoidal {c} {ℓ} using (Setoids-×; ×-monoidal′)

open import Categories.Category using (module Category; _[_∘_])
open import Categories.Category.Construction.Monoids Setoids-×.monoidal using () renaming (Monoids to Monoids[Setoids])
open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.Functor using (Functor; _∘F_) renaming (id to Id)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper; _≃_)
open import Categories.Object.Monoid Setoids-×.monoidal using (Monoid; Monoid⇒)
open import Data.Monoid using (fromMonoid; toMonoid; fromMonoid⇒; toMonoid⇒)
open import Function using (Func; _⟨$⟩_; _∘_) renaming (id to idf)
open import Function.Construct.Identity using () renaming (function to IdFunc)
open import Relation.Binary using (Setoid)

open Category using (id)
open Func
open MonoidHomomorphism using (rawMonoidHomomorphism; ⟦_⟧)
open Monoid⇒

abstract opaque

  unfolding fromMonoid⇒

  identity⇒
      : (A : Alg.Monoid c ℓ)
        (open Alg.Monoid A)
        {x : Carrier}
      → arr (fromMonoid⇒ A A (rawMonoidHomomorphism (id Monoids {A}))) ⟨$⟩ x ≈ x
  identity⇒ = Alg.Monoid.refl

  homo⇒
      : (X Y Z : Alg.Monoid c ℓ)
        {f : MonoidHomomorphism X Y}
        {g : MonoidHomomorphism Y Z}
        {x : Alg.Monoid.Carrier X}
        (open Alg.Monoid Z)
      → arr (fromMonoid⇒ X Z (rawMonoidHomomorphism (Monoids [ g ∘ f ]))) ⟨$⟩ x
      ≈ arr (fromMonoid⇒ Y Z (rawMonoidHomomorphism g)) ⟨$⟩ (arr (fromMonoid⇒ X Y (rawMonoidHomomorphism f)) ⟨$⟩ x)
  homo⇒ X Y Z = Alg.Monoid.refl Z

  resp⇒
      : (A B : Alg.Monoid c ℓ)
        {f g : MonoidHomomorphism A B}
      → f ≗ g
      → {x : Alg.Monoid.Carrier A}
        (open Alg.Monoid B)
      → arr (fromMonoid⇒ A B (rawMonoidHomomorphism f)) ⟨$⟩ x
      ≈ arr (fromMonoid⇒ A B (rawMonoidHomomorphism g)) ⟨$⟩ x
  resp⇒ A B f≗g {x} = f≗g x

From : Functor Monoids Monoids[Setoids]
From = record
    { F₀ = fromMonoid
    ; F₁ = λ {M N} f → fromMonoid⇒ M N (rawMonoidHomomorphism f)
    ; identity = λ {A} → identity⇒ A
    ; homomorphism = λ {X Y Z} → homo⇒ X Y Z
    ; F-resp-≈ = λ {A B} → resp⇒ A B
    }

opaque

  unfolding toMonoid⇒

  identity⇐
      : {A : Monoid}
      → mk-⇒ (toMonoid⇒ A A (id Monoids[Setoids])) ≗ id Monoids {toMonoid A}
  identity⇐ {A} _ = Alg.Monoid.refl (toMonoid A)

  homo⇐
      : {X Y Z : Monoid}
        {f : Monoid⇒ X Y}
        {g : Monoid⇒ Y Z}
      → mk-⇒ (toMonoid⇒ X Z (Monoids[Setoids] [ g ∘ f ]))
      ≗ _[_∘_] Monoids {toMonoid X} {toMonoid Y} {toMonoid Z} (mk-⇒ (toMonoid⇒ Y Z g)) (mk-⇒ (toMonoid⇒ X Y f))
  homo⇐ {X} {Y} {Z} {f} {g} x = Alg.Monoid.refl (toMonoid Z)

  resp⇐
      : {A B : Monoid}
        {f g : Monoid⇒ A B}
      → (∀ {x} (open Setoid (Monoid.Carrier B)) → arr f ⟨$⟩ x ≈ arr g ⟨$⟩ x)
      → _≗_ {toMonoid A} {toMonoid B} (mk-⇒ (toMonoid⇒ A B f)) (mk-⇒ (toMonoid⇒ A B g))
  resp⇐ {A} {B} {f} {g} f≈g x = f≈g {x}

To : Functor Monoids[Setoids] Monoids
To = record
    { F₀ = toMonoid
    ; F₁ = λ {M N} f → mk-⇒ (toMonoid⇒ M N f)
    ; identity = identity⇐
    ; homomorphism = homo⇐
    ; F-resp-≈ = resp⇐
    }

opaque

  unfolding toMonoid Data.Monoid.FromMonoid.μ

  from∘to⇒ : (M : Monoid) → Monoid⇒ (fromMonoid (toMonoid M)) M
  from∘to⇒ M = let open Alg.Monoid (toMonoid M) in record
      { arr = IdFunc setoid
      ; preserves-μ = refl
      ; preserves-η = refl
      }

  from∘to⇐ : (M : Monoid) → Monoid⇒ M (fromMonoid (toMonoid M))
  from∘to⇐ M = let open Alg.Monoid (toMonoid M) in record
      { arr = IdFunc setoid
      ; preserves-μ = refl
      ; preserves-η = refl
      }

  from∘to-isoˡ
      : (M : Monoid)
        (open Alg.Monoid (toMonoid M))
      → {x : Alg.Monoid.Carrier (toMonoid M)}
      → arr (from∘to⇐ M) ⟨$⟩ (arr (from∘to⇒ M) ⟨$⟩ x) ≈ x
  from∘to-isoˡ M = Setoid.refl (Monoid.Carrier M)

  from∘to-isoʳ
      : (M : Monoid)
        (open Setoid (Monoid.Carrier M))
        {x : Setoid.Carrier (Monoid.Carrier M)}
      → arr (from∘to⇒ M) ⟨$⟩ (arr (from∘to⇐ M) ⟨$⟩ x) ≈ x
  from∘to-isoʳ M = Setoid.refl (Monoid.Carrier M)

  opaque
    unfolding fromMonoid⇒ toMonoid⇒
    from∘to⇒-commute
        : {M N : Monoid}
          (f : Monoid⇒ M N)
          {x : Alg.Monoid.Carrier (toMonoid M)}
          (open Setoid (Monoid.Carrier N))
        → arr (from∘to⇒ N) ⟨$⟩ (arr (fromMonoid⇒ (toMonoid M) (toMonoid N) (toMonoid⇒ M N f)) ⟨$⟩ x)
        ≈ arr f ⟨$⟩ (arr (from∘to⇒ M) ⟨$⟩ x)
    from∘to⇒-commute {M} {N} f = Setoid.refl (Monoid.Carrier N)

From∘To : From ∘F To ≃ Id
From∘To = niHelper record
    { η = from∘to⇒
    ; η⁻¹ = from∘to⇐
    ; commute = from∘to⇒-commute
    ; iso = λ M → record
        { isoˡ = from∘to-isoˡ M
        ; isoʳ = from∘to-isoʳ M
        }
    }

opaque
  unfolding toMonoid Data.Monoid.FromMonoid.μ
  to∘from⇒ : (M : Alg.Monoid c ℓ) → MonoidHomomorphism (toMonoid (fromMonoid M)) M
  to∘from⇒ M = let open Alg.Monoid M in mk-⇒ record
      { ⟦_⟧ = idf
      ; isMonoidHomomorphism = record
          { isMagmaHomomorphism = record
              { isRelHomomorphism = record
                  { cong = idf
                  }
              ; homo = λ _ _ → refl
              }
          ; ε-homo = refl
          }
      }

  to∘from⇐ : (M : Alg.Monoid c ℓ) → MonoidHomomorphism M (toMonoid (fromMonoid M))
  to∘from⇐ M = let open Alg.Monoid M in mk-⇒ record
      { ⟦_⟧ = idf
      ; isMonoidHomomorphism = record
          { isMagmaHomomorphism = record
              { isRelHomomorphism = record
                  { cong = idf
                  }
              ; homo = λ _ _ → refl
              }
          ; ε-homo = refl
          }
      }

  to∘from-isoˡ
      : (M : Alg.Monoid c ℓ)
        (open Alg.Monoid (toMonoid (fromMonoid M)))
      → Monoids [ to∘from⇐ M ∘ to∘from⇒ M ] ≗ id Monoids {toMonoid (fromMonoid M)}
  to∘from-isoˡ M _ = Alg.Monoid.refl M

  to∘from-isoʳ
      : (M : Alg.Monoid c ℓ)
        (open Alg.Monoid M)
      → Monoids [ to∘from⇒ M ∘ to∘from⇐ M ] ≗ id Monoids {M}
  to∘from-isoʳ M _ = Alg.Monoid.refl M

  opaque
    unfolding toMonoid⇒ fromMonoid⇒
    to∘from⇒-commute
        : {M N : Alg.Monoid c ℓ}
          (f : MonoidHomomorphism M N)
          (open Alg.Monoid N)
        → Monoids [ to∘from⇒ N ∘ mk-⇒ (toMonoid⇒ (fromMonoid M) (fromMonoid N) (fromMonoid⇒ M N (rawMonoidHomomorphism f))) ]
        ≗ Monoids [ f ∘ to∘from⇒ M ]
    to∘from⇒-commute {_} {N} _ _ = Alg.Monoid.refl N

To∘From : To ∘F From ≃ Id
To∘From = niHelper record
    { η = to∘from⇒
    ; η⁻¹ = to∘from⇐
    ; commute = to∘from⇒-commute
    ; iso = λ M → record
        { isoˡ = to∘from-isoˡ M
        ; isoʳ = to∘from-isoʳ M
        }
    }

-- The category of monoids is equivalent to the category of monoid objects in Setoids
Monoids≈Monoids[Setoids] : StrongEquivalence Monoids Monoids[Setoids]
Monoids≈Monoids[Setoids] = record
    { F = From
    ; G = To
    ; weak-inverse = record
        { F∘G≈id = From∘To
        ; G∘F≈id = To∘From
        }
    }
