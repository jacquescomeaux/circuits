{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Level using (Level; _⊔_)

-- The category of commutative monoids internal to a symmetric monoidal category

module Category.Construction.CMonoids
  {o ℓ e : Level}
  {𝒞 : Category o ℓ e}
  {M : Monoidal 𝒞}
  (symmetric : Symmetric M)
  where

open import Categories.Functor using (Functor)
open import Categories.Morphism.Reasoning 𝒞
open import Object.Monoid.Commutative symmetric

open Category 𝒞
open Monoidal M
open HomReasoning
open CommutativeMonoid⇒

CMonoids : Category (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) e
CMonoids = record
    { Obj = CommutativeMonoid
    ; _⇒_ = CommutativeMonoid⇒
    ; _≈_ = λ f g → arr f ≈ arr g
    ; id = record
        { monoid⇒ = record
            { arr = id
            ; preserves-μ = identityˡ ○ introʳ ⊗.identity
            ; preserves-η = identityˡ
            }
        }
    ; _∘_ = λ f g → record
        { monoid⇒ = record
            { arr = arr f ∘ arr g
            ; preserves-μ = glue (preserves-μ f) (preserves-μ g) ○ ∘-resp-≈ʳ (⟺ ⊗.homomorphism)
            ; preserves-η = glueTrianglesˡ (preserves-η f) (preserves-η g)
            }
        }
    ; assoc = assoc
    ; sym-assoc = sym-assoc
    ; identityˡ = identityˡ
    ; identityʳ = identityʳ
    ; identity² = identity²
    ; equiv = record
      { refl = refl
      ; sym = sym
      ; trans = trans
      }
    ; ∘-resp-≈ = ∘-resp-≈
    }
  where open Equiv
