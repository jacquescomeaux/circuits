{-# OPTIONS --without-K --safe #-}

module DecorationFunctor.Hypergraph.Labeled where

import Categories.Morphism as Morphism

open import Categories.Category.BinaryProducts using (module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Cocartesian using (Cocartesian; module BinaryCoproducts)
open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.Nat using (Nat-Cocartesian)
open import Categories.Category.Instance.Nat using (Nat)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Instance.SingletonSet using (SingletonSetoid)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor using () renaming (_∘F_ to _∘′_)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor.Monoidal.Symmetric using (module Lax)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)

open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)
open import Category.Instance.Setoids.SymmetricMonoidal using (Setoids-×)
open import Category.Instance.Nat.FinitelyCocomplete using (Nat-FinitelyCocomplete)

open import Data.Empty using (⊥-elim)
open import Data.Fin using (#_)
open import Data.Fin.Base using (Fin; splitAt; join; zero; suc; _↑ˡ_; _↑ʳ_; Fin′; cast)
open import Data.Fin.Patterns using (0F; 1F)
open import Data.Fin.Permutation using (lift₀)
open import Data.Fin.Properties
  using
    ( splitAt-join ; join-splitAt
    ; cast-is-id ; cast-trans ; subst-is-cast
    ; splitAt-↑ˡ ; splitAt-↑ʳ
    ; splitAt⁻¹-↑ˡ ; ↑ˡ-injective
    )
open import Data.Nat using (ℕ; _+_)
open import Data.Product.Base using (_,_; Σ)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-setoid)
open import Data.Sum.Base using (_⊎_; map; inj₁; inj₂; swap; map₂) renaming ([_,_]′ to [_,_])
open import Data.Sum.Properties using (map-map; [,]-map; [,]-∘; [-,]-cong; [,-]-cong; [,]-cong; map-cong; swap-involutive)
open import Data.Unit using (tt)
open import Data.Unit.Properties using () renaming (≡-setoid to ⊤-setoid)

open import Function.Base using (_∘_; id; const; case_of_; case_returning_of_)
open import Function.Bundles using (Func; Inverse; _↔_; mk↔)
open import Function.Construct.Composition using (_↔-∘_)
open import Function.Construct.Identity using (↔-id)
open import Function.Construct.Symmetry using (↔-sym)

open import Level using (0ℓ; lift)

open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≗_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; erefl; refl; sym; trans; cong; cong₂; subst; cong-app)
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence; module ≡-Reasoning; dcong; dcong₂; subst-∘; subst-subst; sym-cong; subst-subst-sym; trans-cong; cong-∘; trans-reflʳ)
open import Relation.Nullary.Negation.Core using (¬_)

open Cartesian (Setoids-Cartesian {0ℓ} {0ℓ}) using (products)
open Cocartesian Nat-Cocartesian using (coproducts)
open FinitelyCocompleteCategory Nat-FinitelyCocomplete
    using ()
    renaming (symmetricMonoidalCategory to Nat-smc)
open Morphism (Setoids 0ℓ 0ℓ) using (_≅_)
open Lax using (SymmetricMonoidalFunctor)

open BinaryProducts products using (-×-)
open BinaryCoproducts coproducts using (-+-) renaming (+-assoc to Nat-+-assoc)

open import Data.Circuit.Gate using (Gate; cast-gate; cast-gate-trans; cast-gate-is-id; subst-is-cast-gate)

record Hypergraph (v : ℕ) : Set where

  field
    h : ℕ
    a : Fin h → ℕ
    j : (e : Fin h) → Fin (a e) → Fin v
    l : (e : Fin h) → Gate (a e)

record Hypergraph-same {n : ℕ} (H H′ : Hypergraph n) : Set where

  open Hypergraph H public
  open Hypergraph H′ renaming (h to h′; a to a′; j to j′; l to l′) public

  field
    ↔h : Fin h ↔ Fin h′

  open Inverse ↔h public

  field
    ≗a : a ≗ a′ ∘ to
    ≗j  : (e : Fin h)
          (i : Fin (a e))
        → j e i
        ≡ j′ (to e) (cast (≗a e) i)
    ≗l  : (e : Fin h)
        → l e
        ≡ cast-gate (sym (≗a e)) (l′ (to e))

private

  variable
    n n′ m m′ o : ℕ
    H H′ H″ H₁ H₁′ : Hypergraph n
    H₂ H₂′ : Hypergraph m
    H₃ : Hypergraph o

Hypergraph-same-refl : Hypergraph-same H H
Hypergraph-same-refl {_} {H} = record
    { ↔h = ↔-id (Fin h)
    ; ≗a = cong a ∘ erefl
    ; ≗j = λ e i → cong (j e) (sym (cast-is-id refl i))
    ; ≗l = λ { e → sym (cast-gate-is-id refl (l e)) }
    }
  where
    open Hypergraph H

sym-sym : {A : Set} {x y : A} (p : x ≡ y) → sym (sym p) ≡ p
sym-sym refl = refl

Hypergraph-same-sym : Hypergraph-same H H′ → Hypergraph-same H′ H
Hypergraph-same-sym {V} {H} {H′} ≡H = record
    { ↔h = ↔-sym ↔h
    ; ≗a = sym ∘ a∘from≗a′
    ; ≗j = ≗j′
    ; ≗l = ≗l′
    }
  where
    open Hypergraph-same ≡H
    open ≡-Reasoning
    a∘from≗a′ : a ∘ from ≗ a′
    a∘from≗a′ x = begin
        (a ∘ from) x        ≡⟨ (≗a ∘ from) x ⟩
        (a′ ∘ to ∘ from) x  ≡⟨ (cong a′ ∘ inverseˡ ∘ erefl ∘ from) x ⟩
        a′ x                ∎
    id≗to∘from : id ≗ to ∘ from
    id≗to∘from e = sym (inverseˡ refl)
    ≗arity′ : a′ ≗ a ∘ from
    ≗arity′ e = sym (a∘from≗a′ e)
    ≗arity- : a′ ≗ a′ ∘ to ∘ from
    ≗arity- e = cong a′ (id≗to∘from e)

    ≗j′ : (e : Fin h′) (i : Fin (a′ e)) → j′ e i ≡ j (from e) (cast (≗arity′ e) i)
    ≗j′ e i = begin
        j′ e i                                                      ≡⟨ dcong₂ j′ (id≗to∘from e) (subst-∘ (id≗to∘from e)) ⟩
        j′ (to (from e)) (subst Fin (cong a′ (id≗to∘from e)) i)     ≡⟨ cong (j′ (to (from e))) (subst-is-cast (cong a′ (id≗to∘from e)) i) ⟩
        j′ (to (from e)) (cast (cong a′ (id≗to∘from e)) i)          ≡⟨⟩
        j′ (to (from e)) (cast (trans (≗arity′ e) (≗a (from e))) i) ≡⟨ cong (j′ (to (from e))) (cast-trans (≗arity′ e) (≗a (from e)) i) ⟨
        j′ (to (from e)) (cast (≗a (from e)) (cast (≗arity′ e) i))  ≡⟨ ≗j (from e) (cast (≗arity′ e) i) ⟨
        j (from e) (cast (≗arity′ e) i)                             ∎

    ≗l′ : (e : Fin h′) → l′ e ≡ cast-gate (sym (sym (a∘from≗a′ e))) (l (from e))
    ≗l′ e = begin
      l′ e                                                                              ≡⟨ dcong l′ (sym (id≗to∘from e)) ⟨
      subst (Gate ∘ a′) (sym (id≗to∘from e)) (l′ (to (from e)))                     ≡⟨ subst-∘ (sym (id≗to∘from e)) ⟩
      subst Gate (cong a′ (sym (id≗to∘from e))) (l′ (to (from e)))                  ≡⟨ subst-is-cast-gate (cong a′ (sym (id≗to∘from e))) (l′ (to (from e))) ⟩
      cast-gate _ (l′ (to (from e)))                                                    ≡⟨ cast-gate-trans _ (sym (sym (a∘from≗a′ e))) (l′ (to (from e))) ⟨
      cast-gate (sym (sym (a∘from≗a′ e))) (cast-gate _ (l′ (to (from e)))) ≡⟨ cong (cast-gate (sym (sym (a∘from≗a′ e)))) (≗l (from e)) ⟨
      cast-gate (sym (sym (a∘from≗a′ e))) (l (from e))                     ∎

Hypergraph-same-trans : Hypergraph-same H H′ → Hypergraph-same H′ H″ → Hypergraph-same H H″
Hypergraph-same-trans ≡H₁ ≡H₂ = record
    { ↔h = ↔h ≡H₂ ↔-∘ ↔h ≡H₁
    ; ≗a = λ { x → trans (≗a ≡H₁ x) (≗a ≡H₂ (to (↔h ≡H₁) x)) }
    ; ≗j = λ { e i → trans (≗j ≡H₁ e i) (≗j₂ e i) }
    ; ≗l = λ { e → trans (≗l ≡H₁ e) (≗l₂ e) }
    }
  where
    open Hypergraph-same
    open Inverse
    open ≡-Reasoning
    ≗j₂ : (e : Fin (h ≡H₁))
          (i : Fin (a ≡H₁ e))
        → j ≡H₂ (to (↔h ≡H₁) e) (cast (≗a ≡H₁ e) i)
        ≡ j′ ≡H₂ (to (↔h ≡H₂) (to (↔h ≡H₁) e)) (cast (trans (≗a ≡H₁ e) (≗a ≡H₂ (to (↔h ≡H₁) e))) i)
    ≗j₂ e i = begin
        j ≡H₂ (to (↔h ≡H₁) e) (cast (≗a ≡H₁ e) i)
            ≡⟨ ≗j ≡H₂ (to (↔h ≡H₁) e) (cast (≗a ≡H₁ e) i) ⟩
        j′ ≡H₂ (to (↔h ≡H₂) (to (↔h ≡H₁) e)) (cast (≗a ≡H₂ (to (↔h ≡H₁) e)) (cast (≗a ≡H₁ e) i))
            ≡⟨ cong (j′ ≡H₂ (to (↔h ≡H₂) (to (↔h ≡H₁) e))) (cast-trans (≗a ≡H₁ e) (≗a ≡H₂ (to (↔h ≡H₁) e)) i) ⟩
        j′ ≡H₂ (to (↔h ≡H₂) (to (↔h ≡H₁) e)) (cast (trans (≗a ≡H₁ e) (≗a ≡H₂ (to (↔h ≡H₁) e))) i) ∎
    ≗l₂ : (e : Fin (h ≡H₁)) → cast-gate _ (l′ ≡H₁ (to ≡H₁ e)) ≡ cast-gate _ (l′ ≡H₂ (to ≡H₂ (to ≡H₁ e)))
    ≗l₂ e = trans (cong (cast-gate _) (≗l ≡H₂ (to ≡H₁ e))) (cast-gate-trans _ (sym (≗a ≡H₁ e)) (l′ ≡H₂ (to ≡H₂ (to ≡H₁ e))))

Hypergraph-setoid : ℕ → Setoid 0ℓ 0ℓ
Hypergraph-setoid p = record
    { Carrier = Hypergraph p
    ; _≈_ = Hypergraph-same
    ; isEquivalence = record
        { refl = Hypergraph-same-refl
        ; sym = Hypergraph-same-sym
        ; trans = Hypergraph-same-trans
        }
    }

map-nodes : (Fin n → Fin m) → Hypergraph n → Hypergraph m
map-nodes f H = record
    { h = h
    ; a = a
    ; j = λ e i → f (j e i)
    ; l = l
    }
  where
    open Hypergraph H

Hypergraph-same-cong
    : (f : Fin n → Fin m)  
    → Hypergraph-same H H′
    → Hypergraph-same (map-nodes f H) (map-nodes f H′)
Hypergraph-same-cong f ≡H = record
    { ↔h = ↔h
    ; ≗a = ≗a
    ; ≗j = λ { e i → cong f (≗j e i) }
    ; ≗l = ≗l
    }
  where
    open Hypergraph-same ≡H

Hypergraph-Func : (Fin n → Fin m) → Func (Hypergraph-setoid n) (Hypergraph-setoid m)
Hypergraph-Func f = record
    { to = map-nodes f
    ; cong = Hypergraph-same-cong f
    }

F-resp-≈
    : {f g : Fin n → Fin m}
    → f ≗ g
    → Hypergraph-same (map-nodes f H) (map-nodes g H)
F-resp-≈ {g = g} f≗g = record
    { ↔h = ↔h
    ; ≗a = ≗a
    ; ≗j = λ { e i → trans (f≗g (j e i)) (cong g (≗j e i)) }
    ; ≗l = ≗l
    }
  where
    open Hypergraph-same Hypergraph-same-refl

homomorphism
    : (f : Fin n → Fin m)
    → (g : Fin m → Fin o)
    → Hypergraph-same (map-nodes (g ∘ f) H) (map-nodes g (map-nodes f H))
homomorphism {n} {m} {o} {H} f g = record
    { ↔h = ↔h
    ; ≗a = ≗a
    ; ≗j = λ e i → cong (g ∘ f) (≗j e i)
    ; ≗l = ≗l
    }
  where
    open Hypergraph-same Hypergraph-same-refl

F : Functor Nat (Setoids 0ℓ 0ℓ)
F = record
    { F₀ = Hypergraph-setoid
    ; F₁ = Hypergraph-Func
    ; identity = λ { {n} {H} → Hypergraph-same-refl {H = H} }
    ; homomorphism = λ { {f = f} {g = g} → homomorphism f g }
    ; F-resp-≈ = λ f≗g → F-resp-≈ f≗g
    }

-- monoidal structure

empty-hypergraph : Hypergraph 0
empty-hypergraph = record
    { h = 0
    ; a = λ ()
    ; j = λ ()
    ; l = λ ()
    }

ε : Func (SingletonSetoid {0ℓ} {0ℓ}) (Hypergraph-setoid 0)
ε = record
    { to = const empty-hypergraph
    ; cong = const Hypergraph-same-refl
    }

module _ (H₁ : Hypergraph n) (H₂ : Hypergraph m) where
  private
    module H₁ = Hypergraph H₁
    module H₂ = Hypergraph H₂
  j+j : (e : Fin (H₁.h + H₂.h))
      → Fin ([ H₁.a , H₂.a ] (splitAt H₁.h e))
      → Fin (n + m)
  j+j e i with splitAt H₁.h e
  ... | inj₁ e₁ = H₁.j e₁ i ↑ˡ m
  ... | inj₂ e₂ = n ↑ʳ H₂.j e₂ i
  l+l : (e : Fin (H₁.h + H₂.h)) → Gate ([ H₁.a , H₂.a ] (splitAt H₁.h e))
  l+l e with splitAt H₁.h e
  ... | inj₁ e₁ = H₁.l e₁
  ... | inj₂ e₂ = H₂.l e₂

together : Hypergraph n → Hypergraph m → Hypergraph (n + m)
together {n} {m} H₁ H₂ = record
    { h = h H₁ + h H₂
    ; a = [ a H₁ , a H₂ ] ∘ splitAt (h H₁)
    ; j = j+j H₁ H₂
    ; l = l+l H₁ H₂
    }
  where
    open Hypergraph

+-resp-↔
    : {n n′ m m′ : ℕ}
    → Fin n ↔ Fin n′
    → Fin m ↔ Fin m′
    → Fin (n + m) ↔ Fin (n′ + m′)
+-resp-↔ {n} {n′} {m} {m′} ↔n ↔m = record
    { to = join n′ m′ ∘ map ↔n.to ↔m.to ∘ splitAt n
    ; from = join n m ∘ map ↔n.from ↔m.from ∘ splitAt n′
    ; to-cong = cong (join n′ m′ ∘ map ↔n.to ↔m.to ∘ splitAt n)
    ; from-cong = cong (join n m ∘ map ↔n.from ↔m.from ∘ splitAt n′)
    ; inverse = (λ { refl → to∘from _ }) , λ { refl → from∘to _ }
    }
  where
    module ↔n = Inverse ↔n
    module ↔m = Inverse ↔m
    open ≡-Reasoning
    to∘from : join n′ m′ ∘ map ↔n.to ↔m.to ∘ splitAt n ∘ join n m ∘ map ↔n.from ↔m.from ∘ splitAt n′ ≗ id
    to∘from x = begin
        (join n′ m′ ∘ map ↔n.to ↔m.to ∘ splitAt n ∘ join n m ∘ map ↔n.from ↔m.from ∘ splitAt n′) x
            ≡⟨ cong
                (join n′ m′ ∘ map ↔n.to ↔m.to)
                (splitAt-join n m (map ↔n.from ↔m.from (splitAt n′ x))) ⟩
        (join n′ m′ ∘ map ↔n.to ↔m.to ∘ map ↔n.from ↔m.from ∘ splitAt n′) x
            ≡⟨ cong (join n′ m′) (map-map (splitAt n′ x)) ⟩
        (join n′ m′ ∘ map (↔n.to ∘ ↔n.from) (↔m.to ∘ ↔m.from) ∘ splitAt n′) x
            ≡⟨ cong
                (join n′ m′)
                (map-cong
                    (λ _ → ↔n.inverseˡ refl)
                    (λ _ → ↔m.inverseˡ refl)
                    (splitAt n′ x)) ⟩
        (join n′ m′ ∘ map id id ∘ splitAt n′) x ≡⟨ [,]-map (splitAt n′ x) ⟩
        (join n′ m′ ∘ splitAt n′) x ≡⟨ join-splitAt n′ m′ x ⟩
        x ∎
    from∘to : join n m ∘ map ↔n.from ↔m.from ∘ splitAt n′ ∘ join n′ m′ ∘ map ↔n.to ↔m.to ∘ splitAt n ≗ id
    from∘to x = begin
        (join n m ∘ map ↔n.from ↔m.from ∘ splitAt n′ ∘ join n′ m′ ∘ map ↔n.to ↔m.to ∘ splitAt n) x
            ≡⟨ cong
                (join n m ∘ map ↔n.from ↔m.from)
                (splitAt-join n′ m′ (map ↔n.to ↔m.to (splitAt n x))) ⟩
        (join n m ∘ map ↔n.from ↔m.from ∘ map ↔n.to ↔m.to ∘ splitAt n) x
            ≡⟨ cong (join n m) (map-map (splitAt n x)) ⟩
        (join n m ∘ map (↔n.from ∘ ↔n.to) (↔m.from ∘ ↔m.to) ∘ splitAt n) x
            ≡⟨ cong
                (join n m)
                (map-cong
                    (λ _ → ↔n.inverseʳ refl)
                    (λ _ → ↔m.inverseʳ refl)
                    (splitAt n x)) ⟩
        (join n m ∘ map id id ∘ splitAt n) x ≡⟨ [,]-map (splitAt n x) ⟩
        (join n m ∘ splitAt n) x ≡⟨ join-splitAt n m x ⟩
        x ∎

together-resp-same
    : Hypergraph-same H₁ H₁′
    → Hypergraph-same H₂ H₂′
    → Hypergraph-same (together H₁ H₂) (together H₁′ H₂′)
together-resp-same {n} {H₁} {H₁′} {m} {H₂} {H₂′} ≡H₁ ≡H₂ = record
    { ↔h = +-resp-↔ ≡H₁.↔h ≡H₂.↔h
    ; ≗a = ≗a
    ; ≗j = ≗j
    ; ≗l = ≗l
    }
  where
    module ≡H₁ = Hypergraph-same ≡H₁
    module ≡H₂ = Hypergraph-same ≡H₂
    module H₁+H₂ = Hypergraph (together H₁ H₂)
    module H₁+H₂′ = Hypergraph (together H₁′ H₂′)
    open ≡-Reasoning
    open Inverse
    open Hypergraph
    ≗a  : [ ≡H₁.a , ≡H₂.a ] ∘ splitAt ≡H₁.h
        ≗ [ ≡H₁.a′ , ≡H₂.a′ ] ∘ splitAt ≡H₁.h′
        ∘ join ≡H₁.h′ ≡H₂.h′ ∘ map ≡H₁.to ≡H₂.to ∘ splitAt ≡H₁.h
    ≗a e = begin
      [ ≡H₁.a , ≡H₂.a ] (splitAt ≡H₁.h e)                         ≡⟨ [,]-cong ≡H₁.≗a ≡H₂.≗a (splitAt ≡H₁.h e) ⟩
      ([ ≡H₁.a′ ∘ ≡H₁.to , ≡H₂.a′ ∘ ≡H₂.to ] ∘ splitAt ≡H₁.h) e   ≡⟨ [,]-map (splitAt ≡H₁.h e) ⟨
      ([ ≡H₁.a′ , ≡H₂.a′ ] ∘ map ≡H₁.to ≡H₂.to ∘ splitAt ≡H₁.h) e ≡⟨ (cong [ ≡H₁.a′ , ≡H₂.a′ ] ∘ splitAt-join ≡H₁.h′ ≡H₂.h′ ∘ map ≡H₁.to ≡H₂.to ∘ splitAt ≡H₁.h) e ⟨
      ([ ≡H₁.a′ , ≡H₂.a′ ] ∘ splitAt ≡H₁.h′ ∘ join ≡H₁.h′ ≡H₂.h′ ∘ map ≡H₁.to ≡H₂.to ∘ splitAt ≡H₁.h) e ∎
    ≗j  : (e : Fin H₁+H₂.h)
          (i : Fin (H₁+H₂.a e))
        → H₁+H₂.j e i
        ≡ H₁+H₂′.j (to (+-resp-↔ ≡H₁.↔h ≡H₂.↔h) e) (cast (≗a e) i)
    ≗j e i with splitAt ≡H₁.h e
    ... | inj₁ e₁ rewrite splitAt-↑ˡ ≡H₁.h′ (≡H₁.to e₁) ≡H₂.h′ = cong (_↑ˡ m) (≡H₁.≗j e₁ i)
    ... | inj₂ e₂ rewrite splitAt-↑ʳ ≡H₁.h′ ≡H₂.h′ (≡H₂.to e₂) = cong (n ↑ʳ_) (≡H₂.≗j e₂ i)
    ≗l : (e : Fin H₁+H₂.h) → l+l H₁ H₂ e ≡ cast-gate (sym (≗a e)) (l+l H₁′ H₂′ (to (+-resp-↔ ≡H₁.↔h ≡H₂.↔h) e))
    ≗l e with splitAt ≡H₁.h e | .{≗a e}
    ... | inj₁ e₁ rewrite splitAt-↑ˡ ≡H₁.h′ (≡H₁.to e₁) ≡H₂.h′ = ≡H₁.≗l e₁
    ... | inj₂ e₂ rewrite splitAt-↑ʳ ≡H₁.h′ ≡H₂.h′ (≡H₂.to e₂) = ≡H₂.≗l e₂

commute
    : (f : Fin n → Fin n′)
    → (g : Fin m → Fin m′)
    → Hypergraph-same
        (together (map-nodes f H₁) (map-nodes g H₂))
        (map-nodes  ([ (_↑ˡ m′) ∘ f , (n′ ↑ʳ_) ∘ g ] ∘ splitAt n) (together H₁ H₂))
commute {n} {n′} {m} {m′} {H₁} {H₂} f g = record
    { ↔h = ≡H₁+H₂.↔h
    ; ≗a = ≡H₁+H₂.≗a
    ; ≗j = ≗j
    ; ≗l = ≗l
    }
  where
    module H₁ = Hypergraph H₁
    module H₂ = Hypergraph H₂
    module H₁+H₂ = Hypergraph (together H₁ H₂)
    module ≡H₁+H₂ = Hypergraph-same {H = together H₁ H₂} Hypergraph-same-refl
    open Hypergraph
    open ≡-Reasoning
    ≗j  : (e : Fin (H₁.h + H₂.h))
          (i : Fin (([ H₁.a , H₂.a ] ∘ splitAt H₁.h) e))
        → j (together (map-nodes f H₁) (map-nodes g H₂)) e i
        ≡ j (map-nodes ([ (_↑ˡ m′) ∘ f , (n′ ↑ʳ_) ∘ g ] ∘ splitAt n) (together H₁ H₂)) (≡H₁+H₂.to e) (cast refl i)
    ≗j e i rewrite (cast-is-id refl i) with splitAt H₁.h e
    ... | inj₁ e₁ rewrite splitAt-↑ˡ n (H₁.j e₁ i) m = refl
    ... | inj₂ e₂ rewrite splitAt-↑ʳ n m (H₂.j e₂ i) = refl
    ≗l  : (e : Fin (H₁.h + H₂.h))
        → l+l (map-nodes f H₁) (map-nodes g H₂) e
        ≡ cast-gate refl (l+l H₁ H₂ (≡H₁+H₂.to e))
    ≗l e rewrite cast-gate-is-id refl (l+l H₁ H₂ (≡H₁+H₂.to e)) with splitAt H₁.h e
    ... | inj₁ e₁ = refl
    ... | inj₂ e₁ = refl

⊗-homomorphism : NaturalTransformation (-×- ∘′ (F ⁂ F)) (F ∘′ -+-)
⊗-homomorphism = record
    { η = λ { (m , n) → η }
    ; commute = λ { (f , g) {H₁ , H₂} → commute {H₁ = H₁} {H₂ = H₂} f g }
    ; sym-commute = λ { (f , g) {H₁ , H₂} → Hypergraph-same-sym (commute {H₁ = H₁} {H₂ = H₂} f g) }
    }
  where
    η : Func (×-setoid (Hypergraph-setoid n) (Hypergraph-setoid m)) (Hypergraph-setoid (n + m))
    η = record
        { to = λ { (H₁ , H₂) → together H₁ H₂ }
        ; cong = λ { (≡H₁ , ≡H₂) → together-resp-same ≡H₁ ≡H₂ }
        }

+-assoc-↔ : ∀ (x y z : ℕ) → Fin (x + y + z) ↔ Fin (x + (y + z))
+-assoc-↔ x y z = record
    { to = to
    ; from = from
    ; to-cong = λ { refl → refl }
    ; from-cong = λ { refl → refl }
    ; inverse = (λ { refl → isoˡ _ }) , λ { refl → isoʳ _ }
    }
  where
    module Nat = Morphism Nat
    open Nat._≅_ (Nat-+-assoc {x} {y} {z})

associativity
    : {X Y Z : ℕ}
    → {H₁ : Hypergraph X}
    → {H₂ : Hypergraph Y}
    → {H₃ : Hypergraph Z}
    → Hypergraph-same
        (map-nodes (Inverse.to (+-assoc-↔ X Y Z)) (together (together H₁ H₂) H₃))
        (together H₁ (together H₂ H₃))
associativity {X} {Y} {Z} {H₁} {H₂} {H₃} = record
    { ↔h = ↔h
    ; ≗a = ≗a
    ; ≗j = ≗j
    ; ≗l = ≗l
    }
  where
    module H₁ = Hypergraph H₁
    module H₂ = Hypergraph H₂
    module H₃ = Hypergraph H₃
    open ≡-Reasoning
    open Hypergraph
    ↔h : Fin (H₁.h + H₂.h + H₃.h) ↔ Fin (H₁.h + (H₂.h + H₃.h))
    ↔h = +-assoc-↔ H₁.h H₂.h H₃.h
    ≗a  : (x : Fin (H₁.h + H₂.h + H₃.h))
        → [ [ H₁.a , H₂.a ] ∘ splitAt H₁.h , H₃.a ] (splitAt (H₁.h + H₂.h) x)
        ≡ [ H₁.a , [ H₂.a , H₃.a ] ∘ splitAt H₂.h ] (splitAt H₁.h ([ [ _↑ˡ H₂.h + H₃.h , (H₁.h ↑ʳ_) ∘ (_↑ˡ H₃.h) ] ∘ splitAt H₁.h , (H₁.h ↑ʳ_) ∘ (H₂.h ↑ʳ_) ] (splitAt (H₁.h + H₂.h) x)))
    ≗a x = begin
        ([ [ H₁.a , H₂.a ] ∘ splitAt H₁.h , H₃.a ] ∘ splitAt (H₁.h + H₂.h)) x
            ≡⟨⟩
        ([ [ H₁.a , [ H₂.a , H₃.a ] ∘ inj₁ ] ∘ splitAt H₁.h , H₃.a ] ∘ splitAt (H₁.h + H₂.h)) x
            ≡⟨ [-,]-cong ([,-]-cong (cong [ H₂.a , H₃.a ] ∘ (λ i → splitAt-↑ˡ H₂.h i H₃.h)) ∘ splitAt H₁.h) (splitAt (H₁.h + H₂.h) x) ⟨
        ([ [ H₁.a , [ H₂.a , H₃.a ] ∘ splitAt H₂.h ∘ (_↑ˡ H₃.h) ] ∘ splitAt H₁.h , H₃.a ] ∘ splitAt (H₁.h + H₂.h)) x
            ≡⟨ [-,]-cong ([,]-∘ [ H₁.a , [ H₂.a , H₃.a ] ∘ splitAt H₂.h ] ∘ splitAt H₁.h) (splitAt (H₁.h + H₂.h) x) ⟨
        ([ [ H₁.a , [ H₂.a , H₃.a ] ∘ splitAt H₂.h ] ∘ map₂ (_↑ˡ H₃.h) ∘ splitAt H₁.h , H₃.a ] ∘ splitAt (H₁.h + H₂.h)) x
            ≡⟨⟩
        ([ [ H₁.a , [ H₂.a , H₃.a ] ∘ splitAt H₂.h ] ∘ map₂ (_↑ˡ H₃.h) ∘ splitAt H₁.h , [ H₂.a , H₃.a ] ∘ inj₂ ] ∘ splitAt (H₁.h + H₂.h)) x
            ≡⟨ [,-]-cong (cong [ H₂.a , H₃.a ] ∘ splitAt-↑ʳ H₂.h H₃.h) (splitAt (H₁.h + H₂.h) x) ⟨
        ([ [ H₁.a , [ H₂.a , H₃.a ] ∘ splitAt H₂.h ] ∘ map₂ (_↑ˡ H₃.h) ∘ splitAt H₁.h , [ H₂.a , H₃.a ] ∘ splitAt H₂.h ∘ (H₂.h ↑ʳ_) ] ∘ splitAt (H₁.h + H₂.h)) x
            ≡⟨⟩
        ([ [ H₁.a , [ H₂.a , H₃.a ] ∘ splitAt H₂.h ] ∘ map₂ (_↑ˡ H₃.h) ∘ splitAt H₁.h , [ H₁.a , [ H₂.a , H₃.a ] ∘ splitAt H₂.h ] ∘ inj₂ ∘ (H₂.h ↑ʳ_) ] ∘ splitAt (H₁.h + H₂.h)) x
            ≡⟨ [,]-∘ [ H₁.a , [ H₂.a , H₃.a ] ∘ splitAt H₂.h ] (splitAt (H₁.h + H₂.h) x) ⟨
        ([ H₁.a , [ H₂.a , H₃.a ] ∘ splitAt H₂.h ] ∘ [ map₂ (_↑ˡ H₃.h) ∘ splitAt H₁.h , inj₂ ∘ (H₂.h ↑ʳ_) ] ∘ splitAt (H₁.h + H₂.h)) x
            ≡⟨ cong [ H₁.a , [ H₂.a , H₃.a ] ∘ splitAt H₂.h ] ([,-]-cong (splitAt-↑ʳ H₁.h (H₂.h + H₃.h) ∘ (H₂.h ↑ʳ_)) (splitAt (H₁.h + H₂.h) x)) ⟨
        ([ H₁.a , [ H₂.a , H₃.a ] ∘ splitAt H₂.h ] ∘ [ map₂ (_↑ˡ H₃.h) ∘ splitAt H₁.h , splitAt H₁.h ∘ (H₁.h ↑ʳ_) ∘ (H₂.h ↑ʳ_) ] ∘ splitAt (H₁.h + H₂.h)) x
            ≡⟨ cong [ H₁.a , [ H₂.a , H₃.a ] ∘ splitAt H₂.h ] ([-,]-cong (splitAt-join H₁.h (H₂.h + H₃.h) ∘ map₂ (_↑ˡ H₃.h) ∘ splitAt H₁.h) (splitAt (H₁.h + H₂.h) x)) ⟨
        ([ H₁.a , [ H₂.a , H₃.a ] ∘ splitAt H₂.h ] ∘ [ splitAt H₁.h ∘ join H₁.h (H₂.h + H₃.h) ∘ map₂ (_↑ˡ H₃.h) ∘ splitAt H₁.h , splitAt H₁.h ∘ (H₁.h ↑ʳ_) ∘ (H₂.h ↑ʳ_) ] ∘ splitAt (H₁.h + H₂.h)) x
            ≡⟨ cong [ H₁.a , [ H₂.a , H₃.a ] ∘ splitAt H₂.h ] ([,]-∘ (splitAt H₁.h) (splitAt (H₁.h + H₂.h) x)) ⟨
        ([ H₁.a , [ H₂.a , H₃.a ] ∘ splitAt H₂.h ] ∘ splitAt H₁.h ∘ [ join H₁.h (H₂.h + H₃.h) ∘ map₂ (_↑ˡ H₃.h) ∘ splitAt H₁.h , (H₁.h ↑ʳ_) ∘ (H₂.h ↑ʳ_) ] ∘ splitAt (H₁.h + H₂.h)) x
            ≡⟨⟩
        ([ H₁.a , [ H₂.a , H₃.a ] ∘ splitAt H₂.h ] ∘ splitAt H₁.h ∘ [ [ _↑ˡ H₂.h + H₃.h , H₁.h ↑ʳ_ ] ∘ [ inj₁ , inj₂ ∘ (_↑ˡ H₃.h) ] ∘ splitAt H₁.h , (H₁.h ↑ʳ_) ∘ (H₂.h ↑ʳ_) ] ∘ splitAt (H₁.h + H₂.h)) x
            ≡⟨ cong ([ H₁.a , [ H₂.a , H₃.a ] ∘ splitAt H₂.h ] ∘ splitAt H₁.h) ([-,]-cong ([,]-∘ [ _↑ˡ H₂.h + H₃.h , H₁.h ↑ʳ_ ] ∘ splitAt H₁.h) (splitAt (H₁.h + H₂.h) x)) ⟩
        ([ H₁.a , [ H₂.a , H₃.a ] ∘ splitAt H₂.h ] ∘ splitAt H₁.h ∘ [ [ _↑ˡ H₂.h + H₃.h , (H₁.h ↑ʳ_) ∘ (_↑ˡ H₃.h) ] ∘ splitAt H₁.h , (H₁.h ↑ʳ_) ∘ (H₂.h ↑ʳ_) ] ∘ splitAt (H₁.h + H₂.h)) x ∎
    ≗j  : (e : Fin (H₁.h + H₂.h + H₃.h))
          (i : Fin ([ [ H₁.a , H₂.a ] ∘ splitAt H₁.h , H₃.a ] (splitAt (H₁.h + H₂.h) e)))
        → Inverse.to (+-assoc-↔ X Y Z) (j+j (together H₁ H₂) H₃ e i)
        ≡ j+j H₁ (together H₂ H₃) (Inverse.to ↔h e) (cast (≗a e) i)
    ≗j e i with splitAt (H₁.h + H₂.h) e
    ≗j e i | inj₁ e₁₂ with splitAt H₁.h e₁₂
    ≗j e i | inj₁ e₁₂ | inj₁ e₁
        rewrite splitAt-↑ˡ H₁.h e₁ (H₂.h + H₃.h)
        rewrite splitAt-↑ˡ (X + Y) (H₁.j e₁ i ↑ˡ Y) Z
        rewrite splitAt-↑ˡ X (H₁.j e₁ i) Y = cong ((_↑ˡ Y + Z) ∘ H₁.j e₁) (sym (cast-is-id refl i))
    ≗j e i | inj₁ e₁₂ | inj₂ e₂
        rewrite splitAt-↑ʳ H₁.h H₂.h e₂
        rewrite splitAt-↑ʳ H₁.h (H₂.h + H₃.h) (e₂ ↑ˡ H₃.h)
        rewrite splitAt-↑ˡ H₂.h e₂ H₃.h
        rewrite splitAt-↑ˡ (X + Y) (X ↑ʳ H₂.j e₂ i) Z
        rewrite splitAt-↑ʳ X Y (H₂.j e₂ i) = cong ((X ↑ʳ_) ∘ (_↑ˡ Z) ∘ H₂.j e₂) (sym (cast-is-id refl i))
    ≗j e i | inj₂ e₃
        rewrite splitAt-↑ʳ H₁.h (H₂.h + H₃.h) (H₂.h ↑ʳ e₃)
        rewrite splitAt-↑ʳ H₂.h H₃.h e₃
        rewrite splitAt-↑ʳ (X + Y) Z (H₃.j e₃ i) = cong ((X ↑ʳ_) ∘ (Y ↑ʳ_) ∘ H₃.j e₃) (sym (cast-is-id refl i))
    ≗l  : (e : Fin (H₁.h + H₂.h + H₃.h))
        → l (map-nodes (Inverse.to (+-assoc-↔ X Y Z)) (together (together H₁ H₂) H₃)) e
        ≡ cast-gate (sym (≗a e)) (l (together H₁ (together H₂ H₃)) (Inverse.to ↔h e))
    ≗l e with splitAt (H₁.h + H₂.h) e
    ≗l e | inj₁ e₁₂ with splitAt H₁.h e₁₂
    ≗l e | inj₁ e₁₂ | inj₁ e₁
        rewrite splitAt-↑ˡ H₁.h e₁ (H₂.h + H₃.h) = sym (cast-gate-is-id refl (H₁.l e₁))
    ≗l e | inj₁ e₁₂ | inj₂ e₂
        rewrite splitAt-↑ʳ H₁.h (H₂.h + H₃.h) (e₂ ↑ˡ H₃.h)
        rewrite splitAt-↑ˡ H₂.h e₂ H₃.h = sym (cast-gate-is-id refl (H₂.l e₂))
    ≗l e | inj₂ e₃
        rewrite splitAt-↑ʳ H₁.h (H₂.h + H₃.h) (H₂.h ↑ʳ e₃)
        rewrite splitAt-↑ʳ H₂.h H₃.h e₃ = sym (cast-gate-is-id refl (H₃.l e₃))

n+0↔n : ∀ n → Fin (n + 0) ↔ Fin n
n+0↔n n = record
    { to = to
    ; from = from
    ; to-cong = λ { refl → refl }
    ; from-cong = λ { refl → refl }
    ; inverse = (λ { refl → to∘from _ }) , λ { refl → from∘to _ }
    }
  where
    to : Fin (n + 0) → Fin n
    to x with inj₁ x₁ ← splitAt n x = x₁
    from : Fin n → Fin (n + 0)
    from x = x ↑ˡ 0
    from∘to : (x : Fin (n + 0)) → from (to x) ≡ x
    from∘to x with inj₁ x₁ ← splitAt n x in eq = splitAt⁻¹-↑ˡ eq
    to∘from : (x : Fin n) → to (from x) ≡ x
    to∘from x rewrite splitAt-↑ˡ n x 0 = refl

unitaryʳ : Hypergraph-same (map-nodes ([ (λ x → x) , (λ ()) ] ∘ splitAt n) (together H empty-hypergraph)) H
unitaryʳ {n} {H} = record
    { ↔h = h+0↔h
    ; ≗a = ≗a
    ; ≗j = ≗j
    ; ≗l = ≗l
    }
  where
    module H = Hypergraph H
    module H+0 = Hypergraph (together H empty-hypergraph)
    h+0↔h : Fin H+0.h ↔ Fin H.h
    h+0↔h = n+0↔n H.h
    ≗a : (e : Fin (H.h + 0)) → [ H.a , (λ ()) ] (splitAt H.h e) ≡ H.a (Inverse.to h+0↔h e)
    ≗a e with inj₁ e₁ ← splitAt H.h e in eq = refl
    ≗j  : (e : Fin (H.h + 0))
          (i : Fin ([ H.a , (λ ()) ] (splitAt H.h e)))
        → [ (λ x → x) , (λ ()) ] (splitAt n (j+j H empty-hypergraph e i))
        ≡ H.j (Inverse.to h+0↔h e) (cast (≗a e) i)
    ≗j e i = ≗j-aux (splitAt H.h e) refl (j+j H empty-hypergraph e) refl (≗a e) i
      where
        ≗j-aux
            : (w : Fin H.h ⊎ Fin 0)
            → (eq₁ : splitAt H.h e ≡ w)
            → (w₁ : Fin ([ H.a , (λ ()) ] w) → Fin (n + 0))
            → j+j H empty-hypergraph e ≡ subst (λ hole → Fin ([ H.a , (λ ()) ] hole) → Fin (n + 0)) (sym eq₁) w₁
            → (w₂ : [ H.a , (λ ()) ] w ≡ H.a (Inverse.to h+0↔h e))
              (i : Fin ([ H.a , (λ ()) ] w))
            → [ (λ x → x) , (λ ()) ] (splitAt n (w₁ i))
            ≡ H.j (Inverse.to h+0↔h e) (cast w₂ i)
        ≗j-aux (inj₁ e₁) eq w₁ eq₁ w₂ i
            with (inj₁ x) ← splitAt n (w₁ i) in eq₂
            rewrite eq = trans
                (↑ˡ-injective 0 x (H.j e₁ i) (trans (splitAt⁻¹-↑ˡ eq₂) (sym (cong-app eq₁ i))))
                (cong (H.j e₁) (sym (cast-is-id refl i)))
    ≗l  : (e : Fin (H.h + 0))
        → l+l H empty-hypergraph e
        ≡ cast-gate (sym (≗a e)) (H.l (Inverse.to h+0↔h e))
    ≗l e with splitAt H.h e | {(≗a e)}
    ... | inj₁ e₁ = sym (cast-gate-is-id refl (H.l e₁))

+-comm-↔ : ∀ (n m : ℕ) → Fin (n + m) ↔ Fin (m + n)
+-comm-↔ n m = record
    { to = join m n ∘ swap ∘ splitAt n
    ; from = join n m ∘ swap ∘ splitAt m
    ; to-cong = λ { refl → refl }
    ; from-cong = λ { refl → refl }
    ; inverse = (λ { refl → to∘from _ }) , λ { refl → from∘to _ }
    }
  where
    open ≡-Reasoning
    to∘from : join m n ∘ swap ∘ splitAt n ∘ join n m ∘ swap ∘ splitAt m ≗ id
    to∘from x = begin
        (join m n ∘ swap ∘ splitAt n ∘ join n m ∘ swap ∘ splitAt m) x ≡⟨ (cong (join m n ∘ swap) ∘ splitAt-join n m ∘ swap ∘ splitAt m) x ⟩
        (join m n ∘ swap ∘ swap ∘ splitAt m) x                        ≡⟨ (cong (join m n) ∘ swap-involutive ∘ splitAt m) x ⟩
        (join m n ∘ splitAt m) x                                      ≡⟨ join-splitAt m n x ⟩
        x                                                             ∎
    from∘to : join n m ∘ swap ∘ splitAt m ∘ join m n ∘ swap ∘ splitAt n ≗ id
    from∘to x = begin
        (join n m ∘ swap ∘ splitAt m ∘ join m n ∘ swap ∘ splitAt n) x ≡⟨ (cong (join n m ∘ swap) ∘ splitAt-join m n ∘ swap ∘ splitAt n) x ⟩
        (join n m ∘ swap ∘ swap ∘ splitAt n) x                        ≡⟨ (cong (join n m) ∘ swap-involutive ∘ splitAt n) x ⟩
        (join n m ∘ splitAt n) x                                      ≡⟨ join-splitAt n m x ⟩
        x                                                             ∎

[,]∘swap : {A B C : Set} {f : A → C} {g : B → C} → [ f , g ] ∘ swap ≗ [ g , f ]
[,]∘swap (inj₁ x) = refl
[,]∘swap (inj₂ y) = refl

braiding
    : {n m : ℕ}
      {H₁ : Hypergraph n}
      {H₂ : Hypergraph m}
    → Hypergraph-same (map-nodes ([ m ↑ʳ_ , _↑ˡ n ] ∘ splitAt n) (together H₁ H₂)) (together H₂ H₁)
braiding {n} {m} {H₁} {H₂} = record
    { ↔h = +-comm-↔ H₁.h H₂.h
    ; ≗a = ≗a
    ; ≗j = ≗j
    ; ≗l = ≗l
    }
  where
    open ≡-Reasoning
    module H₁ = Hypergraph H₁
    module H₂ = Hypergraph H₂
    ≗a  : (e : Fin (H₁.h + H₂.h))
        → [ H₁.a , H₂.a ] (splitAt H₁.h e)
        ≡ [ H₂.a , H₁.a ] (splitAt H₂.h (join H₂.h H₁.h (swap (splitAt H₁.h e))))
    ≗a e = begin
        [ H₁.a , H₂.a ] (splitAt H₁.h e)                                        ≡⟨ [,]∘swap (splitAt H₁.h e) ⟨
        [ H₂.a , H₁.a ] (swap (splitAt H₁.h e))                                 ≡⟨ cong [ H₂.a , H₁.a ] (splitAt-join H₂.h H₁.h (swap (splitAt H₁.h e))) ⟨
        [ H₂.a , H₁.a ] (splitAt H₂.h (join H₂.h H₁.h (swap (splitAt H₁.h e)))) ∎
    ≗j  : (e : Fin (Hypergraph.h (map-nodes ([ m ↑ʳ_ , _↑ˡ n ] ∘ splitAt n) (together H₁ H₂))))
          (i : Fin (Hypergraph.a (map-nodes ([ m ↑ʳ_ , _↑ˡ n ] ∘ splitAt n) (together H₁ H₂)) e))
        → Hypergraph.j (map-nodes ([ _↑ʳ_ m , _↑ˡ n ] ∘ splitAt n) (together H₁ H₂)) e i
        ≡ Hypergraph.j (together H₂ H₁) (Inverse.to (+-comm-↔ H₁.h H₂.h) e) (cast (≗a e) i)
    ≗j e i with splitAt H₁.h e
    ≗j e i | inj₁ e₁
        rewrite splitAt-↑ˡ n (H₁.j e₁ i) m
        rewrite splitAt-↑ʳ H₂.h H₁.h e₁ = cong ((m ↑ʳ_) ∘ H₁.j e₁) (sym (cast-is-id refl i))
    ≗j e i | inj₂ e₂
        rewrite splitAt-↑ʳ n m (H₂.j e₂ i)
        rewrite splitAt-↑ˡ H₂.h e₂ H₁.h = cong ((_↑ˡ n) ∘ H₂.j e₂) (sym (cast-is-id refl i))
    ≗l  : (e : Fin (H₁.h + H₂.h))
        → l+l H₁ H₂ e
        ≡ cast-gate (sym (≗a e)) (l+l H₂ H₁ (Inverse.to (+-comm-↔ H₁.h H₂.h) e))
    ≗l e with splitAt H₁.h e | .{≗a e}
    ≗l e | inj₁ e₁ rewrite splitAt-↑ʳ H₂.h H₁.h e₁ = sym (cast-gate-is-id refl (H₁.l e₁))
    ≗l e | inj₂ e₂ rewrite splitAt-↑ˡ H₂.h e₂ H₁.h = sym (cast-gate-is-id refl (H₂.l e₂))

hypergraph : SymmetricMonoidalFunctor Nat-smc (Setoids-× {0ℓ})
hypergraph = record
    { F = F
    ; isBraidedMonoidal = record
        { isMonoidal = record
            { ε = ε
            ; ⊗-homo = ntHelper record
                { η = λ { (m , n) → η }
                ; commute = λ { (f , g) {H₁ , H₂} → commute {H₁ = H₁} {H₂ = H₂} f g }
                }
            ; associativity = λ { {X} {Y} {Z} {(H₁ , H₂) , H₃} → associativity {X} {Y} {Z} {H₁} {H₂} {H₃} }
            ; unitaryˡ = Hypergraph-same-refl
            ; unitaryʳ = unitaryʳ
            }
        ; braiding-compat = λ { {X} {Y} {H₁ , H₂} → braiding {X} {Y} {H₁} {H₂} }
        }
    }
  where
    η : Func (×-setoid (Hypergraph-setoid n) (Hypergraph-setoid m)) (Hypergraph-setoid (n + m))
    η = record
        { to = λ { (H₁ , H₂) → together H₁ H₂ }
        ; cong = λ { (≡H₁ , ≡H₂) → together-resp-same ≡H₁ ≡H₂ }
        }

module F = SymmetricMonoidalFunctor hypergraph

open Gate

and-gate : Func (SingletonSetoid {0ℓ} {0ℓ}) (F.₀ 3)
and-gate = record
    { to = λ { (lift tt) → and-graph }
    ; cong = λ { (lift tt) → Hypergraph-same-refl }
    }
  where
    and-graph : Hypergraph 3
    and-graph = record
        { h = 1
        ; a = λ { 0F → 3 }
        ; j = λ { 0F → edge-0-nodes }
        ; l = λ { 0F → AND }
        }
      where
        edge-0-nodes : Fin 3 → Fin 3
        edge-0-nodes 0F = # 0
        edge-0-nodes 1F = # 1
        edge-0-nodes 2F = # 2
