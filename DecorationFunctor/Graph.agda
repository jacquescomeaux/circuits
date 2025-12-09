{-# OPTIONS --without-K --safe #-}

module DecorationFunctor.Graph where

import Categories.Morphism as Morphism

open import Level using (0ℓ)

open import Categories.Category.BinaryProducts using (module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Instance.Nat using (Nat)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor using () renaming (_∘F_ to _∘′_)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor.Monoidal.Symmetric using (module Lax)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)
open import Category.Instance.Nat.FinitelyCocomplete using (Nat-FinitelyCocomplete)
open import Category.Instance.Setoids.SymmetricMonoidal {0ℓ} {0ℓ} using (Setoids-×; ×-symmetric′)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (#_; Fin; splitAt; join; zero; suc; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Patterns using (0F; 1F)
open import Data.Fin.Properties using (splitAt-join; join-splitAt; splitAt-↑ˡ; splitAt⁻¹-↑ˡ)
open import Data.Nat using (ℕ; _+_)
open import Data.Product.Base using (_,_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-setoid)
open import Data.Setoid.Unit {0ℓ} {0ℓ} using (⊤ₛ)
open import Data.Sum.Base using (_⊎_; map; inj₁; inj₂; swap) renaming ([_,_]′ to [_,_])
open import Data.Sum.Properties using (map-map; [,]-map; [,]-∘; [-,]-cong; [,-]-cong; map-cong; swap-involutive)
open import Data.Unit using (tt)
open import Function using (_∘_; id; const; Func; Inverse; _↔_; mk↔)
open import Function.Construct.Composition using (_↔-∘_)
open import Function.Construct.Constant using () renaming (function to Const)
open import Function.Construct.Identity using (↔-id)
open import Function.Construct.Symmetry using (↔-sym)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (_≗_; _≡_; erefl; refl; sym; trans; cong)
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence; module ≡-Reasoning)
open import Relation.Nullary.Negation.Core using (¬_)

open Cartesian (Setoids-Cartesian {0ℓ} {0ℓ}) using (products)
open FinitelyCocompleteCategory Nat-FinitelyCocomplete
    using (-+-)
    renaming (symmetricMonoidalCategory to Nat-smc; +-assoc to Nat-+-assoc)
open Lax using (SymmetricMonoidalFunctor)
open BinaryProducts products using (-×-)

record Graph (v : ℕ) : Set where

  field
    e : ℕ
    s : Fin e → Fin v
    t : Fin e → Fin v

record Graph-same {n : ℕ} (G G′ : Graph n) : Set where

  open Graph G public
  open Graph G′ renaming (e to e′; s to s′; t to t′) public

  field
    ↔e : Fin e ↔ Fin e′

  open Inverse ↔e public

  field
    ≗s : s ≗ s′ ∘ to
    ≗t : t ≗ t′ ∘ to

private

  variable
    n m o : ℕ
    G G′ G″ G₁ G₁′ : Graph n
    G₂ G₂′ : Graph m
    G₃ : Graph o

Graph-same-refl : Graph-same G G
Graph-same-refl = record
    { ↔e = ↔-id _
    ; ≗s = λ _ → refl
    ; ≗t = λ _ → refl
    }

Graph-same-sym : Graph-same G G′ → Graph-same G′ G
Graph-same-sym ≡G = record
    { ↔e = ↔-sym ↔e
    ; ≗s = sym ∘ s∘from≗s′
    ; ≗t = sym ∘ t∘from≗t′
    }
  where
    open ≡-Reasoning
    open Graph-same ≡G
    s∘from≗s′ : s ∘ from ≗ s′
    s∘from≗s′ x = begin
        s (from x)       ≡⟨ ≗s (from x) ⟩
        s′ (to (from x)) ≡⟨ cong s′ (inverseˡ refl) ⟩
        s′ x             ∎
    t∘from≗t′ : t ∘ from ≗ t′
    t∘from≗t′ x = begin
        t (from x)       ≡⟨ ≗t (from x) ⟩
        t′ (to (from x)) ≡⟨ cong t′ (inverseˡ refl) ⟩
        t′ x             ∎

Graph-same-trans : Graph-same G G′ → Graph-same G′ G″ → Graph-same G G″
Graph-same-trans ≡G₁ ≡G₂ = record
    { ↔e = ↔e ≡G₂ ↔-∘ ↔e ≡G₁
    ; ≗s = λ x → trans (≗s ≡G₁ x) (≗s ≡G₂ _)
    ; ≗t = λ x → trans (≗t ≡G₁ x) (≗t ≡G₂ _)
    }
  where
    open Graph-same

Graph-setoid : ℕ → Setoid 0ℓ 0ℓ
Graph-setoid p = record
    { Carrier = Graph p
    ; _≈_ = Graph-same
    ; isEquivalence = record
        { refl = Graph-same-refl
        ; sym = Graph-same-sym
        ; trans = Graph-same-trans
        }
    }

map-nodes : (Fin n → Fin m) → Graph n → Graph m
map-nodes f G = record
    { e = e
    ; s = f ∘ s
    ; t = f ∘ t
    }
  where
    open Graph G

Graph-same-cong : (f : Fin n → Fin m) → Graph-same G G′ → Graph-same (map-nodes f G) (map-nodes f G′)
Graph-same-cong f ≡G = record
    { ↔e = ↔e
    ; ≗s = cong f ∘ ≗s
    ; ≗t = cong f ∘ ≗t
    }
  where
    open Graph-same ≡G

Graph-Func : (Fin n → Fin m) → Func (Graph-setoid n) (Graph-setoid m)
Graph-Func f = record
    { to = map-nodes f
    ; cong = Graph-same-cong f
    }

F-resp-≈
    : {f g : Fin n → Fin m}
    → (∀ (x : Fin n) → f x ≡ g x)
    → Graph-same (map-nodes f G) (map-nodes g G)
F-resp-≈ {G = G} f≗g = record
    { ↔e = ↔-id _
    ; ≗s = f≗g ∘ s
    ; ≗t = f≗g ∘ t
    }
  where
    open Graph G

F : Functor Nat (Setoids 0ℓ 0ℓ)
F = record
    { F₀ = Graph-setoid
    ; F₁ = Graph-Func
    ; identity = Graph-same-refl
    ; homomorphism = Graph-same-refl
    ; F-resp-≈ = λ f≗g → F-resp-≈ f≗g
    }

discrete : {n : ℕ} → Graph n
discrete = record
    { e = 0
    ; s = λ ()
    ; t = λ ()
    }

ε : Func ⊤ₛ (Graph-setoid 0)
ε = Const ⊤ₛ (Graph-setoid 0) discrete

together : Graph n → Graph m → Graph (n + m)
together {n} {m} G₁ G₂ = record
    { e = e G₁ + e G₂
    ; s = join n m ∘ map (s G₁) (s G₂) ∘ splitAt (e G₁)
    ; t = join n m ∘ map (t G₁) (t G₂) ∘ splitAt (e G₁)
    }
  where
    open Graph

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
    : ∀ {n m : ℕ} {G₁ G₁′ : Graph n} {G₂ G₂′ : Graph m}
    → Graph-same G₁ G₁′
    → Graph-same G₂ G₂′
    → Graph-same (together G₁ G₂) (together G₁′ G₂′)
together-resp-same {n} {m} ≡G₁ ≡G₂ = record
    { ↔e = +-resp-↔ ≡G₁.↔e ≡G₂.↔e
    ; ≗s = ≗s
    ; ≗t = ≗t
    }
  where
    module ≡G₁ = Graph-same ≡G₁
    module ≡G₂ = Graph-same ≡G₂
    open ≡-Reasoning
    module ↔e₁+e₂ = Inverse (+-resp-↔ ≡G₁.↔e ≡G₂.↔e)
    ≗s : join n m ∘ map ≡G₁.s ≡G₂.s ∘ splitAt ≡G₁.e ≗ join n m ∘ map ≡G₁.s′ ≡G₂.s′ ∘ splitAt ≡G₁.e′ ∘ ↔e₁+e₂.to
    ≗s x = begin
        (join n m ∘ map ≡G₁.s ≡G₂.s ∘ splitAt ≡G₁.e) x
            ≡⟨ cong (join n m) (map-cong ≡G₁.≗s ≡G₂.≗s (splitAt ≡G₁.e x)) ⟩
        (join n m ∘ map (≡G₁.s′ ∘ ≡G₁.to) (≡G₂.s′ ∘ ≡G₂.to) ∘ splitAt ≡G₁.e) x
            ≡⟨ cong (join n m) (map-map (splitAt ≡G₁.e x)) ⟨
        (join n m ∘ map ≡G₁.s′ ≡G₂.s′ ∘ map ≡G₁.to ≡G₂.to ∘ splitAt ≡G₁.e) x
            ≡⟨ cong
                (join n m ∘ map ≡G₁.s′ ≡G₂.s′)
                (splitAt-join ≡G₁.e′ ≡G₂.e′ (map ≡G₁.to ≡G₂.to (splitAt ≡G₁.e x))) ⟨
        (join n m ∘ map ≡G₁.s′ ≡G₂.s′ ∘ splitAt ≡G₁.e′ ∘ join ≡G₁.e′ ≡G₂.e′ ∘ map ≡G₁.to ≡G₂.to ∘ splitAt ≡G₁.e) x ≡⟨⟩
        (join n m ∘ map ≡G₁.s′ ≡G₂.s′ ∘ splitAt ≡G₁.e′ ∘ ↔e₁+e₂.to) x ∎
    ≗t : join n m ∘ map ≡G₁.t ≡G₂.t ∘ splitAt ≡G₁.e ≗ join n m ∘ map ≡G₁.t′ ≡G₂.t′ ∘ splitAt ≡G₁.e′ ∘ ↔e₁+e₂.to
    ≗t x = begin
        (join n m ∘ map ≡G₁.t ≡G₂.t ∘ splitAt ≡G₁.e) x
            ≡⟨ cong (join n m) (map-cong ≡G₁.≗t ≡G₂.≗t (splitAt ≡G₁.e x)) ⟩
        (join n m ∘ map (≡G₁.t′ ∘ ≡G₁.to) (≡G₂.t′ ∘ ≡G₂.to) ∘ splitAt ≡G₁.e) x
            ≡⟨ cong (join n m) (map-map (splitAt ≡G₁.e x)) ⟨
        (join n m ∘ map ≡G₁.t′ ≡G₂.t′ ∘ map ≡G₁.to ≡G₂.to ∘ splitAt ≡G₁.e) x
            ≡⟨ cong
                (join n m ∘ map ≡G₁.t′ ≡G₂.t′)
                (splitAt-join ≡G₁.e′ ≡G₂.e′ (map ≡G₁.to ≡G₂.to (splitAt ≡G₁.e x))) ⟨
        (join n m ∘ map ≡G₁.t′ ≡G₂.t′ ∘ splitAt ≡G₁.e′ ∘ join ≡G₁.e′ ≡G₂.e′ ∘ map ≡G₁.to ≡G₂.to ∘ splitAt ≡G₁.e) x ≡⟨⟩
        (join n m ∘ map ≡G₁.t′ ≡G₂.t′ ∘ splitAt ≡G₁.e′ ∘ ↔e₁+e₂.to) x ∎

commute
    : ∀ {n n′ m m′}
    → {G₁ : Graph n}
    → {G₂ : Graph m}
    → (f : Fin n → Fin n′)
    → (g : Fin m → Fin m′)
    → Graph-same
        (together (map-nodes f G₁) (map-nodes g G₂))
        (map-nodes  ([ (_↑ˡ m′) ∘ f , (n′ ↑ʳ_) ∘ g ] ∘ splitAt n) (together G₁ G₂))
commute {n} {n′} {m} {m′} {G₁} {G₂} f g = record
    { ↔e = ↔e
    ; ≗s = source-commute
    ; ≗t = target-commute
    }
  where
    open Graph-same (Graph-same-refl {_} {together G₁ G₂})
    module G₁ = Graph G₁
    module G₂ = Graph G₂
    module fG₁ = Graph (map-nodes f G₁)
    module gG₂ = Graph (map-nodes g G₂)
    module G₁+G₂ = Graph (together G₁ G₂)
    module fG₁+gG₂ = Graph (together (map-nodes f G₁) (map-nodes g G₂))
    open ≡-Reasoning
    source-commute
        : fG₁+gG₂.s
        ≗ [ (_↑ˡ m′) ∘ f , (n′ ↑ʳ_) ∘ g ] ∘ splitAt n
        ∘ G₁+G₂.s
        ∘ to
    source-commute x = begin
        fG₁+gG₂.s x
            ≡⟨⟩
        (join n′ m′ ∘ map fG₁.s gG₂.s ∘ splitAt G₁.e ∘ to) x
            ≡⟨ cong (join n′ m′) (map-map ((splitAt G₁.e ∘ to) x)) ⟨
        (join n′ m′ ∘ map f g ∘ map G₁.s G₂.s ∘ splitAt fG₁.e ∘ to) x
            ≡⟨ [,]-map ((map G₁.s G₂.s ∘ splitAt fG₁.e ∘ to) x) ⟩
        ([ (_↑ˡ m′) ∘ f , (n′ ↑ʳ_) ∘ g ] ∘ map G₁.s G₂.s ∘ splitAt fG₁.e ∘ to) x
            ≡⟨ cong [ (_↑ˡ m′) ∘ f , (n′ ↑ʳ_) ∘ g ] (splitAt-join n m (map G₁.s G₂.s (splitAt fG₁.e (to x)))) ⟨
        ([ (_↑ˡ m′) ∘ f , (n′ ↑ʳ_) ∘ g ] ∘ splitAt n ∘ join n m ∘ map G₁.s G₂.s ∘ splitAt fG₁.e ∘ to) x
            ≡⟨⟩
        ([ (_↑ˡ m′) ∘ f , (n′ ↑ʳ_) ∘ g ] ∘ splitAt n ∘ G₁+G₂.s ∘ to) x ∎
    target-commute
        : fG₁+gG₂.t
        ≗ [ (_↑ˡ m′) ∘ f , (n′ ↑ʳ_) ∘ g ] ∘ splitAt n
        ∘ G₁+G₂.t
        ∘ to
    target-commute x = begin
        fG₁+gG₂.t x
            ≡⟨⟩
        (join n′ m′ ∘ map fG₁.t gG₂.t ∘ splitAt G₁.e ∘ to) x
            ≡⟨ cong (join n′ m′) (map-map ((splitAt G₁.e ∘ to) x)) ⟨
        (join n′ m′ ∘ map f g ∘ map G₁.t G₂.t ∘ splitAt fG₁.e ∘ to) x
            ≡⟨ [,]-map ((map G₁.t G₂.t ∘ splitAt fG₁.e ∘ to) x) ⟩
        ([ (_↑ˡ m′) ∘ f , (n′ ↑ʳ_) ∘ g ] ∘ map G₁.t G₂.t ∘ splitAt fG₁.e ∘ to) x
            ≡⟨ cong [ (_↑ˡ m′) ∘ f , (n′ ↑ʳ_) ∘ g ] (splitAt-join n m (map G₁.t G₂.t (splitAt fG₁.e (to x)))) ⟨
        ([ (_↑ˡ m′) ∘ f , (n′ ↑ʳ_) ∘ g ] ∘ splitAt n ∘ join n m ∘ map G₁.t G₂.t ∘ splitAt fG₁.e ∘ to) x
            ≡⟨⟩
        ([ (_↑ˡ m′) ∘ f , (n′ ↑ʳ_) ∘ g ] ∘ splitAt n ∘ G₁+G₂.t ∘ to) x ∎


⊗-homomorphism : NaturalTransformation (-×- ∘′ (F ⁂ F)) (F ∘′ -+-)
⊗-homomorphism = ntHelper record
    { η = λ { (n , m) → η {n} {m} }
    ; commute = λ { (f , g) {G₁ , G₂} → commute {G₁ = G₁} {G₂ = G₂} f g }
    }
  where
    η : Func (×-setoid (Graph-setoid n) (Graph-setoid m)) (Graph-setoid (n + m))
    η = record
        { to = λ { (G₁ , G₂) → together G₁ G₂ }
        ; cong = λ { (≡G₁ , ≡G₂) → together-resp-same ≡G₁ ≡G₂ }
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
    → (G₁ : Graph X)
    → (G₂ : Graph Y)
    → (G₃ : Graph Z)
    → Graph-same
        (map-nodes (Inverse.to (+-assoc-↔ X Y Z)) (together (together G₁ G₂) G₃))
        (together G₁ (together G₂ G₃))
associativity {X} {Y} {Z} G₁ G₂ G₃ = record
    { ↔e = ↔e
    ; ≗s = ≗s
    ; ≗t = ≗t
    }
  where
    module G₁ = Graph G₁
    module G₂ = Graph G₂
    module G₃ = Graph G₃
    module G₂+G₃ = Graph (together G₂ G₃)
    module G₁+[G₂+G₃] = Graph (together G₁ (together G₂ G₃))
    module G₁+G₂+G₃ = Graph (together (together G₁ G₂) G₃)
    ↔e : Fin (G₁.e + G₂.e + G₃.e) ↔ Fin (G₁.e + (G₂.e + G₃.e))
    ↔e = +-assoc-↔ G₁.e G₂.e G₃.e
    open ≡-Reasoning
    open Inverse
    ≗s : to (+-assoc-↔ X Y Z) ∘ G₁+G₂+G₃.s ≗ G₁+[G₂+G₃].s ∘ to ↔e
    ≗s x = begin
        (to (+-assoc-↔ X Y Z) ∘ G₁+G₂+G₃.s) x                                  ≡⟨⟩
        ([ [ join X (Y + Z) ∘ inj₁ , join X (Y + Z) ∘ inj₂ ∘ _ ] ∘ splitAt X , _ ] ∘ splitAt (X + Y) ∘ G₁+G₂+G₃.s) x
            ≡⟨ [-,]-cong ([,]-∘ (join X (Y + Z)) ∘ splitAt X) (splitAt (X + Y) (G₁+G₂+G₃.s x)) ⟨
        ([ join X (Y + Z) ∘ map id _ ∘ splitAt X , join X (Y + Z) ∘ inj₂ ∘ _ ] ∘ splitAt (X + Y) ∘ G₁+G₂+G₃.s) x
            ≡⟨ [,]-∘ (join X (Y + Z)) (splitAt (X + Y) (G₁+G₂+G₃.s x)) ⟨
        (join X (Y + Z) ∘ [ map id _ ∘ splitAt X , inj₂ ∘ join Y Z ∘ inj₂ ] ∘ splitAt (X + Y) ∘ G₁+G₂+G₃.s) x ≡⟨⟩
        (join X (Y + Z) ∘ [ map id _ ∘ splitAt X , inj₂ ∘ join Y Z ∘ inj₂ ] ∘ splitAt (X + Y) ∘ join (X + Y) Z ∘ map _ G₃.s ∘ splitAt _) x
            ≡⟨ cong
                (join X (Y + Z) ∘ [ map id _ ∘ splitAt X , inj₂ ∘ join Y Z ∘ inj₂ ])
                (splitAt-join (X + Y) Z (map _ G₃.s (splitAt _ x))) ⟩
        (join X (Y + Z) ∘ [ map id _ ∘ splitAt X , inj₂ ∘ join Y Z ∘ inj₂ ] ∘ map _ G₃.s ∘ splitAt _) x
            ≡⟨ cong (join X (Y + Z)) ([,]-map (splitAt (G₁.e + G₂.e) x)) ⟩
        (join X (Y + Z) ∘ [ map id _ ∘ splitAt X ∘ join X Y ∘ map G₁.s G₂.s ∘ splitAt _ , inj₂ ∘ join Y Z ∘ inj₂ ∘ G₃.s ] ∘ splitAt _) x
            ≡⟨ cong
                (join X (Y + Z))
                ([-,]-cong
                    (cong (map id (_↑ˡ Z)) ∘ splitAt-join X Y ∘ map G₁.s G₂.s ∘ splitAt G₁.e)
                    (splitAt (G₁.e + G₂.e) x)) ⟩
        (join X (Y + Z) ∘ [ map id _ ∘ map G₁.s G₂.s ∘ splitAt _ , inj₂ ∘ join Y Z ∘ inj₂ ∘ G₃.s ] ∘ splitAt _) x
          ≡⟨ cong (join X (Y + Z)) ([-,]-cong (map-map ∘ splitAt G₁.e) (splitAt _ x)) ⟩
        (join X (Y + Z) ∘ [ map G₁.s (join Y Z ∘ inj₁ ∘ G₂.s) ∘ splitAt _ , inj₂ ∘ _ ] ∘ splitAt _) x ≡⟨⟩
        (join X (Y + Z) ∘ [ map G₁.s (join Y Z ∘ map G₂.s G₃.s ∘ inj₁) ∘ splitAt _ , _ ] ∘ splitAt _) x
          ≡⟨ cong
              (join X (Y + Z))
              ([-,]-cong
                  (map-cong (cong G₁.s ∘ erefl) (cong (join Y Z ∘ map G₂.s G₃.s) ∘ splitAt-join G₂.e G₃.e ∘ inj₁) ∘ splitAt _)
                  (splitAt (G₁.e + G₂.e) x)) ⟨
        (join X (Y + Z) ∘ [ map G₁.s (join Y Z ∘ map G₂.s G₃.s ∘ splitAt G₂.e ∘ _) ∘ splitAt _ , _ ] ∘ splitAt _) x ≡⟨⟩
        (join X (Y + Z) ∘ [ map G₁.s (G₂+G₃.s ∘ _) ∘ splitAt _ , inj₂ ∘ join Y Z ∘ inj₂ ∘ G₃.s ] ∘ splitAt _) x ≡⟨⟩
        (join X (Y + Z) ∘ [ map G₁.s (G₂+G₃.s ∘ _) ∘ splitAt _ , inj₂ ∘ join Y Z ∘ map G₂.s G₃.s ∘ inj₂ ] ∘ splitAt _) x
          ≡⟨ cong
              (join X (Y + Z))
              ([,-]-cong
                  (cong (inj₂ ∘ join Y Z ∘ map G₂.s G₃.s) ∘ splitAt-join G₂.e G₃.e ∘ inj₂)
                  (splitAt (G₁.e + G₂.e) x)) ⟨
        (join X (Y + Z) ∘ [ map G₁.s _ ∘ splitAt _ , inj₂ ∘ join Y Z ∘ map G₂.s G₃.s ∘ splitAt G₂.e ∘ (G₂.e ↑ʳ_) ] ∘ splitAt _) x ≡⟨⟩
        (join X (Y + Z) ∘ [ map G₁.s _ ∘ splitAt _ , inj₂ ∘ G₂+G₃.s ∘ (G₂.e ↑ʳ_) ] ∘ splitAt _) x ≡⟨⟩
        (join X (Y + Z) ∘ [ map G₁.s _ ∘ splitAt _ , map G₁.s G₂+G₃.s ∘ inj₂ ∘ (G₂.e ↑ʳ_) ] ∘ splitAt _) x
          ≡⟨ cong
              (join X (Y + Z))
              ([-,]-cong
                  (map-map ∘ splitAt G₁.e)
                  (splitAt (G₁.e + G₂.e) x)) ⟨
        (join X (Y + Z) ∘ [ map G₁.s G₂+G₃.s ∘ map id (_↑ˡ G₃.e) ∘ splitAt _ , map G₁.s G₂+G₃.s ∘ inj₂ ∘ (G₂.e ↑ʳ_) ] ∘ splitAt _) x
            ≡⟨ cong (join X (Y + Z)) ([,]-∘ (map G₁.s G₂+G₃.s) (splitAt (G₁.e + G₂.e) x)) ⟨
        (join X (Y + Z) ∘ map G₁.s G₂+G₃.s ∘ [ map id (_↑ˡ G₃.e) ∘ splitAt _ , inj₂ ∘ (G₂.e ↑ʳ_) ] ∘ splitAt _) x
            ≡⟨ cong
                (join X (Y + Z) ∘ map G₁.s G₂+G₃.s)
                (splitAt-join G₁.e G₂+G₃.e (([ map id _ ∘ splitAt _ , inj₂ ∘ (G₂.e ↑ʳ_) ] ∘ splitAt _) x)) ⟨
        (join X (Y + Z) ∘ map G₁.s G₂+G₃.s ∘ splitAt G₁.e ∘ join G₁.e G₂+G₃.e ∘ [ map id _ ∘ splitAt _ , inj₂ ∘ (G₂.e ↑ʳ_) ] ∘ splitAt _) x ≡⟨⟩
        (G₁+[G₂+G₃].s ∘ join G₁.e G₂+G₃.e ∘ [ map id _ ∘ splitAt _ , inj₂ ∘ (G₂.e ↑ʳ_) ] ∘ splitAt _) x
            ≡⟨ cong G₁+[G₂+G₃].s ([,]-∘ (join G₁.e G₂+G₃.e) (splitAt (G₁.e + G₂.e) x)) ⟩
        (G₁+[G₂+G₃].s ∘ [ join G₁.e G₂+G₃.e ∘ map id (_↑ˡ G₃.e) ∘ splitAt _ , join G₁.e G₂+G₃.e ∘ inj₂ ∘ (G₂.e ↑ʳ_) ] ∘ splitAt _) x
            ≡⟨ cong G₁+[G₂+G₃].s ([-,]-cong ([,]-map ∘ splitAt G₁.e) (splitAt (G₁.e + G₂.e) x)) ⟩
        (G₁+[G₂+G₃].s ∘ [ [ _↑ˡ G₂.e + G₃.e , (G₁.e ↑ʳ_) ∘ (_↑ˡ G₃.e) ] ∘ splitAt G₁.e , (G₁.e ↑ʳ_) ∘ (G₂.e ↑ʳ_) ] ∘ splitAt _) x ≡⟨⟩
        (G₁+[G₂+G₃].s ∘ to (+-assoc-↔ G₁.e G₂.e G₃.e)) x  ∎
    ≗t : to (+-assoc-↔ X Y Z) ∘ G₁+G₂+G₃.t ≗ G₁+[G₂+G₃].t ∘ to ↔e
    ≗t x = begin
        (to (+-assoc-↔ X Y Z) ∘ G₁+G₂+G₃.t) x                                  ≡⟨⟩
        ([ [ join X (Y + Z) ∘ inj₁ , join X (Y + Z) ∘ inj₂ ∘ _ ] ∘ splitAt X , _ ] ∘ splitAt (X + Y) ∘ G₁+G₂+G₃.t) x
            ≡⟨ [-,]-cong ([,]-∘ (join X (Y + Z)) ∘ splitAt X) (splitAt (X + Y) (G₁+G₂+G₃.t x)) ⟨
        ([ join X (Y + Z) ∘ map id _ ∘ splitAt X , join X (Y + Z) ∘ inj₂ ∘ _ ] ∘ splitAt (X + Y) ∘ G₁+G₂+G₃.t) x
            ≡⟨ [,]-∘ (join X (Y + Z)) (splitAt (X + Y) (G₁+G₂+G₃.t x)) ⟨
        (join X (Y + Z) ∘ [ map id _ ∘ splitAt X , inj₂ ∘ join Y Z ∘ inj₂ ] ∘ splitAt (X + Y) ∘ G₁+G₂+G₃.t) x ≡⟨⟩
        (join X (Y + Z) ∘ [ map id _ ∘ splitAt X , inj₂ ∘ join Y Z ∘ inj₂ ] ∘ splitAt (X + Y) ∘ join (X + Y) Z ∘ map _ G₃.t ∘ splitAt _) x
            ≡⟨ cong
                (join X (Y + Z) ∘ [ map id _ ∘ splitAt X , inj₂ ∘ join Y Z ∘ inj₂ ])
                (splitAt-join (X + Y) Z (map _ G₃.t (splitAt _ x))) ⟩
        (join X (Y + Z) ∘ [ map id _ ∘ splitAt X , inj₂ ∘ join Y Z ∘ inj₂ ] ∘ map _ G₃.t ∘ splitAt _) x
            ≡⟨ cong (join X (Y + Z)) ([,]-map (splitAt (G₁.e + G₂.e) x)) ⟩
        (join X (Y + Z) ∘ [ map id _ ∘ splitAt X ∘ join X Y ∘ map G₁.t G₂.t ∘ splitAt _ , inj₂ ∘ join Y Z ∘ inj₂ ∘ G₃.t ] ∘ splitAt _) x
            ≡⟨ cong
                (join X (Y + Z))
                ([-,]-cong
                    (cong (map id (_↑ˡ Z)) ∘ splitAt-join X Y ∘ map G₁.t G₂.t ∘ splitAt G₁.e)
                    (splitAt (G₁.e + G₂.e) x)) ⟩
        (join X (Y + Z) ∘ [ map id _ ∘ map G₁.t G₂.t ∘ splitAt _ , inj₂ ∘ join Y Z ∘ inj₂ ∘ G₃.t ] ∘ splitAt _) x
          ≡⟨ cong (join X (Y + Z)) ([-,]-cong (map-map ∘ splitAt G₁.e) (splitAt _ x)) ⟩
        (join X (Y + Z) ∘ [ map G₁.t (join Y Z ∘ inj₁ ∘ G₂.t) ∘ splitAt _ , inj₂ ∘ _ ] ∘ splitAt _) x ≡⟨⟩
        (join X (Y + Z) ∘ [ map G₁.t (join Y Z ∘ map G₂.t G₃.t ∘ inj₁) ∘ splitAt _ , _ ] ∘ splitAt _) x
          ≡⟨ cong
              (join X (Y + Z))
              ([-,]-cong
                  (map-cong (cong G₁.t ∘ erefl) (cong (join Y Z ∘ map G₂.t G₃.t) ∘ splitAt-join G₂.e G₃.e ∘ inj₁) ∘ splitAt _)
                  (splitAt (G₁.e + G₂.e) x)) ⟨
        (join X (Y + Z) ∘ [ map G₁.t (join Y Z ∘ map G₂.t G₃.t ∘ splitAt G₂.e ∘ _) ∘ splitAt _ , _ ] ∘ splitAt _) x ≡⟨⟩
        (join X (Y + Z) ∘ [ map G₁.t (G₂+G₃.t ∘ _) ∘ splitAt _ , inj₂ ∘ join Y Z ∘ inj₂ ∘ G₃.t ] ∘ splitAt _) x ≡⟨⟩
        (join X (Y + Z) ∘ [ map G₁.t (G₂+G₃.t ∘ _) ∘ splitAt _ , inj₂ ∘ join Y Z ∘ map G₂.t G₃.t ∘ inj₂ ] ∘ splitAt _) x
          ≡⟨ cong
              (join X (Y + Z))
              ([,-]-cong
                  (cong (inj₂ ∘ join Y Z ∘ map G₂.t G₃.t) ∘ splitAt-join G₂.e G₃.e ∘ inj₂)
                  (splitAt (G₁.e + G₂.e) x)) ⟨
        (join X (Y + Z) ∘ [ map G₁.t _ ∘ splitAt _ , inj₂ ∘ join Y Z ∘ map G₂.t G₃.t ∘ splitAt G₂.e ∘ (G₂.e ↑ʳ_) ] ∘ splitAt _) x ≡⟨⟩
        (join X (Y + Z) ∘ [ map G₁.t _ ∘ splitAt _ , inj₂ ∘ G₂+G₃.t ∘ (G₂.e ↑ʳ_) ] ∘ splitAt _) x ≡⟨⟩
        (join X (Y + Z) ∘ [ map G₁.t _ ∘ splitAt _ , map G₁.t G₂+G₃.t ∘ inj₂ ∘ (G₂.e ↑ʳ_) ] ∘ splitAt _) x
          ≡⟨ cong
              (join X (Y + Z))
              ([-,]-cong
                  (map-map ∘ splitAt G₁.e)
                  (splitAt (G₁.e + G₂.e) x)) ⟨
        (join X (Y + Z) ∘ [ map G₁.t G₂+G₃.t ∘ map id (_↑ˡ G₃.e) ∘ splitAt _ , map G₁.t G₂+G₃.t ∘ inj₂ ∘ (G₂.e ↑ʳ_) ] ∘ splitAt _) x
            ≡⟨ cong (join X (Y + Z)) ([,]-∘ (map G₁.t G₂+G₃.t) (splitAt (G₁.e + G₂.e) x)) ⟨
        (join X (Y + Z) ∘ map G₁.t G₂+G₃.t ∘ [ map id (_↑ˡ G₃.e) ∘ splitAt _ , inj₂ ∘ (G₂.e ↑ʳ_) ] ∘ splitAt _) x
            ≡⟨ cong
                (join X (Y + Z) ∘ map G₁.t G₂+G₃.t)
                (splitAt-join G₁.e G₂+G₃.e (([ map id _ ∘ splitAt _ , inj₂ ∘ (G₂.e ↑ʳ_) ] ∘ splitAt _) x)) ⟨
        (join X (Y + Z) ∘ map G₁.t G₂+G₃.t ∘ splitAt G₁.e ∘ join G₁.e G₂+G₃.e ∘ [ map id _ ∘ splitAt _ , inj₂ ∘ (G₂.e ↑ʳ_) ] ∘ splitAt _) x ≡⟨⟩
        (G₁+[G₂+G₃].t ∘ join G₁.e G₂+G₃.e ∘ [ map id _ ∘ splitAt _ , inj₂ ∘ (G₂.e ↑ʳ_) ] ∘ splitAt _) x
            ≡⟨ cong G₁+[G₂+G₃].t ([,]-∘ (join G₁.e G₂+G₃.e) (splitAt (G₁.e + G₂.e) x)) ⟩
        (G₁+[G₂+G₃].t ∘ [ join G₁.e G₂+G₃.e ∘ map id (_↑ˡ G₃.e) ∘ splitAt _ , join G₁.e G₂+G₃.e ∘ inj₂ ∘ (G₂.e ↑ʳ_) ] ∘ splitAt _) x
            ≡⟨ cong G₁+[G₂+G₃].t ([-,]-cong ([,]-map ∘ splitAt G₁.e) (splitAt (G₁.e + G₂.e) x)) ⟩
        (G₁+[G₂+G₃].t ∘ [ [ _↑ˡ G₂.e + G₃.e , (G₁.e ↑ʳ_) ∘ (_↑ˡ G₃.e) ] ∘ splitAt G₁.e , (G₁.e ↑ʳ_) ∘ (G₂.e ↑ʳ_) ] ∘ splitAt _) x ≡⟨⟩
        (G₁+[G₂+G₃].t ∘ to (+-assoc-↔ G₁.e G₂.e G₃.e)) x  ∎

unitaryˡ : Graph-same (together (discrete {0}) G) G
unitaryˡ = Graph-same-refl

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

unitaryʳ
    : {G : Graph n}
    → Graph-same (map-nodes ([ (λ x → x) , (λ ()) ] ∘ splitAt n) (together G discrete)) G
unitaryʳ {n} {G} = record
    { ↔e = e+0↔e
    ; ≗s = ≗s+0
    ; ≗t = ≗t+0
    }
  where
    open Graph G
    open ≡-Reasoning
    e+0↔e : Fin (e + 0) ↔ Fin e
    e+0↔e = n+0↔n e
    module e+0↔e = Inverse e+0↔e
    ≗s+0 : [ id , (λ ()) ] ∘ splitAt n ∘ join n 0 ∘ map s (λ ()) ∘ splitAt e ≗ s ∘ e+0↔e.to
    ≗s+0 x+0 with inj₁ x ← splitAt e x+0 = cong [ id , (λ ()) ] (splitAt-↑ˡ n (s x) 0)
    ≗t+0 : [ id , (λ ()) ] ∘ splitAt n ∘ join n 0 ∘ map t (λ ()) ∘ splitAt e ≗ t ∘ e+0↔e.to
    ≗t+0 x+0 with inj₁ x ← splitAt e x+0 = cong [ id , (λ ()) ] (splitAt-↑ˡ n (t x) 0)

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

swap-map
    : {A B C D : Set}
    → {f : A → C} {g : B → D}
    → swap ∘ map f g ≗ map g f ∘ swap
swap-map (inj₁ _) = refl
swap-map (inj₂ _) = refl

join-swap : ∀ {x y : ℕ} →  join x y ∘ swap ≗ [ x ↑ʳ_  , _↑ˡ y ]
join-swap (inj₁ x) = refl
join-swap (inj₂ y) = refl

braiding
    : {G₁ : Graph n}
    → {G₂ : Graph m}
    → Graph-same (map-nodes ([ m ↑ʳ_ , _↑ˡ n ] ∘ splitAt n) (together G₁ G₂)) (together G₂ G₁)
braiding {n} {m} {G₁} {G₂} = record
    { ↔e = +-comm-↔ G₁.e G₂.e
    ; ≗s = ≗s
    ; ≗t = ≗t
    }
  where
    open ≡-Reasoning
    module G₁ = Graph G₁
    module G₂ = Graph G₂
    ≗s : [ m ↑ʳ_  , _↑ˡ n ] ∘ splitAt n
        ∘ join n m ∘ map G₁.s G₂.s ∘ splitAt G₁.e
        ≗ join m n ∘ map G₂.s G₁.s ∘ splitAt G₂.e
        ∘ Inverse.to (+-comm-↔ G₁.e G₂.e)
    ≗s x = begin
        ([ m ↑ʳ_  , _↑ˡ n ] ∘ splitAt n ∘ join n m ∘ map G₁.s G₂.s ∘ splitAt G₁.e) x
            ≡⟨ (join-swap ∘ splitAt n ∘ join n m ∘ map G₁.s G₂.s ∘ splitAt G₁.e) x ⟨
        (join m n ∘ swap ∘ splitAt n ∘ join n m ∘ map G₁.s G₂.s ∘ splitAt G₁.e) x
            ≡⟨ (cong (join m n ∘ swap) ∘ splitAt-join n m ∘ map G₁.s G₂.s ∘ splitAt G₁.e) x ⟩
        (join m n ∘ swap ∘ map G₁.s G₂.s ∘ splitAt G₁.e) x
            ≡⟨ (cong (join m n) ∘ swap-map ∘ splitAt G₁.e) x ⟩
        (join m n ∘ map G₂.s G₁.s ∘ swap ∘ splitAt G₁.e) x
            ≡⟨ (cong (join m n ∘ map G₂.s G₁.s) ∘ splitAt-join G₂.e G₁.e ∘ swap ∘ splitAt G₁.e) x ⟨
        (join m n ∘ map G₂.s G₁.s ∘ splitAt G₂.e ∘ join G₂.e G₁.e ∘ swap ∘ splitAt G₁.e) x ∎
    ≗t : [ m ↑ʳ_  , _↑ˡ n ] ∘ splitAt n
        ∘ join n m ∘ map G₁.t G₂.t ∘ splitAt G₁.e
        ≗ join m n ∘ map G₂.t G₁.t ∘ splitAt G₂.e
        ∘ Inverse.to (+-comm-↔ G₁.e G₂.e)
    ≗t x = begin
        ([ m ↑ʳ_  , _↑ˡ n ] ∘ splitAt n ∘ join n m ∘ map G₁.t G₂.t ∘ splitAt G₁.e) x
            ≡⟨ (join-swap ∘ splitAt n ∘ join n m ∘ map G₁.t G₂.t ∘ splitAt G₁.e) x ⟨
        (join m n ∘ swap ∘ splitAt n ∘ join n m ∘ map G₁.t G₂.t ∘ splitAt G₁.e) x
            ≡⟨ (cong (join m n ∘ swap) ∘ splitAt-join n m ∘ map G₁.t G₂.t ∘ splitAt G₁.e) x ⟩
        (join m n ∘ swap ∘ map G₁.t G₂.t ∘ splitAt G₁.e) x
            ≡⟨ (cong (join m n) ∘ swap-map ∘ splitAt G₁.e) x ⟩
        (join m n ∘ map G₂.t G₁.t ∘ swap ∘ splitAt G₁.e) x
            ≡⟨ (cong (join m n ∘ map G₂.t G₁.t) ∘ splitAt-join G₂.e G₁.e ∘ swap ∘ splitAt G₁.e) x ⟨
        (join m n ∘ map G₂.t G₁.t ∘ splitAt G₂.e ∘ join G₂.e G₁.e ∘ swap ∘ splitAt G₁.e) x ∎

opaque
  unfolding ×-symmetric′
  graph : SymmetricMonoidalFunctor Nat-smc Setoids-×
  graph = record
      { F = F
      ; isBraidedMonoidal = record
          { isMonoidal = record
              { ε = ε
              ; ⊗-homo = ⊗-homomorphism
              ; associativity = λ { {x} {y} {z} {(G₁ , G₂) , G₃} → associativity G₁ G₂ G₃ }
              ; unitaryˡ = unitaryˡ
              ; unitaryʳ = unitaryʳ
              }
          ; braiding-compat = λ { {x} {y} {G₁ , G₂} → braiding {G₁ = G₁} {G₂ = G₂} }
          }
      }

module F = SymmetricMonoidalFunctor graph

and-gate : Func ⊤ₛ (Graph-setoid 3)
and-gate = Const ⊤ₛ (Graph-setoid 3) and-graph
  where
    and-graph : Graph 3
    and-graph = record
        { e = 2
        ; s = λ { 0F → # 0 ; 1F → # 1 }
        ; t = λ { 0F → # 2 ; 1F → # 2 }
        }
