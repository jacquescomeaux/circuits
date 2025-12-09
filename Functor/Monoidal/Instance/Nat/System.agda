{-# OPTIONS --without-K --safe #-}

module Functor.Monoidal.Instance.Nat.System where

import Categories.Category.Monoidal.Utilities as ⊗-Util
import Data.Circuit.Value as Value
import Data.Vec.Functional as Vec
import Relation.Binary.PropositionalEquality as ≡

open import Level using (0ℓ; suc; Level)

open import Category.Monoidal.Instance.Nat using (Nat,+,0; Natop,+,0)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory; BraidedMonoidalCategory)
open import Category.Instance.Setoids.SymmetricMonoidal {0ℓ} {0ℓ} using () renaming (Setoids-× to 0ℓ-Setoids-×)
open import Category.Instance.Setoids.SymmetricMonoidal {suc 0ℓ} {suc 0ℓ} using (Setoids-×)

module Natop,+,0 = SymmetricMonoidalCategory Natop,+,0 renaming (braidedMonoidalCategory to B)
module 0ℓ-Setoids-× = SymmetricMonoidalCategory 0ℓ-Setoids-× renaming (braidedMonoidalCategory to B)

open import Functor.Monoidal.Instance.Nat.Pull using (Pull,++,[])
open import Categories.Functor.Monoidal.Braided Natop,+,0.B 0ℓ-Setoids-×.B using (module Strong)

Pull,++,[]B : Strong.BraidedMonoidalFunctor
Pull,++,[]B = record { isBraidedMonoidal = Pull,++,[].isBraidedMonoidal }
module Pull,++,[]B = Strong.BraidedMonoidalFunctor (record { isBraidedMonoidal = Pull,++,[].isBraidedMonoidal })

open import Categories.Category.BinaryProducts using (module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Instance.Nat using (Nat; Nat-Cocartesian; Natop)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Data.Setoid.Unit using (⊤ₛ)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)
open import Categories.Category.Product using (Product)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor using (Functor)
open import Categories.Functor using (_∘F_)
open import Categories.Functor.Monoidal.Symmetric Nat,+,0 Setoids-× using (module Lax)
open import Categories.NaturalTransformation.Core using (NaturalTransformation; ntHelper)
open import Data.Circuit.Value using (Monoid)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_,_; dmap; _×_) renaming (map to ×-map)
open import Data.Product.Function.NonDependent.Setoid using (_×-function_; proj₁ₛ; proj₂ₛ; <_,_>ₛ; swapₛ)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Setoid using (_⇒ₛ_; ∣_∣)
open import Data.System {suc 0ℓ} using (Systemₛ; System; discrete; _≤_)
open import Data.System.Values Monoid using (++ₛ; splitₛ; Values; ++-cong; _++_; [])
open import Data.System.Values Value.Monoid using (_≋_; module ≋)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function using (Func; _⟶ₛ_; _⟨$⟩_; _∘_; id; case_of_)
open import Function.Construct.Constant using () renaming (function to Const)
open import Function.Construct.Identity using () renaming (function to Id)
open import Function.Construct.Setoid using (_∙_; setoid)
open import Functor.Instance.Nat.Pull using (Pull)
open import Functor.Instance.Nat.Push using (Push)
open import Functor.Instance.Nat.System using (Sys; Sys-defs)
open import Functor.Monoidal.Braided.Strong.Properties Pull,++,[]B using (braiding-compat-inv)
open import Functor.Monoidal.Instance.Nat.Push using (Push,++,[])
open import Functor.Monoidal.Strong.Properties Pull,++,[].monoidalFunctor using (associativity-inv)
open import Functor.Monoidal.Strong.Properties Pull,++,[].monoidalFunctor using (unitaryʳ-inv; unitaryˡ-inv; module Shorthands)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_)

open module ⇒ₛ {A} {B} = Setoid (setoid {0ℓ} {0ℓ} {0ℓ} {0ℓ} A B) using (_≈_)

open Cartesian (Setoids-Cartesian {suc 0ℓ} {suc 0ℓ}) using (products)

open BinaryProducts products using (-×-)
open Cocartesian Nat-Cocartesian using (module Dual; i₁; i₂; -+-; _+₁_; +-assocʳ; +-assocˡ; +-comm; +-swap; +₁∘+-swap; +₁∘i₁; +₁∘i₂)
open Dual.op-binaryProducts using () renaming (×-assoc to +-assoc)
open SymmetricMonoidalCategory using () renaming (braidedMonoidalCategory to B)

open Func

Sys-ε : ⊤ₛ {suc 0ℓ} {suc 0ℓ} ⟶ₛ Systemₛ 0
Sys-ε = Const ⊤ₛ (Systemₛ 0) (discrete 0)

private

  variable
    n m o : ℕ
    c₁ c₂ c₃ c₄ c₅ c₆ : Level
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

_×-⇒_
    : {A : Setoid c₁ ℓ₁}
      {B : Setoid c₂ ℓ₂}
      {C : Setoid c₃ ℓ₃}
      {D : Setoid c₄ ℓ₄}
      {E : Setoid c₅ ℓ₅}
      {F : Setoid c₆ ℓ₆}
    → A ⟶ₛ B ⇒ₛ C
    → D ⟶ₛ E ⇒ₛ F
    → A ×ₛ D ⟶ₛ B ×ₛ E ⇒ₛ C ×ₛ F
_×-⇒_ f g .to (x , y) = to f x ×-function to g y
_×-⇒_ f g .cong (x , y) = cong f x , cong g y

⊗ : System n × System m → System (n + m)
⊗ {n} {m} (S₁ , S₂) = record
    { S = S₁.S ×ₛ S₂.S
    ; fₛ = S₁.fₛ ×-⇒ S₂.fₛ ∙ splitₛ
    ; fₒ = ++ₛ ∙ S₁.fₒ ×-function S₂.fₒ
    }
  where
    module S₁ = System S₁
    module S₂ = System S₂

opaque

  _~_ : {A B : Setoid 0ℓ 0ℓ} → Func A B → Func A B → Set
  _~_ = _≈_
  infix 4 _~_

  sym-~
      : {A B : Setoid 0ℓ 0ℓ}
        {x y : Func A B}
      → x ~ y
      → y ~ x
  sym-~ {A} {B} {x} {y} = 0ℓ-Setoids-×.Equiv.sym {A} {B} {x} {y}

⊗ₛ
    : {n m : ℕ}
    → Systemₛ n ×ₛ Systemₛ m ⟶ₛ Systemₛ (n + m)
⊗ₛ .to = ⊗
⊗ₛ {n} {m} .cong {a , b} {c , d} ((a≤c , c≤a) , (b≤d , d≤b)) = left , right
  where
    module a = System a
    module b = System b
    module c = System c
    module d = System d
    module a≤c = _≤_ a≤c
    module b≤d = _≤_ b≤d
    module c≤a = _≤_ c≤a
    module d≤b = _≤_ d≤b

    open _≤_
    left : ⊗ₛ ⟨$⟩ (a , b) ≤ ⊗ₛ ⟨$⟩ (c , d)
    left .⇒S = a≤c.⇒S ×-function b≤d.⇒S
    left .≗-fₛ i with (i₁ , i₂) ← splitₛ ⟨$⟩ i = dmap (a≤c.≗-fₛ i₁) (b≤d.≗-fₛ i₂)
    left .≗-fₒ = cong ++ₛ ∘ dmap a≤c.≗-fₒ b≤d.≗-fₒ

    right : ⊗ₛ ⟨$⟩ (c , d) ≤ ⊗ₛ ⟨$⟩ (a , b)
    right .⇒S = c≤a.⇒S ×-function d≤b.⇒S
    right .≗-fₛ i with (i₁ , i₂) ← splitₛ ⟨$⟩ i = dmap (c≤a.≗-fₛ i₁) (d≤b.≗-fₛ i₂)
    right .≗-fₒ = cong ++ₛ ∘ dmap c≤a.≗-fₒ d≤b.≗-fₒ

opaque

  unfolding Sys-defs

  System-⊗-≤
      : {n n′ m m′ : ℕ}
        (X : System n)
        (Y : System m)
        (f : Fin n → Fin n′)
        (g : Fin m → Fin m′)
      → ⊗ (Sys.₁ f ⟨$⟩ X , Sys.₁ g ⟨$⟩ Y) ≤ Sys.₁ (f +₁ g) ⟨$⟩ ⊗ (X , Y)
  System-⊗-≤ {n} {n′} {m} {m′} X Y f g = record
      { ⇒S = Id (X.S ×ₛ Y.S)
      ; ≗-fₛ = λ i s → cong (X.fₛ ×-⇒ Y.fₛ) (Pull,++,[].⊗-homo.⇐.sym-commute (f , g) {i}) {s}
      ; ≗-fₒ = λ (s₁ , s₂) → Push,++,[].⊗-homo.commute (f , g) {X.fₒ′ s₁ , Y.fₒ′ s₂}
      }
    where
      module X = System X
      module Y = System Y

  System-⊗-≥
      : {n n′ m m′ : ℕ}
        (X : System n)
        (Y : System m)
        (f : Fin n → Fin n′)
        (g : Fin m → Fin m′)
      → Sys.₁ (f +₁ g) ⟨$⟩ (⊗ (X , Y)) ≤ ⊗ (Sys.₁ f ⟨$⟩ X , Sys.₁ g ⟨$⟩ Y)
  System-⊗-≥ {n} {n′} {m} {m′} X Y f g = record
      { ⇒S = Id (X.S ×ₛ Y.S)
      ; ≗-fₛ = λ i s → cong (X.fₛ ×-⇒ Y.fₛ) (Pull,++,[].⊗-homo.⇐.commute (f , g) {i}) {s}
      ; ≗-fₒ = λ (s₁ , s₂) → Push,++,[].⊗-homo.sym-commute (f , g) {X.fₒ′ s₁ , Y.fₒ′ s₂}
      }
    where
      module X = System X
      module Y = System Y

⊗-homomorphism : NaturalTransformation (-×- ∘F (Sys ⁂ Sys)) (Sys ∘F -+-)
⊗-homomorphism = ntHelper record
    { η = λ (n , m) → ⊗ₛ {n} {m}
    ; commute = λ { (f , g) {X , Y} → System-⊗-≤ X Y f g , System-⊗-≥ X Y f g }
    }

opaque

  unfolding Sys-defs

  ⊗-assoc-≤
      : (X : System n)
        (Y : System m)
        (Z : System o)
      → Sys.₁ (+-assocˡ {n}) ⟨$⟩ (⊗ (⊗ (X , Y) , Z)) ≤ ⊗ (X , ⊗ (Y , Z))
  ⊗-assoc-≤ {n} {m} {o} X Y Z = record
      { ⇒S = assocˡ
      ; ≗-fₛ = λ i ((s₁ , s₂) , s₃) → cong (X.fₛ ×-⇒ (Y.fₛ ×-⇒ Z.fₛ) ∙ assocˡ) (associativity-inv {x = i}) {s₁ , s₂ , s₃}
      ; ≗-fₒ = λ ((s₁ , s₂) , s₃) → Push,++,[].associativity {x = (X.fₒ′ s₁ , Y.fₒ′ s₂) , Z.fₒ′ s₃}
      }
    where
      open Cartesian (Setoids-Cartesian {0ℓ} {0ℓ}) using () renaming (products to 0ℓ-products)
      open BinaryProducts 0ℓ-products using (assocˡ)

      module X = System X
      module Y = System Y
      module Z = System Z

  ⊗-assoc-≥
      : (X : System n)
        (Y : System m)
        (Z : System o)
      → ⊗ (X , ⊗ (Y , Z)) ≤ Sys.₁ (+-assocˡ {n}) ⟨$⟩ (⊗ (⊗ (X , Y) , Z))
  ⊗-assoc-≥ {n} {m} {o} X Y Z = record
      { ⇒S = ×-assocʳ
      ; ≗-fₛ = λ i (s₁ , s₂ , s₃) → cong ((X.fₛ ×-⇒ Y.fₛ) ×-⇒ Z.fₛ) (sym-split-assoc {i}) {(s₁ , s₂) , s₃}
      ; ≗-fₒ = λ (s₁ , s₂ , s₃) → sym-++-assoc {(X.fₒ′ s₁ , Y.fₒ′ s₂) , Z.fₒ′ s₃}
      }
    where
      open Cartesian (Setoids-Cartesian {0ℓ} {0ℓ}) using () renaming (products to prod)
      open BinaryProducts prod using () renaming (assocʳ to ×-assocʳ; assocˡ to ×-assocˡ)

      +-assocℓ : Fin ((n + m) + o) → Fin (n + (m + o))
      +-assocℓ = +-assocˡ {n} {m} {o}

      opaque

        unfolding _~_

        associativity-inv-~ : splitₛ ×-function Id (Values o) ∙ splitₛ ∙ Pull.₁ +-assocℓ ~ ×-assocʳ ∙ Id (Values n) ×-function splitₛ ∙ splitₛ
        associativity-inv-~ {i} = associativity-inv {n} {m} {o} {i}

        associativity-~ : Push.₁ (+-assocˡ {n} {m} {o}) ∙ ++ₛ ∙ ++ₛ ×-function Id (Values o) ~ ++ₛ ∙ Id (Values n) ×-function ++ₛ ∙ ×-assocˡ
        associativity-~ {i} = Push,++,[].associativity {n} {m} {o} {i}

      sym-split-assoc-~ : ×-assocʳ ∙ Id (Values n) ×-function splitₛ ∙ splitₛ ~ splitₛ ×-function Id (Values o) ∙ splitₛ ∙ Pull.₁ +-assocℓ
      sym-split-assoc-~ = sym-~ associativity-inv-~

      sym-++-assoc-~ : ++ₛ ∙ Id (Values n) ×-function ++ₛ ∙ ×-assocˡ ~ Push.₁ (+-assocˡ {n} {m} {o}) ∙ ++ₛ ∙ ++ₛ ×-function Id (Values o)
      sym-++-assoc-~ = sym-~ associativity-~

      opaque

        unfolding _~_

        sym-split-assoc : ×-assocʳ ∙ Id (Values n) ×-function splitₛ ∙ splitₛ ≈ splitₛ ×-function Id (Values o) ∙ splitₛ ∙ Pull.₁ +-assocℓ
        sym-split-assoc {i} = sym-split-assoc-~ {i}

        sym-++-assoc : ++ₛ ∙ Id (Values n) ×-function ++ₛ ∙ ×-assocˡ ≈ Push.₁ (+-assocˡ {n} {m} {o}) ∙ ++ₛ ∙ ++ₛ ×-function Id (Values o)
        sym-++-assoc {i} = sym-++-assoc-~

      module X = System X
      module Y = System Y
      module Z = System Z

  Sys-unitaryˡ-≤  : (X : System n) → Sys.₁ id ⟨$⟩ (⊗ (discrete 0 , X)) ≤ X
  Sys-unitaryˡ-≤ {n} X = record
      { ⇒S = proj₂ₛ
      ; ≗-fₛ = λ i (_ , s) → cong (X.fₛ ∙ proj₂ₛ {A = ⊤ₛ {0ℓ}}) (unitaryˡ-inv {n} {i})
      ; ≗-fₒ = λ (_ , s) → Push,++,[].unitaryˡ {n} {tt , X.fₒ′ s}
      }
    where
      module X = System X

  Sys-unitaryˡ-≥  : (X : System n) → X ≤ Sys.₁ id ⟨$⟩ (⊗ (discrete 0 , X))
  Sys-unitaryˡ-≥ {n} X = record
      { ⇒S = < Const X.S ⊤ₛ tt , Id X.S >ₛ
      ; ≗-fₛ = λ i s → cong (disc.fₛ ×-⇒ X.fₛ ∙ ε⇒ ×-function Id (Values n)) (sym-split-unitaryˡ {i})
      ; ≗-fₒ = λ s → sym-++-unitaryˡ {_ , X.fₒ′ s}
      }
    where
      module X = System X
      open SymmetricMonoidalCategory 0ℓ-Setoids-× using (module Equiv)
      open ⊗-Util.Shorthands 0ℓ-Setoids-×.monoidal using (λ⇐)
      open Shorthands using (ε⇐; ε⇒)
      module disc = System (discrete 0)
      sym-split-unitaryˡ
          : λ⇐ ≈ ε⇐ ×-function Id (Values n) ∙ splitₛ ∙ Pull.₁ ((λ ()) Vec.++ id)
      sym-split-unitaryˡ =
          0ℓ-Setoids-×.Equiv.sym
              {Values n}
              {⊤ₛ ×ₛ Values n}
              {ε⇐ ×-function Id (Values n) ∙ splitₛ ∙ Pull.₁ ((λ ()) Vec.++ id)}
              {λ⇐}
              (unitaryˡ-inv {n})
      sym-++-unitaryˡ : proj₂ₛ {A = ⊤ₛ {0ℓ} {0ℓ}} ≈ Push.₁ ((λ ()) Vec.++ id) ∙ ++ₛ ∙ Push,++,[].ε ×-function Id (Values n)
      sym-++-unitaryˡ =
          0ℓ-Setoids-×.Equiv.sym
              {⊤ₛ ×ₛ Values n}
              {Values n}
              {Push.₁ ((λ ()) Vec.++ id) ∙ ++ₛ ∙ Push,++,[].ε ×-function Id (Values n)}
              {proj₂ₛ}
              (Push,++,[].unitaryˡ {n})


  Sys-unitaryʳ-≤ : (X : System n) → Sys.₁ (id Vec.++ (λ ())) ⟨$⟩ (⊗ {n} {0} (X , discrete 0)) ≤ X
  Sys-unitaryʳ-≤ {n} X = record
      { ⇒S = proj₁ₛ
      ; ≗-fₛ = λ i (s , _) → cong (X.fₛ ∙ proj₁ₛ {B = ⊤ₛ {0ℓ}}) (unitaryʳ-inv {n} {i})
      ; ≗-fₒ = λ (s , _) → Push,++,[].unitaryʳ {n} {X.fₒ′ s , tt}
      }
    where
      module X = System X

  Sys-unitaryʳ-≥ : (X : System n) → X ≤ Sys.₁ (id Vec.++ (λ ())) ⟨$⟩ (⊗ {n} {0} (X , discrete 0))
  Sys-unitaryʳ-≥ {n} X = record
      { ⇒S = < Id X.S , Const X.S ⊤ₛ tt >ₛ
      ; ≗-fₛ = λ i s → cong (X.fₛ ×-⇒ disc.fₛ ∙ Id (Values n) ×-function ε⇒) sym-split-unitaryʳ {s , tt}
      ; ≗-fₒ = λ s → sym-++-unitaryʳ {X.fₒ′ s , tt}
      }
    where
      module X = System X
      module disc = System (discrete 0)
      open ⊗-Util.Shorthands 0ℓ-Setoids-×.monoidal using (ρ⇐)
      open Shorthands using (ε⇐; ε⇒)
      sym-split-unitaryʳ
          : ρ⇐ ≈ Id (Values n) ×-function ε⇐ ∙ splitₛ ∙ Pull.₁ (id Vec.++ (λ ()))
      sym-split-unitaryʳ =
          0ℓ-Setoids-×.Equiv.sym
              {Values n}
              {Values n ×ₛ ⊤ₛ}
              {Id (Values n) ×-function ε⇐ ∙ splitₛ ∙ Pull.₁ (id Vec.++ (λ ()))}
              {ρ⇐}
              (unitaryʳ-inv {n})
      sym-++-unitaryʳ : proj₁ₛ {B = ⊤ₛ {0ℓ}} ≈ Push.₁ (id Vec.++ (λ ())) ∙ ++ₛ ∙ Id (Values n) ×-function Push,++,[].ε
      sym-++-unitaryʳ =
          0ℓ-Setoids-×.Equiv.sym
              {Values n ×ₛ ⊤ₛ}
              {Values n}
              {Push.₁ (id Vec.++ (λ ())) ∙ ++ₛ ∙ Id (Values n) ×-function Push,++,[].ε}
              {proj₁ₛ}
              (Push,++,[].unitaryʳ {n})

  Sys-braiding-compat-≤
      : (X : System n)
        (Y : System m)
      → Sys.₁ (+-swap {m} {n}) ⟨$⟩ (⊗ (X , Y)) ≤ ⊗ (Y , X)
  Sys-braiding-compat-≤ {n} {m} X Y = record
      { ⇒S = swapₛ
      ; ≗-fₛ = λ i (s₁ , s₂) → cong (Y.fₛ ×-⇒ X.fₛ ∙ swapₛ) (braiding-compat-inv {m} {n} {i}) {s₂ , s₁}
      ; ≗-fₒ = λ (s₁ , s₂) → Push,++,[].braiding-compat {n} {m} {X.fₒ′ s₁ , Y.fₒ′ s₂}
      }
    where
      module X = System X
      module Y = System Y

  Sys-braiding-compat-≥
      : (X : System n)
        (Y : System m)
      → ⊗ (Y , X) ≤ Sys.₁ (+-swap {m} {n}) ⟨$⟩ ⊗ (X , Y)
  Sys-braiding-compat-≥ {n} {m} X Y = record
      { ⇒S = swapₛ
      ; ≗-fₛ = λ i (s₂ , s₁) → cong (X.fₛ ×-⇒ Y.fₛ) (sym-braiding-compat-inv {i})
      ; ≗-fₒ = λ (s₂ , s₁) → sym-braiding-compat-++ {X.fₒ′ s₁ , Y.fₒ′ s₂}
      }
    where
      module X = System X
      module Y = System Y
      sym-braiding-compat-inv : swapₛ ∙ splitₛ {m} ≈ splitₛ ∙ Pull.₁ (+-swap {m} {n})
      sym-braiding-compat-inv {i} =
          0ℓ-Setoids-×.Equiv.sym
              {Values (m + n)}
              {Values n ×ₛ Values m}
              {splitₛ ∙ Pull.₁ (+-swap {m} {n})}
              {swapₛ ∙ splitₛ {m}}
              (λ {j} → braiding-compat-inv {m} {n} {j}) {i}
      sym-braiding-compat-++ : ++ₛ {m} ∙ swapₛ ≈ Push.₁ (+-swap {m} {n}) ∙ ++ₛ
      sym-braiding-compat-++ {i} =
          0ℓ-Setoids-×.Equiv.sym
              {Values n ×ₛ Values m}
              {Values (m + n)}
              {Push.₁ (+-swap {m} {n}) ∙ ++ₛ}
              {++ₛ {m} ∙ swapₛ}
              (Push,++,[].braiding-compat {n} {m})

open Lax.SymmetricMonoidalFunctor

Sys,⊗,ε : Lax.SymmetricMonoidalFunctor
Sys,⊗,ε .F = Sys
Sys,⊗,ε .isBraidedMonoidal = record
    { isMonoidal = record
        { ε = Sys-ε
        ; ⊗-homo = ⊗-homomorphism
        ; associativity = λ { {n} {m} {o} {(X , Y), Z} → ⊗-assoc-≤ X Y Z , ⊗-assoc-≥ X Y Z }
        ; unitaryˡ = λ { {n} {_ , X} → Sys-unitaryˡ-≤ X , Sys-unitaryˡ-≥ X }
        ; unitaryʳ = λ { {n} {X , _} → Sys-unitaryʳ-≤ X , Sys-unitaryʳ-≥ X }
        }
    ; braiding-compat = λ { {n} {m} {X , Y} → Sys-braiding-compat-≤ X Y , Sys-braiding-compat-≥ X Y }
    }

module Sys,⊗,ε = Lax.SymmetricMonoidalFunctor Sys,⊗,ε
