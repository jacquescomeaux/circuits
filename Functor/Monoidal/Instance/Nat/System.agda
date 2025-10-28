{-# OPTIONS --without-K --safe #-}

open import Level using (Level; 0ℓ; suc)

module Functor.Monoidal.Instance.Nat.System {ℓ : Level} where

open import Function.Construct.Identity using () renaming (function to Id)
import Function.Construct.Constant as Const

open import Category.Monoidal.Instance.Nat using (Nat,+,0; Natop,+,0)
open import Categories.Category.Instance.Nat using (Natop)
open import Category.Instance.Setoids.SymmetricMonoidal {suc ℓ} {ℓ} using (Setoids-×)
open import Categories.Category.Instance.SingletonSet using (SingletonSetoid)
open import Data.Circuit.Value using (Value)
open import Data.Setoid using (_⇒ₛ_; ∣_∣)
open import Data.System {ℓ} using (Systemₛ; System; ≤-System)
open import Data.System.Values Value using (Values; _≋_; module ≋)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec.Functional using ([])
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_)
open import Functor.Instance.Nat.System {ℓ} using (Sys; map)
open import Function.Base using (_∘_)
open import Function.Bundles using (Func; _⟶ₛ_; _⟨$⟩_)
open import Function.Construct.Setoid using (setoid)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory; BraidedMonoidalCategory)

open Func

module _ where

  open System

  discrete : System 0
  discrete .S = SingletonSetoid
  discrete .fₛ = Const.function (Values 0) (SingletonSetoid ⇒ₛ SingletonSetoid) (Id SingletonSetoid)
  discrete .fₒ = Const.function SingletonSetoid (Values 0) []

Sys-ε : SingletonSetoid {suc ℓ} {ℓ} ⟶ₛ Systemₛ 0
Sys-ε = Const.function SingletonSetoid (Systemₛ 0) discrete

open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)
open Cartesian (Setoids-Cartesian {suc ℓ} {ℓ}) using (products)
open import Categories.Category.BinaryProducts using (module BinaryProducts)
open BinaryProducts products using (-×-)
open import Categories.Functor using (_∘F_)
open import Categories.Category.Product using (_⁂_)

open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Instance.Nat using (Nat-Cocartesian)
open Cocartesian Nat-Cocartesian using (module Dual; i₁; i₂; -+-; _+₁_; +-assocʳ; +-assocˡ; +-comm; +-swap; +₁∘+-swap; +₁∘i₁; +₁∘i₂)
open Dual.op-binaryProducts using () renaming (×-assoc to +-assoc)
open import Data.Product.Base using (_,_; dmap) renaming (map to ×-map)

open import Categories.Functor using (Functor)
open import Categories.Category.Product using (Product)
open import Categories.Category.Instance.Nat using (Nat)
open import Categories.Category.Instance.Setoids using (Setoids)

open import Data.Fin using (_↑ˡ_; _↑ʳ_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Nat using (ℕ; _+_)
open import Data.Product.Base using (_×_)

private

  variable
    n m o : ℕ
    c₁ c₂ c₃ c₄ c₅ c₆ : Level
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

open import Functor.Monoidal.Instance.Nat.Push using (++ₛ; Push,++,[]; Push-++; Push-assoc)
open import Functor.Monoidal.Instance.Nat.Pull using (splitₛ; Pull,++,[]; ++-assoc; Pull-unitaryˡ; Pull-ε)
open import Functor.Instance.Nat.Pull using (Pull; Pull₁; Pull-resp-≈; Pull-identity)
open import Functor.Instance.Nat.Push using (Push₁; Push-identity)

open import Data.Product.Function.NonDependent.Setoid using (_×-function_; proj₁ₛ; proj₂ₛ; <_,_>ₛ; swapₛ)

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

open import Function.Construct.Setoid using (_∙_)

⊗ : System n × System m → System (n + m)
⊗ {n} {m} (S₁ , S₂) = record
    { S = S₁.S ×ₛ S₂.S
    ; fₛ = S₁.fₛ ×-⇒ S₂.fₛ ∙ splitₛ
    ; fₒ = ++ₛ ∙ S₁.fₒ ×-function S₂.fₒ
    }
  where
    module S₁ = System S₁
    module S₂ = System S₂

open import Category.Instance.Setoids.SymmetricMonoidal {0ℓ} {0ℓ} using () renaming (Setoids-× to 0ℓ-Setoids-×)
module 0ℓ-Setoids-× = SymmetricMonoidalCategory 0ℓ-Setoids-× renaming (braidedMonoidalCategory to B)
open module ⇒ₛ {A} {B} = Setoid (setoid {0ℓ} {0ℓ} {0ℓ} {0ℓ} A B) using (_≈_)
open import Categories.Functor.Monoidal.Symmetric Natop,+,0 0ℓ-Setoids-× using (module Strong)
open SymmetricMonoidalCategory using () renaming (braidedMonoidalCategory to B)
module Natop,+,0 = SymmetricMonoidalCategory Natop,+,0 renaming (braidedMonoidalCategory to B)
open import Categories.Functor.Monoidal.Braided Natop,+,0.B 0ℓ-Setoids-×.B using () renaming (module Strong to StrongB)
open Strong using (SymmetricMonoidalFunctor)
open StrongB using (BraidedMonoidalFunctor)

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
    → Func (Systemₛ n ×ₛ Systemₛ m) (Systemₛ (n + m))
⊗ₛ .to = ⊗
⊗ₛ {n} {m} .cong {a , b} {c , d} ((a≤c , c≤a) , (b≤d , d≤b)) = left , right
  where
    module a = System a
    module b = System b
    module c = System c
    module d = System d
    open ≤-System
    module a≤c = ≤-System a≤c
    module b≤d = ≤-System b≤d
    module c≤a = ≤-System c≤a
    module d≤b = ≤-System d≤b

    open Setoid
    open System

    open import Data.Product.Base using (dmap)
    open import Data.Vec.Functional.Properties using (++-cong)
    left : ≤-System (⊗ₛ .to (a , b)) (⊗ₛ .to (c , d))
    left = record
        { ⇒S = a≤c.⇒S ×-function b≤d.⇒S
        ; ≗-fₛ = λ i → dmap (a≤c.≗-fₛ (i ∘ i₁)) (b≤d.≗-fₛ (i ∘ i₂))
        ; ≗-fₒ = λ (s₁ , s₂) → ++-cong (a.fₒ′ s₁) (c.fₒ′ (a≤c.⇒S ⟨$⟩ s₁)) (a≤c.≗-fₒ s₁) (b≤d.≗-fₒ s₂)
        }

    right : ≤-System (⊗ₛ .to (c , d)) (⊗ₛ .to (a , b))
    right = record
        { ⇒S = c≤a.⇒S ×-function d≤b.⇒S
        ; ≗-fₛ = λ i → dmap (c≤a.≗-fₛ (i ∘ i₁)) (d≤b.≗-fₛ (i ∘ i₂))
        ; ≗-fₒ = λ (s₁ , s₂) → ++-cong (c.fₒ′ s₁) (a.fₒ′ (c≤a.⇒S ⟨$⟩ s₁)) (c≤a.≗-fₒ s₁) (d≤b.≗-fₒ s₂)
        }

open import Data.Fin using (Fin)

System-⊗-≤
    : {n n′ m m′ : ℕ}
      (X : System n)
      (Y : System m)
      (f : Fin n → Fin n′)
      (g : Fin m → Fin m′)
    → ≤-System (⊗ (map f X , map g Y)) (map (f +₁ g) (⊗ (X , Y)))
System-⊗-≤ {n} {n′} {m} {m′} X Y f g = record
    { ⇒S = Id (X.S ×ₛ Y.S)
    ; ≗-fₛ = λ i _ → cong X.fₛ (≋.sym (≡.cong i ∘ +₁∘i₁)) , cong Y.fₛ (≋.sym (≡.cong i ∘ +₁∘i₂ {f = f}))
    ; ≗-fₒ = λ (s₁ , s₂) → Push-++ f g (X.fₒ′ s₁) (Y.fₒ′ s₂)
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
    → ≤-System (map (f +₁ g) (⊗ (X , Y))) (⊗ (map f X , map g Y))
System-⊗-≥ {n} {n′} {m} {m′} X Y f g = record
    { ⇒S = Id (X.S ×ₛ Y.S)
    -- ; ≗-fₛ = λ i _ → cong X.fₛ (≡.cong i ∘ +₁∘i₁) , cong Y.fₛ (≡.cong i ∘ +₁∘i₂ {f = f})
    ; ≗-fₛ = λ i _ → cong (X.fₛ ×-⇒ Y.fₛ) (Pull-resp-≈ (+₁∘i₁ {n′}) {i} , Pull-resp-≈ (+₁∘i₂ {f = f}) {i})
    ; ≗-fₒ = λ (s₁ , s₂) → ≋.sym (Push-++ f g (X.fₒ′ s₁) (Y.fₒ′ s₂))
    }
  where
    module X = System X
    module Y = System Y
    import Relation.Binary.PropositionalEquality as ≡

⊗-homomorphism : NaturalTransformation (-×- ∘F (Sys ⁂ Sys)) (Sys ∘F -+-)
⊗-homomorphism = ntHelper record
    { η = λ (n , m) → ⊗ₛ {n} {m}
    ; commute = λ { (f , g) {X , Y} → System-⊗-≤ X Y f g , System-⊗-≥ X Y f g }
    }

⊗-assoc-≤
    : (X : System n)
      (Y : System m)
      (Z : System o)
    → ≤-System (map (+-assocˡ {n}) (⊗ (⊗ (X , Y) , Z))) (⊗ (X , ⊗ (Y , Z)))
⊗-assoc-≤ {n} {m} {o} X Y Z = record
    { ⇒S = ×-assocˡ
    ; ≗-fₛ = λ i ((s₁ , s₂) , s₃) → cong (X.fₛ ×-⇒ (Y.fₛ ×-⇒ Z.fₛ) ∙ assocˡ) (associativity-inv {x = i}) {s₁ , s₂ , s₃}
    ; ≗-fₒ = λ ((s₁ , s₂) , s₃) → Push-assoc (X.fₒ′ s₁) (Y.fₒ′ s₂) (Z.fₒ′ s₃)
    }
  where
    open Cartesian (Setoids-Cartesian {0ℓ} {0ℓ}) using () renaming (products to 0ℓ-products)
    open BinaryProducts 0ℓ-products using (assocˡ)
    open Cartesian (Setoids-Cartesian {ℓ} {ℓ}) using () renaming (products to prod)
    open BinaryProducts prod using () renaming (assocˡ to ×-assocˡ)
    module Pull,++,[] = SymmetricMonoidalFunctor Pull,++,[]
    module Pull,++,[]B = BraidedMonoidalFunctor (record { isBraidedMonoidal = Pull,++,[].isBraidedMonoidal })

    open import Functor.Monoidal.Braided.Strong.Properties Pull,++,[].braidedMonoidalFunctor using (associativity-inv)

    module X = System X
    module Y = System Y
    module Z = System Z

⊗-assoc-≥
    : (X : System n)
      (Y : System m)
      (Z : System o)
    → ≤-System (⊗ (X , ⊗ (Y , Z))) (map (+-assocˡ {n}) (⊗ (⊗ (X , Y) , Z)))
⊗-assoc-≥ {n} {m} {o} X Y Z = record
    { ⇒S = ×-assocʳ
    ; ≗-fₛ = λ i (s₁ , s₂ , s₃) → cong ((X.fₛ ×-⇒ Y.fₛ) ×-⇒ Z.fₛ) (sym-split-assoc {i}) {(s₁ , s₂) , s₃}
    ; ≗-fₒ = λ (s₁ , s₂ , s₃) → sym-++-assoc {(X.fₒ′ s₁ , Y.fₒ′ s₂) , Z.fₒ′ s₃}
    }
  where
    open Cartesian (Setoids-Cartesian {ℓ} {ℓ}) using () renaming (products to prod)
    open BinaryProducts prod using () renaming (assocʳ to ×-assocʳ)
    open Cartesian (Setoids-Cartesian {0ℓ} {0ℓ}) using () renaming (products to 0ℓ-products)
    open BinaryProducts 0ℓ-products using (×-assoc; assocˡ; assocʳ)

    open import Categories.Morphism.Reasoning 0ℓ-Setoids-×.U using (switch-tofromʳ)
    open import Categories.Functor.Monoidal.Symmetric using (module Lax)
    module Lax₂ = Lax Nat,+,0 0ℓ-Setoids-×
    module Pull,++,[] = Strong.SymmetricMonoidalFunctor Pull,++,[]
    open import Functor.Monoidal.Strong.Properties Pull,++,[].monoidalFunctor using (associativity-inv)
    module Push,++,[] = Lax₂.SymmetricMonoidalFunctor Push,++,[]

    +-assocℓ : Fin ((n + m) + o) → Fin (n + (m + o))
    +-assocℓ = +-assocˡ {n} {m} {o}

    opaque

      unfolding _~_

      associativity-inv-~ : splitₛ ×-function Id (Values o) ∙ splitₛ ∙ Pull₁ +-assocℓ ~ assocʳ ∙ Id (Values n) ×-function splitₛ ∙ splitₛ
      associativity-inv-~ {i} = associativity-inv {n} {m} {o} {i}

      associativity-~ : Push₁ (+-assocˡ {n} {m} {o}) ∙ ++ₛ ∙ ++ₛ ×-function Id (Values o) ~ ++ₛ ∙ Id (Values n) ×-function ++ₛ ∙ assocˡ
      associativity-~ {i} = Push,++,[].associativity {n} {m} {o} {i}

    sym-split-assoc-~ : assocʳ ∙ Id (Values n) ×-function splitₛ ∙ splitₛ ~ splitₛ ×-function Id (Values o) ∙ splitₛ ∙ Pull₁ +-assocℓ
    sym-split-assoc-~ = sym-~ associativity-inv-~

    sym-++-assoc-~ : ++ₛ ∙ Id (Values n) ×-function ++ₛ ∙ assocˡ ~ Push₁ (+-assocˡ {n} {m} {o}) ∙ ++ₛ ∙ ++ₛ ×-function Id (Values o)
    sym-++-assoc-~ = sym-~ associativity-~

    opaque

      unfolding _~_

      sym-split-assoc : assocʳ ∙ Id (Values n) ×-function splitₛ ∙ splitₛ ≈ splitₛ ×-function Id (Values o) ∙ splitₛ ∙ Pull₁ +-assocℓ
      sym-split-assoc {i} = sym-split-assoc-~ {i}

      sym-++-assoc : ++ₛ ∙ Id (Values n) ×-function ++ₛ ∙ assocˡ ≈ Push₁ (+-assocˡ {n} {m} {o}) ∙ ++ₛ ∙ ++ₛ ×-function Id (Values o)
      sym-++-assoc {i} = sym-++-assoc-~

    module X = System X
    module Y = System Y
    module Z = System Z

open import Function.Base using (id)
Sys-unitaryˡ-≤  : (X : System n) → ≤-System (map id (⊗ (discrete , X))) X
Sys-unitaryˡ-≤ X = record
    { ⇒S = proj₂ₛ
    ; ≗-fₛ = λ i (_ , s) → X.refl
    ; ≗-fₒ = λ (_ , s) → Push-identity
    }
  where
    module X = System X

Sys-unitaryˡ-≥  : (X : System n) → ≤-System X (map id (⊗ (discrete , X)))
Sys-unitaryˡ-≥ {n} X = record
    { ⇒S = < Const.function X.S SingletonSetoid tt , Id X.S >ₛ
    ; ≗-fₛ = λ i s → tt , X.refl
    ; ≗-fₒ = λ s → Equiv.sym {x = Push₁ id} {Id (Values n)} Push-identity
    }
  where
    module X = System X
    open SymmetricMonoidalCategory 0ℓ-Setoids-× using (module Equiv)

open import Data.Vec.Functional using (_++_)

Sys-unitaryʳ-≤ : (X : System n) → ≤-System (map (id ++ (λ ())) (⊗ {n} {0} (X , discrete))) X
Sys-unitaryʳ-≤ {n} X = record
    { ⇒S = proj₁ₛ
    ; ≗-fₛ = λ i (s , _) → cong (X.fₛ ∙ proj₁ₛ {B = SingletonSetoid {0ℓ}}) (unitaryʳ-inv {n} {i})
    ; ≗-fₒ = λ (s , _) → Push,++,[].unitaryʳ {n} {X.fₒ′ s , tt}
    }
  where
    module X = System X
    module Pull,++,[] = Strong.SymmetricMonoidalFunctor Pull,++,[]
    open import Functor.Monoidal.Strong.Properties Pull,++,[].monoidalFunctor using (unitaryʳ-inv; module Shorthands)
    open import Categories.Functor.Monoidal.Symmetric Nat,+,0 0ℓ-Setoids-× using (module Lax)
    module Push,++,[] = Lax.SymmetricMonoidalFunctor Push,++,[]

Sys-unitaryʳ-≥ : (X : System n) → ≤-System X (map (id ++ (λ ())) (⊗ {n} {0} (X , discrete)))
Sys-unitaryʳ-≥ {n} X = record
    { ⇒S = < Id X.S , Const.function X.S SingletonSetoid tt >ₛ
    ; ≗-fₛ = λ i s →
        cong
            (X.fₛ ×-⇒ Const.function (Values 0) (SingletonSetoid ⇒ₛ SingletonSetoid) (Id (SingletonSetoid {ℓ} {ℓ})) ∙ Id (Values n) ×-function ε⇒)
            sym-split-unitaryʳ
            {s , tt}
    ; ≗-fₒ = λ s → sym-++-unitaryʳ {X.fₒ′ s , tt}
    }
  where
    module X = System X
    module Pull,++,[] = Strong.SymmetricMonoidalFunctor Pull,++,[]
    open import Functor.Monoidal.Strong.Properties Pull,++,[].monoidalFunctor using (unitaryʳ-inv; module Shorthands)
    open import Categories.Functor.Monoidal.Symmetric Nat,+,0 0ℓ-Setoids-× using (module Lax)
    module Push,++,[] = Lax.SymmetricMonoidalFunctor Push,++,[]
    import Categories.Category.Monoidal.Utilities 0ℓ-Setoids-×.monoidal as ⊗-Util

    open ⊗-Util.Shorthands using (ρ⇐)
    open Shorthands using (ε⇐; ε⇒)

    sym-split-unitaryʳ
        : ρ⇐ ≈ Id (Values n) ×-function ε⇐ ∙ splitₛ ∙ Pull₁ (id ++ (λ ()))
    sym-split-unitaryʳ =
        0ℓ-Setoids-×.Equiv.sym
            {Values n}
            {Values n ×ₛ SingletonSetoid}
            {Id (Values n) ×-function ε⇐ ∙ splitₛ ∙ Pull₁ (id ++ (λ ()))}
            {ρ⇐}
            (unitaryʳ-inv {n})

    sym-++-unitaryʳ : proj₁ₛ {B = SingletonSetoid {0ℓ} {0ℓ}} ≈ Push₁ (id ++ (λ ())) ∙ ++ₛ ∙ Id (Values n) ×-function ε⇒
    sym-++-unitaryʳ =
        0ℓ-Setoids-×.Equiv.sym
            {Values n ×ₛ SingletonSetoid}
            {Values n}
            {Push₁ (id ++ (λ ())) ∙ ++ₛ ∙ Id (Values n) ×-function ε⇒}
            {proj₁ₛ}
            (Push,++,[].unitaryʳ {n})

Sys-braiding-compat-≤
    : (X : System n)
      (Y : System m)
    → ≤-System (map (+-swap {m} {n}) (⊗ (X , Y))) (⊗ (Y , X))
Sys-braiding-compat-≤ {n} {m} X Y = record
    { ⇒S = swapₛ
    ; ≗-fₛ = λ i (s₁ , s₂) → cong (Y.fₛ ×-⇒ X.fₛ ∙ swapₛ) (braiding-compat-inv {m} {n} {i}) {s₂ , s₁}
    ; ≗-fₒ = λ (s₁ , s₂) → Push,++,[].braiding-compat {n} {m} {X.fₒ′ s₁ , Y.fₒ′ s₂}
    }
  where
    module X = System X
    module Y = System Y
    module Pull,++,[] = SymmetricMonoidalFunctor Pull,++,[]
    module Pull,++,[]B = BraidedMonoidalFunctor (record { isBraidedMonoidal = Pull,++,[].isBraidedMonoidal })
    open import Functor.Monoidal.Braided.Strong.Properties Pull,++,[].braidedMonoidalFunctor using (braiding-compat-inv)
    open import Categories.Functor.Monoidal.Symmetric Nat,+,0 0ℓ-Setoids-× using (module Lax)
    module Push,++,[] = Lax.SymmetricMonoidalFunctor Push,++,[]

Sys-braiding-compat-≥
    : (X : System n)
      (Y : System m)
    → ≤-System (⊗ (Y , X)) (map (+-swap {m} {n}) (⊗ (X , Y)))
Sys-braiding-compat-≥ {n} {m} X Y = record
    { ⇒S = swapₛ
    ; ≗-fₛ = λ i (s₂ , s₁) → cong (X.fₛ ×-⇒ Y.fₛ) (sym-braiding-compat-inv {i})
    ; ≗-fₒ = λ (s₂ , s₁) → sym-braiding-compat-++ {X.fₒ′ s₁ , Y.fₒ′ s₂}
    }
  where
    module X = System X
    module Y = System Y
    module Pull,++,[] = SymmetricMonoidalFunctor Pull,++,[]
    module Pull,++,[]B = BraidedMonoidalFunctor (record { isBraidedMonoidal = Pull,++,[].isBraidedMonoidal })
    open import Functor.Monoidal.Braided.Strong.Properties Pull,++,[].braidedMonoidalFunctor using (braiding-compat-inv)
    open import Categories.Functor.Monoidal.Symmetric Nat,+,0 0ℓ-Setoids-× using (module Lax)
    module Push,++,[] = Lax.SymmetricMonoidalFunctor Push,++,[]

    sym-braiding-compat-inv : swapₛ ∙ splitₛ {m} ≈ splitₛ ∙ Pull₁ (+-swap {m} {n})
    sym-braiding-compat-inv {i} =
        0ℓ-Setoids-×.Equiv.sym
            {Values (m + n)}
            {Values n ×ₛ Values m}
            {splitₛ ∙ Pull₁ (+-swap {m} {n})}
            {swapₛ ∙ splitₛ {m}}
            (λ {j} → braiding-compat-inv {m} {n} {j}) {i}

    sym-braiding-compat-++ : ++ₛ {m} ∙ swapₛ ≈ Push₁ (+-swap {m} {n}) ∙ ++ₛ
    sym-braiding-compat-++ {i} =
        0ℓ-Setoids-×.Equiv.sym
            {Values n ×ₛ Values m}
            {Values (m + n)}
            {Push₁ (+-swap {m} {n}) ∙ ++ₛ}
            {++ₛ {m} ∙ swapₛ}
            (Push,++,[].braiding-compat {n} {m})

open import Categories.Functor.Monoidal.Symmetric Nat,+,0 Setoids-× using (module Lax)
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
