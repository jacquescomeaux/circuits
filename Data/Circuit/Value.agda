{-# OPTIONS --without-K --safe #-}

module Data.Circuit.Value where

import Relation.Binary.Lattice.Properties.BoundedJoinSemilattice as LatticeProp

open import Algebra.Bundles using (CommutativeMonoid)
open import Algebra.Structures using (IsCommutativeMonoid; IsMonoid; IsSemigroup; IsMagma)
open import Data.Product.Base using (_×_; _,_)
open import Data.String.Base using (String)
open import Level using (0ℓ)
open import Relation.Binary.Lattice.Bundles using (BoundedJoinSemilattice)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open CommutativeMonoid
open IsCommutativeMonoid
open IsMagma
open IsMonoid
open IsSemigroup

data Value : Set where
  U T F X : Value

data ≤-Value : Value → Value → Set where
    v≤v : {v : Value} → ≤-Value v v
    U≤T : ≤-Value U T
    U≤F : ≤-Value U F
    U≤X : ≤-Value U X
    T≤X : ≤-Value T X
    F≤X : ≤-Value F X

≤-reflexive : {x y : Value} → x ≡ y → ≤-Value x y
≤-reflexive ≡.refl = v≤v

≤-transitive : {i j k : Value} → ≤-Value i j → ≤-Value j k → ≤-Value i k
≤-transitive v≤v y = y
≤-transitive x v≤v = x
≤-transitive U≤T T≤X = U≤X
≤-transitive U≤F F≤X = U≤X

≤-antisymmetric : {i j : Value} → ≤-Value i j → ≤-Value j i → i ≡ j
≤-antisymmetric v≤v _ = ≡.refl

showValue : Value → String
showValue U = "U"
showValue T = "T"
showValue F = "F"
showValue X = "X"

join : Value → Value → Value
join U y = y
join x U = x
join T T = T
join T F = X
join F T = X
join F F = F
join X _ = X
join _ X = X

≤-supremum
    : (x y : Value)
    → ≤-Value x (join x y)
    × ≤-Value y (join x y)
    × ((z : Value) → ≤-Value x z → ≤-Value y z → ≤-Value (join x y) z)
≤-supremum U U = v≤v , v≤v , λ _ U≤z _ → U≤z
≤-supremum U T = U≤T , v≤v , λ { z x≤z y≤z → y≤z }
≤-supremum U F = U≤F , v≤v , λ { z x≤z y≤z → y≤z }
≤-supremum U X = U≤X , v≤v , λ { z x≤z y≤z → y≤z }
≤-supremum T U = v≤v , U≤T , λ { z x≤z y≤z → x≤z }
≤-supremum T T = v≤v , v≤v , λ { z x≤z y≤z → x≤z }
≤-supremum T F = T≤X , F≤X , λ { X x≤z y≤z → v≤v }
≤-supremum T X = T≤X , v≤v , λ { z x≤z y≤z → y≤z }
≤-supremum F U = v≤v , U≤F , λ { z x≤z y≤z → x≤z }
≤-supremum F T = F≤X , T≤X , λ { X x≤z y≤z → v≤v }
≤-supremum F F = v≤v , v≤v , λ { z x≤z y≤z → x≤z }
≤-supremum F X = F≤X , v≤v , λ { z x≤z y≤z → y≤z }
≤-supremum X U = v≤v , U≤X , λ { z x≤z y≤z → x≤z }
≤-supremum X T = v≤v , T≤X , λ { z x≤z y≤z → x≤z }
≤-supremum X F = v≤v , F≤X , λ { z x≤z y≤z → x≤z }
≤-supremum X X = v≤v , v≤v , λ { z x≤z y≤z → x≤z }

join-comm : (x y : Value) → join x y ≡ join y x
join-comm U U = ≡.refl
join-comm U T = ≡.refl
join-comm U F = ≡.refl
join-comm U X = ≡.refl
join-comm T U = ≡.refl
join-comm T T = ≡.refl
join-comm T F = ≡.refl
join-comm T X = ≡.refl
join-comm F U = ≡.refl
join-comm F T = ≡.refl
join-comm F F = ≡.refl
join-comm F X = ≡.refl
join-comm X U = ≡.refl
join-comm X T = ≡.refl
join-comm X F = ≡.refl
join-comm X X = ≡.refl

join-assoc : (x y z : Value) → join (join x y) z ≡ join x (join y z)
join-assoc U y z = ≡.refl
join-assoc T U z = ≡.refl
join-assoc T T U = ≡.refl
join-assoc T T T = ≡.refl
join-assoc T T F = ≡.refl
join-assoc T T X = ≡.refl
join-assoc T F U = ≡.refl
join-assoc T F T = ≡.refl
join-assoc T F F = ≡.refl
join-assoc T F X = ≡.refl
join-assoc T X U = ≡.refl
join-assoc T X T = ≡.refl
join-assoc T X F = ≡.refl
join-assoc T X X = ≡.refl
join-assoc F U z = ≡.refl
join-assoc F T U = ≡.refl
join-assoc F T T = ≡.refl
join-assoc F T F = ≡.refl
join-assoc F T X = ≡.refl
join-assoc F F U = ≡.refl
join-assoc F F T = ≡.refl
join-assoc F F F = ≡.refl
join-assoc F F X = ≡.refl
join-assoc F X U = ≡.refl
join-assoc F X T = ≡.refl
join-assoc F X F = ≡.refl
join-assoc F X X = ≡.refl
join-assoc X U z = ≡.refl
join-assoc X T U = ≡.refl
join-assoc X T T = ≡.refl
join-assoc X T F = ≡.refl
join-assoc X T X = ≡.refl
join-assoc X F U = ≡.refl
join-assoc X F T = ≡.refl
join-assoc X F F = ≡.refl
join-assoc X F X = ≡.refl
join-assoc X X U = ≡.refl
join-assoc X X T = ≡.refl
join-assoc X X F = ≡.refl
join-assoc X X X = ≡.refl

Lattice : BoundedJoinSemilattice 0ℓ 0ℓ 0ℓ
Lattice = record
    { Carrier = Value
    ; _≈_ = _≡_
    ; _≤_ = ≤-Value
    ; _∨_ = join
    ; ⊥ = U
    ; isBoundedJoinSemilattice = record
        { isJoinSemilattice = record
            { isPartialOrder = record 
                { isPreorder = record
                    { isEquivalence = ≡.isEquivalence
                    ; reflexive = ≤-reflexive
                    ; trans = ≤-transitive
                    }
                ; antisym = ≤-antisymmetric
                }
            ; supremum = ≤-supremum
            }
        ; minimum = λ where
            U → v≤v
            T → U≤T
            F → U≤F
            X → U≤X
        }
    }

module Lattice = BoundedJoinSemilattice Lattice

Monoid : CommutativeMonoid 0ℓ 0ℓ
Monoid .Carrier = Lattice.Carrier
Monoid ._≈_ = Lattice._≈_
Monoid ._∙_ = Lattice._∨_
Monoid .ε = Lattice.⊥
Monoid .isCommutativeMonoid .isMonoid .isSemigroup .isMagma .isEquivalence = ≡.isEquivalence
Monoid .isCommutativeMonoid .isMonoid .isSemigroup .isMagma .∙-cong = ≡.cong₂ join
Monoid .isCommutativeMonoid .isMonoid .isSemigroup .assoc = join-assoc
Monoid .isCommutativeMonoid .isMonoid .identity = LatticeProp.identity Lattice
Monoid .isCommutativeMonoid .comm = join-comm
