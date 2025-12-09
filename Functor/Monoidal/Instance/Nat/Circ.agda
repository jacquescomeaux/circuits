{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_; 0ℓ; suc)

module Functor.Monoidal.Instance.Nat.Circ where

import Categories.Object.Monoid as MonoidObject
import Data.Permutation.Sort as ↭-Sort
import Function.Reasoning as →-Reasoning

open import Category.Instance.Setoids.SymmetricMonoidal {suc 0ℓ} {suc 0ℓ} using (Setoids-×)
import Categories.Category.Monoidal.Reasoning as ⊗-Reasoning
open import Category.Monoidal.Instance.Nat using (Nat,+,0)
open import Categories.Category.Construction.Monoids using (Monoids)
open import Categories.Category.Instance.Nat using (Nat; Nat-Cocartesian)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Data.Setoid.Unit using (⊤ₛ)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)
open import Categories.Category.Cartesian using (Cartesian)
open Cartesian (Setoids-Cartesian {suc 0ℓ} {suc 0ℓ}) using (products)
open import Categories.Category.BinaryProducts using (module BinaryProducts)
open import Categories.Functor using (_∘F_)
open BinaryProducts products using (-×-)
open import Categories.Category.Product using (_⁂_)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Instance.Nat using (Nat-Cocartesian)
open import Categories.Functor.Monoidal.Symmetric using (module Lax)
open import Categories.Functor using (Functor)
open import Categories.Category.Cocartesian.Bundle using (CocartesianCategory)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Data.Circuit using (Circuit; Circuitₛ; mkCircuit; mkCircuitₛ; _≈_; mk≈; map)
open import Data.Circuit.Gate using (Gates)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_,_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Function using (_⟶ₛ_; Func; _⟨$⟩_; _∘_; id)
open import Functor.Instance.Nat.Circ {suc 0ℓ} using (Circ; module Multiset∘Edge)
open import Functor.Instance.Nat.Edge {suc 0ℓ} using (Edge)
open import Function.Construct.Setoid using (_∙_)

module Setoids-× = SymmetricMonoidalCategory Setoids-×

open import Functor.Instance.FreeCMonoid {suc 0ℓ} {suc 0ℓ} using (FreeCMonoid)

Nat-Cocartesian-Category : CocartesianCategory 0ℓ 0ℓ 0ℓ
Nat-Cocartesian-Category = record { cocartesian = Nat-Cocartesian }

open import Functor.Monoidal.Construction.MultisetOf
     {𝒞 = Nat-Cocartesian-Category} (Edge Gates) FreeCMonoid using (MultisetOf,++,[])

open Lax using (SymmetricMonoidalFunctor)

module MultisetOf,++,[] = SymmetricMonoidalFunctor MultisetOf,++,[]

open SymmetricMonoidalFunctor

ε⇒ : ⊤ₛ ⟶ₛ Circuitₛ 0
ε⇒ = mkCircuitₛ ∙ MultisetOf,++,[].ε

open Cocartesian Nat-Cocartesian using (-+-)

open Func

η : {n m : ℕ} → Circuitₛ n ×ₛ Circuitₛ m ⟶ₛ Circuitₛ (n + m)
η {n} {m} .to (mkCircuit X , mkCircuit Y) = mkCircuit (MultisetOf,++,[].⊗-homo.η (n , m) ⟨$⟩ (X , Y))
η {n} {m} .cong (mk≈ x , mk≈ y) = mk≈ (cong (MultisetOf,++,[].⊗-homo.η (n , m)) (x , y))

⊗-homomorphism : NaturalTransformation (-×- ∘F (Circ ⁂ Circ)) (Circ ∘F -+-)
⊗-homomorphism = ntHelper record
    { η = λ (n , m) → η {n} {m}
    ; commute = λ { (f , g) {mkCircuit X , mkCircuit Y} → mk≈ (MultisetOf,++,[].⊗-homo.commute (f , g) {X , Y}) }
    }

Circ,⊗,ε : SymmetricMonoidalFunctor Nat,+,0 Setoids-×
Circ,⊗,ε .F = Circ
Circ,⊗,ε .isBraidedMonoidal = record
    { isMonoidal = record
        { ε = ε⇒
        ; ⊗-homo = ⊗-homomorphism
        ; associativity = λ { {n} {m} {o} {(mkCircuit x , mkCircuit y) , mkCircuit z} →
                  mk≈ (MultisetOf,++,[].associativity {n} {m} {o} {(x , y) , z}) }
        ; unitaryˡ = λ { {n} {_ , mkCircuit x} → mk≈ (MultisetOf,++,[].unitaryˡ {n} {_ , x}) }
        ; unitaryʳ = λ { {n} {mkCircuit x , _} → mk≈ (MultisetOf,++,[].unitaryʳ {n} {x , _}) }
        }
    ; braiding-compat = λ { {n} {m} {mkCircuit x , mkCircuit y} →
        mk≈ (MultisetOf,++,[].braiding-compat {n} {m} {x , y}) }
    }
