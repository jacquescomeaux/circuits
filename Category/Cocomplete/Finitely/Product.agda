{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Level using (Level)

module Category.Cocomplete.Finitely.Product {o ℓ e : Level} {𝒞 𝒟 : Category o ℓ e} where

open import Categories.Category using (_[_,_])
open import Categories.Category.Cocomplete.Finitely using (FinitelyCocomplete)
open import Categories.Category.Cocartesian using (Cocartesian; BinaryCoproducts)
open import Categories.Category.Product using (Product)
open import Categories.Diagram.Coequalizer using (Coequalizer)
open import Categories.Object.Coproduct using (Coproduct)
open import Categories.Object.Initial using (IsInitial; Initial)
open import Data.Product.Base using (_,_; _×_; dmap; zip; map)

Initial-× : Initial 𝒞 → Initial 𝒟 → Initial (Product 𝒞 𝒟)
Initial-× initial-𝒞 initial-𝒟 = record
    { ⊥ = 𝒞.⊥ , 𝒟.⊥
    ; ⊥-is-initial = record
        { ! = 𝒞.! , 𝒟.!
        ; !-unique = dmap 𝒞.!-unique 𝒟.!-unique
        }
    }
  where
    module 𝒞 = Initial initial-𝒞
    module 𝒟 = Initial initial-𝒟

Coproducts-× : BinaryCoproducts 𝒞 → BinaryCoproducts 𝒟 → BinaryCoproducts (Product 𝒞 𝒟)
Coproducts-× coproducts-𝒞 coproducts-𝒟 = record { coproduct = coproduct }
  where
    coproduct : ∀ {(A₁ , B₁) (A₂ , B₂) : _ × _} → Coproduct (Product 𝒞 𝒟) (A₁ , B₁) (A₂ , B₂)
    coproduct = record
        { A+B = 𝒞.A+B , 𝒟.A+B
        ; i₁ = 𝒞.i₁ , 𝒟.i₁
        ; i₂ = 𝒞.i₂ , 𝒟.i₂
        ; [_,_] = zip 𝒞.[_,_] 𝒟.[_,_]
        ; inject₁ = 𝒞.inject₁ , 𝒟.inject₁
        ; inject₂ = 𝒞.inject₂ , 𝒟.inject₂
        ; unique = zip 𝒞.unique 𝒟.unique
        }
      where
        module Coprod {𝒞} (coprods : BinaryCoproducts 𝒞) where
          open BinaryCoproducts coprods using (coproduct)
          open coproduct public
        module 𝒞 = Coprod coproducts-𝒞
        module 𝒟 = Coprod coproducts-𝒟

Coequalizer-×
    : (∀ {A} {B} (f g : 𝒞 [ A , B ]) → Coequalizer 𝒞 f g)
    → (∀ {A} {B} (f g : 𝒟 [ A , B ]) → Coequalizer 𝒟 f g)
    → ∀ {A} {B} {C} {D} ((f₁ , g₁) (f₂ , g₂) : 𝒞 [ A , B ] × 𝒟 [ C , D ])
    → Coequalizer (Product 𝒞 𝒟) (f₁ , g₁) (f₂ , g₂)
Coequalizer-× coequalizer-𝒞 coequalizer-𝒟 (f₁ , g₁) (f₂ , g₂) = record
    { arr = 𝒞.arr , 𝒟.arr
    ; isCoequalizer = record
        { equality = 𝒞.equality , 𝒟.equality
        ; coequalize = map 𝒞.coequalize 𝒟.coequalize
        ; universal = 𝒞.universal , 𝒟.universal
        ; unique = map 𝒞.unique 𝒟.unique
        }
    }
  where
    module 𝒞 = Coequalizer (coequalizer-𝒞 f₁ f₂)
    module 𝒟 = Coequalizer (coequalizer-𝒟 g₁ g₂)

Cocartesian-× : Cocartesian 𝒞 → Cocartesian 𝒟 → Cocartesian (Product 𝒞 𝒟)
Cocartesian-× cocartesian-𝒞 cocartesian-𝒟 = record
    { initial = Initial-× 𝒞.initial 𝒟.initial
    ; coproducts = Coproducts-× 𝒞.coproducts 𝒟.coproducts
    }
  where
    module 𝒞 = Cocartesian cocartesian-𝒞
    module 𝒟 = Cocartesian cocartesian-𝒟

FinitelyCocomplete-× : FinitelyCocomplete 𝒞 → FinitelyCocomplete 𝒟 → FinitelyCocomplete (Product 𝒞 𝒟)
FinitelyCocomplete-× finitelyCocomplete-𝒞 finitelyCocomplete-𝒟 = record
    { cocartesian = Cocartesian-× 𝒞.cocartesian 𝒟.cocartesian
    ; coequalizer = Coequalizer-× 𝒞.coequalizer 𝒟.coequalizer
    }
  where
    module 𝒞 = FinitelyCocomplete finitelyCocomplete-𝒞
    module 𝒟 = FinitelyCocomplete finitelyCocomplete-𝒟
