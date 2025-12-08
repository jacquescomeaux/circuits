{-# OPTIONS --without-K --safe #-}

open import Level using (Level; suc; _⊔_)

module Category.Instance.FinitelyCocompletes {o ℓ e : Level} where

import Category.Instance.One.Properties as OneProps

open import Categories.Category using (_[_,_])
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Core using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Category.Instance.One using (One; One-⊤)
open import Categories.Category.Monoidal.Instance.Cats using () renaming (module Product to Products)
open import Categories.Category.Product using (πˡ; πʳ; _※_; _⁂_) renaming (Product to ProductCat)
open import Categories.Diagram.Coequalizer using (IsCoequalizer)
open import Categories.Functor using (Functor) renaming (id to idF)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; associator; unitorˡ; unitorʳ; module ≃; _ⓘₕ_)
open import Categories.Object.Coproduct using (IsCoproduct)
open import Categories.Object.Initial using (IsInitial)
open import Categories.Object.Product.Core using (Product)
open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)
open import Category.Cocomplete.Finitely.Product using (FinitelyCocomplete-×)
open import Data.Product.Base using (_,_; proj₁; proj₂; map; dmap; zip′)
open import Function.Base using (id; flip)
open import Functor.Exact using (∘-RightExactFunctor; RightExactFunctor; idREF; IsRightExact; rightexact)

FinitelyCocompletes : Category (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
FinitelyCocompletes = categoryHelper record
    { Obj = FinitelyCocompleteCategory o ℓ e
    ; _⇒_ = RightExactFunctor
    ; _≈_ = λ F G → REF.F F ≃ REF.F G
    ; id = idREF
    ; _∘_ = ∘-RightExactFunctor
    ; assoc = λ {_ _ _ _ F G H} → associator (REF.F F) (REF.F G) (REF.F H)
    ; identityˡ = unitorˡ
    ; identityʳ = unitorʳ
    ; equiv = record
        { refl = ≃.refl
        ; sym = ≃.sym
        ; trans = ≃.trans
        }
    ; ∘-resp-≈ = _ⓘₕ_
    }
  where
    module REF = RightExactFunctor

One-FCC : FinitelyCocompleteCategory o ℓ e
One-FCC = record
    { U = One
    ; finCo = OneProps.finitelyCocomplete
    }

_×_
    : FinitelyCocompleteCategory o ℓ e
    → FinitelyCocompleteCategory o ℓ e
    → FinitelyCocompleteCategory o ℓ e
_×_ 𝒞 𝒟 = record
    { U = ProductCat 𝒞.U 𝒟.U
    ; finCo = FinitelyCocomplete-× 𝒞.finCo 𝒟.finCo
    }
  where
    module 𝒞 = FinitelyCocompleteCategory 𝒞
    module 𝒟 = FinitelyCocompleteCategory 𝒟

module _ (𝒞 𝒟 : FinitelyCocompleteCategory o ℓ e) where

  private
    module 𝒞 = FinitelyCocompleteCategory 𝒞
    module 𝒟 = FinitelyCocompleteCategory 𝒟
    module 𝒞×𝒟 = FinitelyCocompleteCategory (𝒞 × 𝒟)

  πˡ-RightExact : IsRightExact (𝒞 × 𝒟) 𝒞 πˡ
  πˡ-RightExact = record
      { F-resp-⊥ = F-resp-⊥
      ; F-resp-+ = F-resp-+
      ; F-resp-coeq = F-resp-coeq
      }
    where
      F-resp-⊥
          : {(A , B) : 𝒞×𝒟.Obj}
          → IsInitial 𝒞×𝒟.U (A , B)
          → IsInitial 𝒞.U A
      F-resp-⊥ {A , B} initial = record
          { ! = λ { {C} → proj₁ (! {C , B}) }
          ; !-unique = λ { f → proj₁ (!-unique (f , 𝒟.id)) }
          }
        where
          open IsInitial initial
      F-resp-+
          : {(C₁ , D₁) (C₂ , D₂) (C₃ , D₃) : 𝒞×𝒟.Obj}
            {(i₁-c , i₁-d) : 𝒞×𝒟.U [ (C₁ , D₁) , (C₃ , D₃) ]}
            {(i₂-c , i₂-d) : 𝒞×𝒟.U [ (C₂ , D₂) , (C₃ , D₃) ]}
          → IsCoproduct (ProductCat 𝒞.U 𝒟.U) (i₁-c , i₁-d) (i₂-c , i₂-d)
          → IsCoproduct 𝒞.U i₁-c i₂-c
      F-resp-+ {_} {_} {_} {i₁-c , i₁-d} {i₂-c , i₂-d} isCoproduct = record
          { [_,_] = λ { h₁ h₂ → proj₁ (copairing (h₁ , i₁-d) (h₂ , i₂-d)) }
          ; inject₁ = proj₁ inject₁
          ; inject₂ = proj₁ inject₂
          ; unique = λ { eq₁ eq₂ → proj₁ (unique (eq₁ , 𝒟.identityˡ) (eq₂ , 𝒟.identityˡ)) }
          }
        where
          open IsCoproduct isCoproduct renaming ([_,_] to copairing)
      F-resp-coeq
          : {(C₁ , D₁) (C₂ , D₂) (C₃ , D₃) : 𝒞×𝒟.Obj}
            {f g : 𝒞×𝒟.U [ (C₁ , D₁) , (C₂ , D₂) ]}
            {h : 𝒞×𝒟.U [ (C₂ , D₂) , (C₃ , D₃) ]}
          → IsCoequalizer (ProductCat 𝒞.U 𝒟.U) f g h
          → IsCoequalizer 𝒞.U (proj₁ f) (proj₁ g) (proj₁ h)
      F-resp-coeq isCoequalizer = record
          { equality = proj₁ equality
          ; coequalize = λ { eq → proj₁ (coequalize (eq , proj₂ equality)) }
          ; universal = proj₁ universal
          ; unique = λ { eq → proj₁ (unique (eq , 𝒟.Equiv.sym 𝒟.identityˡ)) }
          }
        where
          open IsCoequalizer isCoequalizer

  πʳ-RightExact : IsRightExact (𝒞 × 𝒟) 𝒟 πʳ
  πʳ-RightExact = record
      { F-resp-⊥ = F-resp-⊥
      ; F-resp-+ = F-resp-+
      ; F-resp-coeq = F-resp-coeq
      }
    where
      F-resp-⊥
          : {(A , B) : 𝒞×𝒟.Obj}
          → IsInitial 𝒞×𝒟.U (A , B)
          → IsInitial 𝒟.U B
      F-resp-⊥ {A , B} initial = record
          { ! = λ { {C} → proj₂ (! {A , C}) }
          ; !-unique = λ { f → proj₂ (!-unique (𝒞.id , f)) }
          }
        where
          open IsInitial initial
      F-resp-+
          : {(C₁ , D₁) (C₂ , D₂) (C₃ , D₃) : 𝒞×𝒟.Obj}
            {(i₁-c , i₁-d) : 𝒞×𝒟.U [ (C₁ , D₁) , (C₃ , D₃) ]}
            {(i₂-c , i₂-d) : 𝒞×𝒟.U [ (C₂ , D₂) , (C₃ , D₃) ]}
          → IsCoproduct 𝒞×𝒟.U (i₁-c , i₁-d) (i₂-c , i₂-d)
          → IsCoproduct 𝒟.U i₁-d i₂-d
      F-resp-+ {_} {_} {_} {i₁-c , i₁-d} {i₂-c , i₂-d} isCoproduct = record
          { [_,_] = λ { h₁ h₂ → proj₂ (copairing (i₁-c , h₁) (i₂-c , h₂)) }
          ; inject₁ = proj₂ inject₁
          ; inject₂ = proj₂ inject₂
          ; unique = λ { eq₁ eq₂ → proj₂ (unique (𝒞.identityˡ , eq₁) (𝒞.identityˡ , eq₂)) }
          }
        where
          open IsCoproduct isCoproduct renaming ([_,_] to copairing)
      F-resp-coeq
          : {(C₁ , D₁) (C₂ , D₂) (C₃ , D₃) : 𝒞×𝒟.Obj}
            {f g : 𝒞×𝒟.U [ (C₁ , D₁) , (C₂ , D₂) ]}
            {h : 𝒞×𝒟.U [ (C₂ , D₂) , (C₃ , D₃) ]}
          → IsCoequalizer 𝒞×𝒟.U f g h
          → IsCoequalizer 𝒟.U (proj₂ f) (proj₂ g) (proj₂ h)
      F-resp-coeq isCoequalizer = record
          { equality = proj₂ equality
          ; coequalize = λ { eq → proj₂ (coequalize (proj₁ equality , eq)) }
          ; universal = proj₂ universal
          ; unique = λ { eq → proj₂ (unique (𝒞.Equiv.sym 𝒞.identityˡ , eq)) }
          }
        where
          open IsCoequalizer isCoequalizer

module _ where

  open FinitelyCocompleteCategory using (U)

  IsRightExact-※
      : {𝒞 𝒟 ℰ : FinitelyCocompleteCategory o ℓ e}
        (F : Functor (U 𝒞) (U 𝒟))
        (G : Functor (U 𝒞) (U ℰ))
      → IsRightExact 𝒞 𝒟 F
      → IsRightExact 𝒞 ℰ G
      → IsRightExact 𝒞 (𝒟 × ℰ) (F ※ G)
  IsRightExact-※ {𝒞} {𝒟} {ℰ} F G isRightExact-F isRightExact-G = record 
      { F-resp-⊥ = F-resp-⊥′
      ; F-resp-+ = F-resp-+′
      ; F-resp-coeq = F-resp-coeq′
      }
    where
      module 𝒞 = FinitelyCocompleteCategory 𝒞
      module 𝒟 = FinitelyCocompleteCategory 𝒟
      module ℰ = FinitelyCocompleteCategory ℰ
      open IsRightExact isRightExact-F
      open IsRightExact isRightExact-G renaming (F-resp-⊥ to G-resp-⊥; F-resp-+ to G-resp-+; F-resp-coeq to G-resp-coeq)
      module F = Functor F
      module G = Functor G
      F-resp-⊥′
          : {A : 𝒞.Obj}
          → IsInitial 𝒞.U A
          → IsInitial (ProductCat 𝒟.U ℰ.U) (F.₀ A , G.₀ A)
      F-resp-⊥′ A-isInitial = record
          { ! = F[A]-isInitial.! , G[A]-isInitial.!
          ; !-unique = dmap F[A]-isInitial.!-unique G[A]-isInitial.!-unique
          }
        where
          module F[A]-isInitial = IsInitial (F-resp-⊥ A-isInitial)
          module G[A]-isInitial = IsInitial (G-resp-⊥ A-isInitial)
      F-resp-+′
          : {A B C : 𝒞.Obj} {i₁ : 𝒞.U [ A , C ]} {i₂ : 𝒞.U [ B , C ]}
          → IsCoproduct 𝒞.U i₁ i₂
          → IsCoproduct (ProductCat 𝒟.U ℰ.U) (F.₁ i₁ , G.₁ i₁) (F.₁ i₂ , G.₁ i₂)
      F-resp-+′ {A} {B} {A+B} A+B-isCoproduct = record
          { [_,_] = zip′ F[A+B]-isCoproduct.[_,_] G[A+B]-isCoproduct.[_,_]
          ; inject₁ = F[A+B]-isCoproduct.inject₁ , G[A+B]-isCoproduct.inject₁
          ; inject₂ = F[A+B]-isCoproduct.inject₂ , G[A+B]-isCoproduct.inject₂
          ; unique = zip′ F[A+B]-isCoproduct.unique G[A+B]-isCoproduct.unique
          }
        where
          module F[A+B]-isCoproduct = IsCoproduct (F-resp-+ A+B-isCoproduct)
          module G[A+B]-isCoproduct = IsCoproduct (G-resp-+ A+B-isCoproduct)
      F-resp-coeq′
          : {A B C : 𝒞.Obj} {f g : 𝒞.U [ A , B ]} {h : 𝒞.U [ B , C ]}
          → IsCoequalizer 𝒞.U f g h
          → IsCoequalizer (ProductCat 𝒟.U ℰ.U) (F.₁ f , G.₁ f) (F.₁ g , G.₁ g) (F.₁ h , G.₁ h)
      F-resp-coeq′ h-isCoequalizer = record
          { equality = F[h]-isCoequalizer.equality , G[h]-isCoequalizer.equality
          ; coequalize = map F[h]-isCoequalizer.coequalize G[h]-isCoequalizer.coequalize
          ; universal = F[h]-isCoequalizer.universal , G[h]-isCoequalizer.universal
          ; unique = map F[h]-isCoequalizer.unique G[h]-isCoequalizer.unique
          }
        where
          module F[h]-isCoequalizer = IsCoequalizer (F-resp-coeq h-isCoequalizer)
          module G[h]-isCoequalizer = IsCoequalizer (G-resp-coeq h-isCoequalizer)

  IsRightExact-⁂
      : {𝒜 ℬ 𝒞 𝒟 : FinitelyCocompleteCategory o ℓ e}
        (F : Functor (U 𝒜) (U 𝒞))
        (G : Functor (U ℬ) (U 𝒟))
      → IsRightExact 𝒜 𝒞 F
      → IsRightExact ℬ 𝒟 G
      → IsRightExact (𝒜 × ℬ) (𝒞 × 𝒟) (F ⁂ G)
  IsRightExact-⁂ {𝒜} {ℬ} {𝒞} {𝒟} F G isRightExact-F isRightExact-G = record 
      { F-resp-⊥ = F-resp-⊥′
      ; F-resp-+ = F-resp-+′
      ; F-resp-coeq = F-resp-coeq′
      }
    where
      module 𝒜 = FinitelyCocompleteCategory 𝒜
      module ℬ = FinitelyCocompleteCategory ℬ
      module 𝒞 = FinitelyCocompleteCategory 𝒞
      module 𝒟 = FinitelyCocompleteCategory 𝒟
      module 𝒜×ℬ = FinitelyCocompleteCategory (𝒜 × ℬ)
      module 𝒞×𝒟 = FinitelyCocompleteCategory (𝒞 × 𝒟)
      open IsRightExact isRightExact-F
      open IsRightExact isRightExact-G renaming (F-resp-⊥ to G-resp-⊥; F-resp-+ to G-resp-+; F-resp-coeq to G-resp-coeq)
      module F = Functor F
      module G = Functor G
      F-resp-⊥′
          : {(A , B) : 𝒜×ℬ.Obj}
          → IsInitial 𝒜×ℬ.U (A , B)
          → IsInitial 𝒞×𝒟.U (F.₀ A , G.₀ B)
      F-resp-⊥′ {A , B} A,B-isInitial = record
          { ! = F[A]-isInitial.! , G[B]-isInitial.!
          ; !-unique = dmap F[A]-isInitial.!-unique G[B]-isInitial.!-unique
          }
        where
          module A,B-isInitial = IsInitial A,B-isInitial
          A-isInitial : IsInitial 𝒜.U A
          A-isInitial = record
              { ! = λ { {X} → proj₁ (A,B-isInitial.! {X , B}) }
              ; !-unique = λ { f → proj₁ (A,B-isInitial.!-unique (f , ℬ.id)) }
              }
          B-isInitial : IsInitial ℬ.U B
          B-isInitial = record
              { ! = λ { {X} → proj₂ (A,B-isInitial.! {A , X}) }
              ; !-unique = λ { f → proj₂ (A,B-isInitial.!-unique (𝒜.id , f)) }
              }
          module F[A]-isInitial = IsInitial (F-resp-⊥ A-isInitial)
          module G[B]-isInitial = IsInitial (G-resp-⊥ B-isInitial)
      F-resp-+′
          : {A B C : 𝒜×ℬ.Obj} {(i₁ , i₁′) : 𝒜×ℬ.U [ A , C ]} {(i₂ , i₂′) : 𝒜×ℬ.U [ B , C ]}
          → IsCoproduct 𝒜×ℬ.U (i₁ , i₁′) (i₂ , i₂′)
          → IsCoproduct 𝒞×𝒟.U (F.₁ i₁ , G.₁ i₁′) (F.₁ i₂ , G.₁ i₂′)
      F-resp-+′ {A} {B} {A+B} {i₁ , i₁′} {i₂ , i₂′} A+B,A+B′-isCoproduct = record
          { [_,_] = zip′ F[A+B]-isCoproduct.[_,_] G[A+B′]-isCoproduct.[_,_]
          ; inject₁ = F[A+B]-isCoproduct.inject₁ , G[A+B′]-isCoproduct.inject₁
          ; inject₂ = F[A+B]-isCoproduct.inject₂ , G[A+B′]-isCoproduct.inject₂
          ; unique = zip′ F[A+B]-isCoproduct.unique G[A+B′]-isCoproduct.unique
          }
        where
          module A+B,A+B′-isCoproduct = IsCoproduct A+B,A+B′-isCoproduct
          A+B-isCoproduct : IsCoproduct 𝒜.U i₁ i₂
          A+B-isCoproduct = record
              { [_,_] = λ { f g → proj₁ (A+B,A+B′-isCoproduct.[ (f , i₁′) , (g , i₂′) ]) }
              ; inject₁ = proj₁ A+B,A+B′-isCoproduct.inject₁
              ; inject₂ = proj₁ A+B,A+B′-isCoproduct.inject₂
              ; unique = λ { ≈f ≈g → proj₁ (A+B,A+B′-isCoproduct.unique (≈f , ℬ.identityˡ) (≈g , ℬ.identityˡ)) }
              }
          A+B′-isCoproduct : IsCoproduct ℬ.U i₁′ i₂′
          A+B′-isCoproduct = record
              { [_,_] = λ { f g → proj₂ (A+B,A+B′-isCoproduct.[ (i₁ , f) , (i₂ , g) ]) }
              ; inject₁ = proj₂ A+B,A+B′-isCoproduct.inject₁
              ; inject₂ = proj₂ A+B,A+B′-isCoproduct.inject₂
              ; unique = λ { ≈f ≈g → proj₂ (A+B,A+B′-isCoproduct.unique (𝒜.identityˡ , ≈f) (𝒜.identityˡ , ≈g)) }
              }
          module F[A+B]-isCoproduct = IsCoproduct (F-resp-+ A+B-isCoproduct)
          module G[A+B′]-isCoproduct = IsCoproduct (G-resp-+ A+B′-isCoproduct)
      F-resp-coeq′
          : {A B C : 𝒜×ℬ.Obj} {(f , f′) (g , g′) : 𝒜×ℬ.U [ A , B ]} {(h , h′) : 𝒜×ℬ.U [ B , C ]}
          → IsCoequalizer 𝒜×ℬ.U (f , f′) (g , g′) (h , h′)
          → IsCoequalizer 𝒞×𝒟.U (F.₁ f , G.₁ f′) (F.₁ g , G.₁ g′) (F.₁ h , G.₁ h′)
      F-resp-coeq′ {_} {_} {_} {f , f′} {g , g′} {h , h′} h,h′-isCoequalizer = record
          { equality = F[h]-isCoequalizer.equality , G[h′]-isCoequalizer.equality
          ; coequalize = map F[h]-isCoequalizer.coequalize G[h′]-isCoequalizer.coequalize
          ; universal = F[h]-isCoequalizer.universal , G[h′]-isCoequalizer.universal
          ; unique = map F[h]-isCoequalizer.unique G[h′]-isCoequalizer.unique
          }
        where
          module h,h′-isCoequalizer = IsCoequalizer h,h′-isCoequalizer
          h-isCoequalizer : IsCoequalizer 𝒜.U f g h
          h-isCoequalizer = record
              { equality = proj₁ h,h′-isCoequalizer.equality
              ; coequalize = λ { eq → proj₁ (h,h′-isCoequalizer.coequalize (eq , proj₂ h,h′-isCoequalizer.equality)) }
              ; universal = proj₁ h,h′-isCoequalizer.universal
              ; unique = λ { ≈h → proj₁ (h,h′-isCoequalizer.unique (≈h , ℬ.Equiv.sym ℬ.identityˡ)) }
              }
          h′-isCoequalizer : IsCoequalizer ℬ.U f′ g′ h′
          h′-isCoequalizer = record
              { equality = proj₂ h,h′-isCoequalizer.equality
              ; coequalize = λ { eq′ → proj₂ (h,h′-isCoequalizer.coequalize (proj₁ h,h′-isCoequalizer.equality , eq′)) }
              ; universal = proj₂ h,h′-isCoequalizer.universal
              ; unique = λ { ≈h′ → proj₂ (h,h′-isCoequalizer.unique (𝒜.Equiv.sym 𝒜.identityˡ , ≈h′)) }
              }

          module F[h]-isCoequalizer = IsCoequalizer (F-resp-coeq h-isCoequalizer)
          module G[h′]-isCoequalizer = IsCoequalizer (G-resp-coeq h′-isCoequalizer)
_×₁_
    : {𝒜 ℬ 𝒞 𝒟 : FinitelyCocompleteCategory o ℓ e}
    → RightExactFunctor 𝒜 𝒞
    → RightExactFunctor ℬ 𝒟
    → RightExactFunctor (𝒜 × ℬ) (𝒞 × 𝒟)
F ×₁ G = record
    { F = F.F ⁂ G.F
    ; isRightExact = IsRightExact-⁂ F.F G.F F.isRightExact G.isRightExact
    }
  where
    module F = RightExactFunctor F
    module G = RightExactFunctor G

FinitelyCocompletes-Products : {𝒞 𝒟 : FinitelyCocompleteCategory o ℓ e} → Product FinitelyCocompletes 𝒞 𝒟
FinitelyCocompletes-Products {𝒞} {𝒟} = record
    { A×B = 𝒞 × 𝒟
    ; π₁ = rightexact πˡ (πˡ-RightExact 𝒞 𝒟)
    ; π₂ = rightexact πʳ (πʳ-RightExact 𝒞 𝒟)
    ; ⟨_,_⟩ = λ { (rightexact F isF) (rightexact G isG) → rightexact (F ※ G) (IsRightExact-※  F G isF isG) }
    ; project₁ = λ { {_} {rightexact F _} {rightexact G _} → Cats.project₁ {h = F} {i = G} }
    ; project₂ = λ { {_} {rightexact F _} {rightexact G _} → Cats.project₂ {h = F} {i = G} }
    ; unique = Cats.unique
    }
  where
    module 𝒞 = FinitelyCocompleteCategory 𝒞
    module 𝒟 = FinitelyCocompleteCategory 𝒟
    module Cats = BinaryProducts Products.Cats-has-all

FinitelyCocompletes-BinaryProducts : BinaryProducts FinitelyCocompletes
FinitelyCocompletes-BinaryProducts = record
    { product = FinitelyCocompletes-Products
    }

FinitelyCocompletes-Cartesian : Cartesian FinitelyCocompletes
FinitelyCocompletes-Cartesian = record 
    { terminal = record
        { ⊤ = One-FCC
        ; ⊤-is-terminal = _
        }
    ; products = FinitelyCocompletes-BinaryProducts
    }
