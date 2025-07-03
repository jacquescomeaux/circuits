{-# OPTIONS --without-K --guardedness --safe #-}

open import Text.Parser.Types.Core using (Parameters)

module Data.SExp.Parser {l} {P : Parameters l} where

import Data.String.Base as String
open import Data.List as List using (List)

open import Data.Char.Base using (Char)
open import Data.List.Sized.Interface using (Sized)
open import Data.List.NonEmpty as List⁺ using (List⁺) renaming (map to map⁺)
open import Data.Subset using (Subset; into)
open import Effect.Monad using (RawMonadPlus)
open import Function.Base using (_∘_; _$_)
open import Induction.Nat.Strong using (fix; map; □_)
open import Relation.Binary.PropositionalEquality.Decidable using (DecidableEquality)
open import Relation.Unary using (IUniversal; _⇒_)
open import Level.Bounded using (theSet; [_])
open import Text.Parser.Types P using (Parser)
open import Text.Parser.Combinators {P = P} using (_<$>_; list⁺; _<|>_; _<$_; _<&_; _<&?_; box)
open import Text.Parser.Combinators.Char {P = P} using (alpha; parens; withSpaces; spaces; char)
open import Text.Parser.Combinators.Numbers {P = P} using (decimalℕ)

open import Data.SExp using (SExp)
open SExp

open Parameters P using (M; Tok; Toks)

module _
    {{𝕄 : RawMonadPlus M}}
    {{𝕊 : Sized Tok Toks}}
    {{𝔻 : DecidableEquality (theSet Tok)}}
    {{ℂ : Subset Char (theSet Tok)}}
    {{ℂ⁻ : Subset (theSet Tok) Char}}
  where

  -- An atom is just a non-empty list of alphabetical characters.
  -- We use `<$>` to turn that back into a string and apply the `Atom` constructor.
  atom : ∀[ Parser [ SExp ] ]
  atom = Atom ∘ String.fromList⁺ ∘ map⁺ (into ℂ⁻) <$> list⁺ alpha

  -- Natural number parser
  nat : ∀[ Parser [ SExp ] ]
  nat = Nat <$> decimalℕ

  -- Empty list parser
  nil : ∀[ Parser [ SExp ] ]
  nil = SExps List.[] <$ char '(' <&? box spaces <& box (char ')')

  -- Parser for a list of S-Expressions
  list : ∀[ Parser [ SExp ] ⇒ Parser [ List SExp ] ]
  list sexp = List⁺.toList <$> list⁺ (withSpaces sexp)

  -- Compound S-Expression parser
  compound : ∀[ □ Parser [ SExp ] ⇒ Parser [ SExp ] ]
  compound rec = nil <|> SExps <$> parens (map list rec)

  -- S-Expression parser
  sexp : ∀[ □ Parser [ SExp ] ⇒ Parser [ SExp ] ]
  sexp rec = atom <|> nat <|> compound rec

  -- Build the parser as a fixpoint since SExp is an inductive type
  sexp-top : ∀[ Parser [ SExp ] ]
  sexp-top = fix (Parser [ SExp ]) sexp

  -- Top-level parser for list of S-Expressions
  LIST : ∀[ Parser [ SExp ] ]
  LIST = SExps <$> list sexp-top

  -- Top-level S-Expression parser
  SEXP : ∀[ Parser [ SExp ] ]
  SEXP = withSpaces sexp-top
