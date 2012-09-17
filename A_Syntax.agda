

-- Here begins our Ultra-Basic Agda Tutorial
-- Source is available at https://github.com/sordina/PerthFP-Agda-Presentation

-- Modules:

module A_Syntax where

-- Imports:

open import Data.Nat
open import Data.Bool

-- Tokens must ALWAYS be separated by whitespace except when next to...
--
-- - Parentheses "()"
-- - Underscores "_"
--
-- This includes Arithmatic operators "+-*/" etc.

-- Data-definitions:

data Foo : Set where
  FooInhabitant1 : Foo
  FooInhabitant2 : Foo

-- Value-definitions:

baz : Foo
baz = FooInhabitant1

-- Records:

record Quux : Set where
  field
    Y : Foo

  -- Implicit Type Arguments

  default : {A : Set} → Foo
  default = FooInhabitant1

-- Unicode:

γ : ℕ  -- \bn
γ = 0  -- \gamma

-- MixFix - Underscores denote placeholders:

_+++_ : ℕ → ℕ → ℕ
a +++ b = a + b

-- Advanced Mixfix

ifis_thenis_elseis_ : {A : Set} → Bool → A → A → A
ifis true  thenis x elseis y = x
ifis false thenis x elseis y = y
