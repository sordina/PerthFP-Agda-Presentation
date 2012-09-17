

-- Here begins our Ultra-Basic Agda Tutorial
-- Source is available at https://github.com/sordina/PerthFP-Agda-Presentation

-- Modules:

module AA_Syntax where

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