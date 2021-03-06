

-- Basic Types in Agda
-- Source is available at https://github.com/sordina/PerthFP-Agda-Presentation


-- All Agda modules must declare the module name before any other definitions.
-- The module name must match the file-name, minus the .agda suffix:

module B_Basic_Types where

-- The most basic Agda construct is the data definition.
-- The form of a data-definition is:

data Foo : Set where
  FooInhabitant1 : Foo
  FooInhabitant2 : Foo

-- If you are familiar with Haskell's GADT data-type definitions, this should be
-- immediately recognizable.

-- Here is a less abstract data-type:

data Bool : Set where
  True  : Bool
  False : Bool

-- As an aside, Agda is traditionally edited in Emacs.
-- While there are many good reasons to prefer other editors, the Emacs support
-- for Agda (and lack of support in other editors) makes it the undisputedly
-- superior tool for editing Agda.

-- A couple of Emacs Agda Commands:
-- C-c C-h : Agda Commands List
-- C-c C-l : Load the current file
-- C-c C-d : Type of expression
-- C-c C-n : Evaluate expression

not : Bool → Bool
not True = False
not False = True

-- Here are C-c C-d and C-c C-n used with not {Editor Aside - not, not True}
-- Now back to Agda!


-- Here are some examples of higher-order functions:

const : {A B : Set} → A → B → A
const a = λ _ → a

-- Unlike Haskell, you must define the types of all type variables.
-- The base-type is 'Set'.

id : {A : Set} → A → A
id x = x

-- Editor Aside {const, const True, Const True True, id const, id const True, id const not True True}

-- Here is an example of a parametized type - Maybe.
-- If you are familiar with Haskell, then it needs no explanation, however,
-- if you are not, then Maybe represents the concept of 'Null' from other
-- languages.

data Maybe (A : Set) : Set where
  Nothing :     Maybe A
  Just    : A → Maybe A

trivial-theorem : Bool
trivial-theorem = True

bindMaybe : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
bindMaybe Nothing  f = Nothing
bindMaybe (Just y) f = f y

returnMaybe : {A : Set} → A → Maybe A
returnMaybe x = Just x

-- This is all well and good, but if you are familiar with Haskell's type-classes
-- then suffixing the type of the monadic functions for each type will
-- seem like a dirty hack - And it is!

-- Although agda doesn't have type-classes, it has records, and combined with
-- implicit-parameters, these are strictly more powerful than type-classes
-- as they can be used implicityly, but overridden without the use
-- of ugly newtype wrappers :-)

-- Here is the Monad Class from Haskell defined in Agda:

record Monad (M : Set → Set) : Set₁ where
  field
    return : {A   : Set} → A → M A
    _>>=_  : {A B : Set} → M A → (A → M B) → M B

  -- We can define default implemetations inside the record, but outside the fields:
  join : {A : Set} → M (M A) → M A
  join x = x >>= id

-- 'Class Instances' are defined as stand-alone values of the correct types

Maybe-Monad : Monad Maybe
Maybe-Monad = record { return  = returnMaybe
                     ; _>>=_   = bindMaybe
                     }

-- Using the Monad Instance Explicitly:

maybe-monad-test : Maybe Bool
maybe-monad-test = Monad.return Maybe-Monad True
