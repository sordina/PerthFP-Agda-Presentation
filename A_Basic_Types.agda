

-- Here begins our Ultra-Basic Agda Tutorial
-- Source is available at https://github.com/sordina/PerthFP-Agda-Presentation


-- All Agda modules must declare the module name before any other definitions.
-- The module name must match the file-name, minus the .agda suffix:

module A_Basic_Types where

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
not True  = False
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

bindMaybe : {A B : Set} → (A → Maybe B) → Maybe A → Maybe B
bindMaybe f Nothing  = Nothing
bindMaybe f (Just y) = f y

returnMaybe : {A : Set} → A → Maybe A
returnMaybe x = Just x

record Monad (A : Set) : Set where
  field
     return : A
     _>>=_  : A