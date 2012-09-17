

-- Moving Forward: Inductive Types, Libraries
-- Source is available at https://github.com/sordina/PerthFP-Agda-Presentation


module B_Inductive_Types where

-- We've seen parametized data-constuctors before with Maybe, however,
-- we can make the constructor recursive easily to form an inductive type:

data Natural : Set where
  Zero : Natural
  Succ : Natural → Natural

-- This allows us to use the 'Peano' number system:

naught : Natural
naught = Zero

one    : Natural
one    = Succ Zero

-- Emacs Aside { C-d one, C-n one }

-- It would be a shame if we had to define our own types for everything,
-- luckily there is a standard library for Agda!

open import Data.Nat

-- The first time that a standard library is loaded it is usually __SLOOOOOOW__
-- Agda is hardly optimized for compilation at this point... Anyway...

-- We can now use the nice features of the Nat Library such as 'Builtin' functionality:

naught' : ℕ
naught' = 0

-- Use '\bn' for the ℕ symbol
-- If you're interested in the code for a symbol in the current file use "C-u C-x ="

one' : ℕ
one' = 1


-- There are modules available in the Agda standard library to encompass many tasks.
-- We will leave them be for the remainder of this tutorial.


-- One final inductive data-type will be defined in this module - The List!

data List (A : Set) : Set where
  ε   : List A
  _►_ : A → List A → List A

-- Note, we take full advantage of unicode and mixfix notation here.
-- Now some functions:

-- Try and fail to define head:
-- head : List A → A
-- 

tail : {A : Set} → List A → List A
tail ε        = ε
tail (y ► y') = y' -- '\t7' -- Remember: 'C-u C-x =' for hints on a character.

map : {A B : Set} → (A → B) → List A → List B
map f ε = ε
map f (y ► y') = f y ►  map f y'

_++_ : {A : Set} → List A → List A → List A
ε ++ r        = ε
(y ► y') ++ r = y ►  (y' ++ r)

singleton : {A : Set} → A → List A
singleton x = x ►  ε

reverse : {A : Set} → List A → List A
reverse ε = ε
reverse (y ► y') = reverse y' ++ singleton y