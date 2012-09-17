

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