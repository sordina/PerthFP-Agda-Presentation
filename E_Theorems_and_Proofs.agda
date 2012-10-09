

-- Theorems and Proofs - Using Agda for her intended purpose
-- Source is available at https://github.com/sordina/PerthFP-Agda-Presentation


module E_Theorems_and_Proofs where


-- Simple Tuple (Parens are special sauce - Leave them OUT!)

data _⨂_ (A : Set) (B : Set) : Set where
  _,_ : A → B → A ⨂ B
  -- ⨂ - \Ox

open import Data.Bool

foo  : Bool ⨂ Bool
foo = false , true



-- Have you brushed up on your natural deduction?

-- Theorem:

left-elimination : ∀ { A B } → A ⨂ B → A -- Underscore is special sauce - Hyphens are O.K.!

-- Proof:

left-elimination (x , y) = x

-- The 'Proofs' chapter from Learn you an Agda serves as a good introduction
-- to this style of proof.


-- One thing you will often find when writing proofs in Agda is that
-- the 'shape' of your proof will nearly always match the shape of
-- the data-structures involved in the proof. If it does not, you may
-- find it easier to rewrite your data-structure than to rewrite your
-- proof!


-- Another surprising feature of agda, is that sometimes writing what
-- you would think to be a straight-forward method may start to resemble
-- a proof-task.

-- This highlights that there are some underlying assumptions that you
-- have made that also need to be proven.

-- Take the humble vector:

open import Data.Nat

data Vec (A : Set) : ℕ → Set where
   ε   : Vec A zero
   _►_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

vconcat : {A : Set} → {m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
vconcat ε y = y
vconcat (y ► ys) xs = y ►  (vconcat ys xs)

-- Obviously vrev is just - 
--vrev2 : {A : Set} → {n : ℕ} → Vec A n → Vec A n
--vrev2 ε = ε
--vrev2 (y ► ys) = vconcat (vrev2 ys) (y ► ε)

-- ... Except it isn't :-(

-- Dominique from KU Leuven University kindly supplied the following solution:

open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Algebra.Structures
open import Function

open IsCommutativeSemiring isCommutativeSemiring using (+-comm)

vrev : {A : Set} → {n : ℕ} → Vec A n → Vec A n
vrev ε = ε
vrev {A} {suc n} (y ► ys) = subst (Vec _) (+-comm _ 1) $ vconcat (vrev ys) (y ► ε)

-- We won't dissect this in any depth, but at a glance you can see that we are incorporation
-- 
-- * Properties of the natural numbers
-- * Propositional equality
-- * Algebraic structure
-- * Commutivity of addition

-- This is starting to look a lot more hairy, but it makes sense when you try to match
-- the structure of our initial attempt at a proof to the structure of the definition
-- of the natural numbers.
