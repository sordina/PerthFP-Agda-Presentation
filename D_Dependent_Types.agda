

-- Dependent Types: Agda-Specific Funcitonality
-- Source is available at https://github.com/sordina/PerthFP-Agda-Presentation


module D_Dependent_Types where

-- We were previously looking at the list

data Maybe (A : Set) : Set where
  Nothing :     Maybe A
  Just    : A → Maybe A

data List (A : Set) : Set where
  ε   : List A
  _►_ : A → List A → List A

head-list : {A : Set} → List A → Maybe A
head-list  ε         = Nothing
head-list  (y ► y')  = Just y

data Vector : Set where

-- Taken from http://www.jonmsterling.com/posts/2012-09-07-pi-is-for-power-sigma-for-product.html:
--
-- We use (dependent) records rather than plain-old data declarations
-- because these conveniently provide accessors; an accessor for a
-- Π-type corresponds to function application.

record Π (α : Set) (β : α → Set) : Set where
  constructor Λ
  field _$_ : ((x : α) → β x)

record Σ (α : Set) (β : α → Set) : Set where
  constructor _,_
  field
    fst : α
    snd : β fst

-- A special case of Π: the function arrow.
_~>_ : Set → Set → Set
_~>_ α β = Π α (λ _ → β)

-- A special case of Σ: the cartesian product.
_×_ : Set → Set → Set
_×_ α β = Σ α (λ _ → β)