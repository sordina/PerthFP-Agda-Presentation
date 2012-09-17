

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
