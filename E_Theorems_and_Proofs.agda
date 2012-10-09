

-- Theorems and Proofs - Using Agda for her intended purpose
-- Source is available at https://github.com/sordina/PerthFP-Agda-Presentation


module E_Theorems_and_Proofs where


-- Simple Tuple (Parens are special sauce - Leave them OUT!)

data _⨂_ (A : Set) (B : Set) : Set where
  _,_ : A → B → A ⨂ B
  -- ⨂ - \Ox



-- Have you brushed up on your natural deduction?

-- Theorem:

left-elimination : ∀ { A B } → A ⨂ B → A -- Underscore is special sauce - Hyphens are O.K.!

-- Proof:

left-elimination (x , x₁) = x


-- One thing you will often find when writing proofs in Agda is that the 'shape' of your proof will
-- nearly always match the shape of the data-structures involved in the proof.
