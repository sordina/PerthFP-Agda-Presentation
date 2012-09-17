

> module Email where


Lyndon,

Yes, one solution is to prove this fact about natural numbers. You can
construct such a proof using the standard library:

2012/6/15 Lyndon Maydwell <maydwell@gmail.com>:

> vrev (y ► ys) = vconcat (vrev ys) (y ► ε)
>
> open import Data.Nat.Properties
> open import Relation.Binary.PropositionalEquality
> open import Algebra.Structures
> open import Function
>
> open IsCommutativeSemiring isCommutativeSemiring using (+-comm)
>
> {- ... -}
>
> vrev {A} {suc n} (y ► ys) = subst (Vec _) (+-comm _ 1) $ vconcat (vrev ys) (y ► ε)

However, such casts are a bit unnice, and they typically get in your
way when proving properties of vrev. There are sometimes better
ways to organise your code that allow you to avoid casts. For
example, if you look in the standard library in Data.Vec, you can find
a cleaner way to make everything work (translated to your naming):

> foldl : ∀ {b} {A : Set} (B : ℕ → Set b) {m} →
>          (∀ {n} → B n → A → B (suc n)) →
>          B zero →
>          Vec A m → B m
> foldl b _⊕_ n ε       = n
> foldl b _⊕_ n (x ► xs) = foldl (λ n → b (suc n)) _⊕_ (n ⊕ x) xs
>
> reverse : {A : Set} → {n : ℕ} → Vec A n → Vec A n
> reverse {A} = foldl (Vec A) (flip _►_) ε

You might exploit the same strategy directly, by defining a version of
Data.Nat._+_ that has a different recursion structure:

> reverse : {A : Set} → {n : ℕ} → Vec A n → Vec A n
> reverse {A} = go 0 (flip _►_) ε
>   where _+′_ : ℕ → ℕ → ℕ
>         x +′ zero = x
>         x +′ suc y = suc x +′ y
>
>         go : ∀ m {n} {A : Set} →
>              (∀ {n} → Vec A (n +′ m) → A → Vec A (n +′ suc m)) →
>              Vec A (0 +′ m) →
>              Vec A n → Vec A (n +′ m)
>         go m _⊕_ n ε       = n
>         go m _⊕_ n (x ► xs) = go (suc m) _⊕_ (n ⊕ x) xs

A crucial point here is that while folding, the type of _⊕_ changes to
keep track of the current length of the accumulator. I mean that after
m iterations of foldl, _⊕_'s type will amount to something like

  (∀ {n} → Vec A (m +′ n) → A → Vec A (m +′ suc n))

where the type of _►_ would be hard to work with:

  (∀ {n} → Vec A n → A → Vec A (suc n))

Note also that the recursion structure of _+′_ that we had to define
internally is the same as the recursion structure of the indices of
the vectors in the recursion of go (i.e. we shift one element from the
iteratee to the accumulator each time, so indices (m, suc b) are
turned into indices (suc m, n)).

Anyway, the point is that you can sometimes avoid casts like the subst
call above by organizing your code in the best way. This best way may
be hard to find though...
