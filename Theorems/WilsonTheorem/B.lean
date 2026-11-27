import Mathlib

/-!
# Wilson's theorem — statement B (Gauss, blind formalizer)

Source (TuriMath/wilson-theorem#1, Wikipedia "Wilson's theorem", lead):
> Wilson's theorem states that a natural number n > 1 is a prime number if and only if
> the product of all the positive integers less than n is one less than a multiple of n.
> … (n − 1)! ≡ −1 (mod n)

Mapping, one line per part of the quote:
* "a natural number n"                         ↦ `∀ n : ℕ`
* "n > 1"                                      ↦ hypothesis `1 < n`
* "is a prime number"                          ↦ `Nat.Prime n`
* "if and only if"                             ↦ `↔` (both directions)
* "the product of all the positive integers
   less than n"                                ↦ `∏ k ∈ Finset.Ico 1 n, k` (k = 1, 2, …, n − 1), i.e. (n − 1)!
* "is one less than a multiple of n"           ↦ `n ∣ (∏ k ∈ Finset.Ico 1 n, k) + 1`
   (that is, (n − 1)! ≡ −1 (mod n), stated with divisibility in ℕ, no ZMod and no negatives)

The elementary phrasing (literal product, divisibility in ℕ) is chosen on purpose,
so that the equivalence check against statement A is a real check.
-/

namespace TuriMath.WilsonTheorem.B

open Finset

/-- Wilson's theorem: for every natural number `n > 1`, `n` is prime iff
`n` divides `1 · 2 · ⋯ · (n − 1) + 1`. -/
def Statement : Prop :=
  ∀ n : ℕ, 1 < n → (Nat.Prime n ↔ n ∣ (∏ k ∈ Ico 1 n, k) + 1)

/-! ## Sanity section -/

/-- The hypothesis `1 < n` can hold, both for a prime and for a composite. -/
example : (1 : ℕ) < 2 := by norm_num
example : (1 : ℕ) < 4 := by norm_num

/-- The literal product is the factorial `(n − 1)!` the source writes. -/
example (n : ℕ) : ∏ k ∈ Ico 1 (n + 1), k = n.factorial := Finset.prod_Ico_id_eq_factorial n

/-! ## Concrete checks -/

-- n = 5 (prime): 1·2·3·4 = 24, and 24 + 1 = 25 = 5·5. Both sides true.
example : ∏ k ∈ Ico 1 5, k = 24 := by decide
example : Nat.Prime 5 ∧ 5 ∣ (∏ k ∈ Ico 1 5, k) + 1 := by decide

-- n = 4 (composite): 1·2·3 = 6, and 6 + 1 = 7 is not a multiple of 4. Both sides false.
example : ¬ Nat.Prime 4 ∧ ¬ 4 ∣ (∏ k ∈ Ico 1 4, k) + 1 := by decide

-- n = 7 (prime): 6! = 720, and 721 = 7·103.
example : Nat.Prime 7 ∧ 7 ∣ (∏ k ∈ Ico 1 7, k) + 1 := by decide

-- n = 6 (composite): 5! = 120, and 121 = 11² is not a multiple of 6.
example : ¬ Nat.Prime 6 ∧ ¬ 6 ∣ (∏ k ∈ Ico 1 6, k) + 1 := by decide

-- n = 2 (smallest case): the product is just 1, and 1 + 1 = 2.
example : Nat.Prime 2 ∧ 2 ∣ (∏ k ∈ Ico 1 2, k) + 1 := by decide

/-- The statement's instance at n = 5 is consistent with the concrete check. -/
example (h : Statement) : 5 ∣ (∏ k ∈ Ico 1 5, k) + 1 := (h 5 (by norm_num)).1 (by norm_num)

end TuriMath.WilsonTheorem.B
