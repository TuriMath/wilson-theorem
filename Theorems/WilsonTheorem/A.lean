import Mathlib

/-!
# Wilson's theorem — statement A (Noether, Formalizer A)

Source (issue TuriMath/wilson-theorem#1, Wikipedia "Wilson's theorem", lead):
> Wilson's theorem states that a natural number n > 1 is a prime number if and only if
> the product of all the positive integers less than n is one less than a multiple of n.
> … (n − 1)! ≡ −1 (mod n)

Choices:
* `n : ℕ` because the source says "a natural number n".
* `Nat.Prime` is Mathlib's notion of prime natural number.
* The congruence is stated in `ℤ` (`Int.ModEq`) because "−1" and "one less than a multiple
  of n" live in the integers; `n - 1` is truncated `ℕ` subtraction, exact since `1 < n`.
-/

namespace TuriMath.WilsonTheorem.A

open Nat

/-- Wilson's theorem, both directions.

* "a natural number n"                                  ↦ `∀ n : ℕ`
* "n > 1"                                               ↦ `1 < n →`
* "is a prime number"                                   ↦ `n.Prime`
* "if and only if"                                      ↦ `↔`
* "the product of all the positive integers less than n" ↦ `(n - 1)!`, cast to `ℤ`
* "is one less than a multiple of n", "≡ −1 (mod n)"    ↦ `≡ -1 [ZMOD (n : ℤ)]`
-/
def Statement : Prop :=
  ∀ n : ℕ, 1 < n → (n.Prime ↔ (((n - 1)! : ℕ) : ℤ) ≡ -1 [ZMOD (n : ℤ)])

/-! ## Sanity section -/

/-- The only hypothesis, `1 < n`, is satisfiable. -/
example : ∃ n : ℕ, 1 < n := ⟨2, by norm_num⟩

/-- "Product of all positive integers less than n" really is `(n - 1)!`: for n = 5, 1·2·3·4. -/
example : (5 - 1)! = ∏ i ∈ Finset.Ico 1 5, i := by decide

/-- The right-hand side holds at the prime n = 5: 4! = 24 = 25 − 1. -/
example : (((5 - 1)! : ℕ) : ℤ) ≡ -1 [ZMOD (5 : ℤ)] := by decide

/-- The right-hand side fails at the composite n = 4: 3! = 6 ≢ −1 (mod 4). -/
example : ¬ ((((4 - 1)! : ℕ) : ℤ) ≡ -1 [ZMOD (4 : ℤ)]) := by decide

end TuriMath.WilsonTheorem.A
