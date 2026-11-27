import Mathlib
import Theorems.WilsonTheorem.A
import Theorems.WilsonTheorem.B

/-!
# Wilson's theorem: statements A and B are equivalent (Euler)

The proof matches the two statements: the prime side is identical, the product
`∏ k ∈ Ico 1 n, k` is `(n-1)!`, and `(n-1)! ≡ -1 [ZMOD n]` is `n ∣ (n-1)! + 1`.
Each direction uses the other statement as a hypothesis.
-/

namespace TuriMath.WilsonTheorem

open Nat

/-- Core matching step: A's congruence clause is B's divisibility clause. -/
theorem clause_iff (n : ℕ) (hn : 1 < n) :
    ((((n - 1)! : ℕ) : ℤ) ≡ -1 [ZMOD (n : ℤ)]) ↔ n ∣ (∏ k ∈ Finset.Ico 1 n, k) + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.prod_Ico_id_eq_factorial, Int.modEq_iff_dvd]
  have : (-1 - (((m + 1 - 1)! : ℕ) : ℤ)) = -(((m ! + 1 : ℕ) : ℤ)) := by
    simp; ring
  rw [this, dvd_neg, Int.natCast_dvd_natCast]

theorem equiv : A.Statement ↔ B.Statement := by
  constructor
  · intro h n hn
    rw [← clause_iff n hn]
    exact h n hn
  · intro h n hn
    rw [clause_iff n hn]
    exact h n hn

end TuriMath.WilsonTheorem
