import Mathlib
import Theorems.WilsonTheorem.A

/-!
# Wilson's theorem: proof (Euler)

Not a citation of `ZMod.wilsons_lemma` or `Nat.prime_iff_fac_equiv_neg_one`.
* (→) In the field `ZMod p`, `(p-1)! = ∏ of all nonzero elements = ∏ of units = -1`,
  using `prod_univ_units_id_eq_neg_one` (the product of the units of a finite field is `-1`).
* (←) If `n` is composite, its least prime factor `p` is `< n`, so `p ∣ (n-1)!`;
  but `p ∣ n ∣ (n-1)! + 1`, so `p ∣ 1`, absurd.
-/

namespace TuriMath.WilsonTheorem

open Nat Finset

theorem fact_prime_zmod (p : ℕ) [Fact p.Prime] : (((p - 1)! : ℕ) : ZMod p) = -1 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h1 : (((p - 1)! : ℕ) : ZMod p) = ∏ x ∈ Ico 1 p, (x : ZMod p) := by
    have e : ∏ i ∈ Ico 1 p, i = (p - 1)! := by
      have := Finset.prod_Ico_id_eq_factorial (p - 1)
      rwa [Nat.sub_add_cancel hp] at this
    rw [← Nat.cast_prod, e]
  have h2 : ∏ x ∈ Ico 1 p, (x : ZMod p) = ∏ x : (ZMod p)ˣ, (x : ZMod p) := by
    symm
    refine prod_bij (fun a _ => (a : ZMod p).val) ?_ ?_ ?_ ?_
    · intro a _
      rw [mem_Ico]
      refine ⟨Nat.pos_of_ne_zero ?_, ZMod.val_lt _⟩
      intro h
      exact Units.ne_zero a ((ZMod.val_eq_zero _).mp h)
    · intro a _ b _ h
      exact Units.ext (ZMod.val_injective p h)
    · intro b hb
      rw [mem_Ico] at hb
      have hb0 : (b : ZMod p) ≠ 0 := by
        intro h
        have := (ZMod.natCast_eq_zero_iff b p).mp h
        exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
      exact ⟨Units.mk0 _ hb0, mem_univ _, by simp [ZMod.val_cast_of_lt hb.2]⟩
    · intro a _
      simp
  rw [h1, h2]
  simp_rw [← Units.coeHom_apply, ← map_prod (Units.coeHom (ZMod p)),
    FiniteField.prod_univ_units_id_eq_neg_one, Units.coeHom_apply, Units.val_neg, Units.val_one]

theorem main : A.Statement := by
  intro n hn
  constructor
  · intro hp
    have : Fact n.Prime := ⟨hp⟩
    exact (ZMod.intCast_eq_intCast_iff _ _ n).mp (by simp [fact_prime_zmod n])
  · intro h
    by_contra hnp
    have hd : n ∣ (n - 1)! + 1 := by
      have h' : (n : ℤ) ∣ (((n - 1)! + 1 : ℕ) : ℤ) := by
        have := Int.modEq_iff_dvd.mp h.symm
        simpa using this
      exact_mod_cast h'
    set p := n.minFac
    have hpp : p.Prime := Nat.minFac_prime (by omega)
    have hpn : p ∣ n := Nat.minFac_dvd n
    have hlt : p < n := by
      rcases (Nat.minFac_le (by omega : 0 < n)).lt_or_eq with h | h
      · exact h
      · exact absurd (h ▸ hpp) hnp
    have h1 : p ∣ (n - 1)! := Nat.dvd_factorial hpp.pos (by omega)
    have h2 : p ∣ 1 := (Nat.dvd_add_right h1).mp (hpn.trans hd)
    exact hpp.one_lt.ne' (Nat.dvd_one.mp h2)

end TuriMath.WilsonTheorem
