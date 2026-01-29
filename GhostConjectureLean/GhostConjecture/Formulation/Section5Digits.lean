import GhostConjecture.Formulation.Notation427
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace GhostConjecture

namespace Formulation

open scoped BigOperators

noncomputable section

/--
Kummer/Legendre digit-sum identity for binomial coefficients, phrased using `Dig`.

This is the bridge between digit sums and `p`-adic valuations used repeatedly in Section 5
(`Vertices of the Newton polygon of ghost series`). It is a reformulation of
`sub_one_mul_padicValNat_choose_eq_sub_sum_digits'` from Mathlib.
-/
theorem sub_one_mul_padicValNat_choose_eq_sub_Dig (p A B : ℕ) [Fact (Nat.Prime p)] :
    (p - 1) * padicValNat p (Nat.choose (A + B) B) = Dig p A + Dig p B - Dig p (A + B) := by
  simpa [Dig, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (sub_one_mul_padicValNat_choose_eq_sub_sum_digits' (p := p) (k := B) (n := A))

/--
The basic bound `v_p(n) ≤ ⌊log_p(n)⌋`, recorded as `padicValNat_le_nat_log` in Mathlib.

This is frequently used to control maximal `p`-adic valuations on finite intervals by the size of
the interval.
-/
theorem padicValNat_le_natLog (p n : ℕ) [Fact (Nat.Prime p)] : padicValNat p n ≤ Nat.log p n := by
  simpa using (padicValNat_le_nat_log (p := p) n)

/--
Pointwise bound on `p`-adic valuations over an interval `(A, A+B]`.

If `x ∈ (A, A+B]`, then `v_p(x) ≤ ⌊log_p(A+B)⌋`.
-/
theorem padicValNat_le_natLog_of_mem_Ioc (p A B x : ℕ) [Fact (Nat.Prime p)]
    (hx : x ∈ Finset.Ioc A (A + B)) : padicValNat p x ≤ Nat.log p (A + B) := by
  have hxle : x ≤ A + B := (Finset.mem_Ioc.mp hx).2
  have hlog : Nat.log p x ≤ Nat.log p (A + B) := Nat.log_mono_right hxle
  exact (le_trans (padicValNat_le_natLog (p := p) x) hlog)

end

end Formulation

end GhostConjecture
