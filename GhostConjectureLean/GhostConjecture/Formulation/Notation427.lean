import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace GhostConjecture

namespace Formulation

open scoped BigOperators

/--
The digit-sum function `Dig` from Notation 4.27 in `data/arXiv-2206.15372v2.tex`.

For a natural number `n`, `Dig p n` is the sum of the base-`p` digits of `n` (using `Nat.digits`).
-/
def Dig (p n : ℕ) : ℕ :=
  (p.digits n).sum

/--
`v_p(n!)` as a sum over the interval `(0, n]`.

This is the basic bridge between factorial valuations and sums of valuations of consecutive
integers, as used in Notation 4.27 (`\label{E:sum of consecutive valuations}`).
-/
theorem padicValNat_factorial_eq_sum_Ioc (p n : ℕ) [Fact (Nat.Prime p)] :
    padicValNat p n.factorial = ∑ i ∈ Finset.Ioc 0 n, padicValNat p i := by
  classical
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hn1 : n.succ ≠ 0 := Nat.succ_ne_zero n
      have hnfac : n.factorial ≠ 0 := Nat.factorial_ne_zero n
      calc
        padicValNat p (n + 1).factorial = padicValNat p (n + 1) + padicValNat p n.factorial := by
          simpa [Nat.factorial_succ, Nat.succ_eq_add_one] using
            (padicValNat.mul (p := p) hn1 hnfac)
        _ = padicValNat p (n + 1) + ∑ i ∈ Finset.Ioc 0 n, padicValNat p i := by
          simp [ih]
        _ = ∑ i ∈ Finset.Ioc 0 (n + 1), padicValNat p i := by
          -- Peel off the top endpoint of the interval.
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            (Finset.sum_Ioc_succ_top (a := 0) (b := n) (hab := Nat.zero_le n)
              (f := fun i => padicValNat p i)).symm

/--
The valuation sum over consecutive integers in `(m₁, m₂]`, after clearing denominators.

This is the equation `\label{E:sum of consecutive valuations}` in Notation 4.27, written without
division:

`(p-1) * (∑_{m₁ < i ≤ m₂} v_p(i)) = (m₂ - Dig(m₂)) - (m₁ - Dig(m₁))`.
-/
theorem sub_one_mul_sum_padicValNat_Ioc (p m1 m2 : ℕ) [Fact (Nat.Prime p)] (hm : m1 ≤ m2) :
    (p - 1) * (∑ i ∈ Finset.Ioc m1 m2, padicValNat p i) =
      (m2 - Dig p m2) - (m1 - Dig p m1) := by
  classical
  -- First rewrite the interval sum as the increment of `v_p(n!)` between `m1` and `m2`.
  set S : ℕ := ∑ i ∈ Finset.Ioc m1 m2, padicValNat p i
  have hsum :
      padicValNat p m2.factorial = padicValNat p m1.factorial + S := by
    have hconsec :=
      Finset.sum_Ioc_consecutive (f := fun i : ℕ => padicValNat p i) (m := 0) (n := m1) (k := m2)
        (hmn := Nat.zero_le m1) (hnk := hm)
    have h0m1 :
        (∑ i ∈ Finset.Ioc 0 m1, padicValNat p i) = padicValNat p m1.factorial := by
      simpa using (padicValNat_factorial_eq_sum_Ioc (p := p) (n := m1)).symm
    have h0m2 :
        (∑ i ∈ Finset.Ioc 0 m2, padicValNat p i) = padicValNat p m2.factorial := by
      simpa using (padicValNat_factorial_eq_sum_Ioc (p := p) (n := m2)).symm
    -- Convert `sum_Ioc_consecutive` into a factorial statement.
    have :
        padicValNat p m1.factorial + S = padicValNat p m2.factorial := by
      simpa [S, h0m1, h0m2] using hconsec
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this.symm
  -- Multiply the factorial identity by `(p-1)` and apply Legendre's theorem.
  have hmul := congrArg (fun n : ℕ => (p - 1) * n) hsum
  have hmul' :
      (p - 1) * padicValNat p m2.factorial =
        (p - 1) * padicValNat p m1.factorial + (p - 1) * S := by
    simpa [Nat.mul_add] using hmul
  have hdigits :
      (m1 - Dig p m1) + (p - 1) * S = m2 - Dig p m2 := by
    -- Rewrite `(p-1) * v_p(n!)` using `sub_one_mul_padicValNat_factorial`.
    have h' := hmul'
    rw [sub_one_mul_padicValNat_factorial (p := p) m2,
      sub_one_mul_padicValNat_factorial (p := p) m1] at h'
    simpa [Dig, Nat.add_assoc] using h'.symm
  -- Clear the remaining subtraction using `Nat.eq_sub_of_add_eq'`.
  have hsub := Nat.eq_sub_of_add_eq' hdigits
  simpa [S] using hsub

/--
The valuation sum over consecutive integers in `(m₁, m₂]`.

This is the equation `\label{E:sum of consecutive valuations}` in Notation 4.27, matching the
paper's division-by-`(p-1)` presentation.
-/
theorem sum_padicValNat_Ioc (p m1 m2 : ℕ) [Fact (Nat.Prime p)] (hm : m1 ≤ m2) :
    (∑ i ∈ Finset.Ioc m1 m2, padicValNat p i) =
      ((m2 - Dig p m2) - (m1 - Dig p m1)) / (p - 1) := by
  classical
  have hp1 : 0 < p - 1 := by
    exact Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt
  have hmul := sub_one_mul_sum_padicValNat_Ioc (p := p) (m1 := m1) (m2 := m2) hm
  -- Divide the cleared-denominator identity by `(p-1)`.
  have hdiv :
      (∑ i ∈ Finset.Ioc m1 m2, padicValNat p i) =
        ((p - 1) * (∑ i ∈ Finset.Ioc m1 m2, padicValNat p i)) / (p - 1) := by
    simpa [Nat.mul_comm] using (Nat.mul_div_left (∑ i ∈ Finset.Ioc m1 m2, padicValNat p i) hp1).symm
  calc
    (∑ i ∈ Finset.Ioc m1 m2, padicValNat p i) =
        ((p - 1) * (∑ i ∈ Finset.Ioc m1 m2, padicValNat p i)) / (p - 1) := hdiv
    _ = ((m2 - Dig p m2) - (m1 - Dig p m1)) / (p - 1) := by
        simp [hmul]

end Formulation

end GhostConjecture
