import GhostConjecture.Formulation.GhostMultiplicities

namespace GhostConjecture

namespace Formulation

variable (p : ℕ) [Fact (Nat.Prime p)]

/--
The ghost multiplicity `m_n^{(ε)}(k)` as a natural number.

The paper's multiplicities are nonnegative; our base definition `ghostMultiplicity` is `ℤ`-valued
for convenience. This wrapper converts it back to `ℕ` via `Int.toNat`.
-/
def ghostMultiplicityNat (a sε : ℕ) (kBullet : ℤ) (n : ℕ) : ℕ :=
  Int.toNat (ghostMultiplicity p a sε kBullet n)

/--
The `ℤ`-valued ghost multiplicity is always nonnegative.
-/
theorem ghostMultiplicity_nonneg (a sε : ℕ) (kBullet : ℤ) (n : ℕ) :
    0 ≤ ghostMultiplicity p a sε kBullet n := by
  simp [ghostMultiplicity]

/--
When the first-difference condition in `(2.25.3)` is `+1`, the Nat ghost multiplicity increases by
`1`.

This is the Nat-level reformulation of the `+1` branch of `ghostMultiplicity_succ_sub`.
-/
theorem ghostMultiplicityNat_succ_eq_add_one_of_pos (a sε : ℕ) (hs : sε < pMinusOne p)
    (kBullet : ℤ) (n : ℕ)
    (hpos :
      (dUnr p a sε kBullet : ℤ) ≤ (n : ℤ) ∧ (n : ℤ) < halfDIwClass p a sε kBullet) :
    ghostMultiplicityNat p a sε kBullet (n + 1) =
      ghostMultiplicityNat p a sε kBullet n + 1 := by
  have hdiff :=
    ghostMultiplicity_succ_sub (p := p) (a := a) (sε := sε) hs (kBullet := kBullet) (n := n)
  have hdiff1 :
      ghostMultiplicity p a sε kBullet (n + 1) - ghostMultiplicity p a sε kBullet n = 1 := by
    simpa [hpos] using hdiff
  have hz :
      ghostMultiplicity p a sε kBullet (n + 1) = ghostMultiplicity p a sε kBullet n + 1 := by
    linarith [hdiff1]
  have hn : 0 ≤ ghostMultiplicity p a sε kBullet n :=
    ghostMultiplicity_nonneg (p := p) (a := a) (sε := sε) (kBullet := kBullet) (n := n)
  have : 0 ≤ (1 : ℤ) := by decide
  -- Convert the integer equality to a Nat equality using `Int.toNat_add`.
  simp [ghostMultiplicityNat, hz, Int.toNat_add hn this]

/--
When the first-difference condition in `(2.25.3)` is `-1`, the Nat ghost multiplicity decreases by
`1`, equivalently `m_n = m_{n+1} + 1`.

This is the Nat-level reformulation of the `-1` branch of `ghostMultiplicity_succ_sub`.
-/
theorem ghostMultiplicityNat_eq_succ_add_one_of_neg (a sε : ℕ) (hs : sε < pMinusOne p)
    (kBullet : ℤ) (n : ℕ)
    (hneg :
      halfDIwClass p a sε kBullet ≤ (n : ℤ) ∧
        (n : ℤ) < dIwClass p a sε kBullet - dUnr p a sε kBullet) :
    ghostMultiplicityNat p a sε kBullet n =
      ghostMultiplicityNat p a sε kBullet (n + 1) + 1 := by
  have hdiff :=
    ghostMultiplicity_succ_sub (p := p) (a := a) (sε := sε) hs (kBullet := kBullet) (n := n)
  have hnotPos :
      ¬((dUnr p a sε kBullet : ℤ) ≤ (n : ℤ) ∧ (n : ℤ) < halfDIwClass p a sε kBullet) := by
    intro h
    exact (not_lt_of_ge hneg.1) h.2
  have hdiffm1 :
      ghostMultiplicity p a sε kBullet (n + 1) - ghostMultiplicity p a sε kBullet n = -1 := by
    simpa [hnotPos, hneg] using hdiff
  have hz :
      ghostMultiplicity p a sε kBullet n = ghostMultiplicity p a sε kBullet (n + 1) + 1 := by
    linarith [hdiffm1]
  have hn1 : 0 ≤ ghostMultiplicity p a sε kBullet (n + 1) :=
    ghostMultiplicity_nonneg (p := p) (a := a) (sε := sε) (kBullet := kBullet) (n := n + 1)
  have : 0 ≤ (1 : ℤ) := by decide
  simp [ghostMultiplicityNat, hz, Int.toNat_add hn1 this, Nat.add_assoc]

/--
Outside the `±1` branches of `(2.25.3)`, the Nat ghost multiplicity is unchanged.
-/
theorem ghostMultiplicityNat_succ_eq_of_else (a sε : ℕ) (hs : sε < pMinusOne p) (kBullet : ℤ)
    (n : ℕ)
    (hpos :
      ¬((dUnr p a sε kBullet : ℤ) ≤ (n : ℤ) ∧ (n : ℤ) < halfDIwClass p a sε kBullet))
    (hneg :
      ¬(halfDIwClass p a sε kBullet ≤ (n : ℤ) ∧
          (n : ℤ) < dIwClass p a sε kBullet - dUnr p a sε kBullet)) :
    ghostMultiplicityNat p a sε kBullet (n + 1) = ghostMultiplicityNat p a sε kBullet n := by
  have hdiff :=
    ghostMultiplicity_succ_sub (p := p) (a := a) (sε := sε) hs (kBullet := kBullet) (n := n)
  have hdiff0 :
      ghostMultiplicity p a sε kBullet (n + 1) - ghostMultiplicity p a sε kBullet n = 0 := by
    simpa [hpos, hneg] using hdiff
  have hz :
      ghostMultiplicity p a sε kBullet (n + 1) = ghostMultiplicity p a sε kBullet n := by
    linarith [hdiff0]
  simp [ghostMultiplicityNat, hz]

end Formulation

end GhostConjecture

