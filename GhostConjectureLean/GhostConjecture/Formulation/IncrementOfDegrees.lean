import GhostConjecture.Formulation.DegreeIncrements
import Mathlib.Tactic

namespace GhostConjecture

namespace Formulation

variable (p : ℕ) [Fact (Nat.Prime p)]

/-!
This file contains the arithmetic content of Proposition 4.11 in `data/arXiv-2206.15372v2.tex`:
an explicit description of the degree increments `deg(g_{n+1})-deg(g_n)` relative to the
halo slopes `λ_{n+1}`.
-/

/--
In the range `a + sε < p-1`, the “positive part” `k_{max,•}(n) - k_{mid,•}(n)` differs from
`deg(\\bfe_{n+1})` by `0` on even indices and by `1` on odd indices.

This is equation `E:kmax-kmid` in the proof of Proposition 4.11.
-/
theorem kMaxBullet_sub_kMidBullet_sub_bfeDegreeSucc_eq_of_lt (a sε n : ℕ) (hp2 : p ≠ 2)
    (hcase : a + sε < pMinusOne p) :
    kMaxBullet p a sε n - kMidBullet p a sε n - (bfeDegreeSucc p a sε n : ℤ) =
      if Even n then 0 else 1 := by
  -- Simplify the two residues in the degrees.
  have hmod : (a + sε) % pMinusOne p = a + sε := Nat.mod_eq_of_lt hcase
  have hmin : bfeResidueMin p a sε = sε := by
    simp [bfeResidueMin, hmod, Nat.min_eq_left (Nat.le_add_left _ _)]
  have hmax : bfeResidueMax p a sε = a + sε := by
    simp [bfeResidueMax, hmod, Nat.max_eq_right (Nat.le_add_left _ _)]

  by_cases hn : Even n
  · -- Even `n`.
    have hnZ : Even (n : ℤ) := by simpa [Int.even_coe_nat] using hn
    have hnmod : n % 2 = 0 := (Nat.even_iff).1 hn
    set n0 : ℕ := n / 2
    have hnEq : (n : ℤ) = 2 * (n0 : ℤ) := by
      have hnEqNat : 2 * (n / 2) = n := by
        simpa [hnmod, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (Nat.div_add_mod n 2)
      simpa [n0, Nat.mul_comm] using (show (n : ℤ) = (2 * (n / 2) : ℕ) from by
        exact_mod_cast hnEqNat.symm)
    have hbfe : (bfeDegreeSucc p a sε n : ℤ) = (n0 * pMinusOne p + sε : ℤ) := by
      simp [bfeDegreeSucc, hn, n0, hmin]
    -- Compute `kMaxBullet - kMidBullet`.
    have hkm :
        kMaxBullet p a sε n - kMidBullet p a sε n =
          (n0 : ℤ) * (pMinusOne p : ℤ) + (sε : ℤ) := by
      -- In this case `β_[n] = t₁ = sε + δ`.
      simp [kMaxBullet, kMidBullet, betaBracket, betaEven, tOne, hcase, hnEq, hnZ]
      -- Rewrite `halfPPlusOne * 2` using `p ≠ 2`.
      have : (halfPPlusOne p : ℤ) * 2 = (p + 1 : ℤ) := by
        simpa [mul_comm] using halfPPlusOne_mul_two (p := p) hp2
      have hp1 : 1 ≤ p := Nat.le_of_lt (Fact.out : Nat.Prime p).one_lt
      have hpCast : (pMinusOne p : ℤ) = (p : ℤ) - 1 := by
        simpa [pMinusOne] using (Int.ofNat_sub (m := 1) (n := p) hp1)
      calc
        halfPPlusOne p * (2 * (n0 : ℤ)) + ((sε : ℤ) + (deltaEpsilon p a sε : ℤ)) -
              (2 * (n0 : ℤ) + (deltaEpsilon p a sε : ℤ))
            = (n0 : ℤ) * ((halfPPlusOne p : ℤ) * 2) - (n0 : ℤ) * 2 + (sε : ℤ) := by ring
        _ = (n0 : ℤ) * (p + 1 : ℤ) - (n0 : ℤ) * 2 + (sε : ℤ) := by simp [this]
        _ = (n0 : ℤ) * (p : ℤ) - (n0 : ℤ) + (sε : ℤ) := by ring
        _ = (n0 : ℤ) * (pMinusOne p : ℤ) + (sε : ℤ) := by simp [hpCast]; ring
    -- Conclude: the difference is `0` on even indices.
    simp [hbfe, hkm, hn]
  · -- Odd `n`.
    have hnZ : ¬Even (n : ℤ) := by
      have : Even (n : ℤ) ↔ Even n := (Int.even_coe_nat n)
      exact fun h => hn (this.1 h)
    have hnmod : n % 2 = 1 := by
      have hn' : n % 2 ≠ 0 := by
        intro h0
        exact hn ((Nat.even_iff).2 h0)
      rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
      · exact (hn' h0).elim
      exact h1
    set n0 : ℕ := n / 2
    have hnEq : (n : ℤ) = 2 * (n0 : ℤ) + 1 := by
      have hnEqNat : 2 * (n / 2) + 1 = n := by
        simpa [hnmod, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (Nat.div_add_mod n 2)
      exact_mod_cast hnEqNat.symm
    have hbfe : (bfeDegreeSucc p a sε n : ℤ) = (n0 * pMinusOne p + (a + sε) : ℤ) := by
      simp [bfeDegreeSucc, hn, n0, hmax]
    -- Compute `kMaxBullet - kMidBullet` (this is the `+1` case).
    have hkm :
        kMaxBullet p a sε n - kMidBullet p a sε n =
          (n0 : ℤ) * (pMinusOne p : ℤ) + (a + sε : ℤ) + 1 := by
      simp [kMaxBullet, kMidBullet, betaBracket, betaOdd, tTwo, hcase, hnEq, hnZ]
      have : (halfPPlusOne p : ℤ) * 2 = (p + 1 : ℤ) := by
        simpa [mul_comm] using halfPPlusOne_mul_two (p := p) hp2
      have hOdd : ¬Odd (2 * (n0 : ℤ)) := by
        have hEven : Even (2 * (n0 : ℤ)) := by
          have hTwo : Even (2 : ℤ) := by decide
          exact (Int.even_mul).2 (Or.inl hTwo)
        exact (Int.not_odd_iff_even).2 hEven
      have hp1 : 1 ≤ p := Nat.le_of_lt (Fact.out : Nat.Prime p).one_lt
      have hpCast : (pMinusOne p : ℤ) = (p : ℤ) - 1 := by
        simpa [pMinusOne] using (Int.ofNat_sub (m := 1) (n := p) hp1)
      simp [hOdd]
      calc
        halfPPlusOne p * (2 * (n0 : ℤ) + 1) +
              ((a : ℤ) + sε + (deltaEpsilon p a sε : ℤ) + 2 - halfPPlusOne p) -
            (2 * (n0 : ℤ) + 1 + (deltaEpsilon p a sε : ℤ))
            = (n0 : ℤ) * ((halfPPlusOne p : ℤ) * 2) - (n0 : ℤ) * 2 + (a + sε : ℤ) + 1 := by
              ring
        _ = (n0 : ℤ) * (p + 1 : ℤ) - (n0 : ℤ) * 2 + (a + sε : ℤ) + 1 := by simp [this]
        _ = (n0 : ℤ) * (p : ℤ) - (n0 : ℤ) + (a + sε : ℤ) + 1 := by ring
        _ = (n0 : ℤ) * (pMinusOne p : ℤ) + (a + sε : ℤ) + 1 := by simp [hpCast]; ring
    -- Conclude: the difference is `1` on odd indices.
    simp [hbfe, hkm, hn]

/--
In the range `a + sε ≥ p-1`, the “positive part” `k_{max,•}(n) - k_{mid,•}(n)` differs from
`deg(\\bfe_{n+1})` by `1` on even indices and by `0` on odd indices.

This is the complementary case of equation `E:kmax-kmid` in the proof of Proposition 4.11.
-/
theorem kMaxBullet_sub_kMidBullet_sub_bfeDegreeSucc_eq_of_ge (a sε n : ℕ) (hp2 : p ≠ 2)
    (hs : sε < pMinusOne p) (ha : a < pMinusOne p) (hcase : pMinusOne p ≤ a + sε) :
    kMaxBullet p a sε n - kMidBullet p a sε n - (bfeDegreeSucc p a sε n : ℤ) =
      if Even n then 1 else 0 := by
  set m : ℕ := pMinusOne p
  have hsum_lt : a + sε < m + m := Nat.add_lt_add ha hs
  have hsub_lt : a + sε - m < m := by
    have hrewrite : (a + sε - m) + m = a + sε := Nat.sub_add_cancel hcase
    have : (a + sε - m) + m < m + m := by simpa [hrewrite] using hsum_lt
    exact Nat.lt_of_add_lt_add_right this
  have hmod : (a + sε) % m = a + sε - m := by
    calc
      (a + sε) % m = (a + sε - m) % m := Nat.mod_eq_sub_mod hcase
      _ = a + sε - m := Nat.mod_eq_of_lt hsub_lt
  have hr_le : (a + sε) % m ≤ sε := by
    have ha_le : a ≤ m := Nat.le_of_lt ha
    have hle : a + sε ≤ sε + m := by
      have : a + sε ≤ m + sε := Nat.add_le_add_right ha_le sε
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
    have : a + sε - m ≤ sε := (Nat.sub_le_iff_le_add).2 hle
    simpa [hmod] using this
  have hmin : bfeResidueMin p a sε = (a + sε) % m := by
    simpa [bfeResidueMin, m] using (Nat.min_eq_right hr_le)
  have hmax : bfeResidueMax p a sε = sε := by
    simpa [bfeResidueMax, m] using (Nat.max_eq_left hr_le)

  by_cases hn : Even n
  · -- Even `n`.
    have hnZ : Even (n : ℤ) := by simpa [Int.even_coe_nat] using hn
    have hnmod : n % 2 = 0 := (Nat.even_iff).1 hn
    set n0 : ℕ := n / 2
    have hnEq : (n : ℤ) = 2 * (n0 : ℤ) := by
      have hnEqNat : 2 * (n / 2) = n := by
        simpa [hnmod, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (Nat.div_add_mod n 2)
      simpa [n0, Nat.mul_comm] using (show (n : ℤ) = (2 * (n / 2) : ℕ) from by
        exact_mod_cast hnEqNat.symm)
    have hbfe : (bfeDegreeSucc p a sε n : ℤ) = (n0 * m + (a + sε) % m : ℤ) := by
      simp [bfeDegreeSucc, hn, n0, hmin, m]
    have hkm :
        kMaxBullet p a sε n - kMidBullet p a sε n =
          (n0 : ℤ) * (m : ℤ) + ((a + sε) % m : ℤ) + 1 := by
      have hnot : ¬(a + sε < m) := Nat.not_lt_of_ge hcase
      simp [kMaxBullet, kMidBullet, betaBracket, betaEven, tOne, hnot, hnZ, hnEq, m]
      have hhalf : (halfPPlusOne p : ℤ) * 2 = (p + 1 : ℤ) := by
        simpa [mul_comm] using halfPPlusOne_mul_two (p := p) hp2
      have hp1 : 1 ≤ p := Nat.le_of_lt (Fact.out : Nat.Prime p).one_lt
      have hpCast : (m : ℤ) = (p : ℤ) - 1 := by
        simpa [m, pMinusOne] using (Int.ofNat_sub (m := 1) (n := p) hp1)
      calc
        halfPPlusOne p * (2 * (n0 : ℤ)) +
              (((a + sε) % m : ℤ) + (deltaEpsilon p a sε : ℤ) + 1) -
            (2 * (n0 : ℤ) + (deltaEpsilon p a sε : ℤ))
            = halfPPlusOne p * (2 * (n0 : ℤ)) - 2 * (n0 : ℤ) + ((a + sε) % m : ℤ) + 1 := by
                ring
        _ = (n0 : ℤ) * ((halfPPlusOne p : ℤ) * 2) - (n0 : ℤ) * 2 + ((a + sε) % m : ℤ) + 1 := by
              ring
        _ = (n0 : ℤ) * (p + 1 : ℤ) - (n0 : ℤ) * 2 + ((a + sε) % m : ℤ) + 1 := by
              simp [hhalf]
        _ = (n0 : ℤ) * ((p : ℤ) - 1) + ((a + sε) % m : ℤ) + 1 := by ring
        _ = (n0 : ℤ) * (m : ℤ) + ((a + sε) % m : ℤ) + 1 := by simp [hpCast]
    simp [hbfe, hkm, hn]
  · -- Odd `n`.
    have hnZ : ¬Even (n : ℤ) := by
      have : Even (n : ℤ) ↔ Even n := (Int.even_coe_nat n)
      exact fun h => hn (this.1 h)
    have hnmod : n % 2 = 1 := by
      have hn' : n % 2 ≠ 0 := by
        intro h0
        exact hn ((Nat.even_iff).2 h0)
      rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
      · exact (hn' h0).elim
      exact h1
    set n0 : ℕ := n / 2
    have hnEq : (n : ℤ) = 2 * (n0 : ℤ) + 1 := by
      have hnEqNat : 2 * (n / 2) + 1 = n := by
        simpa [hnmod, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (Nat.div_add_mod n 2)
      exact_mod_cast hnEqNat.symm
    have hbfe : (bfeDegreeSucc p a sε n : ℤ) = (n0 * m + sε : ℤ) := by
      simp [bfeDegreeSucc, hn, n0, hmax, m]
    have hkm :
        kMaxBullet p a sε n - kMidBullet p a sε n =
          (n0 : ℤ) * (m : ℤ) + (sε : ℤ) := by
      have hnot : ¬(a + sε < m) := Nat.not_lt_of_ge hcase
      -- First simplify `betaBracket` using the parity hypothesis, then substitute `n = 2*n0+1`.
      simp [kMaxBullet, kMidBullet, betaBracket, betaOdd, tTwo, hnot, hnZ, m]
      simp [hnEq]
      have hhalf : (halfPPlusOne p : ℤ) * 2 = (p + 1 : ℤ) := by
        simpa [mul_comm] using halfPPlusOne_mul_two (p := p) hp2
      have hp1 : 1 ≤ p := Nat.le_of_lt (Fact.out : Nat.Prime p).one_lt
      have hpCast : (m : ℤ) = (p : ℤ) - 1 := by
        simpa [m, pMinusOne] using (Int.ofNat_sub (m := 1) (n := p) hp1)
      calc
        halfPPlusOne p * (2 * (n0 : ℤ) + 1) +
              ((sε : ℤ) + (deltaEpsilon p a sε : ℤ) + 1 - halfPPlusOne p) -
            (2 * (n0 : ℤ) + 1 + (deltaEpsilon p a sε : ℤ))
            = halfPPlusOne p * (2 * (n0 : ℤ)) - 2 * (n0 : ℤ) + (sε : ℤ) := by ring
        _ = (n0 : ℤ) * ((halfPPlusOne p : ℤ) * 2) - (n0 : ℤ) * 2 + (sε : ℤ) := by ring
        _ = (n0 : ℤ) * (p + 1 : ℤ) - (n0 : ℤ) * 2 + (sε : ℤ) := by simp [hhalf]
        _ = (n0 : ℤ) * ((p : ℤ) - 1) + (sε : ℤ) := by ring
        _ = (n0 : ℤ) * (m : ℤ) + (sε : ℤ) := by simp [hpCast]
    simp [hbfe, hkm, hn]

end Formulation

end GhostConjecture
