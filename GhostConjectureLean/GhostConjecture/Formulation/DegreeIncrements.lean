import GhostConjecture.Formulation.ExtremalKs
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Lemmas
import Mathlib.Tactic

namespace GhostConjecture

namespace Formulation

variable (p : ℕ) [Fact (Nat.Prime p)]

/--
The degree increment `deg(g_{n+1}) - deg(g_n)` computed from the extremal indices
`k_{min,•}(n)`, `k_{mid,•}(n)`, `k_{max,•}(n)` as in the proof of Proposition 4.11
(equation `E:gn+1 - gn` and the subsequent rewrite).
-/
def ghostDegreeIncrement (a sε : ℕ) (n : ℕ) : ℤ :=
  (kMaxBullet p a sε n - kMidBullet p a sε n) -
    (kMidBullet p a sε n - kMinBullet p a sε n + 1)

/--
The degree `deg(g_n)` of the `n`-th ghost coefficient, defined recursively from
`ghostDegreeIncrement` with the normalization `deg(g_0)=0`.
-/
def ghostDegree (a sε : ℕ) : ℕ → ℤ :=
  Nat.rec 0 (fun n acc => acc + ghostDegreeIncrement p a sε n)

/--
The ghost-halo slope term `λ_{n+1}` as an integer, using integer division.

This is `deg(\\bfe_{n+1}) - ⌊deg(\\bfe_{n+1})/p⌋`, matching the paper's definition.
-/
def lambdaSuccZ (a sε : ℕ) (n : ℕ) : ℤ :=
  let d : ℤ := bfeDegreeSucc p a sε n
  d - d / (p : ℤ)

/-- The partial sum `λ₁ + ⋯ + λ_n`, expressed using `lambdaSuccZ`. -/
def lambdaSum (a sε : ℕ) (n : ℕ) : ℤ :=
  Finset.sum (Finset.range n) fun i => lambdaSuccZ p a sε i

/-- The recursion equation `deg(g_{n+1}) = deg(g_n) + (deg(g_{n+1})-deg(g_n))`. -/
theorem ghostDegree_succ (a sε : ℕ) (n : ℕ) :
    ghostDegree p a sε (n + 1) = ghostDegree p a sε n + ghostDegreeIncrement p a sε n := by
  simp [ghostDegree]

/-- By construction, the discrete difference of `ghostDegree` is `ghostDegreeIncrement`. -/
theorem ghostDegree_succ_sub (a sε : ℕ) (n : ℕ) :
    ghostDegree p a sε (n + 1) - ghostDegree p a sε n = ghostDegreeIncrement p a sε n := by
  simp [ghostDegree_succ, sub_eq_add_neg, add_assoc]

/--
For `p ≠ 2`, the quantity `halfPPlusOne p = (p+1)/2` satisfies `((p+1)/2) * 2 = p+1`.

This is used to simplify the parity split computations in Proposition 4.11.
-/
theorem halfPPlusOne_mul_two (hp2 : p ≠ 2) : halfPPlusOne p * 2 = (p + 1 : ℤ) := by
  have hpOdd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp2
  rcases hpOdd with ⟨t, ht⟩
  have h2dvd : (2 : ℤ) ∣ (p + 1 : ℤ) := by
    refine ⟨(t + 1 : ℤ), ?_⟩
    -- Convert `p = 2t+1` into an equality in `ℤ`.
    have ht' : (p : ℤ) = 2 * (t : ℤ) + 1 := by exact_mod_cast ht
    linarith
  -- Unfold `halfPPlusOne` and cancel the division by `2`.
  simpa [halfPPlusOne, Int.ediv_mul_cancel h2dvd]

/--
The ceiling division `⌈x/p⌉` is equivariant with respect to translation by multiples of `p`.

We record this for `intCeilDiv` since it is used to rewrite `kMinBullet` in a more usable form.
-/
theorem intCeilDiv_add_mul (x : ℤ) (k : ℤ) (hp : p ≠ 0) :
    intCeilDiv (x + (p : ℤ) * k) p = intCeilDiv x p + k := by
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  -- Rewrite in terms of Euclidean division of `-x`.
  calc
    intCeilDiv (x + (p : ℤ) * k) p
        = -((-(x + (p : ℤ) * k)) / (p : ℤ)) := by simp [intCeilDiv]
    _ = -(((-x) + (p : ℤ) * (-k)) / (p : ℤ)) := by ring
    _ = -((-x) / (p : ℤ) + (-k)) := by
          simpa using
            congrArg (fun t => -t)
              (Int.add_mul_ediv_left (a := (-x)) (b := (p : ℤ)) (c := (-k)) hpZ)
    _ = -((-x) / (p : ℤ)) + k := by ring
    _ = intCeilDiv x p + k := by simp [intCeilDiv, add_comm, add_left_comm, add_assoc]

/--
An explicit expression for `intCeilDiv` in terms of integer division and divisibility.

For positive `p`, this is the identity
`⌈y/p⌉ = ⌊y/p⌋ + (if p ∣ y then 0 else 1)`.
-/
theorem intCeilDiv_eq_ediv_add (y : ℤ) (hp : 0 < (p : ℤ)) :
    intCeilDiv y p = y / (p : ℤ) + if (p : ℤ) ∣ y then 0 else 1 := by
  have hneg :
      (-y) / (p : ℤ) = -(y / (p : ℤ)) - if (p : ℤ) ∣ y then 0 else (p : ℤ).sign := by
    simpa using (Int.neg_ediv (a := y) (b := (p : ℤ)))
  -- Negate the division formula and use `sign(p)=1` for `p>0`.
  have hsign : (p : ℤ).sign = 1 := Int.sign_eq_one_of_pos hp
  calc
    intCeilDiv y p = -((-y) / (p : ℤ)) := by rfl
    _ = -(-(y / (p : ℤ)) - if (p : ℤ) ∣ y then 0 else (p : ℤ).sign) := by
          simpa [hneg]
    _ = y / (p : ℤ) + if (p : ℤ) ∣ y then 0 else (p : ℤ).sign := by ring
    _ = y / (p : ℤ) + if (p : ℤ) ∣ y then 0 else 1 := by simp [hsign]

/--
For `c < p`, the ceiling difference `⌈y/p⌉ - ⌈(y-c)/p⌉` is `1` exactly when the remainder
`y % p` lies in the interval `[1,c]`.

This is the arithmetic input behind the case-by-case congruence description in Proposition 4.11.
-/
theorem intCeilDiv_sub_intCeilDiv_sub (y : ℤ) (c : ℕ) (hc : c < p) :
    intCeilDiv y p - intCeilDiv (y - (c : ℤ)) p =
      if (1 : ℤ) ≤ y % (p : ℤ) ∧ y % (p : ℤ) ≤ (c : ℤ) then 1 else 0 := by
  have hpZpos : 0 < (p : ℤ) := by
    have : 0 < p := (Fact.out : Nat.Prime p).pos
    exact_mod_cast this
  have hpZne : (p : ℤ) ≠ 0 := ne_of_gt hpZpos
  set m : ℤ := (p : ℤ)
  set cZ : ℤ := (c : ℤ)
  have hcZ : cZ < m := by
    have : (c : ℤ) < (p : ℤ) := by exact_mod_cast hc
    simpa [cZ, m] using this
  set r : ℤ := y % m
  set q : ℤ := y / m
  have hy : r + m * q = y := by
    simpa [r, q] using Int.emod_add_mul_ediv y m
  have hr_nonneg : 0 ≤ r := by
    simpa [r] using Int.emod_nonneg y hpZne
  have hr_lt : r < m := by
    have : r < abs m := by simpa [r] using Int.emod_lt_abs y hpZne
    simpa [m, abs_of_pos hpZpos] using this

  by_cases hrc : r < cZ
  · -- Then `(y-c)/m = q-1` and the remainder is `r + m - c`.
    have hr'nonneg : 0 ≤ r + m - cZ := by linarith [hr_nonneg, le_of_lt hcZ]
    have hr'lt : r + m - cZ < abs m := by
      have : r + m - cZ < m := by linarith [hrc, hcZ]
      simpa [m, abs_of_pos hpZpos] using this
    have hdivMod :
        (y - cZ) / m = q - 1 ∧ (y - cZ) % m = r + m - cZ := by
      have huniq :
          r + m - cZ + m * (q - 1) = y - cZ ∧ 0 ≤ r + m - cZ ∧ r + m - cZ < abs m := by
        refine ⟨?_, hr'nonneg, hr'lt⟩
        -- Rearrange using `y = r + m*q`.
        linarith [hy]
      have := (Int.ediv_emod_unique'' (a := y - cZ) (b := m) (r := r + m - cZ) (q := q - 1)
        hpZne).2 huniq
      exact this
    have hyc_ceil :
        intCeilDiv (y - cZ) p = q := by
      have hndvd : ¬m ∣ (y - cZ) := by
        -- The remainder is positive since `r < cZ < m`.
        have : (y - cZ) % m ≠ 0 := by
          have hrpos : 0 < r + m - cZ := by linarith [hrc, hcZ]
          simpa [hdivMod.2] using ne_of_gt hrpos
        simpa [m] using (mt (Int.dvd_iff_emod_eq_zero).1 this)
      calc
        intCeilDiv (y - cZ) p
            = (y - cZ) / m + if m ∣ (y - cZ) then 0 else 1 := by
                simpa [m, intCeilDiv_eq_ediv_add (p := p)] using
                  (intCeilDiv_eq_ediv_add (p := p) (y := y - cZ) (hp := hpZpos))
        _ = (q - 1) + 1 := by simp [hdivMod.1, hndvd]
        _ = q := by ring
    have hy_ceil :
        intCeilDiv y p = q + if r = 0 then 0 else 1 := by
      -- Rewrite the divisibility condition using `r = y % p`.
      have : (m ∣ y) ↔ r = 0 := by
        simpa [r, m] using (Int.dvd_iff_emod_eq_zero (a := m) (b := y))
      calc
        intCeilDiv y p
            = y / m + if m ∣ y then 0 else 1 := by
                simpa [m, intCeilDiv_eq_ediv_add (p := p)] using
                  (intCeilDiv_eq_ediv_add (p := p) (y := y) (hp := hpZpos))
        _ = q + if r = 0 then 0 else 1 := by simp [q, this]
    -- Now finish by splitting on whether `r=0`.
    by_cases hr0 : r = 0
    · have hrCond : ¬((1 : ℤ) ≤ r ∧ r ≤ cZ) := by
        intro h
        exact (lt_irrefl (0 : ℤ)) (by simpa [hr0] using h.1)
      simp [hyc_ceil, hy_ceil, hr0, r, m, cZ, hrc, hrCond]
    · have hrpos : 1 ≤ r := by
        have : 0 < r := lt_of_le_of_ne hr_nonneg (Ne.symm hr0)
        exact Int.add_one_le_of_lt this
      have hrle : r ≤ cZ := le_of_lt hrc
      have hrCond : (1 : ℤ) ≤ r ∧ r ≤ cZ := ⟨hrpos, hrle⟩
      simp [hyc_ceil, hy_ceil, hr0, r, m, cZ, hrCond]
  · -- The complementary case `c ≤ r`.
    have hrc' : cZ ≤ r := le_of_not_gt hrc
    have hr''nonneg : 0 ≤ r - cZ := sub_nonneg.mpr hrc'
    have hr''lt : r - cZ < abs m := by
      have : r - cZ < m := by linarith [hr_lt, hr''nonneg, le_of_lt hcZ]
      simpa [m, abs_of_pos hpZpos] using this
    have hdivMod :
        (y - cZ) / m = q ∧ (y - cZ) % m = r - cZ := by
      have huniq :
          (r - cZ) + m * q = y - cZ ∧ 0 ≤ r - cZ ∧ r - cZ < abs m := by
        refine ⟨?_, hr''nonneg, hr''lt⟩
        linarith [hy]
      exact (Int.ediv_emod_unique'' (a := y - cZ) (b := m) (r := r - cZ) (q := q) hpZne).2 huniq
    have hyc_ceil :
        intCeilDiv (y - cZ) p = q + if r = cZ then 0 else 1 := by
      have hdiv : (m ∣ (y - cZ)) ↔ r = cZ := by
        calc
          (m ∣ y - cZ) ↔ (y - cZ) % m = 0 := Int.dvd_iff_emod_eq_zero
          _ ↔ r - cZ = 0 := by simpa [hdivMod.2]
          _ ↔ r = cZ := sub_eq_zero
      calc
        intCeilDiv (y - cZ) p
            = (y - cZ) / m + if m ∣ (y - cZ) then 0 else 1 := by
                simpa [m, intCeilDiv_eq_ediv_add (p := p)] using
                  (intCeilDiv_eq_ediv_add (p := p) (y := y - cZ) (hp := hpZpos))
        _ = q + if r = cZ then 0 else 1 := by
              simp [hdivMod.1, hdiv, m]
    have hy_ceil :
        intCeilDiv y p = q + if r = 0 then 0 else 1 := by
      have : (m ∣ y) ↔ r = 0 := by
        simpa [r, m] using (Int.dvd_iff_emod_eq_zero (a := m) (b := y))
      calc
        intCeilDiv y p
            = y / m + if m ∣ y then 0 else 1 := by
                simpa [m, intCeilDiv_eq_ediv_add (p := p)] using
                  (intCeilDiv_eq_ediv_add (p := p) (y := y) (hp := hpZpos))
        _ = q + if r = 0 then 0 else 1 := by simp [q, this]
    -- Since `c ≤ r`, `r=0` cannot happen unless `c=0`.
    by_cases hr0 : r = 0
    · -- Then `c=0` and both sides are `0`.
      have hc0 : c = 0 := by
        have : (cZ : ℤ) = 0 := by linarith [hrc', hr0]
        exact Int.ofNat_eq_zero.mp (by simpa [cZ] using this)
      simp [hc0, hy_ceil, hyc_ceil, hr0, r, m, cZ]
    · -- Here `r > 0`. The difference is `1` exactly when `r = c`.
      have hrpos : 1 ≤ r := by
        have : 0 < r := lt_of_le_of_ne hr_nonneg (Ne.symm hr0)
        exact Int.add_one_le_of_lt this
      by_cases hreq : r = cZ
      · have hrCond : (1 : ℤ) ≤ r ∧ r ≤ cZ := by
          refine ⟨hrpos, ?_⟩
          simpa [hreq]
        have hc0 : c ≠ 0 := by
          -- `r = c` and `r ≠ 0` imply `c ≠ 0`.
          have : (cZ : ℤ) ≠ 0 := by simpa [hreq, cZ] using hr0
          exact Int.ofNat_ne_zero.mp (by simpa [cZ] using this)
        have hc1 : (1 : ℤ) ≤ cZ := by
          have hcNat : (1 : ℕ) ≤ c := (Nat.one_le_iff_ne_zero).2 hc0
          have hcInt : (1 : ℤ) ≤ (c : ℤ) := by exact_mod_cast hcNat
          simpa [cZ] using hcInt
        have hrCond' : (1 : ℤ) ≤ y % (p : ℤ) ∧ y % (p : ℤ) ≤ cZ := by
          -- Here `y % p = r = cZ`.
          refine ⟨?_, ?_⟩
          · simpa [r, m, hreq] using (by simpa [hreq] using hrpos)
          · simpa [r, m, hreq] using (le_rfl : cZ ≤ cZ)
        -- Evaluate both ceilings explicitly and conclude.
        have hy_val : intCeilDiv y p = q + 1 := by simp [hy_ceil, hr0]
        have hyc_val : intCeilDiv (y - cZ) p = q := by simp [hyc_ceil, hreq]
        -- Reduce the goal to `1 = 1` using the explicit values and the satisfied condition.
        have : (if (1 : ℤ) ≤ y % (p : ℤ) ∧ y % (p : ℤ) ≤ cZ then 1 else 0) = (1 : ℤ) := by
          simp [hrCond']
        -- Now `simp` finishes.
        simpa [hy_val, hyc_val, this]
      · have hrCond : ¬((1 : ℤ) ≤ r ∧ r ≤ cZ) := by
          intro h
          exact hreq (le_antisymm h.2 (by linarith [hrc']))
        simp [hy_ceil, hyc_ceil, hr0, hreq, r, m, cZ, hrCond]

end Formulation

end GhostConjecture
