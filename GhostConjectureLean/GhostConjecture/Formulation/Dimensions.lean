import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace GhostConjecture

namespace Formulation

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- The modulus `p-1` that appears throughout the paper. -/
abbrev pMinusOne : ℕ := p - 1

/-- The indicator `δ_ε` from Notation `N:kbullet` (i.e. Notation 4.2 in the paper). -/
def deltaEpsilon (a sε : ℕ) : ℕ :=
  (sε + (a + sε) % (pMinusOne p)) / (pMinusOne p)

/-- The distinguished residue-class representative `k_ε := 2 + {a+2s_ε}` (Notation 2.24). -/
def kEpsilon (a sε : ℕ) : ℕ :=
  2 + (a + 2 * sε) % (pMinusOne p)

/--
The arithmetic identity `(p-1)δ_ε + {a+2s_ε} = s_ε + {a+s_ε}` (Remark `R:delta`).

Here `{x}` is implemented as `x % (p-1)`.
-/
theorem pMinusOne_mul_deltaEpsilon_add_mod_eq (a sε : ℕ) (hs : sε < pMinusOne p) :
    pMinusOne p * deltaEpsilon p a sε + (a + 2 * sε) % (pMinusOne p) =
      sε + (a + sε) % (pMinusOne p) := by
  set m : ℕ := pMinusOne p
  have hm_pos : 0 < m := by
    -- `p` prime implies `1 < p`, hence `0 < p-1`.
    simpa [m, pMinusOne] using Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt
  -- Let `x := sε + {a+sε}`. Then `δ_ε = x / m` by definition.
  set x : ℕ := sε + (a + sε) % m
  have hδ : deltaEpsilon p a sε = x / m := by rfl
  -- Compute `x % m` in terms of `{a+2sε}`.
  have hx_mod : x % m = (a + 2 * sε) % m := by
    -- First, reduce `sε` modulo `m` using `hs`.
    have hs_mod : sε % m = sε := Nat.mod_eq_of_lt (by simpa [m] using hs)
    -- Rewrite `x % m` and use `Nat.add_mod`.
    calc
      x % m
          = (sε % m + ((a + sε) % m) % m) % m := by
              simp [x, Nat.add_mod]
      _ = (sε + (a + sε) % m) % m := by simp [hs_mod]
      _ = ((a + sε) % m + sε) % m := by simp [Nat.add_comm]
      _ = ((a + sε) % m + sε % m) % m := by simp [hs_mod]
      _ = (a + sε + sε) % m := by
            -- use `Nat.add_mod` in reverse direction
            simp [Nat.add_mod]
      _ = (a + 2 * sε) % m := by
            ring_nf
  -- Now use the division algorithm `x % m + m * (x / m) = x`.
  have hx : x % m + m * (x / m) = x := Nat.mod_add_div x m
  -- Substitute the computed remainder and quotient.
  -- `x = sε + {a+sε}` by definition, and `x / m = δ_ε`.
  calc
    m * deltaEpsilon p a sε + (a + 2 * sε) % m
        = m * (x / m) + x % m := by
              simp [hδ, hx_mod, Nat.mul_comm]
    _ = x := by
          -- rearrange `hx` to match the target order
          simpa [Nat.add_comm] using hx
    _ = sε + (a + sε) % m := rfl

/--
The Iwasawa dimension formula from Proposition `P:dimension of SIw` (taken as a definition).

We record it as an integer-valued function to avoid bookkeeping about nonnegativity.
-/
def dIw (a sε : ℕ) (k : ℤ) : ℤ :=
  let m : ℤ := (pMinusOne p : ℤ)
  (k - 2 - (sε : ℤ)) / m + (k - 2 - ((a + sε) % pMinusOne p : ℤ)) / m + 2

/--
Corollary `C:dIw is even`: when `k = k_ε + k_•(p-1)`, we have
`d_k^Iw(\\tilde ε_1) = 2k_• + 2 - 2δ_ε`.

This is the “trivial corollary” requested in `instruction/instruction.tex`.
-/
theorem dIw_eq_two_mul_kBullet_add_two_sub_two_mul_delta (a sε : ℕ) (hs : sε < pMinusOne p)
    (kBullet : ℤ) :
    dIw p a sε ((kEpsilon p a sε : ℤ) + kBullet * (pMinusOne p : ℤ)) =
      2 * kBullet + 2 - 2 * (deltaEpsilon p a sε : ℤ) := by
  -- Set up shorthand notations.
  set mNat : ℕ := pMinusOne p
  set m : ℤ := (mNat : ℤ)
  have hm_pos : 0 < m := by
    have : 0 < mNat := by
      simpa [mNat, pMinusOne] using Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt
    have : (0 : ℤ) < (mNat : ℤ) := by exact_mod_cast this
    simpa [m] using this
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  set rNat : ℕ := (a + sε) % mNat
  set r : ℤ := (rNat : ℤ)
  set δNat : ℕ := deltaEpsilon p a sε
  set δ : ℤ := (δNat : ℤ)
  set res2Nat : ℕ := (a + 2 * sε) % mNat
  set res2 : ℤ := (res2Nat : ℤ)
  have hdeltaNat : mNat * δNat + res2Nat = sε + rNat := by
    simpa [mNat, rNat, res2Nat] using pMinusOne_mul_deltaEpsilon_add_mod_eq (p := p) (a := a)
      (sε := sε) hs
  have hdelta : m * δ + res2 = (sε : ℤ) + r := by
    have : ((mNat * δNat + res2Nat : ℕ) : ℤ) = (sε + rNat : ℕ) := by
      exact_mod_cast hdeltaNat
    -- unfold the abbreviations on the left and right
    simpa [m, δ, res2, r, mNat, δNat, res2Nat, rNat, Nat.cast_add, Nat.cast_mul] using this
  -- Simplify the equality `m*δ + res2 = sε + r`.
  simp [m, mNat, r, rNat, δ, δNat, res2, res2Nat] at hdelta
  -- From `m*δ + res2 = sε + r`, rewrite `res2`.
  have hres2 : res2 = (sε : ℤ) + r - m * δ := by
    linarith [hdelta]
  -- Reduce the two floor divisions to the same integer `kBullet - δ`.
  have hr_lt : (0 : ℤ) ≤ r ∧ r < m := by
    have hr_lt_nat : rNat < mNat := Nat.mod_lt _ (by
      -- `mNat = p-1 > 0`
      simpa [mNat, pMinusOne] using Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt)
    have : (rNat : ℤ) < (mNat : ℤ) := by exact_mod_cast hr_lt_nat
    refine ⟨?_, ?_⟩
    · simpa [r] using (show (0 : ℤ) ≤ (rNat : ℤ) from Int.ofNat_nonneg rNat)
    simpa [r, m] using this
  have hs_lt : (0 : ℤ) ≤ (sε : ℤ) ∧ (sε : ℤ) < m := by
    refine ⟨by exact_mod_cast (Nat.zero_le _), ?_⟩
    have : (sε : ℤ) < (mNat : ℤ) := by exact_mod_cast hs
    simpa [m] using this
  have hr_div : r / m = 0 := Int.ediv_eq_zero_of_lt hr_lt.1 hr_lt.2
  have hs_div : (sε : ℤ) / m = 0 := Int.ediv_eq_zero_of_lt hs_lt.1 hs_lt.2
  -- Now compute `dIw` at `k = 2 + res2 + kBullet*m`.
  -- After rewriting via `hres2`, both divisions become `kBullet - δ`.
  have hdiv1 :
      ((res2 + kBullet * m) - (sε : ℤ)) / m = kBullet - δ := by
    -- `res2 - sε = r - m*δ` by `hres2`.
    have : res2 - (sε : ℤ) = r - m * δ := by
      linarith [hres2]
    -- Rewrite and use `Int.add_mul_ediv_left`.
    calc
      ((res2 + kBullet * m) - (sε : ℤ)) / m
          = (res2 - (sε : ℤ) + m * kBullet) / m := by ring
      _ = ((r - m * δ) + m * kBullet) / m := by simpa [this]
      _ = (r + m * (kBullet - δ)) / m := by ring
      _ = r / m + (kBullet - δ) := by
            simpa [Int.mul_comm] using
              Int.add_mul_ediv_left (a := r) (b := m) (c := kBullet - δ) hm_ne
      _ = kBullet - δ := by simp [hr_div]
  have hdiv2 :
      ((res2 + kBullet * m) - r) / m = kBullet - δ := by
    have : res2 - r = (sε : ℤ) - m * δ := by
      linarith [hres2]
    calc
      ((res2 + kBullet * m) - r) / m
          = (res2 - r + m * kBullet) / m := by ring
      _ = ((sε : ℤ) - m * δ + m * kBullet) / m := by simpa [this]
      _ = ((sε : ℤ) + m * (kBullet - δ)) / m := by ring
      _ = (sε : ℤ) / m + (kBullet - δ) := by
            simpa [Int.mul_comm] using
              Int.add_mul_ediv_left (a := (sε : ℤ)) (b := m) (c := kBullet - δ) hm_ne
      _ = kBullet - δ := by simp [hs_div]
  -- Finish by unfolding `dIw` and substituting the two division computations.
  have hkE : (kEpsilon p a sε : ℤ) = (2 : ℤ) + res2 := by
    simp [kEpsilon, res2, res2Nat, mNat, pMinusOne]
  have hkMinusTwo : ((kEpsilon p a sε : ℤ) + kBullet * m) - 2 = res2 + kBullet * m := by
    calc
      ((kEpsilon p a sε : ℤ) + kBullet * m) - 2 = ((2 : ℤ) + res2 + kBullet * m) - 2 := by
        simpa [hkE, add_assoc, add_left_comm, add_comm]
      _ = res2 + kBullet * m := by ring
  have hr : ((a + sε) % pMinusOne p : ℤ) = r := by rfl
  have hkMinusTwo' :
      ((kEpsilon p a sε : ℤ) + kBullet * (pMinusOne p : ℤ)) - 2 =
        res2 + kBullet * (pMinusOne p : ℤ) := by
    simpa [m, mNat] using hkMinusTwo
  have hdiv1' :
      ((res2 + kBullet * (pMinusOne p : ℤ)) - (sε : ℤ)) / (pMinusOne p : ℤ) = kBullet - δ := by
    simpa [m, mNat] using hdiv1
  have hdiv2' :
      ((res2 + kBullet * (pMinusOne p : ℤ)) - r) / (pMinusOne p : ℤ) = kBullet - δ := by
    simpa [m, mNat] using hdiv2
  -- Unfold `dIw` at this `k` and substitute the two division computations.
  calc
    dIw p a sε ((kEpsilon p a sε : ℤ) + kBullet * (pMinusOne p : ℤ))
        =
          ((res2 + kBullet * (pMinusOne p : ℤ)) - (sε : ℤ)) / (pMinusOne p : ℤ) +
            ((res2 + kBullet * (pMinusOne p : ℤ)) - r) / (pMinusOne p : ℤ) + 2 := by
          simp [dIw, hkMinusTwo', hr]
    _ = (kBullet - δ) + (kBullet - δ) + 2 := by simp [hdiv1', hdiv2']
    _ = 2 * kBullet + 2 - 2 * δ := by ring

end Formulation

end GhostConjecture
