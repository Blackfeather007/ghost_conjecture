import GhostConjecture.Formulation.DegreeIncrements
import Mathlib.Tactic

namespace GhostConjecture

namespace Formulation

variable (p : ℕ) [Fact (Nat.Prime p)]

/-!
This file collects reusable arithmetic lemmas needed for Proposition 4.11
(`data/arXiv-2206.15372v2.tex`, `\label{P:increment of degrees in ghost series}`).

The goal is to isolate the "table computations" involving `intCeilDiv`, integer division,
and the extremal indices `k_{min,•}`, `k_{mid,•}`, `k_{max,•}`.
-/

/--
Cast `(p-1)` to `ℤ` as `p-1`.
-/
theorem pMinusOne_coe (hp1 : 1 ≤ p) : (pMinusOne p : ℤ) = (p : ℤ) - 1 := by
  simpa [pMinusOne] using (Int.ofNat_sub (m := 1) (n := p) hp1)

/--
For integer division, the identity
`((p-1)·n0 + r)/p = n0 - ⌈(n0-r)/p⌉`,
where `⌈·⌉` is `intCeilDiv`.

This is the algebraic form of the paper's "obvious formula"
`\lfloor ((p-1)a+b)/p \rfloor = a - \lceil (a-b)/p \rceil`.
-/
theorem pMinusOne_mul_add_ediv (n0 r : ℤ) :
    ((pMinusOne p : ℤ) * n0 + r) / (p : ℤ) = n0 - intCeilDiv (n0 - r) p := by
  have hp1 : 1 ≤ p := Nat.le_of_lt (Fact.out : Nat.Prime p).one_lt
  have hpZ : (p : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fact.out : Nat.Prime p).pos)
  have hpCast : (pMinusOne p : ℤ) = (p : ℤ) - 1 := pMinusOne_coe (p := p) hp1
  calc
    ((pMinusOne p : ℤ) * n0 + r) / (p : ℤ)
        = (((p : ℤ) - 1) * n0 + r) / (p : ℤ) := by simp [hpCast]
    _ = ((p : ℤ) * n0 + (r - n0)) / (p : ℤ) := by ring
    _ = (r - n0) / (p : ℤ) + n0 := by
          simpa [add_comm, add_left_comm, add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc] using
            (Int.add_mul_ediv_left (a := r - n0) (b := (p : ℤ)) (c := n0) hpZ)
    _ = n0 - intCeilDiv (n0 - r) p := by
          -- `intCeilDiv (n0-r) = -((r-n0)/p)` by definition.
          simp [intCeilDiv, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/--
Rewrite `k_{mid,•}(n) - k_{min,•}(n) + 1` as a single ceiling division term.

This is the identity written in the proof of Proposition 4.11 just after `E:kmax-kmid`:
`k_{mid,•}(n)-k_{min,•}(n)+1 = n - ⌈(...) / p⌉`.
-/
theorem kMidBullet_sub_kMinBullet_add_one (a sε : ℕ) (n : ℕ) (hp2 : p ≠ 2) :
    kMidBullet p a sε n - kMinBullet p a sε n + 1 =
      (n : ℤ) -
        intCeilDiv
          (halfPPlusOne p * ((n : ℤ) - 1) + (deltaEpsilon p a sε : ℤ) -
              betaBracket p a sε ((n : ℤ) - 1) +
            1)
          p := by
  have hp0 : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp0
  have hhalf : (halfPPlusOne p : ℤ) * 2 = (p + 1 : ℤ) := by
    simpa [mul_comm] using halfPPlusOne_mul_two (p := p) hp2
  -- Expand the definitions and separate an explicit `p * δ` term in `kMinTildeBullet`.
  set δ : ℤ := (deltaEpsilon p a sε : ℤ)
  set x : ℤ :=
    halfPPlusOne p * ((n : ℤ) - 1) + δ - betaBracket p a sε ((n : ℤ) - 1) + 1
  have hx : kMinTildeBullet p a sε n = x + (p : ℤ) * δ := by
    -- `kMinTildeBullet = halfPPlusOne*(n-1+2δ) - β_[n-1] + 1`.
    -- Rewrite `halfPPlusOne*(2δ)` using `halfPPlusOne*2 = p+1`, then split `(p+1)δ = pδ + δ`.
    simp [kMinTildeBullet, x, δ]
    -- Move the `2*δ` into a form where `hhalf` applies.
    have : halfPPlusOne p * (2 * δ) = (p + 1 : ℤ) * δ := by
      calc
        halfPPlusOne p * (2 * δ) = (halfPPlusOne p * 2) * δ := by ring
        _ = (p + 1 : ℤ) * δ := by simp [hhalf]
    -- Finish the linearization.
    -- `simp` turns `betaBracket`/`deltaEpsilon` occurrences into `x`, and `ring` closes.
    -- We keep `δ` as a named integer to avoid casts.
    -- After rewriting by `this`, a single `ring` suffices.
    simp [this]
    ring
  -- Use equivariance of `intCeilDiv` to peel off the `p*δ` term.
  have hceil : intCeilDiv (kMinTildeBullet p a sε n) p = intCeilDiv x p + δ := by
    simpa [hx] using intCeilDiv_add_mul (p := p) (x := x) (k := δ) hp0
  -- Conclude by unfolding `kMinBullet` and `kMidBullet`.
  simp [kMidBullet, kMinBullet, hceil, x, δ, add_assoc, add_left_comm, add_comm, sub_eq_add_neg]

end Formulation

end GhostConjecture

