import GhostConjecture.Formulation.GhostMultiplicityNat
import GhostConjecture.Formulation.ExtremalKs
import GhostConjecture.Formulation.Prop418

namespace GhostConjecture

namespace Formulation

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]
variable {Γ₀ : Type*} [LinearOrderedAddCommMonoidWithTop Γ₀]

variable (p : ℕ) [Fact (Nat.Prime p)]

/--
The “+1” condition from `(2.25.3)` for a fixed index `n` and weight `k`.

This is the condition under which the ghost multiplicity `m_{n+1}(k)` equals `m_n(k) + 1`.
-/
def ghostMultiplicityIncPos (a sε : ℕ) (k : ℤ) (n : ℕ) : Prop :=
  (dUnr p a sε k : ℤ) ≤ (n : ℤ) ∧ (n : ℤ) < halfDIwClass p a sε k

/--
The “-1” condition from `(2.25.3)` for a fixed index `n` and weight `k`.

This is the condition under which the ghost multiplicity `m_n(k)` equals `m_{n+1}(k) + 1`.
-/
def ghostMultiplicityIncNeg (a sε : ℕ) (k : ℤ) (n : ℕ) : Prop :=
  halfDIwClass p a sε k ≤ (n : ℤ) ∧ (n : ℤ) < dIwClass p a sε k - dUnr p a sε k

omit [Fact (Nat.Prime p)] in
/--
Rewrite the midpoint inequality `n < ½ d_k^Iw` as a lower bound on the class index `k_•`.

This is the elementary algebra behind replacing `n < halfDIwClass` by `kMidBullet(n) < kBullet`
in Lemma `\label{L:increment of ghost valuation}`.
-/
theorem int_lt_halfDIwClass_iff_kMidBullet_lt (a sε : ℕ) (kBullet : ℤ) (n : ℕ) :
    (n : ℤ) < halfDIwClass p a sε kBullet ↔ kMidBullet p a sε n < kBullet := by
  have h :
      (n : ℤ) < kBullet + 1 - (deltaEpsilon p a sε : ℤ) ↔
        (n : ℤ) + (deltaEpsilon p a sε : ℤ) - 1 < kBullet := by
    constructor <;> intro hn <;> linarith
  simpa [halfDIwClass, kMidBullet, h]

omit [Fact (Nat.Prime p)] in
/--
Rewrite the midpoint inequality `½ d_k^Iw ≤ n` as an upper bound on the class index `k_•`.

This is the elementary algebra behind replacing `halfDIwClass ≤ n` by `kBullet ≤ kMidBullet(n)`
in Lemma `\label{L:increment of ghost valuation}`.
-/
theorem halfDIwClass_le_int_iff_le_kMidBullet (a sε : ℕ) (kBullet : ℤ) (n : ℕ) :
    halfDIwClass p a sε kBullet ≤ (n : ℤ) ↔ kBullet ≤ kMidBullet p a sε n := by
  have h :
      kBullet + 1 - (deltaEpsilon p a sε : ℤ) ≤ (n : ℤ) ↔
        kBullet ≤ (n : ℤ) + (deltaEpsilon p a sε : ℤ) - 1 := by
    constructor <;> intro hn <;> linarith
  simpa [halfDIwClass, kMidBullet, h]

omit [Fact (Nat.Prime p)] in
/--
The `+1` condition `ghostMultiplicityIncPos` rewritten using `kMidBullet`.
-/
theorem ghostMultiplicityIncPos_iff_dUnr_le_and_kMidBullet_lt (a sε : ℕ) (kBullet : ℤ) (n : ℕ) :
    ghostMultiplicityIncPos (p := p) a sε kBullet n ↔
      (dUnr p a sε kBullet : ℤ) ≤ (n : ℤ) ∧ kMidBullet p a sε n < kBullet := by
  constructor
  · intro h
    refine ⟨h.1, (int_lt_halfDIwClass_iff_kMidBullet_lt (p := p) (a := a) (sε := sε) _ _).1 h.2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, (int_lt_halfDIwClass_iff_kMidBullet_lt (p := p) (a := a) (sε := sε) _ _).2 h2⟩

omit [Fact (Nat.Prime p)] in
/--
The `-1` condition `ghostMultiplicityIncNeg` rewritten using `kMidBullet`.
-/
theorem ghostMultiplicityIncNeg_iff_le_kMidBullet_and_lt_end (a sε : ℕ) (kBullet : ℤ) (n : ℕ) :
    ghostMultiplicityIncNeg (p := p) a sε kBullet n ↔
      kBullet ≤ kMidBullet p a sε n ∧ (n : ℤ) < dIwClass p a sε kBullet - dUnr p a sε kBullet := by
  constructor
  · intro h
    refine ⟨(halfDIwClass_le_int_iff_le_kMidBullet (p := p) (a := a) (sε := sε) _ _).1 h.1, h.2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(halfDIwClass_le_int_iff_le_kMidBullet (p := p) (a := a) (sε := sε) _ _).2 h1, h2⟩

/--
The “+1” condition is decidable, since it is built from decidable inequalities on `ℤ`.
-/
instance ghostMultiplicityIncPos_decidablePred (a sε : ℕ) (n : ℕ) :
    DecidablePred (fun k : ℤ => ghostMultiplicityIncPos (p := p) a sε k n) := by
  intro k
  dsimp [ghostMultiplicityIncPos]
  infer_instance

/--
The “-1” condition is decidable, since it is built from decidable inequalities on `ℤ`.
-/
instance ghostMultiplicityIncNeg_decidablePred (a sε : ℕ) (n : ℕ) :
    DecidablePred (fun k : ℤ => ghostMultiplicityIncNeg (p := p) a sε k n) := by
  intro k
  dsimp [ghostMultiplicityIncNeg]
  infer_instance

/--
First-order valuation increment for hatted ghost coefficients, expressed without subtraction.

Let `m_n(k)` be the ghost multiplicity and `g_{n,\\hat k₀}` the product with the `k₀`-factor removed
(Notation 4.17). Evaluating at `w_{k₀}` and applying an additive valuation `v`, the identity
`m_{n+1}(k) - m_n(k) ∈ {1,-1,0}` from `(2.25.3)` yields:

`v(g_{n+1,\\hat k₀}(w_{k₀})) + ∑_{k: incNeg} v(w_{k₀}-w_k)
 = v(g_{n,\\hat k₀}(w_{k₀})) + ∑_{k: incPos} v(w_{k₀}-w_k)`.

This is the additive-monoid version of equation `\label{E:increment of ghost series valuation 1}`
from Lemma `\label{L:increment of ghost valuation}` in the paper, before rewriting the conditions
using the extremal indices `k_{min,•}`, `k_{mid,•}`, `k_{max,•}`.
-/
theorem ghostCoeffHat_eval_val_succ_add_sum_incNeg_eq_add_sum_incPos (v : AddValuation R Γ₀)
    (w : ℤ → R) (a sε : ℕ) (hs : sε < pMinusOne p) (K : Finset ℤ) (k0 : ℤ) (n : ℕ) :
    v ((ghostCoeffHat (R := R) w (fun k => ghostMultiplicityNat p a sε k (n + 1)) K k0).eval
          (w k0)) +
        ∑ k ∈ K.erase k0 with ghostMultiplicityIncNeg (p := p) a sε k n, v (w k0 - w k) =
      v ((ghostCoeffHat (R := R) w (fun k => ghostMultiplicityNat p a sε k n) K k0).eval (w k0)) +
        ∑ k ∈ K.erase k0 with ghostMultiplicityIncPos (p := p) a sε k n, v (w k0 - w k) := by
  classical
  -- Rewrite both valuation terms using `ghostCoeffHat_eval_val`.
  have hv_succ :
      v
            ((ghostCoeffHat (R := R) w (fun k => ghostMultiplicityNat p a sε k (n + 1)) K k0).eval
              (w k0)) =
        ∑ k ∈ K.erase k0, ghostMultiplicityNat p a sε k (n + 1) • v (w k0 - w k) :=
    ghostCoeffHat_eval_val (v := v) (w := w) (m := fun k => ghostMultiplicityNat p a sε k (n + 1))
      (K := K) (k0 := k0)
  have hv :
      v ((ghostCoeffHat (R := R) w (fun k => ghostMultiplicityNat p a sε k n) K k0).eval (w k0)) =
        ∑ k ∈ K.erase k0, ghostMultiplicityNat p a sε k n • v (w k0 - w k) :=
    ghostCoeffHat_eval_val (v := v) (w := w) (m := fun k => ghostMultiplicityNat p a sε k n)
      (K := K) (k0 := k0)
  -- Convert the filtered sums into “indicator” sums.
  have hsumPos :
      (∑ k ∈ K.erase k0 with ghostMultiplicityIncPos (p := p) a sε k n, v (w k0 - w k)) =
        ∑ k ∈ K.erase k0, if ghostMultiplicityIncPos (p := p) a sε k n then v (w k0 - w k) else 0 :=
    by
      simpa using
        (Finset.sum_filter (s := K.erase k0)
          (p := fun k => ghostMultiplicityIncPos (p := p) a sε k n)
          (f := fun k => v (w k0 - w k)))
  have hsumNeg :
      (∑ k ∈ K.erase k0 with ghostMultiplicityIncNeg (p := p) a sε k n, v (w k0 - w k)) =
        ∑ k ∈ K.erase k0, if ghostMultiplicityIncNeg (p := p) a sε k n then v (w k0 - w k) else 0 :=
    by
      simpa using
        (Finset.sum_filter (s := K.erase k0)
          (p := fun k => ghostMultiplicityIncNeg (p := p) a sε k n)
          (f := fun k => v (w k0 - w k)))
  -- Reduce to a pointwise equality inside a single sum.
  rw [hv_succ, hv, hsumNeg, hsumPos]
  -- Combine sums on each side.
  -- Left: `sum + sum` becomes `sum (· + ·)`, and similarly on the right.
  have hsum_left :
      (∑ k ∈ K.erase k0, ghostMultiplicityNat p a sε k (n + 1) • v (w k0 - w k)) +
          (∑ k ∈ K.erase k0,
            if ghostMultiplicityIncNeg (p := p) a sε k n then v (w k0 - w k) else 0) =
        ∑ k ∈ K.erase k0,
          (ghostMultiplicityNat p a sε k (n + 1) • v (w k0 - w k) +
            if ghostMultiplicityIncNeg (p := p) a sε k n then v (w k0 - w k) else 0) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_add_distrib (s := K.erase k0)
            (f := fun k => ghostMultiplicityNat p a sε k (n + 1) • v (w k0 - w k))
            (g := fun k =>
              if ghostMultiplicityIncNeg (p := p) a sε k n then v (w k0 - w k) else 0)).symm
  have hsum_right :
      (∑ k ∈ K.erase k0, ghostMultiplicityNat p a sε k n • v (w k0 - w k)) +
          (∑ k ∈ K.erase k0,
            if ghostMultiplicityIncPos (p := p) a sε k n then v (w k0 - w k) else 0) =
        ∑ k ∈ K.erase k0,
          (ghostMultiplicityNat p a sε k n • v (w k0 - w k) +
            if ghostMultiplicityIncPos (p := p) a sε k n then v (w k0 - w k) else 0) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_add_distrib (s := K.erase k0)
            (f := fun k => ghostMultiplicityNat p a sε k n • v (w k0 - w k))
            (g := fun k =>
              if ghostMultiplicityIncPos (p := p) a sε k n then v (w k0 - w k) else 0)).symm
  -- Apply the combined-sum rewrites.
  rw [hsum_left, hsum_right]
  -- Now prove equality by pointwise rewriting on `K.erase k0`.
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases hPos : ghostMultiplicityIncPos (p := p) a sε k n
  · have hNeg : ¬ghostMultiplicityIncNeg (p := p) a sε k n := by
      intro h
      exact (not_lt_of_ge h.1) hPos.2
    have hm :
        ghostMultiplicityNat p a sε k (n + 1) = ghostMultiplicityNat p a sε k n + 1 :=
      ghostMultiplicityNat_succ_eq_add_one_of_pos (p := p) (a := a) (sε := sε) hs (kBullet := k)
        (n := n) hPos
    -- Simplify the conditionals and close using `succ_nsmul`.
    -- After rewriting by `hm`, this is exactly `(m_n+1)•v = m_n•v + v`.
    simpa [hPos, hNeg, hm] using
      (succ_nsmul (v (w k0 - w k)) (ghostMultiplicityNat p a sε k n))
  · by_cases hNeg : ghostMultiplicityIncNeg (p := p) a sε k n
    · have hm :
          ghostMultiplicityNat p a sε k n = ghostMultiplicityNat p a sε k (n + 1) + 1 :=
        ghostMultiplicityNat_eq_succ_add_one_of_neg (p := p) (a := a) (sε := sε) hs (kBullet := k)
          (n := n) hNeg
      -- Simplify the conditionals and close using `succ_nsmul` (in reverse direction).
      -- After rewriting by `hm`, this is exactly `m_{n+1}•v + v = (m_{n+1}+1)•v`.
      have hstep :
          ghostMultiplicityNat p a sε k (n + 1) • v (w k0 - w k) + v (w k0 - w k) =
            (ghostMultiplicityNat p a sε k (n + 1) + 1) • v (w k0 - w k) := by
        simpa using
          (succ_nsmul (v (w k0 - w k)) (ghostMultiplicityNat p a sε k (n + 1))).symm
      simpa [hPos, hNeg, hm] using hstep
    · have hm :
          ghostMultiplicityNat p a sε k (n + 1) = ghostMultiplicityNat p a sε k n :=
        ghostMultiplicityNat_succ_eq_of_else (p := p) (a := a) (sε := sε) hs (kBullet := k) (n := n)
          hPos hNeg
      simp [hPos, hNeg, hm]

/--
Second-order valuation increment for hatted ghost coefficients, expressed without subtraction.

This is the additive-monoid analogue of equation `\label{E:increment of ghost series valuation 2}`
in Lemma `\label{L:increment of ghost valuation}` in the paper, before rewriting the conditions
using extremal indices.

It is obtained by applying
`ghostCoeffHat_eval_val_succ_add_sum_incNeg_eq_add_sum_incPos` at `n` and `n-1` and adding the
resulting equalities.
-/
theorem ghostCoeffHat_eval_val_secondOrder_add_sums_eq_two_nsmul_add_sums (v : AddValuation R Γ₀)
    (w : ℤ → R) (a sε : ℕ) (hs : sε < pMinusOne p) (K : Finset ℤ) (k0 : ℤ) (n : ℕ)
    (hn : 1 ≤ n) :
    v ((ghostCoeffHat (R := R) w (fun k => ghostMultiplicityNat p a sε k (n + 1)) K k0).eval
          (w k0)) +
        v ((ghostCoeffHat (R := R) w (fun k => ghostMultiplicityNat p a sε k (n - 1)) K k0).eval
          (w k0)) +
        (∑ k ∈ K.erase k0 with ghostMultiplicityIncNeg (p := p) a sε k n, v (w k0 - w k)) +
        (∑ k ∈ K.erase k0 with ghostMultiplicityIncPos (p := p) a sε k (n - 1), v (w k0 - w k)) =
      2 •
          v ((ghostCoeffHat (R := R) w (fun k => ghostMultiplicityNat p a sε k n) K k0).eval
            (w k0)) +
        (∑ k ∈ K.erase k0 with ghostMultiplicityIncPos (p := p) a sε k n, v (w k0 - w k)) +
        (∑ k ∈ K.erase k0 with ghostMultiplicityIncNeg (p := p) a sε k (n - 1), v (w k0 - w k)) :=
  by
  classical
  let g : ℕ → R := fun m =>
    (ghostCoeffHat (R := R) w (fun k => ghostMultiplicityNat p a sε k m) K k0).eval (w k0)
  let sumPos : ℕ → Γ₀ := fun m =>
    ∑ k ∈ K.erase k0 with ghostMultiplicityIncPos (p := p) a sε k m, v (w k0 - w k)
  let sumNeg : ℕ → Γ₀ := fun m =>
    ∑ k ∈ K.erase k0 with ghostMultiplicityIncNeg (p := p) a sε k m, v (w k0 - w k)

  have hsucc : v (g (n + 1)) + sumNeg n = v (g n) + sumPos n := by
    simpa [g, sumPos, sumNeg] using
      ghostCoeffHat_eval_val_succ_add_sum_incNeg_eq_add_sum_incPos (p := p) (v := v) (w := w)
        (a := a) (sε := sε) hs (K := K) (k0 := k0) (n := n)

  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hpred_raw : v (g ((n - 1) + 1)) + sumNeg (n - 1) = v (g (n - 1)) + sumPos (n - 1) := by
    simpa [g, sumPos, sumNeg] using
      ghostCoeffHat_eval_val_succ_add_sum_incNeg_eq_add_sum_incPos (p := p) (v := v) (w := w)
        (a := a) (sε := sε) hs (K := K) (k0 := k0) (n := n - 1)
  have hpred : v (g n) + sumNeg (n - 1) = v (g (n - 1)) + sumPos (n - 1) := by
    simpa [hn'] using hpred_raw
  have hpred' : v (g (n - 1)) + sumPos (n - 1) = v (g n) + sumNeg (n - 1) := hpred.symm

  have hadd :
      (v (g (n + 1)) + sumNeg n) + (v (g (n - 1)) + sumPos (n - 1)) =
        (v (g n) + sumPos n) + (v (g n) + sumNeg (n - 1)) := by
    have htmp := congrArg (fun x => x + (v (g (n - 1)) + sumPos (n - 1))) hsucc
    calc
      (v (g (n + 1)) + sumNeg n) + (v (g (n - 1)) + sumPos (n - 1)) =
          (v (g n) + sumPos n) + (v (g (n - 1)) + sumPos (n - 1)) := by
            simpa [add_assoc] using htmp
      _ = (v (g n) + sumPos n) + (v (g n) + sumNeg (n - 1)) := by
            simpa [hpred']

  -- Rewrite back in terms of `ghostCoeffHat` and reorder into the stated `2•`-form.
  simpa [g, sumPos, sumNeg, two_nsmul, add_assoc, add_left_comm, add_comm] using hadd

end

end Formulation

end GhostConjecture
