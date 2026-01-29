import GhostConjecture.Formulation.UnramifiedDimensions
import Mathlib.Tactic

namespace GhostConjecture

namespace Formulation

variable (p : ℕ) [Fact (Nat.Prime p)]

/--
The Iwasawa dimension `d_k^Iw(\\tilde ε₁)` in the congruence class `k = k_ε + k_•(p-1)`,
expressed in terms of `kBullet : ℤ` (the paper's `k_•`).
-/
def dIwClass (a sε : ℕ) (kBullet : ℤ) : ℤ :=
  dIw p a sε ((kEpsilon p a sε : ℤ) + kBullet * (pMinusOne p : ℤ))

/--
The “new” dimension `d_k^new(ε₁) = d_k^Iw(\\tilde ε₁) - 2 d_k^unr(ε₁)` in the same congruence class.
-/
def dNewClass (a sε : ℕ) (kBullet : ℤ) : ℤ :=
  dIwClass p a sε kBullet - 2 * dUnr p a sε kBullet

/--
The ghost zero multiplicity `m_n^{(ε)}(k)` from Definition `D:ghost series`.

We record the “tent function” as an integer-valued function, using the class parameter `kBullet`
for weights with `k = k_ε + k_•(p-1)`.
-/
def ghostMultiplicity (a sε : ℕ) (kBullet : ℤ) (n : ℕ) : ℤ :=
  let dU : ℤ := dUnr p a sε kBullet
  let dI : ℤ := dIwClass p a sε kBullet
  let nZ : ℤ := n
  max 0 (min (nZ - dU) (dI - dU - nZ))

/--
The explicit `d_k^Iw(\\tilde ε₁)` formula in the congruence class `k = k_ε + k_•(p-1)`.

This is Corollary `C:dIw is even`, rewritten in terms of `dIwClass`.
-/
theorem dIwClass_eq_two_mul_kBullet_add_two_sub_two_mul_delta (a sε : ℕ) (hs : sε < pMinusOne p)
    (kBullet : ℤ) :
    dIwClass p a sε kBullet = 2 * kBullet + 2 - 2 * (deltaEpsilon p a sε : ℤ) := by
  simpa [dIwClass] using
    (dIw_eq_two_mul_kBullet_add_two_sub_two_mul_delta (p := p) (a := a) (sε := sε) hs kBullet)

/--
The midpoint `\\tfrac12 d_k^Iw(\\tilde ε₁)` in the congruence class `k = k_ε + k_•(p-1)`.

We record it in the explicit form `k_• + 1 - δ_ε`, using Corollary `C:dIw is even`.
-/
def halfDIwClass (a sε : ℕ) (kBullet : ℤ) : ℤ :=
  kBullet + 1 - (deltaEpsilon p a sε : ℤ)

/--
Corollary `C:dIw is even` in the form `d_k^Iw(\\tilde ε₁) = 2 * (\\tfrac12 d_k^Iw(\\tilde ε₁))`.
-/
theorem dIwClass_eq_two_mul_halfDIwClass (a sε : ℕ) (hs : sε < pMinusOne p) (kBullet : ℤ) :
    dIwClass p a sε kBullet = 2 * halfDIwClass p a sε kBullet := by
  have hd :
      dIwClass p a sε kBullet = 2 * kBullet + 2 - 2 * (deltaEpsilon p a sε : ℤ) :=
    dIwClass_eq_two_mul_kBullet_add_two_sub_two_mul_delta (p := p) (a := a) (sε := sε) hs kBullet
  -- Factor out the common factor `2`.
  calc
    dIwClass p a sε kBullet = 2 * kBullet + 2 - 2 * (deltaEpsilon p a sε : ℤ) := hd
    _ = 2 * halfDIwClass p a sε kBullet := by
          simp [halfDIwClass]
          ring

/--
Equation `(2.25.3)` from Definition `D:ghost series`: the first discrete difference of the ghost
multiplicity is `+1` before the midpoint and `-1` after it.

We write the midpoint as `halfDIwClass`, using Corollary `C:dIw is even`.
-/
theorem ghostMultiplicity_succ_sub (a sε : ℕ) (hs : sε < pMinusOne p) (kBullet : ℤ) (n : ℕ) :
    ghostMultiplicity p a sε kBullet (n + 1) - ghostMultiplicity p a sε kBullet n =
      if (dUnr p a sε kBullet : ℤ) ≤ (n : ℤ) ∧ (n : ℤ) < halfDIwClass p a sε kBullet then
        1
      else if halfDIwClass p a sε kBullet ≤ (n : ℤ) ∧
          (n : ℤ) < dIwClass p a sε kBullet - dUnr p a sε kBullet then
        -1
      else 0 := by
  set dU : ℤ := dUnr p a sε kBullet
  set dI : ℤ := dIwClass p a sε kBullet
  set mid : ℤ := halfDIwClass p a sε kBullet
  have hdI : dI = 2 * mid := by
    simpa [dI, mid] using dIwClass_eq_two_mul_halfDIwClass (p := p) (a := a) (sε := sε) hs kBullet
  set nZ : ℤ := (n : ℤ)
  have hnZ_succ : ((n + 1 : ℕ) : ℤ) = nZ + 1 := by simp [nZ, Nat.cast_add, Nat.cast_one]
  by_cases hPos : dU ≤ nZ ∧ nZ < mid
  · have hnZ_ge : dU ≤ nZ := hPos.1
    have hnZ_lt : nZ < mid := hPos.2
    have hnZ_succ_ge : dU ≤ nZ + 1 := by linarith
    have hnZ_succ_le : nZ + 1 ≤ mid := by linarith
    have hLeft_le : nZ - dU ≤ dI - dU - nZ := by
      -- `nZ < mid` and `dI = 2*mid` imply `2*nZ ≤ dI`.
      have : 2 * nZ ≤ dI := by
        -- strict inequality gives `2*nZ < 2*mid = dI`.
        have : 2 * nZ < 2 * mid := by linarith
        simpa [hdI] using this.le
      linarith
    have hLeft_succ_le : (nZ + 1) - dU ≤ dI - dU - (nZ + 1) := by
      have : 2 * (nZ + 1) ≤ dI := by
        have : 2 * (nZ + 1) ≤ 2 * mid := by nlinarith
        simpa [hdI] using this
      linarith
    -- Evaluate `ghostMultiplicity` at `n` and `n+1` on the increasing side.
    have hm_n : ghostMultiplicity p a sε kBullet n = nZ - dU := by
      have h0 : 0 ≤ nZ - dU := sub_nonneg.mpr hnZ_ge
      simp [ghostMultiplicity, dU, dI, nZ, min_eq_left hLeft_le, max_eq_right h0]
    have hm_succ : ghostMultiplicity p a sε kBullet (n + 1) = (nZ + 1) - dU := by
      have h0 : 0 ≤ (nZ + 1) - dU := sub_nonneg.mpr hnZ_succ_ge
      simp [ghostMultiplicity, dU, dI, nZ, hnZ_succ, min_eq_left hLeft_succ_le, max_eq_right h0]
    -- Conclude.
    simp [dU, mid, nZ, hPos, hm_n, hm_succ]
  · by_cases hNeg : mid ≤ nZ ∧ nZ < dI - dU
    · have hnZ_ge : mid ≤ nZ := hNeg.1
      have hnZ_lt : nZ < dI - dU := hNeg.2
      have hnZ_succ_le : nZ + 1 ≤ dI - dU := by linarith
      have hRight_le : dI - dU - nZ ≤ nZ - dU := by
        -- `mid ≤ nZ` and `dI = 2*mid` imply `dI ≤ 2*nZ`.
        have : dI ≤ 2 * nZ := by
          have : 2 * mid ≤ 2 * nZ := by nlinarith
          simpa [hdI] using this
        linarith
      have hRight_succ_le : dI - dU - (nZ + 1) ≤ (nZ + 1) - dU := by
        have : dI ≤ 2 * (nZ + 1) := by
          have : 2 * mid ≤ 2 * (nZ + 1) := by nlinarith
          simpa [hdI] using this
        linarith
      have hm_n : ghostMultiplicity p a sε kBullet n = dI - dU - nZ := by
        have h0 : 0 ≤ dI - dU - nZ := sub_nonneg.mpr hnZ_lt.le
        simp [ghostMultiplicity, dU, dI, nZ, min_eq_right hRight_le, max_eq_right h0]
      have hm_succ : ghostMultiplicity p a sε kBullet (n + 1) = dI - dU - (nZ + 1) := by
        have h0 : 0 ≤ dI - dU - (nZ + 1) := sub_nonneg.mpr hnZ_succ_le
        simp [ghostMultiplicity, dU, dI, nZ, hnZ_succ, min_eq_right hRight_succ_le, max_eq_right h0]
      simp [dU, dI, mid, nZ, hPos, hNeg, hm_n, hm_succ]
    · -- Outside the tent region, both values are `0`.
      have hOutside : nZ < dU ∨ dI - dU ≤ nZ := by
        by_cases hDU : dU ≤ nZ
        · have : mid ≤ nZ := by
            have : ¬nZ < mid := by
              intro hlt
              exact hPos ⟨hDU, hlt⟩
            exact le_of_not_gt this
          have : ¬nZ < dI - dU := by
            intro hlt
            exact hNeg ⟨this, hlt⟩
          exact Or.inr (le_of_not_gt this)
        · exact Or.inl (lt_of_not_ge hDU)
      have hm_n : ghostMultiplicity p a sε kBullet n = 0 := by
        rcases hOutside with hlt | hge
        · have hle : nZ - dU ≤ 0 := by linarith
          have hmin : min (nZ - dU) (dI - dU - nZ) ≤ 0 := le_trans (min_le_left _ _) hle
          simp [ghostMultiplicity, dU, dI, nZ, max_eq_left hmin]
        · have hle : dI - dU - nZ ≤ 0 := by linarith
          have hmin : min (nZ - dU) (dI - dU - nZ) ≤ 0 := le_trans (min_le_right _ _) hle
          simp [ghostMultiplicity, dU, dI, nZ, max_eq_left hmin]
      have hm_succ : ghostMultiplicity p a sε kBullet (n + 1) = 0 := by
        rcases hOutside with hlt | hge
        · have hle : (nZ + 1) - dU ≤ 0 := by linarith
          have hmin :
              min ((nZ + 1) - dU) (dI - dU - (nZ + 1)) ≤ 0 :=
            le_trans (min_le_left _ _) hle
          simp [ghostMultiplicity, dU, dI, nZ, hnZ_succ, max_eq_left hmin]
        · have hle : dI - dU - (nZ + 1) ≤ 0 := by linarith
          have hmin :
              min ((nZ + 1) - dU) (dI - dU - (nZ + 1)) ≤ 0 :=
            le_trans (min_le_right _ _) hle
          simp [ghostMultiplicity, dU, dI, nZ, hnZ_succ, max_eq_left hmin]
      simp [dU, dI, mid, nZ, hPos, hNeg, hm_n, hm_succ]

/--
Equation `(2.25.3)` in “backward difference” form: a formula for `m_n - m_{n-1}`.

This is the same content as `ghostMultiplicity_succ_sub`, but with the inequalities rewritten
in terms of the index `n` (rather than `n-1`).
-/
theorem ghostMultiplicity_sub_pred (a sε : ℕ) (hs : sε < pMinusOne p) (kBullet : ℤ) (n : ℕ)
    (hn : 1 ≤ n) :
    ghostMultiplicity p a sε kBullet n - ghostMultiplicity p a sε kBullet (n - 1) =
      if (dUnr p a sε kBullet : ℤ) < (n : ℤ) ∧ (n : ℤ) ≤ halfDIwClass p a sε kBullet then
        1
      else if halfDIwClass p a sε kBullet < (n : ℤ) ∧
          (n : ℤ) ≤ dIwClass p a sε kBullet - dUnr p a sε kBullet then
        -1
      else 0 := by
  have h :=
    ghostMultiplicity_succ_sub (p := p) (a := a) (sε := sε) hs (kBullet := kBullet) (n := n - 1)
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
    simpa using (Int.ofNat_sub (m := 1) (n := n) hn)
  simpa [hn', hcast, Int.le_sub_one_iff, Int.sub_one_lt_iff, and_left_comm, and_assoc, and_comm] using h

/--
Equation `(2.25.4)` from Definition `D:ghost series`: the second discrete difference of the ghost
multiplicity.

We assume the nondegenerate range `d_k^unr(ε₁) < \\tfrac12 d_k^Iw(\\tilde ε₁)`, which is the regime
in which the “cascading pattern” produces a genuine tent function.
-/
theorem ghostMultiplicity_secondDifference (a sε : ℕ) (hs : sε < pMinusOne p) (kBullet : ℤ)
    (n : ℕ) (hn : 2 ≤ n)
    (hUnr_lt_mid : (dUnr p a sε kBullet : ℤ) < halfDIwClass p a sε kBullet) :
    ghostMultiplicity p a sε kBullet (n + 1) - 2 * ghostMultiplicity p a sε kBullet n +
        ghostMultiplicity p a sε kBullet (n - 1) =
      if (n : ℤ) = halfDIwClass p a sε kBullet then
        -2
      else if (n : ℤ) = dUnr p a sε kBullet ∨
          (n : ℤ) = dIwClass p a sε kBullet - dUnr p a sε kBullet then
        1
      else 0 := by
  set dU : ℤ := dUnr p a sε kBullet
  set dI : ℤ := dIwClass p a sε kBullet
  set mid : ℤ := halfDIwClass p a sε kBullet
  set nZ : ℤ := (n : ℤ)
  set endZ : ℤ := dI - dU
  have hUnr_lt_mid' : dU < mid := by simpa [dU, mid] using hUnr_lt_mid
  have hdI : dI = 2 * mid := by
    simpa [dI, mid] using dIwClass_eq_two_mul_halfDIwClass (p := p) (a := a) (sε := sε) hs kBullet
  have hMid_lt_end : mid < endZ := by linarith [hdI, hUnr_lt_mid']

  have hRing :
      ghostMultiplicity p a sε kBullet (n + 1) - 2 * ghostMultiplicity p a sε kBullet n +
            ghostMultiplicity p a sε kBullet (n - 1) =
          (ghostMultiplicity p a sε kBullet (n + 1) - ghostMultiplicity p a sε kBullet n) -
            (ghostMultiplicity p a sε kBullet n - ghostMultiplicity p a sε kBullet (n - 1)) := by
    ring

  have hΔn :
      ghostMultiplicity p a sε kBullet (n + 1) - ghostMultiplicity p a sε kBullet n =
        if dU ≤ nZ ∧ nZ < mid then 1 else if mid ≤ nZ ∧ nZ < endZ then -1 else 0 := by
    simpa [dU, dI, mid, nZ, endZ] using
      ghostMultiplicity_succ_sub (p := p) (a := a) (sε := sε) hs (kBullet := kBullet) (n := n)

  have hpos : 1 ≤ n := le_trans (by decide) hn
  have hΔpred :
      ghostMultiplicity p a sε kBullet n - ghostMultiplicity p a sε kBullet (n - 1) =
        if dU < nZ ∧ nZ ≤ mid then 1 else if mid < nZ ∧ nZ ≤ endZ then -1 else 0 := by
    simpa [dU, dI, mid, nZ, endZ] using
      ghostMultiplicity_sub_pred (p := p) (a := a) (sε := sε) hs (kBullet := kBullet) (n := n) hpos

  by_cases hEqMid : nZ = mid
  · have hΔn_val :
        ghostMultiplicity p a sε kBullet (n + 1) - ghostMultiplicity p a sε kBullet n = -1 := by
      have hPos : ¬(dU ≤ nZ ∧ nZ < mid) := by
        intro h
        exact (lt_irrefl mid) (by simpa [hEqMid] using h.2)
      have hNeg : mid ≤ nZ ∧ nZ < endZ := by
        refine ⟨by simpa [hEqMid], ?_⟩
        simpa [hEqMid] using hMid_lt_end
      simp [hΔn, hPos, hNeg]
    have hΔpred_val :
        ghostMultiplicity p a sε kBullet n - ghostMultiplicity p a sε kBullet (n - 1) = 1 := by
      have hPos : dU < nZ ∧ nZ ≤ mid := by
        refine ⟨by simpa [hEqMid] using hUnr_lt_mid', by simpa [hEqMid]⟩
      have hNeg : ¬(mid < nZ ∧ nZ ≤ endZ) := by
        intro h
        exact lt_irrefl mid (by simpa [hEqMid] using h.1)
      simp [hΔpred, hPos, hNeg]
    -- `(-1) - 1 = -2`.
    have hLHS :
        ghostMultiplicity p a sε kBullet (n + 1) - 2 * ghostMultiplicity p a sε kBullet n +
            ghostMultiplicity p a sε kBullet (n - 1) = -2 := by
      simp [hRing, hΔn_val, hΔpred_val]
    simpa [hEqMid] using hLHS
  · by_cases hEqUnr : nZ = dU
    · have hΔn_val :
          ghostMultiplicity p a sε kBullet (n + 1) - ghostMultiplicity p a sε kBullet n = 1 := by
        have hPos : dU ≤ nZ ∧ nZ < mid := ⟨by simpa [hEqUnr], by simpa [hEqUnr] using hUnr_lt_mid'⟩
        simp [hΔn, hPos]
      have hΔpred_val :
          ghostMultiplicity p a sε kBullet n - ghostMultiplicity p a sε kBullet (n - 1) = 0 := by
        have hPos : ¬(dU < nZ ∧ nZ ≤ mid) := by
          intro h
          exact lt_irrefl dU (by simpa [hEqUnr] using h.1)
        have hNeg : ¬(mid < nZ ∧ nZ ≤ endZ) := by
          intro h
          have : mid < dU := by simpa [hEqUnr] using h.1
          exact not_lt_of_ge (le_of_lt hUnr_lt_mid') this
        simp [hΔpred, hPos, hNeg]
      -- `1 - 0 = 1`, and the RHS selects the second branch.
      have hLHS :
          ghostMultiplicity p a sε kBullet (n + 1) - 2 * ghostMultiplicity p a sε kBullet n +
              ghostMultiplicity p a sε kBullet (n - 1) = 1 := by
        simp [hRing, hΔn_val, hΔpred_val]
      have hRHS :
          (if nZ = mid then (-2 : ℤ) else if nZ = dU ∨ nZ = endZ then 1 else 0) = 1 := by
        have :
            (if nZ = mid then (-2 : ℤ) else if nZ = dU ∨ nZ = endZ then 1 else 0) =
              (if nZ = dU ∨ nZ = endZ then 1 else 0) := by
          simp [hEqMid]
        simpa [this, hEqUnr]
      simpa [hRHS] using hLHS
    · by_cases hEqEnd : nZ = endZ
      · have hΔn_val :
            ghostMultiplicity p a sε kBullet (n + 1) - ghostMultiplicity p a sε kBullet n = 0 := by
          have hPos : ¬(dU ≤ nZ ∧ nZ < mid) := by
            intro h
            have hmid_lt_nZ : mid < nZ := by simpa [hEqEnd] using hMid_lt_end
            exact (not_lt_of_ge hmid_lt_nZ.le) h.2
          have hNeg : ¬(mid ≤ nZ ∧ nZ < endZ) := by
            intro h
            exact lt_irrefl endZ (by simpa [hEqEnd] using h.2)
          simp [hΔn, hPos, hNeg]
        have hΔpred_val :
            ghostMultiplicity p a sε kBullet n - ghostMultiplicity p a sε kBullet (n - 1) = -1 := by
          have hPos : ¬(dU < nZ ∧ nZ ≤ mid) := by
            intro h
            have hmid_lt_nZ : mid < nZ := by simpa [hEqEnd] using hMid_lt_end
            exact (not_lt_of_ge h.2) hmid_lt_nZ
          have hNeg : mid < nZ ∧ nZ ≤ endZ := by
            refine ⟨by simpa [hEqEnd] using hMid_lt_end, by simpa [hEqEnd]⟩
          simp [hΔpred, hPos, hNeg]
        -- `0 - (-1) = 1`, and the RHS selects the second branch.
        have hLHS :
            ghostMultiplicity p a sε kBullet (n + 1) - 2 * ghostMultiplicity p a sε kBullet n +
                ghostMultiplicity p a sε kBullet (n - 1) = 1 := by
          simp [hRing, hΔn_val, hΔpred_val]
        have hRHS :
            (if nZ = mid then (-2 : ℤ) else if nZ = dU ∨ nZ = endZ then 1 else 0) = 1 := by
          have :
              (if nZ = mid then (-2 : ℤ) else if nZ = dU ∨ nZ = endZ then 1 else 0) =
                (if nZ = dU ∨ nZ = endZ then 1 else 0) := by
            simp [hEqMid]
          simpa [this, hEqEnd]
        simpa [hRHS] using hLHS
      · -- Generic case: show both first differences agree, hence the second difference is `0`.
        by_cases hltDU : nZ < dU
        · have hPosn : ¬(dU ≤ nZ ∧ nZ < mid) := by intro h; exact not_lt_of_ge h.1 hltDU
          have hNegn : ¬(mid ≤ nZ ∧ nZ < endZ) := by
            intro h; exact not_lt_of_ge (le_trans (le_of_lt hUnr_lt_mid') h.1) hltDU
          have hPosp : ¬(dU < nZ ∧ nZ ≤ mid) := by intro h; exact not_lt_of_ge (le_of_lt h.1) hltDU
          have hNegp : ¬(mid < nZ ∧ nZ ≤ endZ) := by
            intro h; exact not_lt_of_ge (le_trans (le_of_lt hUnr_lt_mid') (le_of_lt h.1)) hltDU
          have hLHS :
              ghostMultiplicity p a sε kBullet (n + 1) - 2 * ghostMultiplicity p a sε kBullet n +
                  ghostMultiplicity p a sε kBullet (n - 1) = 0 := by
            simp [hRing, hΔn, hΔpred, hPosn, hNegn, hPosp, hNegp]
          simpa [hEqMid, hEqUnr, hEqEnd] using hLHS
        · have hgeDU : dU ≤ nZ := le_of_not_gt hltDU
          have hgtDU : dU < nZ := lt_of_le_of_ne hgeDU (fun h => hEqUnr h.symm)
          by_cases hltMid : nZ < mid
          · have hPosn : dU ≤ nZ ∧ nZ < mid := ⟨hgtDU.le, hltMid⟩
            have hNegn : ¬(mid ≤ nZ ∧ nZ < endZ) := by intro h; exact not_lt_of_ge h.1 hltMid
            have hPosp : dU < nZ ∧ nZ ≤ mid := ⟨hgtDU, le_of_lt hltMid⟩
            have hNegp : ¬(mid < nZ ∧ nZ ≤ endZ) := by intro h; exact not_lt_of_ge (le_of_lt h.1) hltMid
            have hLHS :
                ghostMultiplicity p a sε kBullet (n + 1) - 2 * ghostMultiplicity p a sε kBullet n +
                    ghostMultiplicity p a sε kBullet (n - 1) = 0 := by
              simp [hRing, hΔn, hΔpred, hPosn, hNegn, hPosp, hNegp]
            simpa [hEqMid, hEqUnr, hEqEnd] using hLHS
          · have hgeMid : mid ≤ nZ := le_of_not_gt hltMid
            have hgtMid : mid < nZ := lt_of_le_of_ne hgeMid (fun h => hEqMid h.symm)
            by_cases hltEnd : nZ < endZ
            · have hPosn : ¬(dU ≤ nZ ∧ nZ < mid) := by
                intro h; exact not_lt_of_ge hgtMid.le h.2
              have hNegn : mid ≤ nZ ∧ nZ < endZ := ⟨hgtMid.le, hltEnd⟩
              have hPosp : ¬(dU < nZ ∧ nZ ≤ mid) := by
                intro h; exact not_lt_of_ge h.2 hgtMid
              have hNegp : mid < nZ ∧ nZ ≤ endZ := ⟨hgtMid, le_of_lt hltEnd⟩
              have hLHS :
                  ghostMultiplicity p a sε kBullet (n + 1) - 2 * ghostMultiplicity p a sε kBullet n +
                      ghostMultiplicity p a sε kBullet (n - 1) = 0 := by
                simp [hRing, hΔn, hΔpred, hPosn, hNegn, hPosp, hNegp]
              simpa [hEqMid, hEqUnr, hEqEnd] using hLHS
            · have hgeEnd : endZ ≤ nZ := le_of_not_gt hltEnd
              have hgtEnd : endZ < nZ := lt_of_le_of_ne hgeEnd (fun h => hEqEnd h.symm)
              have hPosn : ¬(dU ≤ nZ ∧ nZ < mid) := by
                intro h; exact not_lt_of_ge hgtMid.le h.2
              have hNegn : ¬(mid ≤ nZ ∧ nZ < endZ) := by
                intro h; exact not_lt_of_ge (le_of_lt hgtEnd) h.2
              have hPosp : ¬(dU < nZ ∧ nZ ≤ mid) := by
                intro h; exact not_lt_of_ge h.2 hgtMid
              have hNegp : ¬(mid < nZ ∧ nZ ≤ endZ) := by
                intro h
                exact lt_irrefl endZ (lt_of_lt_of_le hgtEnd h.2)
              have hLHS :
                  ghostMultiplicity p a sε kBullet (n + 1) - 2 * ghostMultiplicity p a sε kBullet n +
                      ghostMultiplicity p a sε kBullet (n - 1) = 0 := by
                simp [hRing, hΔn, hΔpred, hPosn, hNegn, hPosp, hNegp]
              simpa [hEqMid, hEqUnr, hEqEnd] using hLHS

end Formulation

end GhostConjecture
