import GhostConjecture.Formulation.Prop418Increments
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers

namespace GhostConjecture

namespace Formulation

open scoped BigOperators

noncomputable section

variable (p : ℕ) [Fact (Nat.Prime p)]

/--
A concrete choice of topological generator of `1 + pℤ_p`.

In `data/arXiv-2206.15372v2.tex`, the choice of generator is denoted `exp(p)`, and the weight points
are written using `exp(p(k-2)) - 1`. The paper also notes that one may replace `exp(p)` by any other
topological generator `η ∈ 1 + pℤ_p`, without changing the Newton polygons.

For the purposes of Proposition 4.18, only the valuation identity
`v_p(w_{k₁}-w_{k₂}) = 1 + v_p(k₁-k₂)` (Eq. `\label{E:vp of k1-k2}`) is used; we realize it by fixing
the concrete generator `η := p + 1`.
-/
def weightGenerator : ℚ_[p] :=
  ((p + 1 : ℕ) : ℚ_[p])

/--
The paper’s symbol `exp(p)` as an element of `ℤ_p`.

In this project we fix `exp(p) := p + 1`.
-/
def expP : ℤ_[p] :=
  (p + 1 : ℤ_[p])

/--
The map `n ↦ exp(pn)` on integer arguments, expressed using the fixed generator `exp(p)`.

In the paper, the notation `exp(p(k-2))` is shorthand for `(exp(p))^(k-2)`. We package this as a
single function so that later lemmas can be stated in the same shape as the paper.
-/
def expMulP (n : ℤ) : ℚ_[p] :=
  ((expP (p := p) : ℤ_[p]) : ℚ_[p]) ^ n

/--
The chosen generator in `ℚ_p` is the coercion of `expP`.
-/
theorem weightGenerator_eq_coe_expP :
    weightGenerator (p := p) = ((expP (p := p) : ℤ_[p]) : ℚ_[p]) := by
  simp [weightGenerator, expP]

/--
Rewrite `expMulP` in terms of the concrete generator `p+1` in `ℚ_p`.
-/
theorem expMulP_eq_weightGenerator_zpow (n : ℤ) :
    expMulP (p := p) n = weightGenerator (p := p) ^ n := by
  simp [expMulP, weightGenerator, expP]

/--
The weight points `w_k` used throughout the paper.

In `data/arXiv-2206.15372v2.tex`, these are defined as `w_k := exp(p(k-2)) - 1`, where `exp(p)` is a
choice of topological generator of `1 + pℤ_p`. Writing `η := exp(p)`, this is equivalently
`w_k = η^(k-2) - 1`.

In this project we take the concrete generator `η := p + 1`, i.e. `η = weightGenerator p`.
-/
def padicWeight (k : ℤ) : ℚ_[p] :=
  expMulP (p := p) (k - 2) - 1

/--
Factorization of weight differences for `padicWeight`:

`w_{k₀} - w_k = η^(k-2) * (η^(k₀-k) - 1)`, where `η = weightGenerator p`.
-/
theorem padicWeight_sub (k0 k : ℤ) :
    padicWeight (p := p) k0 - padicWeight (p := p) k =
      expMulP (p := p) (k - 2) * (expMulP (p := p) (k0 - k) - 1) := by
  classical
  set a : ℚ_[p] := expMulP (p := p) 1
  have ha : a ≠ 0 := by
    simpa [a, expMulP, expP] using (show ((p + 1 : ℕ) : ℚ_[p]) ≠ 0 from by
      exact_mod_cast (Nat.succ_ne_zero p))
  have hexp : k0 - 2 = (k - 2) + (k0 - k) := by abel
  have hdiff :
      padicWeight (p := p) k0 - padicWeight (p := p) k = a ^ (k0 - 2) - a ^ (k - 2) := by
    simp [padicWeight, a, expMulP]
  -- Convert `a^(k₀-2) - a^(k-2)` to `a^(k-2) * (a^(k₀-k) - 1)`, then rewrite back to `expMulP`.
  rw [hdiff, hexp, zpow_add₀ ha, mul_sub, mul_one]
  simpa [a, expMulP, expP]

/--
The `p`-adic valuation of the natural number `(p+1)^n - 1` is `padicValNat p n + 1`,
for odd primes `p` and positive integers `n`.

This is the LTE (lifting-the-exponent) special case used in Eq. `\label{E:vp of k1-k2}`.
-/
theorem padicValNat_pAddOne_pow_sub_one (hpOdd : Odd p) (n : ℕ) (hn : n ≠ 0) :
    padicValNat p ((p + 1) ^ n - 1) = padicValNat p n + 1 := by
  have hyx : (1 : ℕ) < p + 1 := Nat.succ_lt_succ (Fact.out : Nat.Prime p).pos
  have hxy : p ∣ (p + 1) - 1 := by
    simp
  have hx : ¬p ∣ (p + 1) := by
    intro h
    have h1 : p ∣ 1 := (Nat.dvd_add_right (a := p) (b := p) (c := 1) (h := dvd_rfl)).1 h
    exact (Fact.out : Nat.Prime p).ne_one (Nat.dvd_one.mp h1)
  have h :=
    padicValNat.pow_sub_pow (p := p) (hp1 := hpOdd) (x := p + 1) (y := 1) (by simpa using hyx)
      (by simpa using hxy) hx hn
  -- Simplify `1^n = 1` and `(p+1) - 1 = p`.
  -- Then `padicValNat p p = 1` for primes.
  simpa [Nat.one_pow, Nat.succ_sub_one, padicValNat_self, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using h

/--
The additive `p`-adic valuation of `(p+1)^m` (with `m : ℤ`) is `0`.

This is used to discard the unit factor `(p+1)^(k-2)` in `w_{k₀}-w_k`.
-/
theorem addValuation_pAddOne_zpow (m : ℤ) :
    Padic.addValuation (p := p) (((p + 1 : ℕ) : ℚ_[p]) ^ m) = 0 := by
  set a : ℚ_[p] := ((p + 1 : ℕ) : ℚ_[p])
  have ha : a ≠ 0 := by
    simpa [a] using (show ((p + 1 : ℕ) : ℚ_[p]) ≠ 0 from by
      exact_mod_cast (Nat.succ_ne_zero p))
  have hx : a ^ m ≠ 0 := zpow_ne_zero m ha
  have hxv := Padic.addValuation.apply (p := p) (x := a ^ m) hx
  have hnot : ¬p ∣ p + 1 := by
    intro h
    have h1 : p ∣ 1 := (Nat.dvd_add_right (a := p) (b := p) (c := 1) (h := dvd_rfl)).1 h
    exact (Fact.out : Nat.Prime p).ne_one (Nat.dvd_one.mp h1)
  have haValNat : padicValNat p (p + 1) = 0 := padicValNat.eq_zero_of_not_dvd hnot
  have ha_val : a.valuation = 0 := by
    have : a.valuation = (padicValNat p (p + 1) : ℤ) := by
      simpa [a] using (Padic.valuation_natCast (p := p) (p + 1))
    simpa [haValNat] using this
  have hxval : (a ^ m).valuation = 0 := by
    simpa [ha_val] using (Padic.valuation_zpow (p := p) (x := a) m)
  simpa [hxval] using hxv

/--
The valuation identity `v_p((p+1)^n - 1) = v_p(n) + 1`, expressed via `Padic.addValuation`.

This is the concrete version of the second part of Eq. `\label{E:vp of k1-k2}`.
-/
theorem addValuation_pAddOne_pow_sub_one (hpOdd : Odd p) (n : ℕ) (hn : n ≠ 0) :
    Padic.addValuation (p := p) (((p + 1 : ℕ) : ℚ_[p]) ^ n - 1) =
      (padicValNat p n + 1 : WithTop ℤ) := by
  classical
  set a : ℚ_[p] := ((p + 1 : ℕ) : ℚ_[p])
  set N : ℕ := (p + 1) ^ n - 1
  have hnz : N ≠ 0 := by
    have h1 : 1 < p + 1 := Nat.succ_lt_succ (Fact.out : Nat.Prime p).pos
    have hpow : 1 < (p + 1) ^ n := Nat.one_lt_pow hn h1
    exact Nat.sub_ne_zero_of_lt hpow
  have hx0 : (↑N : ℚ_[p]) ≠ 0 := by
    exact_mod_cast hnz
  have hcast : (a ^ n - 1) = (↑N : ℚ_[p]) := by
    have hle : (1 : ℕ) ≤ (p + 1) ^ n := Nat.one_le_pow n (p + 1) (Nat.succ_pos p)
    -- `Nat.cast_sub` gives `↑((p+1)^n - 1) = ↑((p+1)^n) - 1`; we use it in reverse.
    simpa [a, N, Nat.cast_pow] using
      (Nat.cast_sub (R := ℚ_[p]) (m := 1) (n := (p + 1) ^ n) hle).symm
  have hxv := Padic.addValuation.apply (p := p) (x := (↑N : ℚ_[p])) hx0
  have hval : (↑N : ℚ_[p]).valuation = (padicValNat p N : ℤ) := by
    simpa [N] using (Padic.valuation_natCast (p := p) N)
  have hxNat : Padic.addValuation (p := p) (↑N : ℚ_[p]) = (padicValNat p N : WithTop ℤ) := by
    simpa [hval] using hxv
  have hLTE : padicValNat p N = padicValNat p n + 1 := by
    simpa [N] using padicValNat_pAddOne_pow_sub_one (p := p) hpOdd n hn
  have hxNat' :
      Padic.addValuation (p := p) (↑N : ℚ_[p]) = (padicValNat p n + 1 : WithTop ℤ) := by
    simpa [hLTE] using hxNat
  simpa [hcast] using hxNat'

/--
The valuation identity `v_p((p+1)^m - 1) = v_p(m) + 1` for integer exponents `m ≠ 0`,
expressed via `Padic.addValuation`.
-/
theorem addValuation_pAddOne_zpow_sub_one (hpOdd : Odd p) (m : ℤ) (hm : m ≠ 0) :
    Padic.addValuation (p := p) (((p + 1 : ℕ) : ℚ_[p]) ^ m - 1) =
      (padicValInt p m + 1 : WithTop ℤ) := by
  classical
  set a : ℚ_[p] := ((p + 1 : ℕ) : ℚ_[p])
  cases m with
  | ofNat n =>
    have hn : n ≠ 0 := by
      simpa using hm
    have hz : a ^ (Int.ofNat n) = a ^ n := by
      simpa using (zpow_ofNat a n)
    simpa [a, hz, padicValInt.of_nat] using addValuation_pAddOne_pow_sub_one (p := p) hpOdd n hn
  | negSucc n =>
    have ha : a ≠ 0 := by
      simpa [a] using (show ((p + 1 : ℕ) : ℚ_[p]) ≠ 0 from by
        exact_mod_cast (Nat.succ_ne_zero p))
    have haPow : a ^ (n + 1) ≠ 0 := pow_ne_zero (n + 1) ha
    have hrewrite :
        a ^ (Int.negSucc n) - 1 = -(a ^ (n + 1) - 1) * (a ^ (n + 1))⁻¹ := by
      simp [zpow_negSucc, sub_eq_add_neg, haPow, mul_add, mul_comm]
    have hunit : Padic.addValuation (p := p) (a ^ (n + 1 : ℕ)) = 0 := by
      have hz : a ^ (Int.ofNat (n + 1)) = a ^ (n + 1) := by
        simpa using (zpow_ofNat a (n + 1))
      have hzv :
          Padic.addValuation (p := p) (a ^ (Int.ofNat (n + 1))) =
            Padic.addValuation (p := p) (a ^ (n + 1)) :=
        congrArg (fun x => Padic.addValuation (p := p) x) hz
      have h0 : Padic.addValuation (p := p) (a ^ (Int.ofNat (n + 1))) = 0 := by
        simpa [a] using addValuation_pAddOne_zpow (p := p) (m := Int.ofNat (n + 1))
      -- Transport `h0` along `hzv`.
      calc
        Padic.addValuation (p := p) (a ^ (n + 1)) =
            Padic.addValuation (p := p) (a ^ (Int.ofNat (n + 1))) := hzv.symm
        _ = 0 := h0
    have hpos :
        Padic.addValuation (p := p) (a ^ (n + 1) - 1) =
          (padicValNat p (n + 1) + 1 : WithTop ℤ) := by
      exact addValuation_pAddOne_pow_sub_one (p := p) hpOdd (n + 1) (Nat.succ_ne_zero n)
    calc
      Padic.addValuation (p := p) (a ^ (Int.negSucc n) - 1) =
          Padic.addValuation (p := p) (-(a ^ (n + 1) - 1) * (a ^ (n + 1))⁻¹) := by
            rw [hrewrite]
      _ = Padic.addValuation (p := p) (-(a ^ (n + 1) - 1)) +
            Padic.addValuation (p := p) ((a ^ (n + 1))⁻¹) := by
            simpa using
              (AddValuation.map_mul (Padic.addValuation (p := p)) (-(a ^ (n + 1) - 1))
                ((a ^ (n + 1))⁻¹))
      _ = Padic.addValuation (p := p) (a ^ (n + 1) - 1) +
            Padic.addValuation (p := p) ((a ^ (n + 1))⁻¹) := by
            rw [AddValuation.map_neg]
      _ = Padic.addValuation (p := p) (a ^ (n + 1) - 1) +
            -Padic.addValuation (p := p) (a ^ (n + 1 : ℕ)) := by
            have hinv :
                Padic.addValuation (p := p) ((a ^ (n + 1))⁻¹) =
                  -Padic.addValuation (p := p) (a ^ (n + 1)) := by
              simpa using
                (AddValuation.map_inv (v := Padic.addValuation (p := p)) (x := a ^ (n + 1)))
            -- Rewrite the inverse valuation and keep the natural-power term explicit.
            rw [hinv]
      _ = Padic.addValuation (p := p) (a ^ (n + 1) - 1) := by
            rw [hunit]
            simp
      _ = (padicValNat p (n + 1) + 1 : WithTop ℤ) := hpos

/--
The valuation identity for `padicWeight`:

`v_p(w_{k₀}-w_k) = v_p(k₀-k) + 1`,

written using `Padic.addValuation` on `ℚ_[p]` and `padicValInt` on integers.
-/
theorem addValuation_padicWeight_sub (hpOdd : Odd p) (k0 k : ℤ) (hk : k ≠ k0) :
    Padic.addValuation (p := p) (padicWeight (p := p) k0 - padicWeight (p := p) k) =
      (padicValInt p (k0 - k) + 1 : WithTop ℤ) := by
  have hm : k0 - k ≠ 0 := sub_ne_zero.mpr hk.symm
  rw [padicWeight_sub (p := p) k0 k]
  calc
    Padic.addValuation (p := p)
        (expMulP (p := p) (k - 2) * (expMulP (p := p) (k0 - k) - 1)) =
        Padic.addValuation (p := p) (expMulP (p := p) (k - 2)) +
          Padic.addValuation (p := p) (expMulP (p := p) (k0 - k) - 1) := by
        simpa using
          (AddValuation.map_mul (Padic.addValuation (p := p)) (expMulP (p := p) (k - 2))
            (expMulP (p := p) (k0 - k) - 1))
    _ = Padic.addValuation (p := p) (expMulP (p := p) (k0 - k) - 1) := by
        have hunit :
            Padic.addValuation (p := p) (expMulP (p := p) (k - 2)) = 0 := by
          simpa [expMulP, expP] using addValuation_pAddOne_zpow (p := p) (m := k - 2)
        rw [hunit]
        simp
    _ = (padicValInt p (k0 - k) + 1 : WithTop ℤ) := by
        simpa [expMulP, expP] using addValuation_pAddOne_zpow_sub_one (p := p) hpOdd (k0 - k) hm

/--
Specialize the valuation normal form `ghostCoeffHat_eval_val` to `padicWeight` and
`Padic.addValuation`.

This turns the valuation of a hatted ghost coefficient at `w_{k₀}` into an explicit sum of
`padicValInt p (k₀-k) + 1` terms.
-/
theorem ghostCoeffHat_eval_val_padicWeight (hpOdd : Odd p) (m : ℤ → ℕ) (K : Finset ℤ) (k0 : ℤ) :
    Padic.addValuation (p := p)
        ((ghostCoeffHat (R := ℚ_[p]) (padicWeight (p := p)) m K k0).eval
          (padicWeight (p := p) k0)) =
      ∑ k ∈ K.erase k0, (m k) • (padicValInt p (k0 - k) + 1 : WithTop ℤ) := by
  classical
  have h :=
    ghostCoeffHat_eval_val (R := ℚ_[p]) (Γ₀ := WithTop ℤ) (v := Padic.addValuation (p := p))
      (w := padicWeight (p := p)) (m := m) (K := K) (k0 := k0)
  refine h.trans ?_
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hkne : k ≠ k0 := (Finset.mem_erase.mp hk).1
  simpa [addValuation_padicWeight_sub (p := p) (hpOdd := hpOdd) (k0 := k0) (k := k) hkne]

/--
First-order valuation increment for hatted ghost coefficients, specialized to `padicWeight` and
`Padic.addValuation`.

This is the `padicValInt`-level version of
`ghostCoeffHat_eval_val_succ_add_sum_incNeg_eq_add_sum_incPos`.
-/
theorem ghostCoeffHat_eval_val_succ_add_sum_incNeg_eq_add_sum_incPos_padicWeight (hpOdd : Odd p)
    (a sε : ℕ) (hs : sε < pMinusOne p) (K : Finset ℤ) (k0 : ℤ) (n : ℕ) :
    Padic.addValuation (p := p)
          ((ghostCoeffHat (R := ℚ_[p]) (padicWeight (p := p))
                (fun k => ghostMultiplicityNat p a sε k (n + 1)) K k0).eval
            (padicWeight (p := p) k0)) +
        (∑ k ∈ K.erase k0 with ghostMultiplicityIncNeg (p := p) a sε k n,
          (padicValInt p (k0 - k) + 1 : WithTop ℤ)) =
      Padic.addValuation (p := p)
          ((ghostCoeffHat (R := ℚ_[p]) (padicWeight (p := p))
                (fun k => ghostMultiplicityNat p a sε k n) K k0).eval
            (padicWeight (p := p) k0)) +
        (∑ k ∈ K.erase k0 with ghostMultiplicityIncPos (p := p) a sε k n,
          (padicValInt p (k0 - k) + 1 : WithTop ℤ)) := by
  classical
  have h :=
    ghostCoeffHat_eval_val_succ_add_sum_incNeg_eq_add_sum_incPos (p := p) (R := ℚ_[p])
      (Γ₀ := WithTop ℤ) (v := Padic.addValuation (p := p)) (w := padicWeight (p := p)) (a := a)
      (sε := sε) hs (K := K) (k0 := k0) (n := n)
  have hNeg :
      (∑ k ∈ K.erase k0 with ghostMultiplicityIncNeg (p := p) a sε k n,
          Padic.addValuation (p := p) (padicWeight (p := p) k0 - padicWeight (p := p) k)) =
        ∑ k ∈ K.erase k0 with ghostMultiplicityIncNeg (p := p) a sε k n,
          (padicValInt p (k0 - k) + 1 : WithTop ℤ) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hkne : k ≠ k0 := (Finset.mem_erase.mp (Finset.mem_filter.mp hk).1).1
    simpa [addValuation_padicWeight_sub (p := p) (hpOdd := hpOdd) (k0 := k0) (k := k) hkne]
  have hPos :
      (∑ k ∈ K.erase k0 with ghostMultiplicityIncPos (p := p) a sε k n,
          Padic.addValuation (p := p) (padicWeight (p := p) k0 - padicWeight (p := p) k)) =
        ∑ k ∈ K.erase k0 with ghostMultiplicityIncPos (p := p) a sε k n,
          (padicValInt p (k0 - k) + 1 : WithTop ℤ) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hkne : k ≠ k0 := (Finset.mem_erase.mp (Finset.mem_filter.mp hk).1).1
    simpa [addValuation_padicWeight_sub (p := p) (hpOdd := hpOdd) (k0 := k0) (k := k) hkne]
  simpa [hNeg, hPos] using h

/--
Second-order valuation increment for hatted ghost coefficients, specialized to `padicWeight` and
`Padic.addValuation`.

This is the `padicValInt`-level version of
`ghostCoeffHat_eval_val_secondOrder_add_sums_eq_two_nsmul_add_sums`.
-/
theorem ghostCoeffHat_eval_val_secondOrder_add_sums_eq_two_nsmul_add_sums_padicWeight (hpOdd : Odd p)
    (a sε : ℕ) (hs : sε < pMinusOne p) (K : Finset ℤ) (k0 : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    Padic.addValuation (p := p)
          ((ghostCoeffHat (R := ℚ_[p]) (padicWeight (p := p))
                (fun k => ghostMultiplicityNat p a sε k (n + 1)) K k0).eval
            (padicWeight (p := p) k0)) +
        Padic.addValuation (p := p)
          ((ghostCoeffHat (R := ℚ_[p]) (padicWeight (p := p))
                (fun k => ghostMultiplicityNat p a sε k (n - 1)) K k0).eval
            (padicWeight (p := p) k0)) +
        (∑ k ∈ K.erase k0 with ghostMultiplicityIncNeg (p := p) a sε k n,
          (padicValInt p (k0 - k) + 1 : WithTop ℤ)) +
        (∑ k ∈ K.erase k0 with ghostMultiplicityIncPos (p := p) a sε k (n - 1),
          (padicValInt p (k0 - k) + 1 : WithTop ℤ)) =
      2 •
          Padic.addValuation (p := p)
            ((ghostCoeffHat (R := ℚ_[p]) (padicWeight (p := p))
                  (fun k => ghostMultiplicityNat p a sε k n) K k0).eval
              (padicWeight (p := p) k0)) +
        (∑ k ∈ K.erase k0 with ghostMultiplicityIncPos (p := p) a sε k n,
          (padicValInt p (k0 - k) + 1 : WithTop ℤ)) +
        (∑ k ∈ K.erase k0 with ghostMultiplicityIncNeg (p := p) a sε k (n - 1),
          (padicValInt p (k0 - k) + 1 : WithTop ℤ)) := by
  classical
  have h :=
    ghostCoeffHat_eval_val_secondOrder_add_sums_eq_two_nsmul_add_sums (p := p) (R := ℚ_[p])
      (Γ₀ := WithTop ℤ) (v := Padic.addValuation (p := p)) (w := padicWeight (p := p)) (a := a)
      (sε := sε) hs (K := K) (k0 := k0) (n := n) hn
  have hFilter (P : ℤ → Prop) [DecidablePred P] :
      (∑ k ∈ K.erase k0 with P k,
          Padic.addValuation (p := p) (padicWeight (p := p) k0 - padicWeight (p := p) k)) =
        ∑ k ∈ K.erase k0 with P k, (padicValInt p (k0 - k) + 1 : WithTop ℤ) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hkne : k ≠ k0 := (Finset.mem_erase.mp (Finset.mem_filter.mp hk).1).1
    simpa [addValuation_padicWeight_sub (p := p) (hpOdd := hpOdd) (k0 := k0) (k := k) hkne]
  have hNeg_n :
      (∑ k ∈ K.erase k0 with ghostMultiplicityIncNeg (p := p) a sε k n,
            Padic.addValuation (p := p) (padicWeight (p := p) k0 - padicWeight (p := p) k)) =
        ∑ k ∈ K.erase k0 with ghostMultiplicityIncNeg (p := p) a sε k n,
          (padicValInt p (k0 - k) + 1 : WithTop ℤ) :=
    hFilter (P := fun k => ghostMultiplicityIncNeg (p := p) a sε k n)
  have hPos_n :
      (∑ k ∈ K.erase k0 with ghostMultiplicityIncPos (p := p) a sε k n,
            Padic.addValuation (p := p) (padicWeight (p := p) k0 - padicWeight (p := p) k)) =
        ∑ k ∈ K.erase k0 with ghostMultiplicityIncPos (p := p) a sε k n,
          (padicValInt p (k0 - k) + 1 : WithTop ℤ) :=
    hFilter (P := fun k => ghostMultiplicityIncPos (p := p) a sε k n)
  have hNeg_pred :
      (∑ k ∈ K.erase k0 with ghostMultiplicityIncNeg (p := p) a sε k (n - 1),
            Padic.addValuation (p := p) (padicWeight (p := p) k0 - padicWeight (p := p) k)) =
        ∑ k ∈ K.erase k0 with ghostMultiplicityIncNeg (p := p) a sε k (n - 1),
          (padicValInt p (k0 - k) + 1 : WithTop ℤ) :=
    hFilter (P := fun k => ghostMultiplicityIncNeg (p := p) a sε k (n - 1))
  have hPos_pred :
      (∑ k ∈ K.erase k0 with ghostMultiplicityIncPos (p := p) a sε k (n - 1),
            Padic.addValuation (p := p) (padicWeight (p := p) k0 - padicWeight (p := p) k)) =
        ∑ k ∈ K.erase k0 with ghostMultiplicityIncPos (p := p) a sε k (n - 1),
          (padicValInt p (k0 - k) + 1 : WithTop ℤ) :=
    hFilter (P := fun k => ghostMultiplicityIncPos (p := p) a sε k (n - 1))
  simpa [hNeg_n, hPos_n, hNeg_pred, hPos_pred] using h

end

end Formulation

end GhostConjecture
