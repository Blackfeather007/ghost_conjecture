import GhostConjecture.Formulation.GhostCoefficients
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Valuation.Basic

namespace GhostConjecture

namespace Formulation

open scoped BigOperators
open scoped Polynomial

noncomputable section

variable {R : Type*} [CommRing R]
variable {Γ₀ : Type*} [LinearOrderedAddCommMonoidWithTop Γ₀]

/--
Evaluation of the “hatted ghost coefficient” at a weight point.

This is the concrete content of Notation 4.17 (`\label{N:gnhatk}`): once the `k₀`-factor is removed,
evaluating at `w_{k₀}` gives a finite product of `(w_{k₀}-w_k)^{m(k)}` over the remaining weights.

This lemma is a starting point for Proposition 4.18 (`\label{P:ghost compatible with theta AL and p-stabilization}`),
where valuations of these expressions are compared.
-/
theorem ghostCoeffHat_eval (w : ℤ → R) (m : ℤ → ℕ) (K : Finset ℤ) (k0 : ℤ) :
    (ghostCoeffHat (R := R) w m K k0).eval (w k0) =
      ∏ k ∈ K.erase k0, (w k0 - w k) ^ (m k) := by
  classical
  -- Unfold the ghost polynomial and keep evaluation as a ring hom.
  simp [ghostCoeffHat, ghostFactor, ghostLinear]
  let φ : R[X] →+* R := Polynomial.eval₂RingHom (RingHom.id R) (w k0)
  change φ (∏ x ∈ K.erase k0, (Polynomial.X - Polynomial.C (w x)) ^ m x) = _
  have hmap :=
    map_prod (g := φ) (f := fun x : ℤ => (Polynomial.X - Polynomial.C (w x)) ^ m x) (s := K.erase k0)
  simpa [φ] using hmap

/--
Evaluation of the “multi-hatted” ghost coefficient at a weight point.

This is the version of `ghostCoeffHat_eval` for `g_{n,\\hat{\\bfk}}` (Notation 4.17), where we
remove an arbitrary finite set of ghost zeros.
-/
theorem ghostCoeffHatSet_eval (w : ℤ → R) (m : ℤ → ℕ) (K Krm : Finset ℤ) (k0 : ℤ) :
    (ghostCoeffHatSet (R := R) w m K Krm).eval (w k0) =
      ∏ k ∈ K \ Krm, (w k0 - w k) ^ (m k) := by
  classical
  simp [ghostCoeffHatSet, ghostFactor, ghostLinear]
  let φ : R[X] →+* R := Polynomial.eval₂RingHom (RingHom.id R) (w k0)
  change φ (∏ x ∈ K \ Krm, (Polynomial.X - Polynomial.C (w x)) ^ m x) = _
  have hmap :=
    map_prod (g := φ) (f := fun x : ℤ => (Polynomial.X - Polynomial.C (w x)) ^ m x) (s := K \ Krm)
  simpa [φ] using hmap

/--
For an additive valuation, the valuation of a finite product is the sum of the valuations.

This is the basic tool for converting ghost coefficients (defined as products) into sums of
`v_p(w_{k₀}-w_k)`-terms as in the proof of Proposition 4.18.
-/
theorem addValuation_map_prod (v : AddValuation R Γ₀) {ι : Type*} (s : Finset ι) (f : ι → R) :
    v (∏ x ∈ s, f x) = ∑ x ∈ s, v (f x) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [v.map_one]
  · intro a s ha hs
    simp [Finset.prod_insert, Finset.sum_insert, ha, v.map_mul, hs]

/--
Valuation of `g_{n,\\hat k₀}(w_{k₀})` as a finite sum.

This is the valuation-level version of `ghostCoeffHat_eval`, and is a convenient “normal form”
for the combinatorial manipulations in Proposition 4.18.
-/
theorem ghostCoeffHat_eval_val (v : AddValuation R Γ₀) (w : ℤ → R) (m : ℤ → ℕ) (K : Finset ℤ)
    (k0 : ℤ) :
    v ((ghostCoeffHat (R := R) w m K k0).eval (w k0)) =
      ∑ k ∈ K.erase k0, (m k) • v (w k0 - w k) := by
  classical
  have heval := ghostCoeffHat_eval (R := R) (w := w) (m := m) (K := K) (k0 := k0)
  -- Rewrite using the product form, then turn products into sums using `v.map_mul` / `v.map_pow`.
  simp [heval, addValuation_map_prod (v := v), v.map_pow]

/--
Valuation of `g_{n,\\hat{\\bfk}}(w_{k₀})` as a finite sum.

This is the `Finset`-valued analogue of `ghostCoeffHat_eval_val`.
-/
theorem ghostCoeffHatSet_eval_val (v : AddValuation R Γ₀) (w : ℤ → R) (m : ℤ → ℕ) (K Krm : Finset ℤ)
    (k0 : ℤ) :
    v ((ghostCoeffHatSet (R := R) w m K Krm).eval (w k0)) =
      ∑ k ∈ K \ Krm, (m k) • v (w k0 - w k) := by
  classical
  have heval := ghostCoeffHatSet_eval (R := R) (w := w) (m := m) (K := K) (Krm := Krm) (k0 := k0)
  simp [heval, addValuation_map_prod (v := v), v.map_pow]

end

end Formulation

end GhostConjecture
