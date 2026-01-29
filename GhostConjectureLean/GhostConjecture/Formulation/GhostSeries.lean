import GhostConjecture.Formulation.ExtremalKs
import GhostConjecture.Formulation.GhostCoefficients
import GhostConjecture.Formulation.GhostMultiplicityNat
import Mathlib.RingTheory.PowerSeries.Basic

namespace GhostConjecture

namespace Formulation

open scoped BigOperators
open scoped Polynomial

noncomputable section

variable {R : Type*} [CommRing R]

variable (p : ℕ) [Fact (Nat.Prime p)]

/--
The finite support set of ghost indices used to define the `n`-th ghost coefficient.

This is the interval `[k_{min,•}(n), k_{max,•}(n)]` from Lemma-Notation `L:extremal ks` in
`data/arXiv-2206.15372v2.tex`. It packages the fact that only finitely many ghost multiplicities
are nonzero for a fixed `n`.
-/
def ghostSupport (a sε : ℕ) (n : ℕ) : Finset ℤ :=
  Finset.Icc (kMinBullet p a sε n) (kMaxBullet p a sε n)

/--
The `n`-th ghost coefficient polynomial `g_n(w)` as a finite product over `ghostSupport`.

This is the finite-product version of Definition 2.25 (ghost series coefficients), with
multiplicity function `k ↦ m_n(k)` given by `ghostMultiplicityNat`.
-/
def ghostCoeffPoly (w : ℤ → R) (a sε : ℕ) (n : ℕ) : R[X] :=
  ghostCoeff (R := R) w (fun k => ghostMultiplicityNat p a sε k n) (ghostSupport p a sε n)

/--
The hatted ghost coefficient polynomial `g_{n,\\hat k₀}(w)` for the coefficient `g_n(w)`.

This removes the `k₀`-factor from the finite product defining `ghostCoeffPoly`, matching
Notation 4.17 (`\label{N:gnhatk}`).
-/
def ghostCoeffHatPoly (w : ℤ → R) (a sε : ℕ) (n : ℕ) (k0 : ℤ) : R[X] :=
  ghostCoeffHat (R := R) w (fun k => ghostMultiplicityNat p a sε k n) (ghostSupport p a sε n) k0

/--
The ghost series `G(w,t) = ∑_{n≥0} g_n(w) t^n` as a power series in `t` with coefficients in
polynomials in `w`.

This packages the family `ghostCoeffPoly` into a single `PowerSeries (R[X])`.
-/
def ghostSeries (w : ℤ → R) (a sε : ℕ) : PowerSeries R[X] :=
  PowerSeries.mk fun n => ghostCoeffPoly (R := R) (p := p) w a sε n

/--
Evaluate the ghost series at a value `w0 : R`, producing a power series in `t` with coefficients in
`R`.

This is the coefficientwise evaluation map `R[X] → R` applied to `ghostSeries`.
-/
def ghostSeriesEval (w : ℤ → R) (a sε : ℕ) (w0 : R) : PowerSeries R :=
  (PowerSeries.map (Polynomial.eval₂RingHom (RingHom.id R) w0))
    (ghostSeries (R := R) (p := p) w a sε)

omit [Fact (Nat.Prime p)] in
/--
The coefficient formula for `ghostSeriesEval`: the `n`-th coefficient is obtained by evaluating
`ghostCoeffPoly` at `w0`.
-/
theorem coeff_ghostSeriesEval (w : ℤ → R) (a sε : ℕ) (w0 : R) (n : ℕ) :
    (PowerSeries.coeff n) (ghostSeriesEval (R := R) (p := p) w a sε w0) =
      (ghostCoeffPoly (R := R) (p := p) w a sε n).eval w0 := by
  simp [ghostSeriesEval, ghostSeries, ghostCoeffPoly]

end

end Formulation

end GhostConjecture
