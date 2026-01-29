import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Basic

namespace GhostConjecture

namespace Formulation

open scoped BigOperators
open scoped Polynomial

noncomputable section

variable {R : Type*} [CommRing R]

/--
The linear factor `(w - w_k)` that appears in the definition of ghost coefficients, viewed as a
polynomial in the variable `w`.

This is the basic building block for Notation `N:gnhatk` (Notation 4.17) in
`data/arXiv-2206.15372v2.tex`.
-/
def ghostLinear (w : ℤ → R) (k : ℤ) : R[X] :=
  Polynomial.X - Polynomial.C (w k)

/--
The ghost factor `(w - w_k)^{m(k)}` for a given multiplicity function `m : ℤ → ℕ`.
-/
def ghostFactor (w : ℤ → R) (m : ℤ → ℕ) (k : ℤ) : R[X] :=
  ghostLinear (R := R) w k ^ (m k)

/--
The ghost coefficient polynomial obtained as a finite product of ghost factors over a finite set of
weights.

This packages the product form `g_n(w) = ∏_k (w-w_k)^{m_n(k)}` from Definition 2.25, but with the
finite support set supplied explicitly as a `Finset`.
-/
def ghostCoeff (w : ℤ → R) (m : ℤ → ℕ) (K : Finset ℤ) : R[X] :=
  ∏ k ∈ K, ghostFactor (R := R) w m k

/--
The coefficient with the `k`-factor removed, written `g_{n,\\hat k}(w)` in Notation `N:gnhatk`
(Notation 4.17).

In the paper this is defined as a quotient by `(w-w_k)^{m_n(k)}`; here we implement it directly by
omitting the `k`-term from the finite product.
-/
def ghostCoeffHat (w : ℤ → R) (m : ℤ → ℕ) (K : Finset ℤ) (k : ℤ) : R[X] :=
  ∏ j ∈ K.erase k, ghostFactor (R := R) w m j

/--
The coefficient with all factors at weights in `Krm` removed, written `g_{n,\\hat{\\bfk}}(w)` in
Notation `N:gnhatk` (Notation 4.17).

This is the finite-product implementation of dividing by
`∏_{k∈Krm} (w-w_k)^{m_n(k)}`.
-/
def ghostCoeffHatSet (w : ℤ → R) (m : ℤ → ℕ) (K Krm : Finset ℤ) : R[X] :=
  ∏ j ∈ K \ Krm, ghostFactor (R := R) w m j

/--
Reinsert the removed factor: `g_{n,\\hat k}(w) * (w-w_k)^{m(k)} = g_n(w)` for finite products.
-/
theorem ghostCoeffHat_mul_factor (w : ℤ → R) (m : ℤ → ℕ) (K : Finset ℤ) (k : ℤ) (hk : k ∈ K) :
    ghostCoeffHat (R := R) w m K k * ghostFactor (R := R) w m k =
      ghostCoeff (R := R) w m K := by
  classical
  simpa [ghostCoeff, ghostCoeffHat] using (Finset.prod_erase_mul K (ghostFactor (R := R) w m) hk)

/--
Removing a singleton set of factors agrees with the single-`k` hat construction.
-/
theorem ghostCoeffHatSet_singleton (w : ℤ → R) (m : ℤ → ℕ) (K : Finset ℤ) (k : ℤ) :
    ghostCoeffHatSet (R := R) w m K {k} = ghostCoeffHat (R := R) w m K k := by
  classical
  simp [ghostCoeffHatSet, ghostCoeffHat, Finset.sdiff_singleton_eq_erase]

/--
Reinsert a whole family of removed factors: if `Krm ⊆ K` then
`g_{n,\\hat{\\bfk}}(w) * ∏_{k∈Krm} (w-w_k)^{m(k)} = g_n(w)`.
-/
theorem ghostCoeffHatSet_mul_removed (w : ℤ → R) (m : ℤ → ℕ) (K Krm : Finset ℤ) (hK : Krm ⊆ K) :
    ghostCoeffHatSet (R := R) w m K Krm * ghostCoeff (R := R) w m Krm =
      ghostCoeff (R := R) w m K := by
  classical
  -- `Finset.prod_sdiff` is exactly the multiplicative statement for products over `K \ Krm` and `Krm`.
  simpa [ghostCoeffHatSet, ghostCoeff] using
    (Finset.prod_sdiff (s₁ := Krm) (s₂ := K) (f := ghostFactor (R := R) w m) hK)

end

end Formulation

end GhostConjecture
