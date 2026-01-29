import Mathlib.Analysis.Convex.Hull
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Valuation.Basic

namespace GhostConjecture

open scoped Pointwise
open scoped PowerSeries

namespace Preparations

/-- The ambient type for Newton polygon points: pairs of real coordinates. -/
abbrev NewtonPoint : Type := ℝ × ℝ

/--
The set of points `(n, v(coeff n F))` used to define the Newton polygon of a power series.

We exclude indices `n` for which the coefficient vanishes, since an additive valuation takes the
value `⊤` on `0`.
-/
def newtonPoints {K : Type*} [Ring K] (v : AddValuation K (WithTop ℤ)) (F : K⟦X⟧) :
    Set NewtonPoint :=
  { p | ∃ n : ℕ, ∃ h : v (F.coeff n) ≠ ⊤,
      p = ((n : ℝ), ((WithTop.untop (v (F.coeff n)) h : ℤ) : ℝ)) }

/--
The Newton polygon of a power series, defined as the convex hull of the points `(n, v(coeff n F))`
(excluding zero coefficients).

This matches Notation `\NP(F)` in `data/arXiv-2206.15372v2.tex` (see Notation 2.1 and
`\label{N:Newton polygon}`), and the "Preparations" section of `instruction/instruction.tex`.
-/
def newtonPolygon {K : Type*} [Ring K] (v : AddValuation K (WithTop ℤ)) (F : K⟦X⟧) :
    Set NewtonPoint :=
  convexHull ℝ (newtonPoints v F)

/--
Lower bound on valuations of coefficients in a product.

This is the basic estimate behind the usual statement that Newton polygons behave well under
multiplication (cf. `instruction/instruction.tex` §1).  The full Minkowski-sum statement is about
the *lower convex hull* of the points, while the present file only records the coefficient-wise
valuation inequality needed in later combinatorial arguments.
-/
theorem coeff_mul_val_ge_inf_antidiagonal {K : Type*} [CommRing K] (v : AddValuation K (WithTop ℤ))
    (F G : K⟦X⟧) (n : ℕ) :
    (Finset.inf' (Finset.antidiagonal n)
          (by
            classical
            -- `antidiagonal n` is nonempty (e.g. `(0,n)` lies in it).
            exact ⟨(0, n), by simp⟩)
          (fun p => v (F.coeff p.1 * G.coeff p.2))) ≤ v ((F * G).coeff n) := by
  classical
  -- Let `g` be the minimum valuation of the terms on the antidiagonal.
  set g :=
    Finset.inf' (Finset.antidiagonal n) (by exact ⟨(0, n), by simp⟩)
      (fun p => v (F.coeff p.1 * G.coeff p.2)) with hg
  have hg_le :
      ∀ p ∈ Finset.antidiagonal n, g ≤ v (F.coeff p.1 * G.coeff p.2) := by
    intro p hp
    -- `g` is the infimum over the finite antidiagonal.
    simpa [hg] using (Finset.inf'_le (s := Finset.antidiagonal n)
      (f := fun p => v (F.coeff p.1 * G.coeff p.2)) hp)
  -- Apply the valuation estimate on finite sums.
  have :
      g ≤ v (∑ p ∈ Finset.antidiagonal n, F.coeff p.1 * G.coeff p.2) :=
    v.map_le_sum hg_le
  -- Rewrite the sum as the coefficient of the product.
  simpa [PowerSeries.coeff_mul, hg] using this

end Preparations

end GhostConjecture
