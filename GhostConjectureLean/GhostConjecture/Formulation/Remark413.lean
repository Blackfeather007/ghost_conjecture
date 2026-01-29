import GhostConjecture.Formulation.UnramifiedDimensions

namespace GhostConjecture

namespace Formulation

variable (p : ℕ) [Fact (Nat.Prime p)]

/--
The Iwasawa dimension formula scaled by a "multiplicity" parameter.

This records the content of Remark 4.13(1) in `data/arXiv-2206.15372v2.tex` in the simplified
setup of this project: if a non-primitive object has multiplicity `m`, then the corresponding
Iwasawa ranks/dimensions scale by the factor `m`.
-/
def dIwWithMultiplicity (m : ℕ) (a sε : ℕ) (k : ℤ) : ℤ :=
  (m : ℤ) * dIw p a sε k

/--
The unramified dimension formula scaled by a "multiplicity" parameter.

This is the unramified analogue of `dIwWithMultiplicity`, matching the second equality in
Remark 4.13(1) of `data/arXiv-2206.15372v2.tex`.
-/
def dUnrWithMultiplicity (m : ℕ) (a sε : ℕ) (kBullet : ℤ) : ℤ :=
  (m : ℤ) * dUnr p a sε kBullet

/--
Unfold `dIwWithMultiplicity`.
-/
theorem dIwWithMultiplicity_eq (m a sε : ℕ) (k : ℤ) :
    dIwWithMultiplicity (p := p) m a sε k = (m : ℤ) * dIw p a sε k := by
  rfl

/--
Unfold `dUnrWithMultiplicity`.
-/
theorem dUnrWithMultiplicity_eq (m a sε : ℕ) (kBullet : ℤ) :
    dUnrWithMultiplicity (p := p) m a sε kBullet = (m : ℤ) * dUnr p a sε kBullet := by
  rfl

end Formulation

end GhostConjecture
