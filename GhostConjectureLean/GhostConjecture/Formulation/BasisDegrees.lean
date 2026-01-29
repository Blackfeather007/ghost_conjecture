import GhostConjecture.Formulation.UnramifiedDimensions

namespace GhostConjecture

namespace Formulation

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- The integer `(p+1)/2` used in Notation `N:tnvarepsilon` (Notation 4.10 in the paper). -/
def halfPPlusOne : ℤ :=
  (p + 1 : ℤ) / 2

/-- The parity-even value `β_even^{(ε)} = t₁^{(ε)}` from Notation `N:tnvarepsilon`. -/
def betaEven (a sε : ℕ) : ℤ :=
  tOne p a sε

/-- The parity-odd value `β_odd^{(ε)} = t₂^{(ε)} - (p+1)/2` from Notation `N:tnvarepsilon`. -/
def betaOdd (a sε : ℕ) : ℤ :=
  (tTwo p a sε : ℤ) - halfPPlusOne p

/--
The auxiliary value `β_{[n]}^{(ε)}` from Notation `N:tnvarepsilon`.

This depends only on the parity of `n`.
-/
def betaBracket (a sε : ℕ) (n : ℤ) : ℤ :=
  if Even n then betaEven p a sε else betaOdd p a sε

/--
The smaller of the two residues appearing in the degrees of the power basis `\bfB^{(ε)}`
from Notation `N:power basis`.
-/
def bfeResidueMin (a sε : ℕ) : ℕ :=
  Nat.min sε ((a + sε) % pMinusOne p)

/--
The larger of the two residues appearing in the degrees of the power basis `\bfB^{(ε)}`
from Notation `N:power basis`.
-/
def bfeResidueMax (a sε : ℕ) : ℕ :=
  Nat.max sε ((a + sε) % pMinusOne p)

/--
The degree of the basis element `\bfe_{n+1}^{(ε)}` (Notation `N:power basis`, items (2)(3)).

We model the ordered basis as the merge of two arithmetic progressions with common step `p-1`,
so degrees alternate between the residues `bfeResidueMin` and `bfeResidueMax`.
-/
def bfeDegreeSucc (a sε : ℕ) (n : ℕ) : ℕ :=
  let m := n / 2
  if Even n then m * pMinusOne p + bfeResidueMin p a sε
  else m * pMinusOne p + bfeResidueMax p a sε

/--
The ghost-Hodge coefficient `λ_{n+1}^{(ε)}` used in the halo discussion
(just before Proposition 4.11).

This is `deg(\bfe_{n+1}^{(ε)}) - ⌊deg(\bfe_{n+1}^{(ε)})/p⌋`, implemented using Nat division.
-/
def lambdaSucc (a sε : ℕ) (n : ℕ) : ℕ :=
  let d : ℕ := bfeDegreeSucc p a sε n
  d - d / p

end Formulation

end GhostConjecture
