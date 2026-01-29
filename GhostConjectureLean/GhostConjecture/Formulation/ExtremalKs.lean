import GhostConjecture.Formulation.BasisDegrees
import Mathlib.Tactic

namespace GhostConjecture

namespace Formulation

variable (p : ℕ) [Fact (Nat.Prime p)]

/--
The ceiling division `⌈x / m⌉` for integers, implemented using Euclidean division.

For `m > 0` this is `-((-x) / m)`.
-/
def intCeilDiv (x : ℤ) (m : ℕ) : ℤ :=
  -((-x) / (m : ℤ))

/--
The midpoint index `k_{mid,•}^{(ε)}(n)` from Lemma-Notation `L:extremal ks`.

This is the unique `kBullet` such that `n = (1/2) d_k^Iw(\\tilde ε₁)` in the congruence class
`k = k_ε + (p-1)k_•`.
-/
def kMidBullet (a sε : ℕ) (n : ℕ) : ℤ :=
  (n : ℤ) + (deltaEpsilon p a sε : ℤ) - 1

/--
The maximal index `k_{max,•}^{(ε)}(n)` from Lemma-Notation `L:extremal ks`.

In the paper this is the largest `kBullet ≥ 0` with `d_k^unr(ε₁) = n`.
-/
def kMaxBullet (a sε : ℕ) (n : ℕ) : ℤ :=
  halfPPlusOne p * (n : ℤ) + betaBracket p a sε (n : ℤ) - 1

/--
The auxiliary integer `\\tilde k_{min,•}^{(ε)}(n)` from Lemma-Notation `L:extremal ks`.

The paper defines `k_{min,•}^{(ε)}(n)` as `⌈\\tilde k_{min,•}^{(ε)}(n) / p⌉`.
-/
def kMinTildeBullet (a sε : ℕ) (n : ℕ) : ℤ :=
  halfPPlusOne p * ((n : ℤ) - 1 + 2 * (deltaEpsilon p a sε : ℤ)) -
      betaBracket p a sε ((n : ℤ) - 1) +
    1

/--
The minimal index `k_{min,•}^{(ε)}(n)` from Lemma-Notation `L:extremal ks`.

This is the ceiling division `⌈\\tilde k_{min,•}^{(ε)}(n) / p⌉`.
-/
def kMinBullet (a sε : ℕ) (n : ℕ) : ℤ :=
  intCeilDiv (kMinTildeBullet p a sε n) p

/--
The weight `k_{mid}^{(ε)}(n) = k_ε + (p-1)k_{mid,•}^{(ε)}(n)`.
-/
def kMid (a sε : ℕ) (n : ℕ) : ℤ :=
  (kEpsilon p a sε : ℤ) + (pMinusOne p : ℤ) * kMidBullet p a sε n

/--
The weight `k_{max}^{(ε)}(n) = k_ε + (p-1)k_{max,•}^{(ε)}(n)`.
-/
def kMax (a sε : ℕ) (n : ℕ) : ℤ :=
  (kEpsilon p a sε : ℤ) + (pMinusOne p : ℤ) * kMaxBullet p a sε n

/--
The weight `k_{min}^{(ε)}(n) = k_ε + (p-1)k_{min,•}^{(ε)}(n)`.
-/
def kMin (a sε : ℕ) (n : ℕ) : ℤ :=
  (kEpsilon p a sε : ℤ) + (pMinusOne p : ℤ) * kMinBullet p a sε n

end Formulation

end GhostConjecture
