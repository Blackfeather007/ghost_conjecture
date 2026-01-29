import GhostConjecture.Formulation.Dimensions

namespace GhostConjecture

namespace Formulation

variable (p : ℕ) [Fact (Nat.Prime p)]

/--
The auxiliary integer `t₁^{(ε)}` used in the explicit unramified-dimension formula
(`data/arXiv-2206.15372v2.tex`, §4, around Proposition `P:dimension of Sunr`).

This depends on the fixed input `a` and the residue parameter `sε` (usually chosen with
`sε < p-1`).
-/
def tOne (a sε : ℕ) : ℕ :=
  if a + sε < pMinusOne p then
    sε + deltaEpsilon p a sε
  else
    (a + sε) % pMinusOne p + deltaEpsilon p a sε + 1

/--
The auxiliary integer `t₂^{(ε)}` used in the explicit unramified-dimension formula
(`data/arXiv-2206.15372v2.tex`, §4, around Proposition `P:dimension of Sunr`).

This depends on the fixed input `a` and the residue parameter `sε` (usually chosen with
`sε < p-1`).
-/
def tTwo (a sε : ℕ) : ℕ :=
  if a + sε < pMinusOne p then
    a + sε + deltaEpsilon p a sε + 2
  else
    sε + deltaEpsilon p a sε + 1

/--
The unramified dimension `d_k^unr(ε₁)` in the congruence class `k ≡ k_ε (mod p-1)`,
taken as a definition (Proposition `P:dimension of Sunr` in `data/arXiv-2206.15372v2.tex`).

The paper writes this in terms of `k = k_ε + k_•(p-1)`; we take `kBullet : ℤ` to model `k_•`.
-/
def dUnr (a sε : ℕ) (kBullet : ℤ) : ℤ :=
  let q : ℤ := (p + 1 : ℤ)
  (kBullet - (tOne p a sε : ℤ)) / q + (kBullet - (tTwo p a sε : ℤ)) / q + 2

end Formulation

end GhostConjecture

