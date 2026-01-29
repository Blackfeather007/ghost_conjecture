# Paper ↔ Lean formalization map

This file tracks where items from `data/arXiv-2206.15372v2.tex` live in the Lean project
`GhostConjectureLean/GhostConjecture`.

The goal is not to mirror the paper line-by-line, but to record the “anchor points”:
definitions/notations/propositions/remarks in the paper and the corresponding Lean declarations.

## Preparations (Newton polygons)

- Paper: Notation 2.1 / `\label{N:Newton polygon}` (Newton polygon of a power series)
  - Lean: `GhostConjecture.Preparations.newtonPoints` in `GhostConjectureLean/GhostConjecture/Preparations/NewtonPolygon.lean`
  - Lean: `GhostConjecture.Preparations.newtonPolygon` in `GhostConjectureLean/GhostConjecture/Preparations/NewtonPolygon.lean`
- Paper: “Newton polygon of a product is Minkowski sum” (requested in `instruction/instruction.tex`)
  - Lean: only the coefficient-wise valuation inequality is currently recorded as
    `GhostConjecture.Preparations.coeff_mul_val_ge_inf_antidiagonal` in
    `GhostConjectureLean/GhostConjecture/Preparations/NewtonPolygon.lean`

## Section 4: Formulation of the local ghost series

### Notation 2.24 / Notation 4.2 / Corollary 4.4

- Paper: Notation 2.24 (`k_ε`) and Notation 4.2 (`δ_ε`)
  - Lean: `GhostConjecture.Formulation.kEpsilon` in `GhostConjectureLean/GhostConjecture/Formulation/Dimensions.lean`
  - Lean: `GhostConjecture.Formulation.deltaEpsilon` in `GhostConjectureLean/GhostConjecture/Formulation/Dimensions.lean`
- Paper: Remark `\label{R:delta}` (arithmetic identity relating `δ_ε`)
  - Lean: `GhostConjecture.Formulation.pMinusOne_mul_deltaEpsilon_add_mod_eq` in
    `GhostConjectureLean/GhostConjecture/Formulation/Dimensions.lean`
- Paper: Corollary 4.4 (“`d_k^Iw` is even” in the `k = k_ε + k_•(p-1)` class)
  - Lean: `GhostConjecture.Formulation.dIw_eq_two_mul_kBullet_add_two_sub_two_mul_delta` in
    `GhostConjectureLean/GhostConjecture/Formulation/Dimensions.lean`

### Proposition 4.1 (taken as a definition)

- Paper: Proposition `\label{P:dimension of SIw}` (dimension formula for `d_k^Iw`)
  - Lean: `GhostConjecture.Formulation.dIw` in `GhostConjectureLean/GhostConjecture/Formulation/Dimensions.lean`
  - Status: taken as a definition (no proof), per `instruction/instruction.tex`

### Section 4.6 auxiliaries (`t₁^{(ε)}`, `t₂^{(ε)}`)

- Paper: `t_1^{(ε)}`, `t_2^{(ε)}` as in §4.6
  - Lean: `GhostConjecture.Formulation.tOne` in `GhostConjectureLean/GhostConjecture/Formulation/UnramifiedDimensions.lean`
  - Lean: `GhostConjecture.Formulation.tTwo` in `GhostConjectureLean/GhostConjecture/Formulation/UnramifiedDimensions.lean`

### Proposition 4.7 (taken as a definition)

- Paper: Proposition `\label{P:dimension of Sunr}` (dimension formula for `d_k^unr` in the class)
  - Lean: `GhostConjecture.Formulation.dUnr` in `GhostConjectureLean/GhostConjecture/Formulation/UnramifiedDimensions.lean`
  - Status: taken as a definition (no proof), per `instruction/instruction.tex`

### Notation 4.10 / Notation 3.8 (basis degrees) / halo slopes

- Paper: Notation `\label{N:tnvarepsilon}` (`β_{[n]}^{(ε)}`, `β_even`, `β_odd`)
  - Lean: `GhostConjecture.Formulation.betaEven` / `betaOdd` / `betaBracket` in
    `GhostConjectureLean/GhostConjecture/Formulation/BasisDegrees.lean`
- Paper: Notation `\label{N:power basis}` / Notation 3.8(2)(3) (degrees of basis elements `\bfe_n`)
  - Lean: `GhostConjecture.Formulation.bfeDegreeSucc` in
    `GhostConjectureLean/GhostConjecture/Formulation/BasisDegrees.lean`
- Paper: definition of halo slope `λ_{n+1}^{(ε)}`
  - Lean: `GhostConjecture.Formulation.lambdaSucc` in
    `GhostConjectureLean/GhostConjecture/Formulation/BasisDegrees.lean`
  - Lean (integer version used in proofs): `GhostConjecture.Formulation.lambdaSuccZ` in
    `GhostConjectureLean/GhostConjecture/Formulation/DegreeIncrements.lean`

### Proposition 4.11 (degree increments)

- Paper: Proposition `\label{P:increment of degrees in ghost series}`
  - Lean: `GhostConjecture.Formulation.ghostDegreeIncrement` / `ghostDegree` in
    `GhostConjectureLean/GhostConjecture/Formulation/DegreeIncrements.lean`
  - Lean: table/ceiling-division arithmetic lemmas in
    `GhostConjectureLean/GhostConjecture/Formulation/Prop411Lemmas.lean`
  - Lean: parity split lemma corresponding to `\eqref{E:kmax-kmid}` in
    `GhostConjectureLean/GhostConjecture/Formulation/IncrementOfDegrees.lean`

### Definition 2.25 (ghost multiplicities) / equations (2.25.3) and (2.25.4)

- Paper: Definition 2.25 (ghost multiplicity “tent function”) and identities (2.25.3), (2.25.4)
  - Lean: `GhostConjecture.Formulation.ghostMultiplicity` in
    `GhostConjectureLean/GhostConjecture/Formulation/GhostMultiplicities.lean`
  - Lean: `GhostConjecture.Formulation.ghostMultiplicity_succ_sub` in
    `GhostConjectureLean/GhostConjecture/Formulation/GhostMultiplicities.lean`
  - Lean: `GhostConjecture.Formulation.ghostMultiplicity_secondDifference` in
    `GhostConjectureLean/GhostConjecture/Formulation/GhostMultiplicities.lean`
- Paper: Definition 2.25 (ghost coefficients `g_n(w)` and ghost series `G(w,t) = ∑ g_n(w)t^n`) as a
  finite product/power series
  - Lean: `GhostConjecture.Formulation.ghostSupport` in `GhostConjectureLean/GhostConjecture/Formulation/GhostSeries.lean`
  - Lean: `GhostConjecture.Formulation.ghostCoeffPoly` in `GhostConjectureLean/GhostConjecture/Formulation/GhostSeries.lean`
  - Lean: `GhostConjecture.Formulation.ghostCoeffHatPoly` in `GhostConjectureLean/GhostConjecture/Formulation/GhostSeries.lean`
  - Lean: `GhostConjecture.Formulation.ghostSeries` / `ghostSeriesEval` in
    `GhostConjectureLean/GhostConjecture/Formulation/GhostSeries.lean`

### Remark 4.13 (non-primitive scaling)

- Paper: Remark 4.13 (label `\label{R:nonprimitive ghost}`), item (1)
  - Lean: `GhostConjecture.Formulation.dIwWithMultiplicity` in
    `GhostConjectureLean/GhostConjecture/Formulation/Remark413.lean`
  - Lean: `GhostConjecture.Formulation.dUnrWithMultiplicity` in
    `GhostConjectureLean/GhostConjecture/Formulation/Remark413.lean`

### Notation 4.17 (`g_{n,\hat k}` and `g_{n,\hat{\bf k}}`)

- Paper: Notation 4.17 (label `\label{N:gnhatk}`)
  - Lean: `GhostConjecture.Formulation.ghostCoeffHat` in
    `GhostConjectureLean/GhostConjecture/Formulation/GhostCoefficients.lean`
  - Lean: `GhostConjecture.Formulation.ghostCoeffHatSet` in
    `GhostConjectureLean/GhostConjecture/Formulation/GhostCoefficients.lean`
  - Lean: reinsertion lemmas `ghostCoeffHat_mul_factor`, `ghostCoeffHatSet_mul_removed` in the same file

### Proposition 4.18 (compatibilities / ghost duality): supporting lemmas in progress

- Paper: Proposition 4.18 (label `\label{P:ghost compatible with theta AL and p-stabilization}`)
  - Lean (supporting step): evaluation and valuation normal forms for hatted ghost coefficients:
    - `GhostConjecture.Formulation.ghostCoeffHat_eval` in `GhostConjectureLean/GhostConjecture/Formulation/Prop418.lean`
    - `GhostConjecture.Formulation.ghostCoeffHat_eval_val` in `GhostConjectureLean/GhostConjecture/Formulation/Prop418.lean`
    - `GhostConjecture.Formulation.ghostCoeffHatSet_eval` in `GhostConjectureLean/GhostConjecture/Formulation/Prop418.lean`
    - `GhostConjecture.Formulation.ghostCoeffHatSet_eval_val` in `GhostConjectureLean/GhostConjecture/Formulation/Prop418.lean`
  - Lean (supporting step): Nat-valued multiplicities for exponents:
    - `GhostConjecture.Formulation.ghostMultiplicityNat` in `GhostConjectureLean/GhostConjecture/Formulation/GhostMultiplicityNat.lean`
  - Lean (supporting step): rewrite the midpoint inequalities in the `±1` conditions using `kMidBullet`:
    - `GhostConjecture.Formulation.int_lt_halfDIwClass_iff_kMidBullet_lt` in
      `GhostConjectureLean/GhostConjecture/Formulation/Prop418Increments.lean`
    - `GhostConjecture.Formulation.halfDIwClass_le_int_iff_le_kMidBullet` in
      `GhostConjectureLean/GhostConjecture/Formulation/Prop418Increments.lean`
    - `GhostConjecture.Formulation.ghostMultiplicityIncPos_iff_dUnr_le_and_kMidBullet_lt` in
      `GhostConjectureLean/GhostConjecture/Formulation/Prop418Increments.lean`
    - `GhostConjecture.Formulation.ghostMultiplicityIncNeg_iff_le_kMidBullet_and_lt_end` in
      `GhostConjectureLean/GhostConjecture/Formulation/Prop418Increments.lean`
  - Lean (supporting step): valuation increment identity (Eq. `\label{E:increment of ghost series valuation 1}` in the proof):
    - `GhostConjecture.Formulation.ghostCoeffHat_eval_val_succ_add_sum_incNeg_eq_add_sum_incPos` in
      `GhostConjectureLean/GhostConjecture/Formulation/Prop418Increments.lean`
  - Lean (supporting step): second-order valuation increment identity (Eq. `\label{E:increment of ghost series valuation 2}` in the proof):
    - `GhostConjecture.Formulation.ghostCoeffHat_eval_val_secondOrder_add_sums_eq_two_nsmul_add_sums` in
      `GhostConjectureLean/GhostConjecture/Formulation/Prop418Increments.lean`
  - Lean (bridge to paper Eq. `\label{E:vp of k1-k2}`): weight points and the valuation formula
    `v_p(w_{k₀}-w_k) = v_p(k₀-k) + 1` (proved for odd primes via LTE):
    - `GhostConjecture.Formulation.expP` in `GhostConjectureLean/GhostConjecture/Formulation/Prop418Padic.lean`
      (Lean name for the paper’s chosen element `exp(p) ∈ 1+pℤ_p`, fixed here to `p+1`)
    - `GhostConjecture.Formulation.expMulP` in `GhostConjectureLean/GhostConjecture/Formulation/Prop418Padic.lean`
      (the paper’s notation `exp(pn)` on integer inputs, implemented as `(exp(p))^n`)
    - `GhostConjecture.Formulation.weightGenerator` in `GhostConjectureLean/GhostConjecture/Formulation/Prop418Padic.lean`
      (a concrete choice of the paper’s topological generator `exp(p)`, fixed to `p+1`)
    - `GhostConjecture.Formulation.padicWeight` in `GhostConjectureLean/GhostConjecture/Formulation/Prop418Padic.lean`
      (implemented as `w_k := η^(k-2) - 1` with `η = weightGenerator = p+1`)
    - `GhostConjecture.Formulation.addValuation_padicWeight_sub` in
      `GhostConjectureLean/GhostConjecture/Formulation/Prop418Padic.lean`
  - Lean (specialized increments with `padicValInt` terms):
    - `GhostConjecture.Formulation.ghostCoeffHat_eval_val_succ_add_sum_incNeg_eq_add_sum_incPos_padicWeight` in
      `GhostConjectureLean/GhostConjecture/Formulation/Prop418Padic.lean`
    - `GhostConjecture.Formulation.ghostCoeffHat_eval_val_secondOrder_add_sums_eq_two_nsmul_add_sums_padicWeight` in
      `GhostConjectureLean/GhostConjecture/Formulation/Prop418Padic.lean`
  - Status: the full Proposition 4.18 statement/proof is not yet formalized; this file sets up the
    product→sum rewriting needed for the valuation comparisons.

### Notation 4.27 (digit sum / sums of consecutive valuations)

- Paper: Notation 4.27 (`\Dig(m)` and `\label{E:sum of consecutive valuations}`)
  - Lean: `GhostConjecture.Formulation.Dig` in `GhostConjectureLean/GhostConjecture/Formulation/Notation427.lean`
  - Lean: `GhostConjecture.Formulation.sub_one_mul_sum_padicValNat_Ioc` in
    `GhostConjectureLean/GhostConjecture/Formulation/Notation427.lean`
  - Lean: division-form version `GhostConjecture.Formulation.sum_padicValNat_Ioc` in
    `GhostConjectureLean/GhostConjecture/Formulation/Notation427.lean`

### Proposition 4.28 (Gouvêa’s `⌊(k-1)/(p+1)⌋` bound): not yet formalized

- Paper: Proposition `\label{P:gouvea k-1/p+1 conjecture}`
  - Status: not yet stated/proved in Lean; the digit-sum/valuation-sum tool from Notation 4.27 is
    now available for this proof.

## Section 5: Vertices of the Newton polygon of ghost series

- Paper: Kummer/Legendre digit-sum identity in the background of Section 5 estimates
  - Lean: `GhostConjecture.Formulation.sub_one_mul_padicValNat_choose_eq_sub_Dig` in
    `GhostConjectureLean/GhostConjecture/Formulation/Section5Digits.lean`
- Paper: basic bound `v_p(n) ≤ ⌊log_p(n)⌋` and the derived interval version used to control maxima
  - Lean: `GhostConjecture.Formulation.padicValNat_le_natLog` in
    `GhostConjectureLean/GhostConjecture/Formulation/Section5Digits.lean`
  - Lean: `GhostConjecture.Formulation.padicValNat_le_natLog_of_mem_Ioc` in
    `GhostConjectureLean/GhostConjecture/Formulation/Section5Digits.lean`

## Status notes

- This map will be extended as the formalization proceeds (e.g. Proposition 4.18 and later).
