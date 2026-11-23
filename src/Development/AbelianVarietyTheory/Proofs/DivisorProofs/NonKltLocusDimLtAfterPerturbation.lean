module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogEqnAddSmulIffOfOff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataLogTerminalLogCanonicalGenerisationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAtAddSmulOfLcAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltAtLcAtOfLeCoeffStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimClosureLeOfSpecializes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem logCanonicalCut_of_step : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    ∀ (Δ D B : X → ℚ) (δ c : ℚ) (x z : X) (j : ℕ), KltAt p n Δ x → IsQCart D → IsQCart B →
      LcAt p n (Δ + D) x → 0 < δ → δ ≤ 1 → c ≤ 1 → Off B z →
      (∀ y, ¬ z ⤳ y → ∀ a : ℚ, 0 ≤ a → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + B) y) →
      topologicalKrullDim (closure ({z} : Set X)) = (j + 1 : ℕ) →
      LcAt p n (Δ + (1 - δ) • D + c • B) x → ¬ KltAt p n (Δ + (1 - δ) • D + c • B) x →
      LcCut p n (Δ + (1 - δ) • D + c • B) x j := by
  intro X _ _ _ p n hp hn Δ D B δ c x z j hk hD hB hl hδ hδ1 hc hoff hsep hdim hlc hnk
  refine ⟨hlc, hnk, fun w hwx hw => ?_⟩
  have hx : KltAt p n (Δ + (1 - δ) • D) x :=
    kltAt_add_smul_of_lcAt X p n hp hn Δ D δ x hD hk hl hδ hδ1
  have hkw : KltAt p n (Δ + (1 - δ) • D) w :=
    (GlobalTheory.T.kawamataLogTerminal_logCanonical_generisation X p n (Δ + (1 - δ) • D) x w hwx).1 hx
  by_cases hzw : z ⤳ w
  · by_cases hwz : w = z
    · subst hwz
      exact absurd ((off_add_smul X p n (Δ + (1 - δ) • D) B c w hoff).1.2 hkw) hw
    · exact topologicalKrullDim_closure_le_of_specializes X z w j hzw hwz hdim
  · exfalso
    have h1 : KltAt p n (Δ + (1 - δ) • D + (1 : ℚ) • B) w := by
      rw [one_smul]; exact hsep w hzw (1 - δ) (by linarith) hkw
    exact hw ((GlobalTheory.T.kltAt_and_lcAt_antitone_coeff X p n hp hn (Δ + (1 - δ) • D) B c 1 w hB hc).1 h1)

end GlobalTheory.PairStep
