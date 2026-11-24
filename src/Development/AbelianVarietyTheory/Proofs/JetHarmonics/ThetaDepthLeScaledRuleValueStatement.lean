module

public import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaDepthLeScaledRuleValue
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

theorem _root_.GlobalTheory.T.thetaDepth_le_scaled_rule_value : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), w.LastPos → ∀ (s : 𝓞 (recB h.toLawsCore).KO), s ≠ 0 → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la), ∀ f ∈ T.th j w, (recPJ h j hj).depth s w la y ≤ (((vLa la ((s : 𝓞 T.Q.c.F) : T.Q.c.F) : ℤ) : ℝ) : EReal) + vAtV y f := by
  first | exact @GlobalTheory.DepthRule.depth_le_scaled_value | exact GlobalTheory.DepthRule.depth_le_scaled_value | (intros; apply GlobalTheory.DepthRule.depth_le_scaled_value <;> assumption)
