module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HolomorphicCuspFormsFramesLeSpanShortThetaReadin
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

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

theorem _root_.GlobalTheory.T.holomorphicCuspForms_frames_le_span_shortThetaReadings : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D), LawsM T.toCore → LawsSh T → GamAt T.toCore → 0 < badN D → (∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧ ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0) → ∀ (j : ℕ) (_hj : InR D j) (ka : WeightFamilies.Wt D j), 8 * D.R.f * D.R.r + 4 ≤ ka.n → GlobalTheory.Dict.holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA ka) ka.n) ≤ Submodule.span ℂ (rdU (T.U j T.σ₀) '' T.sh j ka) := by
  first | exact @GlobalTheory.Dict.holSub0_le_span_short_rec | exact GlobalTheory.Dict.holSub0_le_span_short_rec | (intros; apply GlobalTheory.Dict.holSub0_le_span_short_rec <;> assumption)
