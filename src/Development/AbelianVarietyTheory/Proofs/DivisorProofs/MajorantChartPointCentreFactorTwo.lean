module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFirstColumnsEqGraphTimesTopBlockStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartGraphCoordinatesOpNormLeOfSmallStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantEqOfFirstColumnsChangeStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ModeHalfStatementPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMatMulVec
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.DotAddRight
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SignTypeCancelIdentity
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBottomLeftBlock

@[expose] public section

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.ChartGraph

theorem maj_cpt_le_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (z : V (nd X)), IsOrth X x → (r : ℝ) ^ 2 * ‖z‖ ≤ 1 / 100 → ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj (cpt X x z) τ v ≤ 2 * X.maj x τ v ∧ X.maj x τ v ≤ 2 * X.maj (cpt X x z) τ v := by
  intro E _ _ _ r X x z hxo hz τ v
  have hx : x ∈ X.dom := ModeHalfA.dom_of_orth X hxo
  have ho : X.IsOrtho x := hxo
  have hZ := GlobalTheory.T.chartGraphCoordinates_opNorm_le_of_small E r X z hz
  have hy : X.xZ x (graphCoord X z) ∈ X.dom := OrthonormalChartBounds.xZ_mem_dom X hx ho (by linarith)
  obtain ⟨hdet, hcol⟩ := GlobalTheory.T.chart_firstColumns_eq_graph_times_topBlock E r X x z τ
  have heq := GlobalTheory.T.majorant_eq_of_firstColumns_change E r X (cpt X x z) (X.xZ x (graphCoord X z)) τ (chartMatrixTopBlock X z τ)
    (by rw [hdet]; exact one_ne_zero) (Data.gramPos_det_ne X hy τ) hcol v
  obtain ⟨h1, h2⟩ := UnipMove.MajH.maj_xZ' X hx ho (ρ := 1 / 50) (by norm_num) (by norm_num) hZ τ v
  have h0 : 0 ≤ X.maj x τ v := by
    rw [ModeHalfA.maj_orth X hxo]; exact Finset.sum_nonneg fun _ _ => by positivity
  rw [heq]
  constructor
  · nlinarith
  · nlinarith

end GlobalTheory.ChartGraph
