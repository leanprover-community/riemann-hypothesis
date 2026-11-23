module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDensityChernPolynomialReEqChernPolyTopDensityStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

open GlobalTheory.ChartGlue

namespace GlobalTheory.ChernCalc

theorem chartMeas_congr_source {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] {n : ℕ}
    (e : OpenPartialHomeomorph Y (V n)) {ρ ρ' : Y → ENNReal} (h : ∀ y ∈ e.source, ρ y = ρ' y) :
    chartMeas e ρ = chartMeas e ρ' := by
  unfold chartMeas
  congr 1
  refine withDensity_congr_ae ?_
  refine (ae_restrict_iff' e.open_target.measurableSet).2 (Eventually.of_forall fun v hv => ?_)
  exact h _ (e.map_target hv)

theorem chernTopPart_eq_part : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m 0) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), ∀ (R : MvPolynomial (ι × ℕ) ℝ) (ε : ℤˣ), chernTopPart E H R ε = (atlas X σ).part (evalF (atlas X σ) (chernF E H) R) ε := by
  intro F _ σ X ι m E H R ε
  unfold chernTopPart HolAtlas.part glueMeas
  refine iSup_congr fun c => chartMeas_congr_source _ fun y hy => ?_
  have hx : (atlas X σ).loc (evalF (atlas X σ) (chernF E H) R) c (c.e y) =
      evalF (atlas X σ) (chernF E H) R ⟨(c, y), hy⟩ :=
    HolAtlas.loc_crd (atlas X σ) (evalF (atlas X σ) (chernF E H) R) ⟨(c, y), hy⟩
  show ENNReal.ofReal (_ * chernTop _ _ _) = ENNReal.ofReal (_ * (dens ((atlas X σ).loc _ c (c.e y))).re)
  rw [hx]
  congr 2
  exact (GlobalTheory.T.topDensity_chernPolynomial_re_eq_chernPolyTopDensity X.dim ι m R (fun v => H (E.nonempty (under y)).choose (c.e.symm v)) (c.e y)).symm

end GlobalTheory.ChernCalc
