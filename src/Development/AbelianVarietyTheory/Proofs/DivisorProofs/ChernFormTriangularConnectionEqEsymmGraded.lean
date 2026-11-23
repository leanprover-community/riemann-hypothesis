module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormTriangularEqEsymmFirstChernFormsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlaggedBundleMetricSmoothUnitEtaleChartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorGradedLengthSmoothStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorPosDefPropertiesStatement
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

namespace GlobalTheory.ChernCalc

theorem chernFld_ldPart_eq_esymm_grF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ τ j p, chernFld (atlas X σ) (fun y z => ldPart (gramAt E H τ y z)) j p = aeval (fun i => grF E H ⟨τ, i⟩ p) (esymm (Fin (m τ)) ℂ j) := by
  intro F _ σ X ι _ m E H hH τ j p
  set A := (E.nonempty (under p.pt)).choose with hAdef
  have hA : A ∈ E.S (under p.pt) := (E.nonempty (under p.pt)).choose_spec
  have hev := ((GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m m E H hH p.pt A hA τ).2 p.1.1 p.2)
  change ∀ᶠ v in 𝓝 p.crd, MContDiffAt ∞ (fun u => H A (p.ch.symm u) τ) v ∧ (H A (p.ch.symm v) τ).PosDef at hev
  have h0 := hev.self_of_nhds
  have hs := GlobalTheory.T.gramLowerTriangularFactor_gradedLength_smooth X.dim (m τ) (fun u => H A (p.ch.symm u) τ) p.crd h0.1 h0.2
  have hp0 := GlobalTheory.T.gramLowerTriangularFactor_posDef_properties (m τ) _ h0.2
  show chernAt (fun v => ldPart (H A (p.ch.symm v) τ)) p.crd j = _
  refine (GlobalTheory.T.chernForm_triangular_eq_esymm_firstChernForms X.dim (m τ) (fun v => ldPart (H A (p.ch.symm v) τ))
    (fun i v => grD (H A (p.ch.symm v) τ) i) p.crd hs.1 (fun i => (hp0.2.1 i).1) ?_ j).trans rfl
  filter_upwards [hev] with x hx
  have hpx := GlobalTheory.T.gramLowerTriangularFactor_posDef_properties (m τ) _ hx.2
  exact ⟨hpx.2.2.1, fun i => (hpx.2.1 i).2⟩

end GlobalTheory.ChernCalc
