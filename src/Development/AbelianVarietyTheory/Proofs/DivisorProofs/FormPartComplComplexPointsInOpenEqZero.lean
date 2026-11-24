module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2DbarChartMeasureTransfer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeImageComplPtsIn
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell2Null

theorem part_compl_ptsIn : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (Y : Var F) (β : (atlas Y σ).Fld) (W : Y.X.Opens), genericPoint Y.X ∈ W → ∀ s : ℤˣ, (atlas Y σ).part β s (ptsIn Y.str σ W)ᶜ = 0 := by
  intro F _ σ Y β W hW s
  exact GlueCoverNull.glueMeas_null _ _ (isOpen_ptsIn _).measurableSet.compl fun c =>
    GlobalTheory.Mean4O.CoverInt.volume_image_compl_ptsIn F Y.X Y.str σ σ.injective
      (fun W hW => (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str W).injective) W hW _ c

end GlobalTheory.FlagCell2Null
