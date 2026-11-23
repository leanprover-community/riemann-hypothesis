module

public import GroundTheory.LocalFields.LocalFourier
import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
import GroundTheory.LocalFields.LocalZetaShell
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory GroundTheory.LocalField

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.MultiplicativeHaarInverse

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

instance secondCountableTopology_units : SecondCountableTopology Kˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

instance sigmaCompactSpace_units : SigmaCompactSpace Kˣ := inferInstance

instance regular_multHaar : (multHaar K).Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

instance isInvInvariant_multHaar : (multHaar K).IsInvInvariant :=
  Measure.IsHaarMeasure.isInvInvariant_of_regular (multHaar K)

theorem inv_subst (f : Kˣ → ℂ) (t : Kˣ) :
    (Integrable f (multHaar K) ↔ Integrable (fun x => f (t * x⁻¹)) (multHaar K)) ∧
    ∫ a, f a ∂multHaar K = ∫ x, f (t * x⁻¹) ∂multHaar K := by
  have h1 : (fun x => f (t * x⁻¹)) = fun x => f (t / x) := by
    funext x
    rw [div_eq_mul_inv]
  rw [h1]
  exact ⟨(integrable_comp_div_left f t).symm, (integral_div_left_eq_self f (multHaar K) t).symm⟩

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.MultiplicativeHaarInverse
