module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConvolutionProjection.ConvProjOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj

open PI.PhConvProj

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem inner_map_map {π : G → (K →L[ℂ] K)} (hπ : IsURep π) (g : G) (x y : K) :
    ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let f : K →ₗᵢ[ℂ] K := ⟨(π g).toLinearMap, fun v => hπ.2.2.1 g v⟩
  exact f.inner_map_map x y

theorem map_inv_map {π : G → (K →L[ℂ] K)} (hπ : IsURep π) (g : G) (y : K) :
    π g (π g⁻¹ y) = y := by
  have h := congrArg (fun A : K →L[ℂ] K => A y) (hπ.2.1 g g⁻¹)
  simp only [mul_inv_cancel, hπ.1, ContinuousLinearMap.coe_comp, Function.comp_apply] at h
  rw [← h]
  rfl

theorem inner_map_left {π : G → (K →L[ℂ] K)} (hπ : IsURep π) (g : G) (x y : K) :
    ⟪π g x, y⟫_ℂ = ⟪x, π g⁻¹ y⟫_ℂ := by
  conv_lhs => rw [← (map_inv_map hπ) g y]
  exact (inner_map_map hπ) g x (π g⁻¹ y)

theorem inner_symm [MeasurableInv G] (μ : Measure G) [μ.IsInvInvariant] (ph : G → ℂ) (hph : ∀ g, ph g⁻¹ = star (ph g))
    {π : G → (K →L[ℂ] K)} (hπ : IsURep π) {T : K →L[ℂ] K} (hT : IsOpInt μ π ph T) (x y : K) :
    ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ := by
  have h1 : ⟪T x, y⟫_ℂ = ∫ g, ph g⁻¹ * ⟪x, π g⁻¹ y⟫_ℂ ∂μ := by
    rw [← inner_conj_symm, hT y x, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [map_mul, inner_conj_symm, hph g]
    rw [(inner_map_left hπ)]
    rfl
  rw [h1, hT x y]
  exact integral_inv_eq_self (fun g => ph g * ⟪x, π g y⟫_ℂ) μ

theorem selfAdj : Defs.SelfAdjStep := by
  intro G _ _ _ _ _ _ μ _ _ _ ph m _ hidem K _ _ π T hπ hT x y
  exact inner_symm μ ph hidem.2.1 hπ hT x y

end PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj
