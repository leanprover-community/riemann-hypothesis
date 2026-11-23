module

public import Formalism.PeriodIntegrals.PhSchurConv
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

@[expose] public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace PI.UnitaryGroupMassFormula.PhSchurConv.Main

open PI.PhSchurConv

theorem star_inner {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (a b : H) :
    star ⟪a, b⟫_ℂ = ⟪b, a⟫_ℂ := by
  exact inner_conj_symm b a

theorem map_mul_apply {G : Type} [Group G] [TopologicalSpace G]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : G → (H →L[ℂ] H)} (hU : IsURep σ) (a b : G) (v : H) : σ (a * b) v = σ a (σ b v) := by
  rw [hU.2.1 a b]
  rfl

theorem inner_map {G : Type} [Group G] [TopologicalSpace G]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : G → (H →L[ℂ] H)} (hU : IsURep σ) (g : G) (a b : H) : ⟪σ g a, σ g b⟫_ℂ = ⟪a, b⟫_ℂ := by
  let L : H →ₗᵢ[ℂ] H := ⟨(σ g).toLinearMap, hU.2.2.1 g⟩
  exact L.inner_map_map a b

theorem coef_inv {G : Type} [Group G] [TopologicalSpace G]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : G → (H →L[ℂ] H)} (hU : IsURep σ) (g : G) (w : H) :
    ⟪w, σ g⁻¹ w⟫_ℂ = star ⟪w, σ g w⟫_ℂ := by
  rw [star_inner, ← inner_map hU g w (σ g⁻¹ w), ← map_mul_apply hU, mul_inv_cancel, hU.1,
    ContinuousLinearMap.one_apply]

theorem coef_conv {G : Type} [Group G] [TopologicalSpace G]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : G → (H →L[ℂ] H)} (hU : IsURep σ) (g x y : G) (w : H) :
    ⟪w, σ (x⁻¹ * g⁻¹ * y) w⟫_ℂ = ⟪σ g (σ x w), σ y w⟫_ℂ := by
  have h1 : σ g (σ x w) = σ (g * x) w := (map_mul_apply hU g x w).symm
  rw [h1]
  symm
  calc ⟪σ (g * x) w, σ y w⟫_ℂ = ⟪σ (g * x)⁻¹ (σ (g * x) w), σ (g * x)⁻¹ (σ y w)⟫_ℂ := (inner_map hU _ _ _).symm
    _ = ⟪w, σ (x⁻¹ * g⁻¹ * y) w⟫_ℂ := by
      rw [← map_mul_apply hU, ← map_mul_apply hU, inv_mul_cancel, hU.1, ContinuousLinearMap.one_apply,
        mul_inv_rev]

end PI.UnitaryGroupMassFormula.PhSchurConv.Main
