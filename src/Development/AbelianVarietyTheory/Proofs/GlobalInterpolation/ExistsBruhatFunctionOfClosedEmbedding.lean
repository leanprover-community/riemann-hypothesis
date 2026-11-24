module

public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBruhatFunctionClosedSubgroup
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Topology
open scoped ENNReal

namespace GlobalTheory

theorem exists_bruhat_function_closedEmbedding
    (T T' : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [T2Space T] [MeasurableSpace T] [BorelSpace T]
    [Group T'] [TopologicalSpace T'] [IsTopologicalGroup T'] [MeasurableSpace T'] [BorelSpace T']
    (j : T' →* T) (hj : IsClosedEmbedding j) (m' : Measure T') [m'.IsHaarMeasure]
    [m'.IsInvInvariant] :
    ∃ b : T → ℝ≥0∞, Measurable b ∧ ∀ t, ∫⁻ s, b (j s * t) ∂m' = 1 := by
  classical
  let H : Subgroup T := j.range
  have hH : IsClosed (H : Set T) := by
    simpa [H, MonoidHom.coe_range] using hj.isClosed_range
  let e : T' ≃* H := MonoidHom.ofInjective hj.injective
  have he : Continuous e := hj.continuous.subtype_mk _
  have hes : Continuous e.symm := by
    rw [hj.isEmbedding.isInducing.continuous_iff]
    have : (fun x : H => j (e.symm x)) = fun x : H => (x : T) := by
      funext x
      exact MonoidHom.apply_ofInjective_symm hj.injective x
    rw [Function.comp_def, this]
    exact continuous_subtype_val
  have : (Measure.map e m').IsHaarMeasure := e.isHaarMeasure_map m' he hes
  obtain ⟨φ, hφ, hint, -⟩ := exists_bruhat_function_closed_subgroup T H hH (Measure.map e m')
  refine ⟨fun x => φ x⁻¹, hφ.comp measurable_inv, fun t => ?_⟩
  show ∫⁻ s, φ (j s * t)⁻¹ ∂m' = 1
  have h1 := hint t⁻¹
  have hm : Measurable (fun h : H => φ (t⁻¹ * (h : T))) :=
    hφ.comp (continuous_const.mul continuous_subtype_val).measurable
  rw [lintegral_map hm he.measurable] at h1
  have h2 : ∀ s : T', ((e s : H) : T) = j s := fun s => rfl
  simp only [h2] at h1
  have h3 : ∀ s : T', (j s * t)⁻¹ = t⁻¹ * j s⁻¹ := fun s => by
    rw [mul_inv_rev, map_inv]
  simp only [h3]
  rw [lintegral_inv_eq_self (fun s => φ (t⁻¹ * j s))]
  exact h1

end GlobalTheory
