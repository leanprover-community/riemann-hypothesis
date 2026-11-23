module

public import GroundTheory.AutomorphicForms.GKModules.SmoothVectors
public import Development.AutomorphicArithmetic.TwistedTraces.NormExpSmulSubLeNormDerivOp
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.QuotientMeasure
import GroundTheory.AutomorphicForms.ReductionBlock

@[expose] public section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.exists_nhds_displacement_le_half_of_derivOp_bound :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ h.lieSubalgebra) (C : ℝ), ∃ N ∈ 𝓝 (1 : G), ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E) (v : E), (∀ g w, ‖π g w‖ = ‖w‖) → h.IsSmoothVector π v → (∀ i, ‖h.derivOp π (h.ofLie (b i)) v‖ ≤ C * ‖v‖) → ∀ a ∈ N, ‖π a v - v‖ ≤ 1 / 2 * ‖v‖ := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b C
  let T : 𝔤 →ₗ[ℝ] h.lieSubalgebra :=
    { toFun := h.toLie, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let S : h.lieSubalgebra →ₗ[ℝ] 𝔤 :=
    { toFun := h.ofLie, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hST : ∀ X : 𝔤, S (T X) = X := fun _ => rfl
  let f : 𝔤 → ℝ := fun X => (∑ i, |b.repr (h.toLie X) i|) * |C|
  have hf : Continuous f := by
    refine Continuous.mul (continuous_finsetSum _ fun i _ => ?_) continuous_const
    exact (LinearMap.continuous_of_finiteDimensional ((b.coord i) ∘ₗ T)).abs
  have hf0 : f 0 = 0 := by
    have : h.toLie 0 = 0 := rfl
    simp [f, this]
  have hO : {X : 𝔤 | f X < 1 / 2} ∈ 𝓝 (0 : 𝔤) :=
    (isOpen_lt hf continuous_const).mem_nhds (by simp [hf0])
  have h0 : (0 : 𝔤) ∈ (h.chart 1).symm.source := h.zero_mem_nhd
  have hexp0 : h.expG 0 = 1 := by
    apply Subtype.ext; apply Units.ext
    simp [IsExpLieAlgebra.coe_expG]
  refine ⟨h.expG '' {X : 𝔤 | f X < 1 / 2}, ?_, ?_⟩
  · have h1 := (h.chart 1).symm.image_mem_nhds h0 hO
    have e1 : (h.chart 1).symm 0 = 1 := by
      show 1 * h.expG 0 = 1
      rw [hexp0, one_mul]
    rw [e1] at h1
    refine Filter.mem_of_superset h1 ?_
    rintro _ ⟨X, hX, rfl⟩
    refine ⟨X, hX, ?_⟩
    show h.expG X = 1 * h.expG X
    rw [one_mul]
  · rintro E _ _ π v hπ hv hb _ ⟨X, hX, rfl⟩
    refine (UpperTheory.norm_exp_smul_sub_le_norm_derivOp 𝔸 G 𝔤 h E π v X hπ hv).trans ?_
    have hsum : X = ∑ i, b.repr (h.toLie X) i • h.ofLie (b i) := by
      conv_lhs => rw [← hST X]
      show S (h.toLie X) = _
      conv_lhs => rw [← b.sum_repr (h.toLie X)]

      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul S _ _
    have hD : h.derivOp π X v =
        ∑ i, b.repr (h.toLie X) i • h.derivOp π (h.ofLie (b i)) v := by
      show fderiv ℝ (h.expOrbit π v) 0 X = ∑ i, b.repr (h.toLie X) i •
        fderiv ℝ (h.expOrbit π v) 0 (h.ofLie (b i))
      conv_lhs => rw [hsum]

      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
    have hbound : ‖h.derivOp π X v‖ ≤ f X * ‖v‖ := by
      rw [hD]
      refine (norm_sum_le _ _).trans ?_
      simp only [f, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_smul, Real.norm_eq_abs, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact (hb i).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg v))
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_of_lt hX) (norm_nonneg v))
