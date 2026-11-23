module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.TransInv

theorem im_conj_mul_ne_zero {w₁ w₂ : ℂ} (h : LinearIndependent ℝ ![w₁, w₂]) :
    ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 := by
  intro h0
  rw [LinearIndependent.pair_iff] at h
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h0
  have h1 := h w₂.im (-w₁.im) (by
    apply Complex.ext <;> simp <;> linarith)
  have h2 := h w₂.re (-w₁.re) (by
    apply Complex.ext <;> simp <;> linarith)
  have h3 := h 1 0 (by
    apply Complex.ext <;> simp <;> linarith [h1.2, h2.2])
  exact one_ne_zero h3.1

theorem im_conj_mul_mem {w₁ w₂ u v : ℂ} (hu : u ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ))
    (hv : v ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ)) :
    ∃ k : ℤ, ((starRingEnd ℂ) u * v).im = k * ((starRingEnd ℂ) w₁ * w₂).im := by
  obtain ⟨a, b, rfl⟩ := AddSubgroup.mem_closure_pair.1 hu
  obtain ⟨c, d, rfl⟩ := AddSubgroup.mem_closure_pair.1 hv
  refine ⟨a * d - b * c, ?_⟩
  simp
  ring

theorem area_closure_pair {w₁ w₂ : ℂ} (h : LinearIndependent ℝ ![w₁, w₂]) :
    area (AddSubgroup.closure ({w₁, w₂} : Set ℂ)) = |((starRingEnd ℂ) w₁ * w₂).im| := by
  have h0 := im_conj_mul_ne_zero h
  unfold area
  apply IsLeast.csInf_eq
  refine ⟨⟨abs_pos.2 h0, w₁, AddSubgroup.subset_closure (by simp), w₂,
    AddSubgroup.subset_closure (by simp), rfl⟩, ?_⟩
  rintro a ⟨ha, u, hu, v, hv, rfl⟩
  obtain ⟨k, hk⟩ := im_conj_mul_mem hu hv
  rw [hk] at ha ⊢
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at ha
  have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
  rw [abs_mul]
  nlinarith [abs_nonneg ((starRingEnd ℂ) w₁ * w₂).im]

end GlobalTheory.TransInv
