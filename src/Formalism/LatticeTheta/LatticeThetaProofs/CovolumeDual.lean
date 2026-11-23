module

public import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

open MeasureTheory Matrix
open scoped RealInnerProductSpace

noncomputable section

namespace Formalism.H

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

lemma covolDual_nondegenerate : (innerₗ V).Nondegenerate := by
  constructor <;> intro m hm <;> simpa using hm m

lemma covolDual_det_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (o : OrthonormalBasis ι ℝ V) (e : Module.Basis ι ℝ V) :
    o.toBasis.det (LinearMap.BilinForm.dualBasis (innerₗ V) covolDual_nondegenerate e) * o.toBasis.det e = 1 := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply]
  set P := o.toBasis.toMatrix e with hP
  set Q := o.toBasis.toMatrix (LinearMap.BilinForm.dualBasis (innerₗ V) covolDual_nondegenerate e) with hQ
  have hM : Qᵀ * P = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hsum : ∑ k, Qᵀ i k * P k j =
        ⟪LinearMap.BilinForm.dualBasis (innerₗ V) covolDual_nondegenerate e i, e j⟫ := by
      simp only [hP, hQ, Matrix.transpose_apply, Module.Basis.toMatrix_apply,
        OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
      rw [← o.sum_inner_mul_inner]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [real_inner_comm (o k)]
    rw [hsum]
    have h := LinearMap.BilinForm.apply_dualBasis_left covolDual_nondegenerate e i j
    simp only [innerₗ_apply_apply] at h
    rw [h]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  rw [← Matrix.det_transpose Q, ← Matrix.det_mul, hM, Matrix.det_one]

lemma covolDual_vol_fd {ι : Type*} [Fintype ι] (o : OrthonormalBasis ι ℝ V) :
    volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
  rw [MeasureTheory.measureReal_def,
    MeasureTheory.measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume),
    OrthonormalBasis.coe_toBasis, o.volume_parallelepiped, ENNReal.toReal_one]

end Formalism.H
