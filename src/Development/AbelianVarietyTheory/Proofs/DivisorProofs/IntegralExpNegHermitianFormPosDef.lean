module

public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

namespace GlobalTheory.GaussHerm

lemma finrank_V (n : ℕ) : Module.finrank ℝ (V n) = 2 * n := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (V n), Complex.finrank_real_complex, finrank_euclideanSpace,
    Fintype.card_fin]

lemma det_toEuclideanLin {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det (Matrix.toEuclideanLin C) = C.det := by
  have : Matrix.toEuclideanLin C = Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis C := by
    ext v i : 2
    simp [Matrix.toLin_apply, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      PiLp.single_apply, Pi.single_apply]
  rw [this, LinearMap.det_toLin]

lemma quad_eq {n : ℕ} (H C : Matrix (Fin n) (Fin n) ℂ) (hC : H.transpose = C.conjTranspose * C)
    (w : V n) :
    (∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re = ‖Matrix.toEuclideanLin C w‖ ^ 2 := by
  have hH : ∀ j l, H j l = ∑ k, (starRingEnd ℂ) (C k l) * C k j := by
    intro j l
    have := congrFun (congrFun hC l) j
    simpa [Matrix.mul_apply] using this
  have hc : (∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)) =
      ∑ k, (∑ j, C k j * w j) * (starRingEnd ℂ) (∑ l, C k l * w l) := by

    simp only [hH, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    exact (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans (Finset.sum_comm.trans
      (Finset.sum_congr rfl fun k _ => Finset.sum_comm.trans (Finset.sum_congr rfl fun l _ =>
        Finset.sum_congr rfl fun j _ => by ring)))
  rw [hc, EuclideanSpace.norm_sq_eq, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

theorem exists_eq_conjTranspose_mul_self {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : T.PosSemidef) : ∃ B : Matrix (Fin n) (Fin n) ℂ, T = B.conjTranspose * B := by
  open scoped MatrixOrder in
  have h0 : 0 ≤ T := Matrix.nonneg_iff_posSemidef.mpr hT
  have hs : (CFC.sqrt T).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg T)
  exact ⟨CFC.sqrt T, by rw [hs.1.eq, CFC.sqrt_mul_sqrt_self T h0]⟩

theorem integral_exp_neg_herm : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), H.PosDef →
    Integrable (fun w : V n => Real.exp (-(∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re)) ∧
    ∫ w : V n, Real.exp (-(∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re) =
      Real.pi ^ n / H.det.re := by
  intro n H hH
  have hT : H.transpose.PosDef := Matrix.PosDef.transpose_iff.mpr hH
  obtain ⟨C, hC⟩ := exists_eq_conjTranspose_mul_self hT.posSemidef
  set L : V n →ₗ[ℝ] V n := (Matrix.toEuclideanLin C).restrictScalars ℝ with hL
  have hdetL : LinearMap.det L = Complex.normSq C.det := by
    rw [hL, LinearMap.det_restrictScalars, det_toEuclideanLin, Algebra.norm_complex_apply]
  have hdetC : H.det = (Complex.normSq C.det : ℂ) := by
    rw [← Matrix.det_transpose H, hC, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def,
      mul_comm, Complex.mul_conj]
  have hdetH : H.det.re = Complex.normSq C.det := by rw [hdetC, Complex.ofReal_re]
  have hpos : 0 < Complex.normSq C.det := by
    have := hH.det_pos
    rwa [hdetC, Complex.zero_lt_real] at this
  set g : V n → ℝ := fun v => Real.exp (-1 * ‖v‖ ^ 2) with hg
  have hf : (fun w : V n => Real.exp (-(∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re)) =
      fun w => g (L w) := by
    funext w
    rw [quad_eq H C hC w, hg]
    simp [hL]
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (V n)) (f := L)
    (by rw [hdetL]; exact hpos.ne')
  have hG : ∫ v : V n, g v = Real.pi ^ n := by
    rw [hg, GaussianFourier.integral_rexp_neg_mul_sq_norm one_pos, finrank_V, div_one]
    rw [show ((2 * n : ℕ) : ℝ) / 2 = (n : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hgc : Continuous g := by rw [hg]; fun_prop
  have hI : ∫ w : V n, g (L w) = Real.pi ^ n / H.det.re := by
    rw [← integral_map (L.continuous_of_finiteDimensional.aemeasurable)
      hgc.aestronglyMeasurable, hmap, integral_smul_measure, hG, hdetL, hdetH,
      ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (inv_pos.mpr hpos), smul_eq_mul,
      div_eq_inv_mul]
  rw [hf]
  refine ⟨Integrable.of_integral_ne_zero ?_, hI⟩
  rw [hI, hdetH]
  exact (div_pos (pow_pos Real.pi_pos n) hpos).ne'

end GlobalTheory.GaussHerm
