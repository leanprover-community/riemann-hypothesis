module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.H1cEqH1
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.HasSmithOfOne
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
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.RingTheory.OrderOfVanishing.Basic

@[expose] public section

namespace KStar.Selmer

open Matrix Module

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {n : Type*} [Fintype n] [DecidableEq n]

private theorem lengthDet_unit_mul {R : Type*} [CommRing R] (U A V : Matrix n n R)
    (hU : IsUnit U.det) (hV : IsUnit V.det) :
    Module.length R (H2 (U * A * V)) = Module.length R (H2 A) := by
  have hU' : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).2 hU
  have hV' : IsUnit V := (Matrix.isUnit_iff_isUnit_det V).2 hV
  have hb : Function.Bijective U.mulVecLin :=
    ⟨Matrix.mulVec_injective_of_isUnit hU', Matrix.mulVec_surjective_iff_isUnit.2 hU'⟩
  have hs : LinearMap.range V.mulVecLin = ⊤ :=
    LinearMap.range_eq_top.2 (Matrix.mulVec_surjective_iff_isUnit.2 hV')
  symm
  refine LinearEquiv.length_eq
    (Submodule.Quotient.equiv _ _ (LinearEquiv.ofBijective U.mulVecLin hb) ?_)
  rw [Matrix.mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _ hs, Matrix.mulVecLin_mul,
    LinearMap.range_comp]
  rfl

private theorem lengthDet_diagonal {R : Type*} [CommRing R] (d : n → R) :
    Module.length R (H2 (diagonal d)) = ∑ i, Ring.ord R (d i) := by
  have h : LinearMap.range (diagonal d).mulVecLin =
      Submodule.pi Set.univ (fun i => (Ideal.span {d i} : Submodule R R)) := by
    ext x
    simp only [LinearMap.mem_range, Matrix.mulVecLin_apply, Submodule.mem_pi, Set.mem_univ,
      true_imp_iff, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, rfl⟩ i
      exact ⟨y i, by rw [Matrix.mulVec_diagonal, mul_comm]⟩
    · intro hx
      choose y hy using hx
      exact ⟨y, funext fun i => by rw [Matrix.mulVec_diagonal, mul_comm, hy]⟩
  rw [((Submodule.quotEquivOfEq _ _ h).trans (Submodule.quotientPi _)).length_eq,
    Module.length_pi_of_fintype]
  rfl

private theorem lengthDet_addVal_prod {ι : Type*} (s : Finset ι) (d : ι → O) :
    IsDiscreteValuationRing.addVal O (∏ i ∈ s, d i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal O (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, IsDiscreteValuationRing.addVal_mul, ih]

theorem length_cokernel_eq_addVal_det (Φ : Matrix n n O) :
    Module.length O (H2 Φ) = IsDiscreteValuationRing.addVal O Φ.det := by
  let e : n ≃ Fin (Fintype.card n) := Fintype.equivFin n
  obtain ⟨U, V, d, hU, hV, h, -⟩ := exists_smith _ (Φ.submatrix e.symm e.symm)
  have hΦ : Φ = U.submatrix e e * diagonal (d ∘ e) * V.submatrix e e := by
    rw [← Matrix.submatrix_diagonal_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, ← h]
    ext i j
    simp
  have hU' : IsUnit (U.submatrix e e).det := by rwa [Matrix.det_submatrix_equiv_self]
  have hV' : IsUnit (V.submatrix e e).det := by rwa [Matrix.det_submatrix_equiv_self]
  rw [hΦ, lengthDet_unit_mul _ _ _ hU' hV', lengthDet_diagonal, Matrix.det_mul, Matrix.det_mul,
    IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_eq_zero_iff.2 hU',
    IsDiscreteValuationRing.addVal_eq_zero_iff.2 hV', zero_add, add_zero, Matrix.det_diagonal,
    lengthDet_addVal_prod]
  exact Finset.sum_congr rfl fun i _ => Ring.ord_eq_addVal _

end KStar.Selmer
