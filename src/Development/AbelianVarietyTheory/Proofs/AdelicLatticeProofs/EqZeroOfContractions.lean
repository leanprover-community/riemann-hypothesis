module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

namespace GlobalTheory.CoefficientContraction

theorem coeff_eq_contraction {V W : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W]
    [Module ℚ W] {κ : Type} [DecidableEq κ] (b : Module.Basis κ ℚ W) (i : κ)
    (t : TensorProduct ℚ V W) :
    TensorProduct.equivFinsuppOfBasisRight b t i
      = TensorProduct.rid ℚ V (LinearMap.lTensor V (b.coord i) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul v w => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem eq_zero_of_contractions {V W : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W]
    [Module ℚ W] (t : TensorProduct ℚ V W)
    (h : ∀ m : W →ₗ[ℚ] ℚ, TensorProduct.rid ℚ V (LinearMap.lTensor V m t) = 0) : t = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace ℚ W
  apply (TensorProduct.equivFinsuppOfBasisRight (M := V) b).injective
  ext i
  rw [coeff_eq_contraction, h, map_zero, Finsupp.zero_apply]

end GlobalTheory.CoefficientContraction
