module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoePolyMapX
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.GraphLocal

theorem flat_polyMap_of_flat_aeval : ∀ {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ'] (A : Subalgebra ℂ K)
    (m : ℕ) (v : Fin m → A),
    (MvPolynomial.aeval v : MvPolynomial (Fin m) ℂ →ₐ[ℂ] A).toRingHom.Flat →
    (polyMap (κ' := κ') A v).Flat := by
  intro K κ' _ _ _ _ A m v h
  have h1 : (Algebra.TensorProduct.map (AlgHom.id ℂ κ')
      (MvPolynomial.aeval v : MvPolynomial (Fin m) ℂ →ₐ[ℂ] A)).toRingHom.Flat :=
    RingHom.Flat.tensorProductMap (f := AlgHom.id ℂ κ') (RingHom.Flat.id κ') h
  let e1 := (MvPolynomial.algebraTensorAlgEquiv (σ := Fin m) ℂ κ').symm.toRingEquiv
  let e2 := ((Algebra.TensorProduct.comm ℂ κ' A).trans (tensEquiv (κ' := κ') A)).toRingEquiv
  have h2 := ((RingHom.Flat.of_bijective (f := e1.toRingHom) e1.bijective).comp h1).comp
    (RingHom.Flat.of_bijective (f := e2.toRingHom) e2.bijective)
  convert h2 using 1
  refine MvPolynomial.ringHom_ext (fun b => Subtype.ext ?_) (fun i => Subtype.ext ?_)
  · have : (MvPolynomial.algebraTensorAlgEquiv (σ := Fin m) ℂ κ').symm (MvPolynomial.C b)
        = b ⊗ₜ 1 := by
      rw [AlgEquiv.symm_apply_eq]; simp [MvPolynomial.algebraTensorAlgEquiv_tmul, MvPolynomial.smul_eq_C_mul]
    simp [e1, e2, tensMap, this]
  · simp [e1, e2, tensMap]

end GlobalTheory.GraphLocal
