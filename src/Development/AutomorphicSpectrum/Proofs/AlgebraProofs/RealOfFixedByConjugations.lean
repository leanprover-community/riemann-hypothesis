module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Determinant

@[expose] public section

open NumberField TensorProduct

namespace GlobalTheory.CompanionTheory.UnimodularBaseChange

theorem bijective_baseChange :
    ∀ (Z : Type) [CommRing Z] (L : Type) [AddCommGroup L] [Module.Finite ℤ L] [Module.Free ℤ L]
      (B : LinearMap.BilinForm ℤ L), Function.Bijective B →
      Function.Bijective (B.baseChange Z) := by
  intro Z _ L _ _ _ B hB
  classical
  let b := Module.Free.chooseBasis ℤ L
  let c := b.baseChange Z
  have h1 : IsUnit (LinearMap.toMatrix b b.dualBasis B).det :=
    LinearEquiv.isUnit_det (LinearEquiv.ofBijective B hB) b b.dualBasis
  have h2 : LinearMap.toMatrix c c.dualBasis (B.baseChange Z) =
      (algebraMap ℤ Z).mapMatrix (LinearMap.toMatrix b b.dualBasis B) := by
    ext i j
    simp [c, LinearMap.toMatrix_apply, Module.Basis.baseChange_apply]
  have h3 : IsUnit (LinearMap.toMatrix c c.dualBasis (B.baseChange Z)).det := by
    rw [h2, ← RingHom.map_det]
    exact h1.map _
  exact (LinearEquiv.ofIsUnitDet h3).bijective

end GlobalTheory.CompanionTheory.UnimodularBaseChange
