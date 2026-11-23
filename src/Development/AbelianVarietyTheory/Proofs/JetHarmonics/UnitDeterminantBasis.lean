module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt

@[expose] public section

open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Pdiv

namespace GlobalTheory.UnitDeterminantBasis

theorem det_ne_zero {k A O : Type} [CommRing k] [CommRing A] [Algebra k A] [CommRing O]
    [Algebra k O] [IsDomain O] {n : ℕ} {e : A}
    (b : Module.Basis (Fin n) k (LinearMap.range (LinearMap.mulLeft k e)))
    (T : Fin n → (A →ₐ[k] O)) (hT : Function.Injective T) (hTe : ∀ j, T j e = 1) :
    (Matrix.of fun i j => T j (b i : A)).det ≠ 0 := by
  intro h
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hc0
  have hli := (linearIndependent_algHom_toLinearMap k A O).comp T hT
  rw [Fintype.linearIndependent_iff] at hli
  funext j
  refine hli c ?_ j
  have h1 : (∑ j, c j • (T j).toLinearMap) ∘ₗ
      (LinearMap.range (LinearMap.mulLeft k e)).subtype = 0 := by
    refine b.ext fun i => ?_
    have := congrFun hc i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    simpa [LinearMap.sum_apply, mul_comm] using this
  ext a
  have h2 := LinearMap.congr_fun h1 ⟨e * a, a, rfl⟩
  simpa [LinearMap.sum_apply, hTe] using h2

end GlobalTheory.UnitDeterminantBasis
