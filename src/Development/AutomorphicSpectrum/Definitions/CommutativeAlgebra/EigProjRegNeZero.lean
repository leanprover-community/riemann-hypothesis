module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
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
import Mathlib.RingTheory.PiTensorProduct
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

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.LatTest

open Module NumberField TensorProduct

section Norms

variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]

end Norms

section Eigen

variable {A : Type} [CommRing A] {K : Type} [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]

theorem trace_dualInt (k j) :
    Algebra.trace ℚ E (dualInt E k * integralBasis E j) = if j = k then 1 else 0 := by
  classical
  have := LinearMap.BilinForm.apply_dualBasis_left (B := Algebra.traceForm ℚ E)
    (traceForm_nondegenerate ℚ E) (integralBasis E) k j
  rw [Algebra.traceForm_apply] at this
  convert this using 1
  rfl

theorem expand_dual (x : E) :
    x = ∑ k, Algebra.trace ℚ E (x * integralBasis E k) • dualInt E k := by
  classical
  have h := ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E)
    (integralBasis E)).sum_repr x
  simp only [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply] at h
  exact h.symm

theorem repr_eq_trace (a : 𝓞 E) (k) :
    (((RingOfIntegers.basis E).repr a k : ℤ) : ℚ) = Algebra.trace ℚ E (dualInt E k * (a : E)) := by
  classical
  conv_rhs => rw [← (RingOfIntegers.basis E).sum_repr a]

  simp only [map_sum, RingOfIntegers.coe_eq_algebraMap, Finset.mul_sum, map_zsmul, mul_smul_comm,
  ← integralBasis_apply, trace_dualInt]
  simp

end Eigen

section Further

variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]

end Further

section FurtherEigen

variable {A : Type} [CommRing A] {K : Type} [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]


end FurtherEigen

end GlobalTheory.CompanionTheory.Ar.HT.LatTest
