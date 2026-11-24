module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.FieldSize

theorem sz_fieldRange_embedding (K : Type) [Field K] [NumberField K] (φ : K →+* ℂ) :
    Sz φ.toRatAlgHom.fieldRange (Real.log (Module.finrank ℚ K))
      (Real.log |((discr K : ℤ) : ℝ)| / Module.finrank ℚ K) := by
  let e : K ≃ₐ[ℚ] φ.toRatAlgHom.fieldRange := AlgEquiv.ofInjectiveField φ.toRatAlgHom
  have hfd : FiniteDimensional ℚ φ.toRatAlgHom.fieldRange := e.toLinearEquiv.finiteDimensional
  refine ⟨hfd, ?_⟩
  let _ : NumberField φ.toRatAlgHom.fieldRange := NumberField.mk
  have h1 : Module.finrank ℚ φ.toRatAlgHom.fieldRange = Module.finrank ℚ K := e.toLinearEquiv.finrank_eq.symm
  have h2 : discr φ.toRatAlgHom.fieldRange = discr K := (NumberField.discr_eq_discr_of_algEquiv K e).symm
  rw [h1, h2]
  exact ⟨le_rfl, le_rfl⟩

end GlobalTheory.FieldSize
