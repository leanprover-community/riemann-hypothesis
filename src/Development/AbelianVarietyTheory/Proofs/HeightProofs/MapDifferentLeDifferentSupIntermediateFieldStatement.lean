module

public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.Topology.Sheaves.Presheaf
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MapDifferentLeDifferentSupIntermediateField
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

theorem _root_.GlobalTheory.T.map_different_le_different_sup_intermediateField : ∀ (F F' : IntermediateField ℚ ℂ) [NumberField F] [NumberField F'] [NumberField ↥(F ⊔ F')], letI : Algebra F ↥(F ⊔ F') := (IntermediateField.inclusion le_sup_left).toRingHom.toAlgebra; (differentIdeal ℤ (𝓞 F')).map (RingOfIntegers.mapRingHom (IntermediateField.inclusion (le_sup_right : F' ≤ F ⊔ F')).toRingHom) ≤ differentIdeal (𝓞 F) (𝓞 ↥(F ⊔ F')) := by
  first | exact @GlobalTheory.DiffBaseChange.map_different_le_sup | exact GlobalTheory.DiffBaseChange.map_different_le_sup | (intros; apply GlobalTheory.DiffBaseChange.map_different_le_sup <;> assumption)
