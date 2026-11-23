module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.DatExOf
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DiscriminantMulIntegralMem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

theorem UpperTheory.Reformulated.B.Qk39.pDiscInt :
    UpperTheory.Gal.G1.DiscInt := by
  intro E _ _ _ A y hy
  have h1 := congrArg (fun x : NumberField.RingOfIntegers E => (x : E)) A.tr_eq
  have h2 := congrArg (fun x : NumberField.RingOfIntegers E => (x : E)) A.nm_eq
  simp only [map_add (f := _), map_mul, map_intCast] at h1 h2
  obtain ⟨a, b, h⟩ := UpperTheory.discriminant_mul_integral_mem E (UpperTheory.Gal.W2.Seed.cj E) (A.ω : E) (y : E) A.tr A.nm
    (by rw [← h1]; exact congrArg _ (A.bar_eq _).symm) (by rw [← h2]; exact congrArg _ (A.bar_eq _).symm)
    (NumberField.RingOfIntegers.isIntegral_coe y) hy
  refine ⟨a, b, NumberField.RingOfIntegers.coe_injective ?_⟩
  simp only [map_add (f := _), map_mul, map_intCast]
  exact h
