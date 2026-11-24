module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIdeal
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffNormFormOfFamilyMemRangeIntegrallyClosed
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
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.coeff_normFormOfFamily_mem_range_integrallyClosed : ∀ (A K L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Field L] [Algebra A K]
    [IsFractionRing A K] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L] {m : ℕ}
    (x : Fin m → L), (∀ i, IsIntegral A (x i)) →
    ∀ s, (GlobalTheory.NormSheaf.normForm K L x).coeff s ∈ (algebraMap A K).range := by
  first | exact @GlobalTheory.NormSheaf.IntegralCoeff.coeff_normForm_mem_range | exact GlobalTheory.NormSheaf.IntegralCoeff.coeff_normForm_mem_range | (intros; apply GlobalTheory.NormSheaf.IntegralCoeff.coeff_normForm_mem_range <;> assumption)
