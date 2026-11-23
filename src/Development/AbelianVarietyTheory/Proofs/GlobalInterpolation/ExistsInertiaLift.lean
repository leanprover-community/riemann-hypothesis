module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuationIntegerLeOne
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GaloisValuations.GlobalB
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped nonZeroDivisors

namespace GlobalTheory.CMRam

theorem val_int_le {E Ω : Type*} [Field E] [Field Ω] (ι : E →+* Ω) (A : ValuationSubring Ω) (a : 𝓞 E) :
    A.valuation (ι a) ≤ 1 :=
  (A.valuation_le_one_iff _).2
    (ReciprocityTheory.Gal.mem_of_isIntegral_int A (a.isIntegral_coe.map ι.toIntAlgHom))

theorem exists_den_field {E Ω : Type*} [Field E] [NumberField E] [Field Ω] (ι : E →+* Ω)
    (A : ValuationSubring Ω) {x : E} (hx : A.valuation (ι x) ≤ 1) :
    ∃ s t : 𝓞 E, A.valuation (ι s) = 1 ∧ (s : E) * x = t := by
  first
  | exact @_root_.GlobalTheory.UnitDenominatorValuation.exists_unit_denominator
  | exact _root_.GlobalTheory.UnitDenominatorValuation.exists_unit_denominator
  | (apply _root_.GlobalTheory.UnitDenominatorValuation.exists_unit_denominator <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitDenominatorValuation.exists_unit_denominator <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitDenominatorValuation.exists_unit_denominator <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitDenominatorValuation.exists_unit_denominator ..)

end GlobalTheory.CMRam
