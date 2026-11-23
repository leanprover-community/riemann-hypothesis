module

public import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

theorem EmultiplicityOrd.proof (h₁ : LocalizationPrimeDVR.Statement) : EmultiplicityOrd.Statement := by
  intro R _ _ _ _ q x p _ hq hp hx
  have : IsDiscreteValuationRing (Localization.AtPrime p) := h₁ R q p hq hp
  set O := Localization.AtPrime p
  have hfin : FiniteMultiplicity q x := FiniteMultiplicity.of_prime_left hq hx
  obtain ⟨y, hxy, hy⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  rw [hfin.emultiplicity_eq_multiplicity]

  have hyu : IsUnit (algebraMap R O y) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff O p y]
    change y ∉ p
    rw [hp, Ideal.mem_span_singleton]
    exact hy

  have hmax : maximalIdeal O = Ideal.span {algebraMap R O q} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p O, congrArg (Ideal.map (algebraMap R O)) hp,
      Ideal.map_span, Set.image_singleton]
  have hirr : Irreducible (algebraMap R O q) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax
  have hnz : algebraMap R O q ∈ nonZeroDivisors O :=
    mem_nonZeroDivisors_of_ne_zero hirr.ne_zero
  conv_rhs => rw [hxy, map_mul, map_pow, Ring.ord_mul_of_isUnit_right hyu, Ring.ord_pow hnz,
    Ring.ord_of_irreducible hirr]
  simp

end GroundTheory.Heights₂.Heights
