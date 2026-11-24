module

public import Formalism.PairingDivisors.StatementH
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ProdFormula
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)

namespace Formalism.PairingDivisionLocalBalance

theorem vw_prod {K : Type} [Field K] [NumberField K] [StarRing K] (w : Pl K) {P : Type} (R : Finset P)
    (e : P → K) (he : ∀ q ∈ R, e q ≠ 0) : vw w (∏ q ∈ R, e q) = ∑ q ∈ R, vw w (e q) := by
  classical
  induction R using Finset.induction_on with
  | empty => simp [Formalism.DivisionValues.ValuationRepresentative.vw_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (he a (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr fun q hq => he q (Finset.mem_insert_of_mem hq)),
      ih fun q hq => he q (Finset.mem_insert_of_mem hq)]

theorem sum_valuation_nat : SumValNat := by
  intro K _ _ _ _ n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Formalism.DivisionValues.ValuationRepresentative.vw_zero]
  · have hn0 : (n : K) ≠ 0 := by exact_mod_cast hn.ne'
    obtain ⟨h1, h2⟩ := Formalism.DivisionValues.prod_formula' K (n : K) hn0
    refine ⟨h1, ?_⟩
    rw [← h2]
    have hc : (Fintype.card (InfinitePlace K) : ℝ) * 2 = (finrank ℚ K : ℝ) := by
      have h3 := IsTotallyComplex.finrank K
      have h4 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
      have h5 := IsTotallyComplex.nrRealPlaces_eq_zero K
      rw [h3, h4, h5]; push_cast; ring
    have hpos : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
    simp only [map_natCast, Complex.norm_natCast, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hc]
    have : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hc; linarith
    field_simp

end Formalism.PairingDivisionLocalBalance
