module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerMore
public import Mathlib.RingTheory.Ideal.Height
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSuppA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPCProof

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RegularityDivisorSupportClosed.le_of_height_map_eq_zero {A : Type*} [CommRing A] {P Q : Ideal A} [P.IsPrime]
    (h : (Q.map (Ideal.Quotient.mk P)).height = 0) : Q ≤ P := by
  intro x hx
  rw [Ideal.height_eq_zero_iff_eq_bot] at h
  have : Ideal.Quotient.mk P x ∈ Q.map (Ideal.Quotient.mk P) := Ideal.mem_map_of_mem _ hx
  rwa [h, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this

theorem RegularityDivisorSupportClosed.not_add_add {m : ℕ} {a b : ℕ∞} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ((m : WithBot ℕ∞) + (a : WithBot ℕ∞)) + (b : WithBot ℕ∞) = ((m + 1 : ℕ) : WithBot ℕ∞)) :
    False := by
  have h' : (m : ℕ∞) + a + b = ((m + 1 : ℕ) : ℕ∞) := by exact_mod_cast h
  induction a using ENat.recTopCoe with
  | top => simp at h'; exact ENat.natCast_ne_top (m + 1) (by exact_mod_cast h'.symm)
  | coe a =>
    induction b using ENat.recTopCoe with
    | top => simp at h'; exact ENat.natCast_ne_top (m + 1) (by exact_mod_cast h'.symm)
    | coe b =>
      have : m + a + b = m + 1 := by exact_mod_cast h'
      have : a ≠ 0 := by exact_mod_cast ha
      have : b ≠ 0 := by exact_mod_cast hb
      omega

theorem RegularityDivisorSupportClosed.proof : RegularityDivisorSupportClosed.Statement := by
  intro K _ ι _ P s a W hP hs hsP
  obtain ⟨-, ⟨hPp, hPh, -⟩, -, hPdim⟩ := hP
  have := hPp
  have hsW' : ∀ {Q : Ideal (MRing ι)}, P ⊔ Ideal.span {s} ≤ Q → s ∈ Q := fun h =>
    h (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  constructor
  · rintro ⟨hWmin, hWrel⟩
    have h1 := dim_quot_minimal_add_one P W s hsP hWmin
    rw [hPdim] at h1
    refine ⟨⟨⟨hWmin.1.1, isMultiHomogIdeal_of_mem_minimalPrimes hPh hs hWmin, hWrel⟩,
      withBot_eq_of_add_one (by rw [h1, Nat.add_comm])⟩, le_sup_left.trans hWmin.1.2, hsW' hWmin.1.2⟩
  · rintro ⟨⟨⟨hWp, -, hWrel⟩, hWdim⟩, hPW, hsW⟩
    have hle : P ⊔ Ideal.span {s} ≤ W := sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hsW)
    refine ⟨⟨⟨hWp, hle⟩, fun Q hQ hQW => ?_⟩, hWrel⟩
    have := hQ.1
    have hPQ : P ≤ Q := le_sup_left.trans hQ.2
    have e1 := mvPolynomialInt_dimFormula P Q hPQ
    have e2 := mvPolynomialInt_dimFormula Q W hQW
    rw [hPdim] at e1
    rw [hWdim] at e2
    by_contra hWQ
    have ha : (W.map (Ideal.Quotient.mk Q)).height ≠ 0 := fun h0 =>
      hWQ (RegularityDivisorSupportClosed.le_of_height_map_eq_zero h0)
    have hb : (Q.map (Ideal.Quotient.mk P)).height ≠ 0 := fun h0 =>
      hsP (RegularityDivisorSupportClosed.le_of_height_map_eq_zero h0 (hsW' hQ.2))
    rw [← e2] at e1
    exact RegularityDivisorSupportClosed.not_add_add ha hb (by rw [e1, Nat.add_comm])

end

end GroundTheory.Heights₂.Heights.Inter
