module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsMChart
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocDim
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]


omit [DecidableEq K] in
theorem finiteType_quotient_mRing (I : Ideal (MRing ι F)) : Algebra.FiniteType F (MRing ι F ⧸ I) :=
  Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F I) (Ideal.Quotient.mkₐ_surjective F I)


omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem chartMonomial_not_mem (Q : Ideal (MRing ι F)) [Q.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ Q) (b : K → ℕ) : chartMonomial u b ∉ Q := by
  unfold chartMonomial
  intro h
  obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  exact hu k (Ideal.IsPrime.mem_of_pow_mem ‹_› _ hk)

theorem chart_ringKrullDim_add_card (h : MChartTrdeg.Statement.{u}) (Q : Ideal (MRing ι F)) [Q.IsPrime]
    (hQ : IsMultiHomogIdeal Q) (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ Q) :
    ringKrullDim (MRing ι F ⧸ chartIdeal Q u) + Fintype.card K = ringKrullDim (MRing ι F ⧸ Q) := by
  have := finiteType_quotient_mRing (F := F) (chartIdeal Q u)
  have := finiteType_quotient_mRing (F := F) Q
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F,
    GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F (A := MRing ι F ⧸ Q), ← h F K ι Q hQ u hu,
    map_add, map_natCast]
  norm_cast

end

theorem DegZeroLocDim.proof (h₁ : MChartHomog.Statement.{u}) (h₂ : MChartTrdeg.Statement.{u})
    (h₃ : MChartLocDim.Statement.{u}) : DegZeroLocDim.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW
  have := hP.isPrime
  have := hW.isPrime
  choose u hu using hW.relevant
  have huP : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P := fun k hk => hu k (hPW hk)
  have hle : chartIdeal P u ≤ chartIdeal W u := by
    intro p hp
    obtain ⟨b, h, -, hh⟩ := h₁ F K ι u p
    simp only [chartIdeal, RingHom.mem_ker] at hp ⊢
    rw [hh P huP, div_eq_zero_iff, IsFractionRing.to_map_eq_zero_iff,
      IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.Quotient.eq_zero_iff_mem] at hp
    have hW' : h ∈ W := by
      rcases hp with hp | hp
      · exact hPW hp
      · exact absurd hp (chartMonomial_not_mem P u huP b)
    rw [hh W hu, IsFractionRing.to_map_eq_zero_iff.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr hW'), zero_div]
  have : ((chartIdeal W u).map (Ideal.Quotient.mk (chartIdeal P u))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hle)
  have := finiteType_quotient_mRing (F := F) (chartIdeal P u)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient (k := F)
    ((chartIdeal W u).map (Ideal.Quotient.mk (chartIdeal P u)))
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)] at hform
  show ringKrullDim (degZeroLoc P {W}) + ringKrullDim (MRing ι F ⧸ W) = ringKrullDim (MRing ι F ⧸ P)
  rw [h₃ F K ι P W hPW u hu, ← chart_ringKrullDim_add_card h₂ W hW.multiHomog u hu,
    ← chart_ringKrullDim_add_card h₂ P hP.multiHomog u huP, ← hform, add_assoc]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
