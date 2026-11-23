module

public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

theorem BlowUpChart.comap_eq_maximalIdeal {A K : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] {n : ℕ} {x : Fin n → A}
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal A) {i : Fin n} (hi : x i ≠ 0)
    (P : Ideal (blowUpChart A K x i)) (hP : P.IsPrime) (hxP : algebraMap A _ (x i) ∈ P) :
    P.comap (algebraMap A (blowUpChart A K x i)) = IsLocalRing.maximalIdeal A := by
  apply le_antisymm
  · exact IsLocalRing.le_maximalIdeal (Ideal.IsPrime.comap (algebraMap A (blowUpChart A K x i)) (hK := hP)).ne_top
  · rw [← hx, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    have hxi : algebraMap A K (x i) ≠ 0 := by
      rw [map_ne_zero_iff _ (IsFractionRing.injective A K)]
      exact hi
    have hmem : algebraMap A K (x j) / algebraMap A K (x i) ∈ blowUpChart A K x i :=
      Algebra.subset_adjoin ⟨j, rfl⟩
    have hfac : algebraMap A (blowUpChart A K x i) (x j) =
        ⟨_, hmem⟩ * algebraMap A (blowUpChart A K x i) (x i) := by
      apply Subtype.ext
      simp [div_mul_cancel₀ _ hxi]
    show algebraMap A _ (x j) ∈ P
    rw [hfac]
    exact P.mul_mem_left _ hxP

theorem BlowUpChart.equiv :
    _root_.GroundTheory.Heights₂.Heights.Model.BlowUpChart.Statement ↔
      _root_.GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.BlowUpChart.Statement := by
  constructor
  · intro h A K _ _ _ _ _ _ _ n x hx hne
    obtain ⟨i, hi, hu, -⟩ := h A K n x hx hne
    exact ⟨i, hi, hu, fun P hP hxP => BlowUpChart.comap_eq_maximalIdeal hx hi P hP hxP⟩
  · intro h A _ _ _ _ K _ _ _ n x hx hne
    obtain ⟨i, hi, hu, -⟩ := h A K n x hx hne
    have hne' : Ideal.span {algebraMap A (blowUpChart A K x i) (x i)} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]
      exact hu
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne'
    exact ⟨i, hi, hu, Q, hQ.isPrime, hle (Ideal.subset_span rfl),
      BlowUpChart.comap_eq_maximalIdeal hx hi Q hQ.isPrime (hle (Ideal.subset_span rfl))⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
