module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
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

@[expose] public section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.SurjPass

theorem aic_of_surjective {S : Type} [CommRing S] {T : Type} [CommRing T] (φ : S →+* T)
    (hφ : Function.Surjective φ) (h : Aic (S := S)) : Aic (S := T) := by
  intro P hP hdeg
  rcases subsingleton_or_nontrivial T with hT | hT
  · exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨Q, hQ, hQdeg, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.lifts_iff_coeff_lifts P).mpr fun n => hφ (P.coeff n)) hP
  obtain ⟨x, hx⟩ := h Q hQm (hQdeg ▸ hdeg)
  refine ⟨φ x, ?_⟩
  rw [← hQ, Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_hom, hx.eq_zero, map_zero]

theorem comparable_of_surjective {S : Type} [CommRing S] {T : Type} [CommRing T] (φ : S →+* T)
    (hφ : Function.Surjective φ) (h : Val0 (S := S)) : Val0 (S := T) := by
  intro f g
  obtain ⟨f', rfl⟩ := hφ f
  obtain ⟨g', rfl⟩ := hφ g
  obtain ⟨e, he, h1, h2⟩ := h f' g'
  refine ⟨φ e, ?_, ?_, ?_⟩
  · unfold IsIdempotentElem
    rw [← map_mul, he.eq]
  · rw [Ideal.mem_span_singleton] at h1 ⊢
    rw [← map_mul]
    exact map_dvd φ h1
  · rw [Ideal.mem_span_singleton] at h2 ⊢
    rw [← map_one φ, ← map_sub, ← map_mul]
    exact map_dvd φ h2

theorem absolutely_closed_comparable_surjective : ∀ {S : Type} [CommRing S] {T : Type} [CommRing T] (φ : S →+* T),
    Function.Surjective φ → (Aic (S := S) → Aic (S := T)) ∧ (Val0 (S := S) → Val0 (S := T)) := by
  intro S _ T _ φ hφ
  exact ⟨aic_of_surjective φ hφ, comparable_of_surjective φ hφ⟩

end GlobalTheory.CompanionTheory.SurjPass
