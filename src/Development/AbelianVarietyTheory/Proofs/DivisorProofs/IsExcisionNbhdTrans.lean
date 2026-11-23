module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem isExcisionNbhd_trans :
    ∀ (A A' A'' : Type) [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A'] [Algebra A' A''] [Algebra A A'']
      [IsScalarTower A A' A''] (h : A), IsExcisionNbhd A A' h → IsExcisionNbhd A' A'' (algebraMap A A' h) →
        IsExcisionNbhd A A'' h := by
  intro A A' A'' _ _ _ _ _ _ _ h h1 h2
  obtain ⟨e1, s1, i1⟩ := h1
  obtain ⟨e2, s2, i2⟩ := h2
  have hsc : ∀ x : A, algebraMap A A'' x = algebraMap A' A'' (algebraMap A A' x) :=
    fun x => IsScalarTower.algebraMap_apply A A' A'' x
  refine ⟨Algebra.Etale.comp A A' A'', ?_, ?_⟩
  · intro a''
    obtain ⟨a', ha'⟩ := s2 a''
    obtain ⟨a, ha⟩ := s1 a'
    refine ⟨a, ?_⟩
    rw [Ideal.mem_span_singleton] at ha ha' ⊢
    obtain ⟨c, hc⟩ := ha
    have key : a'' - algebraMap A A'' a = (a'' - algebraMap A' A'' a') +
        algebraMap A' A'' (algebraMap A A' h) * algebraMap A' A'' c := by
      rw [← map_mul, ← hc, map_sub, hsc]
      ring
    rw [key, hsc]
    exact dvd_add ha' (dvd_mul_right _ _)
  · intro a ha
    rw [hsc, hsc] at ha
    exact i1 a (i2 _ ha)

end GlobalTheory.EtC
