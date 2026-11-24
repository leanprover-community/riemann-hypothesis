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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.MonicSplit

open Polynomial

theorem exists_multiset_of_natDegree_eq {S : Type} [CommRing S] (hS : Aic (S := S)) (d : ℕ) :
    ∀ P : Polynomial S, P.Monic → P.natDegree = d →
      ∃ s : Multiset S, P = (s.map fun b => X - C b).prod := by
  rcases subsingleton_or_nontrivial S with hS' | hS'
  · intro P _ _
    exact ⟨0, Subsingleton.elim _ _⟩
  · induction d with
    | zero =>
      intro P hP hd
      refine ⟨0, ?_⟩
      rw [Multiset.map_zero, Multiset.prod_zero]
      exact Polynomial.eq_one_of_monic_natDegree_zero hP hd
    | succ d ih =>
      intro P hP hd
      obtain ⟨x, hx⟩ := hS P hP (by omega)
      have hmul : (X - C x) * (P /ₘ (X - C x)) = P := Polynomial.mul_divByMonic_eq_iff_isRoot.2 hx
      have hQ : (P /ₘ (X - C x)).Monic :=
        Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C x) (by rw [hmul]; exact hP)
      have hQd : (P /ₘ (X - C x)).natDegree = d := by
        have h := (Polynomial.monic_X_sub_C x).natDegree_mul hQ
        rw [hmul, Polynomial.natDegree_X_sub_C, hd] at h
        omega
      obtain ⟨s, hs⟩ := ih _ hQ hQd
      refine ⟨x ::ₘ s, ?_⟩
      rw [Multiset.map_cons, Multiset.prod_cons, ← hs, hmul]

theorem monic_splits : ∀ {S : Type} [CommRing S], Aic (S := S) → ∀ P : Polynomial S, P.Monic →
    ∃ s : Multiset S, P = (s.map fun b => Polynomial.X - Polynomial.C b).prod := by
  intro S _ hS P hP
  exact exists_multiset_of_natDegree_eq hS _ P hP rfl

end GlobalTheory.CompanionTheory.MonicSplit
