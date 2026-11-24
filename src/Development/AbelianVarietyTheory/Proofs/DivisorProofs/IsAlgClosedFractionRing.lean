module

import Development.EtaleCohomology.EtaleSheaves.DomOpenPf
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

open Polynomial

namespace GlobalTheory.FractionRingRootRange

theorem root_mem_range {A B : Type} [CommRing A] [Nontrivial A] [CommRing B] [IsDomain B] [Algebra A B]
    (h : GlobalTheory.EtC.AIC A) (z : B) :
    ∀ (n : ℕ) (p : A[X]), p.natDegree = n → p.Monic → aeval z p = 0 → ∃ a : A, algebraMap A B a = z := by
  intro n
  induction n with
  | zero =>
    intro p hdeg hmon hz
    rw [Polynomial.eq_one_of_monic_natDegree_zero hmon hdeg, map_one] at hz
    exact absurd hz one_ne_zero
  | succ n ih =>
    intro p hdeg hmon hz
    obtain ⟨a, ha⟩ := h p hmon (by omega)
    have hmul : (X - C a) * (p /ₘ (X - C a)) = p := mul_divByMonic_eq_iff_isRoot.mpr ha
    have hqmon : (p /ₘ (X - C a)).Monic :=
      (monic_X_sub_C a).of_mul_monic_left (by rw [hmul]; exact hmon)
    have hqdeg : (p /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic p (monic_X_sub_C a), natDegree_X_sub_C, hdeg]
      omega
    rw [← hmul, map_mul] at hz
    simp only [map_sub, aeval_X, aeval_C] at hz
    rcases mul_eq_zero.mp hz with h1 | h1
    · exact ⟨a, (sub_eq_zero.mp h1).symm⟩
    · exact ih _ hqdeg hqmon h1

theorem isAlgClosed_fractionRing (A : Type) [CommRing A] [IsDomain A] (h : GlobalTheory.EtC.AIC A) :
    IsAlgClosed (FractionRing A) := by
  apply LateralTheory.E.DomOpenPf.algClosed_of_AIC <;> assumption

end GlobalTheory.FractionRingRootRange
