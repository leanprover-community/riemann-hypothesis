module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFrobeniusTwistBijectiveRelFrobenius
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.dieudonne_frobeniusTwist_bijective_relFrobenius :
    ∀ (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Dieu.Base p fun _ _ _ => True)
      (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k),
      Function.Bijective (B.smap trivial trivial (frobProj (p_eq_zero p k) G)) ∧
      (∀ m, B.map trivial trivial (relFrob (p_eq_zero p k) G)
        (B.smap trivial trivial (frobProj (p_eq_zero p k) G) m) = B.F G trivial m) ∧
      ∀ m n, B.smap trivial trivial (frobProj (p_eq_zero p k) G) n =
        B.map trivial trivial (verschiebung (p_eq_zero p k) G) m →
        B.F G trivial n = p • m :=
  @GlobalTheory.Dieu.frobTwist_module
