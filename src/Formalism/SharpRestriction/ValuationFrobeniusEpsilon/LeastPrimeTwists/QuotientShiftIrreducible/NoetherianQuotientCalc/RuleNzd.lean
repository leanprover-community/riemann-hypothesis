module

public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerVanishingBelowDimension
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

theorem chi_of_subsingleton (ts : List (Deg k × R)) : ∀ (F : GMod B R k), Subsingleton F.M →
    ∀ m, chi ts F m = 0 := by
  induction ts with
  | nil =>
    intro F hF m
    have : Subsingleton (F.gr m) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    simp only [chi]
    rw [Module.length_eq_zero]
    rfl
  | cons p ts ih =>
    obtain ⟨d, s⟩ := p
    intro F hF m
    simp only [chi]
    have h1 : Subsingleton (F.quot s).M :=
      ⟨fun a b => by
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
        rw [Subsingleton.elim x y]⟩
    have h2 : Subsingleton (F.ann s d).M :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim (α := F.M) _ _)⟩
    rw [ih _ h1, ih _ h2, sub_zero]

theorem chi_nzd (ts : List (Deg k × R)) (F : GMod B R k) (d : Deg k) (s : R)
    (h : ∀ x : F.M, s • x = 0 → x = 0) (m : Deg k) :
    chi ((d, s) :: ts) F m = chi ts (F.quot s) m := by
  have h2 : Subsingleton (F.ann s d).M :=
    ⟨fun a b => Subtype.ext ((h a.1 a.2).trans (h b.1 b.2).symm)⟩
  simp only [chi]
  rw [chi_of_subsingleton ts _ h2, sub_zero]

theorem ruleNzd : RuleNzd := fun _ _ ts F d s h m => chi_nzd ts F d s h m

end Formalism.MainNotions.V.Pf.V2.Calc
