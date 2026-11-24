module

public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerAdditivityDegreeZero
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleGr
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RulePos
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.VanishingBelowDimensionRule
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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

open IsLocalRing Filter

theorem UB.ann_sup_le_ann {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
    (F : GMod B R k) (s : R) (d : Deg k) : F.Ann ⊔ Ideal.span {s} ≤ (F.ann s d).Ann := by
  refine sup_le ?_ ?_
  · intro a ha
    refine Module.mem_annihilator.mpr fun x => ?_
    have hx : ∀ x : LinearMap.ker (LinearMap.lsmul R F.M s), a • x = 0 :=
      fun x => Subtype.ext (Module.mem_annihilator.mp ha x.1)
    exact hx x
  · rw [Ideal.span_singleton_le_iff_mem]
    refine Module.mem_annihilator.mpr fun x => ?_
    have hx : ∀ x : LinearMap.ker (LinearMap.lsmul R F.M s), s • x = 0 :=
      fun x => Subtype.ext x.2
    exact hx x


open E4 in
theorem ruleUB : RuleUB := by
  intro k X ts us
  induction ts with
  | nil =>
    intro F _ _ _
    exact Eventually.of_forall fun m => le_rfl
  | cons p ts ih =>
    obtain ⟨d, s⟩ := p
    intro F hv hF hA
    have hv' : Valid X.𝒜 (ts ++ us) := fun p hp => hv p (List.mem_cons_of_mem _ hp)
    have hs : s ∈ X.𝒜 d := (hv (d, s) List.mem_cons_self).2
    have hA' : admitted X.𝒜 (ts ++ us) (F.Ann ⊔ Ideal.span {s}) := admissible_tail_of_cons_mem X.𝒜 hA
    obtain ⟨g1, g2⟩ := (ruleGr k X F hF).2.2 d s hs
    have h1 := ih (F.quot s) hv' g1 (admissible_mono_ideal X.𝒜 (ann_sup_le_quot F s) hA')
    have h2 := rulePos k X (ts ++ us) (F.ann s d) hv' g2 (admissible_mono_ideal X.𝒜 (UB.ann_sup_le_ann F s d) hA')
    filter_upwards [h1, h2] with m a b
    show chi (ts ++ us) (F.quot s) m - chi (ts ++ us) (F.ann s d) m ≤ chi us ((F.quot s).quots ts) m
    linarith

end Formalism.MainNotions.V.Pf.V2.Calc
