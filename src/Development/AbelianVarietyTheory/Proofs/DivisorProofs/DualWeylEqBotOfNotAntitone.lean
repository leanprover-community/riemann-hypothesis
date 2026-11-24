module

public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylNonDom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.NonDomZero

theorem exists_lt_lt_of_not_antitone {N : ℕ} {ν : Fin N → ℕ} (hν : ¬ Antitone ν) :
    ∃ a b : Fin N, a < b ∧ ν a < ν b := by
  simp only [Antitone, not_forall] at hν
  obtain ⟨a, b, hab, hlt⟩ := hν
  refine ⟨a, b, lt_of_le_of_ne hab ?_, lt_of_not_ge hlt⟩
  rintro rfl
  exact hlt le_rfl

theorem dualWeyl_eq_bot_of_not_antitone :
    ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ) (ν : Fin N → ℕ),
      ¬ Antitone ν → Formalism.GradedWeylDivisibility.dualWeyl O N N ν = ⊥ := by
  intro O _ _ _ N ν hν
  exact Formalism.GradedWeylDivisibility.dualWeylModuleNonDominant O N N ν (exists_lt_lt_of_not_antitone hν)

end GlobalTheory.NonDomZero
