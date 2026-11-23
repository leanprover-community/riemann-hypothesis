module

public import GroundTheory.ProfiniteCohomology.ContinuousCochains
public import Mathlib.GroupTheory.Torsion
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

universe u

variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

noncomputable def cdp : ℕ∞ :=
  sInf {n : ℕ∞ | ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A], IsAddTorsion A →
    ∀ q : ℕ, n < q → AddCommGroup.primaryComponent (cohomology A q) p = ⊥}

variable {p G}

theorem cdp_le_iff {n : ℕ∞} :
    cdp p G ≤ n ↔ ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A], IsAddTorsion A →
      ∀ q : ℕ, n < q → AddCommGroup.primaryComponent (cohomology A q) p = ⊥ := by
  refine ⟨fun h A _ hA q hq => ?_, fun h => sInf_le h⟩
  obtain ⟨m, hm, hmq⟩ := sInf_lt_iff.1 (h.trans_lt hq)
  exact hm A hA q hmq

theorem primaryComponent_cohomology_eq_bot_of_cdp_lt (A : Rep.{u} (ULift.{u} ℤ) G)
    [IsDiscreteRep A] (hA : IsAddTorsion A) {q : ℕ} (hq : cdp p G < q) :
    AddCommGroup.primaryComponent (cohomology A q) p = ⊥ :=
  cdp_le_iff.1 le_rfl A hA q hq

end GroundTheory.ProfCoh
