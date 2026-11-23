module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.Anisotropic
public import Formalism.PeriodIntegrals.WittExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.EnlargeStep
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.Nondeg
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PI.Witt

theorem witt_of (h1 : OneVector) (h2 : Anisotropic) : PI.WittExtension := by
  intro K V _ _ _ _ _ _ B hB hnd
  have key : ∀ (m : ℕ) (U : Submodule K V), Module.finrank K V - Module.finrank K U = m →
      ∀ f : U →ₗ[K] V, Function.Injective f → (∀ x y : U, B (f x) (f y) = B x y) →
      ∃ g : V ≃ₗ[K] V, (∀ x y, B (g x) (g y) = B x y) ∧ ∀ x : U, g x = f x := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro U hm f hinj hf
    by_cases hU : ∀ x ∈ U, (∀ y ∈ U, B x y = 0) → x = 0
    · obtain ⟨g, hg, hge, -⟩ := nondeg_extend h1 h2 B hB _ U rfl hU f hf
      exact ⟨g, hg, hge⟩
    · push Not at hU
      obtain ⟨r, hrU, hr, hr0⟩ := hU
      obtain ⟨U', hlt, f', hinj', hf', hext⟩ := enlarge_step B hB hnd U f hinj hf r hrU hr0 hr
      have h3 : Module.finrank K U < Module.finrank K U' := Submodule.finrank_lt_finrank_of_lt hlt
      have h4 : Module.finrank K U' ≤ Module.finrank K V := Submodule.finrank_le U'
      obtain ⟨g, hg, hge⟩ := ih (Module.finrank K V - Module.finrank K U') (by omega) U' rfl f' hinj' hf'
      refine ⟨g, hg, fun x => ?_⟩
      rw [← hext x, ← hge]
  intro U f hinj hf
  exact key _ U rfl f hinj hf

end PI.Witt
