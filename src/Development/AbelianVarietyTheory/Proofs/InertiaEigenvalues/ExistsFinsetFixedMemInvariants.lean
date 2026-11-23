module

public import Formalism.WeaklyAdmissibleFiltrations.Statement
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

namespace GlobalTheory.FixedFinsetInvariants

theorem exists_finset_fixed_mem_invariants {G LL V : Type} [Group G] [Field LL] [AddCommGroup V]
    [Module LL V] [FiniteDimensional LL V] (ρ : Representation LL G V) :
    ∃ s : Finset G, ∀ v : V, (∀ g ∈ s, ρ g v = v) → v ∈ Formalism.WeaklyAdmissibleFiltrations.H0V ρ := by
  classical
  let F : Finset G → Submodule LL V := fun s => ⨅ g ∈ s, LinearMap.ker (ρ g - LinearMap.id)
  have hF : ∀ (s : Finset G) (v : V), v ∈ F s ↔ ∀ g ∈ s, ρ g v = v := by
    intro s v
    simp only [F, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
  obtain ⟨_, ⟨s, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule LL V)).has_min (Set.range F) ⟨F ∅, ∅, rfl⟩
  refine ⟨s, fun v hv => ?_⟩
  unfold Formalism.WeaklyAdmissibleFiltrations.H0V
  rw [Submodule.mem_iInf]
  intro g
  have hle : F (insert g s) ≤ F s := by
    intro w hw
    rw [hF] at hw ⊢
    exact fun h hh => hw h (Finset.mem_insert_of_mem hh)
  have heq : F (insert g s) = F s := by
    by_contra hne
    exact hmin _ ⟨insert g s, rfl⟩ (lt_of_le_of_ne hle hne)
  have hv' : v ∈ F (insert g s) := heq ▸ (hF s v).2 hv
  have hg := (hF _ v).1 hv' g (Finset.mem_insert_self g s)
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  exact hg

end GlobalTheory.FixedFinsetInvariants
