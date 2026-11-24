module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

namespace GlobalTheory.TraceOnInjectiveMap

theorem trOn_map_of_injective {X V : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
    (j : X →ₗ[ℂ] V) (hj : Function.Injective j) (M : Submodule ℂ X) (L' : X →ₗ[ℂ] X) (L : V →ₗ[ℂ] V)
    (hL : ∀ x ∈ M, L (j x) = j (L' x)) :
    GlobalTheory.BCT.trOn (Submodule.map j M) L = GlobalTheory.BCT.trOn M L' := by
  have hpres : (∀ v ∈ Submodule.map j M, L v ∈ Submodule.map j M) ↔ ∀ x ∈ M, L' x ∈ M := by
    constructor
    · intro h x hx
      obtain ⟨y, hy, hyx⟩ := h (j x) ⟨x, hx, rfl⟩
      rw [hL x hx] at hyx
      exact hj hyx ▸ hy
    · rintro h _ ⟨x, hx, rfl⟩
      exact ⟨L' x, h x hx, (hL x hx).symm⟩
  unfold GlobalTheory.BCT.trOn
  by_cases h' : ∀ x ∈ M, L' x ∈ M
  · rw [dite_eq_left (hpres.2 h'), dite_eq_left h']
    let e : M ≃ₗ[ℂ] Submodule.map j M := Submodule.equivMapOfInjective j hj M
    have hc : L.restrict (hpres.2 h') = e.conj (L'.restrict h') := by
      apply LinearMap.ext
      intro w
      obtain ⟨x, rfl⟩ := e.surjective w
      apply Subtype.ext
      simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, LinearMap.coe_restrict_apply, e,
        Submodule.coe_equivMapOfInjective_apply]
      exact hL x x.2
    rw [hc, LinearMap.trace_conj']
  · rw [dite_eq_right (mt hpres.1 h'), dite_eq_right h']

end GlobalTheory.TraceOnInjectiveMap
