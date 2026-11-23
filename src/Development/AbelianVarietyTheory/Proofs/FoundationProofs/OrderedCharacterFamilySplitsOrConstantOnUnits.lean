module

public import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem apply_eq_one_of_triv_one_unit {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {χ : kˣ →* ℂˣ} (h : Triv χ 1) (u : kˣ) (hu : valuation k (u : k) = 1) : χ u = 1 := by
  apply h u hu
  calc valuation k ((u : k) - 1) ≤ max (valuation k (u : k)) (valuation k 1) := Valuation.map_sub _ _ _
    _ = valuation k 1 := by simp [hu]

theorem cut_or_const : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → (∃ r : ℕ, 0 < r ∧ r < n ∧ Cut ψ r) ∨ ∃ χ : kˣ →* ℂˣ, ((∀ i, IsSmoothChar (ψ i)) → IsSmoothChar χ) ∧ Agree ψ (fun _ => χ) := by
  intro k _ _ _ _ n ψ hord
  by_cases hc : ∃ m : ℕ, ∃ h : m + 1 < n, ¬ Triv (ψ ⟨m, by omega⟩ / ψ ⟨m + 1, h⟩) 1
  · obtain ⟨m, hm, hnt⟩ := hc
    refine Or.inl ⟨m + 1, by omega, hm, ?_⟩
    intro i j hi hj htr
    have h1 : i ≤ (⟨m, by omega⟩ : Fin n) := by rw [Fin.le_def]; simp; omega
    have h2 : (⟨m, by omega⟩ : Fin n) ≤ ⟨m + 1, hm⟩ := simp [Fin.le_def]
    have h3 : (⟨m + 1, hm⟩ : Fin n) ≤ j := by rw [Fin.le_def]; simp; omega
    exact hnt (hord i _ _ j h1 h2 h3 1 htr)
  · push_neg at hc
    right
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      refine ⟨1, fun _ => ?_, fun i => i.elim0⟩
      show IsOpen ((1 : kˣ →* ℂˣ).ker : Set kˣ)
      simp
    · refine ⟨ψ ⟨0, hn⟩, fun hs => hs _, ?_⟩
      have key : ∀ m (hm : m < n) (u : kˣ), valuation k (u : k) = 1 → ψ ⟨m, hm⟩ u = ψ ⟨0, hn⟩ u := by
        intro m
        induction m with
        | zero => intro _ _ _; rfl
        | succ m ih =>
          intro hm u hu
          have h1 := apply_eq_one_of_triv_one_unit (hc m hm) u hu
          rw [MonoidHom.div_apply, div_eq_one] at h1
          rw [← h1, ih (by omega) u hu]
      intro i u hu
      exact key i.1 i.2 u hu

end GlobalTheory.PsType
