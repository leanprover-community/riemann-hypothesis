module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.MapStdPoly
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift

@[expose] public section

open CompanionTheory.D.gk.admitted (stdPoly)
open GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.OrthoFamily

theorem exists_minimal_of_no_family_below
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : Set (Submodule ℂ H))
    (hcl : ∀ S ∈ L, IsClosed (S : Set H))
    (hinf : ∀ S ∈ L, ∀ T ∈ L, S ⊓ Tᗮ ∈ L) (n : ℕ) :
    ∀ S ∈ L, S ≠ ⊥ →
      (∀ f : Fin n → Submodule ℂ H, (∀ i, f i ∈ L) → (∀ i, f i ≠ ⊥) → (∀ i, f i ≤ S) →
        ¬ Pairwise fun i k => f i ⟂ f k) →
      ∃ Q ∈ L, Q ≠ ⊥ ∧ ∀ T ∈ L, T ≤ Q → T = ⊥ ∨ T = Q := by
  induction n with
  | zero =>
    intro S _ _ hS
    exact (hS (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
      (fun i => i.elim0)).elim
  | succ n ih =>
    intro S hSL hS0 hS
    by_cases hmin : ∀ T ∈ L, T ≤ S → T = ⊥ ∨ T = S
    · exact ⟨S, hSL, hS0, hmin⟩
    · push_neg at hmin
      obtain ⟨T, hTL, hTS, hT0, hTne⟩ := hmin
      refine ih T hTL hT0 ?_
      intro f hfL hf0 hfT hpw
      haveI : CompleteSpace T := (hcl T hTL).completeSpace_coe
      have hR0 : S ⊓ Tᗮ ≠ ⊥ := by
        intro h
        apply hTne
        have hsup := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hTS
        rw [inf_comm, h, sup_bot_eq] at hsup
        exact hsup
      have ho : ∀ j, (S ⊓ Tᗮ) ⟂ f j := fun j => inf_le_right.trans (Submodule.orthogonal_le (hfT j))
      apply hS (Fin.cons (S ⊓ Tᗮ) f)
      · intro i
        induction i using Fin.cases with
        | zero => rw [Fin.cons_zero]; exact hinf S hSL T hTL
        | succ j => rw [Fin.cons_succ]; exact hfL j
      · intro i
        induction i using Fin.cases with
        | zero => rw [Fin.cons_zero]; exact hR0
        | succ j => rw [Fin.cons_succ]; exact hf0 j
      · intro i
        induction i using Fin.cases with
        | zero => rw [Fin.cons_zero]; exact inf_le_left
        | succ j => rw [Fin.cons_succ]; exact (hfT j).trans hTS
      · intro i k hik
        induction i using Fin.cases with
        | zero =>
          induction k using Fin.cases with
          | zero => exact absurd rfl hik
          | succ j =>
            rw [Fin.cons_zero, Fin.cons_succ]
            exact ho j
        | succ j =>
          induction k using Fin.cases with
          | zero =>
            rw [Fin.cons_zero, Fin.cons_succ]
            exact (ho j).symm
          | succ j' =>
            rw [Fin.cons_succ, Fin.cons_succ]
            exact hpw (fun h => hik (congrArg Fin.succ h))

theorem exists_minimal_of_orthogonal_bound :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (L : Set (Submodule ℂ H)) (m : ℕ)
    (S₀ : Submodule ℂ H), (∀ S ∈ L, IsClosed (S : Set H)) → (∀ S ∈ L, ∀ T ∈ L, S ⊓ Tᗮ ∈ L) → S₀ ∈ L → S₀ ≠ ⊥ →
    (∀ f : Fin (m + 1) → Submodule ℂ H, (∀ i, f i ∈ L) → (∀ i, f i ≠ ⊥) → ¬ Pairwise fun i k => f i ⟂ f k) →
    ∃ Q ∈ L, Q ≠ ⊥ ∧ ∀ T ∈ L, T ≤ Q → T = ⊥ ∨ T = Q := by
  intro H _ _ _ L m S₀ hcl hinf hS₀ hS₀0 hfam
  exact exists_minimal_of_no_family_below L hcl hinf (m + 1) S₀ hS₀ hS₀0
    (fun f hfL hf0 _ => hfam f hfL hf0)

end GlobalTheory.CompanionTheory.OrthoFamily
