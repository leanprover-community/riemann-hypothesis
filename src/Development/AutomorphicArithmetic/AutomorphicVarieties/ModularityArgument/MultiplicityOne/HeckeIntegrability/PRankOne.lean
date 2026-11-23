module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LevelTrAAlt
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

@[expose] public section

namespace UpperTheory.V.Z.Mult.Pi

private lemma trace_idem {Y : Type} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
    (f : Module.End ℂ Y) (hf : f * f = f) (hx : ∀ x, ∃ c : ℂ, f * x * f = c • f) (h0 : f ≠ 0) :
    LinearMap.trace ℂ Y f = 1 := by
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact h0 (LinearMap.ext h)
  have hidem : ∀ v, f (f v) = f v := fun v => by
    have := congrArg (fun g : Module.End ℂ Y => g v) hf
    simpa [Module.End.mul_apply] using this
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ Y, φ (f y) = 1 := by
    have h1 : ¬ ∀ φ : Module.Dual ℂ Y, φ (f y) = 0 := fun h =>
      hy ((Module.forall_dual_apply_eq_zero_iff ℂ (f y)).1 h)
    push_neg at h1
    obtain ⟨ψ, hψ⟩ := h1
    refine ⟨(ψ (f y))⁻¹ • ψ, ?_⟩
    simp [hψ]
  have hr : LinearMap.range f = Submodule.span ℂ {f y} := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      obtain ⟨c, hc⟩ := hx (φ.smulRight v)
      have h2 := congrArg (fun g : Module.End ℂ Y => g (f y)) hc
      simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, hidem, hφ,
        map_smul, one_smul] at h2
      exact Submodule.mem_span_singleton.2 ⟨c, h2.symm⟩
    · rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨y, rfl⟩
  have hp : LinearMap.IsProj (LinearMap.range f) f :=
    ⟨fun x => ⟨x, rfl⟩, by rintro _ ⟨v, rfl⟩; exact hidem v⟩
  rw [hp.trace, hr, finrank_span_singleton hy]
  simp

theorem rankOne_pf : RankOne := by
  intro Y _ _ _ f A hf hA hc hx
  by_cases h0 : f = 0
  · left
    simp [h0]
  right
  obtain ⟨c, hcA⟩ := hx A
  have hfA : f * A = c • f := by
    calc f * A = f * f * A := by rw [hf]
      _ = f * (f * A) := mul_assoc _ _ _
      _ = f * (A * f) := by rw [hc]
      _ = f * A * f := (mul_assoc _ _ _).symm
      _ = c • f := hcA
  have hsq : (c * c) • f = f := by
    calc (c * c) • f = (c • f) * (c • f) := by rw [smul_mul_smul_comm, hf]
      _ = (f * A) * (f * A) := by rw [hfA]
      _ = f * (A * f) * A := by simp only [mul_assoc]
      _ = f * (f * A) * A := by rw [hc]
      _ = (f * f) * (A * A) := by simp only [mul_assoc]
      _ = f := by rw [hf, hA, mul_one]
  have hcc : c * c = 1 := by
    have h3 : (c * c - 1) • f = 0 := by rw [sub_smul, one_smul, hsq, sub_self]
    rcases smul_eq_zero.1 h3 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h h0
  have hn : ‖c‖ = 1 := by
    have h4 : ‖c‖ * ‖c‖ = 1 := by rw [← norm_mul, hcc, norm_one]
    nlinarith [norm_nonneg c, sq_nonneg (‖c‖ - 1)]
  rw [hfA, map_smul, trace_idem f hf hx h0, smul_eq_mul, mul_one, hn]

end UpperTheory.V.Z.Mult.Pi
