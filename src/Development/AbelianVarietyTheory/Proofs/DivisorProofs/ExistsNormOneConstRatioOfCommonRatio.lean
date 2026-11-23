module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEqConstMulOfForallExistsNormEq
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero

@[expose] public section

namespace GlobalTheory

theorem exists_norm_one_const_ratio_of_common_ratio :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (I : Type) (S : Set V),
      IsOpen S → IsPreconnected S → ∀ (A B : I → V → ℂ) (t : V → ℂ), (∀ i, DifferentiableOn ℂ (A i) S) →
      (∀ i, DifferentiableOn ℂ (B i) S) → (∀ i, ∀ x ∈ S, A i x = t x * B i x) →
      (∀ i, ∀ x ∈ S, ‖A i x‖ = ‖B i x‖) → ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ i, ∀ x ∈ S, A i x = ε * B i x := by
  intro V _ _ _ I S hS hc A B t hA hB ht hn
  by_cases h0 : ∀ i, ∀ x ∈ S, B i x = 0
  · refine ⟨1, norm_one, fun i x hx => ?_⟩
    rw [ht i x hx, h0 i x hx, mul_zero, mul_zero]
  · simp only [not_forall] at h0
    obtain ⟨i₀, x₀, hx₀, hne⟩ := h0
    obtain ⟨_, c, hcc⟩ := exists_eq_const_mul_of_forall_exists_norm_eq V Unit S hS hc ⟨x₀, hx₀⟩ (A i₀)
      (fun _ => B i₀) (hA i₀) (fun _ => hB i₀) (fun x hx => ⟨(), hn i₀ x hx⟩)
    refine ⟨c, ?_, fun i x hx => ?_⟩
    · have h1 := hn i₀ x₀ hx₀
      rw [hcc x₀ hx₀, norm_mul] at h1
      exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hne) (by rw [one_mul]; exact h1)
    · have hd : DifferentiableOn ℂ (fun y => A i y - c * B i y) S := (hA i).sub ((hB i).const_mul c)
      have := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero hS hc (hB i₀) hd (fun y hy => by
        have e1 := ht i y hy
        have e2 := ht i₀ y hy
        have e3 : A i₀ y = c * B i₀ y := hcc y hy
        show B i₀ y * (A i y - c * B i y) = 0
        rw [e1]
        linear_combination (B i y) * (e3 - e2)) hx₀ hne x hx
      exact sub_eq_zero.mp this

end GlobalTheory
