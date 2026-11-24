module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.DecayOfMemSpan

theorem decay_of_mem_span {G H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ρ : G → H →L[ℂ] H} {D : G → ℝ} {c : ℝ} {S : Set H} {u : H}
    (h : ∀ v ∈ S, ∃ C : ℝ, ∀ g : G,
      ‖Inner.inner ℂ v ((ρ g : H → H) u)‖ ≤ C * Real.exp (-(c * D g))) :
    ∀ v ∈ Submodule.span ℂ S, ∃ C : ℝ, ∀ g : G,
      ‖Inner.inner ℂ v ((ρ g : H → H) u)‖ ≤ C * Real.exp (-(c * D g)) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact ⟨0, fun g => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, hA⟩ := hx
    obtain ⟨B, hB⟩ := hy
    refine ⟨A + B, fun g => ?_⟩
    rw [inner_add_left, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hA g) (hB g))
  | smul a x _ hx =>
    obtain ⟨A, hA⟩ := hx
    refine ⟨‖a‖ * A, fun g => ?_⟩
    rw [inner_smul_left, norm_mul, RCLike.norm_conj, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hA g) (norm_nonneg a)

end GlobalTheory.DecayOfMemSpan
