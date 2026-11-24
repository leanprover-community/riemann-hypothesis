module

public import ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.IntSmulIntegral

open NumberField

theorem exists_int_mul_integral {K : Type} [Field K] [NumberField K] (a : K) :
    ∃ (m : ℤ) (z : 𝓞 K), m ≠ 0 ∧ (z : K) = m • a := by
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.of_finite ℚ K
  obtain ⟨m, hm, hint⟩ := ((Algebra.IsAlgebraic.isAlgebraic a : IsAlgebraic ℚ a).restrictScalars ℤ).exists_integral_multiple
  exact ⟨m, ⟨m • a, hint⟩, hm, rfl⟩

theorem exists_int_smul_mem {r : ℕ} {K : Type} [Field K] [NumberField K]
    {Λ : Submodule (𝓞 K) (Fin r → K)} (hΛ : ReciprocityTheory.MultiplicativeHeights.IsLattice Λ) (v : Fin r → K) :
    ∃ n : ℤ, n ≠ 0 ∧ n • v ∈ Λ := by
  have hv : v ∈ Submodule.span K (Λ : Set (Fin r → K)) := hΛ.2 ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨n₁, hn₁, h₁⟩ := hx
    obtain ⟨n₂, hn₂, h₂⟩ := hy
    refine ⟨n₁ * n₂, mul_ne_zero hn₁ hn₂, ?_⟩
    rw [smul_add, mul_comm, mul_smul, mul_comm, mul_smul]
    exact Λ.add_mem (Λ.toAddSubgroup.zsmul_mem h₁ n₂) (Λ.toAddSubgroup.zsmul_mem h₂ n₁)
  | smul c x _ hx =>
    obtain ⟨n, hn, h⟩ := hx
    obtain ⟨m, z, hm, hz⟩ := exists_int_mul_integral c
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩

    have e : (n * m) • (c • x) = z • (n • x) := by
      rw [mul_smul, ← smul_assoc m c x, ← hz, smul_comm]
      rfl
    rw [e]
    exact Λ.smul_mem z h

end GlobalTheory.IntSmulIntegral
