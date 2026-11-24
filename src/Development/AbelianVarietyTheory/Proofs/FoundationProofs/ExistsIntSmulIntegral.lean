module

public import Mathlib.NumberTheory.NumberField.Basic
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

universe u_1 u_2

namespace GlobalTheory.IntegerScalarIntegral

open NumberField

theorem exists_int_smul_integral {K : Type u_1} [Field K] [NumberField K] (c : K) :
    ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ (d • c) := by
  have hc : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (.of_finite ℚ c)
  exact hc.exists_integral_multiple

theorem exists_int_smul_mem {K : Type u_1} {V : Type u_2} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (L : Submodule (𝓞 K) V) (hL : Submodule.span K (L : Set V) = ⊤) (y : V) :
    ∃ m : ℤ, m ≠ 0 ∧ m • y ∈ L := by
  have hy : y ∈ Submodule.span K (L : Set V) := hL ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hax b
    · rw [mul_smul]; exact zsmul_mem hbz a
  | smul c x _ hx =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨d, hd, hint⟩ := exists_int_smul_integral c
    refine ⟨d * m, mul_ne_zero hd hm, ?_⟩
    let r : 𝓞 K := ⟨d • c, hint⟩
    have hr : (algebraMap (𝓞 K) K r) = d • c := rfl
    have key : (d * m) • (c • x) = r • (m • x) := by
      rw [← algebraMap_smul K r (m • x), hr, smul_comm (d • c) m x, smul_assoc, mul_comm, mul_smul]
    rw [key]
    exact L.smul_mem r hmx

theorem main : ∀ {K : Type u_1} {V : Type u_2} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V]
    [inst_3 : Module K V] [inst_4 : Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (L : Submodule (NumberField.RingOfIntegers K) V),
    Submodule.span K (↑L : Set V) = ⊤ → ∀ (y : V), ∃ (m : ℤ), m ≠ (0 : ℤ) ∧ m • y ∈ L :=
  fun L hL y => exists_int_smul_mem L hL y

end GlobalTheory.IntegerScalarIntegral
