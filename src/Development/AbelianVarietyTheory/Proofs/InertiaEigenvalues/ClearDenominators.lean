module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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

namespace GlobalTheory.ClearDenominatorsIntegral

open GlobalTheory.UnitLemma

theorem clear_denominators (K : UQ) {V : Type} [AddCommGroup V] [Module (UQ.E K) V] [Module (UQ.O K) V]
    [IsScalarTower (UQ.O K) (UQ.E K) V] (M : Submodule (UQ.O K) V) {x : V}
    (hx : x ∈ Submodule.span (UQ.E K) (↑M : Set V)) :
    ∃ (d : UQ.O K), d ≠ (0 : UQ.O K) ∧ d • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ h₁
    · rw [mul_smul]; exact M.smul_mem _ h₂
  | smul e y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (UQ.O K)) e
    have hb : (b : UQ.O K) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    refine ⟨(b : UQ.O K) * d, mul_ne_zero hb hd, ?_⟩
    have key : (b : UQ.O K) • (e • y) = a • y := by
      rw [← smul_assoc, Algebra.smul_def, mul_comm, hab, algebraMap_smul]
    rw [mul_comm, mul_smul, key, smul_smul, mul_comm, ← smul_smul]
    exact M.smul_mem _ h

theorem main : ∀ (K : GlobalTheory.UnitLemma.UQ) {V : Type} [inst : AddCommGroup V] [inst_1 : Module (GlobalTheory.UnitLemma.UQ.E K) V] [inst_2 : Module (GlobalTheory.UnitLemma.UQ.O K) V] [IsScalarTower (GlobalTheory.UnitLemma.UQ.O K) (GlobalTheory.UnitLemma.UQ.E K) V] (M : Submodule (GlobalTheory.UnitLemma.UQ.O K) V) {x : V}, x ∈ Submodule.span (GlobalTheory.UnitLemma.UQ.E K) (↑M : Set V) → ∃ (d : GlobalTheory.UnitLemma.UQ.O K), d ≠ (0 : GlobalTheory.UnitLemma.UQ.O K) ∧ d • x ∈ M :=
  fun K _ _ _ _ _ M _ hx => clear_denominators K M hx

end GlobalTheory.ClearDenominatorsIntegral
