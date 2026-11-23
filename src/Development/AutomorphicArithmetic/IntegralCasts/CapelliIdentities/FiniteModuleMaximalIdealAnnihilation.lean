module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Nakayama

@[expose] public section

theorem UpperTheory.Reformulated.B.FiniteModuleMaximalIdealAnnihilation.exists_pow_maximalIdeal_smul_finite_eq_zero :
    ∀ (R Q : Type) [inst : CommRing R] [inst_1 : IsLocalRing R]
    [inst_2 : AddCommGroup Q] [inst_3 : _root_.Module R Q] [Finite Q],
    ∃ (c : ℕ), ∀ a ∈ IsLocalRing.maximalIdeal R ^ c, ∀ (z : Q), a • z = (0 : Q) := by
  intro R Q _ _ _ _ _
  haveI : Finite (Submodule R Q) :=
    Finite.of_injective (fun N : Submodule R Q => (N : Set Q)) SetLike.coe_injective
  obtain ⟨i, j, hij, h⟩ : ∃ i j : ℕ, i < j ∧
      (IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q)) =
        IsLocalRing.maximalIdeal R ^ j • (⊤ : Submodule R Q) := by
    obtain ⟨i, j, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun n : ℕ => IsLocalRing.maximalIdeal R ^ n • (⊤ : Submodule R Q))
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨i, j, hlt, h⟩
    · exact ⟨j, i, hlt, h.symm⟩
  have hbot : IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q) = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) _
      (Submodule.fg_def.2 ⟨_, Set.toFinite _, Submodule.span_eq _⟩) ?_
      (IsLocalRing.maximalIdeal_le_jacobson _)
    calc IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q)
        = IsLocalRing.maximalIdeal R ^ j • (⊤ : Submodule R Q) := h
      _ ≤ IsLocalRing.maximalIdeal R ^ (i + 1) • (⊤ : Submodule R Q) :=
          Submodule.smul_mono_left (Ideal.pow_le_pow_right hij)
      _ = _ := by rw [pow_succ', Submodule.mul_smul]
  refine ⟨i, fun a ha z => ?_⟩
  have hz : a • z ∈ IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q) :=
    Submodule.smul_mem_smul ha Submodule.mem_top
  rwa [hbot, Submodule.mem_bot] at hz
