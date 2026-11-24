module

public import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

private theorem UpperTheory.Reformulated.B.WeightThresholdDefs.core {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {L : Submodule (NumberField.RingOfIntegers K) V} (h : Submodule.span K (L : Set V) = ⊤) (x : V) :
    ∃ n : NumberField.RingOfIntegers K, n ≠ 0 ∧ (n : K) • x ∈ L := by
  have hx : x ∈ Submodule.span K (L : Set V) := h ▸ Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers K)) K (L : Set V) x hx
  refine ⟨t, nonZeroDivisors.coe_ne_zero t, ?_⟩
  rw [Submodule.span_eq, Submonoid.smul_def] at ht
  have : ((t : NumberField.RingOfIntegers K) : K) • x = (t : NumberField.RingOfIntegers K) • x :=
    algebraMap_smul K (t : NumberField.RingOfIntegers K) x
  rw [this]
  exact ht

theorem UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem :
    ∀ {D : Formalism.L2.Ker.Car} {N : ℕ}
    {L₁ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N → D.host.E)},
    Submodule.span D.host.E (↑L₁ : Set (Fin N → D.host.E)) = ⊤ →
      ∀ (x : Fin N → D.host.E),
        ∃ (n : NumberField.RingOfIntegers D.host.E),
          n ≠ (0 : NumberField.RingOfIntegers D.host.E) ∧
            (↑n : D.host.E) • x ∈
              L₁ := by
  intro D N L₁ h x
  exact UpperTheory.Reformulated.B.WeightThresholdDefs.core h x
