module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem UpperTheory.Reformulated.B.Rd4.exists_nat_smul_mem :
    ∀ {D : Formalism.BasicNotions.D7} {n : ℕ}
    {Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin n → D.host.E)},
    Submodule.IsFullLattice D.host.E Λ →
      ∀ (x : Fin n → D.host.E),
        ∃ (N : ℕ),
          (0 : ℕ) < N ∧
            (↑N : D.host.E) • x ∈
              Λ := by
  intro D n Λ h x
  obtain ⟨⟨_, m, hm, rfl⟩, ht⟩ := multiple_mem_span_of_mem_localization_span
    (Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers D.host.E) (nonZeroDivisors ℤ))
    D.host.E (Λ : Set (Fin n → D.host.E)) x (by rw [h.span_eq_top]; trivial)
  change algebraMap ℤ (NumberField.RingOfIntegers D.host.E) m • x ∈ _ at ht
  rw [Submodule.span_eq, algebraMap_smul] at ht
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  refine ⟨m.natAbs * m.natAbs, by positivity, ?_⟩
  rw [Nat.cast_smul_eq_nsmul, ← natCast_zsmul, Int.natAbs_mul_self, mul_smul]
  exact zsmul_mem ht m
