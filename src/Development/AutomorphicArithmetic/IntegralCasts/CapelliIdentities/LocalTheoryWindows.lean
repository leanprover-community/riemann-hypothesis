module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds
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

attribute [local instance] Formalism.MainNotions.S.starE

theorem UpperTheory.Reformulated.B.LocalTheoryWindows.lat_mult :
    ∀ (D : Formalism.BasicNotions.D7)
    {Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Formalism.MainNotions.S.VS D).V},
    Submodule.IsFullLattice D.host.E Λ →
      ∀ (v : (Formalism.MainNotions.S.VS D).V),
        ∃ (n : ℤ),
          n ≠ (0 : ℤ) ∧
            (↑n : D.host.E) • v ∈
              Λ := by
  intro D Λ h v
  obtain ⟨⟨t, ht⟩, hv⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers D.host.E)) D.host.E (Λ : Set (Formalism.MainNotions.S.VS D).V) v
    (h.span_eq_top ▸ Submodule.mem_top)
  obtain ⟨n, hn, c, hc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) t).exists_nonzero_dvd ht
  refine ⟨n, hn, ?_⟩
  have hc' : (n : NumberField.RingOfIntegers D.host.E) = c * t := by rw [mul_comm]; simpa using hc
  have e : (n : D.host.E) • v = c • t • v := by
    rw [smul_smul, ← hc', ← algebraMap_smul D.host.E (n : NumberField.RingOfIntegers D.host.E) v, map_intCast]
  rw [Submodule.span_eq] at hv
  exact e ▸ Λ.smul_mem c hv
