module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CompactFix

theorem finiteDimensional_ker_sub_id {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T : X →L[ℂ] X) (hT : IsCompactOperator T) :
    FiniteDimensional ℂ (LinearMap.ker ((T : X →ₗ[ℂ] X) - LinearMap.id)) := by
  set K : Submodule ℂ X := LinearMap.ker ((T : X →ₗ[ℂ] X) - LinearMap.id) with hK
  have hfix : ∀ x ∈ K, T x = x := by
    intro x hx
    have : (T : X →ₗ[ℂ] X) x - x = 0 := by simpa [hK] using hx
    simpa [sub_eq_zero] using this
  have hclosed : IsClosed (K : Set X) := by
    have : (K : Set X) = {x | T x = x} := by
      ext x
      constructor
      · exact hfix x
      · intro h
        have h' : T x = x := h
        simp [hK, h']
    rw [this]
    exact isClosed_eq T.continuous continuous_id
  obtain ⟨C, hC, hCsub⟩ := hT
  have hpre : (T ⁻¹' C) ∈ nhds (0 : X) := hCsub
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hpre
  have hcomp : IsCompact (Metric.closedBall (0 : K) r) := by
    have hemb : Topology.IsClosedEmbedding (Subtype.val : K → X) := hclosed.isClosedEmbedding_subtypeVal
    rw [hemb.isCompact_iff]
    refine hC.of_isClosed_subset ?_ ?_
    · have : (Subtype.val '' Metric.closedBall (0 : K) r) = (K : Set X) ∩ Metric.closedBall 0 r := by
        ext x
        simp [Metric.mem_closedBall, dist_eq_norm, and_comm]
      rw [this]
      exact hclosed.inter Metric.isClosed_closedBall
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : (x : X) ∈ Metric.closedBall (0 : X) r := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hx
      have := hball hx'
      simpa [hfix x x.2] using this
  exact FiniteDimensional.of_isCompact_closedBall ℂ hr hcomp

end GlobalTheory.CompanionTheory.CompactFix
