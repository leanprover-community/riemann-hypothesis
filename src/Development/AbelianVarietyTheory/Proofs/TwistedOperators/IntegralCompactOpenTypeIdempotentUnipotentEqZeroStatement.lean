module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompactOpenTypeIdempotentUnipotentEqZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

theorem _root_.GlobalTheory.T.integral_compactOpenTypeIdempotent_unipotent_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r : ℕ}
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ (GL (Fin r) 𝓀[k]) W)
    [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] (μ : Measure (GL (Fin r) k))
    (N : Subgroup (GL (Fin r) k)) (ν : Measure N) [ν.IsMulLeftInvariant] (H : Subgroup (GL (Fin r) 𝓀[k])),
    NoFixed τ H → ∀ x : GL (Fin r) k,
    (∀ v ∈ H, ∃ n ∈ N, ∃ hn : x * n * x⁻¹ ∈ KO k (Fin r), GlobalTheory.LocGL.redK k (Fin r) ⟨x * n * x⁻¹, hn⟩ = v) →
    ∀ w : GL (Fin r) k, ∫ u : N, idemGL k μ τ (x * u * w) ∂ν = 0 := by
  exact @GlobalTheory.TypeIdemAverage.integral_idemGL_eq_zero
