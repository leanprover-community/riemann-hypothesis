module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightedOrbitalIntegralGLZeroOfRadicalIntegrals
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.SplitWeil

theorem _root_.GlobalTheory.T.weightedOrbitalIntegral_GL_zero_of_radical_integrals : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r : ℕ) [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] (μ : Measure (GL (Fin r) k)) [μ.IsHaarMeasure] (ε : Matrix (Fin r) (Fin r) k) (N : Subgroup (GL (Fin r) k)), ε * ε = ε → (∀ g, g ∈ N ↔ ε * (g.1 - 1) * (1 - ε) = g.1 - 1) → ∀ f : GL (Fin r) k → ℂ, Continuous f → HasCompactSupport f → (∀ (ν : Measure N) [ν.IsHaarMeasure] (x y : GL (Fin r) k), ∫ u : N, f (x * u * y) ∂ν = 0) → ∀ γ : GL (Fin r) k, IsRegSS γ.1 → γ.1 * ε = ε * γ.1 → ∀ b : GL (Fin r) k → ℂ, Continuous b → LeftInv (cent γ) b → LeftInv N b → ∀ (dt : Measure (cent γ)) [dt.IsHaarMeasure], HasQuotInt (cent γ) dt μ (fun x => b x * f (x⁻¹ * γ * x)) 0 := by
  first | exact @GlobalTheory.RadicalOrb.hasQuotInt_zero | exact GlobalTheory.RadicalOrb.hasQuotInt_zero | (intros; apply GlobalTheory.RadicalOrb.hasQuotInt_zero <;> assumption)
