module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactSpanHighestWeightLine
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsAdmissibleSubOfFiniteDimensional

@[expose] public section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.maxCompactSpan_highestWeight_line : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ → (∀ v, ContinuousOn (fun g => ρ g v) (Formalism.MainNotions.S.UJset ε)) → (∀ k ∈ Formalism.REAL.Kset ε, ∀ v, ‖ρ k v‖ = ‖v‖) → ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → Formalism.MainNotions.S.IsKStableOn ε ρ S → ∀ (Λ : Fin n → ℝ) (w : H), w ∈ S → w ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ Λ w → (∀ a b : Fin n, a < b → ε a = ε b → ∀ x ∈ S, Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ (Λ + Formalism.REAL.root a b) x → x = 0) → (∀ (μ : Fin n → ℝ) (x : H), x ∈ Submodule.span ℂ ((fun k => ρ k w) '' Formalism.REAL.Kset ε) → x ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ x → Formalism.MainNotions.S.CDom ε μ Λ) ∧ (∀ x ∈ Submodule.span ℂ ((fun k => ρ k w) '' Formalism.REAL.Kset ε), Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ Λ x → ∃ c : ℂ, x = c • w) := by
  first | exact @GlobalTheory.KSpanHighest.kspan_highest | exact GlobalTheory.KSpanHighest.kspan_highest | (intros; apply GlobalTheory.KSpanHighest.kspan_highest <;> assumption)
