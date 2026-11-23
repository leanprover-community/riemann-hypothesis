module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThinUnitaryTubeVolumeLimitArith
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlkExt
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate

theorem _root_.GlobalTheory.T.thinUnitaryTube_volume_limit_arith : ∀ (k : ℕ) (c c₀ : ℝ) (F F' M V : ℝ → ℝ≥0∞), 0 < c → 0 < c₀ → (∀ t s : ℝ, 0 < t → t < s → F t ≤ F' t ∧ F' t ≤ F s) → (∀ ρ : ℝ, 0 < ρ → 0 < V ρ ∧ V ρ < ⊤) → Tendsto (fun ρ : ℝ => M ρ / V ρ) (𝓝[>] 0) (𝓝 (ENNReal.ofReal c₀)) → Tendsto (fun ρ : ℝ => M ρ * (F (ρ ^ 2 / 2) * ENNReal.ofReal (ρ / Real.pi)) / (V ρ * ENNReal.ofReal (2 * ρ * (Real.pi ^ k * ρ ^ (2 * k) / (k.factorial : ℝ))))) (𝓝[>] 0) (𝓝 (ENNReal.ofReal c)) → Tendsto (fun t : ℝ => F' t / ENNReal.ofReal (t ^ k)) (𝓝[>] 0) (𝓝 (ENNReal.ofReal (c / c₀ * (2 * Real.pi) ^ (k + 1) / (k.factorial : ℝ)))) := by
  first | exact @GlobalTheory.Tube.thin_tube_limit_arith | exact GlobalTheory.Tube.thin_tube_limit_arith | (intros; apply GlobalTheory.Tube.thin_tube_limit_arith <;> assumption)
