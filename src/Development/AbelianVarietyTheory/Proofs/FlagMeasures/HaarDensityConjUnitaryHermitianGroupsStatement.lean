module

public import Formalism.PeriodIntegrals.QuotInv
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarDensityConjUnitaryHermitianGroups
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.haar_density_conj_unitaryHermitianGroups : ∀ (m : ℕ) (H H' P : Matrix (Fin m) (Fin m) ℂ), Hᴴ = H → H * H = 1 → H'ᴴ = H' → H' * H' = 1 → IsUnit P → Pᴴ * H' * P = H → ∀ (μ : Measure (PI.MtM m)) (c : ℝ≥0∞), PI.IsHaarOnM (UH H') μ → HasDens (UH H') μ c → PI.IsHaarOnM (UH H) (μ.map fun x : PI.MtM m => Matrix.of.symm (P⁻¹ * Matrix.of x * P)) ∧ HasDens (UH H) (μ.map fun x : PI.MtM m => Matrix.of.symm (P⁻¹ * Matrix.of x * P)) c := by
  first | exact @GlobalTheory.AdDens.haar_dens_conj | exact GlobalTheory.AdDens.haar_dens_conj | (intros; apply GlobalTheory.AdDens.haar_dens_conj <;> assumption)
