module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRadialMapUnitaryLeviBlockProduct
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

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

theorem _root_.GlobalTheory.T.isRadial_map_unitaryLeviBlockProduct : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ → ∀ θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → Formalism.REAL.UJ ε, Measurable θ → (∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2)) → ∀ c : ℝ, IsGauge ε₀ c → IsRadial (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ) (fun g => Formalism.REAL.hs (uMat g - 1)) (n₀ ^ 2 + 2 * ∑ i, j i ^ 2) := by
  first | exact @GlobalTheory.LeviIso.MapRadial.isRadial_map_lev | exact GlobalTheory.LeviIso.MapRadial.isRadial_map_lev | (intros; apply GlobalTheory.LeviIso.MapRadial.isRadial_map_lev <;> assumption)
