module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CwContIntegralComm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.cwCont_integral_comm_alt : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (Bm : R.H → V), (∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) → (∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v) → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm → ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] (μ : Measure X) [IsFiniteMeasure μ] (κ : X → Mx k r) (p : X → ℂ), Continuous κ → (∀ x, κ x ∈ GG k r) → Continuous p → ∀ v ∈ R.sm, (∫ x, p x • R.σ (κ x) v ∂μ) ∈ R.sm → Bm (∫ x, p x • R.σ (κ x) v ∂μ) = ∫ x, p x • Bm (R.σ (κ x) v) ∂μ := by
  first | exact @GlobalTheory.cwCont_integral_comm | exact GlobalTheory.cwCont_integral_comm | (intros; apply GlobalTheory.cwCont_integral_comm <;> assumption)
