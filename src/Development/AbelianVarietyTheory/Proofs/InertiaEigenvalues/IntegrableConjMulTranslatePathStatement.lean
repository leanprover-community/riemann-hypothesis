module

public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableConjMulTranslatePath
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory GlobalTheory.AutomorphicL2Unitary

theorem _root_.GlobalTheory.T.integrable_conj_mul_translate_path' : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (c : ℝ → G), Continuous c → ∀ {f' : G → ℂ}, MemL2Quotient Γ μ f' → Continuous f' → ∀ (H : L2 Γ μ) (t : ℝ), Integrable (Function.uncurry fun (s : ℝ) (q : GlobalTheory.AutomorphicL2Unitary.Quot Γ) => starRingEnd ℂ (H q) * f' (sec Γ q * c s)) ((volume.restrict (Set.uIoc 0 t)).prod (quotMeasure Γ μ)) := by
  first | exact @GlobalTheory.integrable_conj_mul_translate_path | exact GlobalTheory.integrable_conj_mul_translate_path | (intros; apply GlobalTheory.integrable_conj_mul_translate_path <;> assumption)
