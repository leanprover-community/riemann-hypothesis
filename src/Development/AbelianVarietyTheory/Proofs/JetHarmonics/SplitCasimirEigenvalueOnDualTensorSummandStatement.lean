module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirEigenvalueOnDualTensorSummand
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
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.StatementI

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.splitCasimir_eigenvalue_on_dualTensor_summand : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (Ns : Type) [AddCommGroup Ns] [Module ℂ Ns] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (F : Fin n → Fin n → Module.End ℂ Ns) (io : Ns →ₗ[ℂ] (Fin n → M)) (mu : Fin n → ℝ) (s : Fin n), (∀ w, Formalism.REAL.Cas E w = (casG mu : ℂ) • w) → (∀ y, Formalism.REAL.Cas F y = (casG (mu - Pi.single s 1) : ℂ) • y) → (∀ a b y, io (F a b y) = dualTens E a b (io y)) → ∀ y, splitCas E (io y) = ((-mu s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ) • io y := by
  first | exact @GlobalTheory.splitCas_on_summand | exact GlobalTheory.splitCas_on_summand | (intros; apply GlobalTheory.splitCas_on_summand <;> assumption)
