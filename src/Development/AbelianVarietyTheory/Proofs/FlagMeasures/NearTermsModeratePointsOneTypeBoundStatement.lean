module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.NearNonzeroTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NearTermsModeratePointsOneTypeBound
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

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.nearTerms_moderate_points_one_type_bound : GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.Dec.NearUnip → GlobalTheory.Deep.PtBound → ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → 1 ≤ q → CountHyp B Cg n₀ d p q b → (∀ x, 1 / 2 ≤ least B.I x → GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d x = 0) ∧ ∀ (a : ℕ) (j : Fin a → ℕ), 1 ≤ a → (∀ i, 1 ≤ j i) → ∑ i, j i ≤ q → ∫⁻ x in {x | ∃ τ, HasType B.I x j τ} ∩ B.fund, {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf) ≤ ENNReal.ofReal (mainTerm B d * (2 * GlobalTheory.FlagMeas.kapBd B.I.E p q j * (2 * B.I.f * q * (11 * q * Real.log (bigX B b))) ^ a)) := by
  first | exact @GlobalTheory.NearType.near_terms_one_type | exact GlobalTheory.NearType.near_terms_one_type | (intros; apply GlobalTheory.NearType.near_terms_one_type <;> assumption)
