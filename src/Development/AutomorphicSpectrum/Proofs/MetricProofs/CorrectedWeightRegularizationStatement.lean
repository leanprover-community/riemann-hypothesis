module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CorrectedWeightRegularization
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.corrected_weight_regularization : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) [DecidableEq Ψ] [Nonempty Ψ] (M : XModel D) (U : ((Σ k, J k) → ℂ) → ℝ) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu (corrW Hd U)) (rd Lval Ch Cu : ℝ), S.IsTied → S'.IsTied → (∀ z, 0 ≤ U z) → (∀ z ∈ D.Xo, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → U (torusSmul c z) = U z) → PosU S' → ConjU S' → HtU S' Ch rd Lval → MeanU Hd U Cu rd Lval → ∃ X : ComponentSetting D ℤ (Fin 2 → ℤ), X.H = Hd ∧ (∀ z ∈ D.Xo, X.Cd.cuspWeight z = U z) ∧ X.rd = rd ∧ X.Lval = Lval ∧ CuspBundlePos X ∧ MUConjInvariant X ∧ HtInterior Ch X ∧ HtBoundary Ch X ∧ CuspMean Cu X := by
  first | exact @GlobalTheory.CompanionTheory.Relay.corrected_weight_regularization | exact GlobalTheory.CompanionTheory.Relay.corrected_weight_regularization | (intros; apply GlobalTheory.CompanionTheory.Relay.corrected_weight_regularization <;> assumption)
