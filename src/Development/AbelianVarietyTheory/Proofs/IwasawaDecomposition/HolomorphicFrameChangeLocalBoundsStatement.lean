module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicFrameChangeLocalBounds
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology


theorem _root_.GlobalTheory.T.holomorphicFrameChange_local_bounds : ∀ (n : ℕ) (K : Type) [Fintype K] [DecidableEq K] (P : ReciprocityTheory.L2DbarEstimates.V n → Matrix K K ℂ) (r : ℝ), 0 < r → (∀ i k, DifferentiableOn ℂ (fun u => P u i k) (Metric.ball 0 r)) → IsUnit (P 0).det → ∃ r' : ℝ, 0 < r' ∧ r' ≤ r ∧ ∃ B : ℝ, ∀ v : ReciprocityTheory.L2DbarEstimates.V n, ‖v‖ < r' → IsUnit (P v).det ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => P u i k) v) ∧ (∀ᶠ u in nhds v, ∀ η, GlobalTheory.HermFrame.mdbar P u η = 0) ∧ (∀ i k, ‖P v i k‖ ≤ B) ∧ (∀ i k, ‖(P v)⁻¹ i k‖ ≤ B) ∧ (∀ a i k, ‖GlobalTheory.HermFrame.mdel P v (GlobalTheory.GoodMetric.coordVec a) i k‖ ≤ B) ∧ (∀ a b i k, ‖GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.mdel P u (GlobalTheory.GoodMetric.coordVec b)) v (GlobalTheory.GoodMetric.coordVec a) i k‖ ≤ B) := by
  first | exact @GlobalTheory.HermFrame.holoFrame_local_bounds | exact GlobalTheory.HermFrame.holoFrame_local_bounds | (intros; apply GlobalTheory.HermFrame.holoFrame_local_bounds <;> assumption)
