module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvHodgeMetricGramMumfordGoodGrowthBoundaryChart
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

theorem _root_.GlobalTheory.T.inv_hodgeMetricGram_mumfordGoodGrowth_boundaryChart : ∀ (n a : ℕ) (ha : a ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ ∃ (c : ℝ) (N : ℕ), ∀ v : ReciprocityTheory.L2DbarEstimates.V n, v.ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ → (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B v.ofLp).PosDef ∧ (∀ i k, ContDiffAt ℝ 2 (fun u : ReciprocityTheory.L2DbarEstimates.V n => (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B u.ofLp)⁻¹ i k) v) ∧ GlobalTheory.GoodMetric.GoodBound (Finset.univ.map (Fin.castLEEmb ha)) c N (fun u : ReciprocityTheory.L2DbarEstimates.V n => (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B u.ofLp)⁻¹) v := by
  first | exact @GlobalTheory.HodgeInvGood.inv_hodgeGram_goodBound | exact GlobalTheory.HodgeInvGood.inv_hodgeGram_goodBound | (intros; apply GlobalTheory.HodgeInvGood.inv_hodgeGram_goodBound <;> assumption)
