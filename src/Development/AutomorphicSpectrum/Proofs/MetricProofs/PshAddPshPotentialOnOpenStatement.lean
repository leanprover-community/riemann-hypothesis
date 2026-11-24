module

public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PshAddPshPotentialOnOpen
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.psh_add_psh_potential_on_open : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (P : LocPot X) (f : X → ℝ) (Θ : LocPot X), IsOpen U → IsPotential A P → IsPotential A Θ → A.SmoothOn U f → IsPshOn A U (P + LocPot.ofFun f) → IsPsh A Θ → IsPshOn A U (P + LocPot.ofFun f + Θ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PshAdd.isPshOn_add_psh | exact GlobalTheory.CompanionTheory.Ar.PshAdd.isPshOn_add_psh | (intros; apply GlobalTheory.CompanionTheory.Ar.PshAdd.isPshOn_add_psh <;> assumption)
