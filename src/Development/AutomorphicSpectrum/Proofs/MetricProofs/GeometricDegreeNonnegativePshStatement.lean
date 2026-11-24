module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GeometricDegreeNonnegativePsh
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

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.geometric_degree_nonnegative_psh : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (Fl : Set σ), (∀ a ∈ Fl, ∀ t, IsPsh S.A ((S.potT a t).rsmul (-1)) ∧ IsPsh S.A (S.potT a t)) → Re.J = ⊤ → ∀ n : σ → ℤ, (∀ a ∉ Fl, 0 ≤ n a) → ∀ W : Ideal (MRing ι), IsArithVar W 2 → P ≤ W → 0 ≤ geomDeg W (combLine Re.ref n) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.nonneg_degree_horizontal_curve | exact GlobalTheory.CompanionTheory.Ar.PB.nonneg_degree_horizontal_curve | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.nonneg_degree_horizontal_curve <;> assumption)
