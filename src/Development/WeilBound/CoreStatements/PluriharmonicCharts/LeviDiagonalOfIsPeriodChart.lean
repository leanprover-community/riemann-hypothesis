module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.AnalyticForms.LeviForms.HomDens
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsOpenFlagDomainNondegenerateMinorsStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetComparableGramBoundStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GramLogUnitaryTriangularInvarianceStatement
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XPerCell
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialLeviFormCellStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodChartPotentialLeviForm

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgp.per_diag

theorem levi_diagonal_of_isPeriodChart :
    ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ), j ≤ N → ∀ (pot : Ψ × Fin N → LocPot X) (x : X) (V : Set X) (g : Ψ → X → Matrix (Fin N) (Fin N) ℂ), IsPeriodChart A j pot x V g → ∀ k, x ∈ (A.chart k).source → ∃ Lm : (Fin e → ℂ) →ₗ[ℂ] (Ψ × Pairs N → ℂ), (∀ p, ContDiffAt ℝ 2 ((pot p).φ x ∘ (A.chart k).symm) (A.chart k x)) ∧ (∀ (p : Ψ × Fin N) v, levi ((pot p).φ x ∘ (A.chart k).symm) (A.chart k x) v = ∑ q : Pairs N, if q.1.1 ≤ p.2 ∧ p.2 < q.1.2 then (1 / 2 : ℝ) * ‖Lm v (p.1, q)‖ ^ 2 else 0) ∧ (IsFlagImmersionAt A g x → Function.Injective Lm) :=
  _root_.GlobalTheory.CompanionTheory.Ar.PB.levi_diagonal_of_isPeriodChart

end PositivityTheory.Xgp.per_diag
