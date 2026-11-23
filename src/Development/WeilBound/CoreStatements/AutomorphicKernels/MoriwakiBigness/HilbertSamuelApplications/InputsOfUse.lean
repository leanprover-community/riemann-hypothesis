module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.SmallGeneratedCountUpperOfUse
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibreDim
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanNefCriteriaHoldStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LineFibreHolds
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SiuInequalityIntegralHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceRateStatementHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceStatementHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeOfIsIntersectionSystem
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GlobalRegularizationStatementHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MetricLocal
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionFormulaOfArithSystemStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackStatementHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RationalityOfResolutionStatementStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatementStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SignedConvergenceStatementHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.UniformIntegrabilityStatementHoldsStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.HsLinksOfUse
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem inputs_of_use :
    ArithIntersectionSystemStatement → PositivityTheory.MbHsUse.HSUse →
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ResK.ResKStatement → GlobalTheory.CompanionTheory.Ar.PB.Inputs := by
  intro hII hU hBig hRes
  exact ⟨⟨GlobalTheory.T.convergence_statement_holds, GlobalTheory.T.signed_convergence_statement_holds, GlobalTheory.T.convergence_rate_statement_holds, GlobalTheory.T.uniform_integrability_statement_holds, GlobalTheory.T.pullback_statement_holds, GlobalTheory.T.global_regularization_statement_holds⟩,
    ⟨GlobalTheory.T.resolution_exists_of_resolution_statement hRes, degree_of_system hII, (hsLinks_of_use hU hBig).1⟩,
    ⟨GlobalTheory.T.rationality_of_resolution_statement hRes, metricLocal⟩,
    ⟨GlobalTheory.T.projection_formula_of_arith_system hII, lineFibre_holds, fibreDim⟩,
    ⟨GlobalTheory.T.kleiman_nef_criteria_hold.1, GlobalTheory.T.kleiman_nef_criteria_hold.2, GlobalTheory.T.siu_inequality_integral_holds⟩⟩

end GlobalTheory.CompanionTheory.Ar.Giv
