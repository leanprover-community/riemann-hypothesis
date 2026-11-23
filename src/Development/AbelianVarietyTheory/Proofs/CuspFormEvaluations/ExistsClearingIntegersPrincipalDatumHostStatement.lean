module

public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsClearingIntegersPrincipalDatumHost
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

theorem _root_.GlobalTheory.T.exists_clearing_integers_principalDatum_host : ∀ (D : D7) (L : ℝ), 2 ≤ L → lrd D ≤ 2 * L → Real.log D.host.d ≤ 2 * L → Real.log (Ideal.absNorm D.host.ccK) ≤ 2 * L → (∃ NA : ℕ, 0 < NA ∧ (∀ a ∈ D.host.AA, IsIntegral ℤ ((NA : D.host.E) * a)) ∧ Real.log NA ≤ 4 * L) ∧ ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ∈ D.host.AA ∧ 0 < Ideal.absNorm D.host.ccK ∧ (∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : D.host.E) * (2 * D.host.xi0)) ∧ Real.log m ≤ 4 * L) ∧ Real.log (1 / (2 * xiR D)) ≤ 3 * L ∧ fdeg D.host.E = D.R.f ∧ Real.log (dE D.host.E) ≤ 4 * fdeg D.host.E * L ∧ Real.log (rdE D.host.E) ≤ 2 * L ∧ D.R.f ≤ D.R.r ∧ 1 ≤ D.R.f ∧ ReciprocityTheory.ChartRestriction.G.FD.cc D.host.xi0 = -D.host.xi0 ∧ D.host.xi0 ≠ 0 ∧ (∀ τ : D.host.E →+* ℂ, ‖τ D.host.xi0‖ = xiR D) := by
  first | exact @GlobalTheory.HostClear.host_clear | exact GlobalTheory.HostClear.host_clear | (intros; apply GlobalTheory.HostClear.host_clear <;> assumption)
