module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArchimedeanUniqueness.MetricDef
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmMetrisedLineLengthsEqSectionLieNorms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.cm_metrised_line_lengths_eq_section_lie_norms : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (n' : ℕ) (La c₁ : ℝ) (s : CMIn a e th jj n' La c₁) (em : K₁ →+* ℂ), letI := H.starRing; Arch.IsThNormAt a.D₀.P a.D₀.rig th em (s.Tl.n em ^ 2) ∧ (∀ i, Arch.IsLieNormAt s.xΨ.P (s.xΨ.v i) em (Real.log ((s.ℓΨ i).n em))) ∧ (∀ i, Arch.IsLieNormAt s.x'.P (s.x'.v i) em (Real.log ((s.ℓ' i).n em))) ∧ ∀ (DC : Out.DegPre ℂ) (p : Out.IsPullDeg em a.D₀ DC), (∀ thC, ThBC p th thC → Arch.IsThNormAt DC.P DC.rig thC (RingHom.id ℂ) (s.Tl.n em ^ 2)) ∧ ∀ m (u : epsR K₁ ⟶ a.D₀.P.A) (uC : epsR ℂ ⟶ DC.P.A), s.L.IsLetter m u → uC.left ≫ prj p = spMap (dualMap em) ≫ u.left → ∃ x, Arch.IsLieNormAt DC.P uC (RingHom.id ℂ) x ∧ (0 < La → x ≤ Real.log (La * (s.L.ℓ m).n em)) := by
  first | exact @GlobalTheory.ArcCM.NormTie.lengths_eq_norms | exact GlobalTheory.ArcCM.NormTie.lengths_eq_norms | (intros; apply GlobalTheory.ArcCM.NormTie.lengths_eq_norms <;> assumption)
