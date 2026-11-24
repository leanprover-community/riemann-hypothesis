module

public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RunParams
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

theorem _root_.GlobalTheory.T.eta_bound_length_unit_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP C => (dat p i).q ≤ (Fm.D x ι).R.m ∧ 0 ≤ GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m 5 1 ∧ lenT p i PP * GlobalTheory.EtaAn.p16 (Fm.D x ι).host.E (Fm.D x ι).R.r ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Fm.D x ι).R.m 5 1 ≤ C * unitE p ∧ ∀ DF : ℕ, 1 ≤ DF → (DF : ℝ) ≤ (Fm.L x ι).sc.b ^ 2 → GlobalTheory.EtaAn.RunOK (Fm.D x ι).host.E (Fm.D x ι).R.r DF ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Real.sqrt (90 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r + DF))) (Fm.D x ι).R.m ∧ ∀ s : ℝ, (Y.d.l₂.M : ℝ) * s < (Fm.L x ι).sc.b → Real.sqrt s < ReciprocityTheory.ChartRestriction.G.I2.th (E := (Fm.D x ι).host.E) ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) (Real.sqrt (90 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r + DF))) := by
  first | exact @_root_.GlobalTheory.ThetaSizeBounds.run_params_alt | exact _root_.GlobalTheory.ThetaSizeBounds.run_params_alt | (intros; apply _root_.GlobalTheory.ThetaSizeBounds.run_params_alt <;> assumption)
end
