module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColA
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerDefectSubstFormalGroupLog
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

theorem _root_.GlobalTheory.T.frobeniusStickelberger_defect_subst_formal_group_log : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → MvPowerSeries.constantCoeff (g.add (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1)) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ MvPowerSeries.constantCoeff (g.sub (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ MvPowerSeries.constantCoeff (g.sub (GL3Theta.Xv 1) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ MvPowerSeries.constantCoeff (g.sub (GL3Theta.Xv 2) (GL3Theta.Xv 0) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ ∀ (c : ℂ_[p]) (f : Fin 3 → PowerSeries ℂ_[p]) (s : PowerSeries ℂ_[p]), GlobalTheory.FrobStick.defect f s = 0 → Matrix.det (Matrix.of fun i j => (PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) (f j) : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 3) ℂ_[p])) = 2 * PowerSeries.subst (g.add (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1)) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) * PowerSeries.subst (g.sub (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) * PowerSeries.subst (g.sub (GL3Theta.Xv 1) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) * PowerSeries.subst (g.sub (GL3Theta.Xv 2) (GL3Theta.Xv 0) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) := by
  first | exact @GlobalTheory.FrobStick.SubstLog.subst_log_formula | exact GlobalTheory.FrobStick.SubstLog.subst_log_formula | (intros; apply GlobalTheory.FrobStick.SubstLog.subst_log_formula <;> assumption)
