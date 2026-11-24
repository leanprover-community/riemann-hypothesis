module

public import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdeleLogAbsoluteValueEqLogIdeleModule
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.ideleLogAbsoluteValue_eq_log_ideleModule : ∀ (E : Type) [Field E] [NumberField E] (d : (AdeleRing (𝓞 E) E)ˣ), GlobalTheory.Mem.Chr.CharModel.logNorm E d = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E d : ℝ) := by
  first | (exact @GlobalTheory.IdeleLogNormCompare.logNorm_eq_log_ideleModule) | (exact GlobalTheory.IdeleLogNormCompare.logNorm_eq_log_ideleModule) | (intros; apply GlobalTheory.IdeleLogNormCompare.logNorm_eq_log_ideleModule  <;> assumption)
