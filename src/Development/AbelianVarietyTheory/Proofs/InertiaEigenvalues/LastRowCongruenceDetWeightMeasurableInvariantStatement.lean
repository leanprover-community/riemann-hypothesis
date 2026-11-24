module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WtOfLastRowOfDetPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import GroundTheory.AutomorphicForms.ReductionMeasure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowCongruenceDetWeightMeasurableInvariant
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate

theorem _root_.GlobalTheory.T.lastRowCongruenceDetWeight_measurable_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m N : ℕ) (x : ℝ),
    Measurable (GlobalTheory.ZUnf.wt (E := E) (m := m) N x) ∧
    (∀ γ ∈ mirU E (m + 1) m, ∀ g, GlobalTheory.ZUnf.wt N x (ratGL E (m + 1) γ * g) = GlobalTheory.ZUnf.wt N x g) ∧
    ∀ (k : ℕ) (y : UnipotentBlockColumnIndex (m + 1) k k → Ad E) (g : GA E (m + 1)), GlobalTheory.ZUnf.wt N x (blkU y * g) = GlobalTheory.ZUnf.wt N x g := by
  first | exact @GlobalTheory.ZUnfWt.wt_measurable_invariant | exact GlobalTheory.ZUnfWt.wt_measurable_invariant | (intros; apply GlobalTheory.ZUnfWt.wt_measurable_invariant; all_goals assumption)
