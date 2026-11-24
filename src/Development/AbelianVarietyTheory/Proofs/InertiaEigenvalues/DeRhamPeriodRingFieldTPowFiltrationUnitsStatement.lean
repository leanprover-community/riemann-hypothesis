module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnits
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

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI), IsField P.R.BdR ∧ Function.Injective P.ιB ∧ (∀ (a b : ℤ) (x : P.R.BdR), x ∈ Fil P a ↔ tz P b * x ∈ Fil P (a + b)) ∧ (∀ x ∈ Fil P 0, x ∉ Fil P 1 → ∃ y ∈ Fil P 0, x * y = 1) ∧ (∀ x : P.R.BdR, x ≠ 0 → ∃ a : ℤ, x ∈ Fil P a ∧ x ∉ Fil P (a + 1)) ∧ (∀ (a b : ℤ) (x y : P.R.BdR), x ∈ Fil P a → y ∈ Fil P b → x * y ∈ Fil P (a + b)) ∧ (∀ (a : ℤ) (g : GQ l) (x : P.R.BdR), x ∈ Fil P a → P.actQdR g x ∈ Fil P a) ∧ (∀ (a : ℤ) (g : GQ l), P.actQdR g (tz P a) = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a) ∧ (∀ a b : ℤ, tz P (a + b) = tz P a * tz P b) ∧ tz P 0 = 1 ∧ tz P 1 = P.ιB P.tB := by
  first | exact @GlobalTheory.PMon.bdR_tied | exact GlobalTheory.PMon.bdR_tied | (intros; apply GlobalTheory.PMon.bdR_tied <;> assumption)
