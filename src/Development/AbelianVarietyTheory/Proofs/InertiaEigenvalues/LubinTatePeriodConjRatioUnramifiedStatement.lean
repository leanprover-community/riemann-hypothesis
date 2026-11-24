module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTatePeriodConjRatioUnramified
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

theorem _root_.GlobalTheory.T.lubinTate_period_conj_ratio_unramified : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (s : ℕ), 0 < s → ∀ (x : P.R.B), IsUnit x → P.φB^[s] x = (l : P.R.B) * x → P.ιB x ∈ Fil P 1 → P.ιB x ∉ Fil P 2 → (∀ j, 0 < j → j < s → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1) → ∀ g : GQ l, ∃ a : ↥(MaximalUnramifiedExtension l), fr l s a = a ∧ P.actQ g x = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B a * x := by
  first | exact @GlobalTheory.PMon.lt_period_conj_ratio | exact GlobalTheory.PMon.lt_period_conj_ratio | (intros; apply GlobalTheory.PMon.lt_period_conj_ratio <;> assumption)
