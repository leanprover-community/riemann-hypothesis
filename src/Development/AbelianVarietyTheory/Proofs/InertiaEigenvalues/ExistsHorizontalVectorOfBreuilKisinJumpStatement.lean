module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsEqAlgebraMapAddPowMul
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUltrametricDistFinExt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHorizontalVectorOfBreuilKisinJump
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_horizontal_vector_of_breuilKisin_jump : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι), (∀ m ∈ P.M, P.EN m ∈ P.Man) → ∀ i ∈ P.jumps, ∃ (n : ℕ) (d : Fin n → P.D) (c : Fin n → ZMod a → AdjoinRoot (Polynomial.X ^ e + Polynomial.C (l : ↥LL.1))), (∀ k, P.xi (d k) ∈ P.MMl) ∧ GlobalTheory.BKGal.JumpDR.InEhat ↥(OL LL) ↥LL.1 l e i (GlobalTheory.BKGal.JumpDR.hsum P (fun k => GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) (c k)) (fun k => P.xi (d k))) ∧ ¬ GlobalTheory.BKGal.JumpDR.InEhat ↥(OL LL) ↥LL.1 l e (i + 1) (GlobalTheory.BKGal.JumpDR.hsum P (fun k => GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) (c k)) (fun k => P.xi (d k))) := by
  first | exact @GlobalTheory.BKGal.JumpDR.Horiz.main | exact GlobalTheory.BKGal.JumpDR.Horiz.main | (intros; apply GlobalTheory.BKGal.JumpDR.Horiz.main <;> assumption)
