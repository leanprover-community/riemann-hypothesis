module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisClassOfMonodromyEqZero
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galoisClass_of_monodromy_eq_zero : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat ↥(OL LL) ↥LL.1 l e a ι η H) (T : QLat LL) (R : GalDat (thetaW a LL) ϖ (sQ l) D T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → η < H → 8 * H + 1 < l → ∀ y ∈ D.Y, D.Mon y = 0 → ∀ c : ℕ, (l : ↥LL.1) ^ c • D.zeta y ∈ D.MM → ∃ κ₁ ∈ latticeFiniteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.L, R.ClassOf ((l : ↥LL.1) ^ c • y) κ₁ := by
  first | exact @GlobalTheory.BKGal.classOf_of_mon_eq_zero | exact GlobalTheory.BKGal.classOf_of_mon_eq_zero | (intros; apply GlobalTheory.BKGal.classOf_of_mon_eq_zero <;> assumption)
