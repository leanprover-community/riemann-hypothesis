module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTameFieldGoodLatticePotentiallyCrystalline
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

theorem _root_.GlobalTheory.T.exists_tameField_goodLattice_potentiallyCrystalline : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → a = (l - 1).factorial → ∀ (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (Sig : Finset ((pc Pl h hN hF hS).Iner →* (↥LL.1)ˣ)) (Fr : Gl l) (N : ℕ), (pc Pl h hN hF hS).IsFrob Fr → FrobStable (pc Pl h hN hF hS).Iner Fr Sig → 1 ∈ Sig → Sig.card ≤ N → N < l → (∀ χ ∈ Sig, ∀ g : (pc Pl h hN hF hS).Iner, (g : Gl l) ∈ (pc Pl h hN hF hS).H → χ g = 1) → (∀ χ ∈ Sig, Nat.Coprime (orderOf χ) l) → ∃ Sig' : Finset (ZMod e), (∀ c ∈ Sig', (l : ZMod e) * c ∈ Sig') ∧ (0 : ZMod e) ∈ Sig' ∧ Sig'.card ≤ N ∧ maxPeriod l Sig' = Formalism.MainNotions.ElementDenominator.rPrime (pc Pl h hN hF hS).Iner Fr Sig ∧ ∀ T : QLat LL, (pc Pl h hN hF hS).IsPotCrys T.ρ → (pc Pl h hN hF hS).InertiaThrough T.ρ Sig → IsCrys (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ ∧ TameType a ϖ Pl T Sig' := by
  first | exact @GlobalTheory.GoodLatt.main | exact GlobalTheory.GoodLatt.main | (intros; apply GlobalTheory.GoodLatt.main <;> assumption)
