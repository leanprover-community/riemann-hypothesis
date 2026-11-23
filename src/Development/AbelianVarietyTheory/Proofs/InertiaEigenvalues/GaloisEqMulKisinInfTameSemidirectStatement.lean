module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisEqMulKisinInfTameSemidirect
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galois_eq_mul_kisinInf_tameSemidirect : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], (∀ g : GQ l, ∃ h ∈ GK (ϖ.field a), ∃ k ∈ ϖ.GKinf, g = h * k) ∧ (∀ k ∈ ϖ.GKinf, ∃ γ, Covers ↥LL.1 (thetaW a LL) ϖ k γ) ∧ (∀ γ : TameGal ↥LL.1 l e a, ∃ k ∈ ϖ.GKinf, Covers ↥LL.1 (thetaW a LL) ϖ k γ) ∧ (∀ (k : GQ l) (γ γ' : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ k γ → Covers ↥LL.1 (thetaW a LL) ϖ k γ' → γ = γ') ∧ (∀ (k k' : GQ l) (γ γ' : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ k γ → Covers ↥LL.1 (thetaW a LL) ϖ k' γ' → Covers ↥LL.1 (thetaW a LL) ϖ (k * k') (γ * γ')) ∧ (∀ k : GQ l, Covers ↥LL.1 (thetaW a LL) ϖ k (1 : TameGal ↥LL.1 l e a) ↔ k ∈ ϖ.GfieldInf a) ∧ ∀ (k : GQ l) (ζ : rootsOfUnity e ↥LL.1), Covers ↥LL.1 (thetaW a LL) ϖ k (TameGal.inertia ζ : TameGal ↥LL.1 l e a) → ∃ k' ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), Covers ↥LL.1 (thetaW a LL) ϖ (k' : GQ l) (TameGal.inertia ζ : TameGal ↥LL.1 l e a) ∧ (((ζ : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0 = (k' : GQ l) (ϖ.seq 0) := by
  first | exact @GlobalTheory.TameCover.main | exact GlobalTheory.TameCover.main | (intros; apply GlobalTheory.TameCover.main <;> assumption)
