module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFunctorRingPsiOperatorExistsOfGood
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

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.wachFunctorRing_psiOperator_exists_of_good : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∃ ψ : W.EE →ₗ[↥(OL LL)] W.EE, (∀ a x, ψ (W.φE a * x) = a * ψ x) ∧ (∀ g x, ψ (W.γE g x) = W.γE g (ψ x)) ∧ ∀ j < l, ∀ a, ψ (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE ((1 : (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)))) + (letπ : (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))))) ^ j * W.φE a) = if j = 0 then a else 0 := by
  first | exact @GlobalTheory.psiE_exists | exact GlobalTheory.psiE_exists | (intros; apply GlobalTheory.psiE_exists <;> assumption)
