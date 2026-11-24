module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
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

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

theorem _root_.GlobalTheory.T.wachInclusion_X_Q_frobenius : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; E.io W.X = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (D.locA l).π₁ ∧ E.io W.Q = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (D.locA l).ξ ∧ Function.Injective (inclR LL) ∧ Function.Injective E.ioE ∧ (∀ a, inclR LL (E.io (W.φA a)) = φRW LL (inclR LL (E.io a))) ∧ (∀ x : W.EE, (∃ y, inclR LL y = E.ioE x) → ∃ a : AA K LL, algebraMap _ W.EE a = x) ∧ ∀ j : ℕ, IsUnit (algebraMap (AA K LL) W.EE ((W.φA ^ j) W.X)) ∧ IsUnit (algebraMap (AA K LL) W.EE ((W.φA ^ j) W.Q)) := by
  first | exact @GlobalTheory.NL.IoXQ.main | exact GlobalTheory.NL.IoXQ.main | (intros; apply GlobalTheory.NL.IoXQ.main <;> assumption)
