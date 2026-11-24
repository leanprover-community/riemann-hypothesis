module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiQuotientInvariantsLiftRationally
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

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.xiQuotient_invariants_lift_rationally : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm5 D → adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (a e b : ℤ) (j : ℕ) (hle : Gj K j ≤ GK K), s ≤ j → a ≤ e → e ≤ b → IsCrysOn S S.W.GKs T → ∀ p : Qab (AinfSub l) (xiU (D.locA l)) a b →ₗ[ℤ_[l]] Qab (AinfSub l) (xiU (D.locA l)) a e, (∀ x, p (Submodule.Quotient.mk x) = Submodule.Quotient.mk x) → letI := zlMod LL T; ∀ z : (TensorProduct ℤ_[l] ↥T.L.T (Qab (AinfSub l) (xiU (D.locA l)) a e)), (∀ g, (repQ (D.locA l) (Gj K j) ((actTZ LL T).comp (Subgroup.inclusion hle)) a e) g z = z) → ∃ (k : ℕ) (x : (TensorProduct ℤ_[l] ↥T.L.T (Qab (AinfSub l) (xiU (D.locA l)) a b))), (∀ g, (repQ (D.locA l) (Gj K j) ((actTZ LL T).comp (Subgroup.inclusion hle)) a b) g x = x) ∧ LinearMap.lTensor ↥T.L.T p x = (l : ℤ_[l]) ^ k • z := by
  first | exact @GlobalTheory.InvariantLift.invariants_lift | exact GlobalTheory.InvariantLift.invariants_lift | (intros; apply GlobalTheory.InvariantLift.invariants_lift <;> assumption)
