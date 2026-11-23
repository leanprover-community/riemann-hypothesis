module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace InfiniteFiniteFactorization

open Classical

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem stepInf (h6 : G6) {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {S : Finset (Pl E)}
    {Y Y' : Submodule ℂ (XB E a)} (hY : YOK ψ S Y) (hY' : YOK ψ S Y') (m : Pl E → ℕ)
    (h : St ψ S Y Y' 0 m) : ∀ n, n ≤ a - 1 → St ψ S Y Y' n m := by
  intro n
  induction n with
  | zero => intro _; exact h
  | succ n ih => intro hn; exact h6 E a ψ hψ S Y Y' hY hY' n m (by omega) (ih (by omega))

theorem stepFin (h7 : G7) {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {S : Finset (Pl E)}
    {Y Y' : Submodule ℂ (XB E a)} (hY : YOK ψ S Y) (hY' : YOK ψ S Y') (w : Pl E) (hw : w ∈ S)
    (n : ℕ) (m : Pl E → ℕ) (hm : m w = 0) (h : St ψ S Y Y' n m) :
    ∀ k, k ≤ a - 1 → St ψ S Y Y' n (Function.update m w k) := by
  intro k
  induction k with
  | zero => intro _; rw [Function.update_eq_self_iff.mpr hm.symm]; exact h
  | succ k ih =>
    intro hk
    have h' := h7 E a ψ hψ S Y Y' hY hY' n (Function.update m w k) w hw
      (by simp only [Function.update_self]; omega) (ih (by omega))
    simpa only [Function.update_self, Function.update_idem] using h'

end InfiniteFiniteFactorization

open InfiniteFiniteFactorization in
theorem whittaker_factorization_places : G6 → G7 → FourierInductionSteps := by
  classical
  intro h6 h7 E _ _ _ a ψ hψ S Y Y' hY hY' h0
  have h1 := stepInf h6 hψ hY hY' (fun _ => 0) h0 (a - 1) le_rfl
  have key : ∀ T : Finset (Pl E), T ⊆ S →
      St ψ S Y Y' (a - 1) (fun w => if w ∈ T then a - 1 else 0) := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · intro _
      simpa using h1
    · intro x T hx ih hT
      have h := stepFin h7 hψ hY hY' x (hT (Finset.mem_insert_self x T)) (a - 1)
        (fun w => if w ∈ T then a - 1 else 0) (by simp [hx])
        (ih (subset_trans (Finset.subset_insert x T) hT)) (a - 1) le_rfl
      convert h using 1
      funext w
      by_cases hw : w = x
      · subst hw; simp
      · simp [hw]
  exact key S subset_rfl

end PositivityTheory.jumpWindows

end
