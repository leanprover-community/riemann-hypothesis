module

public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OtherLossSum
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

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory.OtherLoss

theorem inertLoss_primeSum : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, ∀ j ∈ SizeData₂.lifts (Fm.D x i), ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ (G.IsResidueClassZero (Fm.D x i) p ∨ G.IsSg (Fm.D x i) p) ∧ (p : ℝ) ≤ (Fm.L x i).sc.X'' (Fm.D x i).R.n ∧ ¬ (G.IsResidueClassZero (Fm.D x i) p ∧ G.hP (Fm.D x i) p = 0)) → ∑ p ∈ P, 2 * Real.log (p : ℝ) * |EatI (Fm.L x i) Fm.GK Fm.cX.err j p| ≤ C * (Fm.L x i).B0 := by
  intro eps Fm _ _
  refine ⟨848, 0, by norm_num, fun x _ hx i j hj P hP => ?_⟩
  have h := sum_eatI (K := Fm.GK) (c := Fm.cX.err) (Fm.sizes x hx i) Fm.fixed.2.1 Fm.fixed.2.2.1 Fm.fixed.2.2.2.2.1 hj P
    (fun p hp => ⟨(hP p hp).1, (hP p hp).2.2.1⟩)
  calc _ = 2 * ∑ p ∈ P, |EatI (Fm.L x i) Fm.GK Fm.cX.err j p| * Real.log (p : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ ≤ _ := by linarith

end GlobalTheory.OtherLoss
