module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
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

namespace GlobalTheory.LatticeSumMembership

open Formalism.MainNotions.TaylorLogMetric

theorem La_mem_sum :
    ∀ (D : Formalism.BasicNotions.D7) (T : Formalism.MainNotions.TaylorLogMetric.Tor D) {N N' : ℕ}
      (L : Submodule (NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (Fin N → (Formalism.BasicNotions.D7.host D).E))
      (L' : Submodule (NumberField.RingOfIntegers ((Formalism.BasicNotions.D7.host D).E)) (Fin N' → (Formalism.BasicNotions.D7.host D).E)),
      ∀ y ∈ Formalism.MainNotions.TaylorLogMetric.La D T L L', ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) ((Formalism.BasicNotions.D7.host D).E)) (w : Fin r → ℂ),
        (∀ (j : Fin r), b j ∈ Formalism.MainNotions.TaylorLogMetric.YYl D L L') ∧ (∀ (j : Fin r), w j ∈ Formalism.MainNotions.TaylorLogMetric.Tor.abelian₂ T) ∧
          y = ∑ j : Fin r, w j • Formalism.MainNotions.TaylorLogMetric.embV D T (b j) := by
  intro D T N N' L L' y hy
  unfold Formalism.MainNotions.TaylorLogMetric.La at hy
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    exact ⟨1, fun _ => A, fun _ => w, fun _ => hA, fun _ => hw, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, by simp⟩
  | add x z _ _ ihx ihz =>
    obtain ⟨r₁, b₁, w₁, hb₁, hw₁, rfl⟩ := ihx
    obtain ⟨r₂, b₂, w₂, hb₂, hw₂, rfl⟩ := ihz
    refine ⟨r₁ + r₂, Fin.append b₁ b₂, Fin.append w₁ w₂, ?_, ?_, ?_⟩
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa using hb₁ i
      · simpa using hb₂ i
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa using hw₁ i
      · simpa using hw₂ i
    · rw [Fin.sum_univ_add]
      simp
  | neg x _ ihx =>
    obtain ⟨r, b, w, hb, hw, rfl⟩ := ihx
    refine ⟨r, b, fun j => -w j, hb, fun j => T.abelian₂.neg_mem (hw j), ?_⟩
    simp [neg_smul, Finset.sum_neg_distrib]

end GlobalTheory.LatticeSumMembership
