module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.DiagInt

theorem finMul {D : D7} {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, w, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w' => ?_, u * w, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w') (hb w')
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem intAt_add {D : D7} {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a + b ∈ intAt D (· = v) :=
  ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add (f := _)]; exact add_mem ha.2 hb.2⟩

theorem intAt_mul {D : D7} {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [RingHom.map_mul]; exact finMul ha.2 hb.2⟩

theorem mul_sub_one {D : D7} {v : Pl D} {a b : AE D} (ha : a - 1 ∈ intAt D (· = v)) (hb : b - 1 ∈ intAt D (· = v)) :
    a * b - 1 ∈ intAt D (· = v) := by
  have e : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by ring
  rw [e]
  exact intAt_add (intAt_add (intAt_mul ha hb) ha) hb

theorem inv_diag_mul {R : Type*} [CommRing R] {ρ : ℕ} (t : GL (Fin ρ) R) (ht : ∀ i j, i ≠ j → t.1 i j = 0)
    (j : Fin ρ) : (t⁻¹).1 j j * t.1 j j = 1 := by
  have h0 : (t⁻¹).1 * t.1 = 1 := t.inv_mul
  have h := congrFun (congrFun h0 j) j
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  rw [← h, Finset.sum_eq_single j]
  · intro k _ hk; rw [ht k j hk, mul_zero]
  · intro h'; exact absurd (Finset.mem_univ j) h'

theorem diag_int : ∀ (D : D7) (ρ : ℕ) (v : Pl D) (t : GL (Fin ρ) (AE D)), (∀ i j, i ≠ j → t.1 i j = 0) → (∀ i, (t⁻¹).1 i i - 1 ∈ intAt D (· = v)) → (∀ i j : Fin ρ, j.1 = i.1 + 1 → t.1 i i * (t⁻¹).1 j j - 1 ∈ intAt D (· = v)) → (∀ i : Fin ρ, i.1 + 1 = ρ → t.1 i i - 1 ∈ intAt D (· = v)) → ∀ i, t.1 i i - 1 ∈ intAt D (· = v) := by
  intro D ρ v t ht _ hr hl
  have key : ∀ k : ℕ, ∀ i : Fin ρ, i.1 + k + 1 = ρ → t.1 i i - 1 ∈ intAt D (· = v) := by
    intro k
    induction k with
    | zero => intro i hi; exact hl i (by omega)
    | succ k ih =>
      intro i hi
      have hj : i.1 + 1 < ρ := by omega
      let j : Fin ρ := ⟨i.1 + 1, hj⟩
      have h1 := hr i j rfl
      have h2 := ih j (by simp [j]; omega)
      have e : t.1 i i = t.1 i i * (t⁻¹).1 j j * t.1 j j := by
        rw [mul_assoc, inv_diag_mul t ht j, mul_one]
      rw [e]
      exact mul_sub_one h1 h2
  intro i
  exact key (ρ - 1 - i.1) i (by omega)

end GlobalTheory.FinPl.DiagInt
