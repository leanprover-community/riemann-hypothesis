module

public import Formalism.GradedWeylDivisibility.StatementA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.GradedWeylDivisibility

open MvPolynomial

def idPoint (R : Type*) [CommRing R] (r n : ℕ) : Fin r × Fin n → R :=
  fun v => if v.1.val = v.2.val then 1 else 0

theorem eval_idPoint_lpMinor (R : Type*) [CommRing R] {r n : ℕ} (s : ℕ) (hr : s ≤ r)
    (hn : s ≤ n) : eval (idPoint R r n) (lpMinor R s hr hn) = 1 := by
  unfold lpMinor
  rw [RingHom.map_det]
  convert Matrix.det_one (R := R) (n := Fin s)
  ext p q
  simp [RingHom.mapMatrix_apply, idPoint, Matrix.one_apply]
  exact if_congr Fin.val_inj rfl rfl

theorem hwrow_sum_single_castLE {r s : ℕ} (hr : s ≤ r) (σ : Equiv.Perm (Fin s)) :
    (∑ q : Fin s, (Pi.single (Fin.castLE hr (σ q)) 1 : Fin r → ℕ)) =
      fun a => if a.val < s then 1 else 0 := by
  have h1 : (∑ q : Fin s, (Pi.single (Fin.castLE hr (σ q)) 1 : Fin r → ℕ)) =
      ∑ q : Fin s, (Pi.single (Fin.castLE hr q) 1 : Fin r → ℕ) :=
    Equiv.sum_comp σ (fun q => (Pi.single (Fin.castLE hr q) 1 : Fin r → ℕ))
  rw [h1]
  funext a
  rw [Finset.sum_apply]
  simp only [Pi.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a.val, h⟩]
    · exact if_pos (Fin.ext rfl)
    · intro b _ hb
      rw [if_neg]
      intro hab
      subst hab
      exact hb (Fin.ext rfl)
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    intro hab
    subst hab
    exact h b.isLt

theorem lpMinor_rowHom (R : Type*) [CommRing R] {r n : ℕ} (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    IsWeightedHomogeneous (rowW r n) (lpMinor R s hr hn)
      (fun a => if a.val < s then 1 else 0) := by
  unfold lpMinor
  rw [Matrix.det_apply]
  apply IsWeightedHomogeneous.sum
  intro σ _
  have hk : IsWeightedHomogeneous (rowW r n)
      (∏ i, (Matrix.of fun p q : Fin s =>
        (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R)) (σ i) i)
      (fun a : Fin r => if a.val < s then 1 else 0) := by
    rw [← hwrow_sum_single_castLE hr σ]
    apply IsWeightedHomogeneous.prod
    intro i _
    simp only [Matrix.of_apply]
    exact isWeightedHomogeneous_X R (rowW r n) _
  rw [← mem_weightedHomogeneousSubmodule] at hk ⊢
  rw [Units.smul_def]
  exact zsmul_mem hk _

end Formalism.GradedWeylDivisibility
