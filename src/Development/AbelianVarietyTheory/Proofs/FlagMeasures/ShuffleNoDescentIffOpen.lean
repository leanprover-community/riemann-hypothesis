module

public import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
public import Mathlib.Order.WellFounded

@[expose] public section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory

theorem shuffle_first_block_upper (a n : ℕ) (σ : Equiv.Perm (Fin n))
    (h : ∀ i j : Fin n, (i : ℕ) < a → a ≤ (j : ℕ) → (σ j : ℕ) ≠ σ i + 1)
    (i : Fin n) (hi : (i : ℕ) < a) (k : ℕ) :
    ∀ j : Fin n, (σ j : ℕ) = σ i + k → (j : ℕ) < a := by
  induction k with
  | zero =>
    intro j hj
    have : σ j = σ i := Fin.ext (by simpa using hj)
    rw [σ.injective this]; exact hi
  | succ k ih =>
    intro j hj
    have hlt : (σ i : ℕ) + k < n := by have := (σ j).isLt; omega
    have h1 : ((σ (σ.symm ⟨σ i + k, hlt⟩) : Fin n) : ℕ) = σ i + k := by simp
    have h2 := ih _ h1
    by_contra hc
    exact h _ j h2 (not_lt.mp hc) (by omega)

theorem shuffle_noDescent_iff_open :
    ∀ (a b n : ℕ) (σ : Equiv.Perm (Fin n)), n = a + b → (∀ i j : Fin n, i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j) → ((∀ i j : Fin n, (i : ℕ) < a → a ≤ (j : ℕ) → (σ j : ℕ) ≠ σ i + 1) ↔ ∀ j : Fin n, (σ j : ℕ) = if (j : ℕ) < a then b + j else j - a) := by
  intro a b n σ hn hmono
  constructor
  · intro h
    have hup : ∀ i j : Fin n, (i : ℕ) < a → a ≤ (j : ℕ) → σ j < σ i := by
      intro i j hi hj
      by_contra hc
      have hc' : (σ i : ℕ) ≤ σ j := not_lt.mp hc
      have := shuffle_first_block_upper a n σ h i hi (σ j - σ i) j (by omega)
      omega
    let ρ : Fin n → Fin n := fun k =>
      ⟨if (k : ℕ) < b then a + k else k - b, by have := k.isLt; split_ifs <;> omega⟩
    have hρ : ∀ k, (ρ k : ℕ) = if (k : ℕ) < b then a + k else k - b := fun _ => rfl
    have hs : StrictMono (fun k => σ (ρ k)) := by
      intro k l hkl
      have hkl' : (k : ℕ) < l := hkl
      have hk := hρ k
      have hl := hρ l
      have hl2 := l.isLt
      show σ (ρ k) < σ (ρ l)
      by_cases h1 : (k : ℕ) < b
      · by_cases h2 : (l : ℕ) < b
        · rw [if_pos h1] at hk; rw [if_pos h2] at hl
          exact hmono _ _ (Fin.lt_def.mpr (by omega)) (Or.inr (by omega))
        · rw [if_pos h1] at hk; rw [if_neg h2] at hl
          exact hup _ _ (by omega) (by omega)
      · have h2 : ¬ (l : ℕ) < b := by omega
        rw [if_neg h1] at hk; rw [if_neg h2] at hl
        exact hmono _ _ (Fin.lt_def.mpr (by omega)) (Or.inl (by omega))
    have hid : ∀ k, σ (ρ k) = k := fun k =>
      le_antisymm (hs.dual.le_apply (x := OrderDual.toDual k)) hs.le_apply
    intro j
    have hj := j.isLt
    let k : Fin n := ⟨if (j : ℕ) < a then b + j else j - a, by split_ifs <;> omega⟩
    have hk : (k : ℕ) = if (j : ℕ) < a then b + j else j - a := rfl
    have hjk : ρ k = j := by
      apply Fin.ext
      rw [hρ, hk]
      split_ifs <;> omega
    rw [← hk, ← hid k, hjk]
  · intro h i j hi hj
    have h1 := h i
    have h2 := h j
    have := j.isLt
    rw [if_pos hi] at h1
    rw [if_neg (by omega)] at h2
    omega

end GlobalTheory
