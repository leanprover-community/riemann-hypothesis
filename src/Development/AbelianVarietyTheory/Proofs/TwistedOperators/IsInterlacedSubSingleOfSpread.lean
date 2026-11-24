module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace GlobalTheory.SepReal

theorem interlaced_sub_single : ∀ {n : ℕ} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {mu : Fin n → ℝ},
    GlobalTheory.SepReal.Interlaced ε lam ε' mu → (∀ a c, a ≠ c → 2 ≤ |lam a - lam c|) → (∀ a i, mu i < lam a → mu i + 1 < lam a) →
      (∀ a i, lam a ≠ mu i) → ∀ s, GlobalTheory.SepReal.Interlaced ε (lam - Pi.single s 1) ε' mu := by
  intro n ε lam ε' mu hI hw hm hne s
  have h01 : ∀ a, (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a = 0 ∨ (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a = 1 := by
    intro a
    by_cases h : a = s
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hb : ∀ a, 0 ≤ (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a ∧ (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a ≤ 1 := by
    intro a
    rcases h01 a with h | h <;> rw [h] <;> norm_num
  have key : ∀ x y : Fin (n + 1) ⊕ Fin n, Sum.elim (lam - Pi.single s 1) mu y < Sum.elim (lam - Pi.single s 1) mu x ↔
      Sum.elim lam mu y < Sum.elim lam mu x := by
    rintro (a | i) (c | j)
    · simp only [Sum.elim_inl, Pi.sub_apply]
      by_cases hac : a = c
      · subst hac; simp
      · have hw' := hw a c hac
        have ha := h01 a
        have hc := h01 c
        generalize (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a = da at ha
        generalize (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) c = dc at hc
        rcases le_abs.1 hw' with h | h <;> rcases ha with rfl | rfl <;> rcases hc with rfl | rfl <;>
          constructor <;> intro h' <;> linarith
    · simp only [Sum.elim_inl, Sum.elim_inr, Pi.sub_apply]
      have hba := hb a
      constructor
      · intro h; linarith
      · intro h; have := hm a j h; linarith
    · simp only [Sum.elim_inl, Sum.elim_inr, Pi.sub_apply]
      have hbc := hb c
      constructor
      · intro h
        by_contra h'
        have hlt : mu i < lam c := lt_of_le_of_ne (not_lt.1 h') (fun e => hne c i e.symm)
        have := hm c i hlt
        linarith
      · intro h; linarith
    · simp
  intro x y h hz
  rw [key] at h
  exact hI x y h (fun z hz' => hz z ⟨(key z y).2 hz'.1, (key x z).2 hz'.2⟩)

end GlobalTheory.SepReal
