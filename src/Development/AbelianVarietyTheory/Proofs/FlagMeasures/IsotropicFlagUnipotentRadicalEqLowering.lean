module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadFullFlag

theorem form_uMat {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star (uMat g *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (uMat g *ᵥ y)) = star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  have h : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  rw [star_mulVec, ← dotProduct_mulVec]
  simp only [mulVec_mulVec, ← Matrix.mul_assoc, h]

private theorem dotProduct_Jm_uMat_sub_one {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ ((uMat g - 1) *ᵥ y)) =
      -(star ((uMat g - 1) *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y)) -
        star ((uMat g - 1) *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ ((uMat g - 1) *ᵥ y)) := by
  have h := form_uMat g x y
  simp only [sub_mulVec, one_mulVec, star_sub, mulVec_sub, dotProduct_sub, sub_dotProduct] at h ⊢
  linear_combination h

theorem flagN_eq_lowers : ∀ (n a : ℕ) (ε : Fin n → Bool) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (W' : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsDualFlag (Formalism.REAL.Jm ε) W (2 * a + 1) → W (2 * a + 1) = ⊤ → (∀ i : Fin (a + 1), W' i = W i) → flagN ε W' = {g | uMat g - 1 ∈ lowers W 0} := by
  intro n a ε W W' hF htop hW'
  obtain ⟨hmono, -, hstab, hdual⟩ := hF
  have hmem : ∀ y, y ∈ W (2 * a + 1) := fun y => by rw [htop]; exact Submodule.mem_top

  have horth : ∀ b, b ≤ 2 * a + 1 → ∀ y,
      y ∈ W (2 * a + 1 - b) ↔ ∀ x ∈ W b, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 :=
    fun b hb y => (hdual b hb y).trans ⟨fun h => h.2, fun h => ⟨hmem y, h⟩⟩
  ext g
  have hsub : ∀ y, (uMat g - 1) *ᵥ y = uMat g *ᵥ y - y := fun y => by
    rw [sub_mulVec, one_mulVec]
  unfold GlobalTheory.FlagMeas.flagN
  simp only [Set.mem_setOf_eq, mem_lowers, add_zero]
  constructor
  · rintro ⟨h1, h2⟩

    have hlow : ∀ b, b < a → ∀ y ∈ W (b + 1), (uMat g - 1) *ᵥ y ∈ W b := by
      intro b hb y hy
      have := h1 ⟨b, hb⟩ y (by rw [hW']; exact hy)
      rw [hW'] at this
      rw [hsub]; exact this
    have hmid : ∀ y ∈ W (a + 1), (uMat g - 1) *ᵥ y ∈ W a := by
      intro y hy
      have hy' : ∀ x ∈ W' (Fin.last a), star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 := by
        rw [hW']
        have e : 2 * a + 1 - a = a + 1 := by omega
        exact (horth a (by omega) y).1 (by rw [e]; exact hy)
      have := h2 y hy'
      rw [hW'] at this
      rw [hsub]; exact this

    have hup : ∀ k, k ≤ a → ∀ y ∈ W (2 * a + 1 - k + 1),
        (uMat g - 1) *ᵥ y ∈ W (2 * a + 1 - k) := by
      intro k
      induction k with
      | zero =>
        intro _ y _
        simpa using hmem ((uMat g - 1) *ᵥ y)
      | succ k ih =>
        intro hk y hy
        rw [horth (k + 1) (by omega)]
        intro x hx
        have hx' : (uMat g - 1) *ᵥ x ∈ W k := hlow k (by omega) x hx
        have hyk : y ∈ W (2 * a + 1 - k) := by
          have e : 2 * a + 1 - (k + 1) + 1 = 2 * a + 1 - k := by omega
          rw [e] at hy; exact hy
        have hgy : (uMat g - 1) *ᵥ y ∈ W (2 * a + 1 - k) :=
          ih (by omega) y (hmono (by omega : 2 * a + 1 - k ≤ 2 * a + 1 - k + 1) hyk)
        rw [dotProduct_Jm_uMat_sub_one, (horth k (by omega) y).1 hyk _ hx',
          (horth k (by omega) _).1 hgy _ hx']
        simp
    intro b y hy
    rcases lt_trichotomy b a with hb | hb | hb
    · exact hlow b hb y hy
    · subst hb; exact hmid y hy
    · by_cases hbm : 2 * a + 1 ≤ b
      · rw [hstab b hbm]; exact hmem _
      · have hk : b = 2 * a + 1 - (2 * a + 1 - b) := by omega
        have := hup (2 * a + 1 - b) (by omega) y (by rw [← hk]; exact hy)
        rw [← hk] at this; exact this
  · intro h
    refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
    · rw [hW'] at hy ⊢
      rw [← hsub]; exact h i y hy
    · rw [hW'] at hy ⊢
      have hy' : y ∈ W (a + 1) := by
        have e : 2 * a + 1 - a = a + 1 := by omega
        rw [← e]; exact (horth a (by omega) y).2 hy
      rw [← hsub]; exact h a y hy'

end GlobalTheory.RadFullFlag
