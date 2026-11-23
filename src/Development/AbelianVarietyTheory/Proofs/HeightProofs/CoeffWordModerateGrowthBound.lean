module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotMemOfMulExp
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

namespace GlobalTheory.TypeSum.CoefClos

theorem wordF_fam {n : ℕ} {ε : Fin n → Bool} {N : ℕ} {f : Mx n → ℂ} {F : List (Mx n) → Mx n → ℂ}
    (h1 : ∀ g ∈ UJset ε, F [] g = f g) (h2 : IsDerFam ε F) (h3 : FamGrowth ε N F) (u : List (Ltr ε)) :
    ∃ G : List (Mx n) → Mx n → ℂ, (∀ g ∈ UJset ε, G [] g = wordF u f g) ∧ IsDerFam ε G ∧ FamGrowth ε N G := by
  induction u with
  | nil => exact ⟨F, h1, h2, h3⟩
  | cons x u ih =>
    obtain ⟨G, k1, k2, k3⟩ := ih
    rcases x with ⟨X, hX⟩ | ⟨k, hk⟩
    · refine ⟨fun l => G (l ++ [X]), fun g hg => (CSm.rder_eq k1 k2 hX hg).symm, fun l hl Y hY g hg => ?_,
        fun l hl => k3 _ ?_⟩
      · exact k2 (l ++ [X]) (fun Z hZ => (List.mem_append.1 hZ).elim (hl Z) (by simp_all)) Y hY g hg
      · exact fun Z hZ => (List.mem_append.1 hZ).elim (hl Z) (by simp_all)
    · have hkU := K_le_UJ hk
      have hmap : ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) →
          ∀ Z ∈ l.map (fun Y => k⁻¹ * Y * k), Z ∈ lieSet ε := by
        intro l hl Z hZ
        obtain ⟨Z, hZ', rfl⟩ := List.mem_map.1 hZ
        exact GlobalTheory.LowTypeDetermined.conj_mem_lie (isUnit_Jm ε) hkU (hl Z hZ')
      refine ⟨fun l g => G (l.map fun Y => k⁻¹ * Y * k) (g * k),
        fun g hg => k1 _ (mul_mem_UJ hg hkU), fun l hl Y hY g hg => ?_, fun l hl => ?_⟩
      · have hY' : k⁻¹ * Y * k ∈ lieSet ε := GlobalTheory.LowTypeDetermined.conj_mem_lie (isUnit_Jm ε) hkU hY
        have := k2 _ (hmap l hl) _ hY' (g * k) (mul_mem_UJ hg hkU)
        refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
        show G _ (g * NormedSpace.exp (t • Y) * k) = G _ (g * k * NormedSpace.exp (t • (k⁻¹ * Y * k)))
        rw [← exp_conj_smul hkU Y t]
        congr 1
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc g k, mul_inv_UJ hkU, Matrix.mul_one]
      · obtain ⟨C, hC⟩ := k3 _ (hmap l hl)
        refine ⟨max C 0 * (1 + Formalism.REAL.hs k) ^ N, fun g hg => (hC _ (mul_mem_UJ hg hkU)).trans ?_⟩
        have h0 : 0 ≤ 1 + Formalism.REAL.hs (g * k) := by
          unfold Formalism.REAL.hs; positivity
        calc C * (1 + Formalism.REAL.hs (g * k)) ^ N ≤ max C 0 * (1 + Formalism.REAL.hs (g * k)) ^ N :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg h0 N)
          _ ≤ max C 0 * ((1 + Formalism.REAL.hs g) * (1 + Formalism.REAL.hs k)) ^ N :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (one_add_hs_mul_le g k) N) (le_max_right _ _)
          _ = _ := by rw [mul_pow]; ring

theorem wordF_growth : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (f : Mx n → ℂ) (F : List (Mx n) → Mx n → ℂ),
    (∀ g ∈ UJset ε, F [] g = f g) → IsDerFam ε F → FamGrowth ε N F →
    ∀ u : List (Ltr ε), ∃ C : ℝ, ∀ g ∈ UJset ε, ‖wordF u f g‖ ≤ C * (1 + Formalism.REAL.hs g) ^ N := by
  intro n ε N f F h1 h2 h3 u
  obtain ⟨G, k1, -, k3⟩ := wordF_fam h1 h2 h3 u
  obtain ⟨C, hC⟩ := k3 [] (by simp)
  exact ⟨C, fun g hg => k1 g hg ▸ hC g hg⟩

end GlobalTheory.TypeSum.CoefClos
