import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodChernWeilOfGoodTopChernForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernNumbersEqIntegralChernFormsSmoothMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceIntersectionNumberAdjacentSwapNeg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmChernRootsMulFibrePoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricTopChernFormIntegralEqSmooth

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagPush

theorem perm_submonoid_eq_top_of_adj (k : ℕ) (T : Submonoid (Equiv.Perm (Fin k)))
    (h : ∀ a b : Fin k, (b : ℕ) = a + 1 → Equiv.swap a b ∈ T) : T = ⊤ := by
  cases k with
  | zero =>
    rw [eq_top_iff]
    intro x _
    have : x = 1 := Subsingleton.elim _ _
    rw [this]; exact T.one_mem
  | succ n =>
    rw [eq_top_iff, ← Equiv.Perm.mclosure_swap_castSucc_succ, Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩
    exact h _ _ (by simp)

theorem alternating_of_adjacent_swap (ι : Type) [Fintype ι] (m : ι → ℕ)
    (L : MvPolynomial (Root m) ℝ →ₗ[ℝ] ℝ)
    (hL : ∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q,
      L (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - L Q)
    (w : ∀ τ, Equiv.Perm (Fin (m τ))) (Q : MvPolynomial (Root m) ℝ) :
    L (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) Q) =
      (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) * L Q := by
  let S : Submonoid (∀ τ, Equiv.Perm (Fin (m τ))) :=
    { carrier := {w | ∀ Q, L (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) Q) =
        (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) * L Q}
      one_mem' := by
        intro Q
        have : (fun x : Root m => (⟨x.1, (1 : ∀ τ, Equiv.Perm (Fin (m τ))) x.1 x.2⟩ : Root m)) = id := by
          funext x; rfl
        rw [this, rename_id]
        simp
      mul_mem' := by
        intro v w hv hw Q
        have : (fun x : Root m => (⟨x.1, (v * w) x.1 x.2⟩ : Root m)) =
            (fun x : Root m => (⟨x.1, v x.1 x.2⟩ : Root m)) ∘
              (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) := by
          funext x; rfl
        simp only [Set.mem_setOf_eq] at hv hw ⊢
        rw [this, ← rename_rename, hv, hw]
        simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib, Units.val_mul, Int.cast_mul]
        ring }
  have hS : S = ⊤ := by
    have htop : (⊤ : Submonoid (∀ τ, Equiv.Perm (Fin (m τ)))) =
        Submonoid.pi Set.univ (fun τ => (⊤ : Submonoid (Equiv.Perm (Fin (m τ))))) := by
      ext x; simp [Submonoid.mem_pi]
    rw [eq_top_iff, htop, ← Submonoid.iSup_map_mulSingle, iSup_le_iff]
    intro τ
    rw [Submonoid.map_le_iff_le_comap]
    rw [perm_submonoid_eq_top_of_adj (m τ) (Submonoid.comap (MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ) S) ?_]
    intro a b hab Q
    have hf : (fun x : Root m => (⟨x.1, (MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ
        (Equiv.swap a b)) x.1 x.2⟩ : Root m)) = Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩ := by
      funext ⟨σ, c⟩
      by_cases h : σ = τ
      · subst h
        simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
        rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
        by_cases h1 : c = a
        · subst h1; simp
        · by_cases h2 : c = b
          · subst h2; simp [h1]
          · simp [h1, h2]
      · simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h, Equiv.Perm.coe_one, id]
        rw [Equiv.swap_apply_of_ne_of_ne]
        · intro e; exact h (congrArg Sigma.fst e)
        · intro e; exact h (congrArg Sigma.fst e)
    have hab' : a ≠ b := by
      intro e; subst e; omega
    have hs : (∏ σ, Equiv.Perm.sign ((MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ
        (Equiv.swap a b)) σ)) = -1 := by
      have : ∀ σ, Equiv.Perm.sign ((MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ
          (Equiv.swap a b)) σ) = (Pi.mulSingle τ (Equiv.Perm.sign (Equiv.swap a b)) : ι → ℤˣ) σ := by
        intro σ
        by_cases h : σ = τ
        · subst h; simp
        · simp [Pi.mulSingle_eq_of_ne h]
      simp only [this, Finset.prod_pi_mulSingle', Finset.mem_univ, if_true]
      exact Equiv.Perm.sign_swap hab'
    show L _ = _
    rw [hf, hs, hL τ a b hab Q]
    simp
  have hw : w ∈ S := by rw [hS]; trivial
  exact hw Q

end GlobalTheory.FlagPush
end

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearForm_alternating_of_adjacent_swap_blocks : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (L : MvPolynomial (Root m) ℝ →ₗ[ℝ] ℝ), (∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q, L (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - L Q) → ∀ (w : ∀ τ, Equiv.Perm (Fin (m τ))) (Q : MvPolynomial (Root m) ℝ), L (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) Q) = (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) * L Q := by
  atlas_forward_decl GlobalTheory.FlagPush.alternating_of_adjacent_swap
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem linForm_eq_of_antisymm_eq : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (L : MvPolynomial (Root m) ℝ →ₗ[ℝ] ℝ), (∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q, L (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - L Q) → ∀ Q Q' : MvPolynomial (Root m) ℝ, antisymm Q = antisymm Q' → L Q = L Q' := by
  intro ι _ m L hL Q Q' h
  have sq : ∀ u : ℤˣ, ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
    intro u
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  have key : ∀ P : MvPolynomial (Root m) ℝ,
      L (antisymm P) = (Fintype.card (∀ τ, Equiv.Perm (Fin (m τ))) : ℝ) * L P := by
    intro P
    simp only [GlobalTheory.GoodMetric.antisymm, map_sum, map_zsmul]
    rw [Finset.sum_congr rfl (fun w _ => by
      rw [GlobalTheory.T.linearForm_alternating_of_adjacent_swap_blocks ι m L hL w P, zsmul_eq_mul, ← mul_assoc, sq, one_mul])]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card (∀ τ, Equiv.Perm (Fin (m τ))) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ∀ τ, Equiv.Perm (Fin (m τ)))).ne'
  have e := congrArg L h
  rw [key, key] at e
  exact mul_left_cancel₀ hc e

end GlobalTheory.FlagPush
end

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearForm_eq_of_weylAntisymmetrization_eq : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (L : MvPolynomial (Root m) ℝ →ₗ[ℝ] ℝ), (∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q, L (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - L Q) → ∀ Q Q' : MvPolynomial (Root m) ℝ, antisymm Q = antisymm Q' → L Q = L Q' := by
  atlas_forward_decl GlobalTheory.FlagPush.linForm_eq_of_antisymm_eq
end

section
section
noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.FlagPushProof

theorem flagPushForward : GlobalTheory.Published.FlagPushForward := by
  intro F _ _ X Y ι _ m E E' φ f gr hf hg Q R hR
  have hswap := GlobalTheory.T.flagSpace_intersectionNumber_adjacent_swap_neg F X Y ι m E E' φ f hf gr hg
  refine GlobalTheory.T.linearForm_eq_of_weylAntisymmetrization_eq ι m (Y.interPoly gr) hswap Q (chernRoots m R * fibrePoint m) ?_
  rw [hR, antisymm_chernRoots_mul_fibrePoint]

end GlobalTheory.FlagPushProof
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullFlagBundle_pushForward_formula : GlobalTheory.Published.FlagPushForward := by
  atlas_forward_decl GlobalTheory.FlagPushProof.flagPushForward
end

section
namespace GlobalTheory.GoodMetric

theorem goodChernWeil : GlobalTheory.Published.GoodChernWeil :=
  goodChernWeil_of_goodTopChernForm GlobalTheory.T.goodMetric_topChernForm_integral_eq_smooth GlobalTheory.T.chernNumbers_eq_integral_chernForms_smoothMetric GlobalTheory.T.fullFlagBundle_pushForward_formula

end GlobalTheory.GoodMetric
end
