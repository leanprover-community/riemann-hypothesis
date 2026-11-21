import Formalism.LocalToGlobal.GlobalTheory.GL6.EqOneOfCoprimeTorsionTwoPrimes
import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement
import Formalism.LogVandermondeBounds.LogVandermondeProofs.MulSingleMulApplySelf
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ClearDenominatorsLattice

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions

section Model

variable {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc}

open Classical in

structure FreeRankModel (A : ColumnsAtT R C) where
  H : Type
  [grp : Group H]
  [finH : Fintype H]
  X : Type
  [finX : Fintype X]
  [act : MulAction (A.vT → H) X]
  e : ∀ v, (A.Fv v)ˣ ≃* H
  E : A.Mu0 ≃ₗ[ℂ] (X → ℂ)
  free : ∀ (g : A.vT → H) (x : X), g • x = x → g = 1
  intertw : ∀ v (a : (A.Fv v)ˣ) (φ : A.Mu0) (h : A.rhoT v a (φ : C.cls 0 → C.Y 0 → ℂ) ∈ A.Mu0) (x : X),
    E ⟨A.rhoT v a φ, h⟩ x = E φ ((Pi.mulSingle v (e v a) : A.vT → H) • x)

attribute [instance] FreeRankModel.grp FreeRankModel.finH FreeRankModel.finX FreeRankModel.act

variable (A : ColumnsAtT R C)

theorem rho_mem_forms (v : A.vT) (a : (A.Fv v)ˣ) (φ : A.Mu0) : A.rhoT v a (φ : C.cls 0 → C.Y 0 → ℂ) ∈ A.Mu0 :=
  A.Mu0_stable v a (Submodule.mem_map_of_mem φ.2)

theorem norm_eq_sum_rho (v : A.vT) (φ : A.Mu0) :
    A.Nm v (φ : C.cls 0 → C.Y 0 → ℂ) =
      ((∑ a : (A.Fv v)ˣ, (⟨A.rhoT v a φ, rho_mem_forms A v a φ⟩ : A.Mu0)) : A.Mu0) := by
  unfold ColumnsAtT.Nm
  rw [LinearMap.sum_apply, Submodule.coe_sum]

open Classical in
theorem mem_ramified_iff_model (M : FreeRankModel A) (φ : A.Mu0) :
    (φ : C.cls 0 → C.Y 0 → ℂ) ∈ A.Mram ↔ M.E φ ∈ Formalism.LogVandermondeBounds.product_first_zeroth_parts.ramSub A.vT M.H M.X ℂ := by
  have key : ∀ v, A.Nm v (φ : C.cls 0 → C.Y 0 → ℂ) = 0 ↔
      ∀ x : M.X, ∑ c : M.H, M.E φ ((Pi.mulSingle v c : A.vT → M.H) • x) = 0 := by
    intro v
    rw [norm_eq_sum_rho, Submodule.coe_eq_zero, ← M.E.map_eq_zero_iff, map_sum, funext_iff]
    refine forall_congr' fun x => ?_
    rw [Finset.sum_apply, Pi.zero_apply]
    have : ∑ a : (A.Fv v)ˣ, M.E ⟨A.rhoT v a φ, rho_mem_forms A v a φ⟩ x =
        ∑ a : (A.Fv v)ˣ, M.E φ ((Pi.mulSingle v (M.e v a) : A.vT → M.H) • x) :=
      Finset.sum_congr rfl fun a _ => M.intertw v a φ _ x
    rw [this]
    exact iff_of_eq (congrArg (· = (0 : ℂ))
      (Fintype.sum_equiv (M.e v).toEquiv _ _ fun a => rfl))
  unfold ColumnsAtT.Mram
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, SetLike.coe_mem, true_and]
  constructor
  · intro h v x; exact (key v).1 (h v) x
  · intro h v; exact (key v).2 (h v)

open Classical in
theorem ramified_rank_eq_finrank (M : FreeRankModel A) :
    A.du = Module.finrank ℂ (Formalism.LogVandermondeBounds.product_first_zeroth_parts.ramSub A.vT M.H M.X ℂ) := by
  have hle : A.Mram ≤ A.Mu0 := inf_le_left
  unfold ColumnsAtT.du
  rw [← (Submodule.comapSubtypeEquivOfLe hle).finrank_eq]
  have hmap : (A.Mram.comap A.Mu0.subtype).map (M.E : A.Mu0 →ₗ[ℂ] (M.X → ℂ)) =
      Formalism.LogVandermondeBounds.product_first_zeroth_parts.ramSub A.vT M.H M.X ℂ := by
    ext F
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      exact (mem_ramified_iff_model A M φ).1 hφ
    · intro hF
      refine ⟨M.E.symm F, ?_, by simp⟩
      show ((M.E.symm F : A.Mu0) : C.cls 0 → C.Y 0 → ℂ) ∈ A.Mram
      rw [mem_ramified_iff_model A M]; simpa using hF
  rw [← hmap, LinearEquiv.finrank_map_eq]

open Classical in

theorem ramified_rank_mul (M : FreeRankModel A) :
    haveI := A.Mu0_fd
    A.du * (A.T - 1) ^ R.f = Module.finrank ℂ A.Mu0 * (A.T - 2) ^ R.f := by
  have := A.Mu0_fd
  have h := Formalism.LogVandermondeBounds.product_first_zeroth_parts.finrankFiberSumZero A.vT M.H M.X ℂ M.free
  rw [← ramified_rank_eq_finrank A M, A.card_vT] at h
  have hX : Module.finrank ℂ A.Mu0 = Fintype.card M.X := by
    rw [M.E.finrank_eq, Module.finrank_fintype_fun_eq_card]
  rw [hX]
  rcases Nat.eq_zero_or_pos R.f with hf | hf
  · simpa [hf] using h
  · have hne : Nonempty A.vT := by
      rw [← Fintype.card_pos_iff, A.card_vT]; exact hf
    obtain ⟨v⟩ := hne
    have hH : Fintype.card M.H = A.T - 1 := by
      rw [← Fintype.card_congr (M.e v).toEquiv, Fintype.card_units, A.card_Fv v]
    rw [hH] at h
    have h2 : A.T - 1 - 1 = A.T - 2 := by omega
    rw [h2] at h
    exact h


end Model


end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions



end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions NumberField Matrix

theorem exists_integer_smul_mem_of_span_top {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) (hL : Submodule.span K (L : Set V) = ⊤) (x : V) :
    ∃ r : 𝓞 K, r ≠ 0 ∧ r • x ∈ L :=
  _root_.UpperTheory.Reformulated.B.ClearDenominatorsLattice.exists_integer_smul_mem_of_span_top L hL x

variable (D : D7) (u : D.what₂.Word)






end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end

section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Classical NumberField

section Parts

variable (D : D7) (u : D.what₂.Word)

def RamifiedSlopeFormula : Prop :=
  (D.fm u).ramLat.mu = ((D.fm u).lat 0).mu -
    (D.R.f : ℝ) * Real.log (((D.mem u).A.T : ℝ) - 1) / (((D.mem u).A.T : ℝ) - 2)

def LatticeInclusionLength : Prop :=
  (∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    (0 ≤ ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift →
      (D.fm u).S 0 w ≤ (D.fm u).Bw 0 w v ∧
      (∃ n : ℕ, len D u w ((D.fm u).Bw 0 w v) ((D.fm u).S 0 w) = n ∧
        (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) *
          ((D.duS u : ℚ) * (wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) / (D.R.k : ℚ))) ∧
      len D u w (Sram D u w) (imgL D u w (Uop D u 0 v) (Sram D u w)) ≤
        len D u w ((D.fm u).Bw 0 w v) ((D.fm u).S 0 w) +
          ((D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) : ℕ) : ℕ∞) +
          len D u w (imgL D u w (Uop D u 0 v) (Sram D u w)) (Sram D u w)) ∧
    (0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v) →
      tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w) ≤ (D.fm u).Bw 0 w v ∧
      (∃ n : ℕ, len D u w ((D.fm u).Bw 0 w v) (tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w)) = n ∧
        (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((D.duS u : ℚ) *
          ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) /
            (D.R.k : ℚ))) ∧
      len D u w (Sram D u w)
          (imgL D u w ((((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v)) • Uop D u 0 v) (Sram D u w)) ≤
        len D u w ((D.fm u).Bw 0 w v) (tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w)) +
          ((D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) : ℕ) : ℕ∞) +
          len D u w (imgL D u w ((((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v)) • Uop D u 0 v) (Sram D u w))
            (Sram D u w)))

end Parts



end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
end
