import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement
import Formalism.LogVandermondeBounds.LogVandermondeProofs.MulSingleMulApplySelf

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
