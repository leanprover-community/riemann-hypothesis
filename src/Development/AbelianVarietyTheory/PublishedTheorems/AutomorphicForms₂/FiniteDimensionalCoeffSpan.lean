import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace GlobalTheory.Published.AutFin.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finiteDimensional_coeffSpan {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (coeffSpan ρ) := by
  let T : Module.Dual ℂ (Module.End ℂ W) →ₗ[ℂ] (K → ℂ) :=
    LinearMap.pi fun k => LinearMap.applyₗ (ρ k)
  have : coeffSpan ρ ≤ LinearMap.range T := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨ℓ, w, rfl⟩
    exact ⟨ℓ.comp (LinearMap.applyₗ w), rfl⟩
  exact Submodule.finiteDimensional_of_le this

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem isAtTau_unique (hθ : IsInfFam θ) {τ : D.what₂.Tau} {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} {x y : GA D V}
    (hx : IsAtTau θ V τ g x) (hy : IsAtTau θ V τ g y) : x = y := by
  refine ((GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V).2.2.1 x hx.1 y hy.1 fun τ' => ?_
  by_cases c : τ' = τ
  · subst c; rw [hx.2.1, hy.2.1]
  · rw [hx.2.2 _ c, hy.2.2 _ c]

theorem kAt_mul (hθ : IsInfFam θ) (τ : D.what₂.Tau) {e : Fin V.rank → Bool}
    {P : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm e * P = gramAt D V τ)
    (k l : Formalism.REAL.KG e) : kAt θ V τ e P (k * l) = kAt θ V τ e P k * kAt θ V τ e P l := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hk := isAtTau_kAt θ V hθ τ hP h k
  have hl := isAtTau_kAt θ V hθ τ hP h l
  have hm := ((GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V).2.2.2.1
  refine isAtTau_unique θ V hθ (isAtTau_kAt θ V hθ τ hP h (k * l)) ⟨mul_mem hk.1 hl.1, ?_, fun τ' c => ?_⟩
  · rw [hm, hk.2.1, hl.2.1]
    have : Formalism.REAL.toMK (k * l) = Formalism.REAL.toMK k * Formalism.REAL.toMK l := rfl
    rw [this]
    calc P⁻¹ * Formalism.REAL.toMK k * P * (P⁻¹ * Formalism.REAL.toMK l * P)
        = P⁻¹ * Formalism.REAL.toMK k * (P * P⁻¹) * Formalism.REAL.toMK l * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [mul_nonsing_inv _ hd]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  · rw [hm, hk.2.2 _ c, hl.2.2 _ c, Matrix.mul_one]



theorem hypotheses_met (D : D7) : ∃ (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (_ : IsInfFam θ)
    (ε : D.what₂.Tau → Fin (D.sp.Y 0).rank → Bool)
    (fr : D.what₂.Tau → Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ),
    IsFrameFam (D.sp.Y 0) ε fr ∧ IsOpen ((⊤ : Subgroup (GA D (D.sp.Y 0))) : Set (GA D (D.sp.Y 0))) ∧
    (∀ τ, IsContRep (Representation.trivial ℂ (Formalism.REAL.KG (ε τ)) ℂ)) ∧
    Submodule.span ℂ (forms θ (D.sp.Y 0) ⊤ ε fr (fun τ => Representation.trivial ℂ (Formalism.REAL.KG (ε τ)) ℂ)
      (fun _ _ => 0)) ≠ ⊥ := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  obtain ⟨ε, fr, h⟩ := exists_isFrameFam (D := D) (D.sp.Y 0) (D.sp.Y_sig 0)
  refine ⟨θ, hθ, ε, fr, h, isOpen_univ, fun _ => isContRep_trivial, fun hb => ?_⟩
  have := Submodule.subset_span (R := ℂ) (const_mem_forms θ (D.sp.Y 0) ⊤ ε fr 1)
  rw [hb] at this
  exact one_ne_zero (congrFun ((Submodule.mem_bot ℂ).1 this) 1)


end GlobalTheory.Published.AutFin.Model

end
