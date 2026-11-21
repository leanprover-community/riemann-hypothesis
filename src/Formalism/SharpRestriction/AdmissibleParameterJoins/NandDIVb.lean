import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataDIV
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces

section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

theorem injective_of_scalars {ι V W : Type*} [DecidableEq ι] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (S : ι → Submodule ℂ V) (hS : DirectSum.IsInternal S)
    (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V)
    (h : ∀ σ, S σ ≠ ⊥ → ∃ lam : ℂ, lam ≠ 0 ∧ ∀ f ∈ S σ, B (A f) = lam • f) :
    Function.Injective A := by
  classical
  have h' : ∀ σ, ∃ lam : ℂ, lam ≠ 0 ∧ ∀ f ∈ S σ, B (A f) = lam • f := by
    intro σ
    by_cases hσ : S σ = ⊥
    · refine ⟨1, one_ne_zero, fun f hf => ?_⟩
      rw [hσ, Submodule.mem_bot] at hf
      simp [hf]
    · exact h σ hσ
  choose c hc0 hc using h'
  let _ := hS.chooseDecomposition
  have key : ∀ v : V, ∀ k, ((DirectSum.decompose S (B (A v)) k : S k) : V) =
      c k • ((DirectSum.decompose S v k : S k) : V) := by
    intro v
    induction v using DirectSum.Decomposition.inductionOn S with
    | zero => intro k; simp
    | @homogeneous i m =>
      intro k
      have hm : B (A (m : V)) ∈ S i := by
        rw [hc i _ m.2]; exact (S i).smul_mem _ m.2
      by_cases hik : i = k
      · subst hik
        rw [DirectSum.decompose_of_mem_same S hm, DirectSum.decompose_of_mem_same S m.2, hc i _ m.2]
      · rw [DirectSum.decompose_of_mem_ne S hm hik, DirectSum.decompose_of_mem_ne S m.2 hik, smul_zero]
    | add a b ha hb =>
      intro k
      simp only [map_add, DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, smul_add, ha k, hb k]
  rw [injective_iff_map_eq_zero]
  intro v hv
  have hz : DirectSum.decompose S v = 0 := by
    ext k
    have := key v k
    rw [hv, map_zero, DirectSum.decompose_zero] at this
    simp only [DirectSum.zero_apply, ZeroMemClass.coe_zero] at this ⊢
    exact (smul_eq_zero.mp this.symm).resolve_left (hc0 k)
  exact (DirectSum.decompose S).injective (by rw [hz, DirectSum.decompose_zero])



theorem finrank_Mj {D : D7} (X : DivX D) (j : ℕ) (hr : (X.MjH j).rank = D.what₂.D0) :
    Module.finrank ℂ (D.what₂.Mj j) = D.what₂.D0 := by
  have hb := X.jM_basis j
  have h1 : Module.finrank ℂ (D.what₂.Mj j) = Fintype.card (X.MjH j).ι :=
    Module.finrank_eq_card_basis (Module.Basis.mk hb.1 (by rw [hb.2]))
  have h2 : (X.MjH j).rank = Fintype.card (X.MjH j).ι := by
    unfold HLat.rank Formalism.HN.rkK
    rw [(X.MjH_good j).2.2, finrank_top]
    exact Module.finrank_eq_card_basis (X.MjH j).b
  rw [h1, ← h2, hr]



end Formalism.MainNotions.J

end
end

section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

def RankMj (D : D7) : Prop := ∀ j ∈ SizeData₂.lifts D, Module.finrank ℂ (D.what₂.Mj j) = D.what₂.D0

def ThetaOnto (D : D7) (μ : D.what₂.Tup) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, Function.Surjective (D.what₂.thetaP μ j)

def LocEachLift (D : D7) : Prop := ∀ j ∈ SizeData₂.lifts D, ∃ i : D.nd.Loc, D.nd.j i = j





theorem theta_injective_of_scalars (D : D7) (h42 : Formalism.MainNotions.SumRepresentations.Conclusion42 D) (hI : Rows.IsotInternal D.what₂)
    (i : D.nd.Loc) (hj : D.nd.j i ∈ SizeData₂.lifts D) :
    Function.Injective (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) := by
  have hj' := Finset.mem_Icc.mp hj
  exact injective_of_scalars (D.what₂.isot (D.nd.j i)) (hI _ hj'.1 hj'.2) _ (D.what₂.thetaP (D.nd.mu i) (D.nd.j i))
    (fun σ hσ => let ⟨lam, h0, hl⟩ := (h42 i σ hσ).1.1; ⟨(lam : ℂ), by exact_mod_cast h0.ne', hl⟩)





end Formalism.MainNotions.J

end
end
