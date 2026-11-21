import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.WeightsConj
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilRepEquivOfCharpolyEq

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne

namespace UpperTheory.GalN

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem scalar_of_charpoly {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] {f : End ℂ V}
    (hf : f.IsSemisimple) {c : ℂ} {t : ℕ} (e : f.charpoly = (X - C c) ^ t) (v : V) : f v = c • v := by
  have h1 : IsNilpotent (f - algebraMap ℂ (End ℂ V) c) := ⟨t, by
    have := LinearMap.aeval_self_charpoly f
    rw [e] at this
    simpa using this⟩
  have h2 : (f - algebraMap ℂ (End ℂ V) c).IsSemisimple := End.isSemisimple_sub_algebraMap_iff.2 hf
  have h3 := sub_eq_zero.1 (End.eq_zero_of_isNilpotent_isSemisimple h1 h2)
  rw [h3]; rfl

theorem exists_sum {W Va Vb : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    [AddCommGroup Va] [Module ℂ Va] [FiniteDimensional ℂ Va] [AddCommGroup Vb] [Module ℂ Vb] [FiniteDimensional ℂ Vb]
    (x : WDRep h W) (a : WDRep h Va) (b : WDRep h Vb) (g : W ≃ₗ[ℂ] Va × Vb)
    (hg : ∀ σ v, g (x.ρ σ v) = (a.sum b).ρ σ (g v)) (hb : b.N = 0) (γ : Weil h) (hγ : deg γ = 0) (c : ℂ)
    (hbγ : ∀ v, b.ρ γ v = c • v) (haγ : ∀ v, a.ρ γ v = c • v → v = 0) (h0 : ∀ v, x.N (g.symm (0, v)) = 0) :
    ∃ a' : WDRep h Va, WD.mk x = WD.mk (a'.sum b) := by
  let M : End ℂ (Va × Vb) := g.conj x.N
  have hM : ∀ v, M (g v) = g (x.N v) := fun v => by simp [M, LinearEquiv.conj_apply]
  have hc : ∀ σ z, (a.sum b).ρ σ (M z) = ((normV w : ℕ) : ℂ) ^ deg σ • M ((a.sum b).ρ σ z) := fun σ z => by
    obtain ⟨v, rfl⟩ := g.surjective z
    have := LinearMap.congr_fun (x.comm σ) v
    simp only [End.mul_apply, LinearMap.smul_apply] at this
    rw [hM, ← hg, ← hg, hM, this, map_smul]
  have hs : Function.Surjective (a.ρ γ - c • (1 : End ℂ Va)) := by
    rw [← LinearMap.injective_iff_surjective, injective_iff_map_eq_zero]
    intro v hv
    exact haγ v (by simpa [sub_eq_zero] using hv)
  have h1 : ∀ v, M (0, v) = 0 := fun v => by
    rw [← g.apply_symm_apply (0, v), hM, h0, map_zero]
  have h2 : ∀ v, (M (v, 0)).2 = 0 := fun v => by
    obtain ⟨u, rfl⟩ := hs v
    have e : (((a.ρ γ - c • (1 : End ℂ Va)) u, 0) : Va × Vb) = (a.sum b).ρ γ (u, 0) - c • (u, 0) := by simp
    have k := hc γ (u, 0)
    rw [hγ, zpow_zero, one_smul] at k
    rw [e, map_sub, map_smul, ← k]
    simp [hbγ]
  let Na : End ℂ Va := LinearMap.fst ℂ Va Vb ∘ₗ M ∘ₗ LinearMap.inl ℂ Va Vb
  have h3 : ∀ v, M (v, 0) = (Na v, 0) := fun v => Prod.ext rfl (h2 v)
  have h4 : ∀ (k : ℕ) v, (M ^ k) (v, 0) = ((Na ^ k) v, 0) := fun k => by
    induction k with
    | zero => intro v; simp
    | succ k ih => intro v; rw [pow_succ', pow_succ', End.mul_apply, End.mul_apply, ih, h3]
  have h5 : ∀ (k : ℕ) v, (M ^ k) (g v) = g ((x.N ^ k) v) := fun k => by
    induction k with
    | zero => intro v; simp
    | succ k ih => intro v; rw [pow_succ', pow_succ', End.mul_apply, End.mul_apply, ih, hM]
  refine ⟨{ ρ := a.ρ, N := Na, smooth := a.smooth, semisimple := a.semisimple, nilpotent := ?_, comm := fun σ => ?_ },
    WD.sound ⟨g, hg, fun v => ?_⟩⟩
  · obtain ⟨k, hk⟩ := x.nilpotent
    refine ⟨k, LinearMap.ext fun v => ?_⟩
    have := h4 k v
    rw [← g.apply_symm_apply (v, 0), h5, hk] at this
    simpa using (congrArg Prod.fst this).symm
  · refine LinearMap.ext fun v => ?_
    have k := hc σ (v, 0)
    have e : (a.sum b).ρ σ (v, 0) = (a.ρ σ v, 0) := by simp
    rw [e, h3, h3] at k
    simpa using congrArg Prod.fst k
  · rw [← hM]
    obtain ⟨p, q⟩ := g v
    have e : ((p, q) : Va × Vb) = (p, 0) + (0, q) := by simp
    conv_lhs => rw [e, map_add, h1, h3, add_zero]
    simp [hb]


end UpperTheory.GalN
