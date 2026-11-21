import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PProjOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PCertProj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PTracePow
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SimultaneousEigenvectors.SimEig
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExtEig
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExtHecke
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PFormGU
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.ZetaMain
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExtEig2Of
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLocAdj
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InfPowConjDiagUnits
import GroundTheory.GlobalFields.TateThesis.IdeleMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesFiniteClassDecomposition
import Formalism.LocalToGlobal.Columns.InvariantSubspaceNonzeroXOfRegular
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PIntConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PIntSim
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.POfUBij
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLocComm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLocMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenKGLInvEntries
import GroundTheory.GlobalFields.Adele.Compact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocEqOneOfMemGam
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.ExistsOpenAvoid
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PNbhdU
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PStepAt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LevEraseLe
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PSatVal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PKerFormU
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PKapOf

section
open Module
universe u v
end

section
open Module
universe u v

namespace UpperTheory.Gal.CertificateRingHomMap

open GlobalTheory.LKDef.HeckeTraceForms

section
variable {Γ H A V : Type} [Group Γ] [Group H] [Group A] [AddCommGroup V] [Module ℂ V]
  {ι : Γ →* H} {K : Subgroup H} {ξ : Representation ℂ Γ V} {c : H →* A} {φ : H → V}

private theorem key (hφ : KerForm ι K ξ c φ) {γ γ' : Γ} {u u' k k' : H} (hu : c u = 1) (hu' : c u' = 1)
    (hk : k ∈ K) (hk' : k' ∈ K) (h : ι γ * u * k = ι γ' * u' * k') : ξ γ (φ u) = ξ γ' (φ u') := by
  obtain ⟨h1, h2, h3⟩ := hφ
  set δ := γ'⁻¹ * γ with hδ
  have hκ : k * k'⁻¹ ∈ K := K.mul_mem hk (K.inv_mem hk')
  have hu'eq : u' = ι δ * u * (k * k'⁻¹) := by
    have e1 : ι γ' * u' = ι γ * u * k * k'⁻¹ := by
      rw [h]
      group
    rw [hδ, map_mul, map_inv]
    calc u' = (ι γ')⁻¹ * (ι γ' * u') := by group
      _ = (ι γ')⁻¹ * ι γ * u * (k * k'⁻¹) := by
        rw [e1]
        group
  have hc : c (ι δ) * c (k * k'⁻¹) = 1 := by
    have e2 := congrArg c hu'eq
    rw [map_mul, map_mul, hu, hu', mul_one] at e2
    exact e2.symm
  have hcκ : c (k * k'⁻¹) = 1 := by
    apply h1 δ⁻¹ _ hκ
    rw [map_inv, map_inv, eq_inv_of_mul_eq_one_right hc]
  have hcδ : c (ι δ) = 1 := by
    rw [hcκ, mul_one] at hc
    exact hc
  rw [hu'eq, h3 _ hκ _ hcκ (by rw [map_mul, hcδ, hu, one_mul]), h2 δ u hcδ hu]
  rw [← Module.End.mul_apply, ← map_mul, hδ, mul_inv_cancel_left]

open Classical in
private noncomputable def ext0 (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) (c : H →* A) (φ : H → V) (g : H) : V :=
  if h : ∃ x : Γ × H × H, c x.2.1 = 1 ∧ x.2.2 ∈ K ∧ g = ι x.1 * x.2.1 * x.2.2 then
    ξ h.choose.1 (φ h.choose.2.1) else 0

private theorem extension_by_zero_double_coset (hφ : KerForm ι K ξ c φ) {γ : Γ} {u k : H} (hu : c u = 1) (hk : k ∈ K) :
    ext0 ι K ξ c φ (ι γ * u * k) = ξ γ (φ u) := by
  have h : ∃ x : Γ × H × H, c x.2.1 = 1 ∧ x.2.2 ∈ K ∧ ι γ * u * k = ι x.1 * x.2.1 * x.2.2 :=
    ⟨(γ, u, k), hu, hk, rfl⟩
  unfold ext0
  rw [dif_pos h]
  obtain ⟨s1, s2, s3⟩ := h.choose_spec
  exact key hφ s1 hu s2 hk s3.symm

private theorem extension_by_zero_outside_support {g : H} (h : ¬ ∃ γ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ * u * k) :
    ext0 ι K ξ c φ g = 0 := by
  unfold ext0
  rw [dif_neg]
  rintro ⟨x, hx1, hx2, hx3⟩
  exact h ⟨x.1, x.2.1, x.2.2, hx1, hx2, hx3⟩

end

theorem pExtZero_holds : ExtZero := by
  intro Γ H A V _ _ _ _ _ ι K ξ c φ hφ
  refine ⟨ext0 ι K ξ c φ, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro γ g
    by_cases hg : ∃ γ₀ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ₀ * u * k
    · obtain ⟨γ₀, u, k, hu, hk, rfl⟩ := hg
      have e : ι γ * (ι γ₀ * u * k) = ι (γ * γ₀) * u * k := by rw [map_mul]; group
      rw [e, extension_by_zero_double_coset hφ hu hk, extension_by_zero_double_coset hφ hu hk, map_mul]; rfl
    · have hg' : ¬ ∃ γ₀ u k, c u = 1 ∧ k ∈ K ∧ ι γ * g = ι γ₀ * u * k := by
        rintro ⟨γ₀, u, k, hu, hk, e⟩
        refine hg ⟨γ⁻¹ * γ₀, u, k, hu, hk, ?_⟩
        rw [map_mul, map_inv]
        calc g = (ι γ)⁻¹ * (ι γ * g) := by group
          _ = (ι γ)⁻¹ * ι γ₀ * u * k := by rw [e]; group
      rw [extension_by_zero_outside_support hg, extension_by_zero_outside_support hg', map_zero]
  · intro k₁ hk₁ g
    by_cases hg : ∃ γ₀ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ₀ * u * k
    · obtain ⟨γ₀, u, k, hu, hk, rfl⟩ := hg
      have e : ι γ₀ * u * k * k₁ = ι γ₀ * u * (k * k₁) := by group
      rw [e, extension_by_zero_double_coset hφ hu (K.mul_mem hk hk₁), extension_by_zero_double_coset hφ hu hk]
    · have hg' : ¬ ∃ γ₀ u k, c u = 1 ∧ k ∈ K ∧ g * k₁ = ι γ₀ * u * k := by
        rintro ⟨γ₀, u, k, hu, hk, e⟩
        refine hg ⟨γ₀, u, k * k₁⁻¹, hu, K.mul_mem hk (K.inv_mem hk₁), ?_⟩
        calc g = g * k₁ * k₁⁻¹ := by group
          _ = ι γ₀ * u * (k * k₁⁻¹) := by rw [e]; group
      rw [extension_by_zero_outside_support hg, extension_by_zero_outside_support hg']
  · intro u hu
    have := extension_by_zero_double_coset (γ := 1) hφ hu K.one_mem
    simpa using this
  · intro g hg
    by_contra h
    exact hg (extension_by_zero_outside_support h)

end UpperTheory.Gal.CertificateRingHomMap
end

section
open Module
universe u v
end

section
open Module

private theorem exists_common_eigenvector_of_commute_of_invariant {E ι : Type} [AddCommGroup E] [Module ℂ E]
    (T : ι → E →ₗ[ℂ] E) (hT : ∀ i j, T i ∘ₗ T j = T j ∘ₗ T i) :
    ∀ n : ℕ, ∀ W : Submodule ℂ E, finrank ℂ W = n → FiniteDimensional ℂ W → W ≠ ⊥ →
      (∀ i, ∀ x ∈ W, T i x ∈ W) → ∃ x ∈ W, x ≠ 0 ∧ ∀ i, ∃ c : ℂ, T i x = c • x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hn hfin hne hW
  by_cases hs : ∀ i, ∃ c : ℂ, ∀ x ∈ W, T i x = c • x
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨x, hx, hx0, fun i => (hs i).imp fun c hc => hc x hx⟩
  · push_neg at hs
    obtain ⟨i, hi⟩ := hs
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hne
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ((T i).restrict (fun x hx => hW i x hx))
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    set W' : Submodule ℂ E := W ⊓ LinearMap.ker (T i - μ • LinearMap.id) with hW'
    have hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ T i x = μ • x := by
      intro x
      simp [hW', sub_eq_zero]
    have hle : W' ≤ W := inf_le_left
    have hlt : W' < W := by
      refine lt_of_le_of_ne hle ?_
      intro heq
      obtain ⟨x, hx, hne'⟩ := hi μ
      exact hne' ((hmem x).1 (by rw [heq]; exact hx)).2
    haveI : FiniteDimensional ℂ W' := Submodule.finiteDimensional_of_le hle
    have hlt' : finrank ℂ W' < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hlt
    have hne' : W' ≠ ⊥ := by
      intro hbot
      have hv0 : (v : E) ∈ W' := (hmem _).2 ⟨v.2, by
        have := hv.apply_eq_smul
        simpa using congrArg Subtype.val this⟩
      rw [hbot, Submodule.mem_bot] at hv0
      exact hv.2 (Subtype.ext hv0)
    have hW'inv : ∀ j, ∀ x ∈ W', T j x ∈ W' := by
      intro j x hx
      rw [hmem] at hx ⊢
      refine ⟨hW j x hx.1, ?_⟩
      have h1 := LinearMap.congr_fun (hT i j) x
      simp only [LinearMap.comp_apply] at h1
      rw [h1, hx.2, map_smul]
    obtain ⟨x, hx, hx0, hc⟩ := ih _ hlt' W' rfl inferInstance hne' hW'inv
    exact ⟨x, hle hx, hx0, hc⟩

theorem UpperTheory.Gal.CertificateRingHomMap.pCentralEig2_of :
    UpperTheory.Gal.CertificateRingHomMap.CentralEig2 := by
  intro Γ H Z V _ _ _ _ _ ι K ξ ζ hζ M hfin hM hne hinv
  let T : Z → (H → V) →ₗ[ℂ] (H → V) := fun z =>
    { toFun := fun Φ g => Φ (g * ζ z), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hT : ∀ a b, T a ∘ₗ T b = T b ∘ₗ T a := by
    intro a b
    refine LinearMap.ext fun Φ => funext fun g => ?_
    show Φ (g * ζ a * ζ b) = Φ (g * ζ b * ζ a)
    rw [mul_assoc, mul_assoc, hζ a (ζ b)]
  obtain ⟨Φ, hΦM, hΦ0, hc⟩ :=
    exists_common_eigenvector_of_commute_of_invariant T hT _ M rfl hfin hne (fun z Φ hΦ => hinv Φ hΦ z)
  choose c hc using hc
  have hcg : ∀ z g, Φ (g * ζ z) = c z • Φ g := fun z g => congrFun (hc z) g
  obtain ⟨g0, hg0⟩ := Function.ne_iff.mp hΦ0
  have hscal : ∀ a b : ℂ, a • Φ g0 = b • Φ g0 → a = b := fun a b h =>
    smul_left_injective ℂ hg0 h
  have hF : (∀ (γ : Γ) (g : H), Φ (ι γ * g) = ξ γ (Φ g)) ∧ ∀ k ∈ K, ∀ g : H, Φ (g * k) = Φ g :=
    hM hΦM
  have h1 : c 1 = 1 := by
    apply hscal
    rw [← hcg 1 g0, map_one, mul_one, one_smul]
  have hmul : ∀ a b, c (a * b) = c a * c b := by
    intro a b
    apply hscal
    rw [← hcg (a * b) g0, map_mul, ← mul_assoc, hcg b, hcg a, smul_smul, mul_comm]
  let χ : Z →* ℂ := { toFun := c, map_one' := h1, map_mul' := hmul }
  refine ⟨Φ, hΦM, hΦ0, χ.toHomUnits, ?_, ?_, ?_⟩
  · intro z g
    exact hcg z g
  · intro z hz
    apply Units.ext
    show c z = 1
    apply hscal
    rw [← hcg z g0, hF.2 _ hz g0, one_smul]
  · intro z γ a hzγ hξ
    show c z = a
    apply hscal
    rw [← hcg z g0, ← hξ (Φ g0), ← hF.1 γ g0, ← hzγ, hζ z g0]
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem cpow_key (q n j : ℕ) (hq : 0 < q) :
    (q : ℂ) ^ (j.choose 2) * (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - (j : ℂ))) / 2) =
      (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ^ j := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hρ : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = (q : ℂ) ^ (((n : ℂ) - 1) / 2) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg q)]
    push_cast
    rfl
  rw [hρ, ← Complex.cpow_nat_mul, ← Complex.cpow_natCast (q : ℂ) (j.choose 2), ← Complex.cpow_add _ _ hq0,
    Nat.cast_choose_two]
  congr 1
  ring

theorem UpperTheory.Gal.CertificateRingHomMap.pRootsAlg_of :
    UpperTheory.Gal.CertificateRingHomMap.RootsAlg := by
  intro q n hq B hB a c ϑ h
  refine ⟨?_, ?_⟩
  · have h0 := h 0 (Nat.zero_le n)
    simpa [GlobalTheory.LFun.satEig, Multiset.esymm] using h0
  · set ρ : ℂ := (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) with hρ
    set s : Multiset ℂ := B.map (fun b : ℂˣ => (b : ℂ)) with hs
    have hcard : Multiset.card s = n := by simp [hs, hB]
    have e1 : (UpperTheory.V.Af.algSat n q B).map (· * c) = s.map (fun x => (ρ * c) • x) := by
      have e0 : UpperTheory.V.Af.algSat n q B = s.map (fun α => ρ * α) := by
        show Multiset.map _ (B.bind fun b => ({(b : ℂ)} : Multiset ℂ)) = _
        rw [Multiset.bind_singleton]
      rw [e0, Multiset.map_map]
      refine Multiset.map_congr rfl fun x _ => ?_
      simp only [Function.comp_apply, smul_eq_mul]
      ring
    have e2 : Multiset.card (s.map (fun x => (ρ * c) • x)) = n := by simp [hcard]
    rw [e1, UpperTheory.Gal.crystallineComparison.rootPol, Multiset.prod_X_sub_X_eq_sum_esymm, e2, Finset.mul_sum, UpperTheory.Gal.crystallineComparison.heckePol]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hk : _ = ρ ^ j := cpow_key q n j hq
    rw [h j hjn, ← Multiset.pow_smul_esymm, smul_eq_mul]
    have e3 : (-1 : ℂ) ^ j * (q : ℂ) ^ (j.choose 2) * (a * GlobalTheory.LFun.satEig q n B j * c ^ j) =
        a * ((-1) ^ j * ((ρ * c) ^ j * s.esymm j)) := by
      have e4 : GlobalTheory.LFun.satEig q n B j = (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - (j : ℂ))) / 2) * s.esymm j := rfl
      rw [e4, mul_pow]
      linear_combination ((-1) ^ j * a * s.esymm j * c ^ j) * hk
    rw [e3]
    simp only [map_mul, map_pow, map_neg, map_one]
    ring
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pFinToHecke_of :
    UpperTheory.Gal.CertificateRingHomMap.FinToHecke := by
  intro E _ _ ψ m ho hk
  obtain ⟨f, hf, hfe⟩ := exists_infPow_hom E m
  let p : Neutral.B1.Ideles E →* (Af E)ˣ :=
    Units.map (MonoidHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E) : _ →* _)
  have hpc : Continuous p := Continuous.units_map _ continuous_snd
  have hψ : Continuous ψ := continuous_of_isOpen_ker' ψ ho
  have hd : ∀ k : Eˣ, p (Neutral.B1.diagUnits E k) = diagF E k := fun k => Units.ext rfl
  have hl : ∀ (w : Plc E) y, p (Neutral.B1.localIdele E w y) = sgl w y := fun w y => Units.ext rfl
  have hi : ∀ k : Eˣ, p (infDiag k) = 1 := fun k => by
    rw [infDiag_eq]
    exact Units.ext rfl
  let θ : Neutral.B1.Ideles E →* ℂˣ := ψ.comp p * f
  have hθ : ∀ x, ((θ x : ℂˣ) : ℂ) = ((ψ (p x) : ℂˣ) : ℂ) * infPow m x := fun x => by
    rw [← hfe]
    rfl
  refine ⟨⟨θ, (hψ.comp hpc).mul hf, fun k => Units.ext ?_⟩, fun k _ => ?_, fun w y => ?_⟩
  · rw [hθ, hd, hk, infPow_diagUnits, Units.val_one]
    exact inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr fun φ _ => zpow_ne_zero _ (by simp))
  · show ((θ (infDiag k) : ℂˣ) : ℂ) = _
    rw [hθ, hi, infPow_infDiag, infPow_diagUnits, map_one, Units.val_one, one_mul]
  · show θ (Neutral.B1.localIdele E w y) = _
    refine Units.ext ?_
    rw [hθ, hl, infPow_localIdele, mul_one]
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal
open scoped Pointwise

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem exists_cover_units (E : Type) [Field E] [NumberField E] (O : Subgroup (Af E)ˣ)
    (hO : IsOpen (O : Set (Af E)ˣ)) :
    ∃ F : Finset (Af E)ˣ, ∀ u ∈ GroundTheory.Global.finiteIntegralUnits E, ∃ f ∈ F, ∃ o ∈ O, u = f * o := by
  obtain ⟨t, ht⟩ := (GroundTheory.Global.isCompact_finiteIntegralUnits E).elim_finite_subcover
    (fun a : (Af E)ˣ => a • (O : Set (Af E)ˣ)) (fun a => hO.smul a)
    (fun c _ => Set.mem_iUnion.2 ⟨c, Set.mem_smul_set.2 ⟨1, one_mem O, mul_one c⟩⟩)
  refine ⟨t, fun u hu => ?_⟩
  obtain ⟨f, hf, huf⟩ := Set.mem_iUnion₂.1 (ht hu)
  obtain ⟨o, ho, rfl⟩ := Set.mem_smul_set.1 huf
  exact ⟨f, hf, o, ho, rfl⟩

private theorem mem_units_of_valued (E : Type) [Field E] [NumberField E] (u : (Af E)ˣ)
    (hu : ∀ P : HeightOneSpectrum (𝓞 E), Valued.v ((u : Af E) P) = 1) :
    u ∈ GroundTheory.Global.finiteIntegralUnits E := by
  refine (GroundTheory.Global.mem_finiteIntegralUnits E).2 fun P => ⟨(hu P).le, ?_⟩
  have e : (((u⁻¹ : (Af E)ˣ) : Af E) P) * ((u : Af E) P) = 1 :=
    congrArg (fun t : Af E => t P) (Units.inv_mul u)
  have e2 := congrArg Valued.v e
  rw [map_mul, hu P, mul_one, map_one] at e2
  exact e2.le

theorem pClassFin_of : ClassFin := by
  intro E _ _ O hO
  classical
  obtain ⟨F, hF⟩ := exists_cover_units E O hO
  let ψ : (Af E)ˣ →* ClassGroup (𝓞 E) :=
    (ReciprocityTheory.Neutral.Bridge.HCFR.classOf E).comp GlobalTheory.ClassCover.toIdeles
  let sel : ClassGroup (𝓞 E) → (Af E)ˣ := fun c => if h : ∃ y, ψ y = c then h.choose else 1
  have hsel : ∀ y, ψ (sel (ψ y)) = ψ y := by
    intro y
    have h : ∃ z, ψ z = ψ y := ⟨y, rfl⟩
    simp only [sel, dif_pos h]
    exact h.choose_spec
  refine ⟨(Finset.univ.image sel ×ˢ F).image (fun p => p.1 * p.2), fun y => ?_⟩
  have hk : ψ ((sel (ψ y))⁻¹ * y) = 1 := by rw [map_mul, map_inv, hsel, inv_mul_cancel]
  obtain ⟨k, u, hu, he⟩ := GlobalTheory.ClassCover.eq_diag_mul_of_classOf _ hk
  obtain ⟨f, hf, o, ho, rfl⟩ := hF u (mem_units_of_valued E u hu)
  refine ⟨sel (ψ y) * f, Finset.mem_image.2 ⟨(sel (ψ y), f), Finset.mem_product.2
    ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hf⟩, rfl⟩, o, ho, k, ?_⟩
  have hy : y = sel (ψ y) * (diagF E k * (f * o)) := by
    rw [show diagF E k * (f * o) = (sel (ψ y))⁻¹ * y from he.symm, mul_inv_cancel_left]
  calc y = sel (ψ y) * (diagF E k * (f * o)) := hy
    _ = sel (ψ y) * f * o * diagF E k := by
      rw [mul_comm (diagF E k), ← mul_assoc, ← mul_assoc]

end UpperTheory.Gal.CertificateRingHomMap
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pXiScalar_of :
    UpperTheory.Gal.CertificateRingHomMap.XiScalar := by
  intro E _ _ _ n W j y s t hy v
  have hy' : y = Formalism.L2.Col.brpSc E t := Units.ext (by rw [hy, Formalism.L2.Col.brpSc_coe])
  have hinv : y⁻¹ = Formalism.L2.Col.brpSc E t⁻¹ := by
    rw [hy']
    exact (map_inv (Units.map (algebraMap E (Matrix (Fin n) (Fin n) E) : E →* Matrix (Fin n) (Fin n) E)) t).symm
  have hemb : embAll E n y⁻¹ = fun u => Formalism.L2.Col.brpSc ℂ (Units.map (u.embedding : E →* ℂ) t⁻¹) := by
    funext u
    ext i k
    rw [hinv]
    change ((((Formalism.L2.Col.brpSc E t⁻¹ : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E).map u.embedding) i k = _
    rw [Formalism.L2.Col.brpSc_coe, Formalism.L2.Col.brpSc_coe]
    by_cases h : i = k <;> simp [Matrix.one_apply, h]
  have hr := Formalism.L2.Col.tensorWeights_scalar_action (K := ℂ) W (fun u => Units.map (u.embedding : E →* ℂ) t⁻¹)
  rw [← hemb] at hr
  simp only [xi, MonoidHom.coe_mk, OneHom.coe_mk, Representation.dual_apply]
  rw [MonoidHom.comp_apply, hr]
  ext x
  simp [Module.Dual.transpose_apply, smul_smul]
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem zpow_sum_eq_prod_zpow {ι : Type*} {a : ℂ} (ha : a ≠ 0) (s : Finset ι) (e : ι → ℤ) :
    a ^ (∑ u ∈ s, e u) = ∏ u ∈ s, a ^ e u := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ ha, ih]

theorem UpperTheory.Gal.CertificateRingHomMap.pXiZeta_of :
    UpperTheory.Gal.CertificateRingHomMap.XiScalar → UpperTheory.Gal.CertificateRingHomMap.XiZeta := by
  intro hXi E _ _ _ n W j x ζ hζ k
  obtain ⟨γ, t, h1, h2, h3, h4⟩ := hζ.onRat k
  refine ⟨γ, h1, fun v => ?_⟩
  have hs : xi0 W j γ v = _ := hXi E n W j γ.1.1 γ.1.2 t h2 v
  rw [hs]
  congr 1
  rw [h4]
  have e : ∀ u : InfinitePlace E, u.embedding (t : E) ^ (-∑ i, (W u).w i) =
      ∏ φ : E →+* ℂ, (if φ x = -u.embedding x then φ (k : E) else 1) ^ (-∑ i, (W u).w i) := by
    intro u
    rw [h3 u.embedding, Finset.prod_filter, Finset.prod_zpow]
  rw [Finset.prod_congr rfl fun u _ => e u, Finset.prod_comm, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun φ _ => ?_
  have ha : φ (k : E) ≠ 0 := (map_ne_zero φ).2 k.ne_zero
  unfold mOf
  rw [zpow_sub₀ ha, div_eq_mul_inv, zpow_sum_eq_prod_zpow ha, ← Finset.prod_inv_distrib]
  congr 1
  refine Finset.prod_congr rfl fun u _ => ?_
  by_cases h : φ x = -u.embedding x
  · have h' : u.embedding x = -φ x := by rw [h, neg_neg]
    rw [if_pos h, if_pos h', _root_.zpow_neg]
  · have h' : ¬ u.embedding x = -φ x := fun h'' => h (by rw [h'', neg_neg])
    rw [if_neg h, if_neg h']
    simp
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem isOpen_intA (F : Type) [Field F] [NumberField F] :
    IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, Valued.v (a v) ≤ 1} :=
  RestrictedProduct.isOpen_forall_mem
    (A := fun v : HeightOneSpectrum (𝓞 F) => ((v.adicCompletionIntegers F : ValuationSubring _) : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)

private theorem continuous_sim {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} :
    Continuous (sim : GUf E n → AfQˣ) := continuous_snd.comp continuous_subtype_val

private theorem continuous_mat {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} :
    Continuous (mat : GUf E n → GL (Fin n) (Af E)) := continuous_fst.comp continuous_subtype_val

private theorem continuous_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Plc E) :
    Continuous (comp w : GUf E n → GL (Fin n) (w.adicCompletion E)) :=
  (Continuous.units_map _ (continuous_id.matrix_map (RestrictedProduct.continuous_eval w))).comp continuous_mat

theorem UpperTheory.Gal.CertificateRingHomMap.pLevOpen_of :
    UpperTheory.Gal.CertificateRingHomMap.LevOpen := by
  intro E _ _ _ n S Kw hK
  have hI : IsOpen {a : Af E | ∀ v, Valued.v (a v) ≤ 1} := isOpen_intA E
  have hJ : IsOpen {a : AfQ | ∀ v, Valued.v (a v) ≤ 1} := isOpen_intA ℚ
  let A : Set (GUf E n) :=
    ((((fun k => ((sim k : AfQˣ) : AfQ)) ⁻¹' {a : AfQ | ∀ v, Valued.v (a v) ≤ 1}) ∩
      ((fun k => (((sim k)⁻¹ : AfQˣ) : AfQ)) ⁻¹' {a : AfQ | ∀ v, Valued.v (a v) ≤ 1})) ∩
    ((⋂ i, ⋂ j, (fun k => (mat k).val i j) ⁻¹' {a : Af E | ∀ v, Valued.v (a v) ≤ 1}) ∩
      (⋂ i, ⋂ j, (fun k => ((mat k)⁻¹).val i j) ⁻¹' {a : Af E | ∀ v, Valued.v (a v) ≤ 1}))) ∩
    ⋂ w ∈ S, comp w ⁻¹' (Kw w : Set (GLw n w))
  have hAo : IsOpen A := by
    refine ((IsOpen.inter ?_ ?_).inter (IsOpen.inter ?_ ?_)).inter ?_
    · exact hJ.preimage (Units.continuous_val.comp continuous_sim)
    · exact hJ.preimage (Units.continuous_val.comp continuous_sim.inv)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        hI.preimage ((Units.continuous_val.comp continuous_mat).matrix_elem i j)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        hI.preimage ((Units.continuous_val.comp continuous_mat.inv).matrix_elem i j)
    · exact isOpen_biInter_finset fun w hw => (hK w hw).preimage (continuous_comp w)
  have hone : ∀ (i j : Fin n) (v : Plc E), Valued.v (((1 : Matrix (Fin n) (Fin n) (Af E)) i j) v) ≤ 1 := by
    intro i j v
    by_cases h : i = j
    · subst h
      rw [Matrix.one_apply_eq]
      change Valued.v (1 : v.adicCompletion E) ≤ 1
      rw [map_one]
    · rw [Matrix.one_apply_ne h]
      change Valued.v (0 : v.adicCompletion E) ≤ 1
      rw [map_zero]
      exact zero_le'
  have hQ : ∀ v : Plc ℚ, Valued.v ((1 : AfQ) v) ≤ 1 := fun v => by
    change Valued.v (1 : v.adicCompletion ℚ) ≤ 1
    rw [map_one]
  have h1 : (1 : GUf E n) ∈ A := by
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · simpa using hQ
    · simpa using hQ
    · simp only [Set.mem_iInter, Set.mem_preimage, map_one]
      exact fun i j => hone i j
    · simp only [Set.mem_iInter, Set.mem_preimage, map_one, inv_one]
      exact fun i j => hone i j
    · simp only [Set.mem_iInter, Set.mem_preimage, map_one]
      exact fun w _ => (Kw w).one_mem
  have hsub : A ⊆ (lev S Kw : Set (GUf E n)) := by
    rintro k ⟨⟨⟨hs, hs'⟩, hm, hm'⟩, hc⟩
    simp only [Set.mem_iInter, Set.mem_preimage] at hm hm' hc
    refine mem_lev.2 ⟨fun v => ?_, fun w hw => hc w hw, fun w _ _ => ?_⟩
    · have h : Valued.v (((sim k : AfQˣ) : AfQ) v * (((sim k)⁻¹ : AfQˣ) : AfQ) v) = 1 := by
        change Valued.v ((((sim k : AfQˣ) : AfQ) * (((sim k)⁻¹ : AfQˣ) : AfQ)) v) = 1
        rw [Units.mul_inv]
        exact map_one _
      rw [map_mul] at h
      refine le_antisymm (hs v) ?_
      calc (1 : _) = _ := h.symm
        _ ≤ Valued.v (((sim k : AfQˣ) : AfQ) v) * 1 := mul_le_mul' le_rfl (hs' v)
        _ = _ := mul_one _
    · rw [GlobalTheory.HenQ.Basic.mem_KGL_iff]
      refine ⟨fun i j => hm i j w, fun i j => ?_⟩
      have : (comp w k)⁻¹ = GeneralLinearGroup.map (pLoc E w) (mat k)⁻¹ := (map_inv _ _).symm
      rw [this]
      exact hm' i j w
  exact Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hAo.mem_nhds h1) hsub)
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem isCompact_ZU : IsCompact (ZU : Set AfQˣ) := by
  have hO := GroundTheory.Global.isCompact_integralFiniteAdeles ℚ
  have hB' : IsCompact (MulOpposite.unop ⁻¹' (GroundTheory.Global.integralFiniteAdeles (𝓞 ℚ) ℚ : Set AfQ) : Set AfQᵐᵒᵖ) :=
    MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hO
  have e : (ZU : Set AfQˣ) = Units.embedProduct _ ⁻¹'
      ((GroundTheory.Global.integralFiniteAdeles (𝓞 ℚ) ℚ : Set AfQ) ×ˢ
        (MulOpposite.unop ⁻¹' (GroundTheory.Global.integralFiniteAdeles (𝓞 ℚ) ℚ : Set AfQ))) := by
    ext s
    simp only [SetLike.mem_coe, Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply, MulOpposite.unop_op,
      GroundTheory.Global.mem_integralFiniteAdeles]
    constructor
    · intro h
      have h2 := (ZU.inv_mem h)
      exact ⟨fun v => (h v).le, fun v => (h2 v).le⟩
    · rintro ⟨h1, h2⟩ v
      have h3 : Valued.v ((s : AfQ) v) * Valued.v ((↑s⁻¹ : AfQ) v) = 1 := by
        rw [← map_mul]
        show Valued.v (((s : AfQ) * (↑s⁻¹ : AfQ)) v) = 1
        rw [Units.mul_inv]; exact map_one _
      refine le_antisymm (h1 v) ?_
      calc (1 : _) = Valued.v ((s : AfQ) v) * Valued.v ((↑s⁻¹ : AfQ) v) := h3.symm
        _ ≤ Valued.v ((s : AfQ) v) * 1 := mul_le_mul_right (h2 v) _
        _ = _ := mul_one _
  rw [e]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage (hO.prod hB')

private theorem isClosed_GUf (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    IsClosed (GUf E n : Set (GL (Fin n) (Af E) × AfQˣ)) := by
  have hl : Continuous fun p : GL (Fin n) (Af E) × AfQˣ =>
      (p.1.val.map (conjFin (GlobalTheory.SplitPts.conjE E)))ᵀ * p.1.val :=
    ((Units.continuous_val.comp continuous_fst).matrix_map (continuous_conjFin _)).matrix_transpose.matrix_mul
      (Units.continuous_val.comp continuous_fst)
  have hr : Continuous fun p : GL (Fin n) (Af E) × AfQˣ =>
      GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (p.2 : AfQ) • (1 : Matrix (Fin n) (Fin n) (Af E)) :=
    Continuous.smul (f := fun p : GL (Fin n) (Af E) × AfQˣ => GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (p.2 : AfQ))
      (g := fun _ => (1 : Matrix (Fin n) (Fin n) (Af E)))
      (GroundTheory.Global.AdeleBaseChange.continuous_finiteAdeleMap.comp (Units.continuous_val.comp continuous_snd))
      continuous_const
  exact isClosed_eq hl hr

theorem UpperTheory.Gal.CertificateRingHomMap.pIntCompact_of :
    UpperTheory.Gal.CertificateRingHomMap.IntCompact := by
  intro E _ _ _ n
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  have e : Subtype.val '' (lev (E := E) (n := n) ∅ (fun _ => ⊤) : Set (GUf E n)) =
      (GUf E n : Set (GL (Fin n) (Af E) × AfQˣ)) ∩ ((GlobalTheory.EulerTw.Kglob E n : Set _) ×ˢ (ZU : Set AfQˣ)) := by
    ext p
    constructor
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨h1, -, h3⟩ := mem_lev.1 hk
      exact ⟨k.2, GlobalTheory.EulerTwRestr.mem_Kglob.2 fun w => h3 w (by simp) (by simp), h1⟩
    · rintro ⟨hp, h1, h2⟩
      refine ⟨⟨p, hp⟩, mem_lev.2 ⟨h2, by simp, fun w _ _ => GlobalTheory.EulerTwRestr.mem_Kglob.1 h1 w⟩, rfl⟩
  rw [e]
  exact ((GlobalTheory.EulerTwRestr.isCompact_Kglob (E := E) (n := n)).prod isCompact_ZU).inter_left (isClosed_GUf E n)
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pLevCompact_of :
    UpperTheory.Gal.CertificateRingHomMap.IntCompact → UpperTheory.Gal.CertificateRingHomMap.IntConj → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.LevOpen → UpperTheory.Gal.CertificateRingHomMap.LevCompact := by
  intro hC hI hL hO E _ _ _ n Up w₀ hw₀ S Kw hS
  obtain ⟨-, hAp, -, -, -, -⟩ := hL E n w₀ hw₀
  have hclosed : IsClosed (lev S Kw : Set (GUf E n)) :=
    Subgroup.isClosed_of_isOpen _ (hO E n S Kw hS.opn)
  have hK₁ := hC E n
  have hJ := hS.cpt w₀ hS.mem
  have hKo := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w₀ n).1
  obtain ⟨F, -, hF⟩ := hJ.elim_nhds_subcover
    (fun a => {y : GLw n w₀ | a⁻¹ * y ∈ GlobalTheory.LFun.KGL w₀ n}) (fun a _ => by
      refine IsOpen.mem_nhds (hKo.preimage (continuous_const.mul continuous_id)) ?_
      simp [Subgroup.one_mem])
  have hcov : IsCompact (⋃ a ∈ F, (fun x : GUf E n => loc hw₀ a * x) ''
      (lev (E := E) (n := n) ∅ (fun _ => ⊤) : Set (GUf E n))) :=
    F.isCompact_biUnion fun a _ => hK₁.image (continuous_const.mul continuous_id)
  refine hcov.of_isClosed_subset hclosed fun k hk => ?_
  obtain ⟨hsim, hmem, hoff⟩ := mem_lev.1 hk
  obtain ⟨a, haF, ha⟩ := Set.mem_iUnion₂.1 (hF (hmem w₀ hS.mem))
  have ha' : a⁻¹ * comp w₀ k ∈ GlobalTheory.LFun.KGL w₀ n := ha
  have hsim' : sim ((loc hw₀ a)⁻¹ * k) ∈ ZU := by simpa using hsim
  have hw : comp w₀ ((loc hw₀ a)⁻¹ * k) ∈ GlobalTheory.LFun.KGL w₀ n := by simpa using ha'
  have hint : ∀ u : Plc E, u ≠ w₀ → u ≠ cj w₀ → comp u k ∈ GlobalTheory.LFun.KGL u n := by
    intro u h1 h2
    have hcc : cj (cj u) = u := GlobalTheory.SplitPts.conjSrc_conjSrc_cm u
    by_cases hu : u ∈ S
    · exact hS.le u hu h1 (hmem u hu)
    by_cases hc : cj u ∈ S
    · have hne : cj u ≠ w₀ := fun h => h2 (by rw [← h, hcc])
      have := hI E n k (cj u) hsim (hS.le _ hc hne (hmem _ hc))
      rwa [hcc] at this
    · exact hoff u hu hc
  have hk' : (loc hw₀ a)⁻¹ * k ∈ lev (E := E) (n := n) ∅ (fun _ => ⊤) := by
    refine mem_lev.2 ⟨hsim', by simp, fun u _ _ => ?_⟩
    by_cases h1 : u = w₀
    · subst h1; exact hw
    by_cases h2 : u = cj w₀
    · subst h2; exact hI E n _ w₀ hsim' hw
    · have happ : GlobalTheory.Cong.Apart u w₀ := (hAp u).2 ⟨h1, h2⟩
      have : comp u ((loc hw₀ a)⁻¹ * k) = comp u k := by
        rw [map_mul, map_inv, comp_loc_of_apart hw₀ happ, inv_one, one_mul]
      rw [this]
      exact hint u h1 h2
  exact Set.mem_iUnion₂.2 ⟨a, haF, _, hk', by simp⟩
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pSphType_of :
    UpperTheory.Gal.CertificateRingHomMap.IntConj → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.SphType := by
  intro hIC hLC E _ _ _ n π w hw
  refine ⟨?_, ?_⟩
  · rintro ⟨B, σ, ⟨-, f, hf0, hfV, hf⟩, hB⟩
    have hker : LinearMap.ker f = ⊥ := by
      refine (((GlobalTheory.CuspRep.isIrreducible_iff σ.ρ).1 σ.irred).2 (LinearMap.ker f) (fun g v hv => ?_)).resolve_right
        fun h => hf0 (LinearMap.ker_eq_top.1 h)
      rw [LinearMap.mem_ker] at hv ⊢
      have h1 := hf ⟨(locF hw g).1, locF_mem hw g⟩ v
      simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, cLoc_locF] at h1
      rw [h1, hv, map_zero]
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hB.1
    have hfix := GlobalTheory.LGrp.mem_fixed.1 hv
    have hφ0 : f v ≠ 0 := fun h => hv0 (LinearMap.ker_eq_bot.1 hker (h.trans (map_zero f).symm))
    have key : ∀ x ∈ locU n w, cLoc w x ∈ GlobalTheory.LFun.KGL w n → RU E n x (f v) = f v := by
      intro x hx hk
      have h1 := hf ⟨x, hx⟩ v
      simp only [MonoidHom.comp_apply, Subgroup.subtype_apply] at h1
      rw [← h1, hfix _ hk]
    obtain ⟨-, -, -, -, hcc, hloc⟩ := hLC E n w hw
    refine ⟨⟨f v, hfV v, hφ0, fun x hx h => ?_⟩, ⟨f v, hfV v, hφ0, fun x hx h => ?_⟩⟩
    · simpa using key x hx h
    · rw [hloc] at hx
      have h2 := hIC E n (ofU ⟨x, (Subgroup.mem_inf.1 hx).1⟩) (cj w) (by rw [sim_ofU]; exact one_mem _)
        (by rw [comp_ofU]; exact h)
      rw [hcc, comp_ofU] at h2
      simpa using key x hx h2
  · rintro J χ ⟨φ, hφ, h0, hact⟩
    have hlev := (π.isAut.aut φ hφ).level
    have hc : Continuous fun k : J => (locF hw k.1 : finU E n) := by
      have h1 : Continuous fun k : GLw n w => (locF hw k : finU E n) :=
        Continuous.subtype_mk (continuous_subtype_val.comp (locE hw).symm.continuous) _
      exact h1.comp continuous_subtype_val
    have hset : {k : J | χ k = 1} = (fun k : J => (locF hw k.1 : finU E n)) ⁻¹' {k : finU E n | RU E n k φ = φ} := by
      ext k
      have hk : cLoc w (locF hw k.1).1 ∈ J := by rw [cLoc_locF]; exact k.2
      have h1 := hact (locF hw k.1).1 (locF_mem hw k.1) hk
      have h2 : (⟨cLoc w (locF hw k.1).1, hk⟩ : J) = k := Subtype.ext (cLoc_locF hw k.1)
      rw [h2] at h1
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      rw [h1]
      constructor
      · intro h; rw [h]; simp
      · intro h
        have h3 : ((χ k : ℂˣ) : ℂ) = 1 := smul_left_injective ℂ h0 (by simpa using h)
        exact Units.ext h3
    rw [hset]
    exact hlev.preimage hc
end

section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open GlobalTheory.LFun (KGL)
open GlobalTheory.CongL (SatU)
open GlobalTheory.Cong (Apart)
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end UpperTheory.Gal.CertificateRingHomMap

theorem UpperTheory.Gal.CertificateRingHomMap.pVecU_of :
    UpperTheory.Gal.CertificateRingHomMap.NbhdU → UpperTheory.Gal.CertificateRingHomMap.StepAt → UpperTheory.Gal.CertificateRingHomMap.SphType → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.VecU :=
  _root_.UpperTheory.Reformulated.B.Grk2.pVecU_of
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep
open GlobalTheory.LFun (KGL heckeVec)
open GlobalTheory.Cong (Apart)
open GlobalTheory.LKDef.HeckeTraceForms (forms)
open Formalism.UG (Tj Ov IsUnifV)
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem hecke_eq_sum {G : Type} [Group G] (K : Subgroup G) (h : G → ℂ) (h01 : ∀ g, h g ≠ 0 → h g = 1)
    (hfin : {q : G ⧸ K | h q.out ≠ 0}.Finite) : ∃ R : Finset G,
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (x : V),
        heckeVec ρ K h x = ∑ g ∈ R, ρ g x := by
  refine ⟨hfin.toFinset.image Quotient.out, ?_⟩
  intro V _ _ ρ x
  rw [Finset.sum_image (fun a _ b _ e => Quotient.out_injective e)]
  have hsupp : (Function.support fun q : G ⧸ K => h q.out • ρ q.out x) ⊆ hfin.toFinset := by
    intro q hq
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h0
    exact hq (by simp [h0])
  have hsum : heckeVec ρ K h x = ∑ q ∈ hfin.toFinset, h q.out • ρ q.out x :=
    finsum_eq_sum_of_support_subset _ hsupp
  rw [hsum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [h01 _ ((Set.Finite.mem_toFinset hfin).1 hq), one_smul]

private theorem tj_one {L : Type} [Field L] {n : ℕ} {O : Subring L} {ϖ : L} {j : ℕ} (g : GL (Fin n) L)
    (hg : Tj ℂ n O ϖ j g ≠ 0) : Tj ℂ n O ϖ j g = 1 := by
  unfold Tj at hg ⊢
  exact Set.indicator_of_mem (Set.mem_of_indicator_ne_zero hg) _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem sum_mem_forms (hC : LocComm) (hM : LocMem) {w : Plc E} (hw : IsSplitAt w) {h : GLw n w → ℂ}
    (hh : h ∈ Formalism.UG.Hecke ℂ (KGL w n)) {R : Finset (GLw n w)}
    (hR : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLw n w) V) (v : V),
      heckeVec ρ (KGL w n) h v = ∑ g ∈ R, ρ g v)
    {S : Finset (Plc E)} {Kw : ∀ w : Plc E, Subgroup (GLw n w)} (hS : w ∉ S) (hcS : cj w ∉ S)
    {V : Type} [AddCommGroup V] [Module ℂ V] {ξ : Representation ℂ (Gam0 E n) V} {Φ : GUf E n → V}
    (hΦ : Φ ∈ forms rat (lev S Kw) ξ) :
    (fun g => ∑ y ∈ R, Φ (g * loc hw y)) ∈ forms rat (lev S Kw) ξ := by
  have hloc : ∀ y ∈ KGL w n, loc hw y ∈ lev S Kw := fun y hy => (hM E n S Kw w hw hcS y).2 hS hy
  let ρ : Representation ℂ (GLw n w) (GUf E n → V) := (rightReg ℂ (GUf E n) V).comp (loc hw)
  have hρ : ∀ y (f : GUf E n → V) g, ρ y f g = f (g * loc hw y) := fun _ _ _ => rfl
  have hfix : Φ ∈ fixed ρ (KGL w n) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    funext g
    rw [hρ]
    exact hΦ.2 _ (hloc k hk) g
  have hΨ := GlobalTheory.LFun.SatCompare.heckeVec_mem_fixed (Formalism.UG.Final.GLintComm E w n) hh hfix
  rw [hR] at hΨ
  have hΨ' := GlobalTheory.LGrp.mem_fixed.1 hΨ
  have hev : ∀ g, (∑ y ∈ R, ρ y Φ) g = ∑ y ∈ R, Φ (g * loc hw y) := fun g => by
    rw [Finset.sum_apply]
    rfl
  refine ⟨fun γ g => ?_, fun k hk g => ?_⟩
  · simp only [map_sum, mul_assoc]
    exact Finset.sum_congr rfl fun y _ => hΦ.1 γ _
  · have hx : comp w k ∈ KGL w n := (mem_lev.1 hk).2.2 w hS hcS
    set x := comp w k with hxdef
    set k' := (loc hw x)⁻¹ * k with hk'def
    have hk'm : k' ∈ lev S Kw := (lev S Kw).mul_mem ((lev S Kw).inv_mem (hloc x hx)) hk
    have hk'1 : comp w k' = 1 := by
      rw [hk'def, map_mul, map_inv, comp_loc, ← hxdef, inv_mul_cancel]
    have hcomm := (hC E n w hw).1 k' hk'1
    have hkk : k = loc hw x * k' := by rw [hk'def, mul_inv_cancel_left]
    have e1 : ∀ y, Φ (g * k * loc hw y) = Φ (g * loc hw x * loc hw y) := fun y => by
      calc Φ (g * k * loc hw y) = Φ (g * loc hw x * loc hw y * k') := by
            rw [hkk, mul_assoc g, mul_assoc _ k', hcomm y]; simp only [mul_assoc]
        _ = _ := hΦ.2 _ hk'm _
    have e2 := congrFun (hΨ' x hx) g
    rw [hρ, hev, hev] at e2
    show ∑ y ∈ R, Φ (g * k * loc hw y) = ∑ y ∈ R, Φ (g * loc hw y)
    rw [← e2]
    exact Finset.sum_congr rfl fun y _ => e1 y

theorem pHeckePres_of (hC : LocComm) (hM : LocMem) : HeckePres := by
  intro E _ _ _ n w hw ϖ hϖ i
  have hh := GlobalTheory.LFun.Tj_mem_hecke (n := n) hϖ i
  obtain ⟨R, hR⟩ := hecke_eq_sum (KGL w n) (Tj ℂ n (Ov E w) ϖ i) (fun g hg => tj_one g hg)
    (Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm E w n) hh.2)
  exact ⟨R, hR, fun S Kw hS hcS V _ _ ξ Φ hΦ => sum_mem_forms hC hM hw hh hR hS hcS hΦ⟩

end UpperTheory.Gal.CertificateRingHomMap

end
end

section
namespace UpperTheory.Gal.CertificateRingHomMap

universe u v

theorem extZero_holds : ExtZero := pExtZero_holds
theorem centralEig2_holds : CentralEig2 := pCentralEig2_of
theorem extEig2_holds : ExtEig2 := pExtEig2_of extZero_holds centralEig2_holds
theorem locAdj_holds : LocAdj := pLocAdj_of
theorem rootsAlg_holds : RootsAlg := pRootsAlg_of
theorem finToHecke_holds : FinToHecke := pFinToHecke_of
theorem classFin_holds : ClassFin := pClassFin_of
theorem xiScalar_holds : XiScalar := pXiScalar_of
theorem xiZeta_holds : XiZeta := pXiZeta_of xiScalar_holds
theorem intConj_holds : IntConj := pIntConj_of
theorem intSim_holds : IntSim := pIntSim_of
theorem ofUBij_holds : OfUBij := pOfUBij_of
theorem locComm_holds : LocComm := pLocComm_of
theorem locMem_holds : LocMem := pLocMem_of intConj_holds locComm_holds
theorem levOpen_holds : LevOpen := pLevOpen_of
theorem intCompact_holds : IntCompact := pIntCompact_of
theorem levCompact_holds : LevCompact := pLevCompact_of intCompact_holds intConj_holds locComm_holds levOpen_holds
theorem nhds_basis_levelSubgroup : Nbhd2 := pNbhd2_of
theorem nbhdU_holds : NbhdU := pNbhdU_of nhds_basis_levelSubgroup intConj_holds locComm_holds ofUBij_holds
theorem sphType_holds : SphType := pSphType_of intConj_holds locComm_holds
theorem stepAt_holds : StepAt := pStepAt_of locAdj_holds locComm_holds ofUBij_holds
theorem vecU_holds : VecU := pVecU_of nbhdU_holds stepAt_holds sphType_holds locComm_holds
theorem satVal_holds : SatVal := pSatVal_of
theorem kerFormU_holds : KerFormU := pKerFormU_of ofUBij_holds
theorem heckePres_holds : HeckePres := pHeckePres_of locComm_holds locMem_holds
theorem kapOf_holds : KapOf := pKapOf_of finToHecke_holds xiZeta_holds intSim_holds levOpen_holds

theorem formGU_holds : FormGU :=
  pFormGU_of extEig2_holds classFin_holds xiZeta_holds kerFormU_holds heckePres_holds satVal_holds locMem_holds locComm_holds
    levOpen_holds ofUBij_holds

theorem seedGU_holds : SeedGU :=
  seedGU_of zetaEx_holds vecU_holds sphType_holds formGU_holds kapOf_holds levOpen_holds levCompact_holds

end UpperTheory.Gal.CertificateRingHomMap
end
