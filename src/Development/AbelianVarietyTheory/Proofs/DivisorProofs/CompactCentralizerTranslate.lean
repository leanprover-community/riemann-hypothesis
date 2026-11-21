import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitsLocallyCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactModNormOneKernelInvolution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerSimilitudeBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCentralizerComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixSqrtNearOneUltrametric

section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.SqrtFixCent

theorem eq_mul_of_comm_mulRight {K A : Type} [Field K] [Ring A] [Algebra K A] (f : Module.End K A)
    (hf : ∀ y : A, LinearMap.mulRight K y * f = f * LinearMap.mulRight K y) (y : A) :
    f y = f 1 * y := by
  have h := congrArg (fun g : Module.End K A => g 1) (hf y)
  change f 1 * y = f (1 * y) at h
  rw [one_mul] at h
  exact h.symm

end GlobalTheory.SqrtFixCent

namespace GlobalTheory

theorem sqrt_fix_near_one_centralizer : ∀ (p : ℕ) [Fact p.Prime] (v : AwayP p) (B : Type) [Ring B] [Algebra (Qv v) B] [Module.Finite (Qv v) B], letI : TopologicalSpace B := moduleTopology (Qv v) B; ∀ (e : B) (σ : B →ₗ[Qv v] B), (∀ a b : B, a * e = e * a → b * e = e * b → a * b = b * a) → (∀ a : B, a * e = e * a → σ a * e = e * σ a) → (∀ a b : B, a * e = e * a → b * e = e * b → σ (a * b) = σ a * σ b) → σ 1 = 1 → ∃ W ∈ nhds (1 : B), ∀ s ∈ W, s * e = e * s → σ s = s → ∃ r : B, r * e = e * r ∧ σ r = r ∧ r * r = s := by
  intro p _ v B _ _ _
  letI tB : TopologicalSpace B := moduleTopology (Qv v) B
  haveI : IsModuleTopology (Qv v) B := ⟨rfl⟩
  intro e σ _ hσe hσm hσ1
  let M : Subalgebra (Qv v) B := Subalgebra.centralizer (Qv v) {e}
  have hM : ∀ x : B, x ∈ M ↔ x * e = e * x := by
    intro x
    simp [M, Subalgebra.mem_centralizer_iff, eq_comm]
  haveI : CharZero (Qv v) := charZero_of_injective_algebraMap (algebraMap ℚ (Qv v)).injective
  letI : NontriviallyNormedField (Qv v) := Valued.toNontriviallyNormedField _ _
  let d := Module.finrank (Qv v) M
  let bM := Module.finBasis (Qv v) M
  let Lm : M →ₐ[Qv v] Matrix (Fin d) (Fin d) (Qv v) :=
    (LinearMap.toMatrixAlgEquiv bM).toAlgHom.comp (Algebra.lmul (Qv v) M)
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (Subalgebra.toSubmodule M)
  let P : B →ₗ[Qv v] M := Submodule.linearProjOfIsCompl (Subalgebra.toSubmodule M) q hq
  have hP : ∀ x : M, P x = x := fun x => Submodule.linearProjOfIsCompl_apply_left hq x
  let L : B →ₗ[Qv v] Matrix (Fin d) (Fin d) (Qv v) := Lm.toLinearMap ∘ₗ P
  have hLc : Continuous L := IsModuleTopology.continuous_of_linearMap L
  have hL1 : L 1 = 1 := by
    show Lm (P ((1 : M) : B)) = 1
    rw [hP, map_one]
  obtain ⟨W₀, hW₀, hW₀s⟩ := GlobalTheory.matrix_sqrt_near_one_ultrametric (Qv v) d (RingHom.id _) continuous_id
  refine ⟨L ⁻¹' W₀, hLc.continuousAt.preimage_mem_nhds (by rw [hL1]; exact hW₀), ?_⟩
  intro s hs hse hσs
  let sM : M := ⟨s, (hM s).2 hse⟩
  have hLs : L s = Lm sM := by
    show Lm (P (sM : B)) = Lm sM
    rw [hP]
  obtain ⟨R, hRR, hRc, -⟩ := hW₀s _ (show L s ∈ W₀ from hs)
  rw [hLs] at hRR hRc
  let T := LinearMap.toMatrixAlgEquiv bM
  let f : Module.End (Qv v) M := T.symm R
  have hTs : Lm sM = T (LinearMap.mulLeft (Qv v) sM) := rfl
  have hf : ∀ g : Module.End (Qv v) M, g * LinearMap.mulLeft (Qv v) sM = LinearMap.mulLeft (Qv v) sM * g →
      g * f = f * g := by
    intro g hg
    apply T.injective
    rw [map_mul, map_mul, AlgEquiv.apply_symm_apply]
    apply hRc
    rw [hTs, ← map_mul, ← map_mul, hg]
  have hff : f * f = LinearMap.mulLeft (Qv v) sM := by
    apply T.injective
    rw [map_mul, AlgEquiv.apply_symm_apply, hRR]
    exact hTs
  have hfy : ∀ y : M, f y = f 1 * y := by
    refine GlobalTheory.SqrtFixCent.eq_mul_of_comm_mulRight f fun y => (hf _ ?_)
    exact LinearMap.ext fun x => mul_assoc sM x y
  have hρρ : f 1 * f 1 = sM := by
    have h := LinearMap.congr_fun hff 1
    change f (f 1) = sM * 1 at h
    rw [hfy (f 1), mul_one] at h
    exact h
  let σM : Module.End (Qv v) M :=
    { toFun := fun x => ⟨σ x, (hM _).2 (hσe x ((hM x).1 x.2))⟩
      map_add' := fun x y => Subtype.ext (by show σ ((x : B) + y) = σ x + σ y; exact map_add σ _ _)
      map_smul' := fun c x => Subtype.ext (by show σ (c • (x : B)) = c • σ x; exact map_smul σ _ _) }
  have hσM : ∀ x : M, ((σM x : M) : B) = σ x := fun x => rfl
  have hcomm : σM * LinearMap.mulLeft (Qv v) sM = LinearMap.mulLeft (Qv v) sM * σM := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    show σ ((sM : B) * x) = (sM : B) * σ x
    rw [hσm s x hse ((hM x).1 x.2), hσs]
  have hσ1M : σM 1 = 1 := Subtype.ext (by show σ ((1 : M) : B) = ((1 : M) : B); exact hσ1)
  have hσρ : σM (f 1) = f 1 := by
    have h := LinearMap.congr_fun (hf σM hcomm) 1
    change σM (f 1) = f (σM 1) at h
    rw [hσ1M] at h
    exact h
  refine ⟨((f 1 : M) : B), (hM _).1 (f 1).2, congrArg Subtype.val hσρ, congrArg Subtype.val hρρ⟩

end GlobalTheory
end
end

section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sqrt_fixed_near_one_commutative_centralizer : ∀ (p : ℕ) [Fact p.Prime] (v : AwayP p) (B : Type) [Ring B] [Algebra (Qv v) B] [Module.Finite (Qv v) B], letI : TopologicalSpace B := moduleTopology (Qv v) B; ∀ (e : B) (σ : B →ₗ[Qv v] B), (∀ a b : B, a * e = e * a → b * e = e * b → a * b = b * a) → (∀ a : B, a * e = e * a → σ a * e = e * σ a) → (∀ a b : B, a * e = e * a → b * e = e * b → σ (a * b) = σ a * σ b) → σ 1 = 1 → ∃ W ∈ nhds (1 : B), ∀ s ∈ W, s * e = e * s → σ s = s → ∃ r : B, r * e = e * r ∧ σ r = r ∧ r * r = s := by
  first | (exact @GlobalTheory.sqrt_fix_near_one_centralizer) | (exact GlobalTheory.sqrt_fix_near_one_centralizer) | (intros; apply GlobalTheory.sqrt_fix_near_one_centralizer <;> assumption)
end

section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.TorusNorm

theorem exists_compact_mod_sim (Z S : Type) [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z]
    [LocallyCompactSpace Z] [SigmaCompactSpace Z] [T2Space Z]
    [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [LocallyCompactSpace S] [SigmaCompactSpace S]
    [T2Space S] (hZ : ∀ a b : Z, a * b = b * a) (hS : ∀ a b : S, a * b = b * a)
    (τ : Z →* Z) (hτc : Continuous τ) (hτi : ∀ z, τ (τ z) = z)
    (hsq : ∃ W ∈ nhds (1 : Z), ∀ s ∈ W, τ s = s → ∃ r : Z, τ r = r ∧ r * r = s)
    (ι : S →* Z) (hιc : Continuous ι) (hτι : ∀ a, τ (ι a) = ι a)
    (hU : ∃ U ∈ nhds (1 : S), ∀ a ∈ U, a * a = 1 → a = 1) (D : Set Z) (hD : IsCompact D) :
    ∃ B : Set Z, IsCompact B ∧ ∀ (z : Z) (a : S), τ z * z * (ι a)⁻¹ ∈ D →
      ∃ u : Z, ∃ l : S, τ u * u = ι l ∧ ∃ b ∈ B, z = u * b := by
  let T : Z × S →* Z × S :=
    { toFun := fun h => (τ h.1 * (ι h.2)⁻¹, h.2⁻¹)
      map_one' := by simp
      map_mul' := fun h k => by
        ext
        · show τ (h.1 * k.1) * (ι (h.2 * k.2))⁻¹ = τ h.1 * (ι h.2)⁻¹ * (τ k.1 * (ι k.2)⁻¹)
          rw [map_mul, map_mul, _root_.mul_inv_rev, hZ (ι k.2)⁻¹ (ι h.2)⁻¹]
          simp only [mul_assoc]
          congr 1
          rw [← mul_assoc, ← mul_assoc, hZ (ι h.2)⁻¹ (τ k.1)]
        · show (h.2 * k.2)⁻¹ = h.2⁻¹ * k.2⁻¹
          rw [_root_.mul_inv_rev, hS] }
  have hT : ∀ h, T h = (τ h.1 * (ι h.2)⁻¹, h.2⁻¹) := fun h => rfl
  have hcomm : ∀ a b : Z × S, a * b = b * a := fun a b => Prod.ext (hZ _ _) (hS _ _)
  have hTc : Continuous T := by
    show Continuous fun h : Z × S => (τ h.1 * (ι h.2)⁻¹, h.2⁻¹)
    exact ((hτc.comp continuous_fst).mul (hιc.comp continuous_snd).inv).prodMk continuous_snd.inv
  have hTi : ∀ h, T (T h) = h := by
    intro h
    rw [hT, hT]
    ext
    · simp only [map_mul, map_inv, hτi, hτι, inv_inv]
      rw [mul_assoc, inv_mul_cancel, mul_one]
    · simp
  obtain ⟨W, hW, hWs⟩ := hsq
  obtain ⟨U, hU1, hUs⟩ := hU
  have hsqT : ∃ W' ∈ nhds (1 : Z × S), ∀ s ∈ W', T s = s → ∃ r : Z × S, T r = r ∧ r * r = s := by
    refine ⟨W ×ˢ U, prod_mem_nhds hW hU1, fun s hs hTs => ?_⟩
    have h2 : s.2⁻¹ = s.2 := congrArg Prod.snd hTs
    have ha : s.2 = 1 := hUs _ hs.2 (by
      calc s.2 * s.2 = s.2 * s.2⁻¹ := by rw [h2]
        _ = 1 := mul_inv_cancel _)
    have h1 : τ s.1 * (ι s.2)⁻¹ = s.1 := congrArg Prod.fst hTs
    rw [ha, map_one, inv_one, mul_one] at h1
    obtain ⟨r, hr, hrr⟩ := hWs _ hs.1 h1
    refine ⟨(r, 1), ?_, ?_⟩
    · rw [hT]; simp [hr]
    · ext
      · exact hrr
      · simp [ha]
  haveI : T2Space (Z × S) := inferInstance
  obtain ⟨B, hB, hBs⟩ := GlobalTheory.InvolutionNorm.exists_compact_mod_kernel (Z × S) hcomm T hTc hTi hsqT
    (D ×ˢ {1}) (hD.prod isCompact_singleton)
  refine ⟨Prod.fst '' B, hB.image continuous_fst, fun z a hz => ?_⟩
  have hmem : T (z, a) * (z, a) ∈ D ×ˢ ({1} : Set S) := by
    rw [hT]
    refine ⟨?_, ?_⟩
    · show τ z * (ι a)⁻¹ * z ∈ D
      rw [mul_assoc, hZ (ι a)⁻¹ z, ← mul_assoc]; exact hz
    · show a⁻¹ * a = 1
      exact inv_mul_cancel a
  obtain ⟨t, ht, b, hb, hzb⟩ := hBs _ hmem
  refine ⟨t.1, t.2, ?_, b.1, ⟨b, hb, rfl⟩, congrArg Prod.fst hzb⟩
  have h1 : τ t.1 * (ι t.2)⁻¹ * t.1 = 1 := congrArg Prod.fst ht
  rw [mul_assoc, hZ _ t.1, ← mul_assoc] at h1
  exact mul_inv_eq_one.1 h1

end GlobalTheory.OrbFinAf.TorusNorm

namespace GlobalTheory.OrbFinAf.TorusNorm

end GlobalTheory.OrbFinAf.TorusNorm
end
end
