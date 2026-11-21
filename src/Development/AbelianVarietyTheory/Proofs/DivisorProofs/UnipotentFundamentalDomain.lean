import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement

section
noncomputable section

namespace GlobalTheory.CuspDbl

open Metric

def IsRegFam {Y : Type} [TopologicalSpace Y] (ht : Y → ℝ) (s₀ : ℂ) (Ez : ℂ → Y → Y → ℂ) : Prop :=
  ∀ s₁ : ℂ, ∃ (k : ℕ) (r C : ℝ) (N : ℕ) (Hf : ℂ → Y → Y → ℂ), 0 < r ∧ (s₁ = s₀ → k = 0) ∧
    (∀ s ∈ ball s₁ r, (s ≠ s₁ ∨ k = 0) → ∀ h h', Hf s h h' = (s - s₁) ^ k * Ez s h h') ∧
    (∀ h h', DifferentiableOn ℂ (Hf · h h') (ball s₁ r)) ∧
    (∀ s ∈ ball s₁ r, Continuous fun x : Y × Y => Hf s x.1 x.2) ∧
    ∀ s ∈ ball s₁ r, ∀ h h', ‖Hf s h h'‖ ≤ C * (ht h * ht h') ^ N

end GlobalTheory.CuspDbl

end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open Formalism.UG (cT)
open GlobalTheory.ThKLiftCusp

noncomputable section

namespace GlobalTheory.UnipMatch

open Matrix

theorem exists_genInv {K : Type} [Field K] {a b : ℕ} (M : Matrix (Fin a) (Fin b) K) :
    ∃ N : Matrix (Fin b) (Fin a) K, M * N * M = M := by
  classical
  let f := Matrix.toLin' M
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range f).subtype (Submodule.ker_subtype _)
  obtain ⟨g', hg'⟩ := LinearMap.exists_rightInverse_of_surjective f.rangeRestrict (LinearMap.range_rangeRestrict f)
  refine ⟨LinearMap.toMatrix' (g' ∘ₗ p), Matrix.toLin'.injective ?_⟩
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro x
  have h1 : p (f x) = f.rangeRestrict x := by
    simpa using LinearMap.congr_fun hp (f.rangeRestrict x)
  have h2 : ∀ y, f (g' y) = y := fun y => by simpa using congrArg Subtype.val (LinearMap.congr_fun hg' y)
  show f (g' (p (f x))) = f x
  rw [h1, h2]
  rfl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cA_inclR (y : E) : cA σ (inclR (F := F) (AF F) y) = inclR (F := F) (AF F) (σ y) := by
  simp [cA, inclR]

theorem adMat_mulVec_eq {d j : ℕ} (J : Matrix (Fin d) (Fin d) E) (hJ : ∀ i l, σ (J l i) = -J i l) (c : E)
    (Y : Matrix (Fin d) (Fin j) E) (z : Fin d → AE F E) (k : Fin j) :
    (adMat F (cT (σ : E →+* E) Y * (c • J.map σ)) *ᵥ z) k =
      -(inclR (F := F) (AF F) c) * formA σ J z (incV F fun i => Y i k) := by
  simp only [mulVec, dotProduct, adMat, map_apply, mul_apply, cT, transpose_apply, Matrix.smul_apply, smul_eq_mul, formA,
    incM, incV, cA_inclR, map_sum, map_mul, map_neg, hJ, Finset.mul_sum, Finset.sum_mul, RingHom.coe_coe]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem cond_iff {d j : ℕ} (J : Matrix (Fin d) (Fin d) E) (hJ : ∀ i l, σ (J l i) = -J i l) {c : E} (hc : c ≠ 0)
    (Y : Matrix (Fin d) (Fin j) E) (U : Matrix (Fin d) (Fin d) (AE F E)) :
    (U * incM F Y = incM F Y ∧
      (∀ z, (∀ k, formA σ J z (incV F fun i => Y i k) = 0) → ∃ a, U *ᵥ z = z + incM F Y *ᵥ a) ∧
      ∀ z k, formA σ J (U *ᵥ z - z) (incV F fun i => Y i k) = 0) ↔
    ((U - 1) * adMat F Y = 0 ∧ adMat F (cT (σ : E →+* E) Y * (c • J.map σ)) * (U - 1) = 0 ∧
      ∀ x : Fin d → E, (cT (σ : E →+* E) Y * (c • J.map σ)) *ᵥ x = 0 →
        ∃ a : Fin j → AF F ⊗[F] E, (U - 1) *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = adMat F Y *ᵥ a) := by
  classical
  set M := cT (σ : E →+* E) Y * (c • J.map σ) with hM
  have hY : incM F Y = adMat F Y := rfl
  have hu : IsUnit (-(inclR (F := F) (AF F) c)) := ((IsUnit.mk0 c hc).map (inclR (F := F) (AF F))).neg
  have hb : ∀ z, (U - 1) *ᵥ z = U *ᵥ z - z := fun z => by rw [sub_mulVec, one_mulVec]
  have hker : ∀ z, (∀ k, formA σ J z (incV F fun i => Y i k) = 0) ↔ adMat F M *ᵥ z = 0 := fun z => by
    constructor
    · intro h; funext k; rw [adMat_mulVec_eq J hJ c Y z k, h k, mul_zero]; rfl
    · intro h k
      have e := adMat_mulVec_eq J hJ c Y z k
      rw [h] at e
      exact hu.mul_right_eq_zero.1 e.symm
  have h1 : U * incM F Y = incM F Y ↔ (U - 1) * adMat F Y = 0 := by
    rw [hY, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero]
  have h3 : (∀ z k, formA σ J (U *ᵥ z - z) (incV F fun i => Y i k) = 0) ↔ adMat F M * (U - 1) = 0 := by
    constructor
    · intro h
      ext k l
      have e : (adMat F M *ᵥ ((U - 1) *ᵥ Pi.single l 1)) k = 0 := by
        rw [adMat_mulVec_eq J hJ c Y _ k, hb, h, mul_zero]
      rw [mulVec_mulVec, mulVec_single_one] at e
      exact e
    · intro h z k
      rw [← hb]
      refine (hker _).2 ?_ k
      rw [mulVec_mulVec, h, zero_mulVec]
  have h2 : (∀ z, (∀ k, formA σ J z (incV F fun i => Y i k) = 0) → ∃ a, U *ᵥ z = z + incM F Y *ᵥ a) ↔
      ∀ x : Fin d → E, M *ᵥ x = 0 →
        ∃ a : Fin j → AF F ⊗[F] E, (U - 1) *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = adMat F Y *ᵥ a := by
    constructor
    · intro h x hx
      have hz : adMat F M *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = 0 := funext fun k => by
        rw [show (fun i => inclR (F := F) (AF F) (x i)) = inclR (F := F) (AF F) ∘ x from rfl, adMat,
          ← RingHom.map_mulVec, hx]
        exact map_zero _
      obtain ⟨a, ha⟩ := h _ ((hker _).2 hz)
      exact ⟨a, by rw [hb, ha, hY, add_sub_cancel_left]⟩
    · intro h z hz
      have hz' := (hker z).1 hz
      obtain ⟨N, hN⟩ := exists_genInv M
      set Q : Matrix (Fin d) (Fin d) E := 1 - N * M with hQ
      have hMQ : M * Q = 0 := by rw [hQ, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hN, sub_self]
      have hcol : ∀ l, M *ᵥ (fun i => Q i l) = 0 := fun l => by
        funext k
        have := congrFun (congrFun hMQ k) l
        simpa [mulVec, dotProduct, mul_apply] using this
      choose a ha using fun l => h (fun i => Q i l) (hcol l)
      let A : Matrix (Fin j) (Fin d) (AF F ⊗[F] E) := Matrix.of fun i l => a l i
      have hQz : adMat F Q *ᵥ z = z := by
        have e : adMat F Q = 1 - adMat F N * adMat F M := by
          simp only [adMat]
          rw [hQ, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        rw [e, sub_mulVec, one_mulVec, ← mulVec_mulVec, hz', mulVec_zero, sub_zero]
      have hmQ : (U - 1) * adMat F Q = adMat F Y * A := by
        ext i l
        have := congrFun (ha l) i
        simpa [mulVec, dotProduct, mul_apply, A] using this
      refine ⟨A *ᵥ z, ?_⟩
      calc U *ᵥ z = z + (U - 1) *ᵥ z := by rw [hb]; abel
        _ = z + (U - 1) *ᵥ (adMat F Q *ᵥ z) := by rw [hQz]
        _ = z + incM F Y *ᵥ (A *ᵥ z) := by rw [mulVec_mulVec, hmQ, ← mulVec_mulVec]; rfl
  rw [h1, h2, h3]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, c, b⟩, fun ⟨a, b, c⟩ => ⟨a, c, b⟩⟩

theorem mem_unipSp_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (d : ℕ) (W : Spc F E d) (r s : ℕ), W.IsSkew σ B r s →
    ∀ (c : E) (hc : c ≠ 0) (j : ℕ) (Y : Matrix (Fin d) (Fin j) E),
      (∀ k l, form σ W.J (fun i => Y i k) (fun i => Y i l) = 0) →
      ∀ g : UA σ W.J, g ∈ GlobalTheory.ThKLiftCusp.unipSp σ W Y ↔ toGAd hσ W.J hc g ∈ GlobalTheory.SiegelSet.unipRad σ (c • W.J.map σ) Y := by
  intro F E _ _ _ _ _ σ hσ B d W r s hW c hc j Y _ g
  have e : (GlobalTheory.ThKLiftCusp.unipSp σ W Y).map (toGAd hσ W.J hc).toMonoidHom =
      GlobalTheory.SiegelSet.unipRad σ (c • W.J.map σ) Y := by
    unfold GlobalTheory.ThKLiftCusp.unipSp GlobalTheory.SiegelSet.unipRad
    rw [MonoidHom.map_closure]
    congr 1
    ext h
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (cond_iff W.J hW.skew hc Y (mat g)).1 hg
    · intro hh
      refine ⟨(toGAd hσ W.J hc).symm h, (cond_iff W.J hW.skew hc Y _).2 ?_, by simp⟩
      have : mat ((toGAd hσ W.J hc).symm h) = ((matHom _ σ (c • W.J.map σ) h) : Matrix (Fin d) (Fin d) (AE F E)) := by
        conv_rhs => rw [← (toGAd hσ W.J hc).apply_symm_apply h]
        rfl
      rw [this]
      exact hh
  rw [← e]
  exact (Subgroup.mem_map_iff_mem (toGAd hσ W.J hc).injective).symm

end GlobalTheory.UnipMatch
end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.RatCorr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inclR_injective : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  haveI : Nontrivial (AF F) := inferInstanceAs (Nontrivial (Ainf F × Af F))
  Algebra.TensorProduct.includeRight_injective (algebraMap F (AF F)).injective

theorem sigR_inclR (σ : E →ₐ[F] E) (x : E) : sigR (AF F) σ (inclR (AF F) x) = inclR (AF F) (σ x) := by
  simp [sigR, inclR]

theorem ratU_iff (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (d : ℕ) (J : Matrix (Fin d) (Fin d) E) (c : E) (hc : c ≠ 0)
    (g : UA σ J) : g ∈ ratU σ J ↔ toGAd hσ J hc g ∈ GlobalTheory.AdelicU.ratPts σ (c • J.map σ) := by
  have hg : (g.1 : GL (Fin d) (AE F E)) ∈ HR (AF F) σ (c • J.map σ) := (toGAd hσ J hc g).2
  change g.1 ∈ (Matrix.GeneralLinearGroup.map (n := Fin d) (inclR (F := F) (E := E) (AF F))).range ↔
    g.1 ∈ (Formalism.UG.UJ (σ : E →+* E) (c • J.map σ)).map (Formalism.UG.bc (inclR (AF F)))
  constructor
  · rintro ⟨g₀, hg₀⟩
    refine ⟨g₀, ?_, hg₀⟩
    have h1 : Formalism.UG.cT (sigR (AF F) σ) ((g.1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) *
        JR (AF F) (c • J.map σ) * ((g.1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) =
        JR (AF F) (c • J.map σ) := hg
    have hm : ((g.1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) =
        (g₀ : Matrix (Fin d) (Fin d) E).map (inclR (AF F)) := by
      rw [← hg₀]; rfl
    rw [hm] at h1
    change Formalism.UG.cT (σ : E →+* E) (g₀ : Matrix (Fin d) (Fin d) E) * (c • J.map σ) * (g₀ : Matrix (Fin d) (Fin d) E) = c • J.map σ
    apply Matrix.map_injective (inclR_injective (F := F) (E := E))
    dsimp only
    have e1 : (Formalism.UG.cT (σ : E →+* E) (g₀ : Matrix (Fin d) (Fin d) E)).map (inclR (F := F) (AF F)) =
        Formalism.UG.cT (sigR (AF F) σ) ((g₀ : Matrix (Fin d) (Fin d) E).map (inclR (AF F))) := by
      ext i j
      simp [Formalism.UG.cT, sigR_inclR]
    have e2 : (c • J.map σ).map (inclR (F := F) (AF F)) = JR (AF F) (c • J.map σ) := rfl
    rw [Matrix.map_mul, Matrix.map_mul, e1, e2]
    exact h1
  · rintro ⟨g₀, -, hg₀⟩
    exact ⟨g₀, hg₀⟩

theorem ratU_iff_ratPts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (d : ℕ) (J : Matrix (Fin d) (Fin d) E) (c : E) (hc : c ≠ 0),
      ∀ g : UA σ J, g ∈ ratU σ J ↔ toGAd hσ J hc g ∈ GlobalTheory.AdelicU.ratPts σ (c • J.map σ) :=
  fun _ _ _ _ _ _ _ σ hσ d J c hc g => ratU_iff σ hσ d J c hc g

end GlobalTheory.RatCorr
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling

namespace GlobalTheory.UnipSpMass

theorem exists_haar_unipSp_mass_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (B : Base F E) (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s →
    ∀ (j : ℕ) (Y : Matrix (Fin d) (Fin j) E), 1 ≤ j → Function.Injective Y.mulVec →
      (∀ k l, form σ W.J (fun a => Y a k) (fun a => Y a l) = 0) →
      ∃ (ν : Measure (GlobalTheory.ThKLiftCusp.unipSp σ W Y)) (𝓕 : Set (GlobalTheory.ThKLiftCusp.unipSp σ W Y)), ν.IsHaarMeasure ∧
        IsFundamentalDomain ((ratU σ W.J).subgroupOf (GlobalTheory.ThKLiftCusp.unipSp σ W Y)) 𝓕 ν ∧ ν 𝓕 = 1 := by
  intro F E _ _ _ _ _ σ hcm B d r s W hW j Y _ hY hiso
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hcm
  obtain ⟨c, hc, hcs⟩ := GlobalTheory.CMImag.exists_imag_ne_zero F E σ hcm
  have hJ : IsHermND σ (c • W.J.map σ) := GlobalTheory.ThK.SqIntHerm.isHermND_smul_map F E σ B d W r s hW c hc hcs
  have hC : GlobalTheory.UAut.IsIsoCols σ (c • W.J.map σ) Y := by
    refine ⟨Matrix.mulVec_injective_iff.1 hY, ?_⟩
    ext k l
    have h := congrArg (fun x => c * σ x) (hiso k l)
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, map_zero, mul_zero] at h
    rw [Matrix.zero_apply, ← h]
    simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.zero_apply, Finset.sum_mul, Finset.mul_sum, RingHom.coe_coe]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring
  have hmem := GlobalTheory.UnipMatch.mem_unipSp_iff F E σ hσ B d W r s hW c hc j Y hiso
  have hrat := GlobalTheory.RatCorr.ratU_iff_ratPts F E σ hσ d W.J c hc
  set e := GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc with he
  obtain ⟨hTG, hLC, hSC, hT2⟩ := GlobalTheory.UnipMass.topUA σ W.J
  haveI := hTG
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI : LocallyCompactSpace (GlobalTheory.SiegelSet.unipRad σ (c • W.J.map σ) Y) :=
    GlobalTheory.UAut.locallyCompact_unipRad hcm hJ hC
  obtain ⟨K', hK', hcov'⟩ := GlobalTheory.UAut.cocompact_unipRad hcm hJ hC
  have hec : Continuous e := continuous_subtype_val.subtype_mk _
  have hes : Continuous e.symm := continuous_subtype_val.subtype_mk _
  let eH : GlobalTheory.ThKLiftCusp.unipSp σ W Y ≃ₜ GlobalTheory.SiegelSet.unipRad σ (c • W.J.map σ) Y :=
    { toFun := fun x => ⟨e x, (hmem x).1 x.2⟩
      invFun := fun y => ⟨e.symm y, (hmem _).2 (by rw [e.apply_symm_apply]; exact y.2)⟩
      left_inv := fun x => by ext; simp
      right_inv := fun y => by ext; simp
      continuous_toFun := (hec.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (hes.comp continuous_subtype_val).subtype_mk _ }
  haveI : LocallyCompactSpace (GlobalTheory.ThKLiftCusp.unipSp σ W Y) := eH.isClosedEmbedding.locallyCompactSpace
  haveI := GlobalTheory.UnipMass.countable_ratU' σ W.J (GlobalTheory.ThKLiftCusp.unipSp σ W Y)
  haveI := GlobalTheory.T.discrete_rational_points_subgroup F E σ d W.J (GlobalTheory.ThKLiftCusp.unipSp σ W Y)
  refine GlobalTheory.T.cocompact_lattice_unit_covolume _ _ (eH ⁻¹' K') (eH.isCompact_preimage.2 hK') fun g => ?_
  obtain ⟨γ', hγ', hK⟩ := hcov' (eH g)
  refine ⟨⟨eH.symm γ', ?_⟩, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    show e.symm (γ' : _) ∈ ratU σ W.J
    rw [hrat, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_subgroupOf.1 hγ'
  · show eH (eH.symm γ' * g) ∈ K'
    have : eH (eH.symm γ' * g) = γ' * eH g := by
      apply Subtype.ext
      show e (e.symm (γ' : _) * (g : _)) = (γ' : _) * e g
      rw [map_mul, MulEquiv.apply_symm_apply]
    rw [this]
    exact hK

end GlobalTheory.UnipSpMass
end
