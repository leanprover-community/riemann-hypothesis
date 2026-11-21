import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.CayleyPhaseQuadratic
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.GaussSumEighthPower
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.UnitaryEighthOf
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.RelIndexEqAbsDetReal
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.ExtensionActionPermutesPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.GaloisDescentSubspaces
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.ExtensionInterSubspace
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.ExtensionFiltrationStable
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.CayleyGaussianIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.DiagonalIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.KerPNonzero
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock

section
noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory
open scoped Pointwise

namespace Formalism.L2.Th1.H

theorem hasSum_unfold {V E : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure V) [μ.IsAddLeftInvariant]
    (G : AddSubgroup V) [Countable G] {D : Set V} (hD : IsAddFundamentalDomain G D μ) {f : V → E}
    (hf : Integrable f μ) :
    HasSum (fun y : G => ∫ z in D, f (z - (y : V)) ∂μ) (∫ z, f z ∂μ) := by
  have h1 : HasSum (fun g : G => ∫ x in g +ᵥ D, f x ∂μ) (∫ z, f z ∂μ) := by
    have h := hasSum_integral_measure (μ := fun g : G => μ.restrict (g +ᵥ D)) (f := f)
      (by rwa [hD.sum_restrict])
    rwa [hD.sum_restrict] at h
  have h2 : ∀ g : G, ∫ x in g +ᵥ D, f x ∂μ = ∫ x in D, f (x - ((-g : G) : V)) ∂μ := by
    intro g
    rw [← Set.image_vadd,
      (measurePreserving_vadd g μ).setIntegral_image_emb (measurableEmbedding_const_vadd g) f D]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [AddSubgroup.vadd_def, add_comm]
  simp_rw [h2] at h1
  exact (Equiv.neg G).hasSum_iff.mp h1

section Reps

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def repMap {Λ Λ' : AddSubgroup V} (Ae : V ≃ₗ[ℂ] V) {S : Finset V}
    (hle : imgLat (Ae : V →ₗ[ℂ] V) Λ' ≤ Λ) (hS : IsReps (imgLat (Ae : V →ₗ[ℂ] V) Λ') Λ S)
    (p : S × Λ') : Λ :=
  ⟨(p.1 : V) + Ae (p.2 : V), Λ.add_mem (hS.1 _ p.1.2) (hle ⟨p.2, p.2.2, rfl⟩)⟩

theorem repMap_bijective {Λ Λ' : AddSubgroup V} (Ae : V ≃ₗ[ℂ] V) {S : Finset V}
    (hle : imgLat (Ae : V →ₗ[ℂ] V) Λ' ≤ Λ) (hS : IsReps (imgLat (Ae : V →ₗ[ℂ] V) Λ') Λ S) :
    Function.Bijective (repMap Ae hle hS) := by
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨y, hy⟩⟩ ⟨⟨s', hs'⟩, ⟨y', hy'⟩⟩ h
    have h0 : s + Ae y = s' + Ae y' := congrArg Subtype.val h
    have h1 : s - s' = Ae (y' - y) := by
      rw [map_sub, sub_eq_sub_iff_add_eq_add, h0, add_comm]
    have h2 : s = s' := hS.2.1 s hs s' hs' (h1 ▸ ⟨y' - y, Λ'.sub_mem hy' hy, rfl⟩)
    subst h2
    have h3 : y = y' := Ae.injective (add_left_cancel h0)
    subst h3
    rfl
  · rintro ⟨x, hx⟩
    obtain ⟨s, hs, y, hy, hxy⟩ := hS.2.2 x hx
    refine ⟨(⟨s, hs⟩, ⟨y, hy⟩), Subtype.ext ?_⟩
    have h : Ae y = x - s := hxy
    change s + Ae y = x
    rw [h]
    abel

end Reps

theorem unfoldingIntegral : UnfoldIntegral := by
  intro V _ _ _ _ _ μ _ H Λ α δ Ae hL hU D' hD' _ S hS
  classical
  set Λ' : AddSubgroup V := Λ ⊓ imgLat (δ : V →ₗ[ℂ] V) Λ with hΛ'
  have : ProperSpace V := FiniteDimensional.proper ℂ V
  have : DiscreteTopology Λ := hL.1
  have hc : Countable Λ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have hc' : Countable Λ' := (AddSubgroup.inclusion_injective (inf_le_left : Λ' ≤ Λ)).countable
  obtain ⟨hT, -⟩ := kernelTermShift V H hU.herm α δ Ae hU.isom hU.cay
  have hgq : Integrable (gq H Ae) μ := (cayleyGaussianIntegral V μ H hU.herm hU.pos δ Ae hU.isom hU.cay).1
  have hle : imgLat (Ae : V →ₗ[ℂ] V) Λ' ≤ Λ := ud_latA_le hU
  let e : S × Λ' ≃ Λ := Equiv.ofBijective _ (repMap_bijective Ae hle hS)
  let f : V → V → ℂ := fun s z => gq H Ae (z - Ae.symm s)
  have hf : ∀ s, Integrable (f s) μ := fun s => hgq.comp_sub_right _
  have hfi : ∀ s, ∫ z, f s z ∂μ = ∫ z, gq H Ae z ∂μ := fun s =>
    integral_sub_right_eq_self (μ := μ) (gq H Ae) (Ae.symm s)
  have hFe : ∀ (p : S × Λ') z,
      termT H α δ ((e p : Λ) : V) z = phiC H α Ae p.1 * f p.1 (z - (p.2 : V)) := by
    intro p z
    rw [hT]
    have h1 : ((e p : Λ) : V) = (p.1 : V) + Ae (p.2 : V) := rfl
    rw [h1, ud_phi_wd hU (hS.1 _ p.1.2) (show Ae (p.2 : V) ∈ latA Λ δ Ae from ⟨p.2, p.2.2, rfl⟩)]
    simp only [f, map_add, LinearEquiv.symm_apply_apply]
    congr 2
    abel
  have hint : ∀ x : Λ, Integrable (fun z => termT H α δ (x : V) z) (μ.restrict D') := by
    intro x
    simp_rw [hT]
    exact ((hgq.comp_sub_right _).const_mul _).restrict
  have hsumn : Summable fun x : Λ => ∫ z in D', ‖termT H α δ (x : V) z‖ ∂μ := by
    have key : Summable fun p : S × Λ' => ∫ z in D', ‖termT H α δ ((e p : Λ) : V) z‖ ∂μ := by
      refine (summable_prod_of_nonneg (fun p => integral_nonneg fun z => norm_nonneg _)).mpr
        ⟨fun s => ?_, Summable.of_finite⟩
      have h := (hasSum_unfold μ Λ' hD' (hf s).norm).summable.mul_left ‖phiC H α Ae s‖
      refine h.congr fun y => ?_
      simp only [hFe, norm_mul, integral_const_mul]
    exact e.summable_iff.mp key
  have hmain := hasSum_integral_of_summable_integral_norm hint hsumn
  have hker : ∀ z, kerP H α Λ (δ.symm z) z * (wt H z : ℂ) = ∑' x : Λ, termT H α δ (x : V) z := by
    intro z
    simp only [kerP, termT, tsum_mul_right]
  simp_rw [hker]
  have hs2 : Summable fun c : S × Λ' => ∫ a in D', termT H α δ ((e c : Λ) : V) a ∂μ :=
    e.summable_iff.mpr hmain.summable
  rw [← hmain.tsum_eq, ← e.tsum_eq, hs2.tsum_prod, tsum_fintype,
    Finset.sum_mul, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp_rw [hFe, integral_const_mul]
  rw [tsum_mul_left, (hasSum_unfold μ Λ' hD' (hf s)).tsum_eq, hfi]

end Formalism.L2.Th1.H
end
end

section
noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Formalism.L2.Th1.H

namespace UC

theorem kerPTh : KerPTh := KerPTh_of exp_series_entire latticeGaussSummable formNormEquiv
theorem kerPNonzero : KerPNonzero := KerPNonzero_of diagonalIntegral
theorem gaussIntegrable : GaussIntegrable := GaussIntegrable_of formNormEquiv
theorem unitaryGauss : UnitaryGauss := UnitaryGauss_of gaussSumEighthPower

section Line

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] {H : Sesq V}
  {Λ : AddSubgroup V} {α : V → ℂ} {δ Ae : V ≃ₗ[ℂ] V}

theorem th_congr (α' : V → ℂ) (h : ∀ x ∈ Λ, α' x = α x) {F : V → ℂ} (hF : F ∈ Th H α Λ) :
    F ∈ Th H α' Λ :=
  ⟨hF.1, fun x hx z => by rw [h x hx]; exact hF.2 x hx z⟩

theorem pull_mem (hU : UnitaryData H Λ α δ Ae) {θ : V → ℂ} (hθ : θ ∈ Th H α Λ) :
    pullInv δ θ ∈ Th H α (imgLat (δ : V →ₗ[ℂ] V) Λ) := by
  rw [thIsom V V H H δ hU.isom Λ α (pullInv δ θ)]
  have e : (fun v => pullInv δ θ (δ v)) = θ := by
    funext v
    simp [pullInv]
  rw [e]
  exact th_congr _ hU.inv hθ

theorem exists_const (hL : IsLat Λ) (hU : UnitaryData H Λ α δ Ae) (hLine : AtMostLine H α Λ) :
    ∃ c : ℂ, ∀ θ ∈ Th H α Λ, pullInv δ θ = c • inter H α Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) θ := by
  obtain ⟨w, z, hwz⟩ := kerPNonzero V H Λ α hU.herm hU.pos hL hU.selfDual hU.semi
  obtain ⟨θ₀, hdef⟩ : ∃ θ₀ : V → ℂ, θ₀ = fun z => kerP H α Λ z w := ⟨_, rfl⟩
  have hθ₀ : θ₀ ∈ Th H α Λ := by
    rw [hdef]
    exact (kerPTh V H Λ α hU.herm hU.pos hL hU.semi w).2
  have hne : θ₀ ≠ 0 := by
    intro h
    apply hwz
    have := congrFun h z
    rw [hdef] at this
    exact this
  obtain ⟨-, hline2⟩ := lineTransport V H hU.herm Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) α hU.selfDual
    (Cay.selfDual_img H Λ δ hU.isom hU.selfDual) hU.semi hU.semi' hU.idx₂ hU.idx₁ θ₀ hθ₀ hne
    (hLine θ₀ hθ₀ hne)
  obtain ⟨c, hc⟩ := hline2 _ (pull_mem hU hθ₀)
  refine ⟨c, fun θ hθ => ?_⟩
  obtain ⟨a, rfl⟩ := hLine θ₀ hθ₀ hne θ hθ
  rw [Inv.inter_smul, smul_comm, ← hc]
  rfl

theorem latA_idx_ne (hL : IsLat Λ) (hU : UnitaryData H Λ α δ Ae) : relIdx (latA Λ δ Ae) Λ ≠ 0 := by
  obtain ⟨-, hidx⟩ := unitary_index V H Λ α δ Ae hL hU
  intro h0
  rw [h0] at hidx
  have hdt0 : LinearMap.det (Ae : V →ₗ[ℂ] V) ≠ 0 := (LinearEquiv.isUnit_det' Ae).ne_zero
  have h1 : (relIdx (imgLat (δ : V →ₗ[ℂ] V) Λ) Λ : ℝ) ≠ 0 := by exact_mod_cast hU.idx₁
  have h2 : ‖LinearMap.det (Ae : V →ₗ[ℂ] V)‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hdt0)
  exact mul_ne_zero h1 h2 (by simpa using hidx.symm)

theorem sqrt_card (hL : IsLat Λ) (hU : UnitaryData H Λ α δ Ae) {S : Finset V}
    (hS : IsReps (latA Λ δ Ae) Λ S) :
    Real.sqrt S.card
      = Real.sqrt (relIdx (imgLat (δ : V →ₗ[ℂ] V) Λ) Λ) * ‖LinearMap.det (Ae : V →ₗ[ℂ] V)‖ := by
  obtain ⟨-, hidx⟩ := unitary_index V H Λ α δ Ae hL hU
  rw [(repsExist V _ _ (latA_idx_ne hL hU)).2 S hS, hidx, Real.sqrt_mul (Nat.cast_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]

end Line

theorem norm_sum_phi {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V} {Λ : AddSubgroup V} {α : V → ℂ}
    {δ Ae : V ≃ₗ[ℂ] V} (hU : UnitaryData H Λ α δ Ae) {S : Finset V} (hS : IsReps (latA Λ δ Ae) Λ S) :
    ‖∑ x ∈ S, phiC H α Ae x‖ = Real.sqrt S.card := by
  have h8 := unitaryGauss V H Λ α δ Ae hU S hS
  have h1 : ‖gaussC H α Ae S‖ = 1 := by
    have := congrArg norm h8
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp this
  have hs : Real.sqrt S.card ≠ 0 := by
    intro h0
    rw [gaussC, h0] at h1
    simp at h1
  rw [gaussC, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)] at h1
  field_simp at h1
  exact h1

theorem diag_integrable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V) (Λ : AddSubgroup V)
    (α : V → ℂ) (hH : IsHerm H) (hP : IsPosDef H) (hL : IsLat Λ) (hα : IsSemiChar H Λ α) (D' : Set V)
    (hb : Bornology.IsBounded D') (y : V) (hy : α y = 1 ∨ α y = -1) :
    Integrable (fun z => α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ)) (μ.restrict D') := by
  obtain ⟨c₀, C₀, hc₀, -, hform⟩ := formNormEquiv V H hH hP
  obtain ⟨u, hu, hule⟩ := latticeGaussSummable V Λ hL (Real.pi / 2 * c₀) ‖y‖ (by positivity)
  have hfin : μ D' < ⊤ := hb.measure_lt_top
  have : IsFiniteMeasure (μ.restrict D') := ⟨by simpa using hfin⟩
  have hbound : ∀ x : Λ, ‖diagCoef H α y (x : V)‖ ≤ u x := by
    intro x
    rw [norm_diagCoef H α y x hy (hα.1 x x.2)]
    refine le_trans ?_ (hule x (-y) (by rw [norm_neg]))
    apply Real.exp_le_exp.mpr
    have h := (hform (y + (x : V))).1
    have e : (x : V) - -y = y + (x : V) := by abel
    rw [e]
    have hpi : 0 < Real.pi / 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h hpi.le]
  have hn : ∀ (x : Λ) (z : V), ‖diagCoef H α y (x : V) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H (y + (x : V)) z : ℂ))‖ ≤ u x := by
    intro x z
    rw [norm_mul, norm_char, mul_one]
    exact hbound x
  have hcont : Continuous fun z => ∑' x : Λ, diagCoef H α y (x : V) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H (y + (x : V)) z : ℂ)) := by
    refine continuous_tsum (fun x => ?_) hu hn
    refine continuous_const.mul (Complex.continuous_exp.comp ?_)
    exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_altE H hH _))
  have e : (fun z => α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ))
      = fun z => ∑' x : Λ, diagCoef H α y (x : V) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H (y + (x : V)) z : ℂ)) :=
    funext fun z => diag_expansion H hH α Λ y z
  rw [e]
  refine Integrable.of_bound hcont.aestronglyMeasurable (∑' x, u x)
    (Filter.Eventually.of_forall fun z => ?_)
  exact tsum_of_norm_bounded hu.hasSum (fun x => hn x z)

theorem const_value {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] {H : Sesq V} {Λ : AddSubgroup V}
    {α : V → ℂ} {δ Ae : V ≃ₗ[ℂ] V} (hL : IsLat Λ) (hU : UnitaryData H Λ α δ Ae)
    (hLine : AtMostLine H α Λ) {D' : Set V}
    (hD' : IsAddFundamentalDomain (Λ ⊓ imgLat (δ : V →ₗ[ℂ] V) Λ : AddSubgroup V) D' μ)
    (hb : Bornology.IsBounded D') {S : Finset V} (hS : IsReps (latA Λ δ Ae) Λ S) :
    ∃ c : ℂ, (∀ θ ∈ Th H α Λ, pullInv δ θ = c • inter H α Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) θ) ∧
      c * ((Real.sqrt (relIdx Λ (imgLat (δ : V →ₗ[ℂ] V) Λ)) : ℝ) : ℂ)⁻¹ * ((μ D').toReal : ℂ)
        = (∑ x ∈ S, phiC H α Ae x) *
            (((∫ z, wt H z ∂μ : ℝ) : ℂ) / LinearMap.det (Ae : V →ₗ[ℂ] V)) := by
  classical
  obtain ⟨c, hc⟩ := exists_const hL hU hLine
  refine ⟨c, hc, ?_⟩
  obtain ⟨S₂, hS₂⟩ := (repsExist V Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) hU.idx₂).1
  have hsd2 := Cay.selfDual_img H Λ δ hU.isom hU.selfDual
  obtain ⟨r, hr⟩ : ∃ r : ℂ, r = ((Real.sqrt (relIdx Λ (imgLat (δ : V →ₗ[ℂ] V) Λ)) : ℝ) : ℂ)⁻¹ := ⟨_, rfl⟩
  rw [← hr]
  have hpt : ∀ z, kerP H α Λ (δ.symm z) z * (wt H z : ℂ)
      = c * r * ∑ y ∈ S₂, α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ) := by
    intro z
    have hm := (kerPTh V H Λ α hU.herm hU.pos hL hU.semi z).2
    have h1 := congrFun (hc _ hm) z
    have h2 := interReps V H hU.herm Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) α hU.semi' _ hm.2 S₂ hS₂ z
    have h3 : pullInv δ (fun v => kerP H α Λ v z) z = kerP H α Λ (δ.symm z) z := rfl
    rw [h3, Pi.smul_apply, h2, ← hr, sumU, smul_eq_mul] at h1
    rw [h1, ← Finset.sum_mul]
    ring
  have hint : ∀ y ∈ S₂, Integrable
      (fun z => α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ)) (μ.restrict D') :=
    fun y hy => diag_integrable μ H Λ α hU.herm hU.pos hL hU.semi D' hb y (hU.semi'.1 y (hS₂.1 y hy))
  have hleft := unfoldingIntegral V μ H Λ α δ Ae hL hU D' hD' hb S hS
  rw [(cayleyGaussianIntegral V μ H hU.herm hU.pos δ Ae hU.isom hU.cay).2] at hleft
  rw [← hleft]
  simp_rw [hpt]
  rw [integral_const_mul, integral_finsetSum _ hint]
  have hdiag := diagonalIntegral V μ H Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) α hU.herm hU.pos hL hU.selfDual hsd2
    hU.semi hU.semi' D' hD' hb
  obtain ⟨y₀, hy₀, hy₀Λ, hsum⟩ := Inv.sum_reps hS₂
    (fun y => ∫ z in D', α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ) ∂μ)
    (fun y hy hyΛ => by
      have := hdiag y (hS₂.1 y hy)
      rw [if_neg hyΛ] at this
      exact this)
  rw [hsum]
  have := hdiag y₀ (hS₂.1 y₀ hy₀)
  rw [if_pos hy₀Λ] at this
  rw [this]

end UC

end Formalism.L2.Th1.H
end
end

section
noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Formalism.L2.Th1.H

namespace UC

section Neg

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem img_neg (Λ : AddSubgroup V) : imgLat ((LinearEquiv.neg ℂ : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) Λ = Λ := by
  ext x
  simp only [imgLat, AddSubgroup.mem_map, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
    LinearEquiv.neg_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact Λ.neg_mem hy
  · intro hx
    exact ⟨-x, Λ.neg_mem hx, neg_neg x⟩

theorem relIdx_self (Λ : AddSubgroup V) : relIdx Λ Λ = 1 := AddSubgroup.relIndex_self Λ

theorem data_neg {H : Sesq V} {Λ : AddSubgroup V} {α : V → ℂ} (hH : IsHerm H) (hP : IsPosDef H)
    (hsd : IsSelfDual H Λ) (hα : IsSemiChar H Λ α) :
    UnitaryData H Λ α (LinearEquiv.neg ℂ) (LinearEquiv.smulOfNeZero ℂ V 2 two_ne_zero) where
  herm := hH
  pos := hP
  selfDual := hsd
  semi := hα
  isom := by
    intro x y
    simp
  semi' := by rw [img_neg]; exact hα
  inv := fun x hx => (semiCharBasic V H hH Λ α hα).2.1 x hx
  idx₁ := by rw [img_neg, relIdx_self]; exact one_ne_zero
  idx₂ := by rw [img_neg, relIdx_self]; exact one_ne_zero
  cay := by
    intro x
    simp [two_smul]

theorem inter_self {H : Sesq V} {Λ : AddSubgroup V} {α : V → ℂ} (hH : IsHerm H) (hα : IsSemiChar H Λ α)
    {F : V → ℂ} (hF : F ∈ fixedBy H α Λ) : inter H α Λ Λ F = F := by
  funext z
  have hS : IsReps Λ Λ ({0} : Finset V) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_singleton.mp hx]
      exact Λ.zero_mem
    · intro x hx y hy _
      rw [Finset.mem_singleton.mp hx, Finset.mem_singleton.mp hy]
    · intro y hy
      exact ⟨0, Finset.mem_singleton_self 0, by simpa using hy⟩
  rw [interReps V H hH Λ Λ α hα F hF {0} hS z, relIdx_self, sumU, Finset.sum_singleton,
    hF 0 Λ.zero_mem z]
  simp

end Neg

end UC

theorem SelfDualCovolume_proof : SelfDualCovolume := by
  intro V _ _ _ _ _ μ _ H Λ α hH hP hL hsd hα hLine D hD hb
  have hU := UC.data_neg hH hP hsd hα
  obtain ⟨S, hS⟩ := (repsExist V _ _ (UC.latA_idx_ne hL hU)).1
  have hD' : IsAddFundamentalDomain
      (Λ ⊓ imgLat ((LinearEquiv.neg ℂ : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) Λ : AddSubgroup V) D μ := by
    rw [UC.img_neg, inf_idem]
    exact hD
  obtain ⟨c, hc, hval⟩ := UC.const_value μ hL hU hLine hD' hb hS
  have hcard := UC.sqrt_card hL hU hS
  have hphi := UC.norm_sum_phi hU hS
  rw [UC.img_neg, UC.relIdx_self] at hval hcard
  rw [UC.img_neg] at hc

  obtain ⟨w, z, hwz⟩ := UC.kerPNonzero V H Λ α hH hP hL hsd hα
  have hm := (UC.kerPTh V H Λ α hH hP hL hα w).2
  have hc' := hc _ hm
  rw [UC.inter_self hH hα hm.2] at hc'
  have h1 : kerP H α Λ (-z) w = c * kerP H α Λ z w := by
    have := congrFun hc' z
    simpa [pullInv] using this
  have h2 : kerP H α Λ z w = c * kerP H α Λ (-z) w := by
    have := congrFun hc' (-z)
    simpa [pullInv] using this
  have hc2 : c * c = 1 := by
    rw [h1, ← mul_assoc] at h2
    exact (mul_right_cancel₀ hwz (by rw [one_mul]; exact h2)).symm
  have hcn : ‖c‖ = 1 := by
    have h := congrArg norm hc2
    rw [norm_mul, norm_one] at h
    nlinarith [norm_nonneg c]
  have hγ : 0 < ∫ z, wt H z ∂μ := (UC.gaussIntegrable V μ H hH hP Real.pi Real.pi_pos).2
  have hdt0 : LinearMap.det ((LinearEquiv.smulOfNeZero ℂ V 2 two_ne_zero : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) ≠ 0 :=
    (LinearEquiv.isUnit_det' _).ne_zero
  have hn := congrArg norm hval
  rw [norm_mul, norm_mul, norm_mul, norm_div, hcn, hphi, hcard, Complex.norm_real, Complex.norm_real,
    norm_inv, Complex.norm_real] at hn
  simp only [Nat.cast_one, Real.sqrt_one, norm_one, inv_one, one_mul] at hn
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg, Real.norm_of_nonneg (le_of_lt hγ)] at hn
  rw [hn]
  have : ‖LinearMap.det ((LinearEquiv.smulOfNeZero ℂ V 2 two_ne_zero : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hdt0
  field_simp

theorem UnitaryConstant_proof : UnitaryConstant := by
  intro V _ _ _ H Λ α δ Ae hL hU hLine S hS θ hθ
  let _ : MeasurableSpace V := borel V
  have : BorelSpace V := ⟨rfl⟩
  let μ : Measure V := Measure.addHaar
  obtain ⟨D, hDf, hDb, hDpos, hsub⟩ := fundamentalDomainExists V μ Λ hL
  have hidx : relIdx (Λ ⊓ imgLat (δ : V →ₗ[ℂ] V) Λ) Λ = relIdx (imgLat (δ : V →ₗ[ℂ] V) Λ) Λ :=
    AddSubgroup.inf_relIndex_left _ _
  obtain ⟨D', hD'f, hD'b, hD'm⟩ := hsub (Λ ⊓ imgLat (δ : V →ₗ[ℂ] V) Λ) inf_le_left
    (by rw [hidx]; exact hU.idx₁)
  obtain ⟨c, hc, hval⟩ := UC.const_value μ hL hU hLine hD'f hD'b hS
  have hcov := SelfDualCovolume_proof V μ H Λ α hU.herm hU.pos hL hU.selfDual hU.semi hLine D hDf hDb
  have hcard := UC.sqrt_card hL hU hS
  have hie := indexEq V H hU.herm Λ (imgLat (δ : V →ₗ[ℂ] V) Λ) hU.selfDual
    (Cay.selfDual_img H Λ δ hU.isom hU.selfDual) hU.idx₂ hU.idx₁
  rw [hc θ hθ]
  congr 1
  rw [gaussC, hcard]
  rw [hD'm, hidx, hie, hcov] at hval
  rw [← hcov] at hval
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = (relIdx (imgLat (δ : V →ₗ[ℂ] V) Λ) Λ : ℝ) := ⟨_, rfl⟩
  rw [← hn] at hval ⊢
  have hnpos : 0 < n := by
    rw [hn]
    exact_mod_cast Nat.pos_of_ne_zero hU.idx₁
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt n := ⟨_, rfl⟩
  have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hnpos
  have hss : n = s * s := by rw [hs]; exact (Real.mul_self_sqrt hnpos.le).symm
  rw [← hs] at hval ⊢
  rw [hss] at hval
  have hdt0 : LinearMap.det (Ae : V →ₗ[ℂ] V) ≠ 0 := (LinearEquiv.isUnit_det' Ae).ne_zero
  have hdn : ((‖LinearMap.det (Ae : V →ₗ[ℂ] V)‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hdt0
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hspos.ne'
  have hDc : (((μ D).toReal : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hDpos.ne'
  push_cast at hval ⊢
  field_simp at hval ⊢
  linear_combination hval

theorem UnitaryEighth_proof : UnitaryEighth :=
  UnitaryEighth_of UnitaryConstant_proof (UnitaryGauss_of gaussSumEighthPower) unitary_index

end Formalism.L2.Th1.H
end
end
