import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitDecay
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterAtUniformizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterOfIdeleClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeValueNotFiniteOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPrimeDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSubmoduleFirstFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSubmoduleSecondFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSpace

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay

namespace GlobalTheory.ThKSoCont

variable {F : Type} [Field F] [NumberField F]

def mkA (a : mixedEmbedding.mixedSpace F) (b : Af F) : AF F :=
  (Prod.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a) b : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

theorem evI_mkA (a : mixedEmbedding.mixedSpace F) (b : Af F) : evI F (mkA a b) = a := by
  simp [evI, mkA]

theorem pureA_add {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (a b : (κ → Af F) → ℂ) :
    pureA F f (a + b) = pureA F f a + pureA F f b := by
  funext x; simp [pureA, mul_add]

theorem pureA_smul {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (c : ℂ) (a : (κ → Af F) → ℂ) :
    pureA F f (c • a) = c • pureA F f a := by
  funext x; simp [pureA]; ring

theorem pureA_zero {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) : pureA F f (0 : (κ → Af F) → ℂ) = 0 := by
  funext x; simp [pureA]

theorem pureA_mkA {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (a : (κ → Af F) → ℂ)
    (y : κ → mixedEmbedding.mixedSpace F) (z : κ → Af F) : pureA F f a (fun i => mkA (y i) (z i)) = f y * a z := by
  simp only [pureA]
  congr 1
  congr 1
  funext i
  exact evI_mkA (y i) (z i)

theorem thetaSum_finset_sum {κ ι : Type} [Fintype κ] (s : Finset ι) (Φ : ι → (κ → AF F) → ℂ)
    (h : ∀ i ∈ s, Φ i ∈ schA F κ) : thetaSum F (∑ i ∈ s, Φ i) = ∑ i ∈ s, thetaSum F (Φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [thetaSum]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      thetaSum_add F (h a (Finset.mem_insert_self a s)) (Submodule.sum_mem _ fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

open scoped Classical in

theorem soCont (hP : KP) : SoCont := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair m φ f u hconv hSo hSoLim h
  have hB := GlobalTheory.T.theta_basic_properties hP.base F E σ B n d X W M χX χW om r s r' s' hPair
  have hU := soDecayUnif hP F E σ B n d X W M χX χW om r s r' s' hPair
  have hpres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d) :=
    hPair.weil.isUSplitting.pres
  haveI := hPair.good.haar
  have hfin : M.μ M.dom < ⊤ := GlobalTheory.UnitaryVol.measure_fundDom_lt_top hP.siegelSetUnitary hPair.base.cm
    (GlobalTheory.UnitaryVol.isHermND_map (GlobalTheory.SiegelSet.sigma_sigma hPair.base.cm) hPair.herm) hPair.good.dom
  haveI : IsFiniteMeasure (M.μ.restrict M.dom) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩

  let So := M.So B.ψ B.τ₁
  let T' : Submodule ℂ ((Fin n × Fin d → Af F) → ℂ) :=
    { carrier := {a | ∀ g : SInf F (Fin n × Fin d), pureA F g a ∈ So}
      add_mem' := fun ha hb g => by rw [pureA_add]; exact So.add_mem (ha g) (hb g)
      zero_mem' := fun g => by rw [pureA_zero]; exact So.zero_mem
      smul_mem' := fun c a ha g => by rw [pureA_smul]; exact So.smul_mem c (ha g) }
  let T := SB (Fin n × Fin d → Af F) ⊓ T'

  have hslice : ∀ Φ ∈ So, ∀ y : Fin n × Fin d → mixedEmbedding.mixedSpace F,
      (fun z : Fin n × Fin d → Af F => Φ (fun i => mkA (y i) (z i))) ∈ T' := by
    intro Φ hΦ y
    induction hΦ using Submodule.span_induction with
    | mem Φ hΦ =>
      obtain ⟨g, ψ, h1, h2, h3, rfl⟩ := hΦ
      let a : (Fin n × Fin d → Af F) → ℂ := fun z => ∏ᶠ v, ψ v fun i => evFin F v (mkA 0 (z i))
      have e1 : (fun z : Fin n × Fin d → Af F => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g ψ (fun i => mkA (y i) (z i))) = g y • a := by
        funext z
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul, a]
        congr 1
        congr 1
        funext i
        exact evI_mkA (y i) (z i)
      have e2 : ∀ g' : SInf F (Fin n × Fin d), pureA F g' a = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g' ψ := fun g' => by
        funext x
        rfl
      rw [e1]
      refine T'.smul_mem _ fun g' => ?_
      rw [e2]
      exact Submodule.subset_span ⟨g', ψ, h1, h2, h3, rfl⟩
    | zero =>
      have e0 : (fun z : Fin n × Fin d → Af F => (0 : (Fin n × Fin d → AF F) → ℂ) (fun i => mkA (y i) (z i))) = 0 := rfl
      rw [e0]
      exact T'.zero_mem
    | add Φ Ψ _ _ hΦ hΨ => exact T'.add_mem hΦ hΨ
    | smul c Φ _ hΦ => exact T'.smul_mem c hΦ

  obtain ⟨C, hC⟩ := Submodule.exists_isCompl T
  have hdec : ∀ j, ∃ t ∈ T, ∃ c ∈ C, t + c = φ j := fun j =>
    Submodule.mem_sup.1 (hC.sup_eq_top ▸ Submodule.mem_top)
  choose t htT c hcC htc using hdec
  have hcSB : ∀ j, c j ∈ SB (Fin n × Fin d → Af F) := fun j => by
    have : c j = φ j - t j := by rw [← htc j]; abel
    rw [this]; exact Submodule.sub_mem _ (hconv j).1 (htT j).1

  have hred : ∀ w : Fin m → SInf F (Fin n × Fin d), ∑ j, pureA F (w j) (φ j) ∈ So →
      ∑ j, pureA F (w j) (φ j) = ∑ j, pureA F (w j) (t j) := by
    intro w hw
    have e : ∑ j, pureA F (w j) (φ j) = ∑ j, pureA F (w j) (t j) + ∑ j, pureA F (w j) (c j) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [← pureA_add, htc j]
    have hΨ : ∑ j, pureA F (w j) (c j) ∈ So := by
      have : ∑ j, pureA F (w j) (c j) = ∑ j, pureA F (w j) (φ j) - ∑ j, pureA F (w j) (t j) := by
        rw [e]; abel
      rw [this]
      exact So.sub_mem hw (So.sum_mem fun j _ => (htT j).2 (w j))
    have h0 : ∀ y, ∑ j, w j y • c j = 0 := by
      intro y
      have h1 : ∑ j, w j y • c j ∈ T := by
        refine ⟨SB _ |>.sum_mem fun j _ => (SB _).smul_mem _ (hcSB j), ?_⟩
        have := hslice _ hΨ y
        have e' : (fun z : Fin n × Fin d → Af F => (∑ j, pureA F (w j) (c j)) (fun i => mkA (y i) (z i))) =
            ∑ j, w j y • c j := by
          funext z
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pureA_mkA]
        rwa [e'] at this
      have h2 : ∑ j, w j y • c j ∈ C := C.sum_mem fun j _ => C.smul_mem _ (hcC j)
      have := hC.inf_eq_bot ▸ (Submodule.mem_inf.2 ⟨h1, h2⟩)
      exact (Submodule.mem_bot ℂ).1 this
    rw [e, add_eq_left]
    funext x
    have := congrFun (h0 fun i => evI F (x i)) (fun i => (x i).2)
    simpa [pureA, Finset.sum_apply, evI] using this

  have hmem : ∀ (a : (Fin n × Fin d → Af F) → ℂ), a ∈ SB (Fin n × Fin d → Af F) → ∀ g : SInf F (Fin n × Fin d),
      pureA F g a ∈ schA F (Fin n × Fin d) := fun a ha g => Submodule.subset_span ⟨g, a, ha, rfl⟩
  have hmeas : ∀ Φ ∈ schA F (Fin n × Fin d),
      AEStronglyMeasurable (fun x => theta om Φ x h) (M.μ.restrict M.dom) := by
    intro Φ hΦ
    haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
    exact ((hB.1 Φ hΦ).1.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  have hbd : ∀ a ∈ T, ∃ (C0 : ℝ) (k0 : ℕ), 0 ≤ C0 ∧ ∀ (g : SInf F (Fin n × Fin d)) x,
      ‖theta om (pureA F g a) x h‖ ≤ C0 * semK (Fin n × Fin d) k0 g * (ht h : ℝ) ^ k0 := by
    intro a ha
    obtain ⟨C0, k0, hC0⟩ := hU a ha.1 ha.2 0
    refine ⟨max C0 0, k0, le_max_right _ _, fun g x => ?_⟩
    have := hC0 g x h
    rw [pow_zero, mul_one] at this
    refine this.trans ?_
    gcongr
    exact le_max_left _ _
  have hint : ∀ a ∈ T, ∀ g : SInf F (Fin n × Fin d),
      Integrable (fun x => theta om (pureA F g a) x h) (M.μ.restrict M.dom) := by
    intro a ha g
    obtain ⟨C0, k0, -, hC0⟩ := hbd a ha
    exact Integrable.mono' (integrable_const (C0 * semK (Fin n × Fin d) k0 g * (ht h : ℝ) ^ k0))
      (hmeas _ (hmem a ha.1 g)) (ae_of_all _ fun x => hC0 g x)
  have hcont : ∀ a ∈ T, ∀ (v : ℕ → SInf F (Fin n × Fin d)) (g0 : SInf F (Fin n × Fin d)), Tendsto v atTop (𝓝 g0) →
      Tendsto (fun k => M.I om (pureA F (v k) a) h) atTop (𝓝 (M.I om (pureA F g0 a) h)) := by
    intro a ha v g0 hv
    obtain ⟨C0, k0, hC0p, hC0⟩ := hbd a ha
    have hsem : ∀ᶠ k in atTop, semK (Fin n × Fin d) k0 (v k) ≤ semK (Fin n × Fin d) k0 g0 + 1 := by
      have h1 := ((schwartz_withSeminorms ℂ _ ℂ).tendsto_nhds' v g0).1 hv
        (Finset.Iic (k0, k0)) 1 one_pos
      filter_upwards [h1] with k hk
      calc semK (Fin n × Fin d) k0 (v k) = semK (Fin n × Fin d) k0 ((v k - g0) + g0) := by rw [sub_add_cancel]
        _ ≤ semK (Fin n × Fin d) k0 (v k - g0) + semK (Fin n × Fin d) k0 g0 := map_add_le_add _ _ _
        _ ≤ semK (Fin n × Fin d) k0 g0 + 1 := by
          have : semK (Fin n × Fin d) k0 (v k - g0) < 1 := hk
          linarith
    simp only [Model.I]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun _ => C0 * (semK (Fin n × Fin d) k0 g0 + 1) * (ht h : ℝ) ^ k0)
      (Eventually.of_forall fun k => hmeas _ (hmem a ha.1 (v k))) ?_ (integrable_const _) ?_
    · filter_upwards [hsem] with k hk
      refine ae_of_all _ fun x => (hC0 (v k) x).trans ?_
      gcongr
    · exact ae_of_all _ fun x => ((hB.2 a ha.1 x h).tendsto g0).comp hv

  have hI : ∀ w : Fin m → SInf F (Fin n × Fin d), ∑ j, pureA F (w j) (φ j) ∈ So →
      M.I om (∑ j, pureA F (w j) (φ j)) h = ∑ j, M.I om (pureA F (w j) (t j)) h := by
    intro w hw
    rw [hred w hw]
    simp only [Model.I]
    rw [← integral_finset_sum _ fun j _ => hint (t j) (htT j) (w j)]
    congr 1
    funext x
    simp only [theta]
    rw [map_sum]
    exact thetaSum_finset_sum _ _ fun j _ => hpres _ _ (hmem _ (htT j).1 (w j))
  rw [hI f hSoLim]
  refine Tendsto.congr (fun k => (hI (u k) (hSo k)).symm) ?_
  exact tendsto_finset_sum _ fun j _ => hcont (t j) (htT j) (fun k => u k j) (f j) (hconv j).2

end GlobalTheory.ThKSoCont
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_orbit_continuous : GlobalTheory.ThK.KP → GlobalTheory.ThK.SoCont := by
  first | exact @GlobalTheory.ThKSoCont.soCont | exact GlobalTheory.ThKSoCont.soCont | (intros; apply GlobalTheory.ThKSoCont.soCont <;> assumption)
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_character_at_uniformizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : Chr F E) (v : Pl F) (t : E →ₐ[F] Fv F v), UnrAt χ (splitPrime t) → chrW χ t (unifAt v) = val χ (splitPrime t) := by
  first | exact @GlobalTheory.ChrWUnif.chrW_unifAt | exact GlobalTheory.ChrWUnif.chrW_unifAt | (intros; apply GlobalTheory.ChrWUnif.chrW_unifAt <;> assumption)
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_character_of_idele_class : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ χ : Chr F E, IsHecke F E χ → ∃ H : Formalism.L2.Host.HChar E, (∀ (W : HeightOneSpectrum (𝓞 E)) (x : (W.adicCompletion E)ˣ), H.loc W x = locChar χ W x) ∧ ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (m : InfinitePlace F → ℤ), HasExp τ χ m → H.HasInf (fun w => (τ w).1) m := by
  first | exact @GlobalTheory.HeckeBridge.exists_hchar | exact GlobalTheory.HeckeBridge.exists_hchar | (intros; apply GlobalTheory.HeckeBridge.exists_hchar <;> assumption)
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_value_not_finite_order : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → IsGalois ℚ E → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (H : Formalism.L2.Host.HChar E) (n : InfinitePlace F → ℤ), H.HasInf (fun w => (τ w).1) n → (∀ w, n w ≠ 0) → ∀ (p : ℕ), p.Prime → ∀ W : HeightOneSpectrum (𝓞 E), Ideal.absNorm W.asIdeal = p → (p : 𝓞 E) ∉ W.asIdeal ^ 2 → ¬ IsOfFinOrder (H.val W) := by
  first | exact @GlobalTheory.CMSplitValue.not_isOfFinOrder_val | exact GlobalTheory.CMSplitValue.not_isOfFinOrder_val | (intros; apply GlobalTheory.CMSplitValue.not_isOfFinOrder_val <;> assumption)
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_prime_degree_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (W : HeightOneSpectrum (𝓞 E)), SplitsFully E (W.under (𝓞 F)) → ∃ p : ℕ, p.Prime ∧ Ideal.absNorm W.asIdeal = p ∧ (p : 𝓞 E) ∉ W.asIdeal ^ 2 := by
  first | exact @GlobalTheory.SplitFullyNorm.exists_prime_absNorm_eq_of_splitsFully | exact GlobalTheory.SplitFullyNorm.exists_prime_absNorm_eq_of_splitsFully | (intros; apply GlobalTheory.SplitFullyNorm.exists_prime_absNorm_eq_of_splitsFully <;> assumption)
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.NuGood

theorem not_root_of_unity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h v hv t k hk hpow
  have hW : splitPrime t ∉ above E (X.T : Set (Pl F)) := by
    intro hmem
    exact hv.1 (by simpa [above, splitPrime_under] using hmem)
  have hunr : UnrAt X.ν (splitPrime t) := by
    rw [Chars.ν, div_eq_mul_inv]
    exact (h.chars.unrα _ hW).mul (h.chars.unrβ _ hW).inv
  rw [GlobalTheory.T.unramified_character_at_uniformizer F E X.ν v t hunr] at hpow
  have hHecke : IsHecke F E X.ν := by
    refine ⟨?_, fun x => ?_⟩
    · exact (h.chars.heckeα.1.div' h.chars.heckeβ.1 :)
    · rw [Chars.ν, MonoidHom.div_apply, h.chars.heckeα.2 x, h.chars.heckeβ.2 x, div_one]
  obtain ⟨H, hloc, hinf⟩ := GlobalTheory.T.hecke_character_of_idele_class F E σ h.base.cm X.ν hHecke
  have hexp : HasExp B.emb X.ν (fun w => B.mα w - B.mβ w) := by
    intro z hz
    have h1 := h.chars.expα z hz
    have h2 := h.chars.expβ z hz
    show (((X.α z / X.β z : Circle)) : ℂ) = _
    rw [Circle.coe_div, h1, h2, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hne : piInf (B.emb w) z ≠ 0 := (z.isUnit.map (piInf (B.emb w))).ne_zero
    have hne' : piInf (B.emb w) z / (‖piInf (B.emb w) z‖ : ℂ) ≠ 0 :=
      div_ne_zero hne (by exact_mod_cast (norm_ne_zero_iff.2 hne))
    rw [zpow_sub₀ hne']
  have hval : val X.ν (splitPrime t) = H.val (splitPrime t) := (hloc _ _).symm
  obtain ⟨p, hp, hN, hsq⟩ := GlobalTheory.T.split_prime_degree_one F E (splitPrime t) (by rw [splitPrime_under]; exact hv.2)
  refine GlobalTheory.T.hecke_value_not_finite_order F E σ h.base.cm h.base.galois B.emb H _ (hinf _ _ hexp) (fun w => ?_) p hp _ hN hsq ?_
  · have := h.geo.kappa w
    omega
  · rw [← hval]
    exact isOfFinOrder_iff_zpow_eq_one.2 ⟨k, hk, hpow⟩

end GlobalTheory.NuGood
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_at_uniformizer_not_root_of_unity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) := by
  first | exact @GlobalTheory.NuGood.not_root_of_unity | exact GlobalTheory.NuGood.not_root_of_unity | (intros; apply GlobalTheory.NuGood.not_root_of_unity <;> assumption)
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.KCoinvGood

theorem augAt_le_SB {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (om : Rep σ Y W) (v : Pl F) : augAt om v ≤ SB _ :=
  Submodule.span_le.mpr fun _ ⟨_, _, _, hφ, _, hφ₁, _, e⟩ => e ▸ sub_mem hφ₁ hφ

theorem acts_zero {F : Type} [Field F] [NumberField F] {R κ : Type} [Zero R] [Fintype κ] (ev : AF F → R)
    (T : Module.End ℂ ((κ → AF F) → ℂ)) : Acts ev T 0 0 := fun r _ => by
  have e : tens ev (0 : (κ → R) → ℂ) r = 0 := funext fun x => by simp [tens]
  rw [e, map_zero]

theorem ker_eq_of {V P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup P] [Module ℂ P] [Nontrivial P]
    (S A : Submodule ℂ V) (p : V →ₗ[ℂ] P) (hA : A ≤ LinearMap.ker p) (honto : S.map p = ⊤)
    (h : S ⊓ LinearMap.ker p = A ∨ S ⊓ LinearMap.ker p = S) : ∀ φ ∈ S, p φ = 0 ↔ φ ∈ A := by
  rcases h with h | h
  · intro φ hφ
    refine ⟨fun h0 => h ▸ ⟨hφ, h0⟩, fun hm => hA hm⟩
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (0 : P)
    have : x ∈ S.map p := honto ▸ Submodule.mem_top
    obtain ⟨y, hy, rfl⟩ := this
    have hy' : y ∈ S ⊓ LinearMap.ker p := by rw [h]; exact hy
    exact hx hy'.2

theorem factor_of {V P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup P] [Module ℂ P]
    (S : Submodule ℂ V) (p : V →ₗ[ℂ] P) (l : V →ₗ[ℂ] ℂ) (honto : S.map p = ⊤) (hk : ∀ φ ∈ S, p φ = 0 → l φ = 0) :
    ∃ l₀ : P →ₗ[ℂ] ℂ, ∀ φ ∈ S, l φ = l₀ (p φ) := by
  set q := p.domRestrict S
  have hs : Function.Surjective q := by
    intro x
    have : x ∈ S.map p := honto ▸ Submodule.mem_top
    obtain ⟨y, hy, rfl⟩ := this
    exact ⟨⟨y, hy⟩, rfl⟩
  have hker : LinearMap.ker q ≤ LinearMap.ker (l.domRestrict S) := fun x hx => hk x.1 x.2 hx
  refine ⟨((LinearMap.ker q).liftQ (l.domRestrict S) hker).comp (q.quotKerEquivOfSurjective hs).symm.toLinearMap,
    fun φ hφ => ?_⟩
  have : (q.quotKerEquivOfSurjective hs).symm (p φ) = Submodule.Quotient.mk ⟨φ, hφ⟩ := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp [this]

theorem kCoinv (hP : GlobalTheory.FunPr.Hypotheses₂) : GlobalTheory.ThK.KCoinv := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hm
  have ht := hm.triple
  have hf := hm.fin
  refine ⟨fun v hv => ?_, GlobalTheory.T.weil_representation_preserves_space hP F E σ B a a' G X om om' ht⟩
  haveI := hf.nontriv v
  have hnr := GlobalTheory.T.character_at_uniformizer_not_root_of_unity F E σ B a a' G X om om' ht v hv
  have k1 : ∀ φ ∈ SB _, Rf.p v φ = 0 ↔ φ ∈ augAt om v :=
    ker_eq_of _ _ _ (hf.inv v) (hf.onto v) <|
      GlobalTheory.T.augmentation_submodule_first_factor hP F E σ B a a' G X om om' ht v hv hnr _ (le_inf (augAt_le_SB om v) (hf.inv v)) inf_le_left
        fun h hh φ hφ φ₁ hφ₁ hact => ⟨hφ₁, by
          have := hf.equiv v h hh φ hφ.1 0 (zero_mem _) φ₁ hφ₁ 0 (zero_mem _) hact (acts_zero _ _)
            (by rw [map_zero]; exact hφ.2)
          rw [map_zero] at this; exact this⟩
  have k2 : ∀ φ ∈ SB _, Rf.p' v φ = 0 ↔ φ ∈ augAt om' v :=
    ker_eq_of _ _ _ (hf.inv' v) (hf.onto' v) <|
      GlobalTheory.T.augmentation_submodule_second_factor hP F E σ B a a' G X om om' ht v hv hnr _ (le_inf (augAt_le_SB om' v) (hf.inv' v)) inf_le_left
        fun h hh φ hφ φ₁ hφ₁ hact => ⟨hφ₁, by
          have := hf.equiv v h hh 0 (zero_mem _) φ hφ.1 0 (zero_mem _) φ₁ hφ₁ (acts_zero _ _) hact
            (by rw [map_zero]; exact hφ.2.symm)
          rw [map_zero] at this; exact this.symm⟩
  refine ⟨k1, k2, fun t ξ => ?_, fun l hl => ?_⟩
  · have : ξ ∈ (SB _).map (Rf.p' v) := hf.onto' v ▸ Submodule.mem_top
    obtain ⟨φ, hφ, rfl⟩ := this
    obtain ⟨φ₀, h₀, hd⟩ := GlobalTheory.T.schwartz_bruhat_local_approximation hP F E σ B a a' G X om om' ht v hv hnr t φ hφ
    refine ⟨φ₀, h₀, ?_⟩
    have := hf.inv' v hd
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
    exact this.symm
  · exact factor_of _ _ _ (hf.onto' v) fun φ hφ h0 => hl ((k2 φ hφ).1 h0)

end GlobalTheory.KCoinvGood
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kernel_coinvariant : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.KCoinv := by
  atlas_forward_decl GlobalTheory.KCoinvGood.kCoinv
end

section
section
noncomputable section

namespace GlobalTheory.ThK.Partner

open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.BigNZ
open scoped TensorProduct Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Pair

variable {n d : ℕ} {X : Spc F E n} {Y : Spc F E d}

theorem pure_smul (c : ℂ) (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) :
    pure (c • f) φ = c • pure f φ := by
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.smul_apply, smul_eq_mul, Pi.smul_apply, mul_assoc]

theorem polData_sum {B : Base F E} {M : Model σ X Y} {Φ} (h : Φ ∈ PolData B M) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, f i ∈ M.Pol B.ψ B.emb ∧ Fam M (φ i)) ∧ Φ = ∑ i, pure (f i) (φ i) := by
  obtain ⟨m, c, g, e⟩ := Submodule.mem_span_set'.1 h
  choose f hf φ hφ hv hΦ using fun i => (g i).2
  refine ⟨m, fun i => c i • f i, φ, fun i => ⟨Submodule.smul_mem _ _ (hf i), hφ i, hv i⟩, ?_⟩
  rw [← e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pure_smul, ← hΦ i]

theorem finite_bad {M : Model σ X Y} {m : ℕ} {φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ}
    (h : ∀ i, Fam M (φ i)) : {v | ∃ i, φ i v ≠ M.vac v}.Finite := by
  have e : {v | ∃ i, φ i v ≠ M.vac v} = ⋃ i, {v | φ i v ≠ M.vac v} := by ext; simp
  rw [e]
  exact Set.finite_iUnion fun i => eventually_cofinite.1 (h i).2

end Pair

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}

theorem partner_of_big (hK : KP) (hM : IsMatched B G X om om' R Rf) {Φ} (hΦ : Φ ∈ PolData B G.M) :
    ∃ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' := by
  have hco : Coinv B G X om om' Rf := GlobalTheory.T.theta_kernel_coinvariant hK.base F E σ B a a' G X om om' R Rf hM
  obtain ⟨m, f, φ, hfφ, rfl⟩ := polData_sum hΦ
  have hfin := finite_bad fun i => (hfφ i).2
  let T : Finset (Pl F) := X.T ∪ {B.v₁} ∪ hfin.toFinset
  have hXT : X.T ⊆ T := fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have h1 : B.v₁ ∈ T := Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  have hout : ∀ i, ∀ v ∉ T, φ i v = G.M.vac v := fun i v hv => by
    by_contra hc
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 ⟨i, hc⟩))
  have hre : ∀ i, ∃ g ∈ G.M'.Pol B.ψ B.emb, R.p' g = R.p (f i) := fun i =>
    Submodule.mem_map.1 (hM.real.quot'.onto ▸ Submodule.mem_top)
  choose f' hf' ef using hre
  have hsb : ∀ i v, ∃ χ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rf.p' v χ = Rf.p v (φ i v) := fun i v =>
    Submodule.mem_map.1 ((hM.fin.onto' v).symm ▸ Submodule.mem_top)
  choose χ hχ eχ using hsb
  have hso : ∀ i, ∃ ζ ∈ G.M'.SoLoc B.ψ B.τ₁, Rf.p' B.v₁ ζ = Rf.p B.v₁ (φ i B.v₁) := fun i =>
    (hco.1 B.v₁ hM.triple.chars.good).2.2.1 B.τ₁ _
  choose ζ hζ eζ using hso
  let φ₀ : Fin m → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ := fun i v => if v ∈ T then χ i v else G.M'.vac v
  let φ' : Fin m → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ := fun i => Function.update (φ₀ i) B.v₁ (ζ i)
  have fam₀ : ∀ i, Fam G.M' (φ₀ i) := fun i => by
    refine ⟨fun v => ?_, T.eventually_cofinite_notMem.mono fun v hv => if_neg hv⟩
    by_cases hv : v ∈ T
    · simp only [φ₀, if_pos hv]; exact hχ i v
    · simp only [φ₀, if_neg hv]; exact (hM.triple.geo.hM'.vac v).1
  have fam' : ∀ i, Fam G.M' (φ' i) := fun i => (fam₀ i).update B.v₁ (hζ i).1
  have out' : ∀ i, ∀ v ∉ T, φ' i v = G.M'.vac v := fun i v hv => by
    have hne : v ≠ B.v₁ := fun e => hv (e ▸ h1)
    simp only [φ', Function.update_of_ne hne, φ₀, if_neg hv]
  refine ⟨∑ i, pure (f' i) (φ' i), Submodule.sum_mem _ fun i _ => Submodule.subset_span
    ⟨f' i, φ' i, (fam' i).1, (fam' i).2, by simp only [φ', Function.update_self]; exact hζ i, rfl⟩, ?_⟩
  refine ⟨T, hXT, m, m, f, φ, f', φ', fun i => ⟨(hfφ i).1, (hfφ i).2.1, hout i⟩,
    fun i => ⟨hf' i, (fam' i).1, out' i⟩, rfl, rfl, ?_⟩
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ef i]
  congr 2
  funext ⟨v, hvT⟩
  by_cases hv : v = B.v₁
  · subst hv
    simp only [φ', Function.update_self, eζ]
  · simp only [φ', Function.update_of_ne hv, φ₀, if_pos hvT, eχ]

theorem partner_of_small (hM : IsMatched B G X om om' R Rf) {Φ'} (hΦ' : Φ' ∈ PolData B G.M') :
    ∃ Φ, PolMatch B G X R Rf Φ Φ' := by
  obtain ⟨m, f', φ', hfφ, rfl⟩ := polData_sum hΦ'
  have hfin := finite_bad fun i => (hfφ i).2
  let T : Finset (Pl F) := X.T ∪ hfin.toFinset
  have hXT : X.T ⊆ T := Finset.subset_union_left
  have hout : ∀ i, ∀ v ∉ T, φ' i v = G.M'.vac v := fun i v hv => by
    by_contra hc
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 ⟨i, hc⟩))
  have hre : ∀ i, ∃ g ∈ G.M.Pol B.ψ B.emb, R.p g = R.p' (f' i) := fun i =>
    Submodule.mem_map.1 (hM.real.quot.onto ▸ Submodule.mem_top)
  choose f hf ef using hre
  have hsb : ∀ i v, ∃ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rf.p v χ = Rf.p' v (φ' i v) := fun i v =>
    Submodule.mem_map.1 ((hM.fin.onto v).symm ▸ Submodule.mem_top)
  choose χ hχ eχ using hsb
  let φ : Fin m → ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ := fun i v => if v ∈ T then χ i v else G.M.vac v
  have hφ : ∀ i v, φ i v ∈ SB _ := fun i v => by
    by_cases hv : v ∈ T
    · simp only [φ, if_pos hv]; exact hχ i v
    · simp only [φ, if_neg hv]; exact (hM.triple.geo.hM.vac v).1
  refine ⟨∑ i, pure (f i) (φ i), T, hXT, m, m, f, φ, f', φ', fun i => ⟨hf i, hφ i, fun v hv => if_neg hv⟩,
    fun i => ⟨(hfφ i).1, (hfφ i).2.1, hout i⟩, rfl, rfl, ?_⟩
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ef i]
  congr 2
  funext ⟨v, hvT⟩
  simp only [φ, if_pos hvT, eχ]

theorem match_of_polMatch (hM : IsMatched B G X om om' R Rf) {Φ Φ'} (hS : Φ' ∈ G.M'.So B.ψ B.τ₁)
    (h : PolMatch B G X R Rf Φ Φ') : Φ ∈ PolData B G.M ∧ Φ' ∈ PolData B G.M' ∧ Match B G X R Rf Φ Φ' := by
  obtain ⟨T, -, m, m', f, φ, f', φ', hi, hj, e1, e2, -⟩ := id h
  have fam : ∀ i, Fam G.M (φ i) := fun i => ⟨(hi i).2.1, T.eventually_cofinite_notMem.mono (hi i).2.2⟩
  have fam' : ∀ j, Fam G.M' (φ' j) := fun j => ⟨(hj j).2.1, T.eventually_cofinite_notMem.mono (hj j).2.2⟩
  refine ⟨e1 ▸ Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, (hi i).1, φ i, (fam i).1, (fam i).2, rfl⟩,
    e2 ▸ Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨f' j, (hj j).1, φ' j, (fam' j).1, (fam' j).2, rfl⟩,
    hS, m, m', fun i => finPartFn (φ i), f, fun _ => f, fun j => finPartFn (φ' j), f', fun _ => f',
    fun i => ⟨(fam i).sb hM.triple.geo.hM, tendsto_const_nhds⟩, fun j => ⟨(fam' j).sb hM.triple.geo.hM', tendsto_const_nhds⟩,
    e1, e2, fun _ => ⟨?_, ?_⟩⟩
  · show ∑ j, pure (f' j) (φ' j) ∈ _
    rw [← e2]; exact hS
  · show PolMatch B G X R Rf (∑ i, pure (f i) (φ i)) (∑ j, pure (f' j) (φ' j))
    rw [← e1, ← e2]; exact h

end GlobalTheory.ThK.Partner

namespace GlobalTheory.ThK

theorem matchEx_of_classicalTheorems (hK : KP) : MatchEx := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hM
  exact ⟨fun Φ hΦ => Partner.partner_of_big hK hM hΦ, fun Φ' hΦ' => Partner.partner_of_small hM hΦ',
    fun Φ Φ' hS h => Partner.match_of_polMatch hM hS h⟩

end GlobalTheory.ThK

end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_matching_exists : GlobalTheory.ThK.KP → GlobalTheory.ThK.MatchEx := by
  atlas_forward_decl GlobalTheory.ThK.matchEx_of_classicalTheorems
end

section
noncomputable section

namespace GlobalTheory.ThKConst

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isHecke_div {χ₁ χ₂ : Chr F E} (h₁ : IsHecke F E χ₁) (h₂ : IsHecke F E χ₂) : IsHecke F E (χ₁ / χ₂) := by
  obtain ⟨c₁, t₁⟩ := h₁
  obtain ⟨c₂, t₂⟩ := h₂
  have e : ⇑(χ₁ / χ₂) = fun x => χ₁ x / χ₂ x := funext fun x => MonoidHom.div_apply χ₁ χ₂ x
  exact And.intro (by rw [e]; exact c₁.div' c₂) fun x => by rw [MonoidHom.div_apply, t₁ x, t₂ x, div_one]

theorem resEtaPow_div {K : Subgroup (AF F)ˣ} {χ₁ χ₂ : Chr F E} {n₁ n₂ n : ℕ} (h₁ : ResEtaPow K χ₁ n₁)
    (h₂ : ResEtaPow K χ₂ n₂) (he : Even (n₁ + n₂)) (hn : Even n) : ResEtaPow K (χ₁ / χ₂) n := by
  intro x
  have e₁ := h₁ x
  have e₂ := h₂ x
  rw [MonoidHom.div_apply, Circle.coe_div, e₁, e₂]
  split_ifs
  · norm_num
  · rcases Nat.even_or_odd n₁ with h | h
    · rw [h.neg_one_pow, ((Nat.even_add.mp he).mp h).neg_one_pow, hn.neg_one_pow]
      norm_num
    · have h' : Odd n₂ := Nat.not_even_iff_odd.mp fun h'' => (Nat.not_even_iff_odd.mpr h) ((Nat.even_add.mp he).mpr h'')
      rw [h.neg_one_pow, h'.neg_one_pow, hn.neg_one_pow]
      norm_num

variable {a a' : ℕ}

theorem isPair_big {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (h : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
  { base := h.base
    herm := h.geo.hV
    skew := h.geo.hW
    good := h.geo.hM
    hX := h.chars.heckeβ
    hW := isHecke_div h.chars.heckeβ h.chars.heckeα
    resX := h.chars.resβ
    resW := resEtaPow_div h.chars.resβ h.chars.resα h.geo.even h.geo.even
    weil := h.weil }

theorem isPair_small {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  { base := h.base
    herm := h.geo.hV'
    skew := h.geo.hW
    good := h.geo.hM'
    hX := h.chars.heckeα
    hW := isHecke_div h.chars.heckeα h.chars.heckeβ
    resX := h.chars.resα
    resW := resEtaPow_div h.chars.resα h.chars.resβ (Nat.even_add.mpr (Nat.even_add.mp h.geo.even).symm) h.geo.even
    weil := h.weil' }

theorem thetaSum_sum {κ ι : Type} [Fintype κ] (s : Finset ι) (f : ι → (κ → AF F) → ℂ) (hf : ∀ k ∈ s, f k ∈ schA F κ) :
    thetaSum F (∑ k ∈ s, f k) = ∑ k ∈ s, thetaSum F (f k) := by
  classical
  revert hf
  refine Finset.induction_on s (fun _ => ?_) ?_
  · simp [thetaSum]
  · intro k s hk ih hf
    have hs : ∀ j ∈ s, f j ∈ schA F κ := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hk, Finset.sum_insert hk,
      thetaSum_add F (hf k (Finset.mem_insert_self k s)) (Submodule.sum_mem _ hs), ih hs]

end GlobalTheory.ThKConst
end
end
