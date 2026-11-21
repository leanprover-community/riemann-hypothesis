import Development.WeilBound.CoreStatements.PlurisubharmonicCones.FlatSat
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AbelianPartHeightLinear
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartIntegralPointAltBis
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianHomLieExtends
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBounds
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartIntegralPoint
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFamilyExistsOnEigenspace
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LabelledDegreeCommensurableBound
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumLogPrimeDivPredLeLog
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LabelledDegreeEqLogIndex
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogIndexOfOrthogonalFamilyStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompactDatumIntersection
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspCorrespondenceBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartLieSignature

section
noncomputable section

namespace LevelTowerAlt

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights TensorProduct

theorem abel_abstract :
    ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (L Ψ : Type) [Field L] [NumberField L] [Fintype Ψ] (B : HermitianBundle.{0} L)
      (F F' : Ψ → Submodule (𝓞 L) B.carrier) (m N : ℕ) (La : ℝ), 1 ≤ Fintype.card Ψ * m → 1 ≤ La →
      ((Fintype.card Ψ * N : ℕ) : ℝ) ≤ Real.exp La → Module.finrank (𝓞 L) B.carrier ≤ Fintype.card Ψ * N →
      (∀ τ, B.rank (F τ) ≤ m) →
      B.slopeMax ≤ ((C₀ * Real.log (2 + Module.finrank (𝓞 L) B.carrier + max (-B.normDegree ⊤) 0) : ℝ) : EReal) →
      ∑ τ, B.normDegree (F τ) + ∑ τ, B.normDegree (F' τ) ≤ B.normDegree ⊤ →
      (∀ τ, |B.normDegree (F τ) - B.normDegree (F' τ)| ≤ C₀ * N * La) →
      ∑ τ, B.normDegree (F τ) ≤ C * (Fintype.card Ψ * m) * La := by
  intro C₀ hC₀
  obtain ⟨C, hC⟩ := LowerBound.InteriorDichotomy.proof C₀ 0 C₀ hC₀ le_rfl hC₀
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro L Ψ _ _ _ B F F' m N La hfm hLa hexp hrank hm hslope hsum0 hdd
  set f : ℝ := (Fintype.card Ψ : ℝ) with hf
  set h : ℝ := -B.normDegree ⊤ with hh
  set n : ℝ := (Module.finrank (𝓞 L) B.carrier : ℝ) with hn
  set g : ℝ := max ((Fintype.card Ψ * N : ℕ) : ℝ) 1 with hg
  set x : ℝ := ∑ τ, B.normDegree (F τ) with hx
  set y : ℝ := ∑ τ, B.normDegree (F' τ) with hy
  have hLa0 : 0 < La := by linarith
  have hf0 : 0 ≤ f := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hg1 : 1 ≤ g := le_max_right _ _
  have hfN : f * N ≤ g := by
    have : ((Fintype.card Ψ * N : ℕ) : ℝ) ≤ g := le_max_left _ _
    simpa [hf] using this
  have hng : n ≤ g := by
    have h1 : n ≤ ((Fintype.card Ψ * N : ℕ) : ℝ) := Nat.cast_le.2 hrank
    exact h1.trans (le_max_left _ _)
  have hfj : (1 : ℝ) ≤ f * m := by
    have : ((1 : ℕ) : ℝ) ≤ ((Fintype.card Ψ * m : ℕ) : ℝ) := by exact_mod_cast hfm
    simpa [hf] using this
  have hgexp : g ≤ Real.exp La := max_le hexp (Real.one_le_exp hLa0.le)

  set μ : ℝ := C₀ * Real.log (2 + n + max h 0) with hμ
  have harg : 1 ≤ 2 + n + max h 0 := by
    have h1 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have h2 := le_max_right h 0
    linarith
  have hμ0 : 0 ≤ μ := mul_nonneg hC₀ (Real.log_nonneg harg)
  have hμg : μ ≤ C₀ * Real.log (2 + g + max h 0) :=
    mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (by linarith)) hC₀
  have hxle : x ≤ f * m * μ := by
    have h1 : ∀ τ, B.normDegree (F τ) ≤ m * μ := fun τ =>
      (HermitianBundle.normDegree_le_rank_mul B _ μ hslope).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hm τ) hμ0)
    calc x ≤ ∑ _τ : Ψ, (m : ℝ) * μ := Finset.sum_le_sum fun τ _ => h1 τ
      _ = f * m * μ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hf]; ring

  have hsum : x + y ≤ -h := by
    rw [hh, neg_neg]
    exact hsum0
  have hxy : x - y ≤ f * (C₀ * N * La) := by
    have h1 : x - y ≤ ∑ _τ : Ψ, C₀ * N * La := by
      rw [hx, hy, ← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum fun τ _ => (le_abs_self _).trans (hdd τ)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    exact h1
  have hfC : f * (C₀ * N * La) ≤ C₀ * g * La := by
    have : C₀ * (f * N) * La ≤ C₀ * g * La :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfN hC₀) hLa0.le
    calc f * (C₀ * N * La) = C₀ * (f * N) * La := by ring
      _ ≤ _ := this
  have hyp : LowerBound.InteriorDichotomy.Hyp C₀ 0 C₀ h (-x) g (f * m) La :=
    { one_le_g := hg1
      one_le_fj := hfj
      g_le_exp := hgexp
      one_le_La := hLa
      lower := by
        have h1 : f * m * μ ≤ f * m * (C₀ * Real.log (2 + g + max h 0)) :=
          mul_le_mul_of_nonneg_left hμg (by linarith)
        have h2 : f * m * (C₀ * Real.log (2 + g + max h 0) + 0 * La) =
            f * m * (C₀ * Real.log (2 + g + max h 0)) := by ring
        rw [h2]
        linarith
      upper := by linarith }
  have hfin := hC h (-x) g (f * m) La hyp
  have h1 : C * (f * m) * La ≤ max C 0 * (f * m) * La :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)) hLa0.le
  have h2 : x ≤ C * (f * m) * La := by linarith
  exact h2.trans h1

theorem mem_eigSp_iff {R M O : Type} [CommRing R] [AddCommGroup M] [Module R M] [CommRing O]
    (ρ : O →+* Module.End R M) (σ : O →+* R) (x : M) : x ∈ eigSp ρ σ ↔ ∀ a, ρ a x = σ a • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

def intLift {E L : Type} [Field E] [Field L] (σ : 𝓞 E →+* L) : 𝓞 E →+* 𝓞 L where
  toFun a := ⟨σ a, map_isIntegral_int σ (RingOfIntegers.isIntegral a)⟩
  map_one' := Subtype.ext (map_one σ)
  map_mul' a b := Subtype.ext (map_mul σ a b)
  map_zero' := Subtype.ext (map_zero σ)
  map_add' a b := Subtype.ext (map_add σ a b)

theorem intLift_apply {E L : Type} [Field E] [Field L] (σ : 𝓞 E →+* L) (a : 𝓞 E) :
    algebraMap (𝓞 L) L (intLift σ a) = σ a := rfl

theorem exists_smul_mem_of_eig {R M O ι : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] [CommRing O]
    (ρ : O →+* Module.End R M) (σ : ι → (O →+* R)) (s : ι) (N : Submodule R M) (hN : N ≤ eigSp ρ (σ s))
    (T : Finset ι) (hT : ∀ t ∈ T, σ t ≠ σ s) :
    ∀ y ∈ eigSp ρ (σ s), y ∈ N ⊔ ⨆ t ∈ T, eigSp ρ (σ t) → ∃ d : R, d ≠ 0 ∧ d • y ∈ N := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro y _ hy
    refine ⟨1, one_ne_zero, ?_⟩
    simpa using hy
  | insert t T ht ih =>
    intro y hy hy'
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 (hT t (Finset.mem_insert_self _ _))
    let φ : M →ₗ[R] M := ρ a - σ t a • LinearMap.id
    have hφ : ∀ u, ∀ z ∈ eigSp ρ (σ u), φ z = (σ u a - σ t a) • z := fun u z hz => by
      change ρ a z - σ t a • z = _
      rw [(mem_eigSp_iff _ _ _).1 hz a, sub_smul]
    have hle : N ⊔ ⨆ u ∈ insert t T, eigSp ρ (σ u) ≤ (N ⊔ ⨆ u ∈ T, eigSp ρ (σ u)).comap φ := by
      refine sup_le (fun z hz => ?_) (iSup₂_le fun u hu z hz => ?_)
      · rw [Submodule.mem_comap, hφ s z (hN hz)]
        exact Submodule.mem_sup_left (N.smul_mem _ hz)
      · rw [Submodule.mem_comap, hφ u z hz]
        rcases Finset.mem_insert.1 hu with rfl | hu
        · rw [sub_self, zero_smul]
          exact Submodule.zero_mem _
        · exact Submodule.mem_sup_right (Submodule.smul_mem _ _
            (Submodule.mem_iSup_of_mem u (Submodule.mem_iSup_of_mem hu hz)))
    have h1 := hle hy'
    rw [Submodule.mem_comap, hφ s y hy] at h1
    obtain ⟨d, hd, h2⟩ := ih (fun u hu => hT u (Finset.mem_insert_of_mem hu)) _ (Submodule.smul_mem _ _ hy) h1
    exact ⟨d * (σ s a - σ t a), mul_ne_zero hd (sub_ne_zero.2 ha.symm), by rwa [mul_smul]⟩

theorem orthAt_saturation {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    {F F' G G' : Submodule (𝓞 L) B.carrier} (h : OrthAt B F F') (hG : ∀ x ∈ G, ∃ a : 𝓞 L, a ≠ 0 ∧ a • x ∈ F)
    (hG' : ∀ x ∈ G', ∃ a : 𝓞 L, a ≠ 0 ∧ a • x ∈ F') : OrthAt B G G' := by
  intro σ x hx y hy
  obtain ⟨a, ha, hx⟩ := hG x hx
  obtain ⟨b, hb, hy⟩ := hG' y hy
  have h1 : inner ℂ (fibreVec B.metric σ (a • x)) (fibreVec B.metric σ (b • y)) = 0 := h σ _ hx _ hy
  rw [fibreVec_smul, fibreVec_smul, inner_smul_left, inner_smul_right] at h1
  have ha' : σ (a : L) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast ha
  have hb' : σ (b : L) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast hb
  exact (mul_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left ((map_ne_zero _).2 ha'))).resolve_left hb'

variable {E L Ψ V : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] [AddCommGroup V] [Module L V]
  [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (ρM : 𝓞 E →+* Module.End (𝓞 L) A.Bq.carrier)

theorem eig_facts (hcard : 2 * Fintype.card Ψ = Module.finrank ℚ E)
    (hρ : ∀ (a : 𝓞 E) (x : A.Λ), A.f ⟨A.ρ a x, A.stable a x x.2⟩ = ρM a (A.f x)) :
    (∀ s, A.Bq.rank (eigSp ρM (intLift (A.σ s))) = A.Bq.rank (A.img s)) ∧
    (∀ s, A.Bq.normDegree (A.img s) ≤ A.Bq.normDegree (eigSp ρM (intLift (A.σ s)))) ∧
    ∑ s, A.Bq.normDegree (eigSp ρM (intLift (A.σ s))) ≤ A.Bq.normDegree ⊤ := by
  classical
  have h1 : ∀ s, A.img s ≤ eigSp ρM (intLift (A.σ s)) := by
    rintro s _ ⟨x, hx, rfl⟩
    have hx' : (x : V) ∈ eigSp A.ρ (A.σ s) := (Submodule.mem_inf.1 hx).2
    refine (mem_eigSp_iff _ _ _).2 fun a => ?_
    rw [← hρ, ← map_smul]
    congr 1
    refine Subtype.ext ?_
    change A.ρ a x = intLift (A.σ s) a • (x : V)
    rw [(mem_eigSp_iff _ _ _).1 hx' a, ← algebraMap_smul L (intLift (A.σ s) a), intLift_apply]
  have h2 : ∀ s, ∀ y ∈ eigSp ρM (intLift (A.σ s)), ∃ a : 𝓞 L, a ≠ 0 ∧ a • y ∈ A.img s := by
    intro s y hy
    have h3 : y ∈ CanonicalFiltration.saturation A.Bq (⨆ t, A.img t) := by
      rw [A.saturation_iSup_img hcard]
      exact Submodule.mem_top
    obtain ⟨c, hc, h3⟩ := h3
    have hle : (⨆ t, A.img t) ≤ A.img s ⊔ ⨆ t ∈ Finset.univ.erase s, eigSp ρM (intLift (A.σ t)) := by
      refine iSup_le fun t z hz => ?_
      by_cases hts : t = s
      · subst hts
        exact Submodule.mem_sup_left hz
      · exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem t
          (Submodule.mem_iSup_of_mem (Finset.mem_erase.2 ⟨hts, Finset.mem_univ t⟩) (h1 t hz)))
    obtain ⟨d, hd, h4⟩ := exists_smul_mem_of_eig ρM (fun t => intLift (A.σ t)) s (A.img s) (h1 s) (Finset.univ.erase s)
      (fun t ht h => (Finset.mem_erase.1 ht).1 (A.σ_bij.1 (RingHom.ext fun a => by
        rw [← intLift_apply, ← intLift_apply (A.σ s)]
        exact congrArg _ (DFunLike.congr_fun h a)))) _ (Submodule.smul_mem _ c hy) (hle h3)
    exact ⟨d * c, mul_ne_zero hd hc, by rwa [mul_smul]⟩
  have mono : ∀ {X Y : Submodule (𝓞 L) A.Bq.carrier}, X ≤ Y → A.Bq.rank X ≤ A.Bq.rank Y := fun h =>
    Submodule.finrank_mono h
  have h5 : ∀ s, A.Bq.rank (eigSp ρM (intLift (A.σ s))) = A.Bq.rank (A.img s) := fun s =>
    le_antisymm ((mono (Y := CanonicalFiltration.saturation A.Bq (A.img s)) fun y hy => h2 s y hy).trans
      (CanonicalFiltration.rank_saturation A.Bq _).le) (mono (h1 s))
  refine ⟨h5, fun s => div_le_div_of_nonneg_right
    (CanonicalFiltration.degree_le_of_le_of_rank_eq A.Bq (h1 s) (h5 s).symm) (Nat.cast_nonneg _), ?_⟩
  have hI := GlobalTheory.T.normalized_degree_orthogonal_sum L A.Bq (Ψ ⊕ Ψ) (fun s => eigSp ρM (intLift (A.σ s))) fun s s' h =>
    orthAt_saturation A.Bq (F := A.img s) (F' := A.img s') (by
      rw [A.img_eq, A.img_eq]
      exact A.orth s s' h) (h2 s) (h2 s')
  have hr : A.Bq.rank (⨆ s, eigSp ρM (intLift (A.σ s))) = A.Bq.rank ⊤ := by
    refine le_antisymm (mono le_top) ?_
    have := CanonicalFiltration.rank_saturation A.Bq (⨆ s, A.img s)
    rw [A.saturation_iSup_img hcard] at this
    rw [this]
    exact mono (iSup_mono h1)
  rw [← hI.1]
  exact div_le_div_of_nonneg_right (CanonicalFiltration.degree_le_of_le_of_rank_eq A.Bq le_top hr) (Nat.cast_nonneg _)

end LevelTowerAlt
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace LevelTowerAlt

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)
  {L : Type} [Field L] [NumberField L] {z : Sp (𝓞 L) ⟶ 𝔐.X}
  {P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)} {V : Type} [AddCommGroup V] [Module L V] [Module (𝓞 L) V]
  [IsScalarTower (𝓞 L) L V] {MV : LieModel P.tK.G (𝟙 (Sp L)) V} {A : LinPt E L (CMType H) V}

theorem finrank_eig' (h : 𝔐.IsLinPtOf z P MV A) (s : CMType H ⊕ CMType H) :
    Module.finrank L (eigSp A.ρ (A.σ s)) = labelRk D s := by
  obtain ⟨U, hU, b, -, hb⟩ := 𝔐.vb s ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), 𝔐.all _⟩ trivial
  have h1 := hb _ trivial hU
  have h2 : (𝔐.dR s).IsFrameAt b ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), 𝔐.all _⟩ :=
    ⟨h1.1, (Lat.patch_of_not _ _ _ fun p hp => PtHt.FrameVal.not_inFibre _ _ p (𝔐.S_prime p hp)).symm.trans h1.2⟩
  obtain ⟨sL, -, hi, hs⟩ := GlobalTheory.T.abelian_part_integral_point_alt E H D l Xo c Y S Ω K J y 𝔐 L z P V MV A s _ b h h2
  rw [← hs, finrank_span_eq_card hi, Fintype.card_fin]

omit [∀ k, Fintype (J k)] in
theorem exists_action (h : 𝔐.IsLinPtOf z P MV A) :
    ∃ (t' : SAB H (Sp (𝓞 L))) (_ : SABMap P.tB t' (spMap (algebraMap (𝓞 L) L)))
      (MB : LieModel t'.G (𝟙 _) A.Bq.carrier) (ρM : 𝓞 E →+* Module.End (𝓞 L) A.Bq.carrier),
      IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) A.Bq MB ∧ MB.IsActOf t'.act.act ρM ∧
        ∀ (a : 𝓞 E) (x : A.Λ), A.f ⟨A.ρ a x, A.stable a x x.2⟩ = ρM a (A.f x) := by
  obtain ⟨hact, -, -, -, -, t', m', MB, hfib, hl⟩ := h
  obtain ⟨ρM, hρ, -⟩ := lieModel_exists_unique_act _ t'.G (𝓞 L) (𝟙 _) _ MB (𝓞 E) t'.act.act t'.act.hom t'.act.one
    t'.act.mul t'.act.add
  refine ⟨t', m', MB, ρM, hfib, hρ, fun a x => ?_⟩
  have := t'.semi.separated
  refine MB.inj (Over.OverMorphism.ext (LieHomOk.ext_of_spMap_injective (dualMap (algebraMap (𝓞 L) L))
    (LieTangent.dualMap_injective (IsFractionRing.injective _ _)) t'.G.hom _ _
    ((Over.w (MB.pt _)).trans (Over.w (MB.pt _)).symm) ?_))
  have h1 : (MV.pt (A.ρ a x) ≫ P.τ.q ≫ P.e.hom).left ≫ m'.φ = _ := hl ⟨A.ρ a x, A.stable a x x.2⟩
  have h2 : (MV.pt x ≫ P.τ.q ≫ P.e.hom).left ≫ m'.φ = _ := hl x
  have h3 : MV.pt (A.ρ a x) ≫ P.τ.q ≫ P.e.hom = (MV.pt x ≫ P.τ.q ≫ P.e.hom) ≫ P.tB.act.act a := by
    rw [hact a x, Category.assoc, P.act a]
    simp only [Category.assoc]
  rw [← h1, h3, hρ a (A.f x)]
  generalize MV.pt x ≫ P.τ.q ≫ P.e.hom = w at h2
  have h4 : (P.tB.act.act a).left ≫ m'.φ = m'.φ ≫ (t'.act.act a).left := m'.act a
  change (w.left ≫ (P.tB.act.act a).left) ≫ m'.φ =
    spMap (dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt (A.f x)).left ≫ (t'.act.act a).left
  rw [Category.assoc, h4]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (t'.act.act a).left) h2).trans (Category.assoc _ _ _))

end Geo

end LevelTowerAlt
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace LevelTowerAlt

theorem phiDeg_le_parts {E L Ψ : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] {V : Type}
    [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (lab : Ψ → Ψ ⊕ Ψ)
    (F : Ψ → Submodule (𝓞 L) V) {r k : ℕ} (v : Fin r → V) (q : Ψ → Fin k → A.Λ) (X : ℝ)
    (hf : 2 * Fintype.card Ψ = Module.finrank ℚ E) (hO : IsOFamily A.ρ A.I v)
    (hq : ∀ τ, A.IsAdapted (lab τ) v (q τ) ∧ ∀ i, (q τ i : V) ∈ A.eig (lab τ))
    (ha : ∀ τ, ∃ 𝔞 : Ideal (𝓞 L), 𝔞 ≠ ⊥ ∧ 𝔞 • F τ ≤ A.eig (lab τ) ∧ 𝔞 • A.eig (lab τ) ≤ F τ ∧
      Real.log (Ideal.absNorm 𝔞) / Module.finrank ℚ L ≤ X) :
    A.phiDeg lab F v q ≤ Fintype.card Ψ * (((r : ℝ) + k) * X) - Fintype.card Ψ * (r * Real.log (hostRd E)) +
      ∑ τ, A.Bq.normDegree (A.img (lab τ)) + Fintype.card Ψ * r / 2 * Real.log (4 * Real.pi) := by
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = Real.log (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) := ⟨_, rfl⟩
  have hstep : ∀ τ, A.labDeg (lab τ) (F τ) v (q τ) ≤ ((r : ℝ) + k) * X +
      (-(r * Real.log (hostRd E)) + I / Module.finrank ℚ E + A.Bq.normDegree (A.img (lab τ))) := by
    intro τ
    obtain ⟨𝔞, h0, h1, h2, h3⟩ := ha τ
    have hc := GlobalTheory.T.labelled_degree_commensurable_bound E L Ψ V A r k v (lab τ) (q τ) (F τ) 𝔞 (hq τ).1 h0 h1 h2
    have hs := GlobalTheory.T.labelled_degree_eq_log_index E L Ψ V A r k v (lab τ) (q τ) hf hO (hq τ).2 (hq τ).1
    have ht := GlobalTheory.T.log_index_of_orthogonal_family E L Ψ V A r v hf hO (lab τ)
    have h4 : ((r : ℝ) + k) * Real.log (Ideal.absNorm 𝔞) / Module.finrank ℚ L ≤ ((r : ℝ) + k) * X := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 := (abs_le.1 hc).2
    rw [hs, ht, ← hI] at h5
    unfold hostRd
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun τ _ => hstep τ
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hE : (Module.finrank ℚ E : ℝ) = 2 * Fintype.card Ψ := by exact_mod_cast hf.symm
  have hc0 : (Fintype.card Ψ : ℝ) ≠ 0 := by
    have hn : 0 < Module.finrank ℚ E := Module.finrank_pos
    have : Fintype.card Ψ ≠ 0 := by omega
    exact_mod_cast this
  have hcI : (Fintype.card Ψ : ℝ) * (I / Module.finrank ℚ E) = I / 2 := by
    rw [hE]
    field_simp
  have hphi : A.phiDeg lab F v q = ∑ τ, A.labDeg (lab τ) (F τ) v (q τ) - I / 2 +
      Fintype.card Ψ * r / 2 * Real.log (4 * Real.pi) := by
    rw [hI]
    rfl
  rw [hphi]
  linarith

theorem small_blocks_numbers {f j r Ca C1 La X rd l4 T : ℝ} (hf : 0 ≤ f) (hj : 0 ≤ j) (hr0 : 0 ≤ r) (hrj : r ≤ j)
    (hLa : 0 ≤ La) (hrd : 0 ≤ rd) (hl4 : l4 ≤ La) (hX : X ≤ (2 * C1 + 2) * La) (hT : T ≤ Ca * (f * j) * La) :
    f * (j * X) - f * (r * rd) + T + f * r / 2 * l4 ≤ (2 * C1 + 2 + Ca + 1) * f * j * La := by
  have hfj : 0 ≤ f * j := mul_nonneg hf hj
  have h1 : f * (j * X) ≤ f * j * ((2 * C1 + 2) * La) := by
    rw [← _root_.mul_assoc]
    exact mul_le_mul_of_nonneg_left hX hfj
  have h2 : 0 ≤ f * (r * rd) := mul_nonneg hf (mul_nonneg hr0 hrd)
  have h3 : f * r / 2 * l4 ≤ f * j * La := by
    have h4 : f * r / 2 * l4 ≤ f * r / 2 * La := mul_le_mul_of_nonneg_left hl4 (by positivity)
    have h5 : f * r / 2 * La ≤ f * r * La := by
      have : 0 ≤ f * r * La := by positivity
      nlinarith
    have h6 : f * r * La ≤ f * j * La :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrj hf) hLa
    linarith
  nlinarith

theorem height_comparison_global_model : (Top.Given → Fl.FlatDegree → FlatSat) → Top.Given → Fl.FlatDegree → ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ B : ℕ) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ Or.𝔐.X) (P : AbPart Or.𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V) (r k : ℕ) (v : Fin r → V) (q : CMType H → Fin k → A.Λ), admitted Xo l c Y Or B₁ → 4 * Dc.f * Dc.N ^ 2 ≤ B → Or.𝔐.IsLinPtOf z P MV A → Module.finrank (𝓞 L) A.Bq.carrier ≤ Fintype.card (CMType H) * (D.p + D.q) → r + k = Dc.j' → IsOFamily A.ρ A.I v → (∀ τ, A.IsAdapted (Or.sm τ) v (q τ) ∧ ∀ i, (q τ i : V) ∈ A.eig (Or.sm τ)) → A.phiDeg Or.sm (fun τ => Or.𝔐.FibLat (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) z P MV) v q ≤ C * Dc.f * Dc.j' * abelian₂ B (hostRd E) (hostLval H) := by
  intro hFS hG hF
  obtain ⟨Cf, hCf0, hflat⟩ := hFS hG hF
  obtain ⟨C1, hC10, hprimes⟩ := GlobalTheory.T.sum_log_prime_div_pred_le_log
  have hG' := hG
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Cs, hCs0, hslope⟩, -⟩ := hG'
  have hC₀ : 0 ≤ Cs + Cf * (2 + C1) := by positivity
  obtain ⟨Ca, hCa0, habel⟩ := abel_abstract (Cs + Cf * (2 + C1)) hC₀
  refine ⟨2 * C1 + 2 + Ca + 1, by positivity, ?_⟩
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B₁ B L _ _ z P V _ _ _ _ MV A r k v q hAdm hB hLin hfin
    hrk hO hq
  obtain ⟨hglob, hgood, hS₀, hcard, -, -, hjj⟩ := hAdm
  obtain ⟨hrd2, hne, hf2⟩ := GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H
  have hf1 : 1 ≤ Dc.f := Fintype.card_pos_iff.2 hne
  have hN2 := Dc.two_le_N
  have hj1 := Dc.one_le_j
  have hjl := Dc.j_le
  have hj' : Dc.j' = Dc.N - Dc.j := rfl
  have hNeq := Or.N_eq
  have hj'1 : 1 ≤ Dc.j' := by omega
  have hpq : 1 ≤ D.p ∧ 1 ≤ D.q := by
    rcases Or.side with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> omega
  have hN4 : 4 ≤ Dc.N ^ 2 := by nlinarith
  have hB16 : 16 ≤ B := by nlinarith
  have hfNB : Dc.f * Dc.N ≤ B := by nlinarith [Nat.le_self_pow (n := 2) (by norm_num) Dc.N]
  have hS₀B : S₀.card ≤ B := hcard.trans hB
  obtain ⟨hp, hR, ht, hvb⟩ := GlobalTheory.T.compact_datum_intersection E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B
  have hHT : ∀ p ∈ S₀ ∪ Dc.SB B, HT.HTFree (Or.𝔐.withS (S₀ ∪ Dc.SB B) hp hR ht hvb) p := by
    intro p hp'
    rcases Finset.mem_union.1 hp' with h | h
    · exact hgood.1 p h
    · exact hgood.2 p (Finset.mem_filter.1 h).1
  have hLin' : (Or.𝔐.withS (S₀ ∪ Dc.SB B) hp hR ht hvb).IsLinPtOf z P MV A := hLin
  have hSr : ∀ r' : ℕ, r'.Prime → (r' : ℤ) ∣ 2 * discr E * l.M' → r' ∈ S₀ ∪ Dc.SB B := fun r' h1 h2 =>
    Finset.mem_union_left _ ((hS₀ r').2 ⟨h1, h2⟩)
  have hSd : ∀ r' : ℕ, r'.Prime → (r' : ℤ) ∣ discr E → r' ∈ S₀ ∪ Dc.SB B := fun r' h1 h2 =>
    hSr r' h1 (Dvd.dvd.mul_right (Dvd.dvd.mul_left h2 2) _)
  have hsumP : ∑ p ∈ S₀ ∪ Dc.SB B, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ C1 * Real.log B := by
    refine hprimes (S₀ ∪ Dc.SB B) S₀ B (by omega) (fun p hp' => ⟨hp p hp', ?_⟩) hS₀B
    rcases Finset.mem_union.1 hp' with h | h
    · exact _root_.Or.inr h
    · exact _root_.Or.inl (Finset.mem_filter.1 h).2
  have hrd0 : 0 < hostRd E := by linarith
  have hlrd : 0 ≤ Real.log (hostRd E) := Real.log_nonneg (by linarith)
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hB16' : (16 : ℝ) ≤ B := by exact_mod_cast hB16
  have hLam : abelian₂ B (hostRd E) (hostLval H) = Real.log B + Real.log (hostRd E) + |hostLval H| := by
    unfold GroundTheory.Heights₂.Heights.LowerBoundFree.abelian₂
    rw [Real.log_mul hB0.ne' hrd0.ne']
  have hlogB : 1 ≤ Real.log B := by
    rw [Real.le_log_iff_exp_le hB0]
    have := Real.exp_one_lt_d9
    linarith
  have hLa1 : 1 ≤ abelian₂ B (hostRd E) (hostLval H) := by
    rw [hLam]
    linarith [abs_nonneg (hostLval H)]
  have hBLa : Real.log B ≤ abelian₂ B (hostRd E) (hostLval H) := by
    rw [hLam]
    linarith [abs_nonneg (hostLval H)]
  have hl4 : Real.log (4 * Real.pi) ≤ abelian₂ B (hostRd E) (hostLval H) := by
    refine le_trans (Real.log_le_log (by positivity) ?_) hBLa
    linarith [Real.pi_le_four]
  have hexp : ((Fintype.card (CMType H) * (D.p + D.q) : ℕ) : ℝ) ≤ Real.exp (abelian₂ B (hostRd E) (hostLval H)) := by
    have h1 : ((Fintype.card (CMType H) * (D.p + D.q) : ℕ) : ℝ) ≤ B := by
      rw [← hNeq]
      exact_mod_cast hfNB
    have h2 : (B : ℝ) ≤ Real.exp (abelian₂ B (hostRd E) (hostLval H)) := by
      rw [← Real.log_le_iff_le_exp hB0]
      exact hBLa
    exact h1.trans h2
  have hrank : ∀ τ, A.Bq.rank (A.img (Or.sm τ)) ≤ Dc.j' := by
    intro τ
    obtain ⟨k', q', -, -, hk', hrk', -⟩ := (GlobalTheory.T.adapted_family_exists_on_eigenspace E L (CMType H) V A hf2).2 r v hO (Or.sm τ)
    have h1 : Module.finrank L (eigSp A.ρ (A.σ (Or.sm τ))) = r + k := by
      rw [← (hq τ).1.2, finrank_span_eq_card (hq τ).1.1, Fintype.card_fin]
    omega
  have hsl : A.Bq.slopeMax ≤ (((Cs + Cf * (2 + C1)) *
      Real.log (2 + Module.finrank (𝓞 L) A.Bq.carrier + max (-A.Bq.normDegree ⊤) 0) : ℝ) : EReal) := by
    obtain ⟨-, -, -, -, hprinc, t', m', MB, hfib, -⟩ := hLin
    refine (hslope E H L t' P.tB m' hprinc A.Bq MB hfib).trans (EReal.coe_le_coe_iff.2 ?_)
    refine mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hCf0 (by linarith : (0 : ℝ) ≤ 2 + C1)]) ?_
    refine Real.log_nonneg ?_
    have h1 : (0 : ℝ) ≤ Module.finrank (𝓞 L) A.Bq.carrier := by positivity
    have h2 : (0 : ℝ) ≤ max (-A.Bq.normDegree ⊤) 0 := le_max_right _ _
    linarith
  obtain ⟨t', m', MB, ρM, hfib, hact, hρ⟩ := exists_action Or.𝔐 hLin
  obtain ⟨e1, e2, e3⟩ := eig_facts A ρM hf2 hρ
  obtain ⟨σ₀, -, hσu, -, -, -, hσc⟩ := GlobalTheory.T.cusp_correspondence_bound E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 L
    (spMap (algebraMap (𝓞 L) L) ≫ z)
  have hσ : A.σ = σ₀ := hσu A.σ hLin.2.1
  have hrk2 : ∀ s, A.Bq.rank (eigSp ρM (intLift (A.σ s))) ≤ labelRk D s := by
    intro s
    obtain ⟨k', q', -, -, hk', hrk', -⟩ := (GlobalTheory.T.adapted_family_exists_on_eigenspace E L (CMType H) V A hf2).2 r v hO s
    rw [finrank_eig' Or.𝔐 hLin] at hk'
    rw [e1]
    omega
  have hfl0 : ∀ τ, |A.Bq.normDegree (eigSp ρM (intLift (A.σ (.inl τ)))) -
      A.Bq.normDegree (eigSp ρM (intLift (A.σ (.inr τ))))| ≤
      (Cs + Cf * (2 + C1)) * ((D.p + D.q : ℕ) : ℝ) * abelian₂ B (hostRd E) (hostLval H) := by
    intro τ
    have h0 := hflat E H L t' P.tB m' A.Bq MB ρM (intLift (A.σ (.inl τ))) (intLift (A.σ (.inr τ))) hLin.2.2.2.2.1 hfib hact
      (GlobalTheory.T.abelian_part_lie_signature E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 L _ P)
      (fun a b hab => A.σ_inj (.inl τ) (congrArg (algebraMap (𝓞 L) L) hab))
      (fun e a => by
        have := DFunLike.congr_fun ((hσc e).2.2 τ) a
        rw [← hσ] at this
        exact this)
    refine h0.trans ?_
    have h2 : 1 + Real.log (hostRd E) + |hostLval H| ≤ (2 + C1) * abelian₂ B (hostRd E) (hostLval H) := by
      have h3 : 0 ≤ C1 * abelian₂ B (hostRd E) (hostLval H) := mul_nonneg hC10 (by linarith)
      have h4 : Real.log (hostRd E) + |hostLval H| ≤ abelian₂ B (hostRd E) (hostLval H) := by
        rw [hLam]
        linarith
      linarith
    have hn : (0 : ℝ) ≤ (D.p : ℝ) + D.q := by positivity
    have hLa0 : 0 ≤ abelian₂ B (hostRd E) (hostLval H) := by linarith
    have h5 : (A.Bq.rank (eigSp ρM (intLift (A.σ (.inl τ)))) : ℝ) + A.Bq.rank (eigSp ρM (intLift (A.σ (.inr τ)))) ≤
        (D.p : ℝ) + D.q := by
      have a1 : A.Bq.rank (eigSp ρM (intLift (A.σ (.inl τ)))) ≤ D.p := hrk2 (.inl τ)
      have a2 : A.Bq.rank (eigSp ρM (intLift (A.σ (.inr τ)))) ≤ D.q := hrk2 (.inr τ)
      exact_mod_cast add_le_add a1 a2
    have h6 : 0 ≤ 1 + Real.log (hostRd E) + |hostLval H| := by positivity
    push_cast
    calc _ ≤ Cf * ((D.p : ℝ) + D.q) * (1 + Real.log (hostRd E) + |hostLval H|) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 hCf0) h6
      _ ≤ Cf * ((D.p : ℝ) + D.q) * ((2 + C1) * abelian₂ B (hostRd E) (hostLval H)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Cf * (2 + C1) * ((D.p : ℝ) + D.q) * abelian₂ B (hostRd E) (hostLval H) := by ring
      _ ≤ (Cs + Cf * (2 + C1)) * ((D.p : ℝ) + D.q) * abelian₂ B (hostRd E) (hostLval H) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hn) hLa0
          linarith
  rw [Fintype.sum_sum_type] at e3
  have hab0 := habel L (CMType H) A.Bq (fun τ => eigSp ρM (intLift (A.σ (Or.sm τ))))
    (fun τ => eigSp ρM (intLift (A.σ (Or.bg τ)))) Dc.j' (D.p + D.q) (abelian₂ B (hostRd E) (hostLval H))
    (Nat.mul_pos hf1 hj'1) hLa1 hexp hfin (fun τ => (e1 _).trans_le (hrank τ)) hsl
    (by
      rcases Or.side with ⟨hb, hs, -⟩ | ⟨hb, hs, -⟩
      · rw [hb, hs]
        linarith
      · rw [hb, hs]
        exact e3)
    (fun τ => by
      rcases Or.side with ⟨hb, hs, -⟩ | ⟨hb, hs, -⟩
      · rw [hb, hs, abs_sub_comm]
        exact hfl0 τ
      · rw [hb, hs]
        exact hfl0 τ)
  have hab := (Finset.sum_le_sum (s := Finset.univ) fun τ _ => e2 (Or.sm τ)).trans hab0
  have hm := GlobalTheory.T.abelian_part_integral_point hG E H D l (Xo l) c Y (S₀ ∪ Dc.SB B) Ω K J Dc.y (Or.𝔐.withS (S₀ ∪ Dc.SB B) hp hR ht hvb) L z P V MV A
    (by omega) hSd hHT hLin'
  have hparts := phiDeg_le_parts A Or.sm (fun τ => Or.𝔐.FibLat (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) z P MV) v q
    (2 * (∑ p ∈ S₀ ∪ Dc.SB B, Real.log (p : ℝ) / ((p : ℝ) - 1)) + 2 * Real.log (hostRd E)) hf2 hO hq
    fun τ => hm (Or.sm τ)
  have hjr : ((r : ℝ) + k) = Dc.j' := by exact_mod_cast hrk
  have hrj : (r : ℝ) ≤ Dc.j' := by
    rw [← hjr]
    have : (0 : ℝ) ≤ k := by positivity
    linarith
  rw [hjr] at hparts
  refine hparts.trans ?_
  refine small_blocks_numbers (f := Dc.f) (by positivity) (by positivity) (by positivity) hrj (by linarith) hlrd hl4 ?_ hab
  have h3 : C1 * Real.log B ≤ C1 * abelian₂ B (hostRd E) (hostLval H) := mul_le_mul_of_nonneg_left hBLa hC10
  have h4 : Real.log (hostRd E) ≤ abelian₂ B (hostRd E) (hostLval H) := by
    rw [hLam]
    linarith [abs_nonneg (hostLval H)]
  linarith

end LevelTowerAlt
end
