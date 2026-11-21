import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeApproximationUpwardIdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtFoldrLineDer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsSecondKindFormPreservingGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupSecondKindCoordinatesNearOne
import BuildAid.ForwardExisting

section
open Filter Topology Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordsSecondKind_formPreservingGroup : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ), ∃ (d : ℕ) (Z : Fin d → Matrix (Fin m) (Fin m) ℂ) (s : Matrix (Fin m) (Fin m) ℂ → Fin d → ℝ), (∀ i, (Z i)ᴴ * A + A * Z i = 0) ∧ Tendsto s (𝓝[{X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * A * X = A}] 1) (𝓝 0) ∧ ∀ᶠ X in 𝓝[{X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * A * X = A}] 1, X = (List.ofFn fun i => NormedSpace.exp (s X i • Z i)).prod := by
  first | exact @GlobalTheory.ClosedMatGroup.coords_second_kind_unitary | exact GlobalTheory.ClosedMatGroup.coords_second_kind_unitary | (intros; apply GlobalTheory.ClosedMatGroup.coords_second_kind_unitary <;> assumption)
end

section
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut Filter Topology
open scoped TensorProduct ContDiff

namespace GlobalTheory.UAut

theorem exists_coordSecondKind_arch : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ w : InfinitePlace F, ∃ (d : ℕ) (η : Fin d → ℝ → GAd σ J) (s : GArch σ J w → Fin d → ℝ),
      (∀ i, IsRealLine σ J (η i)) ∧ Tendsto s (𝓝 1) (𝓝 0) ∧
        ∀ᶠ y in 𝓝 1, embArch σ J w y = (List.ofFn fun i => η i (s y i)).prod := by
  intro F E _ _ _ _ _ σ h n J hJ w
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  set A : Matrix (Fin n) (Fin n) ℂ := J.map τ.1 with hA
  obtain ⟨d, Z, s₀, hZ, hs, hev⟩ := GlobalTheory.T.coordsSecondKind_formPreservingGroup n A
  have hd : IsUnit A.det := by
    rw [hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ hJ.2).map _

  have hy : ∀ (i : Fin d) (t : ℝ), ∃ y : GArch σ J w, GlobalTheory.Orb.archMat σ J τ y = NormedSpace.exp (t • Z i) := by
    intro i t
    obtain ⟨u, hu⟩ := Matrix.isUnit_exp (t • Z i)
    have h1 := GlobalTheory.SmoothForms.exp_mem_UH (X := t • Z i) hd (by
      rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hZ i, smul_zero])
    refine ⟨(archEquiv J h τ).symm ⟨u, show _ * _ * _ = _ from hu ▸ h1⟩, ?_⟩
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, MulEquiv.apply_symm_apply]
    exact hu
  choose y hy using hy

  have hS : ∀ g : GArch σ J w, GlobalTheory.Orb.archMat σ J τ g ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * A * X = A} := by
    intro g
    have := (archEquiv J h τ g).2
    rw [Set.mem_ofPred_eq, GlobalTheory.Orb.archMat_eq_archEquiv J h]
    exact this
  have hc : Tendsto (GlobalTheory.Orb.archMat σ J τ) (𝓝 1) (𝓝[{X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * A * X = A}] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hS⟩
    simpa using (GlobalTheory.Orb.continuous_archMat σ J τ).tendsto 1
  have hinj : Function.Injective (GlobalTheory.Orb.archMat σ J τ) := fun a b e =>
    (GlobalTheory.Orb.isEmbedding_archMat J h τ).injective (by
      show (fun i j => GlobalTheory.Orb.archMat σ J τ a i j) = fun i j => GlobalTheory.Orb.archMat σ J τ b i j
      rw [e])
  refine ⟨d, fun i t => embArch σ J w (y i t), fun g => s₀ (GlobalTheory.Orb.archMat σ J τ g),
    fun i => ⟨w, τ, Z i, hZ i, fun t => ⟨y i t, rfl, hy i t⟩⟩, hs.comp hc, ?_⟩
  filter_upwards [hc.eventually hev] with g hg
  have e1 : (List.ofFn fun i => embArch σ J w (y i (s₀ (GlobalTheory.Orb.archMat σ J τ g) i))).prod =
      embArch σ J w (List.ofFn fun i => y i (s₀ (GlobalTheory.Orb.archMat σ J τ g) i)).prod := by
    rw [map_list_prod, List.map_ofFn]; rfl
  rw [e1]
  congr 1
  apply hinj
  rw [map_list_prod, List.map_ofFn]
  refine hg.trans ?_
  congr 1
  exact List.ofFn_inj.2 (funext fun i => (hy i _).symm)

end GlobalTheory.UAut
end

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut Filter Topology
open scoped TensorProduct ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_secondKindCoordinates_unitaryArchimedeanPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ w : InfinitePlace F, ∃ (d : ℕ) (η : Fin d → ℝ → GAd σ J) (s : GArch σ J w → Fin d → ℝ), (∀ i, IsRealLine σ J (η i)) ∧ Tendsto s (𝓝 1) (𝓝 0) ∧ ∀ᶠ y in 𝓝 1, embArch σ J w y = (List.ofFn fun i => η i (s y i)).prod := by
  atlas_forward_decl GlobalTheory.UAut.exists_coordSecondKind_arch
end

section
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut Filter Topology
open scoped TensorProduct ContDiff

namespace GlobalTheory.InfChartConcat

theorem concat {G X ι : Type*} [Monoid G] (l : Filter X) (P : (ℝ → G) → Prop)
    (d : ι → ℕ) (η : ∀ j, Fin (d j) → ℝ → G) (s : ∀ j, X → Fin (d j) → ℝ)
    (hP : ∀ j i, P (η j i)) (hs : ∀ j, Tendsto (s j) l (𝓝 0)) :
    ∀ L : List ι, ∃ (m : ℕ) (η' : Fin m → ℝ → G) (s' : X → Fin m → ℝ),
      (∀ i, P (η' i)) ∧ Tendsto s' l (𝓝 0) ∧
      ∀ x, (List.ofFn fun i => η' i (s' x i)).prod =
        (L.map fun j => (List.ofFn fun i => η j i (s j x i)).prod).prod
  | [] => ⟨0, Fin.elim0, fun _ => Fin.elim0, fun i => i.elim0,
      tendsto_pi_nhds.2 fun i => i.elim0, fun x => by simp⟩
  | j :: L => by
    obtain ⟨m, η', s', hP', hs', he⟩ := concat l P d η s hP hs L
    refine ⟨d j + m, Fin.append (η j) η', fun x => Fin.append (s j x) (s' x), ?_, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using hP j i
      · simpa using hP' i
    · rw [tendsto_pi_nhds]
      intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · have := ((continuous_apply i).tendsto _).comp (hs j)
        simpa [Function.comp_def] using this
      · have := ((continuous_apply i).tendsto _).comp hs'
        simpa [Function.comp_def] using this
    · intro x
      have hf : (fun i => Fin.append (η j) η' i (Fin.append (s j x) (s' x) i)) =
          Fin.append (fun i => η j i (s j x i)) (fun i => η' i (s' x i)) := by
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
      rw [hf, List.ofFn_fin_append, List.prod_append, he x]
      simp

theorem prod_map_ite_eq {ι M : Type*} [DecidableEq ι] [Monoid M] (u : ι) (a : M) (L : List ι) :
    (L.map fun w => if w = u then a else 1).prod = a ^ L.count u := by
  induction L with
  | nil => simp
  | cons w L ih =>
    simp only [List.map_cons, List.prod_cons, ih, List.count_cons]
    by_cases h : w = u
    · subst h; simp [pow_succ']
    · simp [h]

theorem decomp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {x : GAd σ J} (hx : x ∈ infPts σ J) :
    x = ((Finset.univ : Finset (InfinitePlace F)).toList.map
      fun w => embArch σ J w (projArch σ J w x)).prod := by
  classical
  apply GAd_ext σ J
  · intro u
    rw [map_list_prod, List.map_map]
    have hf : (projArch σ J u ∘ fun w => embArch σ J w (projArch σ J w x)) =
        fun w => if w = u then projArch σ J u x else 1 := by
      funext w
      by_cases h : w = u
      · subst h; simp
      · simp [h, projArch_embArch_ne σ J (Ne.symm h)]
    rw [hf, prod_map_ite_eq, List.count_eq_one_of_mem (Finset.nodup_toList _)
      (Finset.mem_toList.2 (Finset.mem_univ _)), pow_one]
  · intro v
    rw [map_list_prod, List.map_map, (mem_infPts_iff_forall).1 hx v]
    simp [Function.comp_def]

end GlobalTheory.InfChartConcat

theorem GlobalTheory.infPts_secondKind_chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
    IsHermND σ J → ∃ (m : ℕ) (η : Fin m → ℝ → GAd σ J) (s : GAd σ J → Fin m → ℝ),
    (∀ i, IsRealLine σ J (η i)) ∧ Tendsto s (𝓝[(infPts σ J : Set (GAd σ J))] 1) (𝓝 0) ∧
    ∀ᶠ x in 𝓝[(infPts σ J : Set (GAd σ J))] 1, x = (List.ofFn fun i => η i (s x i)).prod := by
  intro F E _ _ _ _ _ σ hCM n J hJ
  classical
  have hp := fun w => GlobalTheory.T.exists_secondKindCoordinates_unitaryArchimedeanPlace F E σ hCM n J hJ w
  choose d η s hη hs he using hp
  have hproj : ∀ w, Tendsto (projArch σ J w) (𝓝[(infPts σ J : Set (GAd σ J))] 1) (𝓝 1) := fun w => by
    have := (continuous_projArch σ J w).tendsto 1
    rw [map_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨m, η', s', hP', hs', heq⟩ := GlobalTheory.InfChartConcat.concat
    (𝓝[(infPts σ J : Set (GAd σ J))] 1) (IsRealLine σ J) d η
    (fun w x => s w (projArch σ J w x)) hη (fun w => (hs w).comp (hproj w))
    (Finset.univ : Finset (InfinitePlace F)).toList
  refine ⟨m, η', s', hP', hs', ?_⟩
  have hev : ∀ᶠ x in 𝓝[(infPts σ J : Set (GAd σ J))] 1, ∀ w, embArch σ J w (projArch σ J w x) =
      (List.ofFn fun i => η w i (s w (projArch σ J w x) i)).prod :=
    Filter.eventually_all.2 fun w => (hproj w).eventually (he w)
  filter_upwards [hev, self_mem_nhdsWithin] with x hx hmem
  rw [heq x, List.map_congr_left (fun w _ => (hx w).symm)]
  exact GlobalTheory.InfChartConcat.decomp σ J hmem
end

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut Filter Topology
open scoped TensorProduct ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondKindCoordinates_infiniteAdelicUnitaryPoints : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∃ (m : ℕ) (η : Fin m → ℝ → GAd σ J) (s : GAd σ J → Fin m → ℝ), (∀ i, IsRealLine σ J (η i)) ∧ Tendsto s (𝓝[(infPts σ J : Set (GAd σ J))] 1) (𝓝 0) ∧ ∀ᶠ x in 𝓝[(infPts σ J : Set (GAd σ J))] 1, x = (List.ofFn fun i => η i (s x i)).prod := by
  atlas_forward_decl GlobalTheory.infPts_secondKind_chart
end

section
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut Filter Topology
open scoped TensorProduct ContDiff

namespace GlobalTheory.DerCont

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem commute_isRealLine_finPts {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (t : ℝ) {k : GAd σ J}
    (hk : k ∈ finPts σ J) : Commute (γ t) k := by
  obtain ⟨w, τ, Z, -, hy⟩ := hγ
  obtain ⟨y, e, -⟩ := hy t
  rw [e]; exact commute_embArch σ J y (mem_finPts_iff_forall.1 hk w)

theorem foldr_lineDer_mul_level {φ : GAd σ J → ℂ} {U : Subgroup (GAd σ J)}
    (hφ : ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g) :
    ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      ∀ k ∈ U, k ∈ finPts σ J → ∀ g, l.foldr lineDer φ (g * k) = l.foldr lineDer φ g := by
  intro l
  induction l with
  | nil => intro _ k hk hk' g; exact hφ k hk hk' g
  | cons γ l ih =>
    intro hl k hk hk' g
    have hγ := hl γ List.mem_cons_self
    have ih' := ih (fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)) k hk hk'
    simp only [List.foldr_cons, lineDer]
    congr 1
    funext t
    rw [mul_assoc, ← (commute_isRealLine_finPts hγ t hk').eq, ← mul_assoc, ih']

theorem eventually_decomp {U : Subgroup (GAd σ J)} (hU : IsOpen (U : Set (GAd σ J))) (g₀ : GAd σ J) :
    Tendsto (fun g => ofInf σ J (projInf σ J (g₀⁻¹ * g))) (𝓝 g₀) (𝓝 1) ∧
    ∀ᶠ g in 𝓝 g₀, ofFin σ J (projFin σ J (g₀⁻¹ * g)) ∈ U ∧ ofFin σ J (projFin σ J (g₀⁻¹ * g)) ∈ finPts σ J := by
  have hc : Tendsto (fun g => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := by
    exact Continuous.tendsto' (by fun_prop) g₀ 1 (by simp)
  have h1 : Tendsto (fun h => ofInf σ J (projInf σ J h)) (𝓝 1) (𝓝 1) := by
    exact Continuous.tendsto' ((continuous_ofInf σ J).comp (continuous_projInf σ J)) 1 1 (by simp)
  have h2 : Tendsto (fun h => ofFin σ J (projFin σ J h)) (𝓝 1) (𝓝 1) := by
    exact Continuous.tendsto' ((continuous_ofFin σ J).comp (continuous_projFin σ J)) 1 1 (by simp)
  refine ⟨h1.comp hc, ?_⟩
  filter_upwards [(h2.comp hc).eventually (hU.mem_nhds U.one_mem)] with g hg
  exact ⟨hg, mem_finPts.2 (projInf_ofFin σ J _)⟩

theorem chart (h : IsCMExt F E σ) (hJ : IsHermND σ J) :
    ∃ (m : ℕ) (η : Fin m → ℝ → GAd σ J) (s : GAd σ J → Fin m → ℝ), (∀ i, IsRealLine σ J (η i)) ∧
      Tendsto s (𝓝[(infPts σ J : Set (GAd σ J))] 1) (𝓝 0) ∧
      ∀ᶠ x in 𝓝[(infPts σ J : Set (GAd σ J))] 1, x = (List.ofFn fun i => η i (s x i)).prod :=
  GlobalTheory.T.secondKindCoordinates_infiniteAdelicUnitaryPoints F E σ h n J hJ

theorem continuous_foldr_lineDer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ φ : GAd σ J → ℂ, (∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g) → Continuous φ → IsSm σ J φ → ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → Continuous (l.foldr lineDer φ) := by
  intro F E _ _ _ _ _ σ h n J hJ φ ⟨U, hU, hlev⟩ _ hsm l hl
  obtain ⟨m, η, s, hη, hs, hP⟩ := chart h hJ
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have hH : Continuous fun t : Fin m → ℝ => l.foldr lineDer φ (g₀ * (List.ofFn fun i => η i (t i)).prod) :=
    (GlobalTheory.ThK.RealLineGrowthDerivative.contDiff_foldr_lineDer hsm l hl m η hη g₀).continuous
  have hη0 : ∀ i, η i 0 = 1 := fun i => by
    have e := isRealLine_add F E σ h n J (η i) (hη i) 0 0
    rw [add_zero] at e
    exact left_eq_mul.1 e
  have h0 : (List.ofFn fun i => η i ((0 : Fin m → ℝ) i)).prod = 1 := by
    simp [hη0]
  obtain ⟨hx, hu⟩ := eventually_decomp hU g₀
  have hx' : Tendsto (fun g => ofInf σ J (projInf σ J (g₀⁻¹ * g))) (𝓝 g₀) (𝓝[(infPts σ J : Set (GAd σ J))] 1) :=
    tendsto_nhdsWithin_iff.2 ⟨hx, Eventually.of_forall fun g => mem_infPts.2 (projFin_ofInf σ J _)⟩
  have key : ∀ᶠ g in 𝓝 g₀, l.foldr lineDer φ (g₀ * (List.ofFn fun i =>
      η i (s (ofInf σ J (projInf σ J (g₀⁻¹ * g))) i)).prod) = l.foldr lineDer φ g := by
    filter_upwards [hu, hx'.eventually hP] with g hu' hP'
    rw [← hP']
    have e : g = g₀ * ofInf σ J (projInf σ J (g₀⁻¹ * g)) * ofFin σ J (projFin σ J (g₀⁻¹ * g)) := by
      rw [mul_assoc, ofInf_projInf_mul_ofFin_projFin, mul_inv_cancel_left]
    conv_rhs => rw [e]
    exact (foldr_lineDer_mul_level hlev l hl _ hu'.1 hu'.2 _).symm
  have lim := (hH.tendsto 0).comp (hs.comp hx')
  rw [h0, mul_one] at lim
  exact lim.congr' key

end GlobalTheory.DerCont
end

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_iteratedRealLineDeriv_unitaryAdelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ φ : GAd σ J → ℂ, (∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g) → Continuous φ → IsSm σ J φ → ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → Continuous (l.foldr lineDer φ) := by
  atlas_forward_decl GlobalTheory.DerCont.continuous_foldr_lineDer
end

section
section
open Matrix
open scoped Topology

noncomputable section

namespace GlobalTheory.UnitaryGroupChart

open Filter

theorem chart_general {E : Type} [NormedRing E] [NormedAlgebra ℝ E] [FiniteDimensional ℝ E]
    (σ : E →ₗ[ℝ] E) (hσ : ∀ a, σ (σ a) = a) (hm : ∀ a b, σ (a * b) = σ b * σ a) (h1 : σ 1 = 1)
    {d e : ℕ} (Z : Fin d → E) (j : Fin e → Fin d) (hZσ : ∀ a, σ (Z a) = -Z a)
    (hli : LinearIndependent ℝ (fun i => Z (j i)))
    (hsp : ∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range fun i => Z (j i))) :
    ∃ s : E → (Fin d → ℝ), ContinuousAt s 1 ∧
      ∀ᶠ g in 𝓝 (1 : E), σ g * g = 1 →
        g = (List.ofFn fun a => NormedSpace.exp (s g a • Z a)).prod := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℝ E
  have hexp : ∀ a, σ (NormedSpace.exp a) = NormedSpace.exp (σ a) := fun a => by
    have hp : ∀ m : ℕ, σ (a ^ m) = σ a ^ m := fun m => by
      induction m with
      | zero => simpa using h1
      | succ m ih => rw [pow_succ, hm, ih, pow_succ']
    have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a).map σ.toAddMonoidHom
      σ.continuous_of_finiteDimensional
    refine h2.unique ?_
    convert NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (σ a) using 1
    funext m
    simp [hp]
  let cL : (Fin e → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
    Fintype.linearCombination ℝ (fun i => Pi.single (j i) (1 : ℝ))
  let cC : (Fin e → ℝ) →L[ℝ] (Fin d → ℝ) := LinearMap.toContinuousLinearMap cL
  have hcC : ∀ t, cC t = cL t := fun _ => rfl
  have hsum : ∀ t : Fin e → ℝ, ∑ a, cL t a • Z a = ∑ i, t i • Z (j i) := fun t => by
    simp only [cL, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [ite_smul]
  set Θ : (Fin e → ℝ) → E :=
    fun t => (List.ofFn fun a => NormedSpace.exp (cL t a • Z a)).prod with hΘ
  have hU : ∀ t, σ (Θ t) * Θ t = 1 ∧ Θ t * σ (Θ t) = 1 := fun t =>
    GlobalTheory.UnitaryChart.unitary_list_prod σ hm h1 _ (fun u hu => by
      obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hu
      rw [hexp, map_smul, hZσ, smul_neg, ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_left,
        ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_right]
      simp)
  let T : (Fin e → ℝ) →L[ℝ] E :=
    ∑ a, (ContinuousLinearMap.toSpanSingleton ℝ (Z a)).comp ((ContinuousLinearMap.proj a).comp cC)
  have hT : ∀ t, T t = ∑ i, t i • Z (j i) := fun t => by
    rw [← hsum]
    simp [T, hcC]
  obtain ⟨h0, hD⟩ : Θ 0 = 1 ∧ HasStrictFDerivAt Θ T 0 :=
    GlobalTheory.UnitaryChart.hasStrictFDerivAt_ofFn_prod d
      (fun a (t : Fin e → ℝ) => NormedSpace.exp (cL t a • Z a)) _ (fun a => by
        refine ⟨by simp, ?_⟩
        have hd : HasStrictFDerivAt (fun s : ℝ => NormedSpace.exp (s • Z a))
            (ContinuousLinearMap.toSpanSingleton ℝ (Z a))
            (((ContinuousLinearMap.proj a).comp cC) 0) := by
          rw [map_zero]
          simpa using (hasStrictDerivAt_exp_smul_const (𝕂 := ℝ) (Z a) (0 : ℝ)).hasStrictFDerivAt
        exact hd.comp (0 : Fin e → ℝ) ((ContinuousLinearMap.proj a).comp cC).hasStrictFDerivAt)
  obtain ⟨P, hP1, hP2, hP3⟩ := GlobalTheory.UnitaryChart.exists_skew_coord σ (fun i => Z (j i)) hσ hli
    (fun i => hZσ (j i)) hsp
  have hΨ : HasStrictFDerivAt (fun t => P (Θ t))
      ((ContinuousLinearEquiv.refl ℝ (Fin e → ℝ) : (Fin e → ℝ) →L[ℝ] (Fin e → ℝ))) 0 := by
    refine (P.hasStrictFDerivAt.comp 0 hD).congr_fderiv ?_
    ext1 t
    simp [hT, hP1]
  have hP0 : P 1 = 0 := hP2 _ h1
  have hΨ0 : P (Θ 0) = 0 := by rw [h0, hP0]
  have p1 := hΨ.localInverse_continuousAt
  have p2 := hΨ.localInverse_apply_image
  have p3 := hΨ.eventually_right_inverse
  simp only [hΨ0] at p1 p2 p3
  set Ψ := hΨ.localInverse _ _ _
  have hσc : Continuous σ := σ.continuous_of_finiteDimensional
  have hnear : ∀ᶠ m in 𝓝 (1 : E), ‖1 - σ m‖ ≤ 1 / 2 := by
    have : ContinuousAt (fun m => ‖1 - σ m‖) 1 := (continuous_const.sub hσc).norm.continuousAt
    exact this.eventually_le_const (by simp [h1])
  have hPt : Tendsto P (𝓝 1) (𝓝 0) := hP0 ▸ P.continuous.tendsto 1
  have hcont : ContinuousAt (fun g => Ψ (P g)) 1 :=
    ContinuousAt.comp_of_eq p1 P.continuous.continuousAt hP0
  have ht : Tendsto (fun g => Θ (Ψ (P g))) (𝓝 1) (𝓝 1) := by
    have h3 : Tendsto (fun g => Ψ (P g)) (𝓝 1) (𝓝 0) := by
      have := hcont.tendsto
      simp only [hP0, p2] at this
      exact this
    have := hD.continuousAt.tendsto.comp h3
    rwa [h0] at this
  refine ⟨fun g => cL (Ψ (P g)), cC.continuous.continuousAt.comp hcont, ?_⟩
  filter_upwards [hPt.eventually p3, hnear, ht.eventually hnear] with g q1 q2 q3 hg1
  haveI : IsArtinianRing E := IsArtinianRing.of_finite ℝ E
  exact (GlobalTheory.UnitaryChart.eq_of_skew_eq (hU _).1 (mul_eq_one_comm.1 hg1) (hP3 _ _ q1) q3 q2).symm

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem chart_matrix (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hdet : IsUnit H.det)
    (d e : ℕ) (Z : Fin d → Matrix (Fin n) (Fin n) ℂ) (j : Fin e → Fin d)
    (hZ : ∀ a, (Z a)ᴴ * H + H * Z a = 0) (hli : LinearIndependent ℝ (fun i => Z (j i)))
    (hsp : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * H + H * X = 0 →
      X ∈ Submodule.span ℝ (Set.range fun i => Z (j i))) :
    ∃ s : Matrix (Fin n) (Fin n) ℂ → (Fin d → ℝ), ContinuousAt s 1 ∧
      ∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), gᴴ * H * g = H →
        g = (List.ofFn fun a => NormedSpace.exp (s g a • Z a)).prod := by
  have hHi : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hdet
  have hHi' : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hdet
  have hHih : (H⁻¹)ᴴ = H⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hH]
  let σ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun x => H⁻¹ * xᴴ * H
      map_add' := fun x y => by rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by simp [conjTranspose_smul] }
  have hs : ∀ x, σ x = H⁻¹ * xᴴ * H := fun _ => rfl
  have hσ : ∀ a, σ (σ a) = a := fun a => by
    simp only [hs, conjTranspose_mul, conjTranspose_conjTranspose, hH, hHih, Matrix.mul_assoc]
    rw [hHi, Matrix.mul_one, ← Matrix.mul_assoc, hHi, Matrix.one_mul]
  have hm : ∀ a b, σ (a * b) = σ b * σ a := fun a b => by
    simp only [hs, conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc H, hHi', Matrix.one_mul]
  have h1 : σ 1 = 1 := by simp [hs, hHi]
  have hZσ : ∀ a, σ (Z a) = -Z a := fun a => by
    rw [hs, Matrix.mul_assoc, eq_neg_of_add_eq_zero_left (hZ a), Matrix.mul_neg, ← Matrix.mul_assoc,
      hHi, Matrix.one_mul]
  have hsp' : ∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range fun i => Z (j i)) := fun X hX => by
    apply hsp
    have h2 : H * σ X = Xᴴ * H := by
      rw [hs, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hHi', Matrix.one_mul]
    rw [← h2, hX, Matrix.mul_neg, neg_add_cancel]
  obtain ⟨s, hs1, hs2⟩ := chart_general σ hσ hm h1 Z j hZσ hli hsp'
  refine ⟨s, hs1, ?_⟩
  filter_upwards [hs2] with g hg hgu
  apply hg
  simp only [Matrix.mul_assoc] at hgu
  rw [hs, Matrix.mul_assoc, Matrix.mul_assoc, hgu, hHi]

end

theorem unitary_chart : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), Hᴴ = H → IsUnit H.det →
    ∀ (d e : ℕ) (Z : Fin d → Matrix (Fin n) (Fin n) ℂ) (j : Fin e → Fin d), Function.Injective j →
      (∀ a, a ∉ Set.range j → Z a = 0) → (∀ a, (Z a)ᴴ * H + H * Z a = 0) →
      LinearIndependent ℝ (fun i => Z (j i)) →
      (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * H + H * X = 0 → X ∈ Submodule.span ℝ (Set.range fun i => Z (j i))) →
      ∃ V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∃ s : Matrix (Fin n) (Fin n) ℂ → (Fin d → ℝ), ContinuousAt s 1 ∧
        ∀ g ∈ V, gᴴ * H * g = H → g = (List.ofFn fun a => NormedSpace.exp (s g a • Z a)).prod := by
  intro n H hH hdet d e Z j _ _ hZ hli hsp
  obtain ⟨s, hs1, hs2⟩ := chart_matrix n H hH hdet d e Z j hZ hli hsp
  exact ⟨_, hs2, s, hs1, fun g hg => hg⟩

end GlobalTheory.UnitaryGroupChart
end
end

open Matrix
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_unitary_group_one_parameter_chart : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), Hᴴ = H → IsUnit H.det →
    ∀ (d e : ℕ) (Z : Fin d → Matrix (Fin n) (Fin n) ℂ) (j : Fin e → Fin d), Function.Injective j →
      (∀ a, a ∉ Set.range j → Z a = 0) → (∀ a, (Z a)ᴴ * H + H * Z a = 0) →
      LinearIndependent ℝ (fun i => Z (j i)) →
      (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * H + H * X = 0 → X ∈ Submodule.span ℝ (Set.range fun i => Z (j i))) →
      ∃ V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∃ s : Matrix (Fin n) (Fin n) ℂ → (Fin d → ℝ), ContinuousAt s 1 ∧
        ∀ g ∈ V, gᴴ * H * g = H → g = (List.ofFn fun a => NormedSpace.exp (s g a • Z a)).prod := by
  atlas_forward_decl GlobalTheory.UnitaryGroupChart.unitary_chart
end

section
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff Topology

noncomputable section

namespace GlobalTheory.UnitChart

open GlobalTheory.Orb (archMat)

def lieU {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | Xᴴ * H + H * X = 0}
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at *
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_setOf_eq] at *
    rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, hX, smul_zero]

theorem exists_realLines_chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∃ (d : ℕ) (δ : Fin d → ℝ → GAd σ J), (∀ a, IsRealLine σ J (δ a)) ∧
      ∀ U ∈ 𝓝 (1 : GAd σ J), ∃ W ∈ 𝓝 (1 : GAd σ J), ∃ s : GAd σ J → (Fin d → ℝ), ContinuousAt s 1 ∧
        ∀ y ∈ W, ∃ u ∈ U, u ∈ finPts σ J ∧ y = (List.ofFn fun a => δ a (s y a)).prod * u := by
  intro F E _ _ _ _ _ σ h n J hJ
  classical
  let τ : ∀ w : InfinitePlace F, EmbOver E w := fun w => Classical.choice inferInstance
  let H : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ := fun w => J.map (τ w).1
  have hHu : ∀ w, IsUnit (H w).det := fun w => by
    show IsUnit (J.map (τ w).1).det
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ hJ.2).map _
  have hHh : ∀ w, (H w)ᴴ = H w := fun w => by
    ext i k
    simp only [H, conjTranspose_apply, map_apply]
    rw [← h.2.2.2, hJ.1 i k]
  let e : InfinitePlace F → ℕ := fun w => Module.finrank ℝ (lieU (H w))
  let b : ∀ w, Module.Basis (Fin (e w)) ℝ (lieU (H w)) := fun w => Module.finBasis ℝ _
  let q : (Σ w : InfinitePlace F, Fin (e w)) ≃ Fin (Fintype.card (Σ w : InfinitePlace F, Fin (e w))) :=
    Fintype.equivFin _
  let Zg : Fin (Fintype.card (Σ w : InfinitePlace F, Fin (e w))) → Matrix (Fin n) (Fin n) ℂ :=
    fun a => (b (q.symm a).1 (q.symm a).2 : Matrix (Fin n) (Fin n) ℂ)
  have hZg : ∀ a, (Zg a)ᴴ * H (q.symm a).1 + H (q.symm a).1 * Zg a = 0 := fun a => (b (q.symm a).1 (q.symm a).2).2
  have hy : ∀ a (t : ℝ), ∃ y : GArch σ J (q.symm a).1,
      archMat σ J (τ (q.symm a).1) y = NormedSpace.exp (t • Zg a) := fun a t => by
    obtain ⟨u, hu⟩ := Matrix.isUnit_exp (t • Zg a)
    have h1 := GlobalTheory.SmoothForms.exp_mem_UH (hHu (q.symm a).1) (X := t • Zg a) ((lieU (H (q.symm a).1)).smul_mem t (hZg a))
    refine ⟨(archEquiv J h (τ (q.symm a).1)).symm ⟨u, show _ * _ * _ = _ from hu ▸ h1⟩, ?_⟩
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, MulEquiv.apply_symm_apply]
    exact hu
  choose y hy using hy
  let δ : Fin (Fintype.card (Σ w : InfinitePlace F, Fin (e w))) → ℝ → GAd σ J :=
    fun a t => embArch σ J (q.symm a).1 (y a t)
  let Zw : InfinitePlace F → Fin (Fintype.card (Σ w : InfinitePlace F, Fin (e w))) → Matrix (Fin n) (Fin n) ℂ :=
    fun w a => if (q.symm a).1 = w then Zg a else 0
  have hK : ∀ w a (t : ℝ), archMat σ J (τ w) (projArch σ J w (δ a t)) = NormedSpace.exp (t • Zw w a) := by
    intro w a t
    by_cases hw : (q.symm a).1 = w
    · subst hw
      simp only [δ, Zw, if_pos rfl, projArch_embArch_self, hy]
    · simp only [δ, Zw, if_neg hw, smul_zero, NormedSpace.exp_zero, projArch_embArch_ne σ J (Ne.symm hw), map_one]
  have hunit : ∀ w (g : GArch σ J w), (archMat σ J (τ w) g)ᴴ * H w * archMat σ J (τ w) g = H w := fun w g => by
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h]
    exact (archEquiv J h (τ w) g).2
  have hinj : ∀ w, Function.Injective (archMat σ J (τ w)) := fun w g g' hg =>
    (archEquiv J h (τ w)).injective (Subtype.ext (Units.ext (by
      rwa [GlobalTheory.Orb.archMat_eq_archEquiv J h, GlobalTheory.Orb.archMat_eq_archEquiv J h] at hg)))
  have hloc : ∀ w, ∃ V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∃ s : Matrix (Fin n) (Fin n) ℂ → (Fin _ → ℝ),
      ContinuousAt s 1 ∧ ∀ g ∈ V, gᴴ * H w * g = H w → g = (List.ofFn fun a => NormedSpace.exp (s g a • Zw w a)).prod := by
    intro w
    have hj : Function.Injective fun i : Fin (e w) => q ⟨w, i⟩ := fun i i' hi => by
      simpa using q.injective hi
    have hZj : ∀ i, Zw w (q ⟨w, i⟩) = (b w i : Matrix (Fin n) (Fin n) ℂ) := fun i => by
      show (if (q.symm (q ⟨w, i⟩)).1 = w then Zg (q ⟨w, i⟩) else 0) = _
      rw [if_pos (by simp)]
      show ((b (q.symm (q ⟨w, i⟩)).1 (q.symm (q ⟨w, i⟩)).2 : Matrix (Fin n) (Fin n) ℂ)) = _
      rw [q.symm_apply_apply]
    refine GlobalTheory.T.hermitian_unitary_group_one_parameter_chart n (H w) (hHh w) (hHu w) _ (e w) (Zw w) (fun i => q ⟨w, i⟩) hj ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Zw]
      rw [if_neg]
      intro hw
      apply ha
      rcases hqa : q.symm a with ⟨w', i⟩
      rw [hqa] at hw
      subst hw
      have h2 := congrArg q hqa
      rw [Equiv.apply_symm_apply] at h2
      exact ⟨i, h2.symm⟩
    · intro a
      simp only [Zw]
      split_ifs with hw
      · subst hw; exact hZg a
      · simp
    · simp only [hZj]
      refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
      refine Fintype.linearIndependent_iff.1 (b w).linearIndependent c (Subtype.ext ?_) i
      simpa using hc
    · intro X hX
      simp only [hZj]
      have e1 := congrArg Subtype.val ((b w).sum_repr ⟨X, hX⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at e1
      rw [← e1]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  choose V hV sw hsw hdec using hloc
  let gw : InfinitePlace F → GAd σ J → Matrix (Fin n) (Fin n) ℂ := fun w x => archMat σ J (τ w) (projArch σ J w x)
  have hgc : ∀ w, Continuous (gw w) := fun w =>
    (GlobalTheory.Orb.continuous_archMat σ J (τ w)).comp (continuous_projArch σ J w)
  have hg1 : ∀ w, gw w 1 = 1 := fun w => by simp [gw]
  refine ⟨_, δ, fun a => ⟨(q.symm a).1, τ _, Zg a, hZg a, fun t => ⟨y a t, rfl, hy a t⟩⟩, fun U hU => ?_⟩
  have hfc : Continuous fun x => ofFin σ J (projFin σ J x) := (continuous_ofFin σ J).comp (continuous_projFin σ J)
  refine ⟨{x | ∀ w, gw w x ∈ V w} ∩ {x | ofFin σ J (projFin σ J x) ∈ U}, ?_,
    fun x a => sw (q.symm a).1 (gw (q.symm a).1 x) a, ?_, ?_⟩
  · refine Filter.inter_mem (Filter.eventually_all.2 fun w => (hgc w).continuousAt.preimage_mem_nhds ?_)
      (hfc.continuousAt.preimage_mem_nhds ?_)
    · rw [hg1]; exact hV w
    · simpa using hU
  · exact continuousAt_pi.2 fun a =>
      (continuous_apply a).continuousAt.comp ((hsw _).comp_of_eq (hgc _).continuousAt (hg1 _))
  · intro x hx
    refine ⟨ofFin σ J (projFin σ J x), hx.2, mem_finPts.2 (projInf_ofFin _ _ _), ?_⟩
    conv_lhs => rw [← ofInf_projInf_mul_ofFin_projFin σ J x]
    congr 1
    apply GAd_ext σ J
    · intro w
      apply hinj w
      rw [projArch_ofInf, projInfArch_projInf, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
      have e2 : (⇑(archMat σ J (τ w)) ∘ ⇑(projArch σ J w) ∘ fun a => δ a (sw (q.symm a).1 (gw (q.symm a).1 x) a)) =
          fun a => NormedSpace.exp (sw w (gw w x) a • Zw w a) := funext fun a => by
        simp only [Function.comp_apply]
        rw [hK]
        by_cases hw : (q.symm a).1 = w
        · subst hw; rfl
        · simp [Zw, hw]
      rw [e2]
      exact hdec w _ (hx.1 w) (hunit w _)
    · intro v
      rw [proj_ofInf, map_list_prod, List.map_ofFn]
      have e3 : (⇑(proj σ J v) ∘ fun a => δ a (sw (q.symm a).1 (gw (q.symm a).1 x) a)) = fun _ => 1 :=
        funext fun a => by simp [δ]
      rw [e3]
      simp

end GlobalTheory.UnitChart
end
end

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realOneParamProduct_chart_adelicUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∃ (d : ℕ) (δ : Fin d → ℝ → GAd σ J), (∀ a, IsRealLine σ J (δ a)) ∧
      ∀ U ∈ 𝓝 (1 : GAd σ J), ∃ W ∈ 𝓝 (1 : GAd σ J), ∃ s : GAd σ J → (Fin d → ℝ), ContinuousAt s 1 ∧
        ∀ y ∈ W, ∃ u ∈ U, u ∈ finPts σ J ∧ y = (List.ofFn fun a => δ a (s y a)).prod * u := by
  atlas_forward_decl GlobalTheory.UnitChart.exists_realLines_chart
end

section
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff Topology

noncomputable section

namespace GlobalTheory.UAut.JointDer

theorem prod_ofFn_append {G : Type} [Monoid G] {d k : ℕ} (δ : Fin d → ℝ → G) (γ : Fin k → ℝ → G) (s : Fin d → ℝ)
    (t : Fin k → ℝ) :
    (List.ofFn fun i => Fin.append δ γ i (Fin.append s t i)).prod =
      (List.ofFn fun a => δ a (s a)).prod * (List.ofFn fun i => γ i (t i)).prod := by
  have e : (fun i => Fin.append δ γ i (Fin.append s t i)) = Fin.append (fun a => δ a (s a)) (fun i => γ i (t i)) := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun j => ?_) i <;> simp [Fin.append_left, Fin.append_right]
  rw [e, List.ofFn_fin_append, List.prod_append]

theorem contDiff_append {d k : ℕ} : ContDiff ℝ ∞ fun q : (Fin d → ℝ) × (Fin k → ℝ) => Fin.append q.1 q.2 := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.addCases (fun a => ?_) (fun j => ?_) i
  · simp only [Fin.append_left]; exact (contDiff_apply ℝ ℝ a).comp contDiff_fst
  · simp only [Fin.append_right]; exact (contDiff_apply ℝ ℝ j).comp contDiff_snd

theorem iteratedFDeriv_slice {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] {H : A × B → ℂ} (hH : ContDiff ℝ ∞ H) (m : ℕ) (a : A) (t : B) :
    iteratedFDeriv ℝ m (fun t => H (a, t)) t =
      (iteratedFDeriv ℝ m H (a, t)).compContinuousLinearMap fun _ => ContinuousLinearMap.inr ℝ A B := by
  have e : (fun t => H (a, t)) = (fun q => H ((a, 0) + q)) ∘ ContinuousLinearMap.inr ℝ A B := by
    funext t; simp
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _
    (show ContDiff ℝ ∞ fun q => H ((a, 0) + q) from hH.comp (contDiff_const.add contDiff_id)) _
    (by exact_mod_cast le_top), iteratedFDeriv_comp_add_left]
  simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem commute_prod_realLine {k : ℕ} {γ : Fin k → ℝ → GAd σ J} (hγ : ∀ i, IsRealLine σ J (γ i)) (t : Fin k → ℝ)
    {u : GAd σ J} (hu : u ∈ finPts σ J) : Commute (List.ofFn fun i => γ i (t i)).prod u := by
  refine Commute.list_prod_left _ _ fun x hx => ?_
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  obtain ⟨w, τ, Z, -, h⟩ := hγ i
  obtain ⟨y, e, -⟩ := h (t i)
  show Commute (γ i (t i)) u
  rw [e]
  exact commute_embArch σ J y (mem_finPts_iff_forall.1 hu w)

end GlobalTheory.UAut.JointDer

open GlobalTheory.UAut.JointDer in

theorem GlobalTheory.UAut.continuous_iteratedFDeriv_prod_realLine : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (d : ℕ) (δ : Fin d → ℝ → GAd σ J), (∀ a, IsRealLine σ J (δ a)) → (∀ U ∈ 𝓝 (1 : GAd σ J), ∃ W ∈ 𝓝 (1 : GAd σ J), ∃ s : GAd σ J → (Fin d → ℝ), ContinuousAt s 1 ∧ ∀ y ∈ W, ∃ u ∈ U, u ∈ finPts σ J ∧ y = (List.ofFn fun a => δ a (s y a)).prod * u) → ∀ φ : GAd σ J → ℂ, (∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g) → IsSm σ J φ → ∀ (k : ℕ) (γ : Fin k → ℝ → GAd σ J), (∀ i, IsRealLine σ J (γ i)) → ∀ m : ℕ, Continuous fun p : GAd σ J × (Fin k → ℝ) => iteratedFDeriv ℝ m (fun t : Fin k → ℝ => φ (p.1 * (List.ofFn fun i => γ i (t i)).prod)) p.2 := by
  intro F E _ _ _ _ _ σ _ n J _ d δ hδ hchart φ hlev hsm k γ hγ m
  obtain ⟨U, hUo, hU⟩ := hlev
  obtain ⟨W, hW, s, hs, hWs⟩ := hchart _ (hUo.mem_nhds U.one_mem)
  set P : (Fin k → ℝ) → GAd σ J := fun t => (List.ofFn fun i => γ i (t i)).prod with hP
  set Q : (Fin d → ℝ) → GAd σ J := fun s => (List.ofFn fun a => δ a (s a)).prod with hQ
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨x₀, t₀⟩ := p₀
  let H : (Fin d → ℝ) × (Fin k → ℝ) → ℂ := fun q => φ (x₀ * (Q q.1 * P q.2))
  have hH : ContDiff ℝ ∞ H := by
    have h1 := hsm (d + k) (Fin.append δ γ)
      (fun i => Fin.addCases (fun a => by simpa [Fin.append_left] using hδ a)
        (fun j => by simpa [Fin.append_right] using hγ j) i) x₀
    have h2 := h1.comp contDiff_append
    convert h2 using 1
    funext q
    simp only [Function.comp_apply, H, prod_ofFn_append, hP, hQ]
  have key : ∀ x, x₀⁻¹ * x ∈ W → ∀ t, φ (x * P t) = H (s (x₀⁻¹ * x), t) := by
    intro x hx t
    obtain ⟨u, huU, huf, e⟩ := hWs _ hx
    have hc : Commute (P t) u := commute_prod_realLine hγ t huf
    have hx' : x = x₀ * (Q (s (x₀⁻¹ * x)) * u) := by
      simp only [hQ]
      rw [← e]
      group
    calc φ (x * P t) = φ (x₀ * (Q (s (x₀⁻¹ * x)) * u) * P t) := by rw [← hx']
      _ = φ ((x₀ * (Q (s (x₀⁻¹ * x)) * P t)) * u) := by
          congr 1
          simp only [mul_assoc]
          rw [hc.eq]
      _ = H (s (x₀⁻¹ * x), t) := hU u huU huf _
  have hev : ∀ᶠ p : GAd σ J × (Fin k → ℝ) in 𝓝 (x₀, t₀),
      (iteratedFDeriv ℝ m H (s (x₀⁻¹ * p.1), p.2)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ (Fin d → ℝ) (Fin k → ℝ)) =
      iteratedFDeriv ℝ m (fun t => φ (p.1 * P t)) p.2 := by
    have hmem : {p : GAd σ J × (Fin k → ℝ) | x₀⁻¹ * p.1 ∈ W} ∈ 𝓝 (x₀, t₀) :=
      (continuous_const.mul continuous_fst).continuousAt.preimage_mem_nhds (by simpa using hW)
    filter_upwards [hmem] with p hp
    rw [← iteratedFDeriv_slice hH, show (fun t => φ (p.1 * P t)) = fun t => H (s (x₀⁻¹ * p.1), t) from
      funext (key p.1 hp)]
  refine ContinuousAt.congr ?_ hev
  have hcont : Continuous fun q => (iteratedFDeriv ℝ m H q).compContinuousLinearMap
      (fun _ => ContinuousLinearMap.inr ℝ (Fin d → ℝ) (Fin k → ℝ)) :=
    (ContinuousMultilinearMap.continuous_precomp _).comp (hH.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  have hsx : ContinuousAt (fun p : GAd σ J × (Fin k → ℝ) => s (x₀⁻¹ * p.1)) (x₀, t₀) :=
    hs.comp_of_eq (continuous_const.mul continuous_fst).continuousAt (by simp)
  exact hcont.continuousAt.comp (hsx.prodMk continuousAt_snd)

end
end

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_iteratedFDeriv_realOneParamProduct_levelFunction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (d : ℕ) (δ : Fin d → ℝ → GAd σ J), (∀ a, IsRealLine σ J (δ a)) → (∀ U ∈ 𝓝 (1 : GAd σ J), ∃ W ∈ 𝓝 (1 : GAd σ J), ∃ s : GAd σ J → (Fin d → ℝ), ContinuousAt s 1 ∧ ∀ y ∈ W, ∃ u ∈ U, u ∈ finPts σ J ∧ y = (List.ofFn fun a => δ a (s y a)).prod * u) → ∀ φ : GAd σ J → ℂ, (∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g) → IsSm σ J φ → ∀ (k : ℕ) (γ : Fin k → ℝ → GAd σ J), (∀ i, IsRealLine σ J (γ i)) → ∀ m : ℕ, Continuous fun p : GAd σ J × (Fin k → ℝ) => iteratedFDeriv ℝ m (fun t : Fin k → ℝ => φ (p.1 * (List.ofFn fun i => γ i (t i)).prod)) p.2 := by
  atlas_forward_decl GlobalTheory.UAut.continuous_iteratedFDeriv_prod_realLine
end

section
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff Topology

noncomputable section

namespace GlobalTheory.Cusp.SmoothParam

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ N : Subgroup G} [DiscreteTopology Γ] [LocallyCompactSpace N]

omit [SecondCountableTopology G] [DiscreteTopology Γ] [LocallyCompactSpace N] in

theorem aestronglyMeasurable_out {E : Type} [NormedAddCommGroup E] [SecondCountableTopology E]
    {Φ : G → E} (hΦ : Continuous Φ) (hinv : ∀ γ ∈ Γ, ∀ x, Φ (γ * x) = Φ x) (g : G)
    (μ : Measure (Quot (Γ.subgroupOf N))) :
    AEStronglyMeasurable (fun q : Quot (Γ.subgroupOf N) => Φ ((q.out : N) * g)) μ := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  have hl : LeftInv (Γ.subgroupOf N) (fun n : N => Φ (n * g)) := fun γ hγ n => by
    simp only [Subgroup.coe_mul, mul_assoc]; exact hinv _ hγ _
  have hm : Measurable (fun n : N => Φ (n * g)) :=
    (hΦ.comp ((continuous_subtype_val).mul continuous_const)).measurable
  have hq : Measurable (descend (Γ.subgroupOf N) (fun n : N => Φ (n * g))) := by
    refine measurable_from_quotient.2 ?_
    have e : (descend (Γ.subgroupOf N) (fun n : N => Φ (n * g))) ∘ Quotient.mk'' = fun n : N => Φ (n * g) :=
      hl.lift_descend
    rw [e]; exact hm
  exact hq.aestronglyMeasurable

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [DiscreteTopology Γ] [LocallyCompactSpace N] in

theorem exists_bound {T E : Type} [TopologicalSpace T] [NormedAddCommGroup E] (hc : Cocompact Γ N)
    {Ψ : G → T → E} (hΨ : Continuous fun p : G × T => Ψ p.1 p.2) (hinv : ∀ γ ∈ Γ, ∀ x t, Ψ (γ * x) t = Ψ x t)
    (g : G) {S : Set T} (hS : IsCompact S) : ∃ C, ∀ (n : N) t, t ∈ S → ‖Ψ (n * g) t‖ ≤ C := by
  obtain ⟨K, hK, hs⟩ := hc
  obtain ⟨C, hC⟩ := (hK.prod hS).exists_bound_of_continuousOn (f := fun p : N × T => Ψ (p.1 * g) p.2)
    (hΨ.comp (((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk continuous_snd)).continuousOn
  refine ⟨C, fun n t ht => ?_⟩
  obtain ⟨γ, hγ, hk⟩ := hs n
  have e : Ψ (((γ * n : N) : G) * g) t = Ψ (n * g) t := by
    simp only [Subgroup.coe_mul, mul_assoc]; exact hinv _ hγ _ _
  exact e ▸ hC (γ * n, t) ⟨hk, ht⟩

theorem hasFDerivAt_param {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hc : Cocompact Γ N) (H : G → (Fin k → ℝ) → E)
    (hinv : ∀ γ ∈ Γ, ∀ x t, H (γ * x) t = H x t) (hd : ∀ x, Differentiable ℝ (H x))
    (h0 : Continuous fun p : G × (Fin k → ℝ) => H p.1 p.2)
    (h1 : Continuous fun p : G × (Fin k → ℝ) => fderiv ℝ (H p.1) p.2) (g : G) (t₀ : Fin k → ℝ) :
    HasFDerivAt (fun t => ∫ q, H ((q.out : N) * g) t ∂probMeasure Γ N)
      (∫ q, fderiv ℝ (H ((q.out : N) * g)) t₀ ∂probMeasure Γ N) t₀ := by
  have := hc.isProbabilityMeasure
  have hinv' : ∀ γ ∈ Γ, ∀ x t, fderiv ℝ (H (γ * x)) t = fderiv ℝ (H x) t := fun γ hγ x t => by
    rw [show H (γ * x) = H x from funext (hinv γ hγ x)]
  obtain ⟨C, hC⟩ := exists_bound (Ψ := fun x t => fderiv ℝ (H x) t) hc h1 hinv' g (isCompact_closedBall t₀ 1)
  obtain ⟨C0, hC0⟩ := exists_bound (Ψ := H) hc h0 hinv g (isCompact_closedBall t₀ 1)
  have hm : ∀ t, AEStronglyMeasurable (fun q : Quot (Γ.subgroupOf N) => H ((q.out : N) * g) t) (probMeasure Γ N) :=
    fun t => aestronglyMeasurable_out (Φ := fun x => H x t) (h0.comp (continuous_id.prodMk continuous_const))
      (fun γ hγ x => hinv γ hγ x t) g _
  have hm' : AEStronglyMeasurable (fun q : Quot (Γ.subgroupOf N) => fderiv ℝ (H ((q.out : N) * g)) t₀)
      (probMeasure Γ N) :=
    aestronglyMeasurable_out (Φ := fun x => fderiv ℝ (H x) t₀) (h1.comp (continuous_id.prodMk continuous_const))
      (fun γ hγ x => hinv' γ hγ x t₀) g _
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
    (Metric.ball_mem_nhds t₀ one_pos) (.of_forall hm)
    (Integrable.of_bound (hm t₀) C0 (.of_forall fun q => hC0 _ t₀ (Metric.mem_closedBall_self zero_le_one))) hm'
    (.of_forall fun q t ht => hC _ t (Metric.ball_subset_closedBall ht)) (integrable_const C)
    (.of_forall fun q t _ => (hd _ t).hasFDerivAt)

omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in

theorem iteratedFDeriv_fderiv_eq {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin k → ℝ) → E) (m : ℕ) (t : Fin k → ℝ) :
    iteratedFDeriv ℝ m (fderiv ℝ f) t =
      (continuousMultilinearCurryRightEquiv' ℝ m (Fin k → ℝ) E) (iteratedFDeriv ℝ (m + 1) f t) := by
  rw [iteratedFDeriv_succ_eq_comp_right]
  simp

omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in

theorem continuous_of_iteratedFDeriv_zero {X : Type} [TopologicalSpace X] {k : ℕ} {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : X → (Fin k → ℝ) → E}
    (h : Continuous fun p : X × (Fin k → ℝ) => iteratedFDeriv ℝ 0 (H p.1) p.2) :
    Continuous fun p : X × (Fin k → ℝ) => H p.1 p.2 := by
  have e : (fun p : X × (Fin k → ℝ) => H p.1 p.2) =
      fun p => continuousMultilinearCurryFin0 ℝ (Fin k → ℝ) E (iteratedFDeriv ℝ 0 (H p.1) p.2) := by
    funext p; simp [continuousMultilinearCurryFin0_apply, iteratedFDeriv_zero_apply]
  rw [e]; exact (continuousMultilinearCurryFin0 ℝ (Fin k → ℝ) E).continuous.comp h

theorem contDiff_param (hc : Cocompact Γ N) (g : G) {k : ℕ} (n : ℕ) :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (H : G → (Fin k → ℝ) → E),
      (∀ γ ∈ Γ, ∀ x t, H (γ * x) t = H x t) → (∀ x, ContDiff ℝ ∞ (H x)) →
      (∀ m : ℕ, Continuous fun p : G × (Fin k → ℝ) => iteratedFDeriv ℝ m (H p.1) p.2) →
      ContDiff ℝ n fun t => ∫ q, H ((q.out : N) * g) t ∂probMeasure Γ N := by
  induction n with
  | zero =>
    intro E _ _ _ H hinv hs hm
    have h1 : Continuous fun p : G × (Fin k → ℝ) => fderiv ℝ (H p.1) p.2 := by
      refine continuous_of_iteratedFDeriv_zero (H := fun x => fderiv ℝ (H x)) ?_
      simp only [iteratedFDeriv_fderiv_eq]
      exact (continuousMultilinearCurryRightEquiv' ℝ 0 (Fin k → ℝ) E).continuous.comp (hm 1)
    refine contDiff_zero.2 (continuous_iff_continuousAt.2 fun t => ?_)
    exact (hasFDerivAt_param hc H hinv (fun x => (hs x).differentiable (by simp))
      (continuous_of_iteratedFDeriv_zero (hm 0)) h1 g t).continuousAt
  | succ n ih =>
    intro E _ _ _ H hinv hs hm
    have hm' : ∀ m : ℕ, Continuous fun p : G × (Fin k → ℝ) => iteratedFDeriv ℝ m (fderiv ℝ (H p.1)) p.2 := by
      intro m
      simp only [iteratedFDeriv_fderiv_eq]
      exact (continuousMultilinearCurryRightEquiv' ℝ m (Fin k → ℝ) E).continuous.comp (hm (m + 1))
    have hinv' : ∀ γ ∈ Γ, ∀ x t, fderiv ℝ (H (γ * x)) t = fderiv ℝ (H x) t := fun γ hγ x t => by
      rw [show H (γ * x) = H x from funext (hinv γ hγ x)]
    refine contDiff_succ_iff_hasFDerivAt.2 ⟨_, ih (fun x => fderiv ℝ (H x)) hinv'
      (fun x => (contDiff_infty_iff_fderiv.1 (hs x)).2) hm', fun t => ?_⟩
    exact hasFDerivAt_param hc H hinv (fun x => (contDiff_infty_iff_fderiv.1 (hs x)).1)
      (continuous_of_iteratedFDeriv_zero (hm 0))
      (continuous_of_iteratedFDeriv_zero (H := fun x => fderiv ℝ (H x)) (hm' 0)) g t

end GlobalTheory.Cusp.SmoothParam

theorem GlobalTheory.Cusp.contDiff_constTermOn_param : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ N : Subgroup G} [DiscreteTopology Γ]
    [LocallyCompactSpace N], GlobalTheory.Cusp.Cocompact Γ N → ∀ {k : ℕ} (F : G → (Fin k → ℝ) → ℂ),
    (∀ γ ∈ Γ, ∀ x t, F (γ * x) t = F x t) → (∀ x, ContDiff ℝ ∞ (F x)) →
    (∀ m : ℕ, Continuous fun p : G × (Fin k → ℝ) => iteratedFDeriv ℝ m (F p.1) p.2) →
    ∀ g : G, ContDiff ℝ ∞ fun t => GlobalTheory.Cusp.constTermOn Γ N (fun x => F x t) g := by
  intro G _ _ _ _ _ _ Γ N _ _ hc k F hinv hs hm g
  exact contDiff_infty.2 fun n => GlobalTheory.Cusp.SmoothParam.contDiff_param hc g n F hinv hs hm
end
end

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_constantTermCocompact_smoothParameterFamily : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ N : Subgroup G} [DiscreteTopology Γ] [LocallyCompactSpace N], GlobalTheory.Cusp.Cocompact Γ N → ∀ {k : ℕ} (F : G → (Fin k → ℝ) → ℂ), (∀ γ ∈ Γ, ∀ x t, F (γ * x) t = F x t) → (∀ x, ContDiff ℝ ∞ (F x)) → (∀ m : ℕ, Continuous fun p : G × (Fin k → ℝ) => iteratedFDeriv ℝ m (F p.1) p.2) → ∀ g : G, ContDiff ℝ ∞ fun t => GlobalTheory.Cusp.constTermOn Γ N (fun x => F x t) g := by
  atlas_forward_decl GlobalTheory.Cusp.contDiff_constTermOn_param
end

section
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff Topology

namespace GlobalTheory.ConstTermSmooth

theorem isSm_of_isConstTermOn : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ)
    (C : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ), IsIsoCols σ J C → ∀ (H K : Subgroup (GAd σ J)) (φ c : GAd σ J → ℂ),
    ratPts σ J ⊓ parFlag σ J C d ≤ H → IsAutOn σ J H K φ → IsConstTermOn σ J (unipFlag σ J C d) φ c → IsSm σ J c := by
  intro F E _ _ _ _ _ σ h n J hJ r C d hC H K φ c hH hφ hc
  haveI := locallyCompact_unipFlag hJ (sigma_sigma h) hC d
  have hl : GlobalTheory.AutomorphicL2Unitary.LeftInv (ratPts σ J ⊓ parFlag σ J C d) φ := fun γ hγ => hφ.left γ (hH hγ)
  obtain ⟨hco, e⟩ := hc.eq_constTermOn_par h hJ hC hl
  obtain ⟨dd, δ, hδ, hW⟩ := GlobalTheory.T.exists_realOneParamProduct_chart_adelicUnitary F E σ h n J hJ
  intro k γ hγ g
  have := GlobalTheory.T.contDiff_constantTermCocompact_smoothParameterFamily hco (fun x t => φ (x * (List.ofFn fun i => γ i (t i)).prod))
    (fun γ' hγ' x t => by simp only [mul_assoc]; exact hl γ' hγ' _) (fun x => hφ.smooth k γ hγ x)
    (GlobalTheory.T.continuous_iteratedFDeriv_realOneParamProduct_levelFunction F E σ h n J hJ dd δ hδ hW φ hφ.level hφ.smooth k γ hγ) g
  simpa [e, GlobalTheory.Cusp.constTermOn_mul_right] using this

end GlobalTheory.ConstTermSmooth

end
end

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_smooth_parabolic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (C : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ), IsIsoCols σ J C → ∀ (H K : Subgroup (GAd σ J)) (φ c : GAd σ J → ℂ), ratPts σ J ⊓ parFlag σ J C d ≤ H → IsAutOn σ J H K φ → IsConstTermOn σ J (unipFlag σ J C d) φ c → IsSm σ J c := by
  atlas_forward_decl GlobalTheory.ConstTermSmooth.isSm_of_isConstTermOn
end

section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open GlobalTheory.AutomorphicL2Unitary (LeftInv)
open GlobalTheory.Cusp (Cocompact constTermOn)
open scoped TensorProduct

namespace GlobalTheory.UAut.ConstAut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem leftInv_foldr {Γ : Subgroup (GAd σ J)} {φ : GAd σ J → ℂ} (h : LeftInv Γ φ) :
    ∀ l : List (ℝ → GAd σ J), LeftInv Γ (l.foldr lineDer φ) := by
  intro l
  induction l with
  | nil => exact h
  | cons γ l ih =>
    intro x hx g
    simp only [List.foldr_cons, lineDer, mul_assoc, ih x hx]

theorem realLine_zero (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) : γ 0 = 1 := by
  have e := isRealLine_add F E σ h n J γ hγ 0 0
  rw [add_zero] at e
  exact mul_left_cancel (e.symm.trans (mul_one _).symm)

theorem hasDerivAt_foldr (h : IsCMExt F E σ) {φ : GAd σ J → ℂ} (hs : IsSm σ J φ) {l : List (ℝ → GAd σ J)}
    (hl : ∀ γ ∈ l, IsRealLine σ J γ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (g : GAd σ J) (t : ℝ) :
    HasDerivAt (fun s => l.foldr lineDer φ (g * γ s)) ((γ :: l).foldr lineDer φ (g * γ t)) t := by
  have hd := (GlobalTheory.ThK.RealLineGrowthDerivative.differentiableAt_foldr_lineDer hs l hl hγ (g * γ t)).hasDerivAt
  have e : ∀ s, g * γ t * γ (s - t) = g * γ s := fun s => by
    rw [mul_assoc, ← isRealLine_add F E σ h n J γ hγ, add_sub_cancel]
  have h2 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact hd)
  simp only [e] at h2
  exact h2

theorem isAutOn_constTerm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (C : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ), IsIsoCols σ J C → ∀ (H K : Subgroup (GAd σ J)) (φ c : GAd σ J → ℂ), ratPts σ J ⊓ parFlag σ J C d ≤ H → IsAutOn σ J H K φ → IsConstTermOn σ J (unipFlag σ J C d) φ c → IsAutOn σ J (leftGrp σ J C d) K c ∧ ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → IsConstTermOn σ J (unipFlag σ J C d) (l.foldr lineDer φ) (l.foldr lineDer c) := by
  intro F E _ _ _ _ _ σ h n J hJ r C d hC H K φ c hH hφ hc
  classical
  haveI := locallyCompact_unipFlag hJ (sigma_sigma h) hC d
  have hφΓ : LeftInv (ratPts σ J ⊓ parFlag σ J C d) φ := fun γ hγ => hφ.left γ (hH hγ)
  obtain ⟨hco, e⟩ := hc.eq_constTermOn_par h hJ hC hφΓ
  have hcont : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → Continuous (l.foldr lineDer φ) :=
    GlobalTheory.T.continuous_iteratedRealLineDeriv_unitaryAdelic F E σ h n J hJ φ hφ.level hφ.cont hφ.smooth
  have hleft : ∀ l : List (ℝ → GAd σ J), LeftInv (ratPts σ J ⊓ parFlag σ J C d) (l.foldr lineDer φ) :=
    leftInv_foldr hφΓ
  have hder : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      l.foldr lineDer c = constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) (l.foldr lineDer φ) := by
    intro l
    induction l with
    | nil => intro _; exact e
    | cons γ l ih =>
      intro hl
      have hl' : ∀ γ' ∈ l, IsRealLine σ J γ' := fun γ' h' => hl γ' (List.mem_cons_of_mem _ h')
      have hγ : IsRealLine σ J γ := hl γ List.mem_cons_self
      funext x
      have hx := GlobalTheory.CuspLie.hasDerivAt_constTermOn hco (hleft l) (hcont l hl') (hleft (γ :: l)) (hcont (γ :: l) hl)
        (GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J γ hγ) (hasDerivAt_foldr h hφ.smooth hl' hγ) x
      rw [realLine_zero h hγ, mul_one] at hx
      rw [List.foldr_cons, ih hl']
      exact hx.deriv
  have hct : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      IsConstTermOn σ J (unipFlag σ J C d) (l.foldr lineDer φ) (l.foldr lineDer c) := by
    intro l hl
    obtain ⟨c', hc', -⟩ := existsUnique_isConstTermOn h hJ hC d (φ := l.foldr lineDer φ)
      fun γ hγ => hleft l γ ⟨hγ.1, unipFlag_le_parFlag hJ (sigma_sigma h) hC d hγ.2⟩
    rwa [hder l hl, ← (hc'.eq_constTermOn_par h hJ hC (hleft l)).2]
  let S : Submodule ℂ (GAd σ J → ℂ) :=
    { carrier := {f | LeftInv (ratPts σ J ⊓ parFlag σ J C d) f ∧ Continuous f}
      add_mem' := fun ha hb => ⟨fun γ hγ g => by simp [ha.1 γ hγ g, hb.1 γ hγ g], ha.2.add hb.2⟩
      zero_mem' := ⟨fun _ _ _ => rfl, continuous_const⟩
      smul_mem' := fun a f hf => ⟨fun γ hγ g => by simp [hf.1 γ hγ g], hf.2.const_smul a⟩ }
  let Tl : S →ₗ[ℂ] (GAd σ J → ℂ) :=
    { toFun := fun f => constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) f.1
      map_add' := fun a b => funext fun x => hco.constTermOn_add a.2.1 a.2.2 b.2.1 b.2.2 x
      map_smul' := fun a f => funext fun x => GlobalTheory.Cusp.constTermOn_smul a f.1 x }
  have hfin : ∀ W : Submodule ℂ (GAd σ J → ℂ), FiniteDimensional ℂ W →
      FiniteDimensional ℂ ((W.comap S.subtype).map Tl) := by
    intro W hW
    haveI : FiniteDimensional ℂ (W.comap S.subtype) := FiniteDimensional.of_injective
      (S.subtype.restrict (q := W) fun _ hx => hx) fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : W => z.1) h))
    infer_instance
  have hsum : ∀ (s : Finset (List (ℝ → GAd σ J))) (a : List (ℝ → GAd σ J) → ℂ),
      (∀ l ∈ s, ∀ γ ∈ l, IsRealLine σ J γ) →
      (∑ l ∈ s, a l • l.foldr lineDer φ) ∈ S ∧
      constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) (∑ l ∈ s, a l • l.foldr lineDer φ) =
        ∑ l ∈ s, a l • constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) (l.foldr lineDer φ) := by
    intro s a hs
    induction s using Finset.induction_on with
    | empty => exact ⟨S.zero_mem, funext fun x => by simp [GlobalTheory.Cusp.constTermOn]⟩
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      obtain ⟨h1, h2⟩ := ih fun l hl => hs l (Finset.mem_insert_of_mem hl)
      have m : a i • i.foldr lineDer φ ∈ S :=
        S.smul_mem _ ⟨hleft i, hcont i (hs i (Finset.mem_insert_self i s))⟩
      refine ⟨S.add_mem m h1, ?_⟩
      rw [← h2]
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hco.constTermOn_add m.1 m.2 h1.1 h1.2 x, GlobalTheory.Cusp.constTermOn_smul]
  have hlevel : ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧
      ∀ k ∈ U, k ∈ finPts σ J → ∀ g, c (g * k) = c g := by
    obtain ⟨U, hU, hUk⟩ := hφ.level
    refine ⟨U, hU, fun k hk hf g => ?_⟩
    rw [e, ← GlobalTheory.Cusp.constTermOn_mul_right]
    exact congrArg (fun f => constTermOn _ _ f g) (funext fun y => hUk k hk hf y)
  have hkfin : GlobalTheory.Doubling.IsKFinite K c := by
    obtain ⟨W, hW, hWk⟩ := GlobalTheory.Doubling.isKFinite_iff.1 hφ.kfin
    refine GlobalTheory.Doubling.isKFinite_iff.2 ⟨_, hfin W hW, fun k hk => ⟨⟨fun g => φ (g * k),
      fun γ hγ g => by simp only [mul_assoc]; exact hφΓ γ hγ _, hφ.cont.comp (continuous_mul_right k)⟩,
      hWk k hk, funext fun g => ?_⟩⟩
    show constTermOn _ _ (fun g => φ (g * k)) g = c (g * k)
    rw [GlobalTheory.Cusp.constTermOn_mul_right, e]
  have hzfin : FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z c}) := by
    haveI := hfin (Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z φ}) hφ.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := ((Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z φ}).comap S.subtype).map Tl) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    have hr : ∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ := hz.1
    have hd1 : dop z φ = ∑ l ∈ z.support, z l • l.foldr lineDer φ := funext fun g => by
      simp [dop, Finsupp.sum, Finset.sum_apply]
    have hd2 : dop z c = ∑ l ∈ z.support, z l •
        constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) (l.foldr lineDer φ) := funext fun g => by
      simp only [dop, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun l hl => by rw [hder l (hr l hl)]
    obtain ⟨m, hm⟩ := hsum z.support (fun l => z l) hr
    refine ⟨⟨_, m⟩, ?_, ?_⟩
    · show (∑ l ∈ z.support, z l • l.foldr lineDer φ) ∈ Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z φ}
      rw [← hd1]
      exact Submodule.subset_span ⟨z, hz, rfl⟩
    · show constTermOn _ _ _ = _
      rw [hm, hd2]
  have hgrowth : ∃ M : ℕ, ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      ∃ B : ℝ, ∀ g, ‖l.foldr lineDer c g‖ ≤ B * (height σ J g : ℝ) ^ M := by
    obtain ⟨M, hM⟩ := hφ.growth
    obtain ⟨K0, hK0, hs⟩ := id hco
    haveI := hco.isProbabilityMeasure
    obtain ⟨A, hA⟩ := (hK0.image continuous_subtype_val).exists_bound_of_continuousOn
      (f := fun x => (height σ J x : ℝ)) (NNReal.continuous_coe.comp (continuous_height_GAd σ J)).continuousOn
    refine ⟨M, fun l hl => ?_⟩
    obtain ⟨B, hB⟩ := hM l hl
    refine ⟨max B 0 * max A 0 ^ M, fun g => ?_⟩
    have h1 : ∀ x : unipFlag σ J C d, ‖l.foldr lineDer φ ((x : GAd σ J) * g)‖ ≤
        max B 0 * (max A 0 * (height σ J g : ℝ)) ^ M := by
      intro x
      obtain ⟨γ, hγ, hk⟩ := hs x
      have e1 : l.foldr lineDer φ ((x : GAd σ J) * g) =
          l.foldr lineDer φ (((γ * x : unipFlag σ J C d) : GAd σ J) * g) := by
        rw [Subgroup.coe_mul, mul_assoc]; exact (hleft l _ hγ _).symm
      have e2 : (height σ J ((γ * x : unipFlag σ J C d) : GAd σ J) : ℝ) ≤ max A 0 := by
        have := hA _ ⟨_, hk, rfl⟩
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans (this.trans (le_max_left _ _))
      have e3 : (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ) ≤ max A 0 * height σ J g :=
        calc (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ)
            ≤ height σ J ((γ * x : unipFlag σ J C d) : GAd σ J) * height σ J g := by
              exact_mod_cast height_mul_le σ J _ _
          _ ≤ max A 0 * height σ J g := mul_le_mul_of_nonneg_right e2 (NNReal.coe_nonneg _)
      rw [e1]
      calc _ ≤ B * (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ) ^ M := hB _
        _ ≤ max B 0 * (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ) ^ M :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (NNReal.coe_nonneg _) _)
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) e3 _) (le_max_right _ _)
    rw [hder l hl]
    refine (norm_integral_le_of_norm_le_const (μ := GlobalTheory.Cusp.probMeasure _ _) (.of_forall fun q => h1 q.out)).trans
      (le_of_eq ?_)
    simp [mul_pow, mul_assoc]
  exact ⟨⟨hc.leftInv h hJ hC hφΓ, hlevel, hc.continuous h hJ hC hφΓ hφ.cont,
    GlobalTheory.T.constant_term_smooth_parabolic F E σ h n J hJ r C d hC H K φ c hH hφ hc, hgrowth, hkfin, hzfin⟩, hct⟩

end GlobalTheory.UAut.ConstAut

end
end
