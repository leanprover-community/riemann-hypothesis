import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IwahoriSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelLocallyFiniteContinuous
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableDescendOfCover
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelCompactTranslateBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLatticePointsInSiegelSetBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularSemisimpleConjugateUnipotentTranslate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemParabolicOfFlagPreserving
import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.Variation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneJacobianIdentity
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapInfFinEquivEqProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodFunctionLineDerivative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicConstantTermParabolic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAutLaurentCoeffSubConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineContinuous
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelDomainOpenSubgroupBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelSetUniformSmoothBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeIntegralFiniteLargeExponentStatement

section
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

theorem smOf : SmOf := by
  intro F E _ _ _ _ _ σ h n J _ f hf k γ hγ g
  exact (GlobalTheory.Orb.isSmoothRealFam_prod (fun i =>
    (GlobalTheory.ThK.CuspTransfer.Smooth.line_fam h (hγ i)).1.comp (contDiff_apply ℝ ℝ i))).contDiff hf g

end MainStatements.WeightKernel.Dec

end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open scoped ContDiff ComplexConjugate Topology

noncomputable section

namespace MainStatements.WeightKernel.Dec.DDerMemc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem exp_entry (Z : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ContDiff ℝ ∞ fun t : ℝ => (NormedSpace.exp (t • Z)) i j := by
  open scoped Matrix.Norms.Operator in
  have h1 : ContDiff ℝ ∞ fun t : ℝ => (NormedSpace.exp (t • Z) : Matrix (Fin n) (Fin n) ℂ) := by
    have : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) :=
      contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
    exact this.comp (contDiff_id.smul contDiff_const)
  open scoped Matrix.Norms.Operator in
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).contDiff.comp h1

theorem lineSm (h : IsCMExt F E σ) {b : ℝ → GAd σ J} (hb : IsRealLine σ J b) :
    ContDiff ℝ ∞ fun t => infCoord σ J (projInf σ J (b t)) := by
  classical
  obtain ⟨w, τ, Z, -, hZ⟩ := hb
  choose y hy hyZ using hZ
  refine contDiff_pi.2 fun u => contDiff_pi.2 fun τ' => contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  have e0 : ∀ t, infCoord σ J (projInf σ J (b t)) u τ' i j = archMat σ J τ' (projArch σ J u (embArch σ J w (y t))) i j :=
    fun t => by rw [← hy t, ← projInfArch_projInf]; rfl
  simp only [e0]
  by_cases hu : u = w
  · subst hu
    simp only [projArch_embArch_self]
    have e1 : ∀ t, infEmb τ ((matHom _ σ J (y t)).1 i j) = (NormedSpace.exp (t • Z)) i j := fun t => by
      rw [← hyZ t]; rfl
    rcases infEmb_eq_or_conj h τ τ' with e | e
    · have : ∀ t, archMat σ J τ' (y t) i j = (NormedSpace.exp (t • Z)) i j := fun t => by
        rw [← e1 t, ← e]; rfl
      simp only [this]; exact exp_entry Z i j
    · have : ∀ t, archMat σ J τ' (y t) i j = conj ((NormedSpace.exp (t • Z)) i j) := fun t => by
        rw [← e1 t]
        change infEmb τ' _ = _
        rw [e]; rfl
      simp only [this]; exact Complex.conjCLE.contDiff.comp (exp_entry Z i j)
  · simp only [projArch_embArch_ne σ J hu]
    exact contDiff_const

theorem main (h : IsCMExt F E σ) {b : ℝ → GAd σ J} (hb : IsRealLine σ J b) {f : GAd σ J → ℂ} (hf : f ∈ CcAd σ J) :
    (∀ g, DifferentiableAt ℝ (fun t => f (g * b t)) 0) ∧ lineDer b f ∈ CcAd σ J := by
  have hβ := lineSm h hb
  have hfin : ∀ t, projFin σ J (b t) = 1 := fun t =>
    mem_infPts.1 (GlobalTheory.RealLineInf.realLine_mem_infPts F E σ n J b hb t)
  have hbc : Continuous b := GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J b hb
  have hb0 : b 0 = 1 := GlobalTheory.UAut.ConstAut.realLine_zero h hb
  obtain ⟨-, ⟨m, hm, em⟩, -⟩ := isGroupCoord_infCoord σ J
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ⟨hac, Φ, hΦ, ea⟩, c, hc, rfl⟩ := hf
    set G := fun p : _ × ℝ => Φ (m (p.1, infCoord σ J (projInf σ J (b p.2)))) with hG
    have hGs : ContDiff ℝ ∞ G := hΦ.comp (hm.comp (contDiff_fst.prodMk (hβ.comp contDiff_snd)))
    have hd : ∀ x, HasDerivAt (fun t : ℝ => G (x, t)) (fderiv ℝ G (x, 0) (0, 1)) 0 := fun x =>
      ((hGs.differentiable (by simp)) (x, (0 : ℝ))).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        ((hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id (0 : ℝ)))
    have ea' : ∀ (g : GInf σ J) t, a (g * projInf σ J (b t)) = G (infCoord σ J g, t) := fun g t => by
      rw [ea, em]
    have e1 : ∀ g, (fun t => infFin σ J a c (g * b t)) =
        fun t => G (infCoord σ J (projInf σ J g), t) * c (projFin σ J g) := fun g => funext fun t => by
      simp only [infFin, map_mul, hfin, mul_one, ea']
    refine ⟨fun g => by rw [e1]; exact ((hd _).mul_const _).differentiableAt, ?_⟩
    have e2 : lineDer b (infFin σ J a c) =
        infFin σ J (fun g => fderiv ℝ G (infCoord σ J g, 0) (0, 1)) c := funext fun g => by
      rw [lineDer, e1, ((hd _).mul_const _).deriv]; rfl
    rw [e2]
    refine infFin_mem_ccAd ⟨HasCompactSupport.intro hac.isCompact fun g hg => ?_,
      fun x => fderiv ℝ G (x, 0) (0, 1), ?_, fun _ => rfl⟩ hc
    · rw [← (hd _).deriv]
      have hc1 : Continuous fun t => g * projInf σ J (b t) :=
        continuous_const.mul ((continuous_projInf σ J).comp hbc)
      have : ∀ᶠ t in 𝓝 (0 : ℝ), g * projInf σ J (b t) ∈ (tsupport a)ᶜ :=
        hc1.continuousAt.eventually_mem ((isClosed_tsupport a).isOpen_compl.mem_nhds (by simpa [hb0] using hg))
      have e3 : (fun t : ℝ => G (infCoord σ J g, t)) =ᶠ[𝓝 0] fun _ => 0 :=
        this.mono fun t ht => (ea' g t).symm.trans (image_eq_zero_of_notMem_tsupport ht)
      rw [e3.deriv_eq, deriv_const]
    · exact ((hGs.fderiv_right (m := ∞) (by simp)).comp (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const
  | zero => exact ⟨fun g => differentiableAt_const _, by
      have : lineDer b (0 : GAd σ J → ℂ) = 0 := funext fun g => by simp [lineDer]
      rw [this]; exact zero_mem _⟩
  | add f f' _ _ h1 h2 =>
    refine ⟨fun g => (h1.1 g).add (h2.1 g), ?_⟩
    have : lineDer b (f + f') = lineDer b f + lineDer b f' := funext fun g => deriv_add (h1.1 g) (h2.1 g)
    rw [this]; exact add_mem h1.2 h2.2
  | smul a f _ h1 =>
    refine ⟨fun g => (h1.1 g).const_smul a, ?_⟩
    have : lineDer b (a • f) = a • lineDer b f := funext fun g => deriv_const_smul a (h1.1 g)
    rw [this]; exact Submodule.smul_mem _ a h1.2

end MainStatements.WeightKernel.Dec.DDerMemc

theorem MainStatements.WeightKernel.Dec.derMem : MainStatements.WeightKernel.Dec.DerMem :=
  fun _ _ _ _ _ _ _ _ h _ _ _ _ hf _ hb => (MainStatements.WeightKernel.Dec.DDerMemc.main h hb hf).2
end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec.DDerVan

theorem mem_aux {G : Type*} [Group G] (K : Set G) (B : Set ℝ) (c : ℝ → G) (x y m : G) (t : ℝ)
    (hk : x * m * (y * c t) ∈ K) (ht : t ∈ B) :
    m ∈ (fun p : G × ℝ => x⁻¹ * p.1 * (y * c p.2)⁻¹) '' (K ×ˢ B) :=
  ⟨(x * m * (y * c t), t), ⟨hk, ht⟩, by simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one]⟩

end MainStatements.WeightKernel.Dec.DDerVan

theorem MainStatements.WeightKernel.Dec.derVan : MainStatements.WeightKernel.Dec.SmOf → MainStatements.WeightKernel.Dec.DerMem → MainStatements.WeightKernel.Dec.DerVan := by
  intro hSm hDer F E _ _ _ _ _ σ h n J hJ N hN f hf b hb hV ν _ x y
  have hfc := GlobalTheory.Orb.continuous_of_mem_ccAd (σ := σ) (J := J) hf
  have hf'c := GlobalTheory.Orb.continuous_of_mem_ccAd (σ := σ) (J := J) (hDer F E σ h n J hJ f hf b hb)
  have hs := hSm F E σ h n J hJ f hf
  have hbc : Continuous b := GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J b hb
  have hK : IsCompact (tsupport f ∪ tsupport (lineDer b f)) := IsCompact.union hfc.2 hf'c.2
  have hS : IsCompact ((fun p : GAd σ J × ℝ => x⁻¹ * p.1 * (y * b p.2)⁻¹) ''
      ((tsupport f ∪ tsupport (lineDer b f)) ×ˢ Metric.closedBall (0 : ℝ) 1)) :=
    (hK.prod (isCompact_closedBall 0 1)).image
      ((continuous_const.mul continuous_fst).mul ((continuous_const.mul (hbc.comp continuous_snd)).inv))
  have hC := hN.isClosedEmbedding_subtypeVal.isCompact_preimage hS
  have key := GlobalTheory.LaurentAut.hasDerivAt_integral_cpt (𝕜 := ℝ) ν (x₀ := 0)
    (Φ := fun t (m : N) => f (x * m * (y * b t))) (Φ' := fun t (m : N) => lineDer b f (x * m * (y * b t))) hC ?_ ?_ ?_ ?_
  · have h0 : (fun t : ℝ => ∫ m : N, f (x * m * (y * b t)) ∂ν) = fun _ => 0 := funext fun t => hV ν x (y * b t)
    rw [h0] at key
    have e := key.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    simpa [GlobalTheory.UAut.ConstAut.realLine_zero h hb] using e
  · intro t
    exact hfc.1.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  · exact hf'c.1.comp ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).mul
      (continuous_const.mul (hbc.comp continuous_fst)))
  · intro t ht m hm
    have hnot : x * ↑m * (y * b t) ∉ tsupport f ∪ tsupport (lineDer b f) := fun hk =>
      hm (MainStatements.WeightKernel.Dec.DDerVan.mem_aux _ _ b x y (↑m) t hk ht)
    exact ⟨image_eq_zero_of_notMem_tsupport (fun h' => hnot (Or.inl h')),
      image_eq_zero_of_notMem_tsupport (fun h' => hnot (Or.inr h'))⟩
  · intro t m
    have := GlobalTheory.UAut.ConstAut.hasDerivAt_foldr h hs (l := []) (by simp) hb (x * ↑m * y) t
    simpa [mul_assoc] using this
end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec.DLevel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem level_of_mem {f : GAd σ J → ℂ} (hf : f ∈ CcAd σ J) :
    ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, f (g * k) = f g := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, -, b, hb, rfl⟩ := hx
    obtain ⟨V, hV, hVb⟩ := GlobalTheory.Orb.exists_biinvariant hb
    refine ⟨V.comap (projFin σ J), hV.preimage (continuous_projFin σ J), fun k hk hkf g => ?_⟩
    show a (projInf σ J (g * k)) * b (projFin σ J (g * k)) = a (projInf σ J g) * b (projFin σ J g)
    rw [map_mul, map_mul, mem_finPts.1 hkf, mul_one, (hVb _ hk _).2]
  | zero => exact ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨U, hU, h⟩ := hx
    obtain ⟨V, hV, h'⟩ := hy
    exact ⟨U ⊓ V, hU.inter hV, fun k hk hkf g => by
      simp only [Pi.add_apply, h k hk.1 hkf g, h' k hk.2 hkf g]⟩
  | smul c x _ hx =>
    obtain ⟨U, hU, h⟩ := hx
    exact ⟨U, hU, fun k hk hkf g => by simp only [Pi.smul_apply, h k hk hkf g]⟩

end MainStatements.WeightKernel.Dec.DLevel

theorem MainStatements.WeightKernel.Dec.level : MainStatements.WeightKernel.Dec.Level := by
  intro F E _ _ _ _ _ σ _ n J _ f hf
  exact MainStatements.WeightKernel.Dec.DLevel.level_of_mem hf

end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
open scoped ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec.DSumSm

lemma loc_fin {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {Γ : Subgroup G} [DiscreteTopology Γ] {f : G → ℂ} (hf : HasCompactSupport f) (z : G)
    [TopologicalSpace X] [WeaklyLocallyCompactSpace X] {φ : X → G} (hφ : Continuous φ) (x₀ : X) :
    ∃ S : Finset Γ, ∀ᶠ x in 𝓝 x₀, ∀ ν : Γ, ν ∉ S → f (z * ν * φ x) = 0 := by
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds x₀
  have hfin := GlobalTheory.AutomorphicL2KernelContinuous.finite_contributing (Γ := Γ) hf (isCompact_singleton (x := z⁻¹))
    (hK.image hφ)
  refine ⟨hfin.toFinset, Filter.mem_of_superset hKn fun x hx ν hν => ?_⟩
  by_contra h
  apply hν
  rw [Set.Finite.mem_toFinset]
  exact ⟨z⁻¹, rfl, φ x, ⟨x, hx, rfl⟩, by simpa using h⟩

lemma cont_prod {G : Type} [Monoid G] [TopologicalSpace G] [ContinuousMul G] :
    ∀ (k : ℕ) (γ : Fin k → ℝ → G), (∀ i, Continuous (γ i)) →
      Continuous fun t : Fin k → ℝ => (List.ofFn fun i => γ i (t i)).prod
  | 0, γ, _ => by simpa using continuous_const
  | k + 1, γ, h => by
    simp only [List.ofFn_succ, List.prod_cons]
    exact ((h 0).comp (continuous_apply 0)).mul
      ((cont_prod k (fun i => γ i.succ) (fun i => h i.succ)).comp
        (continuous_pi fun i => continuous_apply i.succ))

end MainStatements.WeightKernel.Dec.DSumSm

namespace MainStatements.WeightKernel.Dec

open DSumSm in
theorem sumSm : SmOf → SumSm := by
  intro hSm F E _ _ _ _ _ σ h n J hJ Γ hΓ f hf z
  have : DiscreteTopology Γ :=
    DiscreteTopology.of_subset (t := (Γ : Set (GAd σ J))) (s := (ratPts σ J : Set (GAd σ J)))
      (inferInstance : DiscreteTopology (ratPts σ J)) hΓ
  have hs : GlobalTheory.UAut.IsSm σ J f := hSm F E σ h n J hJ f hf
  have hcs : HasCompactSupport f := (continuous_of_mem_ccAd hf).2
  refine ⟨?_, ?_⟩
  · intro k γ hγ g
    rw [contDiff_iff_contDiffAt]
    intro t₀
    have hφ : Continuous fun t : Fin k → ℝ => g * (List.ofFn fun i => γ i (t i)).prod :=
      continuous_const.mul (cont_prod k γ fun i =>
        GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J (γ i) (hγ i))
    obtain ⟨S, hS⟩ := loc_fin (Γ := Γ) hcs z hφ t₀
    have hsum : ContDiffAt ℝ ∞ (fun t : Fin k → ℝ =>
        ∑ ν ∈ S, f (z * ν * (g * (List.ofFn fun i => γ i (t i)).prod))) t₀ := by
      refine ContDiff.contDiffAt (ContDiff.sum fun ν _ => ?_)
      have := hs k γ hγ (z * ν * g)
      simpa only [mul_assoc] using this
    refine hsum.congr_of_eventuallyEq (hS.mono fun t ht => ?_)
    exact tsum_eq_sum (s := S) (fun ν hν => ht ν hν)
  · intro b hb
    funext g
    have hbc := GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J b hb
    obtain ⟨S, hS⟩ := loc_fin (Γ := Γ) (φ := fun t : ℝ => g * b t) hcs z (continuous_const.mul hbc) 0
    have hline : ∀ x : GAd σ J, ContDiff ℝ ∞ fun t : ℝ => f (x * b t) := by
      intro x
      have := (hs 1 (fun _ => b) (fun _ => hb) x).comp
        (contDiff_pi.2 fun _ => contDiff_id : ContDiff ℝ ∞ fun t : ℝ => fun _ : Fin 1 => t)
      convert this using 2
      simp [List.ofFn_succ]
    have e1 : (fun t => nsum Γ f z (g * b t)) =ᶠ[𝓝 0]
        fun t => ∑ ν ∈ S, f (z * ν * (g * b t)) :=
      hS.mono fun t ht => tsum_eq_sum (s := S) (fun ν hν => ht ν hν)
    have e2 : ∀ ν ∉ S, lineDer b f (z * ν * g) = 0 := by
      intro ν hν
      show deriv (fun t => f (z * ν * g * b t)) 0 = 0
      have : (fun t => f (z * ν * g * b t)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) :=
        hS.mono fun t ht => by simpa only [mul_assoc] using ht ν hν
      rw [this.deriv_eq, deriv_const]
    show deriv (fun t => nsum Γ f z (g * b t)) 0 = ∑' ν : Γ, lineDer b f (z * ν * g)
    rw [e1.deriv_eq, tsum_eq_sum (s := S) e2, deriv_fun_sum]
    · refine Finset.sum_congr rfl fun ν _ => ?_
      show _ = deriv (fun t => f (z * ν * g * b t)) 0
      simp only [mul_assoc]
    · intro ν _
      have := ((hline (z * ν * g)).differentiable (by simp)) 0
      simpa only [mul_assoc] using this

end MainStatements.WeightKernel.Dec

end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

theorem variation : Variation := by
  intro F E _ _ _ _ _ σ hCM n J hJ k C hC f hf hfs hV z g e he
  have := GlobalTheory.UAut.locallyCompact_unipRad hCM hJ hC
  have hc : GlobalTheory.Cusp.Cocompact (ratPts σ J) (unipRad σ J C) := GlobalTheory.UAut.cocompact_unipRad hCM hJ hC
  have hcl : IsClosed (unipRad σ J C : Set (GAd σ J)) :=
    GlobalTheory.UAut.unipFlag_const (σ := σ) (J := J) C 0 ▸ GlobalTheory.UAut.isClosed_unipFlag hJ (sigma_sigma hCM) hC _
  let ν : Measure (unipRad σ J C) := Measure.haar
  have h𝓕 := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)) ν
  have hfin : ν (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C))) ≠ ⊤ := hc.measure_ne_top h𝓕
  have hpos : ν (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C))) ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne ν)
  let h : unipRad σ J C → ℂ := fun m => f (z * m * g)
  have hcont : Continuous h := by fun_prop
  let T := (Homeomorph.mulLeft z).trans (Homeomorph.mulRight g)
  have hK : IsCompact (T ⁻¹' tsupport f) := T.isCompact_preimage.2 hfs
  have hsupp : HasCompactSupport h :=
    HasCompactSupport.intro' (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK)
      ((isClosed_tsupport f).preimage (T.continuous.comp continuous_subtype_val))
      fun x hx => image_eq_zero_of_notMem_tsupport (f := f) (x := z * (x : GAd σ J) * g) hx
  have hint : Integrable h ν := hcont.integrable_of_hasCompactSupport hsupp
  have hV0 : ∫ m, h m ∂ν = 0 := hV ν z g
  let F' : (ratPts σ J).subgroupOf (unipRad σ J C) → unipRad σ J C → ℂ := fun γ x => h (γ • x)
  have hmeas : ∀ γ, AEStronglyMeasurable (F' γ) (ν.restrict (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)))) :=
    fun γ => (hcont.comp (continuous_const_smul γ)).aestronglyMeasurable
  have hlin : ∑' γ, ∫⁻ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)), ‖F' γ x‖ₑ ∂ν ≠ ⊤ := by
    have hl : ∫⁻ x, ‖h x‖ₑ ∂ν = ∑' γ, ∫⁻ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)), ‖F' γ x‖ₑ ∂ν := by
      rw [h𝓕.lintegral_eq_tsum' (fun x => ‖h x‖ₑ), ← (Equiv.inv _).tsum_eq]; simp [F']
    rw [← hl]; exact hint.2.ne
  have e1 : ∫ m, h m ∂ν = ∑' γ, ∫ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)), F' γ x ∂ν := by
    rw [h𝓕.integral_eq_tsum' h hint, ← (Equiv.inv _).tsum_eq]; simp [F']
  have e2 := integral_tsum hmeas hlin
  have hΨ : ∀ x : unipRad σ J C, ∑' γ, F' γ x = nsum (NF σ J C) f z ((x : GAd σ J) * g) := fun x => by
    let eq : (ratPts σ J).subgroupOf (unipRad σ J C) ≃ NF σ J C :=
      { toFun := fun γ => ⟨γ.1.1, γ.2, γ.1.2⟩, invFun := fun ν => ⟨⟨ν.1, ν.2.2⟩, ν.2.1⟩,
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    rw [nsum, ← eq.tsum_eq]
    congr 1; funext γ
    show f (z * ((γ • x : unipRad σ J C) : GAd σ J) * g) = _
    rw [Subgroup.smul_def]; simp [eq, mul_assoc]
  have hzero : ∫ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)),
      nsum (NF σ J C) f z ((x : GAd σ J) * g) ∂ν = 0 := by
    simp_rw [← hΨ]; rw [e2]; exact e1.symm.trans hV0
  have hae : ∀ᵐ x ∂(ν.restrict (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)))),
      HasSum (fun γ => F' γ x) (∑' γ, F' γ x) := by
    have h1 : ∫⁻ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)), ∑' γ, ‖F' γ x‖ₑ ∂ν ≠ ⊤ := by
      rw [lintegral_tsum (fun γ => (hmeas γ).enorm)]; exact hlin
    filter_upwards [ae_lt_top' (AEMeasurable.tsum fun γ => (hmeas γ).enorm) h1] with x hx
    have hs : Summable fun γ => ‖F' γ x‖₊ :=
      ENNReal.tsum_coe_ne_top_iff_summable.1 (by simpa [enorm_eq_nnnorm] using hx.ne)
    exact (Summable.of_norm (NNReal.summable_coe.2 hs)).hasSum
  have hΨm : AEStronglyMeasurable (fun x : unipRad σ J C => ∑' γ, F' γ x)
      (ν.restrict (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)))) :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun s => by first
        | exact Finset.aestronglyMeasurable_fun_sum s fun γ _ => hmeas γ
        | exact Finset.aestronglyMeasurable_sum s fun γ _ => hmeas γ) hae
  haveI : IsFiniteMeasure (ν.restrict (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)))) :=
    isFiniteMeasure_restrict.2 hfin
  have hΨi : IntegrableOn (fun x : unipRad σ J C => nsum (NF σ J C) f z ((x : GAd σ J) * g))
      (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C))) ν := by
    refine Integrable.of_bound (C := e + ‖nsum (NF σ J C) f z g‖) ?_ (.of_forall fun x => ?_)
    · simpa only [hΨ] using hΨm
    · have := he x x.2
      calc _ = ‖(nsum (NF σ J C) f z ((x : GAd σ J) * g) - nsum (NF σ J C) f z g) + nsum (NF σ J C) f z g‖ := by
              rw [sub_add_cancel]
        _ ≤ _ := (norm_add_le _ _).trans (by linarith)
  have key : ν.real (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C))) • nsum (NF σ J C) f z g =
      ∫ x in stdDom ((ratPts σ J).subgroupOf (unipRad σ J C)),
        (nsum (NF σ J C) f z g - nsum (NF σ J C) f z ((x : GAd σ J) * g)) ∂ν := by
    rw [integral_sub (integrable_const _) hΨi, hzero, setIntegral_const, sub_zero]
  have hb := norm_setIntegral_le_of_norm_le_const (μ := ν) hfin.lt_top
    (f := fun x : unipRad σ J C => nsum (NF σ J C) f z g - nsum (NF σ J C) f z ((x : GAd σ J) * g)) (C := e)
    (fun x _ => by rw [norm_sub_rev]; exact he x x.2)
  rw [← key, norm_smul, Real.norm_of_nonneg measureReal_nonneg] at hb
  have hp : 0 < ν.real (stdDom ((ratPts σ J).subgroupOf (unipRad σ J C))) := ENNReal.toReal_pos hpos hfin
  nlinarith [norm_nonneg (nsum (NF σ J C) f z g)]

end MainStatements.WeightKernel.Dec
end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
open PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay.NearCusp
open scoped Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

theorem nearCusp : NearCusp := by
  intro F E _ _ _ _ _ σ hCM n J hJ r X Y hW Cm c U hCm hc hU s
  have hσ := sigma_sigma hCM
  have hC : GlobalTheory.UAut.IsIsoCols σ J (pre X s) := GlobalTheory.UAut.isIsoCols_of_isWittFrame hW hσ hJ s.2
  let Cf : Set (GFin σ J) := (fun z : GAd σ J => projFin σ J z) '' Cm
  have hCf : IsCompact Cf := hCm.image (continuous_projFin σ J)
  let Uf : Set (GFin σ J) := ofFin σ J ⁻¹' (U : Set (GAd σ J))
  have hUf : Uf ∈ 𝓝 (1 : GFin σ J) :=
    (hU.preimage (continuous_ofFin σ J)).mem_nhds (by simp only [Set.mem_preimage, map_one]; exact U.one_mem)
  let Wn : Set (GFin σ J) := {x | ∀ h ∈ Cf, h⁻¹ * x * h ∈ Uf}
  have hWn : Wn ∈ 𝓝 (1 : GFin σ J) := conj_mem_nhds hCf hUf
  obtain ⟨Q, hQ, hQm⟩ := GlobalTheory.T.unipotent_radical_compact_fundamental_domain F E σ hCM n J hJ _ (pre X s) hC Wn hWn
  obtain ⟨M₁, hM₁, hM₁b⟩ := GlobalTheory.T.torus_conjugate_unipotent_bounded F E σ hCM n J hJ r X Y hW Q c hQ hc s
  obtain ⟨C₀, hC₀, hC₀b⟩ := exists_bound_archMat (σ := σ) (J := J) hCm
  refine ⟨C₀ * M₁, mul_nonneg hC₀ hM₁, ?_⟩
  intro t ht a ha k hk m hm
  obtain ⟨γ, hγ, q, hqQ, hqU, hqW, rfl⟩ := hQm m hm
  have hγU : γ ∈ unipRad σ J (pre X s) := by
    have := mul_mem hm (inv_mem hqU)
    rwa [mul_inv_cancel_right] at this
  have hfa : projFin σ J a = 1 := mem_infPts.1 ha.1
  refine ⟨γ, ⟨hγ, hγU⟩, ofInf σ J (projInf σ J ((a * k)⁻¹ * q * (a * k))),
    ofFin σ J (projFin σ J ((a * k)⁻¹ * q * (a * k))), ⟨mem_infPts.2 (projFin_ofInf σ J _), ?_⟩, ?_,
    mem_finPts.2 (projInf_ofFin σ J _), ?_⟩
  · intro w τ i j
    have hN := hM₁b q hqQ hqU t ht a ha w τ
    have ev : (a * k)⁻¹ * q * (a * k) = k⁻¹ * (a⁻¹ * q * a) * k := by group
    have hB : archMat σ J τ (projArch σ J w k⁻¹) * archMat σ J τ (projArch σ J w k) = 1 := by
      rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
    have key : archMat σ J τ (projArch σ J w (ofInf σ J (projInf σ J ((a * k)⁻¹ * q * (a * k))))) - 1 =
        archMat σ J τ (projArch σ J w k⁻¹) * (archMat σ J τ (projArch σ J w (a⁻¹ * q * a)) - 1) *
          archMat σ J τ (projArch σ J w k) := by
      rw [projArch_ofInf, projInfArch_projInf, ev, map_mul (projArch σ J w) _ k, map_mul (projArch σ J w) k⁻¹,
        map_mul (archMat σ J τ), map_mul (archMat σ J τ), Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hB]
    rw [key]
    refine (GlobalTheory.CuspGeo.norm_mul_mul_apply_le _ _ _ _ hN i j).trans ?_
    rw [mul_div_assoc C₀]
    exact mul_le_mul_of_nonneg_right (hC₀b k hk w τ i j) (div_nonneg hM₁ (ratio_pos ht s).le)
  · have hh : projFin σ J k ∈ Cf := ⟨k, hk, rfl⟩
    have e : projFin σ J ((a * k)⁻¹ * q * (a * k)) =
        (projFin σ J k)⁻¹ * projFin σ J q * projFin σ J k := by
      simp only [map_mul, map_inv, hfa, one_mul]
    have := hqW _ hh
    rw [← e] at this
    exact this
  · rw [mul_assoc (γ * (a * k)), ofInf_projInf_mul_ofFin_projFin]
    group

end MainStatements.WeightKernel.Dec
end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
open scoped Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec.DBase

theorem ncard_biUnion_le' {α ι : Type*} (I : Finset ι) (S : ι → Set α) (h : ∀ i ∈ I, (S i).Finite) :
    (⋃ i ∈ I, S i).ncard ≤ ∑ i ∈ I, (S i).ncard := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert j I hj ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hj]
    refine (Set.ncard_union_le _ _).trans (Nat.add_le_add_left (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) _)

end MainStatements.WeightKernel.Dec.DBase

namespace MainStatements.WeightKernel.Dec
open DBase

theorem base : Base := by
  intro D V r X Y hW c hc
  obtain ⟨V₀, hV₀c, hV₀n⟩ := exists_compact_mem_nhds (1 : GA D V)
  have hC₀ : IsCompact (V₀⁻¹ * V₀) := hV₀c.inv.mul hV₀c
  obtain ⟨A, B₀, hAB⟩ := GlobalTheory.T.finite_lattice_points_in_siegel_set_bound D V r X Y hW c hc _ hC₀
  refine ⟨A, fun Γ hΓ f hf hfs C W hC hW' => ?_⟩
  set K : Set (GA D V) := C⁻¹ * tsupport f * W⁻¹ with hK
  have hKc : IsCompact K := (hC.inv.mul hfs.isCompact).mul hW'.inv
  have hint : interior V₀ ∈ nhds (1 : GA D V) := interior_mem_nhds.2 hV₀n
  obtain ⟨I, hI⟩ := hKc.elim_finite_subcover (fun g : K => (g : GA D V) • interior V₀)
    (fun g => isOpen_interior.smul _) (fun g hg => Set.mem_iUnion.2 ⟨⟨g, hg⟩,
      ⟨1, mem_of_mem_nhds hint, by simp⟩⟩)
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfs
  refine ⟨max M 0 * I.card * max B₀ 0, fun t ht a ha x hx y hy => ?_⟩
  obtain ⟨hfin₀, hcnt₀⟩ := hAB t ht a ha
  set S₀ := {δ : GF V | a⁻¹ * rat V δ * a ∈ V₀⁻¹ * V₀}
  set S : K → Set (GF V) := fun g => {δ : GF V | a⁻¹ * rat V δ * a ∈ (g : GA D V) • V₀}
  have hS : ∀ g, (S g).Finite ∧ (S g).ncard ≤ S₀.ncard := by
    intro g
    rcases (S g).eq_empty_or_nonempty with h | ⟨δ₀, hδ₀⟩
    · rw [h]; simp
    have hmap : ∀ δ ∈ S g, δ₀⁻¹ * δ ∈ S₀ := by
      intro δ hδ
      obtain ⟨u, hu, hu'⟩ := hδ
      obtain ⟨u₀, hu₀, hu₀'⟩ := hδ₀
      refine ⟨u₀⁻¹, Set.inv_mem_inv.2 hu₀, u, hu, ?_⟩
      simp only [smul_eq_mul] at hu' hu₀'
      have e : a⁻¹ * rat V (δ₀⁻¹ * δ) * a = (a⁻¹ * rat V δ₀ * a)⁻¹ * (a⁻¹ * rat V δ * a) := by
        simp [map_mul, map_inv, mul_assoc]
      rw [e, ← hu', ← hu₀']; group
    have hinj : Set.InjOn (fun δ => δ₀⁻¹ * δ) (S g) := fun _ _ _ _ h => mul_left_cancel h
    have hf1 : (S g).Finite := Set.Finite.of_finite_image (hfin₀.subset (by
      rintro _ ⟨δ, hδ, rfl⟩; exact hmap δ hδ)) hinj
    exact ⟨hf1, Set.ncard_le_ncard_of_injOn _ hmap hinj hfin₀⟩
  set T := {δ : GF V | a⁻¹ * rat V δ * a ∈ K}
  have hTsub : T ⊆ ⋃ g ∈ I, S g := by
    intro δ hδ
    obtain ⟨g, hg, hmem⟩ := Set.mem_iUnion₂.1 (hI hδ)
    exact Set.mem_iUnion₂.2 ⟨g, hg, Set.smul_set_mono interior_subset hmem⟩
  have hUfin : (⋃ g ∈ I, S g).Finite := Set.Finite.biUnion I.finite_toSet fun g _ => (hS g).1
  have hTfin : T.Finite := hUfin.subset hTsub
  have hTcnt : (T.ncard : ℝ) ≤ I.card * max B₀ 0 * (∏ i, max (t i) 1) ^ A := by
    have h1 : T.ncard ≤ I.card * S₀.ncard := by
      refine (Set.ncard_le_ncard hTsub hUfin).trans ((ncard_biUnion_le' I S fun g _ => (hS g).1).trans ?_)
      simpa using Finset.sum_le_sum (s := I) fun g _ => (hS g).2
    have hP : 0 ≤ (∏ i, max (t i) 1) ^ A :=
      pow_nonneg (Finset.prod_nonneg fun i _ => le_trans zero_le_one (le_max_right _ _)) A
    calc (T.ncard : ℝ) ≤ I.card * S₀.ncard := by exact_mod_cast h1
      _ ≤ I.card * (max B₀ 0 * (∏ i, max (t i) 1) ^ A) := by
          gcongr
          exact hcnt₀.trans (by gcongr; exact le_max_left _ _)
      _ = _ := by ring

  set g : Γ → ℂ := fun ν => f (x * a⁻¹ * ν * (a * y)) with hg
  have hsupp : ∀ ν : Γ, g ν ≠ 0 → ∃ δ ∈ T, rat V δ = ν := by
    intro ν hν
    obtain ⟨δ, hδ⟩ : (ν : GA D V) ∈ (ratEmb D.sp.cm.sig V.gram).range :=
      (range_ratEmb D.sp.cm.sig V.gram).symm ▸ hΓ ν.2
    refine ⟨δ, ?_, hδ⟩
    have hs : x * a⁻¹ * ν * (a * y) ∈ tsupport f := subset_tsupport _ hν
    show a⁻¹ * rat V δ * a ∈ K
    refine ⟨x⁻¹ * (x * a⁻¹ * ν * (a * y)), ⟨x⁻¹, Set.inv_mem_inv.2 hx, _, hs, rfl⟩, y⁻¹,
      Set.inv_mem_inv.2 hy, ?_⟩
    show _ = _
    rw [show rat V δ = ν from hδ]; group
  have hsf : (Function.support g).Finite := by
    refine (hTfin.image (rat V)).preimage (Subtype.val_injective.injOn) |>.subset ?_
    intro ν hν
    obtain ⟨δ, hδ, e⟩ := hsupp ν hν
    exact ⟨δ, hδ, e⟩
  have hcard : (hsf.toFinset.card : ℝ) ≤ T.ncard := by
    have : (Function.support g).ncard ≤ T.ncard := by
      have h2 : (Function.support g).ncard ≤ (rat V '' T).ncard :=
        Set.ncard_le_ncard_of_injOn Subtype.val (fun ν hν => by
          obtain ⟨δ, hδ, e⟩ := hsupp ν hν; exact ⟨δ, hδ, e⟩) Subtype.val_injective.injOn (hTfin.image _)
      exact h2.trans (Set.ncard_image_le hTfin)
    rw [Set.ncard_eq_toFinset_card _ hsf] at this
    exact_mod_cast this
  show ‖∑' ν : Γ, g ν‖ ≤ _
  rw [tsum_eq_sum (s := hsf.toFinset) (fun ν hν => by simpa using hν)]
  have hP : 0 ≤ (∏ i, max (t i) 1) ^ A :=
    pow_nonneg (Finset.prod_nonneg fun i _ => le_trans zero_le_one (le_max_right _ _)) A
  calc ‖∑ ν ∈ hsf.toFinset, g ν‖ ≤ ∑ ν ∈ hsf.toFinset, ‖g ν‖ := norm_sum_le _ _
    _ ≤ ∑ _ν ∈ hsf.toFinset, max M 0 := Finset.sum_le_sum fun ν _ => (hM _).trans (le_max_left _ _)
    _ = hsf.toFinset.card * max M 0 := by simp
    _ ≤ T.ncard * max M 0 := by gcongr
    _ ≤ (I.card * max B₀ 0 * (∏ i, max (t i) 1) ^ A) * max M 0 := by gcongr
    _ = _ := by ring

end MainStatements.WeightKernel.Dec
end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
open PositivityTheory.ThKR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec.DCore

theorem nsum_level {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (Γ : Subgroup (GAd σ J)) (f : GAd σ J → ℂ)
    (z h κ : GAd σ J) (hκ : ∀ g, f (g * κ) = f g) : nsum Γ f z (h * κ) = nsum Γ f z h := by
  unfold nsum
  exact tsum_congr fun ν => by rw [← mul_assoc, hκ]

theorem nsum_left {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (Γ : Subgroup (GAd σ J)) (f : GAd σ J → ℂ)
    (z h γ : GAd σ J) (hγ : γ ∈ Γ) : nsum Γ f z (γ * h) = nsum Γ f z h := by
  unfold nsum
  have := (Equiv.mulRight (⟨γ, hγ⟩ : Γ)).tsum_eq (fun ν : Γ => f (z * ν * h))
  simpa [mul_assoc] using this

end MainStatements.WeightKernel.Dec.DCore

namespace MainStatements.WeightKernel.Dec
open MainStatements.WeightKernel.Dec.DCore

theorem core : DerMem → DerVan → Level → SumSm → Variation → NearCusp → Base → Core := by
  intro hDM hDV hL hSS hV hNC hBase D V r X Y hW c hc s
  have hcm := isCMExt_host D
  have hJV := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm).2 V
  have hiso : GlobalTheory.UAut.IsIsoCols D.sp.cm.sig V.gram (pre X s) :=
    GlobalTheory.UAut.isIsoCols_of_isWittFrame hW (sigma_sigma hcm) hJV s.2
  have hcl : IsClosed (unipRad D.sp.cm.sig V.gram (pre X s) : Set (GAd D.sp.cm.sig V.gram)) :=
    GlobalTheory.UAut.unipFlag_const (σ := D.sp.cm.sig) (J := V.gram) (pre X s) 0 ▸
      GlobalTheory.UAut.isClosed_unipFlag hJV (sigma_sigma hcm) hiso _
  obtain ⟨A, hA⟩ := hBase D V r X Y hW c hc
  refine ⟨A, fun m => ?_⟩
  induction m with
  | zero =>
    intro f hf _ C W hC hWc
    obtain ⟨B, hB⟩ := hA (NF D.sp.cm.sig V.gram (pre X s)) inf_le_left f (continuous_of_mem_ccAd hf).1 (continuous_of_mem_ccAd hf).2 C W hC hWc
    exact ⟨B, fun t ht a ha x hx y hy => by simpa using hB t ht a ha x hx y hy⟩
  | succ m ih =>
    intro f hf hvan C W hC hWc
    obtain ⟨q, b, Ω₀, Cv, δ₁, hb, hΩ₀, hδ₁, hCv, hmv⟩ := GlobalTheory.T.siegel_set_uniform_smooth_bound _ _ D.sp.cm.sig hcm _ V.gram hJV
    have hW' : IsCompact ((fun x : GAd D.sp.cm.sig V.gram × GAd D.sp.cm.sig V.gram => x.1 * x.2) '' (W ×ˢ Ω₀)) :=
      (hWc.prod hΩ₀).image (by fun_prop)
    choose B hB using fun i => ih (lineDer (b i) f) (hDM _ _ _ hcm _ _ hJV f hf (b i) (hb i))
      (hDV _ _ _ hcm _ _ hJV _ hcl f hf (b i) (hb i) hvan) C _ hC hW'
    obtain ⟨B₀, hB₀⟩ := ih f hf hvan C W hC hWc
    obtain ⟨U, hUo, hU⟩ := hL _ _ _ hcm _ _ hJV f hf
    obtain ⟨M, hM0, hM⟩ := hNC _ _ _ hcm _ _ hJV r X Y hW W c U hWc hc hUo s
    have hR1 : 1 ≤ max 1 (M / δ₁) := le_max_left _ _
    have hSum : 0 ≤ ∑ i, |B i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    refine ⟨max 1 (M / δ₁) * |B₀| + Cv * M * ∑ i, |B i|, fun t ht a ha x hx y hy => ?_⟩
    have hρ : 0 < ratio t s := ratio_pos ht s
    have hT : 0 ≤ (∏ i, max (t i) 1) ^ A :=
      pow_nonneg (Finset.prod_nonneg fun i _ => le_trans zero_le_one (le_max_right _ _)) _
    have hρm : 0 < (ratio t s)⁻¹ ^ m := pow_pos (inv_pos.2 hρ) m
    have hρm1 : 0 < (ratio t s)⁻¹ ^ (m + 1) := pow_pos (inv_pos.2 hρ) _
    have key : (ratio t s)⁻¹ ^ m = ratio t s * (ratio t s)⁻¹ ^ (m + 1) := by
      rw [pow_succ]; field_simp
    have hB0a : 0 ≤ |B₀| := abs_nonneg _
    have hX : 0 ≤ Cv * M * (∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) := by
      have := mul_nonneg (mul_nonneg hCv hM0) hSum
      positivity
    by_cases hcase : ratio t s ≤ max 1 (M / δ₁)
    · have h1 := hB₀ t ht a ha x hx y hy
      have h2 : B₀ * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m ≤
          |B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hT) hρm.le
      have h3 : ratio t s * (|B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1)) ≤
          max 1 (M / δ₁) * (|B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1)) :=
        mul_le_mul_of_nonneg_right hcase (by positivity)
      have h4 : |B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m =
          ratio t s * (|B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1)) := by
        rw [key]; ring
      have h5 : (max 1 (M / δ₁) * |B₀| + Cv * M * ∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) =
          max 1 (M / δ₁) * (|B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1)) +
          Cv * M * (∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) := by ring
      rw [h5]
      linarith
    · push Not at hcase
      have hδ : M / ratio t s ≤ δ₁ := by
        rw [div_le_iff₀ hρ]
        have h1 : M / δ₁ ≤ max 1 (M / δ₁) := le_max_right _ _
        rw [div_le_iff₀ hδ₁] at h1
        nlinarith
      have hsm := hSS _ _ _ hcm _ _ hJV (NF D.sp.cm.sig V.gram (pre X s)) inf_le_left f hf (x * a⁻¹)
      have hcc : ∀ i, ∀ x' ∈ Ω₀, ‖lineDer (b i) (nsum (NF D.sp.cm.sig V.gram (pre X s)) f (x * a⁻¹)) ((a * y) * x')‖ ≤
          |B i| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m := fun i x' hx' => by
        rw [hsm.2 (b i) (hb i), mul_assoc]
        exact (hB i t ht a ha x hx (y * x') ⟨(y, x'), ⟨hy, hx'⟩, rfl⟩).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hT) hρm.le)
      have hvar := hV _ _ _ hcm _ _ hJV _ (pre X s) hiso f (continuous_of_mem_ccAd hf).1 (continuous_of_mem_ccAd hf).2
        hvan (x * a⁻¹) (a * y) (Cv * (M / ratio t s) * ∑ i, |B i| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m)
        (fun m' hm' => by
          obtain ⟨γ, hγ, u, κ, hu, hκU, hκf, e'⟩ := hM t ht a ha y hy m' hm'
          rw [e', nsum_level _ _ _ _ _ (hU κ hκU hκf), mul_assoc γ, nsum_left _ _ _ _ _ hγ]
          exact hmv _ hsm.1 (a * y) u _ (div_nonneg hM0 hρ.le) hδ hu _ hcc)
      have hsum : ∑ i, |B i| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m =
          (∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m := by
        rw [Finset.sum_mul, Finset.sum_mul]
      have h6 : Cv * (M / ratio t s) * ∑ i, |B i| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ m =
          Cv * M * (∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) := by
        rw [hsum, pow_succ, div_eq_mul_inv]; ring
      have h7 : 0 ≤ max 1 (M / δ₁) * |B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) := by positivity
      rw [h6] at hvar
      have h5 : (max 1 (M / δ₁) * |B₀| + Cv * M * ∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) =
          max 1 (M / δ₁) * |B₀| * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) +
          Cv * M * (∑ i, |B i|) * (∏ i, max (t i) 1) ^ A * (ratio t s)⁻¹ ^ (m + 1) := by ring
      rw [h5]
      linarith

end MainStatements.WeightKernel.Dec
end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

theorem bridge : Bridge := by
  intro D V r X Y hW j
  rw [NA_frameFlag]
  rfl

end MainStatements.WeightKernel.Dec

end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec

namespace DDecay

theorem tsum_eq (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (j : Fin r)
    (hB : NA (frameFlag (isIsoFrame_firstCols hW j)) = unipRad D.sp.cm.sig V.gram (pre X j))
    (g : GA D V → ℂ) :
    ∑' ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm, g (rat V ν) =
      ∑' ν : NF D.sp.cm.sig V.gram (pre X j), g ν := by
  have hS : ((NF D.sp.cm.sig V.gram (pre X j) : Subgroup (GA D V)) : Set (GA D V)) =
      rat V '' (((frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm : Subgroup (GF V)) : Set (GF V)) := by
    rw [← Subgroup.coe_map, map_unipRat, hB]; rfl
  calc ∑' ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm, g (rat V ν)
      = ∑' b : (rat V '' (((frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm : Subgroup (GF V)) :
          Set (GF V))), g b := (tsum_image g (ratEmb_injective _ _).injOn).symm
    _ = ∑' c : ((NF D.sp.cm.sig V.gram (pre X j) : Subgroup (GA D V)) : Set (GA D V)),
          g (Equiv.setCongr hS c) := (Equiv.tsum_eq (Equiv.setCongr hS) (fun b => g b)).symm
    _ = ∑' ν : NF D.sp.cm.sig V.gram (pre X j), g ν := rfl

end DDecay

theorem decay : Core → Bridge → Decay := by
  intro hCore hBridge D V r X Y hW c hc j f hf hU C W hC hW'
  obtain ⟨A, hA⟩ := hCore D V r X Y hW c hc j
  have hB := hBridge D V r X Y hW j
  have hV : Van (unipRad D.sp.cm.sig V.gram (pre X j)) f := by
    have h0 : Van (NA (frameFlag (isIsoFrame_firstCols hW j))) f := fun ν _ x y => (hU ν x y).2
    rw [hB] at h0
    exact h0
  refine ⟨A, fun m => ?_⟩
  obtain ⟨B, hBd⟩ := hA m f hf hV C W hC hW'
  refine ⟨B, fun t ht a ha x hx y hy => ?_⟩
  have h1 := hBd t ht a ha x hx y hy
  have h2 : ∑' ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm,
      f (x * (a⁻¹ * rat V ν * a) * y) = nsum (NF D.sp.cm.sig V.gram (pre X j)) f (x * a⁻¹) (a * y) := by
    rw [nsum, ← DDecay.tsum_eq D V r X Y hW j hB (fun g => f (x * a⁻¹ * g * (a * y)))]
    congr 1; funext ν; congr 1; group
  rw [h2]
  exact h1

end MainStatements.WeightKernel.Dec
end
end

section
namespace MainStatements.WeightKernel.Dec

theorem decay_holds : Decay :=
  decay (core derMem (derVan smOf derMem) level (sumSm smOf) variation nearCusp base) bridge

end MainStatements.WeightKernel.Dec
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Matrix
open scoped Pointwise

noncomputable section
open GlobalTheory.CompanionTheory.RegInt
namespace MainStatements.WeightKernel.RegInt

variable {D : D7} {V : HSp D} {r : ℕ}

theorem cone_lower {c : ℝ} (hc : 0 < c) : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ i, c₀ ≤ t i := by
  set d := min c 1 with hd
  have hd0 : 0 < d := lt_min hc one_pos
  have hd1 : d ≤ 1 := min_le_right _ _
  refine ⟨d ^ r, pow_pos hd0 _, fun t ht i => ?_⟩
  have key : ∀ k : ℕ, ∀ i : Fin r, r - i.val = k + 1 → d ^ (k + 1) ≤ t i := by
    intro k
    induction k with
    | zero =>
      intro i hi
      have : i.val + 1 = r := by have := i.2; omega
      rw [zero_add, pow_one]
      exact (min_le_left c 1).trans (ht.2.2 i this)
    | succ k ih =>
      intro i hi
      have hlt : i.val + 1 < r := by have := i.2; omega
      have h1 := ih ⟨i.val + 1, hlt⟩ (by simp only; omega)
      have h2 := ht.2.1 i ⟨i.val + 1, hlt⟩ rfl
      have h3 := ht.1 ⟨i.val + 1, hlt⟩
      calc d ^ (k + 1 + 1) = d * d ^ (k + 1) := by ring
        _ ≤ d * t ⟨i.val + 1, hlt⟩ := by gcongr
        _ ≤ c * t ⟨i.val + 1, hlt⟩ := by gcongr; exact min_le_left _ _
        _ ≤ t i := h2
  have hi := i.2
  obtain ⟨k, hk⟩ : ∃ k, r - i.val = k + 1 := ⟨r - i.val - 1, by omega⟩
  exact (pow_le_pow_of_le_one hd0.le hd1 (by omega)).trans (key k i hk)

theorem le_pow_of_root {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) {ρ : ℝ} (hρ : 1 ≤ ρ) (h : ∀ j, root t j ≤ ρ) (i : Fin r) :
    t i ≤ ρ ^ r := by
  have key : ∀ k : ℕ, ∀ i : Fin r, r - i.val = k + 1 → t i ≤ ρ ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro i hi
      have h1 := h i
      rw [root, dif_neg (by have := i.2; omega)] at h1
      simpa using h1
    | succ k ih =>
      intro i hi
      have hlt : i.val + 1 < r := by have := i.2; omega
      have h1 := ih ⟨i.val + 1, hlt⟩ (by simp only; omega)
      have h2 := h i
      rw [root, dif_pos hlt, div_le_iff₀ (ht _)] at h2
      calc t i ≤ ρ * t ⟨i.val + 1, hlt⟩ := h2
        _ ≤ ρ * ρ ^ (k + 1) := by gcongr
        _ = ρ ^ (k + 1 + 1) := by ring
  have hi := i.2
  obtain ⟨k, hk⟩ : ∃ k, r - i.val = k + 1 := ⟨r - i.val - 1, by omega⟩
  exact (key k i hk).trans (pow_le_pow_right₀ hρ (by omega))

theorem prod_max_le {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) {ρ : ℝ} (hρ : 1 ≤ ρ) (h : ∀ j, root t j ≤ ρ) :
    ∏ i, max (t i) 1 ≤ ρ ^ (r * r) := by
  calc ∏ i, max (t i) 1 ≤ ∏ _i : Fin r, ρ ^ r :=
        Finset.prod_le_prod (fun i _ => by positivity) fun i _ =>
          max_le (le_pow_of_root ht hρ h i) (one_le_pow₀ hρ)
    _ = ρ ^ (r * r) := by simp [pow_mul]

theorem one_le_prod_max (t : Fin r → ℝ) : 1 ≤ ∏ i, max (t i) 1 := by
  have := Finset.prod_le_prod (s := Finset.univ) (f := fun _ : Fin r => (1 : ℝ)) (g := fun i => max (t i) 1)
    (fun _ _ => zero_le_one) fun i _ => le_max_right _ _
  simpa using this

theorem inv_pow_le_prod {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) {ρ : ℝ} (hρ : 1 ≤ ρ) (h : ∀ j, root t j ≤ ρ) (m : ℕ) :
    ρ⁻¹ ^ (r * r * m) ≤ ∏ i, (t i)⁻¹ ^ m := by
  have hρ0 : 0 < ρ := by linarith
  calc ρ⁻¹ ^ (r * r * m) = ∏ _i : Fin r, ((ρ ^ r)⁻¹) ^ m := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow, ← pow_mul]
        congr 2; ring
    _ ≤ ∏ i, (t i)⁻¹ ^ m := Finset.prod_le_prod (fun i _ => by positivity) fun i _ => by
        gcongr
        · exact ht i
        · exact le_pow_of_root ht hρ h i

theorem coset_sum {G : Type} [Group G] (N : Subgroup G) (Cl : Set G) (h : G → ℂ) {β : ℝ} (hβ : 0 ≤ β) {κ : ℝ}
    (hfin : (Function.support h ∩ Cl).Finite) (hcard : (((Function.support h ∩ Cl).ncard : ℕ) : ℝ) ≤ κ)
    (h1 : ∀ δ ∈ Cl, h δ ≠ 0 → ∀ ν ∈ N, δ * ν ∈ Cl)
    (h3 : ∀ δ ∈ Cl, h δ ≠ 0 → ‖∑' ν : N, h (δ * ν)‖ ≤ β) :
    ‖∑' δ : Cl, h δ‖ ≤ κ * β := by
  classical
  set S := hfin.toFinset with hS
  have hSm : ∀ δ, δ ∈ S ↔ h δ ≠ 0 ∧ δ ∈ Cl := fun δ => by simp [hS]
  have e0 : ∑' δ : Cl, h δ = ∑ δ ∈ S, h δ := by
    rw [tsum_subtype Cl h]
    refine (tsum_eq_sum (s := S) fun δ hδ => ?_).trans (Finset.sum_congr rfl fun δ hδ => ?_)
    · by_cases hc : δ ∈ Cl
      · rw [Set.indicator_of_mem hc]; by_contra hne; exact hδ ((hSm δ).2 ⟨hne, hc⟩)
      · rw [Set.indicator_of_notMem hc]
    · rw [Set.indicator_of_mem ((hSm δ).1 hδ).2]
  let q : G → G ⧸ N := QuotientGroup.mk
  have e1 : ∑ δ ∈ S, h δ = ∑ b ∈ S.image q, ∑ δ ∈ S with q δ = b, h δ :=
    (Finset.sum_fiberwise_of_maps_to (fun δ hδ => Finset.mem_image_of_mem q hδ) _).symm
  have e2 : ∀ b ∈ S.image q, ‖∑ δ ∈ S with q δ = b, h δ‖ ≤ β := by
    intro b hb
    obtain ⟨δ₀, hδ₀, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨hne, hcl⟩ := (hSm δ₀).1 hδ₀
    refine le_trans (le_of_eq ?_) (h3 δ₀ hcl hne)
    congr 1
    have hinj : Function.Injective fun ν : N => δ₀ * (ν : G) := fun a b e =>
      Subtype.ext (mul_left_cancel e)
    set u : G → ℂ := fun δ => if q δ = q δ₀ then h δ else 0 with hu
    have hq : ∀ ν : N, q (δ₀ * ν) = q δ₀ := fun ν => by
      exact QuotientGroup.eq.2 (by simp)
    have e3 : ∑' ν : N, h (δ₀ * ν) = ∑' ν : N, u (δ₀ * ν) :=
      tsum_congr fun ν => by simp only [hu, hq ν, if_true]
    have hsupp : Function.support u ⊆ Set.range fun ν : N => δ₀ * (ν : G) := by
      intro δ hδ
      have hδ' : q δ = q δ₀ := by
        by_contra hn; exact hδ (by simp only [hu, if_neg hn])
      have : δ₀⁻¹ * δ ∈ N := QuotientGroup.eq.1 hδ'.symm
      exact ⟨⟨_, this⟩, by simp⟩
    rw [e3, hinj.tsum_eq hsupp]
    have e4 : ∑' δ, u δ = ∑ δ ∈ S with q δ = q δ₀, u δ := by
      refine tsum_eq_sum fun δ hδ => ?_
      by_contra hne'
      have hq' : q δ = q δ₀ := by
        by_contra hn; exact hne' (by simp only [hu, if_neg hn])
      have hhδ : h δ ≠ 0 := by
        intro h0; exact hne' (by simp only [hu, if_pos hq', h0])
      have hN : δ₀⁻¹ * δ ∈ N := QuotientGroup.eq.1 hq'.symm
      have hc := h1 δ₀ hcl hne _ hN
      rw [mul_inv_cancel_left] at hc
      exact hδ (Finset.mem_filter.2 ⟨(hSm δ).2 ⟨hhδ, hc⟩, hq'⟩)
    rw [e4]
    exact Finset.sum_congr rfl fun δ hδ => by simp only [hu, if_pos (Finset.mem_filter.1 hδ).2]
  have hcardS : ((S.image q).card : ℝ) ≤ κ := by
    refine le_trans ?_ hcard
    rw [Set.ncard_eq_toFinset_card _ hfin]
    exact_mod_cast Finset.card_image_le
  rw [e0, e1]
  calc ‖∑ b ∈ S.image q, ∑ δ ∈ S with q δ = b, h δ‖ ≤ ((S.image q).card : ℝ) * β := by
        simpa using norm_sum_le_of_le (S.image q) e2
    _ ≤ κ * β := by gcongr

theorem set_sum_le {G : Type} (Cl : Set G) (h : G → ℂ) {M : ℝ} (hM : ∀ g, ‖h g‖ ≤ M) (hM0 : 0 ≤ M) {κ : ℝ}
    (hfin : (Function.support h ∩ Cl).Finite) (hcard : (((Function.support h ∩ Cl).ncard : ℕ) : ℝ) ≤ κ) :
    ‖∑' δ : Cl, h δ‖ ≤ κ * M := by
  classical
  set S := hfin.toFinset with hS
  have hSm : ∀ δ, δ ∈ S ↔ h δ ≠ 0 ∧ δ ∈ Cl := fun δ => by simp [hS]
  have e0 : ∑' δ : Cl, h δ = ∑ δ ∈ S, h δ := by
    rw [tsum_subtype Cl h]
    refine (tsum_eq_sum (s := S) fun δ hδ => ?_).trans (Finset.sum_congr rfl fun δ hδ => ?_)
    · by_cases hc : δ ∈ Cl
      · rw [Set.indicator_of_mem hc]; by_contra hne; exact hδ ((hSm δ).2 ⟨hne, hc⟩)
      · rw [Set.indicator_of_notMem hc]
    · rw [Set.indicator_of_mem ((hSm δ).1 hδ).2]
  have hcardS : (S.card : ℝ) ≤ κ := by
    refine le_trans ?_ hcard
    rw [Set.ncard_eq_toFinset_card _ hfin]
  rw [e0]
  calc ‖∑ δ ∈ S, h δ‖ ≤ (S.card : ℝ) * M := by
        simpa using norm_sum_le_of_le S (fun δ _ => hM δ)
    _ ≤ κ * M := by gcongr

theorem continuous_classKernel {f : GA D V → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) {γ : GA D V}
    (hγ : γ ∈ GQ V) : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) γ f) := by
  have hmem : ∀ δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass (GQ V) γ, (δ : GA D V) ∈ GQ V :=
    fun ⟨δ, k, hk, e⟩ => e ▸ mul_mem (mul_mem (inv_mem hk) hγ) hk
  let ι : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass (GQ V) γ → GQ V := fun δ => ⟨δ, hmem δ⟩
  have hι : Function.Injective ι := fun a b e => Subtype.ext (congrArg (fun z : GQ V => (z : GA D V)) e)
  have hlf : LocallyFinite fun δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass (GQ V) γ =>
      Function.support fun x : GA D V => f (x⁻¹ * δ * x) := by
    intro x
    obtain ⟨C, hC, hx⟩ := exists_compact_mem_nhds x
    refine ⟨C, hx, ((GlobalTheory.AutomorphicL2KernelContinuous.finite_contributing (Γ := GQ V) hc hC hC).preimage hι.injOn).subset ?_⟩
    rintro δ ⟨y, h, h1⟩
    exact ⟨y, h1, y, h1, h⟩
  have h : Continuous fun x : GA D V => ∑ᶠ δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass (GQ V) γ, f (x⁻¹ * δ * x) :=
    continuous_finsum (fun δ => by fun_prop) hlf
  refine h.congr fun x => ?_
  refine (tsum_eq_finsum ?_).symm
  exact ((GlobalTheory.AutomorphicL2Unitary.finite_support_kernel (Γ := GQ V) hc x x).preimage hι.injOn).subset fun δ hδ => hδ

theorem rat_mem (g : GF V) : rat V g ∈ GQ V := by
  rw [show GQ V = (rat V).range from (range_ratEmb ..).symm]; exact ⟨g, rfl⟩

def classEquiv (γ : GF V) : {δ : GF V | IsConj γ δ} ≃ GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass (GQ V) (rat V γ) :=
  Equiv.ofBijective (fun δ => ⟨rat V δ, by
      obtain ⟨c, hc⟩ := isConj_iff.1 δ.2
      refine ⟨rat V c⁻¹, rat_mem _, ?_⟩
      rw [← hc]; simp only [map_mul, map_inv, inv_inv]⟩)
    ⟨fun a b h => Subtype.ext (ratEmb_injective _ _ (congrArg Subtype.val h)), fun δ => by
      obtain ⟨δ, g, hg, rfl⟩ := δ
      rw [show GQ V = (rat V).range from (range_ratEmb ..).symm] at hg
      obtain ⟨c, rfl⟩ := hg
      refine ⟨⟨c⁻¹ * γ * c, isConj_iff.2 ⟨c⁻¹, by group⟩⟩, Subtype.ext ?_⟩
      simp only [map_mul, map_inv]⟩

theorem classKernel_eq (γ : GF V) (f : GA D V → ℂ) (x : GA D V) :
    GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f x = ∑' δ : {δ : GF V | IsConj γ δ}, f (x⁻¹ * rat V δ * x) :=
  ((classEquiv γ).tsum_eq fun δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass (GQ V) (rat V γ) => f (x⁻¹ * δ * x)).symm

theorem regSS_of_conj {γ δ : GF V} (h : IsConj γ δ) (hγ : IsRegSS γ.1.1) : IsRegSS δ.1.1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 h
  show IsRegSS ((g.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * γ.1.1 * ((g.1)⁻¹ : GL (Fin V.rank) D.host.E).1)
  unfold IsRegSS
  rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  exact hγ

theorem conj_id {G : Type} [Group G] (a ω d n : G) :
    (a * ω)⁻¹ * (d * n) * (a * ω) = ω⁻¹ * (a⁻¹ * d * a) * (a⁻¹ * n * a) * ω := by group

set_option maxHeartbeats 1000000 in
open GlobalTheory.SiegelSet in

theorem class_bound {X Y : Matrix (Fin V.rank) (Fin r) D.host.E} (hW : IsWittFrame D.sp.cm.sig V.gram X Y)
    {K : Subgroup (GA D V)} {Ω : Set (GA D V)} {c : ℝ} (hK : IsCompact (K : Set (GA D V))) (hΩ : IsCompact Ω)
    (hΩP : Ω ⊆ minParOne D.sp.cm.sig V.gram X) (hc : 0 < c)
    (hconj : ∃ C : Set (GA D V), IsCompact C ∧ ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a,
      IsTorusElt D.sp.cm.sig V.gram X Y t a → a⁻¹ * p * a ∈ C)
    {f : GA D V → ℂ} (hf : f ∈ CcGA V) (hcusp : MainStatements.RegularCuspidalTrace.IsCuspFn f) {γ : GF V} (hreg : IsRegSS γ.1.1) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt D.sp.cm.sig V.gram X Y t a → ∀ k ∈ K,
      ‖GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f (p * a * k)‖ ≤ B * ∏ i, (t i)⁻¹ ^ m := by
  obtain ⟨C₀, hC₀, hC₀m⟩ := hconj
  obtain ⟨hfc, hfs⟩ := GlobalTheory.Orb.continuous_of_mem_ccAd hf
  have hS : IsCompact (tsupport f) := hfs.isCompact
  set W : Set (GA D V) := C₀ * (K : Set (GA D V)) with hWdef
  have hWc : IsCompact W := hC₀.mul hK
  set C₁ : Set (GA D V) := W * tsupport f * W⁻¹ with hC₁
  have hC₁c : IsCompact C₁ := (hWc.mul hS).mul hWc.inv
  obtain ⟨A₁, B₁, hcnt⟩ := GlobalTheory.T.finite_lattice_points_in_siegel_set_bound D V r X Y hW c hc C₁ hC₁c
  have hdec := fun j : Fin r => MainStatements.WeightKernel.Dec.decay_holds D V r X Y hW c hc j f hf
    (hcusp _ (IsoFlag.proper_single _)) (W⁻¹ * C₁) W (hWc.inv.mul hC₁c) hWc
  choose A hA using hdec
  obtain ⟨t1, ht1⟩ := GlobalTheory.CompanionTheory.FlagKey.flag_key _ _ D.sp.cm.sig (isCMExt_host D) V.rank V.gram (GlobalTheory.Doubling.isHermND_gram V) r X Y hW
    Ω hΩ hΩP K hK c hc (tsupport f) hS
  obtain ⟨c₀, hc₀, hlow⟩ := cone_lower (r := r) hc
  obtain ⟨M, hM⟩ := hfc.bounded_above_of_compact_support hfs
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  set R₀ : ℝ := max 1 (max t1 (t1 / c₀)) with hR₀
  have hR1 : 1 ≤ R₀ := le_max_left _ _
  have hRt : t1 ≤ R₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hRt' : t1 / c₀ ≤ R₀ := (le_max_right _ _).trans (le_max_right _ _)
  set A₂ : ℕ := ∑ j, A j with hA₂
  set m' : ℕ := r * r * (A₁ + A₂ + m) with hm'
  choose Bj hBj using fun j => hA j m'
  set B₂ : ℝ := ∑ j, |Bj j| with hB₂
  have hB₂0 : 0 ≤ B₂ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set B₁' : ℝ := |B₁| with hB₁'
  have hB₁0 : 0 ≤ B₁' := abs_nonneg _
  refine ⟨B₁' * M * R₀ ^ (r * r * (A₁ + m)) + B₁' * B₂, by positivity, ?_⟩
  intro p hp t ht a ha k hk
  have tpos := ht.1
  set T : ℝ := ∏ i, max (t i) 1 with hT
  have hT1 : 1 ≤ T := one_le_prod_max t
  set ω : GA D V := a⁻¹ * p * a * k with hω
  have hωW : ω ∈ W := Set.mul_mem_mul (hC₀m p hp t ht a ha) hk
  have hx : p * a * k = a * ω := by rw [hω]; group
  set x : GA D V := p * a * k with hxdef
  set h : GF V → ℂ := fun δ => f (x⁻¹ * rat V δ * x) with hh
  set Cl : Set (GF V) := {δ | IsConj γ δ} with hCl
  have hsub : ∀ δ, h δ ≠ 0 → a⁻¹ * rat V δ * a ∈ C₁ := by
    intro δ hδ
    have h1 : x⁻¹ * rat V δ * x ∈ tsupport f := subset_tsupport f hδ
    have e : a⁻¹ * rat V δ * a = ω * (x⁻¹ * rat V δ * x) * ω⁻¹ := by rw [hx]; group
    rw [e]
    exact Set.mul_mem_mul (Set.mul_mem_mul hωW h1) (Set.inv_mem_inv.2 hωW)
  obtain ⟨hfin0, hcard0⟩ := hcnt t ht a ha
  have hss : Function.support h ∩ Cl ⊆ {δ : GF V | a⁻¹ * rat V δ * a ∈ C₁} := fun δ hδ => hsub δ hδ.1
  have hfin : (Function.support h ∩ Cl).Finite := hfin0.subset hss
  have hcard : (((Function.support h ∩ Cl).ncard : ℕ) : ℝ) ≤ B₁' * T ^ A₁ := by
    have h1 : (Function.support h ∩ Cl).ncard ≤ {δ : GF V | a⁻¹ * rat V δ * a ∈ C₁}.ncard := Set.ncard_le_ncard hss hfin0
    have h2 : B₁ * T ^ A₁ ≤ B₁' * T ^ A₁ := by gcongr; exact le_abs_self _
    exact le_trans (by exact_mod_cast h1) (hcard0.trans h2)
  rw [classKernel_eq]
  by_cases hsh : ∀ j, root t j ≤ R₀
  ·
    have h1 := set_sum_le Cl h (fun _ => hM _) hM0 hfin hcard
    have h2 : T ≤ R₀ ^ (r * r) := prod_max_le tpos hR1 hsh
    have h3 := inv_pow_le_prod tpos hR1 hsh m
    have hR0 : 0 < R₀ := by linarith
    have h4 : T ^ A₁ ≤ R₀ ^ (r * r * A₁) := by
      rw [pow_mul]; gcongr
    have hP : 0 ≤ ∏ i, (t i)⁻¹ ^ m := Finset.prod_nonneg fun i _ => by have := tpos i; positivity
    calc ‖∑' δ : Cl, h δ‖ ≤ B₁' * T ^ A₁ * M := h1
      _ ≤ B₁' * R₀ ^ (r * r * A₁) * M := by gcongr
      _ = B₁' * M * R₀ ^ (r * r * (A₁ + m)) * R₀⁻¹ ^ (r * r * m) := by
          rw [mul_add, pow_add, inv_pow]; field_simp
      _ ≤ B₁' * M * R₀ ^ (r * r * (A₁ + m)) * ∏ i, (t i)⁻¹ ^ m := by gcongr
      _ ≤ _ := by
          rw [add_mul]
          have : 0 ≤ B₁' * B₂ * ∏ i, (t i)⁻¹ ^ m := by positivity
          linarith
  ·
    push_neg at hsh
    obtain ⟨j₁, hj₁⟩ := hsh
    obtain ⟨j, -, hjmax⟩ := Finset.exists_max_image Finset.univ (root t) ⟨j₁, Finset.mem_univ _⟩
    set ρ : ℝ := root t j with hρ
    have hρR : R₀ < ρ := hj₁.trans_le (hjmax j₁ (Finset.mem_univ _))
    have hρ1 : 1 ≤ ρ := hR1.trans hρR.le
    have hρ0 : 0 < ρ := by linarith
    have hall : ∀ i, root t i ≤ ρ := fun i => hjmax i (Finset.mem_univ _)
    have hc1 : t1 < t j := by
      by_cases hl : j.val + 1 < r
      · have e : ρ = t j / t ⟨j.val + 1, hl⟩ := by rw [hρ, root, dif_pos hl]
        have hp := tpos ⟨j.val + 1, hl⟩
        have h2 : R₀ * t ⟨j.val + 1, hl⟩ < t j := by
          rw [e, lt_div_iff₀ hp] at hρR; exact hρR
        have h3 := hlow t ht ⟨j.val + 1, hl⟩
        have h4 : t1 / c₀ * c₀ ≤ R₀ * t ⟨j.val + 1, hl⟩ := by
          have : 0 ≤ R₀ := by linarith
          exact mul_le_mul hRt' h3 hc₀.le this
        rw [div_mul_cancel₀ _ hc₀.ne'] at h4
        linarith
      · have e : ρ = t j := by rw [hρ, root, dif_neg hl]
        rw [← e]; linarith
    have hc2 : ∀ j' : Fin r, j'.val = j.val + 1 → t1 * t j' < t j := by
      intro j' hj'
      have hl : j.val + 1 < r := hj' ▸ j'.2
      have e : ρ = t j / t ⟨j.val + 1, hl⟩ := by rw [hρ, root, dif_pos hl]
      have e' : j' = ⟨j.val + 1, hl⟩ := Fin.ext hj'
      have hp := tpos j'
      rw [e', ] at hp ⊢
      rw [e, lt_div_iff₀ hp] at hρR
      exact lt_of_le_of_lt (by gcongr) hρR
    have hstab : ∀ δ, h δ ≠ 0 → δ ∈ (frameFlag (isIsoFrame_firstCols hW j)).parRat D.sp.cm := by
      intro δ hδ
      exact GlobalTheory.T.mem_parabolic_of_flag_preserving D V r X Y hW j δ
        (ht1 p hp t ht a ha k hk δ (subset_tsupport f hδ) j hc1 hc2)
    have hmul : ∀ δ ∈ Cl, h δ ≠ 0 → ∀ ν ∈ (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm, δ * ν ∈ Cl := by
      intro δ hδ hne ν hν
      obtain ⟨g, hg⟩ := GlobalTheory.T.regular_semisimple_conjugate_unipotent_translate D V _ _ (isIsoFrame_firstCols hW j) δ (regSS_of_conj hδ hreg) (hstab δ hne) ν hν
      exact IsConj.trans hδ (isConj_iff.2 ⟨g, hg⟩)
    have hT' : T ≤ ρ ^ (r * r) := prod_max_le tpos hρ1 hall
    set β : ℝ := B₂ * T ^ A₂ * ρ⁻¹ ^ m' with hβ
    have hβ0 : 0 ≤ β := by positivity
    have hsum : ∀ δ ∈ Cl, h δ ≠ 0 →
        ‖∑' ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm, h (δ * ν)‖ ≤ β := by
      intro δ hδ hne
      have hy := hsub δ hne
      have hb := hBj j t ht a ha (ω⁻¹ * (a⁻¹ * rat V δ * a)) (Set.mul_mem_mul (Set.inv_mem_inv.2 hωW) hy) ω hωW
      have e : ∀ ν : (frameFlag (isIsoFrame_firstCols hW j)).unipRat D.sp.cm,
          h (δ * ν) = f (ω⁻¹ * (a⁻¹ * rat V δ * a) * (a⁻¹ * rat V ν * a) * ω) := fun ν => by
        have e1 : (rat V) (δ * (ν : GF V)) = rat V δ * rat V ν := map_mul _ _ _
        simp only [hh, e1, hx]
        rw [conj_id]
      simp only [e]
      refine hb.trans ?_
      have h1 : Bj j ≤ B₂ := (le_abs_self _).trans
        (Finset.single_le_sum (f := fun j => |Bj j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j))
      have h2 : T ^ A j ≤ T ^ A₂ := pow_le_pow_right₀ hT1
        (Finset.single_le_sum (f := A) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
      have h3 : (0 : ℝ) ≤ ρ⁻¹ ^ m' := by positivity
      have h4 : (0 : ℝ) ≤ T ^ A j := by positivity
      rw [hβ]
      gcongr
    have h1 := coset_sum _ Cl h hβ0 hfin hcard hmul hsum
    have hP := inv_pow_le_prod tpos hρ1 hall m
    have hP0 : 0 ≤ ∏ i, (t i)⁻¹ ^ m := le_trans (by positivity) hP
    have h5 : T ^ A₁ ≤ ρ ^ (r * r * A₁) := by rw [pow_mul]; gcongr
    have h6 : T ^ A₂ ≤ ρ ^ (r * r * A₂) := by rw [pow_mul]; gcongr
    have h7 : ρ ^ (r * r * A₁) * ρ ^ (r * r * A₂) * ρ⁻¹ ^ m' = ρ⁻¹ ^ (r * r * m) := by
      have ha : ρ ^ (r * r * A₁) ≠ 0 := by positivity
      have hb : ρ ^ (r * r * A₂) ≠ 0 := by positivity
      rw [hm', mul_add, mul_add, pow_add, pow_add, inv_pow, inv_pow]
      field_simp
    calc ‖∑' δ : Cl, h δ‖ ≤ B₁' * T ^ A₁ * β := h1
      _ = B₁' * B₂ * (T ^ A₁ * T ^ A₂ * ρ⁻¹ ^ m') := by rw [hβ]; ring
      _ ≤ B₁' * B₂ * (ρ ^ (r * r * A₁) * ρ ^ (r * r * A₂) * ρ⁻¹ ^ m') := by gcongr
      _ = B₁' * B₂ * ρ⁻¹ ^ (r * r * m) := by rw [h7]
      _ ≤ B₁' * B₂ * ∏ i, (t i)⁻¹ ^ m := by gcongr
      _ ≤ _ := by
          rw [add_mul]
          have : 0 ≤ B₁' * M * R₀ ^ (r * r * (A₁ + m)) * ∏ i, (t i)⁻¹ ^ m := by
            have : 0 < R₀ := by linarith
            positivity
          linarith

end MainStatements.WeightKernel.RegInt

namespace MainStatements.WeightKernel.RegInt
open GlobalTheory.SiegelSet in

theorem regClassInt : PositivityTheory.ThKR.SiegelCore → MainStatements.RegularCuspidalTrace.RegClassInt := by
  intro hcore D V μ _ f hf hcusp γ hreg
  have hknown := PositivityTheory.ThKR.siegel_of_core hcore
  have hcm := isCMExt_host D
  have hJ := GlobalTheory.Doubling.isHermND_gram V
  obtain ⟨r, X, Y, hWF⟩ := exists_isWittFrame hcm hJ
  obtain ⟨K, Ω, c, hK, hΩ, hΩP, hc, -, hcl, hcov, hconj, hmeas, -, -⟩ := hknown _ _ D.sp.cm.sig hcm _ _ hJ r X Y hWF
  obtain ⟨-, Cm, hbd⟩ := hmeas μ inferInstance
  obtain ⟨hfc, hfs⟩ := GlobalTheory.Orb.continuous_of_mem_ccAd hf
  have hcont : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f) :=
    continuous_classKernel hfc hfs (rat_mem γ)
  refine GlobalTheory.CompanionTheory.AutCover.integrable_descend_of_cover D V μ _ hcl.measurableSet hcov _ (fun δ hδ x => GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel_mul _ _ hδ x)
    hcont.measurable ?_
  obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.cone_integral_finite_large_exponent D.host.F V.rank r c hc
  obtain ⟨B, hB0, hB⟩ := class_bound hWF hK hΩ hΩP hc hconj hf hcusp hreg m₀
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  have hm := hm₀ m₀ le_rfl
  set w : (Fin r → ℝ) → ENNReal := fun t => ENNReal.ofReal ((modulus D.host.F V.rank t * ∏ i, t i)⁻¹) with hw
  set q : (Fin r → ℝ) → ENNReal := fun t => ENNReal.ofReal (∏ i, (t i)⁻¹ ^ m₀) with hq
  have hqm : Measurable q := by
    refine ENNReal.measurable_ofReal.comp ?_
    refine Finset.measurable_prod _ fun i _ => ?_
    exact ((measurable_pi_apply i).inv).pow_const _
  have h1 := hbd (fun g => ‖GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f g‖ₑ)
    (fun t => ENNReal.ofReal B * q t) (hqm.const_mul _) (fun p hp t ht a ha k hk => by
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul hB0]
      exact ENNReal.ofReal_le_ofReal (hB p hp t ht a ha k hk))
  have h2 : ∫⁻ t in cone r c, ENNReal.ofReal B * q t * w t =
      ENNReal.ofReal B * ∫⁻ t in cone r c, q t * w t := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_congr fun t => mul_assoc _ _ _
  rw [HasFiniteIntegral]
  refine lt_of_le_of_lt h1 ?_
  rw [h2]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hm)

end MainStatements.WeightKernel.RegInt
end
end
