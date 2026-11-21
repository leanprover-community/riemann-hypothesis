import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PairingMulFirstChern
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnLogNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalisationGenericSmoothCover
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithVarComplexPointsCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrableRegularVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFiberArithmeticVarietyIntegralProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionGenericFiberPullbackLocalIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralPointClosureClosedSubscheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFiberArithmeticVarietyIntegralProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasureIntegralEqGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightOneIffPointClosureDimProjArith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithReciprocityNoCommonDivisorProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchLogNormIntegralEqSumEmbeddings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchRestrictedEqZeroOfNoComplexPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveArakelovFormulaRhsTensorAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightOneIffPointClosureDimProjArithStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionCalculusCycleHeightsOfAnalytic

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

open Set Filter Topology

namespace GlobalTheory.LogNormIntGen

theorem archIntegrable : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {D : ℕ}, IsArithVar p D → GenSmooth p D → ∀ (M N : HermLB p) {r : N.B.ι → X.functionFieldˣ}
      (hr : IsRatSec N.B r), M.ArchIntegrable N D hr := by
  intro k _ X _ p D hX hs M N r hr σ
  have := hX.compactSpace σ
  have := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  obtain ⟨R⟩ := hs σ
  have hσ : Function.Injective σ := ChernNull.injective_of_arithVar hX σ
  have key (ε : ℤˣ) : IntegrableOn (logNorm (N.φ σ) r) (offSupp p σ (N.div hr))
      ((M.φ σ).chernPart D ε) := by
    have h (y : CxPts p σ) : ∃ O ∈ 𝓝 y, IntegrableOn (logNorm (N.φ σ) r)
        (offSupp p σ (N.div hr) ∩ O) ((M.φ σ).chernPart D ε) :=
      have ⟨_, hi⟩ := R.cover y
      LogNormInt.exists_integrableOn hσ (M.cInf σ) (N.cInf σ) hr ε _ hi
    choose O hO hint using h
    obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover O fun y _ => hO y
    refine ((integrableOn_finset_iUnion (s := t)).2 fun y _ => hint y).mono_set fun z hz => ?_
    obtain ⟨y, hy, hz'⟩ := mem_iUnion₂.1 (ht (mem_univ z))
    exact mem_iUnion₂.2 ⟨y, hy, hz, hz'⟩
  exact ⟨key 1, key (-1)⟩

end GlobalTheory.LogNormIntGen
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logNorm_rationalSection_archIntegrable : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}, IsArithVar p D → GenSmooth p D → ∀ (M N : HermLB p) {r : N.B.ι → X.functionFieldˣ} (hr : IsRatSec N.B r), M.ArchIntegrable N D hr := by
  atlas_forward_decl GlobalTheory.LogNormIntGen.archIntegrable
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArchIntGenSmooth

open Set

theorem archIntegrable : Published.Principalisation → ∀ (k : Type) [CommRing k] (Y : Scheme.{0})
    [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ), IsArithVar q e → ∀ (M N : HermLB q)
    (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), N.ArchIntegrable M e hr := by
  intro hP k _ Y _ q e hY M N r hr σ
  obtain ⟨Y', ρ, _, hcov, hgs⟩ := GlobalTheory.GenSmoothCover.exists_isCov_genSmooth hP k Y q e hY
  have hη : ρ (genericPoint Y') ⤳ genericPoint Y := hcov.2.1 ▸ specializes_rfl
  have hr' := MultPull.isRatSec_pull_map ρ hη hr
  have hup := GlobalTheory.T.logNorm_rationalSection_archIntegrable hcov.1 hgs (N.restr ρ) (M.restr ρ) hr' σ
  have hsub : ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl) ⊆
      offSupp (ρ ≫ q) σ ((M.restr ρ).div hr') := fun y hy =>
    GlobalTheory.ArchIntAlter.mem_offSupp_pull M ρ hη hr hy
  have hm : MeasurableSet (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl)) :=
    (isOpen_ptsIn _).measurableSet
  have heq : EqOn (logNorm ((M.restr ρ).φ σ) fun c => Units.map
      (TrueGeo.SmallSec.fnMap ρ hη).toMonoidHom (r (c PUnit.unit)))
      (fun y => logNorm (M.φ σ) r (PtsOver.map ρ rfl _ y))
      (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ (M.div hr).supp.compl)) := fun y hy =>
    GlobalTheory.ArchIntAlter.logNorm_pull M ρ hη hr hy
  exact GlobalTheory.T.chernIntegrableOn_descend_genericallyFinite k Y q e hY Y' ρ hcov.1 hcov.2.1 hcov.2.2 N σ _ _
    (GlobalTheory.ArchIntAlter.continuousOn_logNorm (M.φ σ) hr (M.cInf σ))
    ⟨(hup.1.mono_set hsub).congr_fun heq hm, (hup.2.mono_set hsub).congr_fun heq hm⟩

end GlobalTheory.ArchIntGenSmooth
end
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.ArchIntegClosing

theorem archInteg : GlobalTheory.Published.Principalisation → GlobalTheory.MixHt.ArchInteg :=
  fun hP k _ Y _ q e hY M N r hr => GlobalTheory.ArchIntGenSmooth.archIntegrable hP k Y q e hY M N r hr

end GlobalTheory.ArchIntegClosing
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archLogNormChernIntegrable_of_principalisation : GlobalTheory.Published.Principalisation → GlobalTheory.MixHt.ArchInteg := by
  atlas_forward_decl GlobalTheory.ArchIntegClosing.archInteg
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix.BcPull

theorem isom_of_chart {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} (L M : MLine p σ)
    (e : M.B.ι → L.B.ι) (hU : ∀ a, M.B.U a ≤ L.B.U (e a))
    (hg : ∀ (x : X) a a', x ∈ M.B.U a → x ∈ M.B.U a' →
      gm (𝟙 X) x (M.B.U a ⊓ M.B.U a') (M.B.g a a') = gm (𝟙 X) x (L.B.U (e a) ⊓ L.B.U (e a')) (L.B.g (e a) (e a')))
    (hφ : ∀ a, ∀ y ∈ ptsIn p σ (M.B.U a), M.φ.φ a y = L.φ.φ (e a) y) : L.Isom M := by
  have le (c : M.B.ι × L.B.ι) : M.B.U c.1 ⊓ L.B.U c.2 ≤ L.B.U (e c.1) ⊓ L.B.U c.2 := inf_le_inf_right _ (hU c.1)
  refine ⟨⟨fun c => res (le c) (L.B.g (e c.1) c.2)⟩, fun c c' => Geo.Tor.unit_ext fun x hx => ?_, fun a b y ha hb => ?_⟩
  · have hx' : x ∈ M.B.U c.1 ⊓ L.B.U c.2 ⊓ (M.B.U c'.1 ⊓ L.B.U c'.2) := hx
    refine ((Geo.Tor.gm_res (𝟙 X) x _ hx _).trans (Geo.Tor.gm_res (𝟙 X) x (le c) hx'.1 _)).trans (Eq.symm ?_)
    refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (Geo.Tor.gm_div L.B M.B (𝟙 X) x c c' hx')
      ((Geo.Tor.gm_res (𝟙 X) x _ hx _).trans (Geo.Tor.gm_res (𝟙 X) x (le c') hx'.2 _))).trans ?_)
    have h₁ := Geo.Tor.gm_cocycle L.φ.isLB (𝟙 X) x (hU _ hx'.1.1) (hU _ hx'.2.1) hx'.2.2
    have h₂ := Geo.Tor.gm_cocycle L.φ.isLB (𝟙 X) x (hU _ hx'.1.1) hx'.1.2 hx'.2.2
    rw [hg x _ _ hx'.1.1 hx'.2.1, mul_right_comm, h₁, ← h₂, mul_inv_cancel_right]
  · rw [hφ a y ha, L.φ.trans (e a) b y (ptsIn_mono (hU a) ha) hb, sub_add_eq_add_sub, eq_sub_iff_add_eq]
    exact congrArg (fun z : ℂ => _ + Real.log (‖z‖ ^ 2))
      (CxPts.ev_res (le (a, b)) (mem_ptsIn_inf.2 ⟨ha, hb⟩) _).symm

theorem bc_φ {k K : Type} [CommRing k] [CommRing K] {X G : Scheme.{0}} {p : X ⟶ Sp k} {q : G ⟶ Sp K} {j : G ⟶ X}
    {ρ : k →+* K} (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) (A : MLine p (τ.comp ρ)) (i : PUnit → A.B.ι) (z : CxPts q τ) :
    (A.bc w τ).φ.φ i z = A.φ.φ (i PUnit.unit) (bcPt w τ z) :=
  (Fintype.sum_unique fun a : PUnit.{1} => ((1 : ℤ) : ℝ) * A.φ.φ (i a) (bcPt w τ z)).trans (by simp)

theorem bc_pull_isom : ∀ (k K : Type) [CommRing k] [CommRing K] (ρ : k →+* K) (X G Z G' : Scheme.{0}) (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (w : j ≫ p = q ≫ spMap ρ) (i : Z ⟶ X) (j' : G' ⟶ Z) (g : G' ⟶ G), g ≫ j = j' ≫ i → ∀ (w' : j' ≫ i ≫ p = (g ≫ q) ≫ spMap ρ) (τ : K →+* ℂ) (A : MLine p (τ.comp ρ)), ((A.pull i rfl).bc w' τ).Isom ((A.bc w τ).pull g rfl) := by
  intro k K _ _ ρ X G Z G' p q j w i j' g h w' τ A
  have hm (a : PUnit → PUnit → A.B.ι) (x : G') (hx : x ∈ ((A.B.pull j).pull g).U a) :
      x ∈ ((A.B.pull i).pull j').U a := by
    have h₀ : j (g x) ∈ A.B.U (a PUnit.unit PUnit.unit) := Geo.Tor.mem_pull.1 (Geo.Tor.mem_pull.1 hx)
    have h₁ : (g ≫ j) x ∈ A.B.U (a PUnit.unit PUnit.unit) := h₀
    rw [h] at h₁
    exact Geo.Tor.mem_pull.2 (Geo.Tor.mem_pull.2 h₁)
  refine isom_of_chart _ _ (fun a : PUnit → PUnit → A.B.ι => a) hm
    (fun x (a a' : PUnit → PUnit → A.B.ι) ha ha' => ?_) fun (a : PUnit → PUnit → A.B.ι) y _ => ?_
  · refine ((Geo.Tor.gm_pull_g (A.B.pull j) g (𝟙 G') x a a' ha ha').trans
      (Geo.Tor.gm_pull_g A.B j (𝟙 G' ≫ g) x _ _ (Geo.Tor.mem_pull.1 ha) (Geo.Tor.mem_pull.1 ha'))).trans (Eq.symm ?_)
    refine ((Geo.Tor.gm_pull_g (A.B.pull i) j' (𝟙 G') x a a' (hm a x ha) (hm a' x ha')).trans
      (Geo.Tor.gm_pull_g A.B i (𝟙 G' ≫ j') x _ _ (Geo.Tor.mem_pull.1 (hm a x ha))
        (Geo.Tor.mem_pull.1 (hm a' x ha')))).trans ?_
    rw [Category.assoc, Category.assoc, h]
  · refine (((A.bc w τ).φ.pull_φ g rfl a y).trans (bc_φ w τ A _ _)).trans (Eq.symm ?_)
    refine ((bc_φ w' τ (A.pull i rfl) a y).trans (A.φ.pull_φ i rfl _ _)).trans (congrArg _ (Subtype.ext ?_))
    change (y.1 ≫ j') ≫ i = (y.1 ≫ g) ≫ j
    rw [Category.assoc, Category.assoc, h]

end GlobalTheory.Mix.BcPull
end
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Mix.cycInt_genericFibre : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) (e : ℕ), IsArithVar p (e + 1) → ∀ (L : Fin e → MLine p (τ.comp (algebraMap k K))) (f : CxPts p (τ.comp (algebraMap k K)) → ℝ) (x : G), Order.coheight x = 1 → cycInt (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) x = cycInt L f (j x) := by
  intro k K _ _ _ _ X G _ p q j hp τ e hX L f x hx
  obtain ⟨hGi, hGn, hGproj, hGdim, hgen, hinj, hstalk, hcoh, hempty⟩ :=
    GlobalTheory.Mix.genericFibre_facts k K X G p q j hp (e + 1) hX
  obtain ⟨hZi, hZgen, hZdim, hZuniv⟩ := GlobalTheory.ClosFacts.clos_facts X (j x)
  obtain ⟨hxi, hxgen, -, hxuniv⟩ := GlobalTheory.ClosFacts.clos_facts G x

  have hK : CharZero K := by
    have := hX.charZero_base
    exact (RingHom.charZero_iff (IsFractionRing.injective k K)).1 inferInstance
  have hc : CharZero Γ(clos (j x), ⊤) := by
    obtain ⟨g0, hg0, -, -, -⟩ := hZuniv (clos x) (closι x ≫ j) (by
      simp only [Scheme.Hom.comp_apply, hxgen])
    have : IsDomain Γ(clos x, ⊤) := inferInstance
    let φ : K →+* Γ(clos x, ⊤) :=
      ((closι x ≫ q).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    have : CharZero Γ(clos x, ⊤) := (RingHom.charZero_iff φ.injective).1 hK
    exact g0.appTop.hom.charZero
  have hdim : topologicalKrullDim (clos (j x)) = (e + 1 : ℕ) := by
    rw [hZdim]
    have h1 := (GlobalTheory.MixHt.dimOne k X p (GlobalTheory.MixHt.isAmb_of_isArithVar hX) (e + 1) hX.dim_eq).1 (j x)
    exact h1.1 ((hcoh x).trans hx)
  have hZ : IsArithVar (closι (j x) ≫ p) e := hX.of_isClosedImmersion (closι (j x)) hc hdim
  haveI := hZi
  let G' := Limits.pullback (closι (j x) ≫ p) (spMap (algebraMap k K))
  let j' : G' ⟶ clos (j x) := Limits.pullback.fst _ _
  let q' : G' ⟶ Sp K := Limits.pullback.snd _ _
  have hp' : IsPullback j' q' (closι (j x) ≫ p) (spMap (algebraMap k K)) := IsPullback.of_hasPullback _ _
  obtain ⟨hG'i, -, hG'proj, -, hG'gen, -, -, -, -⟩ :=
    GlobalTheory.Mix.genericFibre_facts k K (clos (j x)) G' (closι (j x) ≫ p) q' j' hp' e hZ
  have hw : (j' ≫ closι (j x)) ≫ p = q' ≫ spMap (algebraMap k K) := by
    rw [Category.assoc]; exact hp'.w
  let g : G' ⟶ G := hp.lift (j' ≫ closι (j x)) q' hw
  have hg1 : g ≫ j = j' ≫ closι (j x) := hp.lift_fst _ _ hw
  have hg2 : g ≫ q = q' := hp.lift_snd _ _ hw
  have hp'' : IsPullback j' (g ≫ q) (closι (j x) ≫ p) (spMap (algebraMap k K)) := by rw [hg2]; exact hp'
  have hsq : IsPullback g j' j (closι (j x)) := IsPullback.of_right hp''.flip hg1 hp.flip
  have : IsClosedImmersion g := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip inferInstance
  have hgx : g (genericPoint G') = x := by
    apply hinj
    rw [← Scheme.Hom.comp_apply, hg1, Scheme.Hom.comp_apply, hG'gen, hZgen]
  have hproj'' : IsProjOver (g ≫ q) := by rw [hg2]; exact hG'proj
  obtain ⟨-, h1⟩ := GlobalTheory.T.mixed_chern_integral_point_closure_closed_subscheme K G G' q (g ≫ q) τ hGproj g rfl e (fun i => (L i).bc hp.w τ)
    (fun y => f (bcPt hp.w τ y))
  obtain ⟨-, h2⟩ := GlobalTheory.T.mixedChernMeasure_integral_eq_genericFibre k K (clos (j x)) G' (closι (j x) ≫ p) (g ≫ q) j' hp'' τ e hZ
    (fun i => (L i).pull (closι (j x)) rfl)
  have h3 := fun i => GlobalTheory.Mix.BcPull.bc_pull_isom k K (algebraMap k K) X G (clos (j x)) G' p q j hp.w (closι (j x)) j' g hg1
    hp''.w τ (L i)
  have h4 := GlobalTheory.T.mixedChernFormSignedPartMeasure_eq_of_isometric_projOver K G' (g ≫ q) τ hproj'' e _ _ h3
  conv_lhs => rw [← hgx]
  rw [h1]
  have h5 := (h2 (fun y => f (ptMap (closι (j x)) rfl _ y))).2
  change _ = Mix.int _ _
  rw [← h5]
  unfold Mix.int
  rw [h4 1, h4 (-1)]
  congr 2 <;> (funext y; exact congrArg f (Subtype.ext (by
    simp only [bcPt_val, PtsOver.map_val, ptMap, Category.assoc, hg1])))
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.horizontal_prime_divisor_integral_eq_generic_fibre : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) (e : ℕ), IsArithVar p (e + 1) → ∀ (L : Fin e → MLine p (τ.comp (algebraMap k K))) (f : CxPts p (τ.comp (algebraMap k K)) → ℝ) (x : G), Order.coheight x = 1 → cycInt (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) x = cycInt L f (j x) := by
  atlas_forward_decl GlobalTheory.Mix.cycInt_genericFibre
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem side_bc_eq : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral G] [IsLocallyNoetherian G] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) (e : ℕ), IsArithVar p (e + 1) → ∀ (Δ : CartierDiv X) (Δ' : CartierDiv G), (∀ x, Δ'.mult x = Δ.mult (j x)) → ∀ (N : MLine p (τ.comp (algebraMap k K))) (L : Fin e → MLine p (τ.comp (algebraMap k K))) (f g : CxPts p (τ.comp (algebraMap k K)) → ℝ), side (N.bc hp.w τ) (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) (fun y => g (bcPt hp.w τ y)) Δ' = side N L f g Δ := by
  intro k K _ _ _ _ X G _ _ _ _ p q j hp τ e hA Δ Δ' hΔ N L f g
  obtain ⟨_, _, _, _, _, hinj, _, hcoh, hemp⟩ := GlobalTheory.T.generic_fiber_arithmetic_variety_integral_projective k K X G p q j hp (e + 1) hA
  have hcons : (Fin.cons (N.bc hp.w τ) (fun i => (L i).bc hp.w τ) : Fin (e + 1) → MLine q τ) =
      fun i => ((Fin.cons N L : Fin (e + 1) → MLine p (τ.comp (algebraMap k K))) i).bc hp.w τ := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  have h1 := ((GlobalTheory.T.mixedChernMeasure_integral_eq_genericFibre k K X G p q j hp τ (e + 1) hA (Fin.cons N L)).2 f).2
  have hzero : ∀ z : X, z ∉ Set.range j → cycInt L g z = 0 := by
    intro z hz
    haveI := hemp z hz (τ.comp (algebraMap k K))
    simp [cycInt, Mix.int, MeasureTheory.integral_of_isEmpty]
  unfold side
  rw [hcons, h1]
  congr 1
  calc ∑ᶠ x, (Δ'.mult x : ℝ) * cycInt (fun i => (L i).bc hp.w τ) (fun y => g (bcPt hp.w τ y)) x
      = ∑ᶠ x, (Δ.mult (j x) : ℝ) * cycInt L g (j x) := by
        refine finsum_congr fun x => ?_
        rw [hΔ]
        by_cases h : Δ.mult (j x) = 0
        · simp [h]
        · rw [GlobalTheory.T.horizontal_prime_divisor_integral_eq_generic_fibre k K X G p q j hp τ e hA L g x
            (by rw [← hcoh]; exact CartierDiv.coheight_eq_one_of_mult_ne_zero h)]
    _ = ∑ᶠ z ∈ Set.range j, (Δ.mult z : ℝ) * cycInt L g z := (finsum_mem_range (f := fun z => (Δ.mult z : ℝ) * cycInt L g z) hinj).symm
    _ = ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L g z := by
        rw [finsum_mem_def]
        refine finsum_congr fun z => ?_
        by_cases hz : z ∈ Set.range j
        · simp [hz]
        · simp [hz, hzero z hz]

end GlobalTheory.Mix
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reciprocitySide_eq_genericFibre_pullback : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral G] [IsLocallyNoetherian G] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) (e : ℕ), IsArithVar p (e + 1) → ∀ (Δ : CartierDiv X) (Δ' : CartierDiv G), (∀ x, Δ'.mult x = Δ.mult (j x)) → ∀ (N : MLine p (τ.comp (algebraMap k K))) (L : Fin e → MLine p (τ.comp (algebraMap k K))) (f g : CxPts p (τ.comp (algebraMap k K)) → ℝ), side (N.bc hp.w τ) (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) (fun y => g (bcPt hp.w τ y)) Δ' = side N L f g Δ := by
  atlas_forward_decl GlobalTheory.Mix.side_bc_eq
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.MixRec

theorem injective_of_finite_int {k : Type} [CommRing k] [IsDomain k] [Module.Finite ℤ k]
    (σ : k →+* ℂ) : Function.Injective σ := by
  rw [injective_iff_map_eq_zero]
  have hker : RingHom.ker σ = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
    simp [hn]
  intro a ha
  have : a ∈ RingHom.ker σ := ha
  rwa [hker, Ideal.mem_bot] at this

theorem exists_extension {k : Type} [CommRing k] [IsDomain k] [Module.Finite ℤ k]
    (K : Type) [Field K] [Algebra k K] [IsFractionRing k K] (σ : k →+* ℂ) :
    ∃ τ : K →+* ℂ, σ = τ.comp (algebraMap k K) :=
  ⟨IsFractionRing.lift (A := k) (K := K) (injective_of_finite_int σ),
    RingHom.ext fun x => (IsFractionRing.lift_algebraMap (K := K) (injective_of_finite_int σ) x).symm⟩

theorem side_symm : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (e : ℕ), IsArithVar p (e + 1) → ∀ (σ : k →+* ℂ) (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro hP k _ X _ _ p e h σ
  haveI := h.isDomain
  haveI := h.finite
  obtain ⟨K, _, _, _⟩ : ∃ (K : Type) (_ : Field K) (_ : Algebra k K), IsFractionRing k K :=
    ⟨FractionRing k, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨τ, hτ⟩ := exists_extension K σ
  subst hτ
  intro L M N s hs t ht hcod
  obtain ⟨G, j, q, hp⟩ : ∃ (G : Scheme.{0}) (j : G ⟶ X) (q : G ⟶ Sp K),
      IsPullback j q p (spMap (algebraMap k K)) := ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  obtain ⟨hGi, hGn, hproj, hdim, hgen, -, hstalk, hcoh, -⟩ :=
    GlobalTheory.T.generic_fiber_arithmetic_variety_integral_projective k K X G p q j hp (e + 1) h
  obtain ⟨s', hs', hsl, hsm, hslog⟩ := GlobalTheory.T.exists_section_generic_fiber_pullback_local_iso k K X G p q j hp τ hstalk M s hs hgen
  obtain ⟨t', ht', htl, htm, htlog⟩ := GlobalTheory.T.exists_section_generic_fiber_pullback_local_iso k K X G p q j hp τ hstalk N t ht hgen
  have hcod' : ∀ z : G, Order.coheight z = 1 → z ∈ nonzeroLocus s' ∨ z ∈ nonzeroLocus t' := by
    intro z hz
    rw [hsl, htl]
    exact hcod (j z) ((hcoh z).trans hz)
  have hrec := GlobalTheory.T.arithReciprocity_noCommonDivisor_projective hP K G q τ e hproj hdim (fun i => (L i).bc hp.w τ) (M.bc hp.w τ)
    (N.bc hp.w τ) s' hs' t' ht' hcod'
  have e1 := GlobalTheory.T.reciprocitySide_eq_genericFibre_pullback k K X G p q j hp τ e h _ _ hsm N L (M.logSec s) (N.logSec t)
  have e2 := GlobalTheory.T.reciprocitySide_eq_genericFibre_pullback k K X G p q j hp τ e h _ _ htm M L (N.logSec t) (M.logSec s)
  have hsf : (M.bc hp.w τ).logSec s' = fun y => M.logSec s (bcPt hp.w τ y) := funext hslog
  have htf : (N.bc hp.w τ).logSec t' = fun y => N.logSec t (bcPt hp.w τ y) := funext htlog
  rw [hsf, htf] at hrec
  exact e1.symm.trans (hrec.trans e2)

end GlobalTheory.MixRec
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_reciprocity_at_complex_embedding : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (e : ℕ), IsArithVar p (e + 1) → ∀ (σ : k →+* ℂ) (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  atlas_forward_decl GlobalTheory.MixRec.side_symm
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.MixHt

theorem logSec_restr_secPull {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} (N : HermLB p) (t : N.B.Sec)
    (i : Y ⟶ X) (σ : k →+* ℂ) :
    (MLine.ofHerm (N.restr i) σ).logSec (Cartier.secPull t i) =
      fun y => (MLine.ofHerm N σ).logSec t (ptMap i rfl σ y) :=
  funext fun y => congrArg (fun a => Real.log a / 2) ((N.φ σ).nsq_pull_secPull i rfl t y)

theorem resArch_eq_finsum_cycInt : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (e : ℕ), IsArithVar p (e + 1) → ∀ (L : Fin e → HermLB p) (N : HermLB p) (t : N.B.Sec) (z : X), Order.coheight z = 1 → z ∈ nonzeroLocus t → MixHt.resArch L N t z = ∑ᶠ σ : k →+* ℂ, cycInt (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm N σ).logSec t) z := by
  intro hP k _ X _ _ p e hX L N t z hz htz
  have hamb : IsAmb p := isAmb_of_isArithVar hX
  have hgen : genericPoint (clo z) ∈ nonzeroLocus (Cartier.secPull t (cloι z)) := by
    rw [Cartier.nonzeroLocus_secPull]
    show cloι z (genericPoint (clo z)) ∈ nonzeroLocus t
    rw [cloι_genericPoint]; exact htz
  have hd : topologicalKrullDim (clo z) = (e + 1 : ℕ) :=
    ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k X p hamb (e + 1) hX.dim_eq).2 z (genericPoint (clo z)) hz).1
  have hamb' : IsAmb (cloι z ≫ p) := hamb.sub (cloι z)
  have hc (σ : k →+* ℂ) := (GlobalTheory.T.mixed_chern_integral_point_closure_closed_subscheme k X (clo z) p (cloι z ≫ p) σ hX.isProjOver (cloι z) rfl e
    (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm N σ).logSec t)).2
  simp only [cloι_genericPoint] at hc
  refine (dif_pos hgen).trans ?_
  rcases isArithVar_or_isEmpty hamb' hd with hv | hE
  · refine (GlobalTheory.T.mixedArchLogNormIntegral_eq_sum_embeddings hP k (clo z) (cloι z ≫ p) e hv (fun a => (L a).restr (cloι z)) (N.restr (cloι z))
      (Cartier.secPull t (cloι z)) hgen).trans (finsum_congr fun σ => ?_)
    rw [hc σ, logSec_restr_secPull]
    rfl
  · refine (mixArch_eq_zero_of_isEmpty hE _ _ _).trans (finsum_eq_zero_of_forall_eq_zero fun σ => ?_).symm
    rw [hc σ]
    haveI := hE σ
    simp only [Mix.int, MeasureTheory.integral_of_isEmpty, sub_zero]

end GlobalTheory.MixHt
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictedArchIntegral_eq_sum_closureIntegrals : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (e : ℕ), IsArithVar p (e + 1) → ∀ (L : Fin e → HermLB p) (N : HermLB p) (t : N.B.Sec) (z : X), Order.coheight z = 1 → z ∈ nonzeroLocus t → MixHt.resArch L N t z = ∑ᶠ σ : k →+* ℂ, cycInt (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm N σ).logSec t) z := by
  atlas_forward_decl GlobalTheory.MixHt.resArch_eq_finsum_cycInt
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.MixHt

theorem archRecip_of_principalisation (hP : GlobalTheory.Published.Principalisation) : ArchRecip := by
  intro k _ Y _ _ q e hq M N L s t hs ht hcov
  have : IsNoetherian Y := hq.isNoetherian
  have : Finite (k →+* ℂ) := hq.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have hcons (A : HermLB q) (σ : k →+* ℂ) :
      (fun i => MLine.ofHerm ((Fin.cons A L : Fin (e + 1) → HermLB q) i) σ) =
        Fin.cons (MLine.ofHerm A σ) (fun i => MLine.ofHerm (L i) σ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  have key (A B : HermLB q) (a : A.B.Sec) (b : B.B.Sec) (ha : genericPoint Y ∈ nonzeroLocus a)
      (hab : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus a ∨ z ∈ nonzeroLocus b) (z : Y) :
      ((divOfSec A.isLB a ha).mult z : ℝ) * resArch L B b z =
        ∑ σ : k →+* ℂ, ((divOfSec A.isLB a ha).mult z : ℝ) *
          cycInt (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm B σ).logSec b) z := by
    by_cases h0 : (divOfSec A.isLB a ha).mult z = 0
    · simp [h0]
    · have hz := CartierDiv.coheight_eq_one_of_mult_ne_zero h0
      have hza : z ∉ nonzeroLocus a := fun h =>
        (notMem_supp_divOfSec.2 h) (CartierDiv.mem_supp_of_mult_ne_zero h0)
      rw [GlobalTheory.T.restrictedArchIntegral_eq_sum_closureIntegrals hP k Y q e hq L B b z hz ((hab z hz).resolve_left hza), finsum_eq_sum_of_fintype,
        Finset.mul_sum]
  have fin (D : CartierDiv Y) (g : Y → ℝ) : (Function.support fun z => (D.mult z : ℝ) * g z).Finite :=
    D.finite_support_mult.subset fun z hz => by
      simp only [Function.mem_support] at hz ⊢
      intro h
      simp [h] at hz
  have hside (A B : HermLB q) (a : A.B.Sec) (b : B.B.Sec) (ha : genericPoint Y ∈ nonzeroLocus a)
      (hab : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus a ∨ z ∈ nonzeroLocus b) :
      mixArch (Fin.cons B L : Fin (e + 1) → HermLB q) A (isRatSec_ratOfSec a ha) +
          ∑ᶠ z, ((divOfSec A.isLB a ha).mult z : ℝ) * resArch L B b z =
        ∑ σ : k →+* ℂ, side (MLine.ofHerm B σ) (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm A σ).logSec a)
          ((MLine.ofHerm B σ).logSec b) (divOfSec (MLine.ofHerm A σ).φ.isLB a ha) := by
    rw [GlobalTheory.T.mixedArchLogNormIntegral_eq_sum_embeddings hP k Y q (e + 1) hq, finsum_eq_sum_of_fintype, finsum_congr (key A B a b ha hab),
      finsum_sum_comm _ _ (fun σ _ => fin _ _), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [side, ← hcons]
    rfl
  rw [hside M N s t hs hcov, hside N M t s ht fun z hz => (hcov z hz).symm]
  exact Finset.sum_congr rfl fun σ _ => GlobalTheory.T.arith_variety_reciprocity_at_complex_embedding hP k Y q e hq σ (fun i => MLine.ofHerm (L i) σ)
    (MLine.ofHerm M σ) (MLine.ofHerm N σ) s hs t ht hcov

end GlobalTheory.MixHt
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archLogNormReciprocity_of_principalisation : GlobalTheory.Published.Principalisation → GlobalTheory.MixHt.ArchRecip := by
  atlas_forward_decl GlobalTheory.MixHt.archRecip_of_principalisation
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem GlobalTheory.MixHt.arCalc_of_principalisation :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.ArCalc := fun h =>
  (GlobalTheory.T.arithIntersectionCalculus_cycleHeights_of_analytic (GlobalTheory.T.archLogNormChernIntegrable_of_principalisation h) (GlobalTheory.T.archLogNormReciprocity_of_principalisation h)).1
end
