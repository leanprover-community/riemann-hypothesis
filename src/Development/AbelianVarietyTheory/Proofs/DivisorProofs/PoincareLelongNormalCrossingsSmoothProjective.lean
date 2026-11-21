import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist
import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSncCoordinatesComplexPointSmoothVariety
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H0NeBotOfHorizontalFunction
import ReciprocityTheory.AnalyticForms.RegularLocalRings.WMultA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqSpanOnBasicOpensOfStalkPrincipal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleLogSectionNormProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableLogNormSectionMixedChernForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralEqMongeAmpereIntegralCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromSpecStalkMemZeroLocusIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MongeAmpereIntegralInvariantHomeomorphTransport

section
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.SncComp

theorem smooth_of_regular_stalk (K : Type) [Field K] [PerfectField K] (Y : Scheme.{0}) (q : Y ⟶ Sp K)
    [LocallyOfFiniteType q] (d : ℕ)
    (h : ∀ y : Y, IsClosed ({y} : Set Y) →
      IsRegularLocalRing (Y.presheaf.stalk y) ∧ ringKrullDim (Y.presheaf.stalk y) = d) :
    SmoothOfRelativeDimension d q := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace q
  choose A _ _ j _ pt hj hq using exists_affine_chart_over q
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Y (fun y => Spec (.of (A y))) j (fun y => ⟨y, pt y, hj y⟩)
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension d)
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension d) 𝒰 fun (y : Y) => ?_
  change SmoothOfRelativeDimension d (j y ≫ q)
  have hft : LocallyOfFiniteType (spMap (algebraMap K (A y))) := by
    have : LocallyOfFiniteType (j y ≫ q) := inferInstance
    rwa [hq y] at this
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
  have : Algebra.FiniteType K (A y) := RingHom.finiteType_algebraMap.mp hft
  rw [hq y]
  refine RegGenSmooth.smooth_of_regular K (A y) d fun m hm => ?_
  let w : Spec (.of (A y)) := (⟨m, inferInstance⟩ : PrimeSpectrum _)
  have hw : IsClosed ({w} : Set (Spec (.of (A y)))) := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hm
  have hc : IsClosed ({j y w} : Set Y) := by
    have h1 := (j y).isOpenEmbedding.preimage_closedPoints
    have h2 : w ∈ (j y) ⁻¹' closedPoints Y := by rw [h1]; exact hw
    exact h2
  obtain ⟨h1, h2⟩ := h _ hc
  let e := (asIso ((j y).stalkMap w) ≪≫ Spec.stalkIso (.of _) w).commRingCatIsoToRingEquiv
  exact ⟨IsRegularLocalRing.of_ringEquiv e, (ringKrullDim_eq_of_ringEquiv e).symm.trans h2⟩

theorem smooth_component : ∀ (F : Type) [Field F] [CharZero F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (e : ℕ), IsProjOver p → SmoothOfRelativeDimension (e + 1) p → ∀ (r : ℕ) (z : Fin r → X), (∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x) → ∀ a, SmoothOfRelativeDimension e (closι (z a) ≫ p) := by
  intro F _ _ X _ p e _ hsm r z hL a
  have : Smooth p := SmoothOfRelativeDimension.smooth (e + 1) p
  have hdim := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth p (e + 1) hsm
  refine smooth_of_regular_stalk F _ _ e fun y hy => ?_
  let I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z a})
  have hc : IsClosed ({closι (z a) y} : Set X) := by
    simpa using (closι (z a)).isClosedEmbedding.isClosedMap _ hy
  have hd := (ProperCut.ringKrullDim_stalk_eq p hc).trans hdim
  obtain ⟨hreg, n, t, ε, hR, hI⟩ := hL (closι (z a) y)
  have hmem : closι (z a) y ∈ Closeds.closure {z a} := by
    have := Vanishing.ι_mem_support I y
    have h := Scheme.IdealSheafData.coe_support_vanishingIdeal (Closeds.closure {z a})
    exact h.le this
  have hker : RingHom.ker ((closι (z a)).stalkMap y).hom = Ideal.span {t (ε ⟨a, hmem⟩)} :=
    (Vanishing.ker_stalkMap I y).trans (hI ⟨a, hmem⟩)
  have hm : t (ε ⟨a, hmem⟩) ∈ IsLocalRing.maximalIdeal _ := hR.1 ▸ Ideal.subset_span ⟨_, rfl⟩
  obtain ⟨h1, h2⟩ := isRegularLocalRing_quotient_of_not_mem_sq hm ((regular_params_spec t hR.1 hR.2).1 _)
  let φ := (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective ((closι (z a)).stalkMap_surjective y))
  refine ⟨IsRegularLocalRing.of_ringEquiv φ, ?_⟩
  rw [← ringKrullDim_eq_of_ringEquiv φ]
  rw [hd] at h2
  generalize ringKrullDim (X.presheaf.stalk (closι (z a) y) ⧸ Ideal.span {t (ε ⟨a, hmem⟩)}) = u at h2
  induction u using WithBot.recBotCoe with
  | bot => exact absurd h2 (by rw [WithBot.bot_add]; exact WithBot.bot_ne_coe)
  | coe u =>
    induction u using ENat.recTopCoe with
    | top => exact absurd (WithBot.coe_injective h2) (ENat.top_ne_coe _)
    | coe u =>
      have : u + 1 = e + 1 := by exact_mod_cast h2
      exact_mod_cast Nat.succ_injective this

end GlobalTheory.SncComp
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_snc_component_closure_charZero : ∀ (F : Type) [Field F] [CharZero F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (e : ℕ), IsProjOver p → SmoothOfRelativeDimension (e + 1) p → ∀ (r : ℕ) (z : Fin r → X), (∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x) → ∀ a, SmoothOfRelativeDimension e (closι (z a) ≫ p) := by
  atlas_forward_decl GlobalTheory.SncComp.smooth_component
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.DivSec

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {e : ℕ}

section Transport

variable {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (h : X ≃ₜ CxPts p σ)

def ChartsAlg : Prop := ∀ j, ∃ c : AlgChart p σ e, A.chart j = h.transOpenPartialHomeomorph c.finChart

variable {A h} (hA : ChartsAlg A h)

def algAtlas : FinHolAtlas e (CxPts p σ) where
  n := A.n
  chart j := (hA j).choose.finChart
  cover y := (A.cover (h.symm y)).imp fun j hj => by
    rw [(hA j).choose_spec, Homeomorph.transOpenPartialHomeomorph_source] at hj
    simpa using hj
  holo _ _ := AlgChart.analyticOnNhd_trans _ _

theorem isAlgAtlas_algAtlas : IsAlgAtlas (algAtlas hA) := fun _ => ⟨_, rfl⟩

theorem chart_eq (j : Fin A.n) :
    A.chart j = h.transOpenPartialHomeomorph ((algAtlas hA).chart j) := (hA j).choose_spec

theorem holoOn_comp_iff {S : Set (CxPts p σ)} {g : CxPts p σ → ℂ} :
    A.HoloOn (h ⁻¹' S) (g ∘ h) ↔ (algAtlas hA).HoloOn S g := by
  refine forall_congr' fun j => ?_
  rw [chart_eq hA j, Homeomorph.transOpenPartialHomeomorph_symm_apply,
    Homeomorph.transOpenPartialHomeomorph_target]
  have e1 : (g ∘ h) ∘ (h.symm ∘ ((algAtlas hA).chart j).symm) = g ∘ ((algAtlas hA).chart j).symm := by
    funext v; simp
  have e2 : (h.symm ∘ ((algAtlas hA).chart j).symm) ⁻¹' (h ⁻¹' S) = ((algAtlas hA).chart j).symm ⁻¹' S := by
    ext v; simp
  rw [e1, e2]

theorem smoothOn_comp_iff {S : Set (CxPts p σ)} {g : CxPts p σ → ℝ} :
    A.SmoothOn (h ⁻¹' S) (g ∘ h) ↔ (algAtlas hA).SmoothOn S g := by
  refine forall_congr' fun j => ?_
  rw [chart_eq hA j, Homeomorph.transOpenPartialHomeomorph_symm_apply,
    Homeomorph.transOpenPartialHomeomorph_target]
  have e1 : (g ∘ h) ∘ (h.symm ∘ ((algAtlas hA).chart j).symm) = g ∘ ((algAtlas hA).chart j).symm := by
    funext v; simp
  have e2 : (h.symm ∘ ((algAtlas hA).chart j).symm) ⁻¹' (h ⁻¹' S) = ((algAtlas hA).chart j).symm ⁻¹' S := by
    ext v; simp
  rw [e1, e2]

theorem isCompatChart_trans {ψ : OpenPartialHomeomorph (CxPts p σ) (Fin e → ℂ)}
    (hψ : IsCompatChart (algAtlas hA) ψ) : IsCompatChart A (h.transOpenPartialHomeomorph ψ) := fun j => by
  obtain ⟨h1, h2⟩ := hψ j
  rw [chart_eq hA j]
  simp only [Homeomorph.transOpenPartialHomeomorph_symm_apply, Homeomorph.transOpenPartialHomeomorph_apply,
    Homeomorph.transOpenPartialHomeomorph_target, Homeomorph.transOpenPartialHomeomorph_source]
  constructor
  · have e1 : (ψ ∘ h) ∘ (h.symm ∘ ((algAtlas hA).chart j).symm) = ψ ∘ ((algAtlas hA).chart j).symm := by
      funext v; simp
    have e2 : (h.symm ∘ ((algAtlas hA).chart j).symm) ⁻¹' (h ⁻¹' ψ.source) =
        ((algAtlas hA).chart j).symm ⁻¹' ψ.source := by
      ext v; simp
    rw [e1, e2]; exact h1
  · have e1 : (((algAtlas hA).chart j) ∘ h) ∘ (h.symm ∘ ψ.symm) = ((algAtlas hA).chart j) ∘ ψ.symm := by
      funext v; simp
    have e2 : (h.symm ∘ ψ.symm) ⁻¹' (h ⁻¹' ((algAtlas hA).chart j).source) =
        ψ.symm ⁻¹' ((algAtlas hA).chart j).source := by
      ext v; simp
    rw [e1, e2]; exact h2

theorem isPotential_pullback {L : LocPot (CxPts p σ)} (hL : IsPotential (algAtlas hA) L) :
    IsPotential A (L.pullback h h.continuous) := by
  refine ⟨fun x => (smoothOn_comp_iff hA).2 (hL.1 (h x)), fun x x' y hy => ?_⟩
  obtain ⟨W, hW, hyW, G, hG, e⟩ := hL.2 (h x) (h x') (h y) hy
  refine ⟨h ⁻¹' W, hW.preimage h.continuous, hyW, G ∘ h, (holoOn_comp_iff hA).2 hG, fun z hz => ?_⟩
  exact e (h z) ⟨⟨hz.1.1, hz.1.2⟩, hz.2⟩

theorem isSection_pullback {L : LocPot (CxPts p σ)} {s : CxPts p σ → CxPts p σ → ℂ}
    (hs : IsSection (algAtlas hA) L s) :
    IsSection A (L.pullback h h.continuous) (fun x z => s (h x) (h z)) :=
  ⟨fun x => (holoOn_comp_iff hA (g := s (h x))).2 (hs.1 (h x)),
    fun x x' y hy => hs.2 (h x) (h x') (h y) hy⟩

theorem isSNC_pullback {L : LocPot (CxPts p σ)} {s : CxPts p σ → CxPts p σ → ℂ} {r : ℕ} {m : Fin r → ℕ}
    {W : Fin r → Set (CxPts p σ)} (hs : IsSNC (algAtlas hA) L s m W) :
    IsSNC A (L.pullback h h.continuous) (fun x z => s (h x) (h z)) m (fun k => h ⁻¹' W k) := fun x => by
  obtain ⟨ψ, hc, hx, hsub, τ, hinj, hW, u, hu, hu0, he⟩ := hs (h x)
  refine ⟨h.transOpenPartialHomeomorph ψ, isCompatChart_trans hA hc, hx, fun z hz => hsub hz, τ, hinj,
    fun k => ?_, u ∘ h, ?_, fun z hz => hu0 (h z) hz, fun z hz => he (h z) hz⟩
  · ext z
    have := Set.ext_iff.1 (hW k) (h z)
    simpa [Homeomorph.transOpenPartialHomeomorph_source] using this
  · have := (holoOn_comp_iff hA (S := ψ.source) (g := u)).2 hu
    simpa [Homeomorph.transOpenPartialHomeomorph_source] using this

end Transport

section Data

variable {d m : ℕ} {R : AnRead p σ d} {C : Fin m → Closeds Y} {n : Fin m → CxPts p σ → ℝ}
  (hn : ∀ i, IsDivNorm R (C i) (n i))

def eqV (i : Fin m) (y : CxPts p σ) : Y.affineOpens := ((hn i).2 y).choose

def eqT (i : Fin m) (y : CxPts p σ) : Γ(Y, (eqV hn i y).1) := ((hn i).2 y).choose_spec.choose

def eqF (i : Fin m) (y : CxPts p σ) : CxPts p σ → ℝ := ((hn i).2 y).choose_spec.choose_spec.choose

theorem eq_spec (i : Fin m) (y : CxPts p σ) :
    y ∈ ptsIn p σ (eqV hn i y).1 ∧
      (Scheme.IdealSheafData.vanishingIdeal (C i)).ideal (eqV hn i y) = Ideal.span {eqT hn i y} ∧
      R.SmoothOn (ptsIn p σ (eqV hn i y).1) (eqF hn i y) ∧
      ∀ z ∈ ptsIn p σ (eqV hn i y).1, n i z ^ 2 = ‖ev p σ (eqV hn i y).1 (eqT hn i y) z‖ ^ 2 * Real.exp (-eqF hn i y z) :=
  ((hn i).2 y).choose_spec.choose_spec.choose_spec

def divPot : LocPot (CxPts p σ) where
  U y := ⋂ i, ptsIn p σ (eqV hn i y).1
  isOpen_U y := isOpen_iInter_of_finite fun i => isOpen_ptsIn _
  mem_U y := Set.mem_iInter.2 fun i => (eq_spec hn i y).1
  φ y z := ∑ i, eqF hn i y z / 2

def divSec (y z : CxPts p σ) : ℂ := ∏ i, ev p σ (eqV hn i y).1 (eqT hn i y) z

theorem mem_eqV {y z : CxPts p σ} (hz : z ∈ (divPot hn).U y) (i : Fin m) : z ∈ ptsIn p σ (eqV hn i y).1 :=
  Set.mem_iInter.1 hz i

theorem norm_divSec_mul {y z : CxPts p σ} (hz : z ∈ (divPot hn).U y) :
    ‖divSec hn y z‖ * Real.exp (-(divPot hn).φ y z) = ∏ i, n i z := by
  have h1 : ∀ i, n i z = ‖ev p σ (eqV hn i y).1 (eqT hn i y) z‖ * Real.exp (-eqF hn i y z / 2) := fun i => by
    have e := (eq_spec hn i y).2.2.2 z (mem_eqV hn hz i)
    have h0 := ((hn i).1 z).1
    have hx : Real.exp (-eqF hn i y z) = Real.exp (-eqF hn i y z / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hx, ← mul_pow] at e
    exact (pow_left_inj₀ h0 (by positivity) two_ne_zero).1 e
  simp only [divSec, divPot, norm_prod, h1]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 2
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem divSec_eq_zero_iff (y : CxPts p σ) : divSec hn y y = 0 ↔ ∃ i, LiesIn y (C i) := by
  simp only [divSec, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
  exact exists_congr fun i => ev_eq_zero_iff (eq_spec hn i y).2.1 (eq_spec hn i y).1

end Data

section Sec

variable {d m : ℕ} {R : AnRead p σ d} {C : Fin m → Closeds Y} {n : Fin m → CxPts p σ → ℝ}
  (hn : ∀ i, IsDivNorm R (C i) (n i))

theorem holoOn_divSec (y : CxPts p σ) : R.HoloOn ((divPot hn).U y) (divSec hn y) := fun j => by
  have h : ∀ i, DifferentiableOn ℂ
      (fun v => ev p σ (eqV hn i y).1 (eqT hn i y) ((R.chart j).e.symm v))
      ((R.chart j).e.target ∩ (R.chart j).e.symm ⁻¹' (divPot hn).U y) := fun i =>
    (R.holoOn_ev _ (eqT hn i y) j).mono fun v hv => ⟨hv.1, mem_eqV hn hv.2 i⟩
  have key : ∀ s : Finset (Fin m), DifferentiableOn ℂ
      (fun v => ∏ i ∈ s, ev p σ (eqV hn i y).1 (eqT hn i y) ((R.chart j).e.symm v))
      ((R.chart j).e.target ∩ (R.chart j).e.symm ⁻¹' (divPot hn).U y) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using differentiableOn_const (1 : ℂ)
    | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (h a).mul ih
  refine (key Finset.univ).congr fun v _ => ?_
  simp [divSec]

theorem isSection_divSec {B : FinHolAtlas d (CxPts p σ)} (hB : IsAlgAtlas B) :
    IsSection B (divPot hn) (divSec hn) :=
  ⟨fun y => (hB.holoOn_iff R ((divPot hn).isOpen_U y)).2 (holoOn_divSec hn y),
    fun _ _ _ hz => by rw [norm_divSec_mul hn hz.1, norm_divSec_mul hn hz.2]⟩

end Sec

end GlobalTheory.DivSec
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O
open GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh

namespace GlobalTheory.DivSec

theorem exists_rsp_replace : ∀ (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) (r : Fin n → R), Rsp R n r →
    ∀ (ι : Type) (e : ι ↪ Fin n) (s : ι → R), (∀ i, Ideal.span {s i} = Ideal.span {r (e i)}) →
    ∃ r' : Fin n → R, Rsp R n r' ∧ ∀ i, r' (e i) = s i := by
  intro R _ _ n r hR ι e s hs
  classical
  let r' : Fin n → R := fun j => if h : ∃ i, e i = j then s h.choose else r j
  have hr' : ∀ i, r' (e i) = s i := fun i => by
    have h : ∃ i', e i' = e i := ⟨i, rfl⟩
    simp only [r', dif_pos h]
    congr 1
    exact e.injective h.choose_spec
  refine ⟨r', ⟨?_, hR.2⟩, hr'⟩
  rw [← hR.1]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    by_cases h : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := h
      rw [hr']
      have : s i ∈ Ideal.span {r (e i)} := hs i ▸ Ideal.subset_span rfl
      exact Ideal.span_mono (Set.singleton_subset_iff.2 (Set.mem_range_self (e i))) this
    · simp only [r', dif_neg h]
      exact Ideal.subset_span ⟨j, rfl⟩
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    by_cases h : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := h
      have : r (e i) ∈ Ideal.span {s i} := (hs i).symm ▸ Ideal.subset_span rfl
      exact Ideal.span_mono (Set.singleton_subset_iff.2 (show s i ∈ Set.range r' from ⟨e i, hr' i⟩)) this
    · have : r j = r' j := by simp only [r', dif_neg h]
      rw [this]
      exact Ideal.subset_span ⟨j, rfl⟩

theorem exists_affine_germ_eq : ∀ (Y : Scheme.{0}) (y : Y) (n : ℕ) (r : Fin n → Y.presheaf.stalk y),
    ∃ (V : Y.affineOpens) (hy : y ∈ V.1) (F : Fin n → Γ(Y, V.1)), ∀ j, Y.presheaf.germ V.1 y hy (F j) = r j := by
  intro Y y n r
  classical
  choose U hU s hs using fun j => TopCat.Presheaf.germ_exist Y.presheaf (r j)
  have hmem : ∀ t : Finset (Fin n), y ∈ t.inf U := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      rw [Finset.inf_insert]
      exact ⟨hU a, ih⟩
  obtain ⟨V, hV, hyV, hVO⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (hmem Finset.univ)
  have hle : ∀ j, V ≤ U j := fun j => le_trans hVO (Finset.inf_le (Finset.mem_univ j))
  refine ⟨⟨V, hV⟩, hyV, fun j => resG Y (hle j) (s j), fun j => ?_⟩
  rw [← hs j]
  exact Y.presheaf.germ_res_apply (homOfLE (hle j)) y hyV (s j)

theorem fderiv_ev_eq_of_germ_eq : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (n : ℕ)
    (c : AlgChart p σ n) (x₀ : CxPts p σ), x₀ ∈ c.e.source → ∀ (U V : Y.Opens)
    (hU : x₀.1 (IsLocalRing.closedPoint ℂ) ∈ U) (hV : x₀.1 (IsLocalRing.closedPoint ℂ) ∈ V) (f : Γ(Y, U)) (g : Γ(Y, V)),
    Y.presheaf.germ U _ hU f = Y.presheaf.germ V _ hV g →
    fderiv ℂ (ev p σ U f ∘ c.e.symm) (c.e x₀) = fderiv ℂ (ev p σ V g ∘ c.e.symm) (c.e x₀) := by
  intro k _ Y p σ n c x₀ hx U V hU hV f g h
  obtain ⟨W, hW, iU, iV, he⟩ := TopCat.Presheaf.germ_eq Y.presheaf _ hU hV f g h
  have hWU : W ≤ U := leOfHom iU
  have hWV : W ≤ V := leOfHom iV
  have hx' : x₀ ∈ ptsIn p σ W := mem_ptsIn.2 hW
  have hres : resG Y hWU f = resG Y hWV g := he
  have e1 : ∀ z ∈ ptsIn p σ W, ev p σ U f z = ev p σ V g z := by
    intro z hz
    rw [← ev_res hWU hz, ← ev_res hWV hz, hres]
  have e2 : ev p σ U f ∘ c.e.symm =ᶠ[nhds (c.e x₀)] ev p σ V g ∘ c.e.symm :=
    Filter.eventually_of_mem ((GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn W)).mem_nhds
      (GlobalTheory.ChartGlue.mem_over c.e hx hx')) fun v hv => e1 _ hv.2
  exact e2.fderiv_eq

theorem linearIndependent_fderiv_eqns : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ),
    SmoothOfRelativeDimension n p → ∀ (c : AlgChart p σ n) (x₀ : CxPts p σ), x₀ ∈ c.e.source →
    ∀ (m : ℕ) (C : Fin m → Closeds Y), LSncAt Y C (x₀.1 (IsLocalRing.closedPoint ℂ)) →
    ∀ (U : Fin m → Y.affineOpens) (f : ∀ i, Γ(Y, (U i).1)), (∀ i, x₀ ∈ ptsIn p σ (U i).1) →
    (∀ i, (Scheme.IdealSheafData.vanishingIdeal (C i)).ideal (U i) = Ideal.span {f i}) →
    LinearIndependent ℂ (fun i : {i : Fin m // x₀.1 (IsLocalRing.closedPoint ℂ) ∈ C i} =>
      fderiv ℂ (ev p σ (U i.1).1 (f i.1) ∘ c.e.symm) (c.e x₀)) := by
  intro k _ _ Y p n σ hsm c x₀ hx m C hL U f hU hf
  haveI := hsm
  obtain ⟨hreg, N, r, e, hR, hr⟩ := hL
  have hyU : ∀ i, x₀.1 (IsLocalRing.closedPoint ℂ) ∈ (U i).1 := fun i => mem_ptsIn.1 (hU i)
  let s : {i : Fin m // x₀.1 (IsLocalRing.closedPoint ℂ) ∈ C i} → Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ)) :=
    fun i => Y.presheaf.germ (U i.1).1 _ (hyU i.1) (f i.1)
  have hs : ∀ i, Ideal.span {s i} = Ideal.span {r (e i)} := fun i => by
    rw [← hr i, ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ _ _ (U i.1) (hyU i.1), hf, Ideal.map_span,
      Set.image_singleton]
  obtain ⟨r', hR', hr'⟩ := exists_rsp_replace _ N r hR _ e s hs
  obtain ⟨V, hyV, F, hF⟩ := exists_affine_germ_eq Y _ N r'
  have hR'' : Rsp (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) N
      (fun j => Y.presheaf.germ V.1 _ hyV (F j)) := by
    have : (fun j => Y.presheaf.germ V.1 _ hyV (F j)) = r' := funext hF
    rw [this]; exact hR'
  have hli := SncChart.linearIndependent_fderiv_params k Y p n σ c x₀ hx V hyV N F hR''
  have h2 := hli.comp e e.injective
  convert h2 using 1
  funext i
  simp only [Function.comp_apply]
  exact fderiv_ev_eq_of_germ_eq k Y p σ n c x₀ hx _ _ (hyU i.1) hyV (f i.1) (F (e i)) ((hr' i).symm.trans (hF (e i)).symm)

theorem isCompatChart_of_holAlong : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (n : ℕ)
    (B : FinHolAtlas n (CxPts p σ)), IsAlgAtlas B → ∀ (e : OpenPartialHomeomorph (CxPts p σ) (Fin n → ℂ)),
    (∀ j, HolAlong e.source fun x => e x j) → IsHolTo e.target (fun z => (e.symm z).1) → IsCompatChart B e := by
  intro k _ Y p σ n B hB e hhol hsymm j
  obtain ⟨c, hcj⟩ := hB j
  rw [hcj]
  constructor
  · refine (c.analyticOnNhd_finChart_iff e.open_source e).2 ?_
    refine differentiableOn_pi.2 fun i => ?_
    have hO := GlobalTheory.ChartGlue.isOpen_over c.e e.open_source
    exact hhol i _ _ c.e.symm hO (GlobalTheory.ShFam.Hor.Sec.isHolTo_symm c hO Set.inter_subset_left) (fun b hb => hb.2)
  · have hO : IsOpen (e.target ∩ e.symm ⁻¹' c.finChart.source) := e.isOpen_inter_preimage_symm c.finChart.open_source
    refine (SCV.analyticOnNhd_iff_differentiableOn hO).2 ?_
    intro b hb
    have h1 := GlobalTheory.TrueCx.TorHolo.differentiableAt_chart e.open_target hsymm c hb.1 hb.2
    exact ((EuclideanSpace.equiv (Fin n) ℂ).differentiable.differentiableAt.comp b h1).differentiableWithinAt

theorem isSNC_divSec : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (σ : F →+* ℂ) (m : ℕ) (C : Fin m → Closeds Y.X) (n : Fin m → Pts Y σ → ℝ) (hn : ∀ i, IsDivNorm (Y.an σ) (C i) (n i)) (B : FinHolAtlas Y.dim (Pts Y σ)), IsAlgAtlas B → (∀ y : Y.X, LSncAt Y.X C y) → IsSNC B (GlobalTheory.DivSec.divPot hn) (GlobalTheory.DivSec.divSec hn) (fun _ : Fin m => 1) (fun i => {z | LiesIn z (C i)}) := by
  intro F _ _ Y σ m C n hn B hB hsnc
  classical
  intro x
  let S : Finset (Fin m) := Finset.univ.filter fun i => LiesIn x (C i)
  have hS : ∀ i, i ∈ S ↔ LiesIn x (C i) := fun i => by simp [S]
  obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := Y.dim) (p := Y.str) (σ := σ) x
  let W : Y.X.Opens := Finset.univ.inf fun i => (GlobalTheory.DivSec.eqV hn i x).1
  have hWle : ∀ i, W ≤ (GlobalTheory.DivSec.eqV hn i x).1 := fun i => Finset.inf_le (Finset.mem_univ i)
  have hmemI : ∀ (z : Pts Y σ) (s : Finset (Fin m)), z ∈ ptsIn Y.str σ (s.inf fun i => (GlobalTheory.DivSec.eqV hn i x).1) ↔
      ∀ i ∈ s, z ∈ ptsIn Y.str σ (GlobalTheory.DivSec.eqV hn i x).1 := by
    intro z s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.inf_insert, mem_ptsIn_inf, ih, Finset.forall_mem_insert]
  have hWU : ptsIn Y.str σ W = (GlobalTheory.DivSec.divPot hn).U x := by
    ext z
    rw [hmemI z Finset.univ]
    simp only [GlobalTheory.DivSec.divPot, Set.mem_iInter, Finset.mem_univ, true_implies]
  have hxW : x ∈ ptsIn Y.str σ W := hWU ▸ (GlobalTheory.DivSec.divPot hn).mem_U x
  let ix : Fin S.card → Fin m := fun j => (S.equivFin.symm j).1
  have hix : Function.Injective ix := fun i j h => S.equivFin.symm.injective (Subtype.ext h)
  have hixS : ∀ j, LiesIn x (C (ix j)) := fun j => (hS _).1 (S.equivFin.symm j).2
  let g : Fin S.card → Γ(Y.X, W) := fun j => resG Y.X (hWle (ix j)) (GlobalTheory.DivSec.eqT hn (ix j) x)
  have hgev : ∀ i z, z ∈ ptsIn Y.str σ W →
      ev Y.str σ W (resG Y.X (hWle i) (GlobalTheory.DivSec.eqT hn i x)) z = ev Y.str σ _ (GlobalTheory.DivSec.eqT hn i x) z :=
    fun i z hz => ev_res _ hz _
  have hzero : ∀ i z, z ∈ ptsIn Y.str σ W →
      (ev Y.str σ _ (GlobalTheory.DivSec.eqT hn i x) z = 0 ↔ LiesIn z (C i)) := fun i z hz =>
    ev_eq_zero_iff (GlobalTheory.DivSec.eq_spec hn i x).2.1 (ptsIn_mono (hWle i) hz)
  have h0 : ∀ j, ev Y.str σ W (g j) x = 0 := fun j => by
    simp only [g]; rw [hgev _ _ hxW]; exact (hzero _ _ hxW).2 (hixS j)
  have hliA := linearIndependent_fderiv_eqns F Y.X Y.str Y.dim σ inferInstance c x hc m C (hsnc _) (fun i => GlobalTheory.DivSec.eqV hn i x)
    (fun i => GlobalTheory.DivSec.eqT hn i x) (fun i => (GlobalTheory.DivSec.eq_spec hn i x).1) (fun i => (GlobalTheory.DivSec.eq_spec hn i x).2.1)
  have hli : LinearIndependent ℂ (fun j => fderiv ℂ (ev Y.str σ W (g j) ∘ c.e.symm) (c.e x)) := by
    have h2 := hliA.comp (fun j => (⟨ix j, hixS j⟩ : {i : Fin m // x.1 (IsLocalRing.closedPoint ℂ) ∈ C i}))
      (by intro a b h; exact hix (by simpa using congrArg Subtype.val h))
    convert h2 using 1
    funext j
    have e : ev Y.str σ W (g j) ∘ c.e.symm =ᶠ[nhds (c.e x)]
        ev Y.str σ _ (GlobalTheory.DivSec.eqT hn (ix j) x) ∘ c.e.symm :=
      Filter.eventually_of_mem ((GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn W)).mem_nhds
        (GlobalTheory.ChartGlue.mem_over c.e hc hxW)) fun v hv => hgev _ _ hv.2
    simp only [Function.comp_apply]
    exact e.fderiv_eq
  have hcard : S.card ≤ Y.dim := by
    have := hli.fintype_card_le_finrank
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := ReciprocityTheory.L2DbarEstimates.V Y.dim) (F' := ℂ)).finrank_eq,
      Module.finrank_linearMap, Module.finrank_self, _root_.mul_one] at this
    simpa [ReciprocityTheory.L2DbarEstimates.V] using this
  obtain ⟨e, hx0, hsub, -, hhol, hsymm, hev⟩ :=
    SncChart.exists_chart_of_fderiv F Y.X Y.str Y.dim σ c x hc W hxW S.card g h0 hli
  let O : Set (Pts Y σ) := (GlobalTheory.DivSec.divPot hn).U x ∩ ⋂ k, {z | LiesIn x (C k) ∨ ¬ LiesIn z (C k)}
  have hO : IsOpen O := by
    refine ((GlobalTheory.DivSec.divPot hn).isOpen_U x).inter (isOpen_iInter_of_finite fun k => ?_)
    by_cases h : LiesIn x (C k)
    · simp [h]
    · simpa [h] using isOpen_not_liesIn (p := Y.str) (σ := σ) (C k)
  let ψ := e.restrOpen O hO
  have hψs : ψ.source = e.source ∩ O := e.restrOpen_source O hO
  have hψa : ∀ z, ψ z = e z := fun z => rfl
  have hψW : ∀ z ∈ ψ.source, z ∈ ptsIn Y.str σ W := fun z hz => hsub (hψs ▸ hz).1
  have hψO : ∀ z ∈ ψ.source, z ∈ O := fun z hz => (hψs ▸ hz).2
  have hcompat : IsCompatChart B ψ := by
    refine isCompatChart_of_holAlong F Y.X Y.str σ Y.dim B hB ψ (fun j => ?_) ?_
    · intro V _ _ _ B' y hB' hy hm
      exact hhol j V B' y hB' hy (fun b hb => (hψs ▸ hm hb).1)
    · exact GlobalTheory.LocLift.isHolTo_mono hsymm ψ.open_target fun z hz => hz.1
  let pos : ∀ k, LiesIn x (C k) → Fin Y.dim := fun k hk =>
    ⟨S.equivFin ⟨k, (hS k).2 hk⟩, lt_of_lt_of_le (Fin.isLt _) hcard⟩
  let τ : Fin m → Option (Fin Y.dim) := fun k => if hk : LiesIn x (C k) then some (pos k hk) else none
  have hτ : ∀ k (hk : LiesIn x (C k)) z, z ∈ ψ.source → ψ z (pos k hk) = ev Y.str σ _ (GlobalTheory.DivSec.eqT hn k x) z := by
    intro k hk z hz
    rw [hψa, hev z (hψs ▸ hz).1 (pos k hk) (S.equivFin ⟨k, (hS k).2 hk⟩).isLt]
    have hj : (⟨(pos k hk : ℕ), (S.equivFin ⟨k, (hS k).2 hk⟩).isLt⟩ : Fin S.card) = S.equivFin ⟨k, (hS k).2 hk⟩ := rfl
    have hk' : ix (S.equivFin ⟨k, (hS k).2 hk⟩) = k := by simp [ix]
    rw [hj]
    simp only [g]
    rw [hgev _ _ (hψW z hz)]
    rw [hk']
  refine ⟨ψ, hcompat, hψs ▸ ⟨hx0, (GlobalTheory.DivSec.divPot hn).mem_U x, Set.mem_iInter.2 fun k => ?_⟩,
    fun z hz => (hψO z hz).1, τ, ?_, ?_, fun z => ∏ k ∈ Finset.univ.filter (fun k => ¬ LiesIn x (C k)),
      ev Y.str σ _ (GlobalTheory.DivSec.eqT hn k x) z, ?_, ?_, ?_⟩
  · by_cases h : LiesIn x (C k)
    · exact Or.inl h
    · exact Or.inr h
  · intro k k' i h1 h2
    simp only [τ] at h1 h2
    split_ifs at h1 h2 with hk hk'
    have := (Option.some.inj h1).trans (Option.some.inj h2).symm
    have h3 : S.equivFin ⟨k, (hS k).2 hk⟩ = S.equivFin ⟨k', (hS k').2 hk'⟩ := Fin.ext (by simpa [pos] using congrArg Fin.val this)
    exact congrArg Subtype.val (S.equivFin.injective h3)
  · intro k
    ext z
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, τ]
    constructor
    · rintro ⟨hzk, hz⟩
      refine ⟨hz, ?_⟩
      by_cases hk : LiesIn x (C k)
      · refine ⟨pos k hk, by simp [hk], ?_⟩
        rw [hτ k hk z hz]
        exact (hzero k z (hψW z hz)).2 hzk
      · exact absurd hzk ((Set.mem_iInter.1 (hψO z hz).2 k).resolve_left hk)
    · rintro ⟨hz, i, hi, h0⟩
      refine ⟨?_, hz⟩
      by_cases hk : LiesIn x (C k)
      · simp only [hk, dite_true, Option.some.injEq] at hi
        subst hi
        rw [hτ k hk z hz] at h0
        exact (hzero k z (hψW z hz)).1 h0
      · simp [hk] at hi
  · refine (hB.holoOn_iff (Y.an σ) ψ.open_source).2 fun j => ?_
    have h : ∀ k, DifferentiableOn ℂ (fun v => ev Y.str σ _ (GlobalTheory.DivSec.eqT hn k x) (((Y.an σ).chart j).e.symm v))
        (((Y.an σ).chart j).e.target ∩ ((Y.an σ).chart j).e.symm ⁻¹' ψ.source) := fun k =>
      ((Y.an σ).holoOn_ev _ (GlobalTheory.DivSec.eqT hn k x) j).mono fun v hv => ⟨hv.1, ptsIn_mono (hWle k) (hψW _ hv.2)⟩
    have key : ∀ s : Finset (Fin m), DifferentiableOn ℂ
        (fun v => ∏ k ∈ s, ev Y.str σ _ (GlobalTheory.DivSec.eqT hn k x) (((Y.an σ).chart j).e.symm v))
        (((Y.an σ).chart j).e.target ∩ ((Y.an σ).chart j).e.symm ⁻¹' ψ.source) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using differentiableOn_const (1 : ℂ)
      | insert a s ha ih =>
        simp only [Finset.prod_insert ha]
        exact (h a).mul ih
    exact (key _).congr fun v _ => rfl
  · intro z hz
    refine Finset.prod_ne_zero_iff.2 fun k hk => ?_
    have hk' : ¬ LiesIn x (C k) := (Finset.mem_filter.1 hk).2
    intro h
    exact (Set.mem_iInter.1 (hψO z hz).2 k).resolve_left hk' ((hzero k z (hψW z hz)).1 h)
  · intro z hz
    simp only [GlobalTheory.DivSec.divSec]
    rw [← Finset.prod_filter_not_mul_prod_filter Finset.univ (fun k => LiesIn x (C k))]
    congr 1
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun k _ => ?_
    by_cases hk : LiesIn x (C k)
    · simp only [hk, if_true, τ, dite_true, pow_one]
      exact (hτ k hk z hz).symm
    · simp [hk, τ]

end GlobalTheory.DivSec
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SncForm

theorem ideal_vanishingIdeal_closure {X : Scheme.{0}} (U : X.affineOpens) {η : X} (hη : η ∈ U.1) :
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})).ideal U =
      (U.2.primeIdealOf ⟨η, hη⟩).asIdeal := by
  have hU : IsAffineOpen U.1 := U.2
  have emb := hU.fromSpec.isOpenEmbedding
  have h1 : hU.fromSpec (hU.primeIdealOf ⟨η, hη⟩) = η := hU.fromSpec_primeIdealOf ⟨η, hη⟩
  have h2 : hU.fromSpec ⁻¹' ({η} : Set X) = {hU.primeIdealOf ⟨η, hη⟩} := by
    ext Q
    exact ⟨fun h => emb.injective (h.trans h1.symm), fun h => (congrArg _ h).trans h1⟩
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
  change PrimeSpectrum.vanishingIdeal (hU.fromSpec ⁻¹' closure ({η} : Set X)) = _
  have h3 := (emb.isOpenMap.preimage_closure_eq_closure_preimage emb.continuous {η}).trans
    (congrArg closure h2)
  exact (congrArg PrimeSpectrum.vanishingIdeal h3).trans
    ((PrimeSpectrum.vanishingIdeal_closure _).trans (PrimeSpectrum.vanishingIdeal_singleton _))

theorem exists_isLocalization_stalk {X : Scheme.{0}} (U : X.affineOpens) {y η : X} (hy : y ∈ U.1)
    (hη : η ∈ U.1) (hηy : η ⤳ y) (p : Ideal (X.presheaf.stalk y)) [p.IsPrime]
    (hp : FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})) y = p) :
    ∃ _ : Algebra (X.presheaf.stalk y) (X.presheaf.stalk η),
      IsLocalization.AtPrime (X.presheaf.stalk η) p ∧ ∀ a : Γ(X, U.1),
        X.presheaf.germ U.1 η hη a =
          algebraMap (X.presheaf.stalk y) (X.presheaf.stalk η) (X.presheaf.germ U.1 y hy a) := by
  have hU : IsAffineOpen U.1 := U.2
  let yU : U.1 := ⟨y, hy⟩
  let algY : Algebra Γ(X, U.1) (X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf yU
  have hlocY : IsLocalization.AtPrime (X.presheaf.stalk y) (hU.primeIdealOf yU).asIdeal :=
    hU.isLocalization_stalk yU
  set Py := hU.primeIdealOf yU with hPy
  let Pη := hU.primeIdealOf ⟨η, hη⟩
  have hfromη : hU.fromSpec Pη = η := hU.fromSpec_primeIdealOf ⟨η, hη⟩
  have hfromy : hU.fromSpec Py = y := hU.fromSpec_primeIdealOf yU
  have emb := hU.fromSpec.isOpenEmbedding
  have hspec : ∀ P Q : PrimeSpectrum Γ(X, U.1), hU.fromSpec P ⤳ hU.fromSpec Q ↔ P ≤ Q := by
    intro P Q
    rw [PrimeSpectrum.le_iff_specializes]
    exact emb.isInducing.specializes_iff
  have hle : Pη ≤ Py := (hspec _ _).mp (by rw [hfromη, hfromy]; exact hηy)
  have hdisj : Disjoint (Py.asIdeal.primeCompl : Set Γ(X, U.1)) Pη.asIdeal :=
    Set.disjoint_left.mpr fun x hx hx' => hx ((show Pη.asIdeal ≤ Py.asIdeal from hle) hx')
  rw [WMult.stalkId_eq_map_germ _ y U hy, ideal_vanishingIdeal_closure U hη] at hp
  have hPeq : Pη.asIdeal = p.comap (algebraMap Γ(X, U.1) (X.presheaf.stalk y)) := by
    rw [← hp]
    exact (IsLocalization.under_map_of_isPrime_disjoint Py.asIdeal.primeCompl
      (X.presheaf.stalk y) Pη.isPrime hdisj).symm
  let T := Localization.AtPrime p
  have hT : IsLocalization.AtPrime T (p.comap (algebraMap Γ(X, U.1) (X.presheaf.stalk y))) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (M := Py.asIdeal.primeCompl) (S := X.presheaf.stalk y) (T := T) p
  have hT' : IsLocalization Pη.asIdeal.primeCompl T := by
    have hsm : Pη.asIdeal.primeCompl =
        (Ideal.comap (algebraMap Γ(X, U.1) (X.presheaf.stalk y)) p).primeCompl := by
      ext x; rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hPeq]
    rw [hsm]; exact hT
  let ηU : U.1 := ⟨η, hη⟩
  let algη : Algebra Γ(X, U.1) (X.presheaf.stalk η) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ηU
  have hlocη : IsLocalization.AtPrime (X.presheaf.stalk η) Pη.asIdeal :=
    hU.isLocalization_stalk ηU
  let φ : X.presheaf.stalk η ≃ₐ[Γ(X, U.1)] T := IsLocalization.algEquiv Pη.asIdeal.primeCompl _ _
  let algYη : Algebra (X.presheaf.stalk y) (X.presheaf.stalk η) :=
    (φ.symm.toRingEquiv.toRingHom.comp (algebraMap (X.presheaf.stalk y) T)).toAlgebra
  refine ⟨algYη, (IsLocalization.isLocalization_iff_of_ringEquiv (M := p.primeCompl)
      (S := T) φ.symm.toRingEquiv).mp inferInstance, fun a => ?_⟩
  have h1 := (φ.symm.commutes a).symm
  rw [IsScalarTower.algebraMap_apply Γ(X, U.1) (X.presheaf.stalk y) T] at h1
  exact h1

theorem germ_eq_unit_mul_monomial : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (B : LB X) (hB : B.IsLB) (s : B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (r : ℕ) (z : Fin r → X), Function.Injective z → (∀ a, Order.coheight (z a) = 1) → ((nonzeroLocus s : Set X)ᶜ = ⋃ a, closure {z a}) → ∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x → ∀ (i : B.ι) (hi : x ∈ B.U i), ∃ (n : ℕ) (g : Fin n → X.presheaf.stalk x) (e : {a : Fin r // x ∈ (Closeds.closure {z a})} ↪ Fin n) (u : (X.presheaf.stalk x)ˣ) (_ : Fintype {a : Fin r // x ∈ (Closeds.closure {z a})}), FinalTheorems.Rsp (X.presheaf.stalk x) n g ∧ (∀ a, FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z a.1})) x = Ideal.span {g (e a)}) ∧ X.presheaf.germ _ x hi (s.f i) = u * ∏ a, g (e a) ^ ((divOfSec hB s hs).mult (z a.1)).toNat := by
  classical
  intro X _ _ B hB s hs r z _ hz hZ x hx i hi
  obtain ⟨hreg, n, g, e, hg, hI⟩ := hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVi⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hi (B.U i).isOpen
  let U : X.affineOpens := ⟨V, hV⟩
  have hVi' : V ≤ B.U i := hVi
  let t : Γ(X, V) := X.presheaf.map (homOfLE hVi').op (s.f i)
  have ht : ∀ (w : X) (hw : w ∈ V), X.presheaf.germ V w hw t =
      X.presheaf.germ _ w (hVi' hw) (s.f i) := fun w hw =>
    X.presheaf.germ_res_apply (homOfLE hVi') w hw _
  set γ := X.presheaf.germ _ x hi (s.f i) with hγ
  have hγ0 : γ ≠ 0 := fun h0 => fnOf_sec_ne_zero hs (gen_mem hi)
    ((algebraMap_germ hi (s.f i)).symm.trans ((congrArg _ h0).trans (map_zero _)))
  let J : Finset (Fin n) := Finset.univ.map e
  have hrad : (∏ j ∈ J, g j) ∈ (Ideal.span {γ}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro Q ⟨hQγ, hQ⟩
    let P : PrimeSpectrum Γ(X, V) := ⟨Q.comap (X.presheaf.germ V x hxV).hom, inferInstance⟩
    have htP : t ∈ P.asIdeal := by
      change X.presheaf.germ V x hxV t ∈ Q
      rw [ht]
      exact hQγ (Ideal.mem_span_singleton_self _)
    have hmem : hV.fromSpec P ∈ V := by
      have : hV.fromSpec P ∈ Set.range hV.fromSpec := ⟨P, rfl⟩
      rwa [hV.range_fromSpec] at this
    have hnz : hV.fromSpec P ∉ nonzeroLocus s := by
      rw [mem_nonzeroLocus_iff s i (hVi' hmem)]
      intro h
      have h' : hV.fromSpec P ∈ X.basicOpen t := by
        rw [Scheme.mem_basicOpen _ _ _ hmem, ht]
        exact (Scheme.mem_basicOpen _ _ _ _).1 h
      have h'' : P ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen t := h'
      rw [hV.fromSpec_preimage_basicOpen] at h''
      exact h'' htP
    have hc : hV.fromSpec P ∈ ((nonzeroLocus s : Set X)ᶜ) := hnz
    rw [hZ] at hc
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hc
    have hPx : hV.fromSpec P ⤳ x := by
      have h1 : hV.fromSpec (hV.primeIdealOf ⟨x, hxV⟩) = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
      have h2 : P ≤ hV.primeIdealOf ⟨x, hxV⟩ := by
        rw [hV.primeIdealOf_eq_map_closedPoint]
        exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ.ne_top)
      have h3 := ((PrimeSpectrum.le_iff_specializes _ _).1 h2).map hV.fromSpec.continuous
      rwa [h1] at h3
    have hxa : x ∈ Closeds.closure {z a} := hPx.mem_closed isClosed_closure ha
    have hsup : hV.fromSpec P ∈
        ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z a})).support : Set X) := by
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact ha
    rw [WMult.mem_support_fromSpec_iff _ U hV] at hsup
    have h3 : Ideal.span {g (e ⟨a, hxa⟩)} ≤ Q := by
      rw [← hI ⟨a, hxa⟩, WMult.stalkId_eq_map_germ _ x U hxV]
      exact Ideal.map_le_iff_le_comap.mpr hsup
    exact Q.mem_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_map_of_mem e (Finset.mem_univ _)))
      (h3 (Ideal.mem_span_singleton_self _))
  obtain ⟨u, m, -, hγu⟩ := eq_unit_mul_monomial g hg.1 hg.2 J hγ0 hrad
  refine ⟨n, g, e, u, inferInstance, hg, hI, ?_⟩
  have hord : ∀ a, ((divOfSec hB s hs).mult (z a.1)).toNat = m (e a) := by
    intro a
    have hsp : z a.1 ⤳ x := specializes_iff_mem_closure.2 a.2
    have hzV : z a.1 ∈ V := hsp.mem_open V.isOpen hxV
    have hpr : Prime (g (e a)) := prime_of_regular_params g hg.1 hg.2 _
    have hP : (Ideal.span {g (e a)}).IsPrime := (Ideal.span_singleton_prime hpr.ne_zero).mpr hpr
    obtain ⟨alg, hloc, hgerm⟩ := exists_isLocalization_stalk U hxV hzV hsp _ (hI a)
    have h := WMult.ord_isLocalization_eq_exponent g hg.1 hg.2 J u m (e a)
      (Finset.mem_map_of_mem e (Finset.mem_univ _)) (X.presheaf.stalk (z a.1))
    rw [← hγu, hγ, ← ht x hxV, ← hgerm t, ht] at h
    rw [mult_divOfSec (hz _) (hVi' hzV), Int.toNat_natCast]
    exact (congrArg ENat.toNat h).trans (ENat.toNat_natCast _)
  rw [hγu, Finset.prod_map]
  exact congrArg _ (Finset.prod_congr rfl fun a _ => by rw [hord])

end GlobalTheory.SncForm
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

noncomputable section

namespace GlobalTheory.SecSnc

open GlobalTheory.ShFam (LiesIn ev_eq_zero_iff isOpen_not_liesIn)

section Local

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem eventually_ev_eq (x : CxPts p σ) {U V : X.Opens} (hU : x.1 (IsLocalRing.closedPoint ℂ) ∈ U)
    (hV : x.1 (IsLocalRing.closedPoint ℂ) ∈ V) (f : Γ(X, U)) (g : Γ(X, V))
    (h : X.presheaf.germ U _ hU f = X.presheaf.germ V _ hV g) :
    ∀ᶠ y in 𝓝 x, ev p σ U f y = ev p σ V g y := by
  obtain ⟨W, hW, iU, iV, he⟩ := TopCat.Presheaf.germ_eq X.presheaf _ hU hV f g h
  have hWU : W ≤ U := leOfHom iU
  have hWV : W ≤ V := leOfHom iV
  have hres : resG X hWU f = resG X hWV g := he
  refine Filter.eventually_of_mem ((isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)) fun z hz => ?_
  rw [← ev_res hWU hz, ← ev_res hWV hz, hres]

theorem eventually_ev_ne_zero (x : CxPts p σ) {V : X.Opens} (hV : x.1 (IsLocalRing.closedPoint ℂ) ∈ V)
    (g : Γ(X, V)) (h : IsUnit (X.presheaf.germ V _ hV g)) : ∀ᶠ y in 𝓝 x, ev p σ V g y ≠ 0 := by
  have hx : x ∈ ptsIn p σ (X.basicOpen g) := mem_ptsIn.2 ((X.mem_basicOpen g _ hV).2 h)
  refine Filter.eventually_of_mem ((isOpen_ptsIn _).mem_nhds hx) fun z hz => ?_
  exact (mem_ptsIn_basicOpen (ptsIn_mono (X.basicOpen_le g) hz) g).1 hz

theorem eventually_ev_eq_zero_iff [IsLocallyNoetherian X] (x : CxPts p σ) (V : X.affineOpens)
    (hV : x.1 (IsLocalRing.closedPoint ℂ) ∈ V.1) (g : Γ(X, V.1)) (C : Closeds X)
    (h : FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal C) (x.1 (IsLocalRing.closedPoint ℂ)) =
      Ideal.span {X.presheaf.germ V.1 _ hV g}) :
    ∀ᶠ y in 𝓝 x, (ev p σ V.1 g y = 0 ↔ LiesIn y C) := by
  rw [WMult.stalkId_eq_map_germ _ _ V hV] at h
  obtain ⟨s, hs, H⟩ := GlobalTheory.IdealSpread.ideal_eq_span_of_germ X _ V _ hV g
    (IsLocallyNoetherian.component_noetherian V) h
  refine Filter.eventually_of_mem ((isOpen_ptsIn _).mem_nhds (mem_ptsIn.2 hs)) fun z hz => ?_
  rw [← ev_res (X.basicOpen_le s) hz]
  exact ev_eq_zero_iff (V := X.affineBasicOpen s) (H s le_rfl) hz

theorem mem_range_ptMap_closι (z : X) (y : CxPts p σ) :
    y ∈ Set.range (ptMap (closι z) rfl σ) ↔ LiesIn y (Closeds.closure {z}) := by
  have hr : Set.range (closι z) = (Closeds.closure {z} : Closeds X) :=
    (Scheme.IdealSheafData.range_subschemeι _).trans (Scheme.IdealSheafData.coe_support_vanishingIdeal _)
  constructor
  · rintro ⟨w, rfl⟩
    have : closι z (w.1 (IsLocalRing.closedPoint ℂ)) ∈ Set.range (closι z) := ⟨_, rfl⟩
    rw [hr] at this
    exact this
  · intro hy
    have : IsReduced (Sp ℂ) := inferInstanceAs (IsReduced (Spec _))
    have hle : Set.range y.1 ⊆ Set.range (closι z) := by
      rintro _ ⟨a, rfl⟩
      have ha : a = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
      rw [hr, ha]
      exact hy
    have hk : (closι z).ker ≤ y.1.ker := ker_le_ker_of_range_subset_of_isReduced (closι z) y.1 hle
    have hl := IsClosedImmersion.lift_fac (closι z) y.1 hk
    exact ⟨⟨IsClosedImmersion.lift (closι z) y.1 hk, by rw [← Category.assoc, hl, y.2]⟩, Subtype.ext hl⟩

end Local

theorem exists_compatChart {F : Type} [Field F] {X : Scheme.{0}} {p : X ⟶ Sp F} {σ : F →+* ℂ} {D : ℕ}
    [SmoothOfRelativeDimension D p] {A : FinHolAtlas D (CxPts p σ)} (hA : IsAlgAtlas A) (x : CxPts p σ)
    {N : Set (CxPts p σ)} (hN : N ∈ 𝓝 x) (V : X.affineOpens) (hV : x.1 (IsLocalRing.closedPoint ℂ) ∈ V.1) {n : ℕ}
    (G : Fin n → Γ(X, V.1))
    (hR : FinalTheorems.Rsp (X.presheaf.stalk (x.1 (IsLocalRing.closedPoint ℂ))) n (fun j => X.presheaf.germ V.1 _ hV (G j))) :
    ∃ (hn : n ≤ D) (ψ : OpenPartialHomeomorph (CxPts p σ) (Fin D → ℂ)), IsCompatChart A ψ ∧ x ∈ ψ.source ∧
      ψ.source ⊆ N ∧ ψ.source ⊆ ptsIn p σ V.1 ∧
      ∀ y ∈ ψ.source, ∀ j, ψ y (Fin.castLE hn j) = ev p σ V.1 (G j) y := by
  haveI : CharZero F := σ.charZero
  obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := D) (p := p) (σ := σ) x
  have hli := SncChart.linearIndependent_fderiv_params F X p D σ c x hc V hV n G hR
  have hxV : x ∈ ptsIn p σ V.1 := mem_ptsIn.2 hV
  have h0 : ∀ i, ev p σ V.1 (G i) x = 0 := by
    intro i
    by_contra hne
    have hb := mem_ptsIn.1 ((mem_ptsIn_basicOpen hxV (G i)).2 hne)
    rw [Scheme.mem_basicOpen _ _ _ hV] at hb
    have hmem : X.presheaf.germ V.1 _ hV (G i) ∈ IsLocalRing.maximalIdeal _ := by
      rw [← hR.1]; exact Ideal.subset_span ⟨i, rfl⟩
    exact hmem hb
  have hn : n ≤ D := by
    have := hli.fintype_card_le_finrank
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := ReciprocityTheory.L2DbarEstimates.V D) (F' := ℂ)).finrank_eq,
      Module.finrank_linearMap, Module.finrank_self, _root_.mul_one] at this
    simpa [ReciprocityTheory.L2DbarEstimates.V] using this
  obtain ⟨e, hx0, hsub, -, hhol, hsymm, hev⟩ :=
    SncChart.exists_chart_of_fderiv F X p D σ c x hc V.1 hxV n G h0 hli
  obtain ⟨O, hON, hO, hxO⟩ := mem_nhds_iff.1 hN
  let ψ := e.restrOpen O hO
  have hψs : ψ.source = e.source ∩ O := e.restrOpen_source O hO
  refine ⟨hn, ψ, ?_, hψs ▸ ⟨hx0, hxO⟩, fun y hy => hON (hψs ▸ hy).2, fun y hy => hsub (hψs ▸ hy).1,
    fun y hy j => hev y (hψs ▸ hy).1 (Fin.castLE hn j) j.2⟩
  refine GlobalTheory.DivSec.isCompatChart_of_holAlong F X p σ D A hA ψ (fun j => ?_) ?_
  · intro V _ _ _ B' y hB' hy hm
    exact hhol j V B' y hB' hy (fun b hb => (hψs ▸ hm hb).1)
  · exact GlobalTheory.LocLift.isHolTo_mono hsymm ψ.open_target fun z hz => hz.1

theorem isSNC_locSec : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → SmoothOfRelativeDimension D p → ∀ (A : FinHolAtlas D (CxPts p σ)), IsAlgAtlas A → ∀ (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (r : ℕ) (z : Fin r → X), Function.Injective z → (∀ a, Order.coheight (z a) = 1) → ((nonzeroLocus s : Set X)ᶜ = ⋃ a, closure {z a}) → (∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x) → IsSNC A M.φ.locPot (M.φ.locSec (secVal p σ s)) (fun a => ((divOfSec M.φ.isLB s hs).mult (z a)).toNat) (fun a => Set.range (ptMap (closι (z a)) rfl σ)) := by
  intro F _ X _ _ p σ D _ hsm A hA M s hs r z hz hco hzero hsnc x
  classical
  haveI := hsm
  have hxi := mem_pick (p := p) (σ := σ) M.φ.isLB x
  have hi := mem_ptsIn.1 hxi
  obtain ⟨n, g, e, u, inst, hR, hI, hf⟩ :=
    GlobalTheory.SncForm.germ_eq_unit_mul_monomial X M.B M.φ.isLB s hs r z hz hco hzero _ (hsnc _) (pick M.φ.isLB x) hi
  obtain ⟨V, hV, G', hG'⟩ := GlobalTheory.DivSec.exists_affine_germ_eq X (x.1 (IsLocalRing.closedPoint ℂ)) (n + 1)
    (Fin.cons (u : X.presheaf.stalk _) g)
  let G : Fin n → Γ(X, V.1) := fun j => G' j.succ
  have hG : ∀ j, X.presheaf.germ V.1 _ hV (G j) = g j := fun j => hG' j.succ
  have hU : X.presheaf.germ V.1 _ hV (G' 0) = u := hG' 0
  have e1 := eventually_ev_eq x hi hV (s.f (pick M.φ.isLB x))
    (G' 0 * ∏ a, G (e a) ^ ((divOfSec M.φ.isLB s hs).mult (z a.1)).toNat) (by
      rw [hf, map_mul, map_prod, hU]
      simp only [map_pow, hG])
  have e2 := eventually_ev_ne_zero x hV (G' 0) (hU ▸ u.isUnit)
  have e3 := Filter.eventually_all.2 fun a => eventually_ev_eq_zero_iff x V hV (G (e a)) _ (by rw [hG]; exact hI a)
  have e4 : ∀ᶠ y in 𝓝 x, ∀ a, ¬ LiesIn x (Closeds.closure {z a}) → ¬ LiesIn y (Closeds.closure {z a}) :=
    Filter.eventually_all.2 fun a => by
      by_cases h : LiesIn x (Closeds.closure {z a})
      · exact Filter.Eventually.of_forall fun _ h' => absurd h h'
      · exact Filter.eventually_of_mem ((isOpen_not_liesIn _).mem_nhds h) fun y hy _ => hy
  have e5 : ∀ᶠ y in 𝓝 x, y ∈ M.φ.locPot.U x := (M.φ.locPot.isOpen_U x).mem_nhds (M.φ.locPot.mem_U x)
  obtain ⟨hn, ψ, hψ, hxψ, hN, hψV, hev⟩ := exists_compatChart hA x (e1.and (e2.and (e3.and (e4.and e5)))) V hV G
    (by rw [funext hG]; exact hR)
  let τ : Fin r → Option (Fin D) := fun a =>
    if h : x.1 (IsLocalRing.closedPoint ℂ) ∈ Closeds.closure {z a} then some (Fin.castLE hn (e ⟨a, h⟩)) else none
  refine ⟨ψ, hψ, hxψ, fun y hy => (hN hy).2.2.2.2, τ, ?_, ?_, ev p σ V.1 (G' 0), ?_, fun y hy => (hN hy).2.1, ?_⟩
  · intro a a' i h1 h2
    simp only [τ] at h1 h2
    split_ifs at h1 h2 with ha ha'
    have := Fin.castLE_injective hn ((Option.some.inj h1).trans (Option.some.inj h2).symm)
    exact congrArg Subtype.val (e.injective this)
  · intro a
    ext y
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_range_ptMap_closι]
    refine and_comm.trans (and_congr_right fun hy => ?_)
    by_cases h : x.1 (IsLocalRing.closedPoint ℂ) ∈ Closeds.closure {z a}
    · simp only [τ, dif_pos h, Option.some.injEq, exists_eq_left', hev y hy]
      exact ((hN hy).2.2.1 ⟨a, h⟩).symm
    · simp only [τ, dif_neg h, reduceCtorEq, false_and, exists_false, iff_false]
      exact (hN hy).2.2.2.1 a h
  · exact (hA.holoOn_iff hA.anRead ψ.open_source).2 ((hA.anRead.holoOn_ev V.1 (G' 0)).mono hψV)
  · intro y hy
    refine (hN hy).1.trans ?_
    rw [ev_mul, ev_eq (hψV hy) (∏ _, _), map_prod,
      ← Fintype.prod_subtype_mul_prod_subtype (fun a => x.1 (IsLocalRing.closedPoint ℂ) ∈ Closeds.closure {z a})]
    congr 1
    rw [Finset.prod_eq_one (s := Finset.univ)
      (f := fun a : {a // ¬ x.1 (IsLocalRing.closedPoint ℂ) ∈ Closeds.closure {z a}} => _)
      (fun a _ => by simp only [τ, dif_neg a.2]), mul_one]
    refine Finset.prod_congr (by ext; simp) fun a _ => ?_
    simp only [τ, dif_pos a.2, map_pow, hev y hy, ev_eq (hψV hy)]

end GlobalTheory.SecSnc
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAnalyticSNC_of_algebraicSNC_section : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → SmoothOfRelativeDimension D p → ∀ (A : FinHolAtlas D (CxPts p σ)), IsAlgAtlas A → ∀ (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (r : ℕ) (z : Fin r → X), Function.Injective z → (∀ a, Order.coheight (z a) = 1) → ((nonzeroLocus s : Set X)ᶜ = ⋃ a, closure {z a}) → (∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x) → IsSNC A M.φ.locPot (M.φ.locSec (secVal p σ s)) (fun a => ((divOfSec M.φ.isLB s hs).mult (z a)).toNat) (fun a => Set.range (ptMap (closι (z a)) rfl σ)) := by
  atlas_forward_decl GlobalTheory.SecSnc.isSNC_locSec
end

section
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

open ReciprocityTheory.AnForm.R

namespace GlobalTheory.SncLocal

theorem mem_comps_of_compList {X : Scheme.{0}} {B : Set X} {m : ℕ} {C : Fin m → Closeds X}
    (hC : FinalTheorems.CompList B C) (i : Fin m) : (C i : Set X) ∈ ReciprocityTheory.AnForm.R.comps B := by
  classical
  refine ⟨⟨hC.1 i, hC.2.1 ▸ Set.subset_iUnion (fun j => (C j : Set X)) i⟩, fun D hD hiD => ?_⟩
  obtain ⟨z, hz, hDz⟩ := (isIrreducible_iff_sUnion_isClosed.1 hD.1)
    (Finset.univ.image fun j => (C j : Set X))
    (fun z hz => by
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
      exact (C j).isClosed)
    (by
      refine hD.2.trans (hC.2.1 ▸ Set.iUnion_subset fun j => ?_)
      exact Set.subset_sUnion_of_mem (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
  have hij : i = j := hC.2.2 i j (hiD.trans hDz)
  subst hij
  exact hDz

theorem lSncAt_of_snc (X : Scheme.{0}) [IsNoetherian X] (B : Closeds X) (m : ℕ) (C : Fin m → Closeds X)
    (hB : Snc (Scheme.IdealSheafData.vanishingIdeal B)) (hC : CompList (B : Set X) C) (x : X) :
    LSncAt X C x := by
  obtain ⟨hreg, U, hx, n, f, J, hrsp, hZU⟩ := hB x
  haveI := hreg
  have hs : ((Scheme.IdealSheafData.vanishingIdeal B).support : Set X) = B := by simp
  obtain ⟨O, hxO, -, hO⟩ := exists_open_comps x U hx f J hrsp hZU
  have key : ∀ i : {i : Fin m // x ∈ C i}, ∃ j ∈ J,
      ReciprocityTheory.AnForm.R.IsBranch ((Scheme.IdealSheafData.vanishingIdeal B).support : Set X) (f j) x (C i.1) ∧
      stalkId (Scheme.IdealSheafData.vanishingIdeal (C i.1)) x =
        Ideal.span {X.presheaf.germ U.1 x hx (f j)} := by
    rintro ⟨i, hxi⟩
    have hCi : ((C i : Closeds X) : Set X) ∈
        ReciprocityTheory.AnForm.R.comps ((Scheme.IdealSheafData.vanishingIdeal B).support : Set X) :=
      hs ▸ mem_comps_of_compList hC i
    have hO' := hO _ hCi
    have hq : ∀ q : PrimeSpectrum (X.presheaf.stalk x), X.fromSpecStalk x q ∈ (C i : Set X) ↔
        ∃ j ∈ J, ReciprocityTheory.AnForm.R.IsBranch ((Scheme.IdealSheafData.vanishingIdeal B).support : Set X)
          (f j) x (C i) ∧ X.presheaf.germ U.1 x hx (f j) ∈ q.asIdeal := by
      intro q
      have hqO : X.fromSpecStalk x q ∈ (O : Set X) := by
        have h : X.fromSpecStalk x q ∈ Set.range (X.fromSpecStalk x) := ⟨q, rfl⟩
        rw [Scheme.range_fromSpecStalk] at h
        exact Specializes.mem_open h O.isOpen hxO
      have h := Set.ext_iff.1 hO' (X.fromSpecStalk x q)
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hqO, and_true, true_and,
        GlobalTheory.SncComponents.fromSpecStalk_mem_zeroLocus_iff U x hx] at h
      exact h
    obtain ⟨j, hj, hbj, -⟩ := (hq (IsLocalRing.closedPoint _)).1
      (by rw [Scheme.fromSpecStalk_closedPoint]; exact hxi)
    refine ⟨j, hj, hbj, ?_⟩
    have hCC : (C i).compl.compl = C i := SetLike.coe_injective (compl_compl _)
    have hp : Prime (X.presheaf.germ U.1 x hx (f j)) :=
      prime_of_regular_params (fun i => X.presheaf.germ U.1 x hx (f i)) hrsp.1 hrsp.2 j
    have h := GlobalTheory.AffineComplement.stalkId_vanishingIdeal_compl (C i).compl x
      (X.presheaf.germ U.1 x hx (f j)) fun q => by
        refine not_congr ((hq q).trans ⟨?_, fun h => ⟨j, hj, hbj, h⟩⟩)
        rintro ⟨k, hk, hbk, h⟩
        by_cases hjk : j = k
        · exact hjk ▸ h
        · exact absurd rfl (branch_ne x U hx f J hrsp hZU hj hk hjk hbj hbk)
    rw [hCC] at h
    rw [h]
    exact ((Ideal.span_singleton_prime hp.ne_zero).2 hp).radical
  choose g hgJ hgb hgs using key
  refine ⟨hreg, n, fun k => X.presheaf.germ U.1 x hx (f k), ⟨g, fun a b hab => ?_⟩, hrsp, hgs⟩
  have h1 := hgb a
  rw [hab] at h1
  obtain ⟨D, -, hD⟩ := existsUnique_branch x U hx f J hrsp hZU (g b) (hgJ b)
  have e : (C a.1 : Set X) = C b.1 := (hD _ h1).trans (hD _ (hgb b)).symm
  exact Subtype.ext (hC.2.2 _ _ e.le)

theorem lSncAt_of_snc' : ∀ (X : Scheme.{0}) [IsNoetherian X] (B : Closeds X) (m : ℕ) (C : Fin m → Closeds X), Snc (Scheme.IdealSheafData.vanishingIdeal B) → CompList (B : Set X) C → ∀ x : X, LSncAt X C x :=
  fun X _ B m C hB hC x => lSncAt_of_snc X B m C hB hC x

end GlobalTheory.SncLocal
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.SncGenericPoints

theorem mem_vanishingIdeal_closure {X : Scheme.{0}} (x : X) (U : X.affineOpens) (hx : x ∈ U.1)
    (s : Γ(X, U.1)) (hs : ¬ IsUnit (X.presheaf.germ U.1 x hx s)) :
    s ∈ (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})).ideal U := by
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
  intro q hq
  by_contra hsq
  have hp : q ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen s := by
    rw [U.2.fromSpec_preimage_basicOpen]; exact hsq
  have hq' : U.2.fromSpec q ∈ closure ({x} : Set X) := hq
  have hsp : x ⤳ U.2.fromSpec q := specializes_iff_mem_closure.2 hq'
  have hxs : x ∈ X.basicOpen s := hsp.mem_open (X.basicOpen s).isOpen hp
  exact hs ((X.mem_basicOpen s x hx).1 hxs)

theorem maximalIdeal_le_stalkId {X : Scheme.{0}} (x : X) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk x) ≤
      FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})) x := by
  intro a ha
  obtain ⟨V, hxV, f, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  have hle : W ≤ V := hWV
  have e : X.presheaf.germ W x hxW (X.presheaf.map (homOfLE hle).op f) = X.presheaf.germ V x hxV f :=
    X.presheaf.germ_res_apply (homOfLE hle) x hxW f
  rw [← e] at ha ⊢
  generalize X.presheaf.map (homOfLE hle).op f = g at ha ⊢
  have hu : ¬ IsUnit (X.presheaf.germ W x hxW g) :=
    mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 ha)
  have hm := mem_vanishingIdeal_closure x ⟨W, hW⟩ hxW g hu
  have h1 : Ideal.map (X.presheaf.germ W x hxW).hom
      ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})).ideal ⟨W, hW⟩) ≤
      FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})) x :=
    le_iSup₂_of_le (f := fun (U : X.affineOpens) (hx : x ∈ U.1) =>
      Ideal.map (X.presheaf.germ U.1 x hx).hom
        ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})).ideal U)) ⟨W, hW⟩ hxW le_rfl
  exact h1 (Ideal.mem_map_of_mem _ hm)

theorem coheight_eq_one_of_lSncAt {X : Scheme.{0}} {r : ℕ} (z : Fin r → X) (a : Fin r)
    (h : FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) (z a)) : Order.coheight (z a) = 1 := by
  obtain ⟨hreg, n, t, e, ht, hI⟩ := h
  have ha : z a ∈ (Closeds.closure {z a} : Closeds X) := subset_closure (Set.mem_singleton _)
  have hn : 1 ≤ n := (e ⟨a, ha⟩).pos
  have hm : IsLocalRing.maximalIdeal (X.presheaf.stalk (z a)) = Ideal.span {t (e ⟨a, ha⟩)} := by
    refine le_antisymm ((maximalIdeal_le_stalkId (z a)).trans (hI ⟨a, ha⟩).le) ?_
    rw [← ht.1]
    exact Ideal.span_mono (Set.singleton_subset_iff.2 ⟨_, rfl⟩)
  have hmin : IsLocalRing.maximalIdeal (X.presheaf.stalk (z a)) ∈
      (Ideal.span {t (e ⟨a, ha⟩)}).minimalPrimes := by
    rw [← hm, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl
  have hle := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  have h1 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := X.presheaf.stalk (z a))
  have h2 := ringKrullDim_stalk_eq_coheight (z a)
  have h3 : (IsLocalRing.maximalIdeal (X.presheaf.stalk (z a))).height = Order.coheight (z a) :=
    WithBot.coe_eq_coe.1 (h1.trans h2)
  have h4 : ((n : ℕ∞)) = Order.coheight (z a) := WithBot.coe_eq_coe.1 (ht.2.trans h2)
  refine le_antisymm (h3 ▸ hle) ?_
  rw [← h4]
  exact_mod_cast hn

theorem exists_genericPoints : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (D : ℕ), IsProjOver p → SmoothOfRelativeDimension D p → ∀ T : Closeds X, FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal T) → ∃ (r : ℕ) (z : Fin r → X), Function.Injective z ∧ (∀ a, Order.coheight (z a) = 1) ∧ (T : Set X) = ⋃ a, closure {z a} ∧ (∀ w : X, w ∈ T → Order.coheight w = 1 → ∃ a, w = z a) ∧ ∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x := by
  intro F _ X _ p D hp hs T hT
  haveI : QuasiCompact p := by
    obtain ⟨N, i, hi, rfl⟩ := hp
    haveI : IsProper (PSpace.str F N) := isProper_str F N
    infer_instance
  haveI : Smooth p := SmoothOfRelativeDimension.smooth D p
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  haveI : IsNoetherian X := {}
  obtain ⟨m, C, hC, -⟩ := GlobalTheory.SncComponents.exists_compList_effCartier F X p D T hT
  have hL := GlobalTheory.SncLocal.lSncAt_of_snc' X T m C hT hC
  have hz : ∀ a, ∃ z : X, closure {z} = (C a : Set X) := fun a =>
    QuasiSober.sober (hC.1 a) (C a).isClosed
  choose z hz using hz
  have hCz : (fun a => (Closeds.closure {z a} : Closeds X)) = C :=
    funext fun a => SetLike.coe_injective (hz a)
  have hL' : ∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x := by
    rw [hCz]; exact hL
  have hco : ∀ a, Order.coheight (z a) = 1 := fun a => coheight_eq_one_of_lSncAt z a (hL' _)
  have hU : (T : Set X) = ⋃ a, closure {z a} := by
    rw [← hC.2.1]; simp only [hz]
  refine ⟨m, z, fun a b hab => hC.2.2 a b ?_, hco, hU, fun w hw hw1 => ?_, hL'⟩
  · rw [← hz, ← hz, hab]
  · have hw' : w ∈ (T : Set X) := hw
    rw [hU] at hw'
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hw'
    have hsp : z a ⤳ w := specializes_iff_mem_closure.2 ha
    refine ⟨a, ?_⟩
    by_contra hne
    have hlt : w < z a := lt_of_le_not_ge hsp fun h =>
      hne ((show w ⤳ z a from h).antisymm hsp).eq
    have := Order.coheight_strictAnti hlt (by rw [hco a]; exact ENat.natCast_lt_top 1)
    rw [hco a, hw1] at this
    exact lt_irrefl _ this

end GlobalTheory.SncGenericPoints
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_closed_eq_iUnion_closure_codim_one_points : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (D : ℕ), IsProjOver p → SmoothOfRelativeDimension D p → ∀ T : Closeds X, FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal T) → ∃ (r : ℕ) (z : Fin r → X), Function.Injective z ∧ (∀ a, Order.coheight (z a) = 1) ∧ (T : Set X) = ⋃ a, closure {z a} ∧ (∀ w : X, w ∈ T → Order.coheight w = 1 → ∃ a, w = z a) ∧ ∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x := by
  atlas_forward_decl GlobalTheory.SncGenericPoints.exists_genericPoints
end

section
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

open GlobalTheory.Mean4O.CombForm in

theorem exists_subAtlas : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (π : Y ⟶ X) [IsClosedImmersion π] (hπ : π ≫ p = q) (e : ℕ) (A : FinHolAtlas (e + 1) (CxPts p σ)), IsAlgAtlas A → SmoothOfRelativeDimension e q → ∃ B : FinHolAtlas e (Set.range (ptMap π hπ σ)), HoloMap B A Subtype.val ∧ ∀ (L : Fin e → MLine p σ) (v : CxPts p σ → ℝ), Continuous v → mInt B (fun i => (L i).φ.locPot.pullback Subtype.val continuous_subtype_val) (v ∘ Subtype.val) = Mix.int (fun i => (L i).pull π hπ) (fun y => v (ptMap π hπ σ y)) := by
  intro k _ X Y p q σ hp π _ hπ e A hA hs
  have hq : IsProjOver q := by
    obtain ⟨N, i, hi, h⟩ := hp
    exact ⟨N, π ≫ i, inferInstance, by rw [Category.assoc, h, hπ]⟩
  haveI : CompactSpace (CxPts q σ) := CxPts.compactSpace σ hq
  haveI : T2Space (CxPts q σ) := CxPts.t2Space_cxPts_of_isProjOver σ hq
  haveI : SecondCountableTopology (CxPts q σ) := CxPts.secondCountableTopology_of_isProjOver σ hq
  haveI : T2Space (CxPts p σ) := CxPts.t2Space_cxPts_of_isProjOver σ hp
  have hc : Continuous (ptMap π hπ σ) := PtsOver.continuous_map π hπ _
  have hinj : Function.Injective (ptMap π hπ σ) := fun a b h =>
    Subtype.ext ((cancel_mono π).1 (congrArg Subtype.val h))
  have hE : IsClosedEmbedding (ptMap π hπ σ) := hc.isClosedEmbedding hinj
  let h : CxPts q σ ≃ₜ Set.range (ptMap π hπ σ) := hE.isEmbedding.toHomeomorph
  haveI : CompactSpace (Set.range (ptMap π hπ σ)) := h.compactSpace
  let A' : FinHolAtlas e (CxPts q σ) := (AnRead.all q σ e).finAtlas
  have hA' : IsAlgAtlas A' := AnRead.isAlgAtlas_finAtlas _
  have hm : HoloMap A' A (ptMap π hπ σ) := hA.holoMap hA' (f := π) fun _ => rfl
  have hB : HoloMap (tAtlas A' h) A Subtype.val := ⟨continuous_subtype_val, fun j l => hm.2 j l⟩
  refine ⟨tAtlas A' h, hB, fun L v hv => ?_⟩
  have hsm (i : Fin e) : (L i).φ.IsSmooth hA.anRead := (Weight.isCInf_iff_isSmooth _).1 (L i).cInf
  have hv' : Continuous fun y => v (ptMap π hπ σ y) := hv.comp hc
  have hP (i : Fin e) : IsPotential A' ((L i).pull π hπ).φ.locPot :=
    Weight.isPotential_locPot ((Weight.isCInf_iff_isSmooth _).1 ((L i).pull π hπ).cInf)
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact k Y q σ e A' hA' (fun i => (L i).pull π hπ) _ hv'.measurable
  rw [h₂ (h₁.2 (mIntegrableCont _ _ hP _ hv')),
    GlobalTheory.Adopt.mongeAmpereIntegral_invariant_homeomorph_transport e _ _ A' h _ _
      (fun i => isPotentialPullback A _ _ hB _ ((hsm i).isPotential hA))
      (hv.comp continuous_subtype_val)]
  exact (SameForm.mInt_eq (fun i => (hsm i).sameForm_pull hA hA' π hπ) _).symm

end GlobalTheory.Mix
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_subAtlas_smooth_closedSubscheme : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (π : Y ⟶ X) [IsClosedImmersion π] (hπ : π ≫ p = q) (e : ℕ) (A : FinHolAtlas (e + 1) (CxPts p σ)), IsAlgAtlas A → SmoothOfRelativeDimension e q → ∃ B : FinHolAtlas e (Set.range (ptMap π hπ σ)), HoloMap B A Subtype.val ∧ ∀ (L : Fin e → MLine p σ) (v : CxPts p σ → ℝ), Continuous v → mInt B (fun i => (L i).φ.locPot.pullback Subtype.val continuous_subtype_val) (v ∘ Subtype.val) = Mix.int (fun i => (L i).pull π hπ) (fun y => v (ptMap π hπ σ y)) := by
  atlas_forward_decl GlobalTheory.Mix.exists_subAtlas
end

section
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix.PLSnc

theorem int_half {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ) : Mix.int L (fun y => f y / 2) = Mix.int L f / 2 := by
  simp only [Mix.int, integral_div, sub_div]

theorem finsum_mult {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {B : LB X} (hB : B.IsLB) (s : B.Sec)
    (hs : genericPoint X ∈ nonzeroLocus s) {r : ℕ} {z : Fin r → X} (hz : Function.Injective z)
    (h : ∀ w : X, w ∉ nonzeroLocus s → Order.coheight w = 1 → ∃ a, w = z a) (g : X → ℝ) :
    ∑ᶠ w, ((divOfSec hB s hs).mult w : ℝ) * g w =
      ∑ a, ((((divOfSec hB s hs).mult (z a)).toNat : ℕ) : ℝ) * g (z a) := by
  classical
  rw [finsum_eq_sum_of_support_subset (s := Finset.univ.image z), Finset.sum_image fun a _ b _ e => hz e]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (mult_divOfSec_nonneg _)]
  · intro w hw
    have h0 : (divOfSec hB s hs).mult w ≠ 0 := fun e => hw (by simp [e])
    obtain ⟨a, rfl⟩ := h w (fun e => notMem_supp_divOfSec.2 e (CartierDiv.mem_supp_of_mult_ne_zero h0))
      (CartierDiv.coheight_eq_one_of_mult_ne_zero h0)
    simp

theorem poincareLelong_snc : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → SmoothOfRelativeDimension (e + 1) p → ∀ (L : Fin e → MLine p σ) (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (nonzeroLocus s).compl) → ∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), 2 * Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (M.logSec s) = ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L u z - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) u := by
  intro F _ X _ _ p σ e hp hsm L M s hs hsnc u hu
  haveI : CharZero F := σ.charZero
  haveI := CxPts.compactSpace σ hp
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hp
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hp
  let R := AnRead.all p σ (e + 1)
  have hA := R.isAlgAtlas_finAtlas
  generalize R.finAtlas = A at hA
  obtain ⟨r, z, hinj, hco, hT, hall, hl⟩ := GlobalTheory.T.snc_closed_eq_iUnion_closure_codim_one_points F X p (e + 1) hp hsm _ hsnc
  have hS := GlobalTheory.T.isAnalyticSNC_of_algebraicSNC_section F X p σ (e + 1) hp hsm A hA M s hs r z hinj hco hT hl
  choose B hB hBint using fun a => GlobalTheory.T.exists_holomorphic_subAtlas_smooth_closedSubscheme F X (clos (z a)) p _ σ hp (closι (z a)) rfl e A hA
    (GlobalTheory.T.smooth_snc_component_closure_charZero F X p e hp hsm r z hl a)
  have pot (N : MLine p σ) : IsPotential A N.φ.locPot :=
    ((Weight.isCInf_iff_isSmooth R).1 N.cInf).isPotential hA
  have hv (y) : CInfAt (fun y => u y / 2) y :=
    ((hu y).const_mul (1 / 2)).congr (.of_forall fun z => by ring)
  have hvc : Continuous fun y => u y / 2 := continuous_iff_continuousAt.2 fun y => (hv y).continuousAt
  have key := poincareLelong A M.φ.locPot _ _ _ B (pot M)
    (M.φ.isSection_of_isAlgAtlas hA (R.secVal_mem_holSec s)) hS hB (fun y => u y / 2)
    ((hA.smooth_iff R).2 ((cInfAt_iff_smoothOn R isOpen_univ).1 fun y _ => hv y))
    (fun i => (L i).φ.locPot) fun i => pot _
  have e₁ : logNormSec M.φ.locPot (M.φ.locSec (secVal p σ s)) = M.logSec s := funext fun y => by
    rw [Weight.logNormSec_locSec, MLine.logSec]; ring
  have e₂ : Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (M.logSec s) =
      mInt A (Fin.cons (LocPot.ofFun fun y => u y / 2) fun i => (L i).φ.locPot) (M.logSec s) := by
    rw [(GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact F X p σ _ A hA _ _ (GlobalTheory.Mix.SecNorm.logSec_basic F X p σ M s).1).2
      (GlobalTheory.T.integrable_logNormSection_mixedChernForms F X p σ _ hp hsm _ M s hs)]
    refine SameForm.mInt_eq (fun i => ?_) _
    refine Fin.cases ?_ (fun i => ?_) i
    · exact Weight.sameForm_ofFun A u
    · exact SameForm.refl _ _
  have e₃ : Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (fun y => u y / 2) =
      mInt A (Fin.cons M.φ.locPot fun i => (L i).φ.locPot) fun y => u y / 2 := by
    have h := GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact F X p σ _ A hA (Fin.cons M L : Fin (e + 1) → MLine p σ) _ hvc.measurable
    rw [h.2 (h.1.2 (mIntegrableCont A _ (fun i => pot _) _ hvc))]
    congr 1
    exact funext fun i => Fin.cases rfl (fun _ => rfl) i
  have e₄ (a) : mInt (B a) (fun i => (L i).φ.locPot.pullback Subtype.val continuous_subtype_val)
      ((fun y => u y / 2) ∘ Subtype.val) = cycInt L u (z a) / 2 :=
    (hBint a L _ hvc).trans (int_half _ _)
  rw [e₁, ← e₂, ← e₃, int_half] at key
  simp only [e₄] at key
  rw [key, finsum_mult M.φ.isLB s hs hinj (fun w hw => hall w hw), mul_sub, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun a _ => by ring
  · ring

end GlobalTheory.Mix.PLSnc
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareLelong_normalCrossings_smoothProjective : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → SmoothOfRelativeDimension (e + 1) p → ∀ (L : Fin e → MLine p σ) (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (nonzeroLocus s).compl) → ∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), 2 * Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (M.logSec s) = ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L u z - Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) u := by
  atlas_forward_decl GlobalTheory.Mix.PLSnc.poincareLelong_snc
end
