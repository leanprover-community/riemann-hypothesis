import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksSubOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearOfBilinearSchwartzBruhatProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanSchwartzBruhatProductEqTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilInertPlaceVacuumEigenfunction
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingLocalIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingLocalEquivariance
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicIntertwine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharEqAddEquivAddHaarChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzAdelicEqSpanPure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilObjectsInhabited
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentMapsForThetaTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumTwistedVacuumConditionDoubledLattic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblScal.LocAt

theorem liftV_one_mul' {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  refine Prod.ext ?_ ?_
  · exact zero_mul _
  · change GlobalTheory.AdelicU.singleFin v 1 * b.2 = GlobalTheory.AdelicU.singleFin v (evFin F v b)
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
      rfl
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, GlobalTheory.AdelicU.evalV_singleFin_ne hw, zero_mul]

theorem schr_trans' {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ]
    (w : κ → AF F) (Φ : (κ → AF F) → ℂ) : GlobalTheory.WeilM.schr ψ (w, 0) Φ = fun y => Φ (y + w) := by
  funext y
  simp [GlobalTheory.WeilM.schr]

theorem acts_of_comm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (ψ : AddChar (AF F) ℂ) (hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T Φ ∈ GlobalTheory.WeilM.schA F κ)
    (hunit : ∀ μ : @MeasureTheory.Measure (κ → AF F) (borel _),
      @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∫⁻ y, ‖T Φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖Φ y‖ₑ ^ 2 ∂μ)
    (hcomm : ∀ u : AF F, evFin F v u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
      T (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (T Φ))
    (φ : (κ → Fv F v) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) :
    ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T φ φ₁ := by
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v ψ T hstd (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace ψ hstd) hkeep hunit hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : κ → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h := hcomm u hu p 0 Φ hΦ
    rw [smul_zero, schr_trans', schr_trans'] at h
    exact h
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  refine ⟨(R 0)⁻¹ • fun t => T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩
  · exact (GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ (GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2))
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← liftV_one_mul']
      ring
    have hpat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R with hΦ₀
    set Φ₁ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (κ → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem _ _ hm₀)
    have hfz : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, hpdef, Pi.smul_apply, smul_eq_mul]
    field_simp

end GlobalTheory.DblScal.LocAt

namespace GlobalTheory.DblScal.LocAt

theorem locOps : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd → ∀ v : Pl F, GlobalTheory.DblScal.LocOps omd v := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP dd omd hS v g hg φ hφ
  refine acts_of_comm v B.ψ hP.base.std (omd g) (fun Φ hΦ => hS.pres g Φ hΦ)
    (fun μ hμ Φ hΦ => hS.unit μ hμ g Φ hΦ) ?_ φ hφ
  intro u hu p q Φ hΦ
  set w := dd.e.symm (p, q) with hw
  have he : dd.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  let G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) := ((g : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix _ _ _)
  have h2 : u • (G - 1) = 0 := hg u hu
  have e2 : (u • w) * G.transpose = u • w := by
    have : (u • w) * G.transpose - u • w = w * (u • (G - 1)).transpose := by
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.mul_sub, Matrix.mul_one, smul_sub]
    rw [h2, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
    exact this
  have hact : actB (cA σ) g (u • w) = u • w := e2
  have h3 := hS.impl g (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h3
  exact h3

end GlobalTheory.DblScal.LocAt
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_splitting_pair_identity : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd → ∀ v : Pl F, GlobalTheory.DblScal.LocOps omd v := by
  atlas_forward_decl GlobalTheory.DblScal.LocAt.locOps
end

section
section
open scoped TensorProduct
open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac

noncomputable section
namespace GlobalTheory.SBProdExt

def comapEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    SB Y ≃ₗ[ℂ] SB X :=
  LinearEquiv.ofLinear (comapH e) (comapH e.symm)
    (LinearMap.ext fun F => Subtype.ext (funext fun x => by simp))
    (LinearMap.ext fun F => Subtype.ext (funext fun y => by simp))

def restrictEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : (X → ℂ) →ₗ[ℂ] (Y → ℂ)) (hf : Set.BijOn f (SB X : Set (X → ℂ)) (SB Y : Set (Y → ℂ))) :
    SB X ≃ₗ[ℂ] SB Y :=
  LinearEquiv.ofBijective (f.restrict (p := SB X) (q := SB Y) fun x hx => hf.mapsTo hx)
    ⟨fun a b hab => Subtype.ext (hf.injOn a.2 b.2 (congrArg Subtype.val hab)),
     fun y => by
       obtain ⟨x, hx, hxy⟩ := hf.surjOn y.2
       exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

theorem exists_prod_equiv {P Q P' Q' : Type} [TopologicalSpace P] [T2Space P] [LocallyCompactSpace P]
    [TotallyDisconnectedSpace P] [TopologicalSpace Q] [T2Space Q] [LocallyCompactSpace Q]
    [TotallyDisconnectedSpace Q] [TopologicalSpace P'] [T2Space P'] [LocallyCompactSpace P']
    [TotallyDisconnectedSpace P'] [TopologicalSpace Q'] [T2Space Q'] [LocallyCompactSpace Q']
    [TotallyDisconnectedSpace Q'] (eP : SB P ≃ₗ[ℂ] SB P') (eQ : SB Q ≃ₗ[ℂ] SB Q') :
    ∃ L : SB (P × Q) ≃ₗ[ℂ] SB (P' × Q'), ∀ a b, L (prodSB a b) = prodSB (eP a) (eQ b) := by
  obtain ⟨l, hl⟩ := exists_linear_of_bilinear_prodSB P Q (SB (P' × Q'))
    ((prodSBBil P' Q').compl₁₂ eP.toLinearMap eQ.toLinearMap)
  obtain ⟨l', hl'⟩ := exists_linear_of_bilinear_prodSB P' Q' (SB (P × Q))
    ((prodSBBil P Q).compl₁₂ eP.symm.toLinearMap eQ.symm.toLinearMap)
  have h1 : l.comp l' = LinearMap.id := by
    refine LinearMap.ext_on_range (Span.span_prodSB_eq_top P' Q') fun q => ?_
    simp [hl, hl', prodSBBil]
  have h2 : l'.comp l = LinearMap.id := by
    refine LinearMap.ext_on_range (Span.span_prodSB_eq_top P Q) fun q => ?_
    simp [hl, hl', prodSBBil]
  refine ⟨LinearEquiv.ofLinear l l' h1 h2, fun a b => ?_⟩
  simp [hl, prodSBBil]

theorem exists_linear_bijOn_prod : ∀ {P Q P' Q' Z Z' : Type} [TopologicalSpace P] [T2Space P] [LocallyCompactSpace P]
    [TotallyDisconnectedSpace P] [TopologicalSpace Q] [T2Space Q] [LocallyCompactSpace Q] [TotallyDisconnectedSpace Q]
    [TopologicalSpace P'] [T2Space P'] [LocallyCompactSpace P'] [TotallyDisconnectedSpace P']
    [TopologicalSpace Q'] [T2Space Q'] [LocallyCompactSpace Q'] [TotallyDisconnectedSpace Q']
    [TopologicalSpace Z] [TopologicalSpace Z'] (eZ : Z ≃ₜ P × Q) (eZ' : Z' ≃ₜ P' × Q')
    (f : (P → ℂ) →ₗ[ℂ] (P' → ℂ)) (g : (Q → ℂ) →ₗ[ℂ] (Q' → ℂ)),
    Set.BijOn f (GlobalTheory.WeilM.SB P : Set (P → ℂ)) (GlobalTheory.WeilM.SB P' : Set (P' → ℂ)) →
    Set.BijOn g (GlobalTheory.WeilM.SB Q : Set (Q → ℂ)) (GlobalTheory.WeilM.SB Q' : Set (Q' → ℂ)) →
    ∃ h : (Z → ℂ) →ₗ[ℂ] (Z' → ℂ), Set.BijOn h (GlobalTheory.WeilM.SB Z : Set (Z → ℂ)) (GlobalTheory.WeilM.SB Z' : Set (Z' → ℂ)) ∧
      ∀ a ∈ GlobalTheory.WeilM.SB P, ∀ b ∈ GlobalTheory.WeilM.SB Q,
        h (fun z => a (eZ z).1 * b (eZ z).2) = fun z' => f a (eZ' z').1 * g b (eZ' z').2 := by
  intro P Q P' Q' Z Z' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eZ eZ' f g hf hg
  simp only [GlobalTheory.WeilM.SB_eq] at hf hg ⊢
  obtain ⟨L, hL⟩ := exists_prod_equiv (restrictEquiv f hf) (restrictEquiv g hg)
  let E : SB Z ≃ₗ[ℂ] SB Z' := ((comapEquiv eZ).symm.trans L).trans (comapEquiv eZ')
  obtain ⟨h, hh⟩ := LinearMap.exists_extend ((SB Z').subtype.comp E.toLinearMap)
  have happ : ∀ F : SB Z, h F.1 = (E F).1 := fun F => LinearMap.congr_fun hh F
  refine ⟨h, ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩, fun a ha b hb => ?_⟩
  · rw [happ ⟨x, hx⟩]; exact (E _).2
  · rw [happ ⟨x, hx⟩, happ ⟨y, hy⟩] at hxy
    exact congrArg Subtype.val (E.injective (Subtype.ext hxy))
  · refine ⟨(E.symm ⟨y, hy⟩).1, (E.symm ⟨y, hy⟩).2, ?_⟩
    rw [happ]; simp
  · have hF : (fun z => a (eZ z).1 * b (eZ z).2) = (comapEquiv eZ (prodSB ⟨a, ha⟩ ⟨b, hb⟩)).1 := rfl
    rw [hF, happ]
    funext z'
    simp only [E, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, hL]
    rfl

end GlobalTheory.SBProdExt
end
end

open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totally_disconnected_product_locally_compact : ∀ {P Q P' Q' Z Z' : Type} [TopologicalSpace P] [T2Space P] [LocallyCompactSpace P]
    [TotallyDisconnectedSpace P] [TopologicalSpace Q] [T2Space Q] [LocallyCompactSpace Q] [TotallyDisconnectedSpace Q]
    [TopologicalSpace P'] [T2Space P'] [LocallyCompactSpace P'] [TotallyDisconnectedSpace P']
    [TopologicalSpace Q'] [T2Space Q'] [LocallyCompactSpace Q'] [TotallyDisconnectedSpace Q']
    [TopologicalSpace Z] [TopologicalSpace Z'] (eZ : Z ≃ₜ P × Q) (eZ' : Z' ≃ₜ P' × Q')
    (f : (P → ℂ) →ₗ[ℂ] (P' → ℂ)) (g : (Q → ℂ) →ₗ[ℂ] (Q' → ℂ)),
    Set.BijOn f (GlobalTheory.WeilM.SB P : Set (P → ℂ)) (GlobalTheory.WeilM.SB P' : Set (P' → ℂ)) →
    Set.BijOn g (GlobalTheory.WeilM.SB Q : Set (Q → ℂ)) (GlobalTheory.WeilM.SB Q' : Set (Q' → ℂ)) →
    ∃ h : (Z → ℂ) →ₗ[ℂ] (Z' → ℂ), Set.BijOn h (GlobalTheory.WeilM.SB Z : Set (Z → ℂ)) (GlobalTheory.WeilM.SB Z' : Set (Z' → ℂ)) ∧
      ∀ a ∈ GlobalTheory.WeilM.SB P, ∀ b ∈ GlobalTheory.WeilM.SB Q,
        h (fun z => a (eZ z).1 * b (eZ z).2) = fun z' => f a (eZ' z').1 * g b (eZ' z').2 := by
  atlas_forward_decl GlobalTheory.SBProdExt.exists_linear_bijOn_prod
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.DblLin

open Matrix

def schrLin {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w : (κ → R) × (κ → R)) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ → R) → ℂ) where
  toFun := schr ψ w
  map_add' f g := by funext x; simp only [schr, Pi.add_apply, mul_add]
  map_smul' a f := by funext x; simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def conjLin {Y Y' : Type} (ι : (Y → ℂ) →ₗ[ℂ] (Y' → ℂ)) : (Y → ℂ) →ₗ[ℂ] (Y' → ℂ) where
  toFun φ := star (ι (star φ))
  map_add' f g := by rw [star_add, map_add, star_add]
  map_smul' a f := by rw [star_smul, map_smul, star_smul, star_star]; rfl

theorem star_mem_SB {Y : Type} [TopologicalSpace Y] {f : Y → ℂ} (hf : f ∈ SB Y) : star f ∈ SB Y :=
  ⟨hf.1.comp star, hf.2.comp_left (g := star) (star_zero ℂ)⟩

theorem conjLin_bijOn {Y Y' : Type} [TopologicalSpace Y] [TopologicalSpace Y'] (ι : (Y → ℂ) →ₗ[ℂ] (Y' → ℂ))
    (h : Set.BijOn ι (SB Y : Set (Y → ℂ)) (SB Y' : Set (Y' → ℂ))) :
    Set.BijOn (conjLin ι) (SB Y : Set (Y → ℂ)) (SB Y' : Set (Y' → ℂ)) := by
  refine ⟨fun φ hφ => star_mem_SB (h.mapsTo (star_mem_SB hφ)), fun φ hφ φ' hφ' e => ?_, fun g hg => ?_⟩
  · have e' : ι (star φ) = ι (star φ') := star_injective e
    exact star_injective (h.injOn (star_mem_SB hφ) (star_mem_SB hφ') e')
  · obtain ⟨φ, hφ, e⟩ := h.surjOn (star_mem_SB hg)
    refine ⟨star φ, star_mem_SB hφ, ?_⟩
    show star (ι (star (star φ))) = g
    rw [star_star, e, star_star]

def colsHomeo (m a b k : Type) [TopologicalSpace k] :
    Matrix m (a ⊕ b) k ≃ₜ Matrix m a k × Matrix m b k where
  toFun Y := (Y.submatrix id Sum.inl, Y.submatrix id Sum.inr)
  invFun p := Matrix.fromCols p.1 p.2
  left_inv Y := by ext i (j | j) <;> rfl
  right_inv p := by ext <;> rfl
  continuous_toFun := (continuous_id.matrix_submatrix _ _).prodMk (continuous_id.matrix_submatrix _ _)
  continuous_invFun := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases j with j | j
    · exact (continuous_apply_apply i j).comp continuous_fst
    · exact (continuous_apply_apply i j).comp continuous_snd

theorem eqOn_SB_of_box {k : Type} [TopologicalSpace k] [T2Space k] [LocallyCompactSpace k] [TotallyDisconnectedSpace k]
    {κ : Type} [Fintype κ] {N : Type} [AddCommGroup N] [Module ℂ N] (L₁ L₂ : ((κ ⊕ κ → k) → ℂ) →ₗ[ℂ] N)
    (h : ∀ a ∈ SB (κ → k), ∀ b ∈ SB (κ → k), L₁ (boxFun a b) = L₂ (boxFun a b)) :
    ∀ φ ∈ SB (κ ⊕ κ → k), L₁ φ = L₂ φ := by
  intro φ hφ
  let e : (κ ⊕ κ → k) ≃ₜ (κ → k) × (κ → k) := Homeomorph.sumArrowHomeomorphProdArrow
  let M₁ : GlobalTheory.SplitWeil.SB ((κ → k) × (κ → k)) →ₗ[ℂ] N :=
    L₁ ∘ₗ (SB (κ ⊕ κ → k)).subtype ∘ₗ GlobalTheory.LocFlat.CFac.comapH e
  let M₂ : GlobalTheory.SplitWeil.SB ((κ → k) × (κ → k)) →ₗ[ℂ] N :=
    L₂ ∘ₗ (SB (κ ⊕ κ → k)).subtype ∘ₗ GlobalTheory.LocFlat.CFac.comapH e
  have hM : M₁ = M₂ := LinearMap.ext_on_range (GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top _ _)
    fun q => h q.1.1 q.1.2 q.2.1 q.2.2
  have := LinearMap.congr_fun hM (GlobalTheory.LocFlat.CFac.comapH e.symm ⟨φ, hφ⟩)
  have e2 : ((GlobalTheory.LocFlat.CFac.comapH e (GlobalTheory.LocFlat.CFac.comapH e.symm ⟨φ, hφ⟩)).1 : (κ ⊕ κ → k) → ℂ) = φ := by
    funext x
    simp only [GlobalTheory.LocFlat.CFac.comapH_apply, Homeomorph.symm_apply_apply]
  simp only [M₁, M₂, LinearMap.comp_apply, Submodule.subtype_apply] at this
  rw [← e2]
  exact this

theorem coord_inl {m k : Type} [Fintype m] [DecidableEq m] [Field k] {d : ℕ} (B : Matrix m m k)
    (A : Matrix m (Fin d ⊕ Fin d) k) (c : GL (Fin d) k) :
    (B * A * ((GlobalTheory.DblScal.dsum c)⁻¹).valᵀ).submatrix id Sum.inl = B * A.toCols₁ * (c⁻¹).valᵀ := by
  have e : ((GlobalTheory.DblScal.dsum c)⁻¹).val = Matrix.fromBlocks (c⁻¹).val 0 0 (c⁻¹).val := rfl
  conv_lhs => rw [e, fromBlocks_transpose, ← Matrix.fromCols_toCols A, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks]
  ext i j
  simp

theorem coord_inr {m k : Type} [Fintype m] [DecidableEq m] [Field k] {d : ℕ} (B : Matrix m m k)
    (A : Matrix m (Fin d ⊕ Fin d) k) (c : GL (Fin d) k) :
    (B * A * ((GlobalTheory.DblScal.dsum c)⁻¹).valᵀ).submatrix id Sum.inr = B * A.toCols₂ * (c⁻¹).valᵀ := by
  have e : ((GlobalTheory.DblScal.dsum c)⁻¹).val = Matrix.fromBlocks (c⁻¹).val 0 0 (c⁻¹).val := rfl
  conv_lhs => rw [e, fromBlocks_transpose, ← Matrix.fromCols_toCols A, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks]
  ext i j
  simp

theorem dblLin : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ dd : GlobalTheory.DblScal.DblCo σ X W, IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
    ∃ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd ∧
      ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₂ ∈ SB (Fin n × Fin d → Fv F v),
        ιd (boxFun φ₁ φ₂) = fun Y => ι φ₁ (Y.submatrix id Sum.inl) *
          starRingEnd ℂ (ι (fun x => starRingEnd ℂ (φ₂ x)) (Y.submatrix id Sum.inr)) := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair v t b c ι hι dd hdd
  classical
  have hψ1 : ∀ x, ‖B.ψ x‖ = 1 := GlobalTheory.StdCharFromIsStd.norm_psi hpair.base.std
  have hψc : Continuous B.ψ := hpair.base.std.1
  have hψv : ∀ x, ‖GlobalTheory.LatVac.psiAt B.ψ v x‖ = 1 := fun x => hψ1 _
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin d) (Fv F v)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin d → Fv F v))
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin d) (Fv F v)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin d → Fv F v))
  obtain ⟨ιd, hbij, hprod⟩ := GlobalTheory.T.totally_disconnected_product_locally_compact (Homeomorph.sumArrowHomeomorphProdArrow (X := Fv F v)
    (ι := Fin n × Fin d) (ι' := Fin n × Fin d)) (colsHomeo (Fin n) (Fin d) (Fin d) (Fv F v)) ι (conjLin ι) hι.bij
    (conjLin_bijOn ι hι.bij)
  have hbox : ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₂ ∈ SB (Fin n × Fin d → Fv F v),
      ιd (boxFun φ₁ φ₂) = fun Y => ι φ₁ (Y.submatrix id Sum.inl) * star (ι (star φ₂) (Y.submatrix id Sum.inr)) :=
    fun φ₁ h₁ φ₂ h₂ => hprod φ₁ h₁ φ₂ h₂

  have hsplit : ∀ u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E),
      GlobalTheory.LatVac.locCo dd v u = (Sum.elim (GlobalTheory.LatVac.locCo M.co v u.toCols₁).1 (GlobalTheory.LatVac.locCo M.co v u.toCols₂).1,
        Sum.elim (GlobalTheory.LatVac.locCo M.co v u.toCols₁).2 (-(GlobalTheory.LatVac.locCo M.co v u.toCols₂).2)) := by
    intro u
    have e := hdd u.toCols₁ u.toCols₂
    rw [Matrix.fromCols_toCols] at e
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · rcases k with k | k <;>
        simp [GlobalTheory.LatVac.locCo, e]
    · rcases k with k | k <;>
        simp [GlobalTheory.LatVac.locCo, e]
  have hat1 : ∀ u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E), At (evFin F v) u → At (evFin F v) u.toCols₁ :=
    fun u hu a ha => Matrix.ext fun i j => congrFun (congrFun (hu a ha) i) (Sum.inl j)
  have hat2 : ∀ u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E), At (evFin F v) u → At (evFin F v) u.toCols₂ :=
    fun u hu a ha => Matrix.ext fun i j => congrFun (congrFun (hu a ha) i) (Sum.inr j)
  have hmap1 : ∀ (u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) (π : AE F E →+* Fv F v), u.map π = 0 →
      u.toCols₁.map π = 0 := fun u π h => Matrix.ext fun i j => congrFun (congrFun h i) (Sum.inl j)
  have hmap2 : ∀ (u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) (π : AE F E →+* Fv F v), u.map π = 0 →
      u.toCols₂.map π = 0 := fun u π h => Matrix.ext fun i j => congrFun (congrFun h i) (Sum.inr j)
  have hc1 : ∀ (u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) (π : AE F E →+* Fv F v), (u.map π).toCols₁ = u.toCols₁.map π :=
    fun u π => rfl
  have hc2 : ∀ (u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) (π : AE F E →+* Fv F v), (u.map π).toCols₂ = u.toCols₂.map π :=
    fun u π => rfl

  have hloc : ∀ u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E), At (evFin F v) u →
      ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), ∀ φ₁, Acts (evFin F v) (dd.rho B.ψ u) φ φ₁ →
        φ₁ = schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v u) φ := fun u hu φ hφ φ₁ hA =>
    GlobalTheory.TensUniq.eq_of_tens_eq v φ _ _ hφ fun r hr =>
      (hA r hr).symm.trans (GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v u hu φ r hr)

  have hschr : ∀ u : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E), ∀ a ∈ SB (Fin n × Fin d → Fv F v),
      ∀ b' ∈ SB (Fin n × Fin d → Fv F v),
      ιd (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v u) (boxFun a b')) = fun Y =>
        ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u.toCols₁) a) (Y.submatrix id Sum.inl) *
          star (ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u.toCols₂) (star b'))
            (Y.submatrix id Sum.inr)) := by
    intro u a ha b' hb
    have e0 : boxFun a b' = boxFun a (fun x => star ((star b') x)) := by
      funext x; simp [boxFun]
    rw [hsplit u, e0, GlobalTheory.DblVacLine.schr_box _ hψv]
    rw [hbox _ (GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ a ha)
      (fun x => star (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u.toCols₂) (star b') x))
      (star_mem_SB (GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ _ (star_mem_SB hb)))]
    have e1 : (star fun x => star (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u.toCols₂) (star b') x)) =
        schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u.toCols₂) (star b') := by
      funext x; simp
    rw [e1]
  refine ⟨ιd, ⟨hbij, ?_, ?_⟩, hbox⟩
  · intro u hu hu0 φ hφ φ₁ hφ₁ hA Y
    rw [hloc u hu φ hφ φ₁ hA]
    set sh := (b⁻¹).val * u.map (piW t) * ((GlobalTheory.DblScal.dsum c)⁻¹).valᵀ
    have key := eqOn_SB_of_box (ιd ∘ₗ schrLin (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v u))
      (LinearMap.funLeft ℂ ℂ (fun Y => Y + sh) ∘ₗ ιd) (fun a ha b' hb => ?_) φ hφ
    · exact congrFun key Y
    show ιd (schr _ _ (boxFun a b')) = fun Y => ιd (boxFun a b') (Y + sh)
    rw [hschr u a ha b' hb, hbox a ha b' hb]
    funext Y
    have t1 := hι.trans u.toCols₁ (hat1 u hu) (hmap1 u _ hu0) a ha _ (GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ a ha)
      (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ (hat1 u hu) a) (Y.submatrix id Sum.inl)
    have t2 := hι.trans u.toCols₂ (hat2 u hu) (hmap2 u _ hu0) _ (star_mem_SB hb) _
      (GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ _ (star_mem_SB hb))
      (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ (hat2 u hu) _) (Y.submatrix id Sum.inr)
    have s1 : (Y + sh).submatrix id Sum.inl = Y.submatrix id Sum.inl + (b⁻¹).1 * u.toCols₁.map (piW t) * (c⁻¹).1ᵀ := by
      rw [show (Y + sh).submatrix id Sum.inl = Y.submatrix id Sum.inl + sh.submatrix id Sum.inl from rfl, coord_inl, hc1]
    have s2 : (Y + sh).submatrix id Sum.inr = Y.submatrix id Sum.inr + (b⁻¹).1 * u.toCols₂.map (piW t) * (c⁻¹).1ᵀ := by
      rw [show (Y + sh).submatrix id Sum.inr = Y.submatrix id Sum.inr + sh.submatrix id Sum.inr from rfl, coord_inr, hc2]
    rw [t1, t2]
    beta_reduce
    rw [s1, s2]
  · intro u hu hu0 φ hφ φ₁ hφ₁ hA x hx hx0
    rw [hloc u hu φ hφ φ₁ hA]
    set P := (b⁻¹).val * x.map (piW t) * ((GlobalTheory.DblScal.dsum c)⁻¹).valᵀ
    set z := B.ψ (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J)) x u)
    have key := eqOn_SB_of_box (LinearMap.proj P ∘ₗ ιd ∘ₗ schrLin (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v u))
      (z • (LinearMap.proj P ∘ₗ ιd)) (fun a ha b' hb => ?_) φ hφ
    · exact key
    show ιd (schr _ _ (boxFun a b')) P = z * ιd (boxFun a b') P
    rw [hschr u a ha b' hb, hbox a ha b' hb]
    have p1 : P.submatrix id Sum.inl = (b⁻¹).1 * x.toCols₁.map (piW t) * (c⁻¹).1ᵀ := by
      rw [coord_inl, hc1]
    have p2 : P.submatrix id Sum.inr = (b⁻¹).1 * x.toCols₂.map (piW t) * (c⁻¹).1ᵀ := by
      rw [coord_inr, hc2]
    have m1 := hι.mult u.toCols₁ (hat1 u hu) (hmap1 u _ hu0) a ha _ (GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ a ha)
      (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ (hat1 u hu) a) x.toCols₁ (hat1 x hx) (hmap1 x _ hx0)
    have m2 := hι.mult u.toCols₂ (hat2 u hu) (hmap2 u _ hu0) _ (star_mem_SB hb) _
      (GlobalTheory.SchrSB.schr_mem_SB B.ψ hψc v _ _ (star_mem_SB hb))
      (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v _ (hat2 u hu) _) x.toCols₂ (hat2 x hx) (hmap2 x _ hx0)
    beta_reduce
    rw [p1, p2, m1, m2]
    have hs : symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J)) x u =
        symp (cA σ) (-1) (incM F X.J) (incM F W.J) x.toCols₁ u.toCols₁ -
          symp (cA σ) (-1) (incM F X.J) (incM F W.J) x.toCols₂ u.toCols₂ := by
      conv_lhs => rw [← Matrix.fromCols_toCols x, ← Matrix.fromCols_toCols u]
      exact GlobalTheory.DblVacLine.symp_dbl _ _ _ _ _ _ _ _
    have hz : z = B.ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x.toCols₁ u.toCols₁) *
        star (B.ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x.toCols₂ u.toCols₂)) := by
      rw [GlobalTheory.DblVacLine.star_eq_neg B.ψ hψ1, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← hs]
    rw [hz, star_mul]
    ring

end GlobalTheory.DblLin
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_model_double_splitting : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ dd : GlobalTheory.DblScal.DblCo σ X W, IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
    ∃ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd ∧
      ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₂ ∈ SB (Fin n × Fin d → Fv F v),
        ιd (boxFun φ₁ φ₂) = fun Y => ι φ₁ (Y.submatrix id Sum.inl) *
          starRingEnd ℂ (ι (fun x => starRingEnd ℂ (φ₂ x)) (Y.submatrix id Sum.inr)) := by
  atlas_forward_decl GlobalTheory.DblLin.dblLin
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped Matrix Kronecker

noncomputable section

namespace GlobalTheory.DblSiegelScal

open Matrix MeasureTheory

section Algebra

variable {K : Type} [CommRing K] {β : Type} [Fintype β] [DecidableEq β]

theorem det_of_diag {a b c d T : Matrix β β K}
    (h : fromBlocks a b c d * (diagCols β : Matrix (β ⊕ β) β K) = (diagCols β : Matrix (β ⊕ β) β K) * T) :
    (fromBlocks a b c d).det = T.det * (d - b).det := by
  simp only [diagCols, fromRows_mul, fromBlocks_mul_fromRows, Matrix.mul_one, Matrix.one_mul, fromRows_ext_iff] at h
  have h6 : fromBlocks a b c d * fromBlocks 1 0 1 1 =
      fromBlocks 1 0 1 1 * (fromBlocks T b 0 (d - b) : Matrix (β ⊕ β) (β ⊕ β) K) := by
    simp [fromBlocks_multiply, h.1, h.2]
  simpa [det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁] using congrArg det h6

theorem adj_diag {P P' : Matrix (β ⊕ β) (β ⊕ β) K} {J T : Matrix β β K} (hJ : IsUnit J.det) (hP : IsUnit P.det)
    (hU : Pᵀ * fromBlocks J 0 0 (-J) * P' = fromBlocks J 0 0 (-J))
    (h : P * (diagCols β : Matrix (β ⊕ β) β K) = (diagCols β : Matrix (β ⊕ β) β K) * T) :
    ∃ T' : Matrix β β K, P' * (diagCols β : Matrix (β ⊕ β) β K) = (diagCols β : Matrix (β ⊕ β) β K) * T' ∧
      P.det * T'.det = T.det := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, P = fromBlocks a b c d := ⟨_, _, _, _, (fromBlocks_toBlocks P).symm⟩
  have hd := det_of_diag h
  have hT : IsUnit T.det := isUnit_of_mul_isUnit_left (hd ▸ hP)
  have h3 := congrArg (· * (diagCols β : Matrix (β ⊕ β) β K)) hU
  simp only [Matrix.mul_assoc] at h3
  obtain ⟨u, w, huw⟩ : ∃ u w, P' * (diagCols β : Matrix (β ⊕ β) β K) = fromRows u w := ⟨_, _, (fromRows_toRows _).symm⟩
  rw [huw] at h3 ⊢
  simp only [diagCols, fromBlocks_transpose, fromRows_mul, fromBlocks_mul_fromRows, Matrix.mul_one, Matrix.one_mul,
    Matrix.zero_mul, add_zero, zero_add, fromRows_ext_iff, Matrix.neg_mul, Matrix.mul_neg] at h h3 ⊢
  have e : Tᵀ * J * (u - w) = 0 := by
    have e1 : Tᵀ * (J * u) = aᵀ * (J * u) + bᵀ * (J * u) := by rw [← h.1, transpose_add, Matrix.add_mul]
    have e2 : Tᵀ * (J * w) = cᵀ * (J * w) + dᵀ * (J * w) := by rw [← h.2, transpose_add, Matrix.add_mul]
    rw [Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_sub, e1, e2]
    refine Eq.trans ?_ ((congrArg₂ (· + ·) h3.1 h3.2).trans (add_neg_cancel J))
    abel
  have hu : IsUnit (Tᵀ * J) := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [det_mul, det_transpose]; exact hT.mul hJ)
  obtain rfl : u = w := sub_eq_zero.1 (hu.mul_right_eq_zero.1 e)
  refine ⟨u, ⟨rfl, rfl⟩, ?_⟩
  have h4 : (d - b)ᵀ * J * u = J := by
    rw [transpose_sub, Matrix.mul_assoc, Matrix.sub_mul]
    refine Eq.trans ?_ ((congrArg Neg.neg h3.2).trans (neg_neg J))
    abel
  have h5 : (d - b).det * u.det = 1 := by
    have := congrArg det h4
    rw [det_mul, det_mul, det_transpose] at this
    exact hJ.mul_left_cancel (by linear_combination this)
  rw [hd, mul_assoc, h5, mul_one]

theorem mul_diagCols {α : Type} (z : Matrix α β K) : z * (diagCols β : Matrix (β ⊕ β) β K)ᵀ = fromCols z z := by
  rw [diagCols, transpose_fromRows, mul_fromCols, transpose_one, Matrix.mul_one]

theorem diagCols_map {L : Type} [CommRing L] (f : K →+* L) :
    (diagCols β : Matrix (β ⊕ β) β K).map f = diagCols β := by
  ext (i | i) j <;> by_cases hij : i = j <;> simp [diagCols, hij]

theorem symp_dbl_diag {R : Type} [CommRing R] [Algebra R K] (c : K →ₐ[R] K) {α : Type} [Fintype α] [DecidableEq α] (ξ : K)
    (JA : Matrix α α K) (JB : Matrix β β K) (x₁ x₂ z : Matrix α β K) :
    symp (R := R) c ξ JA (dbl JB) (fromCols x₁ x₂) (fromCols z z) = symp (R := R) c ξ JA JB (x₁ - x₂) z := by
  unfold symp
  congr 2
  unfold hTens
  simp only [dbl, Fintype.sum_sum_type, fromCols_apply_inl, fromCols_apply_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, mul_neg, neg_mul, Finset.sum_neg_distrib, Matrix.sub_apply, sub_mul,
    Finset.sum_sub_distrib]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem pairing_mul {α : Type} [Fintype α] (A : Matrix α α K) (Y : Matrix α β K) (B : Matrix β β K) (P : Matrix α β K) :
    ∑ k, ∑ l, (A * Y * B) k l * P k l = ∑ k, ∑ l, Y k l * (Aᵀ * P * Bᵀ) k l := by
  have e : ∀ M Q : Matrix α β K, ∑ k, ∑ l, M k l * Q k l = Matrix.trace (M * Qᵀ) := by
    intro M Q
    simp [Matrix.trace, Matrix.mul_apply]
  rw [e, e, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    show A * Y * B * Pᵀ = A * (Y * B * Pᵀ) by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, Matrix.transpose_transpose]

theorem exists_factor {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (ι : V →ₗ[ℂ] V')
    (S : Submodule ℂ V) (h : Set.InjOn ι S) (l : V →ₗ[ℂ] ℂ) : ∃ m : V' →ₗ[ℂ] ℂ, ∀ φ ∈ S, m (ι φ) = l φ := by
  obtain ⟨g, hg⟩ := (ι.domRestrict S).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 fun x y e => Subtype.ext (h x.2 y.2 e))
  exact ⟨l ∘ₗ S.subtype ∘ₗ g, fun φ hφ => congrArg (fun x : S => l x) (LinearMap.congr_fun hg ⟨φ, hφ⟩)⟩

end Algebra

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem form_comp_invT [Invertible (2 : k)] (ψ : AddChar k ℂ) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (m : (Matrix α (β ⊕ β) k → ℂ) →ₗ[ℂ] ℂ)
    (htr : ∀ C : Matrix α β k, ∀ f ∈ SB (Matrix α (β ⊕ β) k), m (fun Y => f (Y + fromCols C C)) = m f)
    (hmu : ∀ D : Matrix α β k, ∀ f ∈ SB (Matrix α (β ⊕ β) k),
      m (fun Y => ψ (∑ i, ∑ j, (Y.toCols₁ - Y.toCols₂) i j * D i j) * f Y) = m f)
    (g : GL (β ⊕ β) k) (T : GL β k)
    (h : g.val * (diagCols β : Matrix (β ⊕ β) β k) = (diagCols β : Matrix (β ⊕ β) β k) * T.val)
    {f : Matrix α (β ⊕ β) k → ℂ} (hf : f ∈ SB (Matrix α (β ⊕ β) k)) :
    m (fun Y => f (Y * (GlobalTheory.SplitFlip.invT g).val)) =
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet T) (Fintype.card α : ℂ) * m f := by
  let σ : α × β ≃ α × β := Equiv.refl _
  let e : Matrix α (β ⊕ β) k ≃ₜ (α × β ⊕ α × β → k) :=
    { toEquiv := (flat (dblNum σ)).toEquiv
      continuous_toFun := continuous_pi fun q => (continuous_id (X := Matrix α (β ⊕ β) k)).matrix_elem _ _
      continuous_invFun := continuous_matrix fun i j => continuous_apply ((dblNum σ).symm (i, j)) }
  have he : ∀ X Y : Matrix α β k, e (fromCols X Y) = Sum.elim (flat σ X) (flat σ Y) := flat_fromCols σ
  have s1 : ∀ φ ∈ SB (α × β ⊕ α × β → k), (fun Y => φ (e Y)) ∈ SB (Matrix α (β ⊕ β) k) := fun φ hφ =>
    ⟨hφ.1.comp_continuous e.continuous, hφ.2.comp_homeomorph e⟩
  have s2 : ∀ f ∈ SB (Matrix α (β ⊕ β) k), (fun x => f (e.symm x)) ∈ SB (α × β ⊕ α × β → k) := fun f hf =>
    ⟨hf.1.comp_continuous e.symm.continuous, hf.2.comp_homeomorph e.symm⟩
  let l := m ∘ₗ LinearMap.funLeft ℂ ℂ e
  have hl0 : ∀ f, l (fun x => f (e.symm x)) = m f := fun f =>
    congrArg m (funext fun Y => congrArg f (e.symm_apply_apply Y))
  have hl : ∀ x y : α × β → k, ∀ φ ∈ SB (α × β ⊕ α × β → k),
      l (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = l φ := by
    intro x y φ hφ
    obtain ⟨C, rfl⟩ := (flat σ).surjective x
    obtain ⟨D, rfl⟩ := (flat σ).surjective y
    have s3 : (fun Y => φ (e (Y + fromCols C C))) ∈ SB (Matrix α (β ⊕ β) k) :=
      ⟨(s1 φ hφ).1.comp_continuous (continuous_add_const _), (s1 φ hφ).2.comp_homeomorph (Homeomorph.addRight _)⟩
    refine Eq.trans ?_ ((hmu D _ s3).trans (htr C _ (s1 φ hφ)))
    refine congrArg m (funext fun Y => ?_)
    obtain ⟨Y₁, Y₂, rfl⟩ : ∃ Y₁ Y₂, Y = fromCols Y₁ Y₂ := ⟨_, _, (fromCols_toCols Y).symm⟩
    have ea : e (fromCols Y₁ Y₂ + fromCols C C) = e (fromCols Y₁ Y₂) + e (fromCols C C) := rfl
    show schr ψ _ φ (e _) = _
    rw [ea, he, he, schr]
    congr 2
    simp only [toCols₁_fromCols, toCols₂_fromCols, sumElim_dotProduct_sumElim, dotProduct_neg, add_neg_cancel, mul_zero,
      add_zero, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib, ← sub_eq_add_neg]
    simp only [dotProduct, Fintype.sum_prod_type]
    rfl
  let G : Matrix (α × β) (α × β) k := (1 : Matrix α α k) ⊗ₖ (T⁻¹).val
  have hG : G.det = ((GeneralLinearGroup.det T)⁻¹ ^ Fintype.card α : kˣ) := by
    rw [det_kronecker, det_one, one_pow, one_mul, ← map_inv, Units.val_pow_eq_pow_val]
    rfl
  let g₀ : GL (α × β) k := GeneralLinearGroup.mkOfDetNeZero G (hG ▸ Units.ne_zero _)
  have hg : GeneralLinearGroup.det g₀ = (GeneralLinearGroup.det T)⁻¹ ^ Fintype.card α := Units.ext hG
  have hgx : ∀ X : Matrix α β k, g₀.val.mulVec (flat σ X) = flat σ (X * (T⁻¹).valᵀ) := by
    intro X
    funext q
    show ∑ q', G q q' * X q'.1 q'.2 = (X * (T⁻¹).valᵀ) q.1 q.2
    rw [Fintype.sum_prod_type, mul_apply]
    simp [G, kroneckerMap_apply, one_apply, mul_comm]
  have h1 : (g⁻¹).val * (diagCols β : Matrix (β ⊕ β) β k) = (diagCols β : Matrix (β ⊕ β) β k) * (T⁻¹).val := by
    have := congrArg (fun N => (g⁻¹).val * N * (T⁻¹).val) h
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at this
    rw [this, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  let R : Matrix α (β ⊕ β) k ≃ₜ Matrix α (β ⊕ β) k :=
    { toFun := fun Y => Y * (GlobalTheory.SplitFlip.invT g).val
      invFun := fun Y => Y * ((GlobalTheory.SplitFlip.invT g)⁻¹).val
      left_inv := fun Y => by simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      right_inv := fun Y => by simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      continuous_toFun := continuous_id.matrix_mul continuous_const
      continuous_invFun := continuous_id.matrix_mul continuous_const }
  have hf' : (fun Y => f (Y * (GlobalTheory.SplitFlip.invT g).val)) ∈ SB (Matrix α (β ⊕ β) k) :=
    ⟨hf.1.comp_continuous R.continuous, hf.2.comp_homeomorph R⟩
  have key := diag_invariant_comp ψ hψ hψ1 l hl g₀ (s2 _ hf) (s2 _ hf') (fun x => by
    obtain ⟨X, rfl⟩ := (flat σ).surjective x
    rw [hgx, ← he, ← he, e.symm_apply_apply, e.symm_apply_apply, ← mul_diagCols, ← mul_diagCols,
      GlobalTheory.SplitFlip.invT_val, Matrix.mul_assoc, Matrix.mul_assoc, ← transpose_mul, ← transpose_mul, h1])
  rw [hl0 f, hl0 (fun Y => f (Y * (GlobalTheory.SplitFlip.invT g).val)), hg] at key
  rw [← key, ← mul_assoc, GlobalTheory.SplitFlip.apow, Complex.cpow_natCast, GlobalTheory.SplitWeil.nabs]
  have hpos : (0 : ℝ) < distribHaarChar k (GeneralLinearGroup.det T) := distribHaarChar_pos (A := k)
  have hne : ((distribHaarChar k (GeneralLinearGroup.det T) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  simp only [map_pow, map_inv, NNReal.coe_pow, NNReal.coe_inv, Complex.ofReal_pow, Complex.ofReal_inv]
  rw [← mul_pow, mul_inv_cancel₀ hne, one_pow, one_mul]

end Local

section Adelic

open GlobalTheory.SplitGLLift GlobalTheory.SplitIdele GlobalTheory.DblScal
open GlobalTheory.Div.CoordOpp (piW_cA incM_map_piW)
open scoped GlobalTheory.VacAny

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}

theorem exists_rest_ne (κ : Type) [Fintype κ] (v : Pl F) :
    ∃ R : (κ ⊕ κ → AF F) → ℂ, (∀ φ ∈ SB (κ ⊕ κ → Fv F v), Rest (evFin F v) φ R) ∧
      ∃ φ ∈ SB (κ ⊕ κ → Fv F v), GlobalTheory.DiagForm.lDiag F κ (tens (evFin F v) φ R) ≠ 0 := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨Φ, hΦ, h0⟩ := GlobalTheory.DiagForm.exists_lDiag_ne (F := F) (κ := κ)
  rw [GlobalTheory.WeylSpan.schA_eq_span_pure] at hΦ
  refine h0 ((Submodule.span_le (p := LinearMap.ker (GlobalTheory.DiagForm.lDiag F κ))).2 ?_ hΦ)
  rintro _ ⟨f, φs, h1, h2, rfl⟩
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φs h2
  have := hne r (fun φ hφ => ⟨hr, ?_⟩) (φs v) (h1 v)
  · rwa [hrt, Function.update_eq_self] at this
  · rw [hrt φ]
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually φs v φ h2)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact h1 w

theorem exists_lift (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {α β : Type} (P₀ P₁ : Matrix α β (Fv F v)) :
    ∃ u : Matrix α β (AE F E), At (evFin F v) u ∧ u.map (piW t) = P₀ ∧ u.map (piW (t.comp σ)) = P₁ :=
  ⟨of fun i j => liftPair h t (P₀ i j, P₁ i j), fun a ha => Matrix.ext fun _ _ => at_liftPair h t _ a ha,
    Matrix.ext fun _ _ => piW_liftPair h t _, Matrix.ext fun _ _ => piW_comp_liftPair h t _⟩

omit [NumberField E] in

theorem at_det {β : Type} [Fintype β] [DecidableEq β] {N : Matrix β β (AE F E)} (h : At (evFin F v) (N - 1)) :
    At (evFin F v) (N.det - 1) := by
  intro a ha
  let I : Ideal (AE F E) := LinearMap.ker (LinearMap.lsmul (AE F E) (AE F E) (algebraMap (AF F) (AE F E) a))
  have hI : ∀ z, z ∈ I ↔ a • z = 0 := fun z => by
    rw [Algebra.smul_def]; rfl
  have e : (Ideal.Quotient.mk I).mapMatrix N = (Ideal.Quotient.mk I).mapMatrix 1 :=
    Matrix.ext fun i j => Ideal.Quotient.eq.2 ((hI _).2 (congrFun (congrFun (h a ha) i) j))
  rw [← hI, ← Ideal.Quotient.eq, RingHom.map_det, e, map_one, det_one, map_one]

theorem exists_siegel (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
    (hJ : IsUnit (J.map t).det) (c : GL (Fin d) (Fv F v)) {p : UD σ J} (hp : p ∈ UDAt σ J (evFin F v))
    {T : Matrix (Fin d) (Fin d) (Fv F v)}
    (hT : (locMatD t c p).val * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) * T) :
    ∃ (T₀ : GL (Fin d) (Fv F v)) (y : (Fv F v)ˣ) (N : GL (Fin d) (AE F E)), T₀.val = T ∧
      (p : GL (Fin d ⊕ Fin d) (AE F E)).val * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
        (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * N.val ∧
      GeneralLinearGroup.det N = idl h t (GlobalTheory.SplitFlip.gdet T₀, y⁻¹) ∧
      GlobalTheory.SplitFlip.gdet (locMatD t c p) = GlobalTheory.SplitFlip.gdet T₀ * y := by
  set P := (p : GL (Fin d ⊕ Fin d) (AE F E)).val with hP
  have hPu : IsUnit P.det := Matrix.isUnits_det_units _
  have hc : (dsum c).val * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) = (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) * c.val := by
    simp [dsum, diagCols, fromBlocks_mul_fromRows, fromRows_mul]
  have hl : (locMatD t c p).val = ((dsum c)⁻¹).val * P.map (piW t) * (dsum c).val := rfl
  have h1 : P.map (piW t) * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) * (c.val * T * (c⁻¹).val) := by
    have := congrArg (fun Z => (dsum c).val * Z * (c⁻¹).val) hT
    simp only [hl, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, hc] at this
    rw [Matrix.mul_assoc (P.map _), hc, Matrix.mul_assoc, Matrix.mul_assoc _ c.val, Units.mul_inv, Matrix.mul_one] at this
    simpa only [Matrix.mul_assoc] using this
  have hU : (P.map (piW t))ᵀ * fromBlocks (J.map t) 0 0 (-J.map t) * P.map (piW (t.comp σ)) =
      fromBlocks (J.map t) 0 0 (-J.map t) := by
    have := congrArg (fun M => M.map (piW t)) (show Pᵀ * dbl (incM F J) * P.map (cA σ) = dbl (incM F J) from p.2)
    have e1 : (dbl (incM F J)).map (piW t) = fromBlocks (J.map t) 0 0 (-J.map t) := by
      rw [← incM_map_piW]
      ext (i | i) (j | j) <;> simp [dbl]
    have e2 : (P.map (cA σ)).map (piW t) = P.map (piW (t.comp σ)) := Matrix.ext fun i j => piW_cA σ t _
    simpa only [Matrix.map_mul, Matrix.transpose_map, e1, e2] using this
  have hd : ∀ τ : E →ₐ[F] Fv F v, ∀ {β : Type} [Fintype β] [DecidableEq β] (Z : Matrix β β (AE F E)),
      (Z.map (piW τ)).det = piW τ Z.det := fun τ _ _ _ Z => (RingHom.map_det _ _).symm
  obtain ⟨T', h2, h3⟩ := adj_diag hJ (hd t P ▸ hPu.map _) hU h1
  obtain ⟨u, hu, hu1, hu2⟩ := exists_lift h t (c.val * T * (c⁻¹).val - 1) (T' - 1)
  have m1 : (1 + u).map (piW t) = c.val * T * (c⁻¹).val := by
    rw [Matrix.map_add _ (map_add _), hu1, Matrix.map_one _ (map_zero _) (map_one _), add_sub_cancel]
  have m2 : (1 + u).map (piW (t.comp σ)) = T' := by
    rw [Matrix.map_add _ (map_add _), hu2, Matrix.map_one _ (map_zero _) (map_one _), add_sub_cancel]
  have hu' : At (evFin F v) (1 + u - 1) := by rwa [add_sub_cancel_left]
  have hΔ : ∀ τ : E →ₐ[F] Fv F v, (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E).map τ = diagCols (Fin d) :=
    fun τ => diagCols_map (τ : E →+* Fv F v)
  have hN := adelic_intertwine h t (g := P) (P := (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E)) hp hu'
    (by rw [m1, hΔ]; exact h1) (by rw [m2, hΔ]; exact h2)
  rw [show incM F (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E) = diagCols (Fin d) from
    diagCols_map (inclR (F := F) (E := E) (AF F) : E →+* AE F E)] at hN
  have hNu : IsUnit (1 + u).det := by
    have := hN
    rw [← fromBlocks_toBlocks P] at this
    have e := det_of_diag this
    rw [fromBlocks_toBlocks] at e
    exact isUnit_of_mul_isUnit_left (e ▸ hPu)
  have dT : (c.val * T * (c⁻¹).val).det = T.det := det_units_conj c T
  have hTu : IsUnit T.det := by rw [← dT, ← m1, hd]; exact hNu.map _
  have hT'u : IsUnit T'.det := by rw [← m2, hd]; exact hNu.map _
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).2 hTu).unit, hT'u.unit⁻¹, ((Matrix.isUnit_iff_isUnit_det _).2 hNu).unit, rfl, hN,
    Units.ext ?_, ?_⟩
  · rw [inv_inv, ← sub_eq_zero]
    refine eq_zero_of_at h t (fun a ha => ?_) ?_ ?_
    · rw [← sub_sub_sub_cancel_right _ _ 1, smul_sub, at_idl h t _ _ a ha, sub_zero]
      exact at_det hu' a ha
    · rw [map_sub, piW_idl, sub_eq_zero]
      exact (hd t (1 + u)).symm.trans (by rw [m1, dT]; rfl)
    · rw [map_sub, piW_comp_idl, sub_eq_zero]
      exact (hd (t.comp σ) (1 + u)).symm.trans (by rw [m2]; rfl)
  · refine eq_mul_inv_of_mul_eq (Units.ext ?_)
    show (locMatD t c p).val.det * T'.det = T.det
    rw [hl, det_units_conj', h3, dT]

theorem psi_symp (h : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (t : E →ₐ[F] Fv F v) {n d : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {K : Matrix (Fin d) (Fin d) E} (hJ : ∀ i j, σ (J j i) = J i j) (hK : ∀ i j, σ (K j i) = -K i j)
    {x z : Matrix (Fin n) (Fin d) (AE F E)} (hx : At (evFin F v) x) (hz : z.map (piW t) = 0) :
    ψ (symp (cA σ) (-1) (incM F J) (incM F K) x z) = GlobalTheory.LatVac.psiAt ψ v
      (∑ i, ∑ j, (x.map (piW t)) i j * (-(J.map t * z.map (piW (t.comp σ)) * (K.map t)ᵀ)) i j) := by
  have hA : At (evFin F v) (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F K) x z) := by
    intro a ha
    have h0 : ∀ i j, a • x i j = 0 := fun i j => congrFun (congrFun (hx a ha) i) j
    rw [symp, ← map_smul, ← mul_smul_comm, hTens]
    simp only [Finset.smul_sum, ← smul_mul_assoc, h0, zero_mul, Finset.sum_const_zero, mul_zero, map_zero]
  rw [GlobalTheory.VacAny.eq_atPlace_of_at v _ hA]
  show GlobalTheory.LatVac.psiAt ψ v (evFin F v _) = _
  rw [GlobalTheory.LinCoords.splitTrace' h v t J K hJ hK x z hx, hz]
  simp

end Adelic

open GlobalTheory.DblScal GlobalTheory.SplitIdele
open scoped GlobalTheory.VacAny

theorem scalar_siegel : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
      (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (dbl (incM F W.J)) dd χX (diagCols (Fin d)) omd →
      GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd → ∀ cd, GlobalTheory.DblScal.IsShapeD omd t c ιd cd →
      ∀ p ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v),
        (∃ T : Matrix (Fin d) (Fin d) (Fv F v),
          ((GlobalTheory.DblScal.locMatD t c p).val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (Fv F v)) *
            (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) =
            (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) * T) →
        cd p = (chrW χX t (GlobalTheory.SplitFlip.gdet (GlobalTheory.DblScal.locMatD t c p)) : ℂ) *
          GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (GlobalTheory.DblScal.locMatD t c p)) (-(n : ℂ) / 2) := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v t b c dd omd hdd hW hloc ιd hι cd hcd p hp ⟨T, hT⟩
  have hcm : IsCMExt F E σ := hP.base.cm
  have hstd := hP.base.std
  have hX : IsUnit (X.J.map t).det :=
    isUnit_iff_ne_zero.2 (GlobalTheory.SplitIdele.det_map_ne_zero (GlobalTheory.SplitIdele.det_ne_zero_herm hP.herm) t)
  have hK : IsUnit (W.J.map t).det :=
    isUnit_iff_ne_zero.2 (GlobalTheory.SplitIdele.det_map_ne_zero (GlobalTheory.SplitIdele.det_ne_zero_skew hP.skew) t)
  obtain ⟨R, hR, φ₀, hφ₀, h0⟩ := exists_rest_ne (Fin n × Fin d) v
  let lam : ((Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ := GlobalTheory.DiagForm.lDiag F (Fin n × Fin d) ∘ₗ
    { toFun := fun φ => tens (evFin F v) φ R
      map_add' := fun _ _ => funext fun _ => add_mul _ _ _
      map_smul' := fun _ _ => funext fun _ => mul_assoc _ _ _ }
  have hlam : ∀ φ, lam φ = GlobalTheory.DiagForm.lDiag F (Fin n × Fin d) (tens (evFin F v) φ R) := fun _ => rfl
  obtain ⟨m, hm⟩ := exists_factor ιd _ hι.bij.injOn lam
  have hinv : ∀ z : Matrix (Fin n) (Fin d) (AE F E), ∀ Φ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d),
      GlobalTheory.DiagForm.lDiag F _ (dd.rho B.ψ (fromCols z z) Φ) = GlobalTheory.DiagForm.lDiag F _ Φ := fun z Φ hΦ => by
    rw [Darboux.rho, hdd z z, GlobalTheory.DiagForm.lDiag_schr B.ψ _ _ hΦ]
  have hat : ∀ z : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) z → At (evFin F v) (fromCols z z) := fun z hz a ha => by
    ext i (j | j) <;> exact congrFun (congrFun (hz a ha) i) j
  have hrho : ∀ z : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) z → ∀ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v),
      ∃ φ₁ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), Acts (evFin F v) (dd.rho B.ψ (fromCols z z)) φ φ₁ ∧
        m (ιd φ₁) = m (ιd φ) := fun z hz φ hφ => by
    have h1 := GlobalTheory.SchrSB.schr_mem_SB B.ψ hstd.1 v (GlobalTheory.LatVac.locCo dd v (fromCols z z)) φ hφ
    have h2 := GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v _ (hat z hz) φ
    refine ⟨_, h1, h2, ?_⟩
    rw [hm _ h1, hm _ hφ, hlam, hlam, ← h2 R (hR φ hφ), hinv z _ (hR φ hφ).2]
  have hco : ∀ Y₁ Y₂ : Matrix (Fin n) (Fin d) (Fv F v),
      (b⁻¹).val * fromCols (b.val * Y₁ * c.valᵀ) (b.val * Y₂ * c.valᵀ) * ((dsum c)⁻¹).valᵀ = fromCols Y₁ Y₂ := by
    intro Y₁ Y₂
    have e : ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), (b⁻¹).val * (b.val * Y * c.valᵀ) * (c⁻¹).valᵀ = Y := fun Y => by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, ← transpose_mul,
        Units.inv_mul, transpose_one, Matrix.mul_one]
    rw [show ((dsum c)⁻¹).val = fromBlocks (c⁻¹).val 0 0 (c⁻¹).val from rfl, mul_fromCols, fromBlocks_transpose, fromCols_mul_fromBlocks, transpose_zero, Matrix.mul_zero, Matrix.mul_zero,
      add_zero, zero_add, e, e]
  have htr : ∀ C : Matrix (Fin n) (Fin d) (Fv F v), ∀ f ∈ SB (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)),
      m (fun Y => f (Y + fromCols C C)) = m f := by
    intro C f hf
    obtain ⟨φ, hφ, rfl⟩ := hι.bij.surjOn hf
    obtain ⟨z, hz, z1, z2⟩ := exists_lift hcm t (b.val * C * c.valᵀ) 0
    obtain ⟨φ₁, hφ₁, ha, e⟩ := hrho z hz φ hφ
    rw [← e]
    refine congrArg m (funext fun Y => ?_)
    rw [hι.trans _ (hat z hz) (by rw [fromCols_map, z2, fromCols_zero]) φ hφ φ₁ hφ₁ ha Y, fromCols_map, z1, hco]
  have hmu : ∀ D : Matrix (Fin n) (Fin d) (Fv F v), ∀ f ∈ SB (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)),
      m (fun Y => GlobalTheory.LatVac.psiAt B.ψ v (∑ i, ∑ j, (Y.toCols₁ - Y.toCols₂) i j * D i j) * f Y) = m f := by
    intro D f hf
    obtain ⟨φ, hφ, rfl⟩ := hι.bij.surjOn hf
    obtain ⟨z, hz, z1, z2⟩ := exists_lift hcm t 0
      (-((X.J.map t)⁻¹ * ((b⁻¹).valᵀ * D * (c⁻¹).val) * ((W.J.map t)⁻¹)ᵀ))
    obtain ⟨φ₁, hφ₁, ha, e⟩ := hrho z hz φ hφ
    rw [← e]
    refine congrArg m (funext fun Y => ?_)
    obtain ⟨Y₁, Y₂, rfl⟩ : ∃ Y₁ Y₂, Y = fromCols Y₁ Y₂ := ⟨_, _, (fromCols_toCols Y).symm⟩
    obtain ⟨x₁, hx₁, a1, a2⟩ := exists_lift hcm t (b.val * Y₁ * c.valᵀ) 0
    obtain ⟨x₂, hx₂, b1, b2⟩ := exists_lift hcm t (b.val * Y₂ * c.valᵀ) 0
    have hx : At (evFin F v) (fromCols x₁ x₂) := fun a ha => by
      ext i (j | j)
      exacts [congrFun (congrFun (hx₁ a ha) i) j, congrFun (congrFun (hx₂ a ha) i) j]
    have key := hι.mult _ (hat z hz) (by rw [fromCols_map, z1, fromCols_zero]) φ hφ φ₁ hφ₁ ha _ hx
      (by rw [fromCols_map, a2, b2, fromCols_zero])
    rw [fromCols_map, a1, b1, hco, symp_dbl_diag, psi_symp hcm B.ψ t hP.herm.herm hP.skew.skew
      (fun a ha => by rw [smul_sub, hx₁ a ha, hx₂ a ha, sub_zero]) z1, Matrix.map_sub _ (map_sub _), a1, b1, z2,
      ← Matrix.sub_mul, ← Matrix.mul_sub, pairing_mul] at key
    rw [key, toCols₁_fromCols, toCols₂_fromCols]
    have e2 : b.valᵀ * -(X.J.map t * -((X.J.map t)⁻¹ * ((b⁻¹).valᵀ * D * (c⁻¹).val) * ((W.J.map t)⁻¹)ᵀ) * (W.J.map t)ᵀ) *
        c.valᵀᵀ = D := by
      rw [Matrix.mul_neg (X.J.map t), Matrix.neg_mul, neg_neg, transpose_transpose, ← Matrix.mul_assoc (X.J.map t),
        ← Matrix.mul_assoc (X.J.map t), Matrix.mul_nonsing_inv _ hX, Matrix.one_mul, Matrix.mul_assoc _ _ (W.J.map t)ᵀ,
        ← transpose_mul, Matrix.mul_nonsing_inv _ hK, transpose_one, Matrix.mul_one, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, ← transpose_mul, Units.inv_mul, transpose_one, Matrix.one_mul, Matrix.mul_assoc,
        Units.inv_mul, Matrix.mul_one]
    rw [e2]
  obtain ⟨T₀, y, N, rfl, hN, hdet, hp'⟩ := exists_siegel hcm t hK c hp hT
  obtain ⟨φ₁, hφ₁, ha⟩ := hloc p hp φ₀ hφ₀
  have k1 := hW.2.2 _ GlobalTheory.DiagForm.lDiag_adm (fun z Φ hΦ => by rw [mul_diagCols]; exact hinv z Φ hΦ) p N hN _
    (hR φ₀ hφ₀).2
  rw [ha R (hR φ₀ hφ₀), GlobalTheory.ModuNorm.modu_norm_eq_absE F E hcm.1, hdet, Fintype.card_fin,
    char_idl hcm χX hP.resX, ← hlam, ← hlam, ← hm _ hφ₁, hcd p hp φ₀ hφ₀ φ₁ hφ₁ ha, map_smul,
    form_comp_invT _ (GlobalTheory.SchrSB.continuous_psiAt _ hstd.1 v) (GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd v) m htr hmu _ T₀ hT
      (hι.bij.mapsTo hφ₀), hm _ hφ₀, Fintype.card_fin, smul_eq_mul, ← mul_assoc] at k1
  have k2 := mul_right_cancel₀ h0 k1
  refine mul_right_cancel₀ (GlobalTheory.SplitFlip.apow_ne_zero (GlobalTheory.SplitFlip.gdet T₀) (n : ℂ)) ?_
  have k3 := GlobalTheory.SplitFlip.apow_add (GlobalTheory.SplitFlip.gdet T₀) (-(n : ℂ) / 2) n
  rw [show -(n : ℂ) / 2 + n = n / 2 by ring] at k3
  rw [k2, hp', map_mul, Units.val_mul, GlobalTheory.SplitFlip.apow_mul, k3]
  ring

end GlobalTheory.DblSiegelScal

end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_scaling_local_vanishing : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
      (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (dbl (incM F W.J)) dd χX (diagCols (Fin d)) omd →
      GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd → ∀ cd, GlobalTheory.DblScal.IsShapeD omd t c ιd cd →
      ∀ p ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v),
        (∃ T : Matrix (Fin d) (Fin d) (Fv F v),
          ((GlobalTheory.DblScal.locMatD t c p).val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (Fv F v)) *
            (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) =
            (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (Fv F v)) * T) →
        cd p = (chrW χX t (GlobalTheory.SplitFlip.gdet (GlobalTheory.DblScal.locMatD t c p)) : ℂ) *
          GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (GlobalTheory.DblScal.locMatD t c p)) (-(n : ℂ) / 2) := by
  atlas_forward_decl GlobalTheory.DblSiegelScal.scalar_siegel
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblScalBox

open Matrix

section Local

variable {F : Type} [Field F] [NumberField F]

theorem box_mem_SB {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem conj_mem_SB {Y : Type} [TopologicalSpace Y] {φ : Y → ℂ} (h : φ ∈ SB Y) :
    (fun y => starRingEnd ℂ (φ y)) ∈ SB Y :=
  ⟨h.1.comp _, h.2.comp_left (map_zero _)⟩

theorem tens_box (v : Pl F) {κ κ' : Type} (φ₁ : (κ → Fv F v) → ℂ) (φ₂ : (κ' → Fv F v) → ℂ)
    (r₁ : (κ → AF F) → ℂ) (r₂ : (κ' → AF F) → ℂ) :
    tens (evFin F v) (boxFun φ₁ φ₂) (boxFun r₁ r₂) = boxFun (tens (evFin F v) φ₁ r₁) (tens (evFin F v) φ₂ r₂) := by
  funext x
  simp only [tens, boxFun, Function.comp_def]
  ring

theorem rest_box (v : Pl F) {κ κ' : Type} [Fintype κ] [Fintype κ'] {φ₁ : (κ → Fv F v) → ℂ} {φ₂ : (κ' → Fv F v) → ℂ}
    {r₁ : (κ → AF F) → ℂ} {r₂ : (κ' → AF F) → ℂ} (h₁ : Rest (evFin F v) φ₁ r₁) (h₂ : Rest (evFin F v) φ₂ r₂) :
    Rest (evFin F v) (boxFun φ₁ φ₂) (boxFun r₁ r₂) := by
  refine ⟨fun x z hz => ?_, ?_⟩
  · have hz1 : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by
      funext i; exact congrFun (hz u hu) (Sum.inl i)
    have hz2 : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by
      funext i; exact congrFun (hz u hu) (Sum.inr i)
    show r₁ ((x + z) ∘ Sum.inl) * r₂ ((x + z) ∘ Sum.inr) = r₁ (x ∘ Sum.inl) * r₂ (x ∘ Sum.inr)
    rw [show (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl from rfl,
      show (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr from rfl, h₁.1 _ _ hz1, h₂.1 _ _ hz2]
  · rw [tens_box]
    exact GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ _ h₁.2 _ h₂.2

theorem eq_of_tens_ne (v : Pl F) {κ : Type} {ψ₁ ψ₂ : (κ → Fv F v) → ℂ} {r : (κ → AF F) → ℂ}
    (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) {x₀ : κ → AF F} (h0 : r x₀ ≠ 0)
    (h : tens (evFin F v) ψ₁ r = tens (evFin F v) ψ₂ r) : ψ₁ = ψ₂ := by
  funext y
  let z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x₀ i))
  have hz : At (evFin F v) z := by
    intro u hu; funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hev : (fun i => evFin F v ((x₀ + z) i)) = y := by
    funext i
    simp only [Pi.add_apply, z, map_add, GlobalTheory.LatVac.evFin_liftV]
    abel
  have e := congrFun h (x₀ + z)
  simp only [tens, hev, hr x₀ z hz] at e
  exact mul_right_cancel₀ h0 e

end Local

theorem scal_diag_one : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ κ : UA σ W.J → ℂ, (∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = κ h • fun Y => ι φ (Y * (GlobalTheory.SplitFlip.invT (locMat t c h)).val)) →
    ∀ (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd →
      (∀ (g : UA σ W.J) (gd : GlobalTheory.DblScal.UD σ W.J),
        ((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
          Matrix.fromBlocks (mat g) 0 0 1 →
        ∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d), omd gd (boxFun φ₁ φ₂) = boxFun (om (1, g) φ₁) φ₂) →
      GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd →
      (∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₂ ∈ SB (Fin n × Fin d → Fv F v),
        ιd (boxFun φ₁ φ₂) = fun Y => ι φ₁ (Y.submatrix id Sum.inl) *
          starRingEnd ℂ (ι (fun x => starRingEnd ℂ (φ₂ x)) (Y.submatrix id Sum.inr))) →
      ∀ cd, GlobalTheory.DblScal.IsShapeD omd t c ιd cd →
      ∀ h ∈ UAt σ W (evFin F v), ∀ gd : GlobalTheory.DblScal.UD σ W.J,
        ((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
          Matrix.fromBlocks (mat h) 0 0 1 → κ h = cd gd := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair v t b c ι hι κ hκ dd omd hdd hspl hres hloc ιd hιd hbox cd
    hcd h hh gd hgd
  have hιL : M.IsLin B.ψ (piW t) (piW (t.comp σ)) (fun u => (b⁻¹).1 * u.map (piW t) * (c⁻¹).1ᵀ) ι := hι

  set φ₀ : (Fin n × Fin d → Fv F v) → ℂ := Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 with hφ₀def
  have h0 : φ₀ ∈ SB (Fin n × Fin d → Fv F v) := GlobalTheory.StdVacuum.indicator_mem_SB v
  have hφ₀0 : φ₀ (fun _ => 0) = 1 := by
    rw [hφ₀def, Set.indicator_of_mem (show (fun _ => (0 : Fv F v)) ∈
      {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun i => zero_mem _)]
    rfl
  have hne : ι φ₀ ≠ 0 := by
    intro e
    have e0 : φ₀ = 0 := hιL.bij.injOn h0 (SB _).zero_mem (by rw [e, map_zero])
    have e1 := congrFun e0 (fun _ => 0)
    rw [hφ₀0] at e1
    exact one_ne_zero e1
  obtain ⟨Y₀, hY₀⟩ : ∃ Y, ι φ₀ Y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne (funext hc)
  set φ₂ : (Fin n × Fin d → Fv F v) → ℂ := fun x => starRingEnd ℂ (φ₀ x) with hφ₂def
  have h2 : φ₂ ∈ SB (Fin n × Fin d → Fv F v) := conj_mem_SB h0
  have hcc : (fun x => starRingEnd ℂ (φ₂ x)) = φ₀ := funext fun x => Complex.conj_conj _

  have h1mem : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := by
    intro u _
    have e : mat (1 : UA σ X.J) = 1 := rfl
    rw [e, sub_self, smul_zero]
  obtain ⟨φ₁, ⟨h1, hA1⟩, -⟩ := (GlobalTheory.T.theta_action_exists hP F E σ B n d X W M χX χW om r s r' s' hPair v).1 1 h1mem h hh φ₀ h0
  have hk := hκ h hh φ₀ h0 φ₁ h1 hA1

  have hgdAt : gd ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v) := by
    intro u hu
    rw [hgd, GlobalTheory.DblScal.fromBlocks_sub_one, Matrix.fromBlocks_smul, hh u hu]
    simp
  obtain ⟨Φ₁, hΦ₁, hAd⟩ := hloc gd hgdAt (boxFun φ₀ φ₂) (box_mem_SB h0 h2)
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) (Fin n × Fin d) v
  have hRb := rest_box v (hR φ₀ h0) (hR φ₂ h2)
  have e := hAd _ hRb
  rw [tens_box, hres h gd hgd _ (hR φ₀ h0).2 _ (hR φ₂ h2).2, hA1 R (hR φ₀ h0), ← tens_box] at e
  have h0r : boxFun R R (0 : Fin n × Fin d ⊕ Fin n × Fin d → AF F) ≠ 0 := by
    show R 0 * R 0 ≠ 0
    exact mul_ne_zero hR0 hR0
  have eΦ : Φ₁ = boxFun φ₁ φ₂ := eq_of_tens_ne v hRb.1 h0r e.symm

  have hs := hcd gd hgdAt (boxFun φ₀ φ₂) (box_mem_SB h0 h2) Φ₁ hΦ₁ hAd
  rw [eΦ] at hs
  set L := locMat t c h with hL
  have hD : (GlobalTheory.DblScal.locMatD t c gd).val = Matrix.fromBlocks L.val 0 0 1 := by
    show ((GlobalTheory.DblScal.dsum c)⁻¹).val * (((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix _ _ _).map (piW t)) *
      (GlobalTheory.DblScal.dsum c).val = _
    rw [hgd, hL, locMat_val, fromBlocks_map]
    simp only [GlobalTheory.DblScal.dsum, Units.inv_mk, fromBlocks_multiply, Matrix.map_zero _ (map_zero (piW t)),
      Matrix.map_one _ (map_zero (piW t)) (map_one (piW t)), Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      Matrix.mul_one, Matrix.one_mul]
    congr 1
    simp [Units.mul_inv]
  have hDinv : ((GlobalTheory.DblScal.locMatD t c gd)⁻¹).val = Matrix.fromBlocks (L⁻¹).val 0 0 1 := by
    have hm : Matrix.fromBlocks (L⁻¹).val 0 0 1 * (GlobalTheory.DblScal.locMatD t c gd).val = 1 := by
      rw [hD, fromBlocks_multiply]
      simp [← fromBlocks_one]
    calc ((GlobalTheory.DblScal.locMatD t c gd)⁻¹).val
        = (Matrix.fromBlocks (L⁻¹).val 0 0 1 * (GlobalTheory.DblScal.locMatD t c gd).val) *
            ((GlobalTheory.DblScal.locMatD t c gd)⁻¹).val := by rw [hm, Matrix.one_mul]
      _ = Matrix.fromBlocks (L⁻¹).val 0 0 1 := by
          rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hT : (GlobalTheory.SplitFlip.invT (GlobalTheory.DblScal.locMatD t c gd)).val =
      Matrix.fromBlocks (GlobalTheory.SplitFlip.invT L).val 0 0 1 := by
    rw [GlobalTheory.SplitFlip.invT_val, GlobalTheory.SplitFlip.invT_val, hDinv, fromBlocks_transpose]
    simp
  have hY : Y₀ * L.valᵀ * (GlobalTheory.SplitFlip.invT L).val = Y₀ := by
    rw [GlobalTheory.SplitFlip.invT_val, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
      Matrix.mul_one]
  have hsl : ∀ A Bm : Matrix (Fin n) (Fin d) (Fv F v), (Matrix.fromCols A Bm).submatrix id Sum.inl = A := by
    intro A Bm; ext i j; rfl
  have hsr : ∀ A Bm : Matrix (Fin n) (Fin d) (Fv F v), (Matrix.fromCols A Bm).submatrix id Sum.inr = Bm := by
    intro A Bm; ext i j; rfl
  have hmul : Matrix.fromCols (Y₀ * L.valᵀ) Y₀ * (GlobalTheory.SplitFlip.invT (GlobalTheory.DblScal.locMatD t c gd)).val =
      Matrix.fromCols Y₀ Y₀ := by
    rw [hT, Matrix.fromCols_mul_fromBlocks]
    simp [hY]
  have eY := congrFun hs (Matrix.fromCols (Y₀ * L.valᵀ) Y₀)
  rw [hbox φ₁ h1 φ₂ h2, Pi.smul_apply, smul_eq_mul, hmul, hbox φ₀ h0 φ₂ h2] at eY
  simp only [hsl, hsr, hcc, hk, Pi.smul_apply, smul_eq_mul, hY] at eY
  have hP0 : ι φ₀ Y₀ * starRingEnd ℂ (ι φ₀ Y₀) ≠ 0 := mul_ne_zero hY₀ ((map_ne_zero _).mpr hY₀)
  apply mul_right_cancel₀ hP0
  linear_combination eY

end GlobalTheory.DblScalBox

end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_model_compact_equivariance : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ κ : UA σ W.J → ℂ, (∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = κ h • fun Y => ι φ (Y * (GlobalTheory.SplitFlip.invT (locMat t c h)).val)) →
    ∀ (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd →
      (∀ (g : UA σ W.J) (gd : GlobalTheory.DblScal.UD σ W.J),
        ((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
          Matrix.fromBlocks (mat g) 0 0 1 →
        ∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d), omd gd (boxFun φ₁ φ₂) = boxFun (om (1, g) φ₁) φ₂) →
      GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd →
      (∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₂ ∈ SB (Fin n × Fin d → Fv F v),
        ιd (boxFun φ₁ φ₂) = fun Y => ι φ₁ (Y.submatrix id Sum.inl) *
          starRingEnd ℂ (ι (fun x => starRingEnd ℂ (φ₂ x)) (Y.submatrix id Sum.inr))) →
      ∀ cd, GlobalTheory.DblScal.IsShapeD omd t c ιd cd →
      ∀ h ∈ UAt σ W (evFin F v), ∀ gd : GlobalTheory.DblScal.UD σ W.J,
        ((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
          Matrix.fromBlocks (mat h) 0 0 1 → κ h = cd gd := by
  atlas_forward_decl GlobalTheory.DblScalBox.scal_diag_one
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.DblSurj

open Matrix GlobalTheory.EmbChart

section Lift

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))
  {ι : Type} [Fintype ι] [DecidableEq ι]

def ext0 (M : Matrix ι ι (Fv F v ⊗[F] E)) : Matrix ι ι (AE F E) := M.map (tensAt E v)

theorem matrixExtendByZero_add (M N : Matrix ι ι (Fv F v ⊗[F] E)) : ext0 v (M + N) = ext0 v M + ext0 v N := by
  ext i j; simp [ext0]

theorem matrixExtendByZero_zero : ext0 v (0 : Matrix ι ι (Fv F v ⊗[F] E)) = 0 := by
  ext i j; simp [ext0]

theorem ext_zero_mul_right (M : Matrix ι ι (Fv F v ⊗[F] E)) (C : Matrix ι ι (AE F E)) :
    ext0 v M * C = ext0 v (M * C.map (compFin F E v)) := by
  ext i j
  simp only [ext0, Matrix.mul_apply, Matrix.map_apply, map_sum, tensAt_mul_right]

theorem ext_zero_mul_left (M : Matrix ι ι (Fv F v ⊗[F] E)) (C : Matrix ι ι (AE F E)) :
    C * ext0 v M = ext0 v (C.map (compFin F E v) * M) := by
  ext i j
  simp only [ext0, Matrix.mul_apply, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, tensAt_mul_right, mul_comm]

theorem matrixExtendByZero_mul (M N : Matrix ι ι (Fv F v ⊗[F] E)) : ext0 v M * ext0 v N = ext0 v (M * N) := by
  rw [ext_zero_mul_right]
  congr 2
  ext i j
  exact compFin_tensAt v _

theorem ext_zero_transpose (M : Matrix ι ι (Fv F v ⊗[F] E)) : (ext0 v M)ᵀ = ext0 v Mᵀ := rfl

theorem ext_zero_map_conj (σ : E →ₐ[F] E) (M : Matrix ι ι (Fv F v ⊗[F] E)) :
    (ext0 v M).map (cA σ) = ext0 v (M.map (sigR (Fv F v) σ)) := by
  ext i j
  exact sigR_tensAt v σ _

theorem ext_zero_comp_finite (M : Matrix ι ι (Fv F v ⊗[F] E)) : (ext0 v M).map (compFin F E v) = M := by
  ext i j
  exact compFin_tensAt v _

def lift (Y : Matrix ι ι (Fv F v ⊗[F] E)) : Matrix ι ι (AE F E) := 1 + ext0 v (Y - 1)

theorem lift_mul (Y Z : Matrix ι ι (Fv F v ⊗[F] E)) : lift v Y * lift v Z = lift v (Y * Z) := by
  have e : Y * Z - 1 = (Y - 1) + (Z - 1) + (Y - 1) * (Z - 1) := by noncomm_ring
  rw [lift, lift, lift, e, matrixExtendByZero_add, matrixExtendByZero_add, ← matrixExtendByZero_mul]
  noncomm_ring

theorem lift_one : lift v (1 : Matrix ι ι (Fv F v ⊗[F] E)) = 1 := by
  rw [lift, sub_self, matrixExtendByZero_zero, add_zero]

theorem compFin_lift (Y : Matrix ι ι (Fv F v ⊗[F] E)) : (lift v Y).map (compFin F E v) = Y := by
  have h2 : (1 : Matrix ι ι (AE F E)).map (compFin F E v) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1 : (lift v Y).map (compFin F E v) = (1 : Matrix ι ι (AE F E)).map (compFin F E v) +
      (ext0 v (Y - 1)).map (compFin F E v) := by
    ext i j; simp only [lift, Matrix.map_apply, Matrix.add_apply, map_add]
  rw [h1, ext_zero_comp_finite, h2]
  abel

theorem lift_sub_one_at (Y : Matrix ι ι (Fv F v ⊗[F] E)) : At (evFin F v) (lift v Y - 1) := by
  intro u hu
  rw [lift, add_sub_cancel_left]
  ext i j
  simp only [ext0, Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply]
  rw [Algebra.smul_def, mul_comm, tensAt_mul_right]
  have : compFin F E v (algebraMap (AF F) (AE F E) u) = 0 := by
    change (evFin F v u) ⊗ₜ[F] (1 : E) = 0
    rw [hu, TensorProduct.zero_tmul]
  rw [this, mul_zero, map_zero]

theorem lift_unitary (σ : E →ₐ[F] E) (J : Matrix ι ι E) (Y : Matrix ι ι (Fv F v ⊗[F] E))
    (hY : Yᵀ * J.map (inclR (Fv F v)) * Y.map (sigR (Fv F v) σ) = J.map (inclR (Fv F v))) :
    (lift v Y)ᵀ * incM F J * (lift v Y).map (cA σ) = incM F J := by
  set C := incM F J
  have hC : C.map (compFin F E v) = J.map (inclR (Fv F v)) := by
    ext i j
    change compFin F E v ((1 : AF F) ⊗ₜ[F] J i j) = (1 : Fv F v) ⊗ₜ[F] J i j
    change evFin F v 1 ⊗ₜ[F] J i j = _
    rw [map_one]
  have hT : (lift v Y)ᵀ = 1 + ext0 v (Y - 1)ᵀ := by
    rw [lift, Matrix.transpose_add, Matrix.transpose_one, ext_zero_transpose]
  have hS : (lift v Y).map (cA σ) = 1 + ext0 v ((Y - 1).map (sigR (Fv F v) σ)) := by
    rw [← ext_zero_map_conj]
    ext i j
    simp [lift, Matrix.one_apply]
  rw [hT, hS]
  have e1 : (1 + ext0 v (Y - 1)ᵀ) * C * (1 + ext0 v ((Y - 1).map (sigR (Fv F v) σ))) =
      C + (ext0 v (Y - 1)ᵀ * C + C * ext0 v ((Y - 1).map (sigR (Fv F v) σ)) +
        ext0 v (Y - 1)ᵀ * C * ext0 v ((Y - 1).map (sigR (Fv F v) σ))) := by noncomm_ring
  rw [e1, ext_zero_mul_right, matrixExtendByZero_mul, ext_zero_mul_left, ← matrixExtendByZero_add, ← matrixExtendByZero_add, hC]
  have hYs : (Y - 1).map (sigR (Fv F v) σ) = Y.map (sigR (Fv F v) σ) - 1 := by
    rw [Matrix.map_sub _ (fun a b => map_sub _ a b), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [hYs, Matrix.transpose_sub, Matrix.transpose_one]
  set Jl : Matrix ι ι (Fv F v ⊗[F] E) := J.map (inclR (Fv F v))
  have e2 : (Yᵀ - 1) * Jl + Jl * (Y.map (sigR (Fv F v) σ) - 1) + (Yᵀ - 1) * Jl * (Y.map (sigR (Fv F v) σ) - 1) =
      Yᵀ * Jl * Y.map (sigR (Fv F v) σ) - Jl := by noncomm_ring
  rw [e2, hY, sub_self, matrixExtendByZero_zero, add_zero]

end Lift

end GlobalTheory.DblSurj

namespace GlobalTheory.DblSurj

open Matrix GlobalTheory.EmbChart

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem map_mul_alg (f : Fv F v ⊗[F] E →ₐ[Fv F v] Fv F v) (M N : Matrix ι ι (Fv F v ⊗[F] E)) :
    (M * N).map f = M.map f * N.map f :=
  Matrix.map_mul (f := f.toRingHom)

theorem mat_split_ext (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {Y Z : Matrix ι ι (Fv F v ⊗[F] E)}
    (h1 : Y.map (splitProj t) = Z.map (splitProj t))
    (h2 : Y.map (splitProj (t.comp σ)) = Z.map (splitProj (t.comp σ))) : Y = Z := by
  ext i j
  exact split_ext h t (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

def pairMat (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (A B : Matrix ι ι (Fv F v)) :
    Matrix ι ι (Fv F v ⊗[F] E) := fun i j => (splitAlgEquiv h t).symm (A i j, B i j)

theorem pairMat_fst (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (A B : Matrix ι ι (Fv F v)) :
    (pairMat h t A B).map (splitProj t) = A := by
  ext i j; simp [pairMat]

theorem pairMat_snd (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (A B : Matrix ι ι (Fv F v)) :
    (pairMat h t A B).map (splitProj (t.comp σ)) = B := by
  ext i j; simp [pairMat]

theorem pairMat_mul (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (A B A' B' : Matrix ι ι (Fv F v)) :
    pairMat h t A B * pairMat h t A' B' = pairMat h t (A * A') (B * B') :=
  mat_split_ext h t (by rw [map_mul_alg, pairMat_fst, pairMat_fst, pairMat_fst])
    (by rw [map_mul_alg, pairMat_snd, pairMat_snd, pairMat_snd])

theorem pairMat_one (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) :
    pairMat h t (1 : Matrix ι ι (Fv F v)) 1 = 1 :=
  mat_split_ext h t (by rw [pairMat_fst, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [pairMat_snd, Matrix.map_one _ (map_zero _) (map_one _)])

def conjComp (t : E →ₐ[F] Fv F v) (J : Matrix ι ι E) (g : GL ι (Fv F v)) : Matrix ι ι (Fv F v) :=
  (J.map t)⁻¹ * ((g⁻¹ : GL ι (Fv F v)) : Matrix ι ι (Fv F v))ᵀ * J.map t

theorem conjComp_mul (t : E →ₐ[F] Fv F v) (J : Matrix ι ι E) (hJ : IsUnit (J.map t).det)
    (g₁ g₂ : GL ι (Fv F v)) : conjComp t J (g₁ * g₂) = conjComp t J g₁ * conjComp t J g₂ := by
  simp only [conjComp, _root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left _ _ hJ]

theorem conjComp_one (t : E →ₐ[F] Fv F v) (J : Matrix ι ι E) (hJ : IsUnit (J.map t).det) :
    conjComp t J 1 = 1 := by
  simp only [conjComp, inv_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one]
  exact Matrix.nonsing_inv_mul _ hJ

def locPt (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix ι ι E) (g : GL ι (Fv F v)) :
    Matrix ι ι (Fv F v ⊗[F] E) := pairMat h t g (conjComp t J g)

theorem locPt_mul (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix ι ι E)
    (hJ : IsUnit (J.map t).det) (g₁ g₂ : GL ι (Fv F v)) :
    locPt h t J (g₁ * g₂) = locPt h t J g₁ * locPt h t J g₂ := by
  rw [locPt, locPt, locPt, pairMat_mul, conjComp_mul t J hJ, Units.val_mul]

theorem locPt_one (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix ι ι E)
    (hJ : IsUnit (J.map t).det) : locPt h t J 1 = 1 := by
  rw [locPt, conjComp_one t J hJ, Units.val_one, pairMat_one]

theorem locPt_unitary_skew (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (J : Matrix ι ι E)
    (hJ : IsUnit (J.map t).det) (skew : ∀ i j, σ (J j i) = -J i j) (g : GL ι (Fv F v)) :
    (locPt h t J g)ᵀ * J.map (inclR (Fv F v)) * (locPt h t J g).map (sigR (Fv F v) σ) =
      J.map (inclR (Fv F v)) := by
  have hJl : ∀ τ : E →ₐ[F] Fv F v, (J.map (inclR (Fv F v))).map (splitProj τ) = J.map τ := fun τ =>
    Matrix.ext fun i j => by
      simp only [Matrix.map_apply]; exact splitProj_inclR τ (J i j)
  have hs1 : ((locPt h t J g).map (sigR (Fv F v) σ)).map (splitProj t) = conjComp t J g := by
    rw [Matrix.map_map]
    have : (splitProj t ∘ sigR (Fv F v) σ) = splitProj (t.comp σ) := funext fun y => (splitProj_comp t σ y).symm
    rw [this, locPt, pairMat_snd]
  have hs2 : ((locPt h t J g).map (sigR (Fv F v) σ)).map (splitProj (t.comp σ)) = g := by
    rw [Matrix.map_map]
    have : (splitProj (t.comp σ) ∘ sigR (Fv F v) σ) = splitProj t := funext fun y => splitProj_comp_sigR h t y
    rw [this, locPt, pairMat_fst]
  have hJs : J.map (t.comp σ) = -(J.map t)ᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, AlgHom.comp_apply, Matrix.neg_apply]
    rw [skew j i, map_neg]
  refine mat_split_ext h t ?_ ?_
  · rw [map_mul_alg, map_mul_alg, Matrix.transpose_map, hJl, hs1, locPt, pairMat_fst, conjComp]
    set Jt := J.map t
    set A : Matrix ι ι (Fv F v) := ((g⁻¹ : GL ι (Fv F v)) : Matrix ι ι (Fv F v))
    calc (g : Matrix ι ι (Fv F v))ᵀ * Jt * (Jt⁻¹ * Aᵀ * Jt)
        = (g : Matrix ι ι (Fv F v))ᵀ * (Jt * Jt⁻¹) * Aᵀ * Jt := by simp only [Matrix.mul_assoc]
      _ = (A * (g : Matrix ι ι (Fv F v)))ᵀ * Jt := by
          rw [Matrix.mul_nonsing_inv _ hJ, Matrix.mul_one, Matrix.transpose_mul]
      _ = Jt := by
          rw [show A * (g : Matrix ι ι (Fv F v)) = 1 from Units.inv_mul g, Matrix.transpose_one,
            Matrix.one_mul]
  · rw [map_mul_alg, map_mul_alg, Matrix.transpose_map, hJl, hs2, locPt, pairMat_snd, conjComp, hJs]
    set Jt := J.map t
    set A : Matrix ι ι (Fv F v) := ((g⁻¹ : GL ι (Fv F v)) : Matrix ι ι (Fv F v))
    calc (Jt⁻¹ * Aᵀ * Jt)ᵀ * -Jtᵀ * (g : Matrix ι ι (Fv F v))
        = -(Jtᵀ * A * (Jt * Jt⁻¹)ᵀ * (g : Matrix ι ι (Fv F v))) := by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.mul_neg,
            Matrix.neg_mul]
      _ = -(Jtᵀ * (A * (g : Matrix ι ι (Fv F v)))) := by
          rw [Matrix.mul_nonsing_inv _ hJ, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_assoc]
      _ = -Jtᵀ := by rw [show A * (g : Matrix ι ι (Fv F v)) = 1 from Units.inv_mul g, Matrix.mul_one]

end Local

end GlobalTheory.DblSurj

namespace GlobalTheory.DblSurj

open scoped Matrix

theorem det_ne_zero_of_sig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  have key : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star =
      (Aᵀ * M * A.map star).submatrix e.symm e.symm := by
    ext i j; rfl
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, hA, Matrix.det_mul, Matrix.det_mul] at hd
  intro h0
  rw [h0] at hd
  simp [Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg] at hd
  exact pow_ne_zero _ (by norm_num) hd.symm

end GlobalTheory.DblSurj

open scoped Matrix

open GlobalTheory.DblSurj in

theorem GlobalTheory.DblSurj.exists_locMatD_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (c : GL (Fin d) (Fv F v)) (g : GL (Fin d ⊕ Fin d) (Fv F v)),
      ∃ p ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v), GlobalTheory.DblScal.locMatD t c p = g := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v t c g
  have h := hP.base.cm
  have hW := hP.skew
  have hJ1 : IsUnit (W.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := det_ne_zero_of_sig (hW.sig (InfinitePlace.mk φ))
    have h1 : W.J.det ≠ 0 := fun e => h0 (by
      rw [Matrix.det_smul, show W.J.map _ = RingHom.mapMatrix _ W.J from rfl, ← RingHom.map_det, e, map_zero,
        mul_zero])
    rw [show W.J.map t = (t : E →+* Fv F v).mapMatrix W.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  set Jd : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) E := Matrix.fromBlocks W.J 0 0 (-W.J) with hJdef
  have hJd : IsUnit (Jd.map t).det := by
    have e : Jd.map t = Matrix.fromBlocks (W.J.map t) 0 0 (-(W.J.map t)) := by
      rw [hJdef, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero t), Matrix.map_neg _ (map_neg t)]
    rw [e, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    exact hJ1.mul ((isUnit_one.neg.pow _).mul hJ1)
  have skew : ∀ i j, σ (Jd j i) = -Jd i j := by
    rintro (i | i) (j | j) <;> simp [hJdef, hW.skew]
  have hdbl : dbl (incM F W.J) = incM F Jd := by
    rw [hJdef, dbl, incM, incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _)]
  set g₀ : GL (Fin d ⊕ Fin d) (Fv F v) := GlobalTheory.DblScal.dsum c * g * (GlobalTheory.DblScal.dsum c)⁻¹ with hg₀
  let G : GL (Fin d ⊕ Fin d) (AE F E) :=
    ⟨lift v (locPt h t Jd g₀), lift v (locPt h t Jd g₀⁻¹),
      by rw [lift_mul, ← locPt_mul h t Jd hJd, mul_inv_cancel, locPt_one h t Jd hJd, lift_one],
      by rw [lift_mul, ← locPt_mul h t Jd hJd, inv_mul_cancel, locPt_one h t Jd hJd, lift_one]⟩
  have hu : (lift v (locPt h t Jd g₀))ᵀ * dbl (incM F W.J) * (lift v (locPt h t Jd g₀)).map (cA σ) =
      dbl (incM F W.J) := by
    rw [hdbl]; exact lift_unitary v σ Jd _ (locPt_unitary_skew h t Jd hJd skew g₀)
  let p : GlobalTheory.DblScal.UD σ W.J := ⟨G, hu⟩
  refine ⟨p, lift_sub_one_at v _, ?_⟩
  have hpi : Matrix.GeneralLinearGroup.map (piW t) p.1 = g₀ := by
    apply Units.ext
    show (lift v (locPt h t Jd g₀)).map (piW t) = g₀.val
    have e : ∀ N : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E),
        N.map (piW t) = (N.map (compFin F E v)).map (splitProj t) := fun N => by rw [Matrix.map_map]; rfl
    rw [e, compFin_lift, locPt, pairMat_fst]
  show (GlobalTheory.DblScal.dsum c)⁻¹ * Matrix.GeneralLinearGroup.map (piW t) p.1 * GlobalTheory.DblScal.dsum c = g
  rw [hpi, hg₀]
  group
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_scaling_iwasawa_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (c : GL (Fin d) (Fv F v)) (g : GL (Fin d ⊕ Fin d) (Fv F v)),
      ∃ p ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v), GlobalTheory.DblScal.locMatD t c p = g := by
  atlas_forward_decl GlobalTheory.DblSurj.exists_locMatD_eq
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.DblScal in
theorem GlobalTheory.DblScal.scalW_main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ κ : UA σ W.J → ℂ, (∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = κ h • fun Y => ι φ (Y * (GlobalTheory.SplitFlip.invT (locMat t c h)).val)) →
    ∀ h ∈ UAt σ W (evFin F v), κ h = (chrW χX t (GlobalTheory.SplitFlip.gdet (locMat t c h)) : ℂ) *
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (locMat t c h)) (-(n : ℂ) / 2) := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v t b c ι hι κ hκ h hh
  obtain ⟨⟨-, dd, omd, hdc, hws, hbox⟩, -, -⟩ := hP.weil
  have hspl := hws.2.1
  have hloc := GlobalTheory.T.double_splitting_pair_identity hPr F E σ B n d X W M χX χW om r s r' s' hP dd omd hspl v
  obtain ⟨ιd, hιd, hprod⟩ := GlobalTheory.T.linear_model_double_splitting hPr F E σ B n d X W M χX χW om r s r' s' hP v t b c ι hι dd hdc
  obtain ⟨cd, hcd⟩ := GlobalTheory.T.double_scaling_local_identity hPr F E σ B n d X W M χX χW om r s r' s' hP v t b c dd omd hspl hloc ιd hιd
  obtain ⟨χd, hχd⟩ := GlobalTheory.T.double_scaling_local_equivariance hPr F E σ B n d X W M χX χW om r s r' s' hP v t b c dd omd hspl hloc ιd hιd cd hcd
  obtain ⟨gd, hgd⟩ := exists_diag_one h
  have hgdAt : gd ∈ UDAt σ W.J (evFin F v) := by
    intro u hu
    change u • (((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) - 1) = 0
    have h1 : u • (mat h - 1) = 0 := hh u hu
    rw [hgd, fromBlocks_sub_one, Matrix.fromBlocks_smul, h1]
    simp
  have e1 : κ h = cd gd := GlobalTheory.T.linear_model_compact_equivariance hPr F E σ B n d X W M χX χW om r s r' s' hP v t b c ι hι κ hκ dd omd hdc hspl
    (fun g gd' hg φ₁ hφ₁ φ₂ hφ₂ => hbox g gd' hg φ₁ hφ₁ φ₂ hφ₂) hloc ιd hιd hprod cd hcd h hh gd hgd
  obtain ⟨p, hpAt, hp⟩ := GlobalTheory.T.double_scaling_iwasawa_decomposition F E σ B n d X W M χX χW om r s r' s' hP v t c (fixDiag (locMat t c h))
  have e5 := GlobalTheory.T.double_scaling_local_vanishing hPr F E σ B n d X W M χX χW om r s r' s' hP v t b c dd omd hdc hws hloc ιd hιd cd hcd p hpAt
    ⟨1, by rw [hp]; exact fixDiag_diag _⟩
  rw [hp, gdet_fixDiag] at e5
  have f1 : cd gd = χd (GlobalTheory.SplitFlip.gdet (locMat t c h)) := by rw [hχd gd hgdAt, gdet_locMatD_diag t c h gd hgd]
  have f2 : cd p = χd (GlobalTheory.SplitFlip.gdet (locMat t c h)) := by rw [hχd p hpAt, hp, gdet_fixDiag]
  rw [e1, f1, ← f2]
  exact e5
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_model_compact_intertwines : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ κ : UA σ W.J → ℂ, (∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = κ h • fun Y => ι φ (Y * (GlobalTheory.SplitFlip.invT (locMat t c h)).val)) →
    ∀ h ∈ UAt σ W (evFin F v), κ h = (chrW χX t (GlobalTheory.SplitFlip.gdet (locMat t c h)) : ℂ) *
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (locMat t c h)) (-(n : ℂ) / 2) := by
  atlas_forward_decl GlobalTheory.DblScal.scalW_main
end
