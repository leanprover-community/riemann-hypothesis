import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.TupStdOfTwo
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.StdConjExOfWitt

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem contDiffAt_bilinear_comp_prod {P Q M T : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup T] [NormedSpace ℝ T]
    (B : M →L[ℝ] T →L[ℝ] T) (A : Q → M) (K : P → T) (p0 : P) (q0 : Q)
    (hA : ContDiffAt ℝ 1 A q0) (hK : ContDiffAt ℝ 1 K p0) :
    ContDiffAt ℝ 1 (fun z : P × Q => B (A z.2) (K z.1)) (p0, q0) ∧
    ∀ x t, fderiv ℝ (fun z : P × Q => B (A z.2) (K z.1)) (p0, q0) (x, t) =
      B (fderiv ℝ A q0 t) (K p0) + B (A q0) (fderiv ℝ K p0 x) := by
  have hA' : ContDiffAt ℝ 1 (fun z : P × Q => A z.2) (p0, q0) := hA.comp (p0, q0) contDiffAt_snd
  have hK' : ContDiffAt ℝ 1 (fun z : P × Q => K z.1) (p0, q0) := hK.comp (p0, q0) contDiffAt_fst
  refine ⟨(B.contDiff.contDiffAt.comp (p0, q0) hA').clm_apply hK', fun x t => ?_⟩
  have dA : HasFDerivAt (fun z : P × Q => A z.2) ((fderiv ℝ A q0).comp (ContinuousLinearMap.snd ℝ P Q)) (p0, q0) :=
    (hA.differentiableAt one_ne_zero).hasFDerivAt.comp (p0, q0) (hasFDerivAt_snd)
  have dK : HasFDerivAt (fun z : P × Q => K z.1) ((fderiv ℝ K p0).comp (ContinuousLinearMap.fst ℝ P Q)) (p0, q0) :=
    (hK.differentiableAt one_ne_zero).hasFDerivAt.comp (p0, q0) (hasFDerivAt_fst)
  have dBA := (B.hasFDerivAt.comp (p0, q0) dA)
  have h : HasFDerivAt (fun z : P × Q => B (A z.2) (K z.1)) _ (p0, q0) := dBA.clm_apply dK
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.flip_apply]
  rw [add_comm]

section Rm

variable {D : D7} (X : HidaSetting D)

theorem rmulT_add_left (a a' : MfI X) (Y : TupI X) : rmulT X (a + a') Y = rmulT X a Y + rmulT X a' Y := by
  funext b i
  simp [rmulT, add_mul, Finset.sum_add_distrib]

theorem rmulT_add_right (a : MfI X) (Y Y' : TupI X) : rmulT X a (Y + Y') = rmulT X a Y + rmulT X a Y' := by
  funext b i
  simp [rmulT, mul_add, Finset.sum_add_distrib]

theorem symm_add_of {A B : Type} [AddCommGroup A] [TopologicalSpace A] [AddCommGroup B] [TopologicalSpace B]
    (e : A ≃ₜ B) (he : ∀ x y, e (x + y) = e x + e y) (x y : B) : e.symm (x + y) = e.symm x + e.symm y := by
  apply e.injective
  rw [he, e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply]

def Rm {μ' : Type} (eM : MfI X ≃ₜ EuclideanSpace ℝ μ') (m : EuclideanSpace ℝ μ')
    (y : EuclideanSpace ℝ (KapI X)) : EuclideanSpace ℝ (KapI X) :=
  tupCoord X (rmulT X (eM.symm m) ((tupCoord X).symm y))

theorem rm_bil {μ' : Type} [Fintype μ'] (eM : MfI X ≃ₜ EuclideanSpace ℝ μ') (heM : ∀ x y, eM (x + y) = eM x + eM y) :
    ∃ B : EuclideanSpace ℝ μ' →L[ℝ] EuclideanSpace ℝ (KapI X) →L[ℝ] EuclideanSpace ℝ (KapI X),
      ∀ m y, B m y = Rm X eM m y := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hTs := symm_add_of (tupCoord X) (tupCoord_add X)
  have hMs := symm_add_of eM heM
  have H1 : ∀ m m' y, Rm X eM (m + m') y = Rm X eM m y + Rm X eM m' y := by
    intro m m' y
    simp only [Rm, hMs, rmulT_add_left, tupCoord_add]
  have H3 : ∀ m y y', Rm X eM m (y + y') = Rm X eM m y + Rm X eM m y' := by
    intro m y y'
    simp only [Rm, hTs, rmulT_add_right, tupCoord_add]
  have hc1 : ∀ y, Continuous fun m => Rm X eM m y := fun y =>
    (tupCoord X).continuous.comp ((continuous_right_mul_tuple X).comp
      ((eM.symm.continuous).prodMk continuous_const))
  have hc2 : ∀ m, Continuous fun y => Rm X eM m y := fun m =>
    (tupCoord X).continuous.comp ((continuous_right_mul_tuple X).comp
      (continuous_const.prodMk (tupCoord X).symm.continuous))
  have H2 : ∀ (r : ℝ) m y, Rm X eM (r • m) y = r • Rm X eM m y := fun r m y =>
    map_real_smul (AddMonoidHom.mk' (fun m => Rm X eM m y) fun a b => H1 a b y) (hc1 y) r m
  have H4 : ∀ (r : ℝ) m y, Rm X eM m (r • y) = r • Rm X eM m y := fun r m y =>
    map_real_smul (AddMonoidHom.mk' (fun y => Rm X eM m y) fun a b => H3 m a b) (hc2 m) r y
  let B0 : EuclideanSpace ℝ μ' →ₗ[ℝ] EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X) :=
    LinearMap.mk₂ ℝ (Rm X eM) H1 H2 H3 H4
  refine ⟨LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ B0), fun m y => rfl⟩

end Rm

def KapOrb {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) {ι : Type}
    (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ (KapI X) :=
  tupCoord X (κ x • Y0 X u')

theorem eM_ex {D : D7} (X : HidaSetting D) : ∃ (μ' : Type) (_ : Fintype μ') (eM : MfI X ≃ₜ EuclideanSpace ℝ μ'),
    ∀ x y, eM (x + y) = eM x + eM y := by
  haveI : NumberField.IsTotallyReal X.B.I.F := X.B.I.cm.totReal
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  obtain ⟨k, eK, hK⟩ := sq_coord_tens X.B.I.F X.B.I.E
  obtain ⟨k1, e1, h1⟩ := sq_coord_pi eK hK (Fin (D.R.rS + 1 + D.R.rS))
  obtain ⟨N, eM, hM⟩ := sq_coord_pi e1 h1 (Fin (D.R.rS + 1 + D.R.rS))
  refine ⟨Fin N, inferInstance, eM.trans (EuclideanSpace.equiv (Fin N) ℝ).symm.toHomeomorph, fun x y => ?_⟩
  show (EuclideanSpace.equiv (Fin N) ℝ).symm (eM (x + y)) =
    (EuclideanSpace.equiv (Fin N) ℝ).symm (eM x) + (EuclideanSpace.equiv (Fin N) ℝ).symm (eM y)
  have h2 : eM ((x + y : MfI X)) = eM x + eM y := hM x y
  rw [h2, map_add]

theorem psiC_eq {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (a : HmI X → MfI X) {ι η μ' : Type} [Fintype ι]
    [Fintype η] (κ : EuclideanSpace ℝ ι → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)
    (eH : HmI X ≃ₜ EuclideanSpace ℝ η) (eM : MfI X ≃ₜ EuclideanSpace ℝ μ') :
    PsiC X u' a κ eH = fun z => Rm X eM (eM (a (eH.symm z.2))) (KapOrb X u' κ z.1) := by
  funext z
  simp only [PsiC, Rm, KapOrb, Homeomorph.symm_apply_apply, smul_rmulT]

def LieComplementChartContDiffAt : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
    StdConj X hb u' c S → LieCompl X S L →
    ContDiffAt ℝ 1 (KapOrb X u' (kap0 X hb c L)) 0 ∧ kap0 X hb c L 0 • Y0 X u' = Y0 X u'

def LamMap {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) {ι η : Type} [Fintype ι] [Fintype η]
    (eH : HmI X ≃ₜ EuclideanSpace ℝ η) (dK : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (KapI X))
    (z : EuclideanSpace ℝ ι × EuclideanSpace ℝ η) : EuclideanSpace ℝ (KapI X) :=
  dK z.1 + (1 / 2 : ℝ) • tupCoord X (rmulT X (TinvI X u' * ((eH.symm z.2 : HmI X) : Matrix _ _ _)) (Y0 X u'))

open Classical in

def LamDet : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ {η : Type} [Fintype η] (eH : HmI X ≃ₜ EuclideanSpace ℝ η) (cν : ℝ), (∀ S T, eH (S + T) = eH S + eH T) →
    νinf.map eH = ENNReal.ofReal cν • volume →
    ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
    StdConj X hb u' c S → LieCompl X S L →
    ∃ Φ : (EuclideanSpace ℝ ι × EuclideanSpace ℝ η) ≃L[ℝ] EuclideanSpace ℝ (KapI X),
      (∀ z, Φ z = LamMap X u' eH (fderiv ℝ (KapOrb X u' (kap0 X hb c L)) 0) z) ∧
      ∃ Dv : ℝ, 0 < Dv ∧
        (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)).map Φ = ENNReal.ofReal Dv • volume ∧
        Real.sqrt |(matI X).det| / (Dv * cν) = tVal X u'

def KapSm : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
    StdConj X hb u' c S → LieCompl X S L → ContDiffAt ℝ 1 (KapOrb X u' (kap0 X hb c L)) 0

theorem kappa_c1_of_smooth (h : KapSm) : LieComplementChartContDiffAt := by
  intro D X u' ψ hT μinf νinf fibInf hP hb c S ι _ L hc hL
  exact ⟨h X u' ψ hT μinf νinf fibInf hP hb c S L hc hL, by rw [kap0_zero, one_smul]⟩

theorem tuple_c1_of_kappa (hK : LieComplementChartContDiffAt) : PolarMapContDiffAtBase := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC hD η _ eH hadd hb c S ι _ L hc hL
  obtain ⟨μ', _, eM, heM⟩ := eM_ex X
  obtain ⟨B, hB⟩ := rm_bil X eM heM
  obtain ⟨hA, -⟩ := hD eH eM hadd heM
  obtain ⟨hk, -⟩ := hK X u' ψ hT μinf νinf fibInf hP hb c S L hc hL
  have e : PsiC X u' a (kap0 X hb c L) eH =
      fun z => B (eM (a (eH.symm z.2))) (KapOrb X u' (kap0 X hb c L) z.1) := by
    rw [psiC_eq X u' a (kap0 X hb c L) eH eM]
    funext z
    rw [hB]
  unfold PolarChartContDiffAt
  rw [e]
  exact (contDiffAt_bilinear_comp_prod B (fun t => eM (a (eH.symm t))) _ 0 (eH (TI X u' hT)) hA hk).1

theorem tupDet_of (hK : LieComplementChartContDiffAt) (hLam : LamDet) : TupDet := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC hD η _ eH cν hadd hν hb c S ι _ L hc hL
  obtain ⟨μ', _, eM, heM⟩ := eM_ex X
  obtain ⟨B, hB⟩ := rm_bil X eM heM
  obtain ⟨hA, hdA⟩ := hD eH eM hadd heM
  obtain ⟨hk, h0⟩ := hK X u' ψ hT μinf νinf fibInf hP hb c S L hc hL
  obtain ⟨Φ, hΦ, Dv, hDv, hvol, har⟩ := hLam X u' ψ hT μinf νinf fibInf hP eH cν hadd hν hb c S L hc hL
  refine ⟨Φ, Dv, ?_, hDv, hvol, har⟩
  have e : PsiC X u' a (kap0 X hb c L) eH =
      fun z => B (eM (a (eH.symm z.2))) (KapOrb X u' (kap0 X hb c L) z.1) := by
    rw [psiC_eq X u' a (kap0 X hb c L) eH eM]
    funext z
    rw [hB]
  rw [e]
  refine ContinuousLinearMap.ext fun z => ?_
  rw [(contDiffAt_bilinear_comp_prod B (fun t => eM (a (eH.symm t))) _ 0 (eH (TI X u' hT)) hA hk).2 z.1 z.2, hdA, map_smul,
    ContinuousLinearMap.smul_apply, hB, hB]
  show _ = Φ (z.1, z.2)
  rw [hΦ, LamMap, add_comm]
  congr 1
  · simp only [Rm, Homeomorph.symm_apply_apply, eH.symm_apply_apply, hC.2.1, rmulT_one, Homeomorph.apply_symm_apply]
  · simp only [Rm, KapOrb, Homeomorph.symm_apply_apply, h0]

theorem tupStd_of_kap (hK : LieComplementChartContDiffAt) (hLam : LamDet) : TupStd :=
  tupStd_of_two (tuple_c1_of_kappa hK) (tupDet_of hK hLam)

theorem tupStd_of_sm (hK : KapSm) (hLam : LamDet) : TupStd := tupStd_of_kap (kappa_c1_of_smooth hK) hLam

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

theorem contDiff_conj_exp {ι : Type} [Fintype ι] {n : ℕ}
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) (A B : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) :
    ContDiff ℝ 1 (fun x => (A * NormedSpace.exp (L x) * B) *ᵥ y) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  let Lc : EuclideanSpace ℝ ι →L[ℝ] Matrix (Fin n) (Fin n) ℂ := LinearMap.toContinuousLinearMap L
  let H : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Fin n → ℂ) :=
    { toFun := fun M => (A * M * B) *ᵥ y
      map_add' := fun M M' => by simp [Matrix.mul_add, Matrix.add_mul, Matrix.add_mulVec]
      map_smul' := fun c M => by
        simp only [RingHom.id_apply]
        rw [Matrix.mul_smul, Matrix.smul_mul]
        funext i
        simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Pi.smul_apply, Finset.smul_sum, smul_mul_assoc] }
  let Hc : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap H
  have he : ContDiff ℝ 1 (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) :=
    contDiff_iff_contDiffAt.2 fun M => (NormedSpace.exp_analytic (𝕂 := ℝ) M).contDiffAt
  exact Hc.contDiff.comp (he.comp Lc.contDiff)

theorem theta_act {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (hb : AdBridgeIso X.B.I) (s : X.B.I.Ginf)
    (v : InfinitePlace X.B.I.F) (b : Fin (D.R.rS + 1 + D.R.rS)) (i : Fin X.B.I.n) :
    PI.AprimeInfU.thetaInf X v ((X.toInf hb s • Y0 X u') b i) =
      ((X.B.I.P v * uMat (s v) * (X.B.I.P v)⁻¹) *ᵥ fun j => X.B.I.φ v (tupH (frameOf X u') b j)) i := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  set Mm : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :=
    ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (X.toInf hb s) : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) with hMm
  have hmap : Mm.map (PI.AprimeInfU.thetaInf X v) = X.B.I.P v * uMat (s v) * (X.B.I.P v)⁻¹ := by
    rw [uMat_toInf X hb s v, ← hMm]
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.mul_one]
  rw [← hmap]
  show PI.AprimeInfU.thetaInf X v ((Mm *ᵥ Y0 X u' b) i) = _
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show Y0 X u' b j = inclR (Ainf X.B.I.F) (tupH (frameOf X u') b j) from rfl, thetaInf_inclR]

theorem continuous_thetaInf {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F) :
    Continuous (PI.AprimeInfU.thetaInf X v) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  let σ : Ainf X.B.I.F →+* ℂ := PI.AprimeInfU.evInf X v
  have hσ : Continuous σ :=
    (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp (continuous_apply v)
  let φl : (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) →ₛₗ[σ] ℂ :=
    { toFun := PI.AprimeInfU.thetaInf X v
      map_add' := map_add _
      map_smul' := fun a y => by
        rw [Algebra.smul_def, map_mul, smul_eq_mul]
        congr 1
        show PI.AprimeInfU.thetaInf X v (a ⊗ₜ[X.B.I.F] (1 : X.B.I.E)) = _
        rw [thetaInf_tmul, map_one, mul_one] }
  exact IsModuleTopology.continuous_of_linearMapₛₗ hσ φl

theorem kapSm_holds : KapSm := by
  intro D X u' ψ hT μinf νinf fibInf hP hb c S ι _ L hc hL
  classical
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : IsTotallyReal X.B.I.F := X.B.I.cm.totReal
  let Φ : TupI X →+ (InfinitePlace X.B.I.F → Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → ℂ) :=
    { toFun := fun Y v b i => PI.AprimeInfU.thetaInf X v (Y b i)
      map_zero' := by funext v b i; exact map_zero _
      map_add' := by intro Y Z; funext v b i; exact map_add _ _ _ }
  have hsa : ∀ z z', (tupCoord X).symm (z + z') = (tupCoord X).symm z + (tupCoord X).symm z' := by
    intro z z'; apply (tupCoord X).injective; rw [tupCoord_add]; simp
  let T0 : EuclideanSpace ℝ (KapI X) →+ TupI X :=
    { toFun := (tupCoord X).symm
      map_zero' := by
        have h := hsa 0 0
        rw [add_zero] at h
        simpa using h
      map_add' := hsa }
  let Ψ0 := Φ.comp T0
  have hc0 : Continuous Ψ0 := by
    refine continuous_pi fun v => continuous_pi fun b => continuous_pi fun i => ?_
    exact (continuous_thetaInf X v).comp ((continuous_apply i).comp ((continuous_apply b).comp
      (tupCoord X).symm.continuous))
  let Ψ := Ψ0.toRealLinearMap hc0
  have hΨ : ∀ z v b i, Ψ z v b i = PI.AprimeInfU.thetaInf X v ((tupCoord X).symm z b i) := fun _ _ _ _ => rfl
  have hinj : Function.Injective Ψ := by
    intro z z' h
    apply (tupCoord X).symm.injective
    funext b i
    have key : ∀ v, PI.AprimeInfU.thetaInf X v ((tupCoord X).symm z b i) =
        PI.AprimeInfU.thetaInf X v ((tupCoord X).symm z' b i) := by
      intro v
      rw [← hΨ, ← hΨ, h]
    exact sub_eq_zero.1 (thetaInf_inj X _ fun v => by rw [map_sub, key v, sub_self])
  have hcbi : Fintype.card (Module.Free.ChooseBasisIndex (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex,
      Module.finrank_eq_card_basis (Algebra.TensorProduct.basis (Ainf X.B.I.F)
        (Module.finBasisOfFinrankEq X.B.I.F X.B.I.E X.B.I.cm.deg2)), Fintype.card_fin]
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (KapI X)) =
      Module.finrank ℝ (InfinitePlace X.B.I.F → Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → ℂ) := by
    simp only [finrank_euclideanSpace, Fintype.card_prod, hcbi, Module.finrank_pi_fintype,
      Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fin]
    ring
  let Ψe := LinearMap.linearEquivOfInjective (Ψ : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] _) hinj hdim
  have hΨe : ∀ Z : TupI X, tupCoord X Z = Ψe.symm (Φ Z) := by
    intro Z
    apply Ψe.injective
    rw [LinearEquiv.apply_symm_apply, LinearMap.linearEquivOfInjective_apply]
    show Φ (T0 (tupCoord X Z)) = Φ Z
    simp [T0]
  have hG : ∀ x v b, (fun i => Φ (kap0 X hb c L x • Y0 X u') v b i) =
      ((X.B.I.P v * uMat (c v)) * NormedSpace.exp (L x v) * (uMat (c v)⁻¹ * (X.B.I.P v)⁻¹)) *ᵥ
        fun j => X.B.I.φ v (tupH (frameOf X u') b j) := by
    intro x v b
    funext i
    show PI.AprimeInfU.thetaInf X v ((X.toInf hb (c * (fun w => expU (X.B.I.ε w) (L x w)) * c⁻¹) • Y0 X u') b i) = _
    rw [theta_act]
    have hu : uMat ((c * (fun w => expU (X.B.I.ε w) (L x w)) * c⁻¹) v) =
        uMat (c v) * NormedSpace.exp (L x v) * uMat (c v)⁻¹ := by
      have e := expU_val (X.B.I.ε v) (L x v) (hL.1 x v).1
      simp only [uMat, Pi.mul_apply, Pi.inv_apply, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul] at e ⊢
      rw [e]
    rw [hu]
    simp only [Matrix.mul_assoc]
  have hGc : ContDiff ℝ 1 (fun x => Φ (kap0 X hb c L x • Y0 X u')) := by
    refine contDiff_pi.2 fun v => contDiff_pi.2 fun b => ?_
    have e : (fun x => Φ (kap0 X hb c L x • Y0 X u') v b) = fun x =>
        ((X.B.I.P v * uMat (c v)) * NormedSpace.exp (((LinearMap.proj v : (InfinitePlace X.B.I.F →
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) →ₗ[ℝ] _) ∘ₗ L) x) * (uMat (c v)⁻¹ * (X.B.I.P v)⁻¹)) *ᵥ
          fun j => X.B.I.φ v (tupH (frameOf X u') b j) := by
      funext x
      exact hG x v b
    rw [e]
    exact contDiff_conj_exp _ _ _ _
  have hK : KapOrb X u' (kap0 X hb c L) = fun x => Ψe.symm (Φ (kap0 X hb c L x • Y0 X u')) := by
    funext x
    exact hΨe _
  rw [hK]
  have h1 : ContDiff ℝ 1 (fun y => Ψe.symm y) := Ψe.toContinuousLinearEquiv.symm.contDiff
  exact (h1.comp hGc).contDiffAt

end PI.AprimeInfW
end
end

section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

def betaV {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F) (Y : TupI X) :
    Matrix (Fin X.B.I.n) (Fin (D.R.rS + 1 + D.R.rS)) ℂ :=
  Matrix.of fun i b => ((X.B.I.P v)⁻¹ *ᵥ fun j => PI.AprimeInfU.thetaInf X v (Y b j)) i

theorem betaV_add {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F) (Y Z : TupI X) :
    betaV X v (Y + Z) = betaV X v Y + betaV X v Z := by
  ext i b
  simp only [betaV, Matrix.of_apply, Matrix.add_apply]
  rw [← Pi.add_apply ((X.B.I.P v)⁻¹ *ᵥ _), ← Matrix.mulVec_add]
  congr 2
  funext j
  exact map_add _ _ _


theorem betaV_rmul {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F) (a : MfI X) (Y : TupI X) :
    betaV X v (rmulT X a Y) = betaV X v Y * a.map (PI.AprimeInfU.thetaInf X v) := by
  ext i b
  simp only [betaV, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, rmulT, Matrix.mulVec, dotProduct,
    map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem betaV_inj {D : D7} (X : HidaSetting D) (Y Z : TupI X) (h : ∀ v, betaV X v Y = betaV X v Z) : Y = Z := by
  funext b j
  refine sub_eq_zero.1 (thetaInf_inj X _ fun v => ?_)
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have hc : (fun j => PI.AprimeInfU.thetaInf X v (Y b j)) = fun j => PI.AprimeInfU.thetaInf X v (Z b j) := by
    have e : (X.B.I.P v)⁻¹ *ᵥ (fun j => PI.AprimeInfU.thetaInf X v (Y b j)) =
        (X.B.I.P v)⁻¹ *ᵥ (fun j => PI.AprimeInfU.thetaInf X v (Z b j)) := by
      funext i
      have := congrFun (congrFun (h v) i) b
      simpa [betaV] using this
    have e2 := congrArg (fun y => X.B.I.P v *ᵥ y) e
    simpa only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mulVec] using e2
  rw [map_sub, congrFun hc j, sub_self]

end PI.AprimeInfW
end
end
