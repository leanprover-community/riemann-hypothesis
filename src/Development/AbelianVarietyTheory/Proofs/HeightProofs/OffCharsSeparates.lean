import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.OmegaUpDownForms
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsAddHaarMeasureIsAddFundamentalDomainPrei
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticValTauCompat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsJunkLiftNotVanishing
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOfHeisenbergLevelAndSmooth
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothIffRealCoordinatesAndRealLines
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsArchimedeanAdeleChartOfRealChart
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealChartInfiniteAdelesCmType

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct

namespace GlobalTheory.WeilTieCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gram_mul_inv (V : HSp D) : HeisenbergWeilMatrices.gramA V * HeisenbergWeilMatrices.gramInvA V = 1 := by
  unfold HeisenbergWeilMatrices.gramA HeisenbergWeilMatrices.gramInvA
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne V))]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem inv_mul_gram (V : HSp D) : HeisenbergWeilMatrices.gramInvA V * HeisenbergWeilMatrices.gramA V = 1 := mul_eq_one_comm.1 (gram_mul_inv V)

theorem gram_conj (V : HSp D) : ((HeisenbergWeilMatrices.gramA V).map (cA D))ᵀ = HeisenbergWeilMatrices.gramA V := by
  ext i j
  exact (DualPairCheck.cA_incA _).trans (congrArg (incA D) (DualPairCheck.gram_star V j i))

theorem gramInv_conj (V : HSp D) : ((HeisenbergWeilMatrices.gramInvA V).map (cA D))ᵀ = HeisenbergWeilMatrices.gramInvA V := by
  have h : HeisenbergWeilMatrices.gramA V * ((HeisenbergWeilMatrices.gramInvA V).map (cA D))ᵀ = 1 := by
    rw [← gram_conj, ← Matrix.transpose_mul, ← Matrix.map_mul, inv_mul_gram,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  calc _ = (HeisenbergWeilMatrices.gramInvA V * HeisenbergWeilMatrices.gramA V) * ((HeisenbergWeilMatrices.gramInvA V).map (cA D))ᵀ := by rw [inv_mul_gram, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, h, Matrix.mul_one]

def kap (A B : HSp D) : WA A B ≃+ WA A B where
  toFun x := HMul.hMul (HeisenbergWeilMatrices.gramInvA A)ᵀ x
  invFun y := HMul.hMul (HeisenbergWeilMatrices.gramA A)ᵀ y
  left_inv x := by
    simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, inv_mul_gram, Matrix.transpose_one, Matrix.one_mul]
  right_inv x := by
    simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, gram_mul_inv, Matrix.transpose_one, Matrix.one_mul]
  map_add' x y := Matrix.mul_add _ _ _

theorem kap_apply (A B : HSp D) (x : WA A B) : kap A B x = HMul.hMul (HeisenbergWeilMatrices.gramInvA A)ᵀ x := rfl

theorem kap_symm_apply (A B : HSp D) (x : WA A B) : (kap A B).symm x = HMul.hMul (HeisenbergWeilMatrices.gramA A)ᵀ x := rfl

def kapT (A B : HSp D) : WA A B ≃+ WA B A := (kap A B).trans (Matrix.transposeAddEquiv _ _ _)

theorem kapT_apply (A B : HSp D) (x : WA A B) : kapT A B x = (kap A B x)ᵀ := rfl

theorem topRing (D : D7) : IsTopologicalRing (AE D) :=
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)

theorem hHom_kap {A B : HSp D} (hr : A.rank ≤ B.rank) (x y : WA A B) :
    hHom A B (kap A B y) (kap A B x) = HeisenbergWeilMatrices.herm x y := by
  have s := DualPairCheck.sum_small (cA D) (HeisenbergWeilMatrices.gramA A) (HeisenbergWeilMatrices.gramA B) (kap A B y) (kap A B x)
  unfold hHom
  rw [if_pos hr]
  refine Eq.trans s ?_
  simp only [kap_apply, HeisenbergWeilMatrices.herm, HeisenbergWeilMatrices.adj, HeisenbergWeilMatrices.colMat, Formalism.UG.cT, Matrix.transpose_transpose, Matrix.map_mul,
    Matrix.transpose_mul, Matrix.transpose_map, gramInv_conj, Matrix.mul_assoc, inv_mul_gram, Matrix.mul_one]
  rfl

theorem actHom_kap {A B : HSp D} (hr : A.rank ≤ B.rank) (g : GA D A) (h : GA D B) (x : WA A B) :
    actHom A B g h (kap A B x) = kap A B (HeisenbergWeilMatrices.act (g, h) x) := by
  have h1 : ((mt A g).map (cA D))ᵀ * HeisenbergWeilMatrices.gramA A * mt A g = HeisenbergWeilMatrices.gramA A := mt_rel A g
  have h2 : mt A g * HeisenbergWeilMatrices.gMat g⁻¹ = 1 := by
    change HeisenbergWeilMatrices.gMat g * _ = 1
    rw [← HeisenbergWeilMatrices.gMat_mul, mul_inv_cancel, HeisenbergWeilMatrices.gMat_one]
  have h3 : HeisenbergWeilMatrices.gramInvA A * ((mt A g).map (cA D))ᵀ = HeisenbergWeilMatrices.gMat g⁻¹ * HeisenbergWeilMatrices.gramInvA A := by
    calc _ = HeisenbergWeilMatrices.gramInvA A * (((mt A g).map (cA D))ᵀ * (HeisenbergWeilMatrices.gramA A * (mt A g * HeisenbergWeilMatrices.gMat g⁻¹) * HeisenbergWeilMatrices.gramInvA A)) := by
          rw [h2, Matrix.mul_one, gram_mul_inv, Matrix.mul_one]
      _ = HeisenbergWeilMatrices.gramInvA A * (((mt A g).map (cA D))ᵀ * HeisenbergWeilMatrices.gramA A * mt A g) * (HeisenbergWeilMatrices.gMat g⁻¹ * HeisenbergWeilMatrices.gramInvA A) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, inv_mul_gram, Matrix.one_mul]
  have h4 := congrArg Matrix.transpose h3
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at h4
  unfold actHom
  rw [if_pos hr]
  simp only [kap_apply, HeisenbergWeilMatrices.act, HeisenbergWeilMatrices.colMat, cM, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc, h4]
  rfl

def IsChange {A B V W : HSp D} (κ : WA A B ≃+ WA V W) (σ : GA D V × GA D W → GA D A × GA D B) : Prop :=
  Continuous κ ∧ Continuous κ.symm ∧ (∀ x y, symplH V W (κ x) (κ y) = HeisenbergWeilMatrices.hsymp x y) ∧
    (∀ x, κ x ∈ ratL V W ↔ x ∈ HeisenbergWeilMatrices.WQ A B) ∧ (∀ (c : AE D) x, κ (c • x) = c • κ x) ∧
    ∀ g h x, actHom V W g h (κ x) = κ (HeisenbergWeilMatrices.act (σ (g, h)) x)

theorem isChange_kap {A B : HSp D} (hr : A.rank ≤ B.rank) : IsChange (kap A B) id := by
  have := topRing D
  refine ⟨continuous_const.matrix_mul continuous_id, continuous_const.matrix_mul continuous_id, fun x y => ?_,
    fun x => ⟨?_, ?_⟩, fun c x => Matrix.mul_smul (HeisenbergWeilMatrices.gramInvA A)ᵀ c x, actHom_kap hr⟩
  · unfold symplH sympl
    rw [hHom_kap hr]
    rfl
  · rintro ⟨γ, hγ⟩
    refine ⟨A.gramᵀ * γ, ?_⟩
    rw [← (kap A B).symm_apply_apply x, ← hγ]
    exact Matrix.map_mul (f := incA D)
  · rintro ⟨γ, rfl⟩
    exact ⟨(A.gram⁻¹)ᵀ * γ, Matrix.map_mul (f := incA D)⟩

theorem isChange_kapT {A B : HSp D} (hr : A.rank < B.rank) : IsChange (kapT A B) Prod.swap := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := isChange_kap hr.le
  refine ⟨h1.matrix_transpose, h2.comp continuous_id.matrix_transpose, fun x y => ?_, fun x => ?_, fun c x => ?_,
    fun g h x => ?_⟩
  · rw [← h3]
    unfold symplH sympl
    rw [kapT_apply, kapT_apply, hHom_transpose A B hr.ne]
  · rw [← h4]
    constructor
    · rintro ⟨γ, hγ⟩
      exact ⟨γᵀ, congrArg Matrix.transpose hγ⟩
    · rintro ⟨γ, hγ⟩
      exact ⟨γᵀ, congrArg Matrix.transpose hγ⟩
  · rw [kapT_apply, h5]; rfl
  · rw [kapT_apply, actHom_swap A B hr.ne, h6]; rfl

theorem heis_change {A B V W : HSp D} {κ : WA A B ≃+ WA V W} {σ} (hκ : IsChange κ σ) (ψ : AddChar (AF D.host.F) ℂ)
    (u : WA A B) (f : WA V W → ℂ) : Heisenberg₂ ψ V W (κ u) f ∘ κ = HeisenbergWeilMatrices.rho ψ u (f ∘ κ) := by
  funext w
  simp only [Function.comp, Heisenberg₂, HeisenbergWeilMatrices.rho_apply, hκ.2.2.1, map_add]

theorem isSplitIdem_iff (e : AE D) : IsSplitIdem D e ↔ ∃ v, HeisenbergWeilMatrices.IsSplitIdem D v e := by
  classical
  constructor
  · rintro ⟨h1, h2, v, ε, ⟨α, rfl, hv, hv'⟩, h3⟩
    refine ⟨v, h1, h2, h3.trans ?_⟩
    have : α = singleV D.host.F v 1 := by
      refine RestrictedProduct.ext _ _ fun w => ?_
      by_cases hw : w = v
      · subst hw
        exact hv.trans (RestrictedProduct.single_eq_same _ _ _).symm
      · exact (hv' w hw).trans (RestrictedProduct.single_eq_of_ne _ _ hw).symm
    rw [this]; rfl
  · rintro ⟨v, h1, h2, h3⟩
    exact ⟨h1, h2, v, _, ⟨singleV D.host.F v 1, rfl,
      RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) v 1,
      fun w hw => RestrictedProduct.single_eq_of_ne
        (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) 1 hw⟩, h3⟩

theorem suppAt_iff {v} {e : AE D} (he : HeisenbergWeilMatrices.IsSplitIdem D v e) (V : HSp D) (g : GA D V) :
    SuppAt e V g ↔ HeisenbergWeilMatrices.IsAt (HeisenbergWeilMatrices.idemFin D v) g := by
  rw [← he.sum]
  unfold SuppAt HeisenbergWeilMatrices.IsAt
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  change (e + cA D e) * (mt V g i j - (1 : Matrix _ _ (AE D)) i j) = mt V g i j - (1 : Matrix _ _ (AE D)) i j ↔
    (1 - (e + cA D e)) * mt V g i j = (1 - (e + cA D e)) * (1 : Matrix _ _ (AE D)) i j
  constructor <;> intro h <;> linear_combination -h

theorem isDetAt_iff {e : AE D} (he : IsIdempotentElem e) (V : HSp D) (g : GA D V) (x : (AE D)ˣ) :
    IsDetAt e V g x ↔ x = HeisenbergWeilMatrices.atIdem he (HeisenbergWeilMatrices.detA V g) := by
  rw [Units.ext_iff]; rfl

theorem isDetRoot_iff (V : HSp D) (g : GA D V) (x : (AE D)ˣ) :
    IsDetRoot V g x ↔ HeisenbergWeilMatrices.IsRoot D x (HeisenbergWeilMatrices.detA V g) := by
  unfold HeisenbergWeilMatrices.IsRoot
  rw [mul_inv_eq_iff_eq_mul, Units.ext_iff]; rfl

end GlobalTheory.WeilTieCompare

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct ContDiff

namespace GlobalTheory.WeilTieCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem map_zero_change {A B V W : HSp D} (κ : WA A B →+ WA V W) (hκ : ∀ (c : AE D) x, κ (c • x) = c • κ x)
    {R : Type} [CommRing R] (φ : AE D →+* R) (x : WA A B) (hx : x.map φ = 0) : (κ x).map φ = 0 := by
  classical
  ext k l
  rw [Matrix.matrix_eq_sum_single x]
  simp only [map_sum, Matrix.map_apply, Matrix.sum_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  have e : Matrix.single i j (x i j) = x i j • Matrix.single i j (1 : AE D) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  have h0 : φ (x i j) = 0 := congrFun (congrFun hx i) j
  rw [e, hκ, Matrix.smul_apply, smul_eq_mul, map_mul, h0, zero_mul]

theorem IsChange.map_zero_iff {A B V W : HSp D} {κ : WA A B ≃+ WA V W} {σ} (hκ : IsChange κ σ)
    {R : Type} [CommRing R] (φ : AE D →+* R) (x : WA A B) : (κ x).map φ = 0 ↔ x.map φ = 0 := by
  refine ⟨fun h => ?_, map_zero_change κ.toAddMonoidHom hκ.2.2.2.2.1 φ x⟩
  rw [← κ.symm_apply_apply x]
  refine map_zero_change κ.symm.toAddMonoidHom (fun c y => κ.injective ?_) φ _ h
  change κ (κ.symm _) = κ (c • κ.symm y)
  rw [hκ.2.2.2.2.1, κ.apply_symm_apply, κ.apply_symm_apply]

theorem smooth_iff {A B V W : HSp D} {κ : WA A B ≃+ WA V W} {σ} (hκ : IsChange κ σ) (f : WA V W → ℂ) :
    (∀ (k : ℕ) (L : (Fin k → ℝ) →+ WA V W), Continuous L → (∀ t, (L t).map (finPart D) = 0) →
      ∀ w, ContDiff ℝ ∞ fun t => f (w + L t)) ↔
    ∀ w : WA A B, ContDiff ℝ ∞
      fun p : Fin A.rank → Fin B.rank → (InfinitePlace D.host.F → ℝ) × (InfinitePlace D.host.F → ℝ) =>
        (f ∘ κ) (w + Matrix.of fun i j => HeisenbergWeilMatrices.realPt D (p i j)) := by
  let R := Fin A.rank → Fin B.rank → (InfinitePlace D.host.F → ℝ) × (InfinitePlace D.host.F → ℝ)
  let P : R →+ WA A B := AddMonoidHom.mk' (fun p => Matrix.of fun i j => HeisenbergWeilMatrices.realPt D (p i j)) fun p q =>
    Matrix.ext fun i j => (DualPairCompare.realPtHom D).map_add _ _
  have hP : Continuous P := continuous_pi fun i => continuous_pi fun j =>
    (DualPairCompare.continuous_realPt D).comp ((continuous_apply j).comp (continuous_apply i))
  constructor
  · intro h w
    let e : R ≃L[ℝ] (Fin (Module.finrank ℝ R) → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
    have := (h _ (κ.toAddMonoidHom.comp (P.comp e.symm.toLinearMap.toAddMonoidHom))
      (hκ.1.comp (hP.comp e.symm.continuous)) (fun t => (hκ.map_zero_iff _ _).2 (Matrix.ext fun i j =>
        DualPairCompare.finPart_realPt D _)) (κ w)).comp e.contDiff
    convert this using 1
    funext p
    change f (κ (w + P p)) = f (κ w + κ (P (e.symm (e p))))
    rw [e.symm_apply_apply, map_add]
  · intro h k L hL h0 w
    obtain ⟨co, hc, -, h2⟩ := DualPairCompare.exists_co D
    let q : (Fin k → ℝ) →+ R := AddMonoidHom.mk' (fun t i j => co (κ.symm (L t) i j)) fun s t => by
      funext i j
      rw [map_add, map_add, Matrix.add_apply, map_add]
      rfl
    have hq : Continuous q := continuous_pi fun i => continuous_pi fun j =>
      hc.comp ((continuous_apply j).comp ((continuous_apply i).comp (hκ.2.1.comp hL)))
    have := (h (κ.symm w)).comp (q.toRealLinearMap hq).contDiff
    convert this using 1
    funext t
    have z : (κ.symm (L t)).map (finPart D) = 0 := by
      rw [← hκ.map_zero_iff, κ.apply_symm_apply]; exact h0 t
    have e : P (q t) = κ.symm (L t) := Matrix.ext fun i j => h2 _ (congrFun (congrFun z i) j)
    change _ = f (κ (κ.symm w + P (q t)))
    rw [e, map_add, κ.apply_symm_apply, κ.apply_symm_apply]

theorem theta_iff {A B V W : HSp D} {κ : WA A B ≃+ WA V W} {σ} (hκ : IsChange κ σ) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : Continuous ψ) (f : WA V W → ℂ) : IsThetaFun ψ V W f ↔ HeisenbergWeilMatrices.IsTheta ψ (f ∘ κ) := by
  have sk : ∀ x y, -symplH V W (κ x) (κ y) = HeisenbergWeilMatrices.hsymp y x := fun x y => by
    rw [← hκ.2.2.1]
    unfold symplH
    rw [DualPairCheck.sympl_skew V W (κ x), mul_neg]
  have lv : ∀ u, Heisenberg₂ ψ V W (κ u) f = f ↔ HeisenbergWeilMatrices.rho ψ u (f ∘ κ) = f ∘ κ := fun u => by
    rw [← heis_change hκ]
    exact (κ.surjective.injective_comp_right.eq_iff).symm
  constructor
  · rintro ⟨h1, ⟨U, hU, h2⟩, -, h4⟩
    refine ⟨fun γ hγ w => ?_, (smooth_iff hκ f).1 h4, U.comap κ.toAddMonoidHom, hU.preimage hκ.1, fun u hu h0 =>
      (lv u).1 (h2 _ hu ((hκ.map_zero_iff _ _).2 h0))⟩
    obtain ⟨δ, hδ⟩ := (hκ.2.2.2.1 γ).2 hγ
    have := h1 δ (κ w)
    rw [show ratW V W δ = κ γ from hδ, sk, ← map_add] at this
    exact this
  · rintro ⟨h1, h2, U, hU, h3⟩
    have l : ∃ U : AddSubgroup (WA V W), IsOpen (U : Set (WA V W)) ∧
        ∀ u ∈ U, u.map (infPart D) = 0 → Heisenberg₂ ψ V W u f = f := by
      refine ⟨U.comap κ.symm.toAddMonoidHom, hU.preimage hκ.2.1, fun u hu h0 => ?_⟩
      obtain ⟨u, rfl⟩ := κ.surjective u
      exact (lv u).2 (h3 u (κ.symm_apply_apply u ▸ hu) ((hκ.map_zero_iff _ _).1 h0))
    have s := (smooth_iff hκ f).2 h2
    obtain ⟨θ, hθ⟩ := DualPairCompare.exists_infFam D
    obtain ⟨ρ, r1, r2, r3⟩ := FockCompare.exists_real_chart D θ hθ (DualPairCompare.plF_bijective D)
    obtain ⟨s', hs'⟩ := FockCompare.RealChart.exists_chart D θ hθ ρ r1 r2 r3
    refine ⟨fun δ w => ?_, l, FockCompare.ThetaCont.continuous_of_level_of_smooth D θ s' hs' ψ hψ V W f l
      (((FockCompare.smooth_iff_sm_and_real_lines D θ s' hs' V W).1 f).1 s), s⟩
    obtain ⟨γ, hγ⟩ := κ.surjective (ratW V W δ)
    obtain ⟨w, rfl⟩ := κ.surjective w
    rw [← hγ, sk, ← map_add]
    exact h1 γ ((hκ.2.2.2.1 γ).1 ⟨δ, hγ.symm⟩) w

theorem stdChar_iff (ψ : AddChar (AF D.host.F) ℂ) : IsStdChar D ψ (-1) ↔ HeisenbergWeilMatrices.IsStdChar D (-1) ψ := by
  refine and_congr_right fun _ => ⟨fun h x => ?_, fun h => ⟨DualPairCompare.exists_infFam D, fun θ hθ x => ?_⟩⟩
  · obtain ⟨θ, hθ⟩ := h.1
    rw [h.2 θ hθ x, DualPairCompare.sum_infFam θ hθ]
    rfl
  · rw [h x, DualPairCompare.sum_infFam θ hθ]
    rfl

theorem theta_continuous {A B : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) (hr : A.rank ≤ B.rank)
    (f : HeisenbergWeilMatrices.Theta ψ A B) : Continuous (f : WA A B → ℂ) := by
  have hκ := isChange_kap hr
  have h : IsThetaFun ψ A B ((f : WA A B → ℂ) ∘ (kap A B).symm) := by
    rw [theta_iff hκ hψ]
    have : ((f : WA A B → ℂ) ∘ (kap A B).symm) ∘ kap A B = f := by funext x; simp
    rw [this]; exact f.2
  have := h.cont.comp hκ.1
  convert this using 1
  funext x; simp

def SameNorm (V W : HSp D) (f f' : WA V W → ℂ) : Prop :=
  ∀ (μ : Measure (WA V W)) (𝓕 : Set (WA V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V W) 𝓕 μ →
    ∫ w in 𝓕, ‖f' w‖ ^ 2 ∂μ = ∫ w in 𝓕, ‖f w‖ ^ 2 ∂μ

theorem sameNorm_change {A B V W : HSp D} {κ : WA A B ≃+ WA V W} {σ} (hκ : IsChange κ σ) (f f' : WA V W → ℂ) :
    SameNorm V W f f' ↔ SameNorm A B (f ∘ κ) (f' ∘ κ) := by
  have : BorelSpace (WA A B) := ⟨rfl⟩
  have : BorelSpace (WA V W) := ⟨rfl⟩
  have := (GlobalTheory.AdelicMatrixLattice.lattice D A B).1
  have := (GlobalTheory.AdelicMatrixLattice.lattice D V W).1
  constructor
  · intro h μ 𝓕 hμ hF
    obtain ⟨ν, h1, h2, h3⟩ := GlobalTheory.exists_isAddHaarMeasure_isAddFundamentalDomain_preimage _ _ κ.symm hκ.2.1 hκ.1 (ratL V W) (ratL A B)
      (fun x => ((hκ.2.2.2.1 (κ.symm x)).symm.trans (by rw [κ.apply_symm_apply]))) μ 𝓕 hμ hF
    rw [← h3 fun w => ‖(f' ∘ κ) w‖ ^ 2, ← h3 fun w => ‖(f ∘ κ) w‖ ^ 2]
    simpa using h ν _ h1 h2
  · intro h μ 𝓕 hμ hF
    obtain ⟨ν, h1, h2, h3⟩ := GlobalTheory.exists_isAddHaarMeasure_isAddFundamentalDomain_preimage _ _ κ hκ.1 hκ.2.1 (ratL A B) (ratL V W) hκ.2.2.2.1 μ 𝓕 hμ hF
    rw [← h3 fun w => ‖f' w‖ ^ 2, ← h3 fun w => ‖f w‖ ^ 2]
    exact h ν _ h1 h2

theorem exists_probPair (A B : HSp D) : ∃ m : Measure (WA A B) × Set (WA A B), HeisenbergWeilMatrices.IsProbPair A B m.1 m.2 := by
  have : BorelSpace (WA A B) := ⟨rfl⟩
  obtain ⟨_, _, _, _, _, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D A B
  obtain ⟨μ, 𝓕, h⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact _ (ratL A B) K hK hc).1
  exact ⟨(μ, 𝓕), h⟩

theorem sameNorm_iff {A B : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (hr : A.rank ≤ B.rank)
    (f f' : HeisenbergWeilMatrices.Theta ψ A B) :
    SameNorm A B f f' ↔ ∃ N, N ≠ ⊤ ∧ HeisenbergWeilMatrices.IsNormSq (f : WA A B → ℂ) N ∧ HeisenbergWeilMatrices.IsNormSq (f' : WA A B → ℂ) N := by
  have : BorelSpace (WA A B) := ⟨rfl⟩
  obtain ⟨_, _, _, _, _, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D A B
  have key := fun f : HeisenbergWeilMatrices.Theta ψ A B => (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact _ (ratL A B) K hK hc).2 f (theta_continuous hψ.1 hr f)
    fun γ hγ w => by rw [f.2.law γ hγ w, norm_mul, hψ.2.1, one_mul]
  obtain ⟨N, hN⟩ := key f
  obtain ⟨N', hN'⟩ := key f'
  obtain ⟨m, hm⟩ := exists_probPair A B
  have e : ∀ (g : WA A B → ℂ) (M : NNReal), (∀ (μ : Measure (WA A B)) (𝓕 : Set (WA A B)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratL A B) 𝓕 μ → μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤ ∧ ∫⁻ w in 𝓕, ‖g w‖ₑ ^ 2 ∂μ = μ 𝓕 * M ∧
        ∫ w in 𝓕, ‖g w‖ ^ 2 ∂μ = (μ 𝓕).toReal * M) → HeisenbergWeilMatrices.IsNormSq g M := fun g M h =>
    ⟨⟨m, hm⟩, fun a ha => (h a.1 a.2 ha.1 ha.2.1).2.2.1.trans (by rw [ha.2.2, one_mul])⟩
  constructor
  · intro h
    have h1 := h m.1 m.2 hm.1 hm.2.1
    rw [(hN _ _ hm.1 hm.2.1).2.2.2, (hN' _ _ hm.1 hm.2.1).2.2.2, hm.2.2] at h1
    have h2 : N' = N := by simpa using h1
    exact ⟨N, ENNReal.coe_ne_top, e _ _ hN, h2 ▸ e _ _ hN'⟩
  · rintro ⟨M, -, h1, h2⟩ μ 𝓕 hμ hF
    have h3 : (N' : ENNReal) = N :=
      (((e _ _ hN').2 m hm).symm.trans (h2.2 m hm)).trans ((h1.2 m hm).symm.trans ((e _ _ hN).2 m hm))
    rw [(hN _ _ hμ hF).2.2.2, (hN' _ _ hμ hF).2.2.2, ENNReal.coe_inj.1 h3]

theorem alg_inj (D : D7) : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
  Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective

theorem wComp_ne {v} {e : AE D} (he : HeisenbergWeilMatrices.IsSplitIdem D v e) (u : (AE D)ˣ) : HeisenbergWeilMatrices.wComp D v e u ≠ 0 := by
  classical
  have h1 : e * e = e := he.idem
  have h2 : e * cA D e = 0 := he.orth
  have h3 : e + cA D e = HeisenbergWeilMatrices.idemFin D v := he.sum
  have k : HeisenbergWeilMatrices.trA D (e * u) * HeisenbergWeilMatrices.trA D (e * ↑u⁻¹) = pairA D.host.F 0 (singleV D.host.F v 1) := by
    apply alg_inj D
    have hu : cA D u * cA D ↑u⁻¹ = 1 := by rw [← map_mul, u.mul_inv, map_one]
    have hc : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
    rw [map_mul]
    refine Eq.trans ?_ h3
    erw [GlobalTheory.FockCompare.SymplVal.trace_AE D, GlobalTheory.FockCompare.SymplVal.trace_AE D]
    rw [map_mul, map_mul]
    linear_combination (e * e) * u.mul_inv + h1 + (cA D e * cA D e) * hu + hc +
      (u * cA D ↑u⁻¹ + cA D u * ↑u⁻¹) * h2
  intro h0
  have := congrArg (fun a => evalV D.host.F v (sndA D.host.F a)) k
  simp only [map_mul] at this
  change HeisenbergWeilMatrices.wComp D v e u * _ = _ at this
  rw [h0, zero_mul] at this
  exact zero_ne_one (this.trans
    (RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletionIntegers D.host.F) v 1))

theorem splitMod_pos {v} {e : AE D} (he : HeisenbergWeilMatrices.IsSplitIdem D v e) (A B : HSp D) (p : GA D A × GA D B) :
    0 < HeisenbergWeilMatrices.splitMod A B v e p := by
  have k : ∀ u : (AE D)ˣ, 0 < HeisenbergWeilMatrices.absV D v (HeisenbergWeilMatrices.wComp D v e u) := fun u =>
    NNReal.coe_pos.2 (WithZeroMulInt.toNNReal_pos _ ((Valuation.ne_zero_iff _).2 (wComp_ne he u)))
  exact mul_pos (Real.rpow_pos_of_pos (k _) _) (Real.rpow_pos_of_pos (k _) _)

section Clauses

variable {A B V W : HSp D} {κ : WA A B ≃+ WA V W} {σ : GA D V × GA D W → GA D A × GA D B}
  {ψ : AddChar (AF D.host.F) ℂ} {S : Type} [AddCommGroup S] [Module ℂ S]
  {ev : S →ₗ[ℂ] (WA V W → ℂ)} {E : S ≃ₗ[ℂ] HeisenbergWeilMatrices.Theta ψ A B}

theorem heis_iff (hκ : IsChange κ σ) (hE : ∀ Φ, ev Φ ∘ κ = E Φ) (u : WA A B) (Φ Φ' : S) :
    ev Φ' = Heisenberg₂ ψ V W (κ u) (ev Φ) ↔ (E Φ' : WA A B → ℂ) = HeisenbergWeilMatrices.rho ψ u (E Φ) := by
  rw [← hE, ← hE, ← heis_change hκ]
  exact (κ.surjective.injective_comp_right.eq_iff).symm

theorem impl_iff (hκ : IsChange κ σ) (hE : ∀ Φ, ev Φ ∘ κ = E Φ) {M : Module.End ℂ S}
    {N : Module.End ℂ (HeisenbergWeilMatrices.Theta ψ A B)} (hM : ∀ Φ, E (M Φ) = N (E Φ)) (g : GA D V) (h : GA D W) :
    (∀ w₀ Φ Φ', ev Φ' = Heisenberg₂ ψ V W w₀ (ev Φ) → ev (M Φ') = Heisenberg₂ ψ V W (actHom V W g h w₀) (ev (M Φ))) ↔
      HeisenbergWeilMatrices.Implements N (σ (g, h)) := by
  unfold HeisenbergWeilMatrices.Implements
  rw [κ.surjective.forall]
  refine forall_congr' fun u => ?_
  rw [E.surjective.forall]
  refine forall_congr' fun Φ => ?_
  rw [E.surjective.forall]
  refine forall_congr' fun Φ' => ?_
  rw [hκ.2.2.2.2.2, heis_iff hκ hE, heis_iff hκ hE, hM, hM]

theorem unit_iff (hκ : IsChange κ σ) (hE : ∀ Φ, ev Φ ∘ κ = E Φ) (hψ : IsCharAF D.host.F ψ) (hr : A.rank ≤ B.rank)
    (Φ Φ' : S) : SameNorm V W (ev Φ) (ev Φ') ↔
      ∃ N, N ≠ ⊤ ∧ HeisenbergWeilMatrices.IsNormSq (E Φ : WA A B → ℂ) N ∧ HeisenbergWeilMatrices.IsNormSq (E Φ' : WA A B → ℂ) N := by
  rw [sameNorm_change hκ, hE, hE, sameNorm_iff hψ hr]

theorem actsBy_iff (hκ : IsChange κ σ) (hE : ∀ Φ, ev Φ ∘ κ = E Φ) {M : Module.End ℂ S}
    {N : Module.End ℂ (HeisenbergWeilMatrices.Theta ψ A B)} (hM : ∀ Φ, E (M Φ) = N (E Φ)) (e : AE D) (c : ℂ) :
    (∀ ℓ : S →ₗ[ℂ] ℂ, (∀ u : WA V W, (∀ i j, cA D e * u i j = u i j) → ∀ Φ Φ', ev Φ' = Heisenberg₂ ψ V W u (ev Φ) → ℓ Φ' = ℓ Φ) →
      ∀ Φ, ℓ (M Φ) = c * ℓ Φ) ↔ HeisenbergWeilMatrices.ActsBy e N c := by
  have key : ∀ l : HeisenbergWeilMatrices.Theta ψ A B →ₗ[ℂ] ℂ,
      (∀ u : WA V W, (∀ i j, cA D e * u i j = u i j) → ∀ Φ Φ', ev Φ' = Heisenberg₂ ψ V W u (ev Φ) → l (E Φ') = l (E Φ)) ↔
      ∀ y ∈ HeisenbergWeilMatrices.lagr A B (HeisenbergWeilMatrices.cj D e), ∀ f f' : HeisenbergWeilMatrices.Theta ψ A B,
        (f' : WA A B → ℂ) = HeisenbergWeilMatrices.rho ψ y f → l f' = l f := by
    intro l
    rw [κ.surjective.forall]
    refine forall_congr' fun u => imp_congr ?_ ?_
    · change _ ↔ cA D e • u = u
      rw [← κ.injective.eq_iff, hκ.2.2.2.2.1, ← Matrix.ext_iff]
      rfl
    · rw [E.surjective.forall]
      refine forall_congr' fun Φ => ?_
      rw [E.surjective.forall]
      refine forall_congr' fun Φ' => ?_
      rw [heis_iff hκ hE]
  constructor
  · intro h l hl f
    obtain ⟨Φ, rfl⟩ := E.surjective f
    rw [← hM]
    exact h (l ∘ₗ E.toLinearMap) ((key l).2 hl) Φ
  · intro h ℓ hℓ Φ
    have := h (ℓ ∘ₗ E.symm.toLinearMap) ((key _).1 fun u hu Φ Φ' hh => by simpa using hℓ u hu Φ Φ' hh) (E Φ)
    rw [← hM] at this
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using this

theorem ev_zero (hE : ∀ Φ, ev Φ ∘ κ = E Φ) (Φ : S) : ev Φ 0 = (E Φ : WA A B → ℂ) 0 := by
  rw [← hE, Function.comp, map_zero]

end Clauses

end GlobalTheory.WeilTieCompare

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct

namespace GlobalTheory.WeilTieCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {X : ThetaX D} {T : ThetaTied D X}

theorem split_iff (V W : HSp D) (χ χ' : X.Chr) : SplittingKernelQuotients.IsSplitting V W (T.eChr χ) (T.eChr χ') ↔
    ResEta D (T.eChr χ) V.rank ∧ ResEta D (T.eChr χ') W.rank := by
  have k : ∀ χ, IsHeckeChar D (T.eChr χ) := fun χ =>
    ((Set.ext_iff.1 T.eChr_range _).1 ⟨χ, rfl⟩).1
  exact ⟨fun h => ⟨h.resA, h.resB⟩, fun h => ⟨k χ, k χ', h.1, h.2⟩⟩

def Rel (C : SplittingKernelQuotients.Core T) (ev : ∀ V W, X.Sch V W →ₗ[ℂ] (WA V W → ℂ))
    (om : ∀ V W, X.Chr → X.Chr → (GA D V × GA D W →* Module.End ℂ (X.Sch V W))) : Prop :=
  ∀ (A B : HSp D) (hr : A.rank < B.rank),
    (∀ Φ, ev A B Φ ∘ kap A B = C.eUp A B hr.le Φ) ∧ (∀ Φ, ev B A Φ ∘ kapT A B = C.eDn A B hr Φ) ∧
    ∀ χA χB hs g h, om A B χA χB (g, h) = C.omUp A B hr.le χA χB hs (g, h) ∧
      om B A χB χA (h, g) = C.omDn A B hr χA χB hs (g, h)

def Match (Wl : WeilTied D X T) (C : SplittingKernelQuotients.Core T) : Prop := Wl.ψ = C.ψ ∧ Rel C Wl.evS Wl.om

def Twist (C : SplittingKernelQuotients.Core T) : Prop :=
  ∀ (A B : HSp D) (hr : A.rank < B.rank) χA χB χA' χB' hs hs' (g : GA D A) (h : GA D B), ∃ cg ch : Circle,
    HeisenbergWeilMatrices.IsTildeVal D (T.eChr χB' / T.eChr χB) (HeisenbergWeilMatrices.detA A g) cg ∧
    HeisenbergWeilMatrices.IsTildeVal D (T.eChr χA' / T.eChr χA) (HeisenbergWeilMatrices.detA B h) ch ∧
    C.om A B hr.le χA' χB' hs' (g, h) = ((cg⁻¹ * ch : Circle) : ℂ) • C.om A B hr.le χA χB hs (g, h)

def ExactModulus (Wl : WeilTied D X T) : Prop :=
  ∀ (A B : HSp D) χ χ', A.rank < B.rank → ResEta D (T.eChr χ) A.rank → ResEta D (T.eChr χ') B.rank →
    ∀ v e, HeisenbergWeilMatrices.IsSplitIdem D v e → ∀ g h, SuppAt e A g → SuppAt e B h → ∀ x y, IsDetAt e A g x → IsDetAt e B h y →
    ∀ ℓ : X.Sch A B →ₗ[ℂ] ℂ,
      (∀ u : WA A B, (∀ i j, cA D e * u i j = u i j) → ∀ Φ Φ',
        Wl.evS A B Φ' = Heisenberg₂ Wl.ψ A B u (Wl.evS A B Φ) → ℓ Φ' = ℓ Φ) →
      ∀ Φ, ℓ (Wl.om A B χ χ' (g, h) Φ) =
        (HeisenbergWeilMatrices.splitMod A B v e (g, h) : ℂ) * (splitFac A B (T.eChr χ) (T.eChr χ') x y : ℂ) * ℓ Φ

def Converges (Wl : WeilTied D X T) : Prop :=
  ∀ (V W : HSp D) χ χ', V.rank ≠ W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank → V.SigOK →
    AllSome (fun m : Measure (GA D V) × Set (GA D V) => IsVolPair D V m.1 m.2) fun m =>
      ∀ (Φ : X.Sch V W) (F : X.cusp V) (h : GA D W),
        IntegrableOn (fun g => Wl.evS V W (Wl.om V W χ χ' (g, h) Φ) 0 * T.ev V (F : X.AF V) g) m.2 m.1

def EqualRank (T : ThetaTied D X) (ψ : AddChar (AF D.host.F) ℂ) : Prop :=
  ∀ A B : HSp D, A.rank = B.rank → ∃ E : X.Sch A B ≃ₗ[ℂ] HeisenbergWeilMatrices.Theta ψ A B,
    ∀ χA χB, SplittingKernelQuotients.IsSplitting A B (T.eChr χA) (T.eChr χB) → ∃ om : SplittingKernelQuotients.Rep ψ A B,
      HeisenbergWeilMatrices.IsWeil ψ (T.eChr χA) (T.eChr χB) om ∧ (A.SigOK → ∀ (Φ : X.Sch A B) (φ : X.cusp A) (h : GA D B),
        SplittingKernelQuotients.IsQuotInt A (T.petC A) (fun g => SplittingKernelQuotients.kern om (E Φ) g h * T.ev A (φ : X.AF A) g)
          (T.ev B (X.th A B χA χB Φ φ) h))

def EqualRankWith (T : ThetaTied D X) (ψ : AddChar (AF D.host.F) ℂ)
    (P : ∀ A B : HSp D, (X.Sch A B → WA A B → ℂ) → Prop) : Prop :=
  ∀ A B : HSp D, A.rank = B.rank → ∃ E : X.Sch A B ≃ₗ[ℂ] HeisenbergWeilMatrices.Theta ψ A B, (P A B fun Φ => (E Φ : WA A B → ℂ)) ∧
    ∀ χA χB, SplittingKernelQuotients.IsSplitting A B (T.eChr χA) (T.eChr χB) → ∃ om : SplittingKernelQuotients.Rep ψ A B,
      HeisenbergWeilMatrices.IsWeil ψ (T.eChr χA) (T.eChr χB) om ∧ (A.SigOK → ∀ (Φ : X.Sch A B) (φ : X.cusp A) (h : GA D B),
        SplittingKernelQuotients.IsQuotInt A (T.petC A) (fun g => SplittingKernelQuotients.kern om (E Φ) g h * T.ev A (φ : X.AF A) g)
          (T.ev B (X.th A B χA χB Φ φ) h))

def EqualRankPure (T : ThetaTied D X) (ψ : AddChar (AF D.host.F) ℂ) : Prop :=
  EqualRankWith T ψ fun A B ev => ∀ Φ, Φ ∈ X.fact A B ↔ SplittingKernelQuotients.IsPure ψ (ev Φ)

def FactPure (Wl : WeilTied D X T) : Prop :=
  ∀ A B : HSp D, A.rank < B.rank →
    (∀ Φ, Φ ∈ X.fact A B ↔ SplittingKernelQuotients.IsPure Wl.ψ (Wl.evS A B Φ ∘ kap A B)) ∧
    ∀ Φ, Φ ∈ X.fact B A ↔ SplittingKernelQuotients.IsPure Wl.ψ (Wl.evS B A Φ ∘ kapT A B)

section FromRel

variable {C : SplittingKernelQuotients.Core T} {ev : ∀ V W, X.Sch V W →ₗ[ℂ] (WA V W → ℂ)}
  {om : ∀ V W, X.Chr → X.Chr → (GA D V × GA D W →* Module.End ℂ (X.Sch V W))}

theorem Rel.up (R : Rel C ev om) {A B : HSp D} (hr : A.rank < B.rank) {χA χB} (hs) (g h) (Φ) :
    C.eUp A B hr.le (om A B χA χB (g, h) Φ) = C.om A B hr.le χA χB hs (g, h) (C.eUp A B hr.le Φ) := by
  rw [((R A B hr).2.2 χA χB hs g h).1]
  simp [SplittingKernelQuotients.Core.omUp, LinearEquiv.conj_apply]

theorem Rel.dn (R : Rel C ev om) {A B : HSp D} (hr : A.rank < B.rank) {χA χB} (hs) (g h) (Φ) :
    C.eDn A B hr (om B A χB χA (h, g) Φ) = C.om A B hr.le χA χB hs (g, h) (C.eDn A B hr Φ) := by
  rw [((R A B hr).2.2 χA χB hs g h).2]
  simp [SplittingKernelQuotients.Core.omDn, LinearEquiv.conj_apply]

theorem Rel.kernUp (R : Rel C ev om) {A B : HSp D} (hr : A.rank < B.rank) {χA χB} (hs) (g h) (Φ) :
    ev A B (om A B χA χB (g, h) Φ) 0 = SplittingKernelQuotients.kern (C.om A B hr.le χA χB hs) (C.eUp A B hr.le Φ) g h := by
  rw [ev_zero (R A B hr).1, R.up hr hs]; rfl

theorem Rel.kernDn (R : Rel C ev om) {A B : HSp D} (hr : A.rank < B.rank) {χA χB} (hs) (g h) (Φ) :
    ev B A (om B A χB χA (h, g) Φ) 0 = SplittingKernelQuotients.kern (C.om A B hr.le χA χB hs) (C.eDn A B hr Φ) g h := by
  rw [ev_zero (R A B hr).2.1, R.dn hr hs]; rfl

theorem Rel.transpose_iff (R : Rel C ev om) {A B : HSp D} (hr : A.rank < B.rank) (Φ : X.Sch A B) (Φ' : X.Sch B A) :
    (∀ x : WA A B, ev B A Φ' xᵀ = ev A B Φ x) ↔ C.eDn A B hr Φ' = C.eUp A B hr.le Φ := by
  rw [(kap A B).surjective.forall, Subtype.ext_iff, ← (R A B hr).1, ← (R A B hr).2.1, funext_iff]
  rfl

theorem Rel.transpose_iff' (R : Rel C ev om) {A B : HSp D} (hr : A.rank < B.rank) (Φ : X.Sch A B) (Φ' : X.Sch B A) :
    (∀ x : WA B A, ev A B Φ xᵀ = ev B A Φ' x) ↔ C.eDn A B hr Φ' = C.eUp A B hr.le Φ := by
  rw [← R.transpose_iff hr]
  exact ⟨fun h x => (h xᵀ).symm, fun h x => (h xᵀ).symm⟩

theorem Rel.smul (R : Rel C ev om) {A B : HSp D} (hr : A.rank < B.rank) {χA χB χA' χB' hs hs' g h} {c : ℂ}
    (H : C.om A B hr.le χA' χB' hs' (g, h) = c • C.om A B hr.le χA χB hs (g, h)) :
    om A B χA' χB' (g, h) = c • om A B χA χB (g, h) ∧ om B A χB' χA' (h, g) = c • om B A χB χA (h, g) := by
  constructor
  · refine LinearMap.ext fun Φ => (C.eUp A B hr.le).injective ?_
    rw [R.up hr hs', H, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, R.up hr hs]
  · refine LinearMap.ext fun Φ => (C.eDn A B hr).injective ?_
    rw [R.dn hr hs', H, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, R.dn hr hs]

theorem tilde_val {χ : (AE D)ˣ →* Circle} (h0 : ResEta D χ 0) (V : HSp D) (g : GA D V) {x : (AE D)ˣ}
    (hx : IsDetRoot V g x) : HeisenbergWeilMatrices.IsTildeVal D χ (HeisenbergWeilMatrices.detA V g) (χ x) := by
  refine ⟨⟨x, (isDetRoot_iff V g x).1 hx⟩, fun y hy => ?_⟩
  obtain ⟨a, rfl⟩ := (GlobalTheory.Member.isDetRoot_laws D V).2.1 g x y hx ((isDetRoot_iff V g y).2 hy)
  obtain ⟨η, hη⟩ := h0.1
  rw [map_mul, h0.2 η hη, pow_zero, mul_one]

theorem tilde_one {χ : (AE D)ˣ →* Circle} {u c} (h : HeisenbergWeilMatrices.IsTildeVal D (χ / χ) u c) : c = 1 := by
  obtain ⟨x, hx⟩ := h.1
  rw [← h.2 x hx, div_self', MonoidHom.one_apply]

theorem tilde_mul {χ ν : X.Chr} {V : HSp D} {g : GA D V} {x c} (hx : IsDetRoot V g x)
    (h : HeisenbergWeilMatrices.IsTildeVal D (T.eChr (χ * ν) / T.eChr χ) (HeisenbergWeilMatrices.detA V g) c) : c = T.eChr ν x := by
  rw [map_mul, mul_div_cancel_left] at h
  exact (h.2 x ((isDetRoot_iff V g x).1 hx)).symm

theorem Twist.target (H : Twist C) (A B : HSp D) (hr : A.rank < B.rank) (χA χB ν hs hs' g h x) (hx : IsDetRoot A g x) :
    C.om A B hr.le χA (χB * ν) hs' (g, h) = (((T.eChr ν x)⁻¹ : Circle) : ℂ) • C.om A B hr.le χA χB hs (g, h) := by
  obtain ⟨cg, ch, h1, h2, h3⟩ := H A B hr χA χB χA (χB * ν) hs hs' g h
  rwa [tilde_one h2, tilde_mul hx h1, mul_one] at h3

theorem Twist.source (H : Twist C) (A B : HSp D) (hr : A.rank < B.rank) (χA χB ν hs hs' g h x) (hx : IsDetRoot B h x) :
    C.om A B hr.le (χA * ν) χB hs' (g, h) = ((T.eChr ν x : Circle) : ℂ) • C.om A B hr.le χA χB hs (g, h) := by
  obtain ⟨cg, ch, h1, h2, h3⟩ := H A B hr χA χB (χA * ν) χB hs hs' g h
  rwa [tilde_one h1, tilde_mul hx h2, inv_one, one_mul] at h3

theorem Rel.twist (R : Rel C ev om) : TwRule T om → Twist C := by
  intro H A B hr χA χB χA' χB' hs hs' g h
  obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D A g
  obtain ⟨y, hy⟩ := GlobalTheory.RecDict.exists_isDetRoot D B h
  have z : ∀ {χ χ' : X.Chr} {n}, ResEta D (T.eChr χ) n → ResEta D (T.eChr χ') n → ResEta D (T.eChr (χ' / χ)) 0 :=
    fun {χ χ' n} h h' => by
      rw [div_eq_mul_inv, map_mul, map_inv]
      exact resEta_parity (resEta_mul h' (resEta_inv h)) (by omega)
  have hA := z hs.resA hs'.resA
  have hB := z hs.resB hs'.resB
  have e1 := H.twW_up A B χA' χB (χB' / χB) hr hs'.resA hs.resB hB g h x hx
  have e2 := H.twV_up A B χA χB (χA' / χA) hr hs.resA hs.resB hA g h y hy
  rw [mul_div_cancel] at e1 e2
  refine ⟨_, _, map_div T.eChr _ _ ▸ tilde_val hB A g hx, map_div T.eChr _ _ ▸ tilde_val hA B h hy, ?_⟩
  refine LinearMap.ext fun f => ?_
  obtain ⟨Φ, rfl⟩ := (C.eUp A B hr.le).surjective f
  rw [LinearMap.smul_apply, ← R.up hr hs, ← R.up hr hs', e1, e2, smul_smul, LinearMap.smul_apply, map_smul,
    Circle.coe_mul, map_div, map_div]

theorem Rel.twRule (R : Rel C ev om) (H : Twist C) : TwRule T om := by
  have m : ∀ {χ ν : X.Chr} {n}, ResEta D (T.eChr χ) n → ResEta D (T.eChr ν) 0 → ResEta D (T.eChr (χ * ν)) n :=
    fun h h' => by rw [map_mul]; exact resEta_mul h h'
  exact ⟨fun V W χ χ' ν hr h1 h2 h0 g h x hx => (R.smul hr (H.target V W hr χ χ' ν ((split_iff _ _ _ _).2 ⟨h1, h2⟩)
      ((split_iff _ _ _ _).2 ⟨h1, m h2 h0⟩) g h x hx)).1,
    fun V W χ χ' ν hr h1 h2 h0 g h x hx => (R.smul hr (H.source V W hr χ χ' ν ((split_iff _ _ _ _).2 ⟨h1, h2⟩)
      ((split_iff _ _ _ _).2 ⟨m h1 h0, h2⟩) g h x hx)).1,
    fun V W χ χ' ν hr h1 h2 h0 g h x hx => (R.smul hr (H.source W V hr χ' χ ν ((split_iff _ _ _ _).2 ⟨h2, h1⟩)
      ((split_iff _ _ _ _).2 ⟨m h2 h0, h1⟩) h g x hx)).2,
    fun V W χ χ' ν hr h1 h2 h0 g h x hx => (R.smul hr (H.target W V hr χ' χ ν ((split_iff _ _ _ _).2 ⟨h2, h1⟩)
      ((split_iff _ _ _ _).2 ⟨h2, m h1 h0⟩) h g x hx)).2⟩

theorem Rel.twRule_iff (R : Rel C ev om) : TwRule T om ↔ Twist C := ⟨R.twist, R.twRule⟩

end FromRel

theorem exists_equiv {A B V W : HSp D} {κ : WA A B ≃+ WA V W} {σ} (hκ : IsChange κ σ) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : Continuous ψ) {S : Type} [AddCommGroup S] [Module ℂ S] (ev : S →ₗ[ℂ] (WA V W → ℂ)) (hi : Function.Injective ev)
    (hr : Set.range ev = {f | IsThetaFun ψ V W f}) : ∃ E : S ≃ₗ[ℂ] HeisenbergWeilMatrices.Theta ψ A B, ∀ Φ, ev Φ ∘ κ = E Φ := by
  let L : S →ₗ[ℂ] HeisenbergWeilMatrices.Theta ψ A B := LinearMap.codRestrict _ (LinearMap.funLeft ℂ ℂ κ ∘ₗ ev) fun Φ =>
    (theta_iff hκ hψ _).1 ((Set.ext_iff.1 hr _).1 ⟨Φ, rfl⟩)
  refine ⟨LinearEquiv.ofBijective L ⟨fun Φ Φ' h => hi (κ.surjective.injective_comp_right (congrArg Subtype.val h)),
    fun f => ?_⟩, fun _ => rfl⟩
  have e : ((f : WA A B → ℂ) ∘ κ.symm) ∘ κ = f := funext fun x => congrArg (f : WA A B → ℂ) (κ.symm_apply_apply x)
  obtain ⟨Φ, hΦ⟩ := (Set.ext_iff.1 hr _).2 ((theta_iff hκ hψ _).2 (e.symm ▸ f.2))
  exact ⟨Φ, Subtype.ext ((congrArg (· ∘ κ) hΦ).trans e)⟩

theorem range_eq {A B V W : HSp D} {κ : WA A B ≃+ WA V W} {σ} (hκ : IsChange κ σ) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : Continuous ψ) {S : Type} [AddCommGroup S] [Module ℂ S] {ev : S →ₗ[ℂ] (WA V W → ℂ)}
    {E : S ≃ₗ[ℂ] HeisenbergWeilMatrices.Theta ψ A B} (hE : ∀ Φ, ev Φ ∘ κ = E Φ) : Set.range ev = {f | IsThetaFun ψ V W f} := by
  ext f
  rw [Set.mem_ofPred_eq, theta_iff hκ hψ]
  constructor
  · rintro ⟨Φ, rfl⟩
    rw [hE]; exact (E Φ).2
  · intro h
    obtain ⟨Φ, hΦ⟩ := E.surjective ⟨_, h⟩
    exact ⟨Φ, κ.surjective.injective_comp_right ((hE Φ).trans (congrArg Subtype.val hΦ))⟩

theorem scalar_eq {A B : HSp D} (hr : A.rank ≤ B.rank) (c c' : (AE D)ˣ →* Circle) {v e} (he : HeisenbergWeilMatrices.IsSplitIdem D v e)
    (g : GA D A) (h : GA D B) : HeisenbergWeilMatrices.splitScalar A B c c' he (g, h) = (HeisenbergWeilMatrices.splitMod A B v e (g, h) : ℂ) *
      (splitFac A B c c' (HeisenbergWeilMatrices.atIdem he.idem (HeisenbergWeilMatrices.detA A g)) (HeisenbergWeilMatrices.atIdem he.idem (HeisenbergWeilMatrices.detA B h)) : ℂ) := by
  unfold splitFac
  rw [if_pos hr, mul_comm]
  rfl

theorem exists_rel (C : SplittingKernelQuotients.Core T) : ∃ ev om, (∀ V W, Function.Injective (ev V W)) ∧ Rel C ev om := by
  classical
  have h1 : ∀ V W : HSp D, ∃ ev : X.Sch V W →ₗ[ℂ] (WA V W → ℂ), Function.Injective ev ∧
      (∀ hr : V.rank < W.rank, ∀ Φ, ev Φ ∘ kap V W = C.eUp V W hr.le Φ) ∧
      ∀ hr : W.rank < V.rank, ∀ Φ, ev Φ ∘ kapT W V = C.eDn W V hr Φ := by
    intro V W
    rcases le_or_gt V.rank W.rank with h | h
    · refine ⟨LinearMap.funLeft ℂ ℂ (kap V W).symm ∘ₗ (Submodule.subtype _) ∘ₗ (C.eUp V W h).toLinearMap,
        fun Φ Φ' e => (C.eUp V W h).injective (Subtype.ext ((kap V W).symm.surjective.injective_comp_right e)),
        fun _ Φ => funext fun x => congrArg (C.eUp V W h Φ : WA V W → ℂ) ((kap V W).symm_apply_apply x),
        fun hr => absurd h (not_le.2 hr)⟩
    · refine ⟨LinearMap.funLeft ℂ ℂ (kapT W V).symm ∘ₗ (Submodule.subtype _) ∘ₗ (C.eDn W V h).toLinearMap,
        fun Φ Φ' e => (C.eDn W V h).injective (Subtype.ext ((kapT W V).symm.surjective.injective_comp_right e)),
        fun hr => absurd h (not_lt.2 hr.le),
        fun _ Φ => funext fun x => congrArg (C.eDn W V h Φ : WA W V → ℂ) ((kapT W V).symm_apply_apply x)⟩
  have h2 : ∀ (V W : HSp D) (χ χ' : X.Chr), ∃ om : GA D V × GA D W →* Module.End ℂ (X.Sch V W),
      (∀ (hr : V.rank < W.rank) hs g h, om (g, h) = C.omUp V W hr.le χ χ' hs (g, h)) ∧
      ∀ (hr : W.rank < V.rank) hs g h, om (g, h) = C.omDn W V hr χ' χ hs (h, g) := by
    intro V W χ χ'
    by_cases hs : SplittingKernelQuotients.IsSplitting V W (T.eChr χ) (T.eChr χ')
    · rcases le_or_gt V.rank W.rank with h | h
      · exact ⟨(C.eUp V W h).symm.conjRingEquiv.toMonoidHom.comp (C.om V W h χ χ' hs), fun _ _ _ _ => rfl,
          fun hr => absurd h (not_le.2 hr)⟩
      · exact ⟨((C.eDn W V h).symm.conjRingEquiv.toMonoidHom.comp (C.om W V h.le χ' χ hs.symm)).comp
          MulEquiv.prodComm.toMonoidHom, fun hr => absurd h (not_lt.2 hr.le), fun _ _ _ _ => rfl⟩
    · exact ⟨1, fun _ h => absurd h hs, fun _ h => absurd h.symm hs⟩
  choose ev h11 h12 h13 using h1
  choose om h21 h22 using h2
  exact ⟨ev, om, h11, fun A B hr => ⟨h12 A B hr, h13 B A hr, fun χA χB hs g h =>
    ⟨h21 A B χA χB hr hs g h, h22 B A χB χA hr hs h g⟩⟩⟩

section Build

variable {C : SplittingKernelQuotients.Core T} {ev : ∀ V W, X.Sch V W →ₗ[ℂ] (WA V W → ℂ)}
  {om : ∀ V W, X.Chr → X.Chr → (GA D V × GA D W →* Module.End ℂ (X.Sch V W))}

theorem Rel.splitUp (R : Rel C ev om) {A B : HSp D} (hr : A.rank < B.rank) {χ χ'}
    (hs : SplittingKernelQuotients.IsSplitting A B (T.eChr χ) (T.eChr χ')) {v e} (he : HeisenbergWeilMatrices.IsSplitIdem D v e) {g h}
    (hg : SuppAt e A g) (hh : SuppAt e B h) {x y} (hx : IsDetAt e A g x) (hy : IsDetAt e B h y) :
    HeisenbergWeilMatrices.ActsBy e (C.om A B hr.le χ χ' hs (g, h))
      ((HeisenbergWeilMatrices.splitMod A B v e (g, h) : ℂ) * (splitFac A B (T.eChr χ) (T.eChr χ') x y : ℂ)) := by
  rw [(isDetAt_iff he.idem A g x).1 hx, (isDetAt_iff he.idem B h y).1 hy, ← scalar_eq hr.le]
  exact (C.om_weil A B hr.le χ χ' hs).split v e he (g, h) ((suppAt_iff he A g).1 hg) ((suppAt_iff he B h).1 hh)

def Rel.tied (R : Rel C ev om) (hi : ∀ V W, Function.Injective (ev V W)) (tw : Twist C) : WeilTied D X T where
  ψ := C.ψ
  ψ_std := (stdChar_iff _).2 C.ψ_std
  evS := ev
  evS_inj := hi
  evS_range V W hne := by
    rcases lt_or_gt_of_ne hne with hr | hr
    · exact range_eq (isChange_kap hr.le) C.ψ_std.1.1 (R V W hr).1
    · exact range_eq (isChange_kapT hr) C.ψ_std.1.1 (R W V hr).2.1
  om := om
  om_heis V W χ χ' hne h1 h2 g h := by
    have hs := (split_iff V W χ χ').2 ⟨h1, h2⟩
    rcases lt_or_gt_of_ne hne with hr | hr
    · exact (impl_iff (isChange_kap hr.le) (R V W hr).1 (R.up hr hs g h) g h).2 ((C.om_weil _ _ _ _ _ hs).impl _)
    · exact (impl_iff (isChange_kapT hr) (R W V hr).2.1 (R.dn hr hs.symm h g) g h).2
        ((C.om_weil _ _ _ _ _ hs.symm).impl _)
  om_aut V W χ χ' hne h1 h2 γ hγ γ' hγ' Φ := by
    have hs := (split_iff V W χ χ').2 ⟨h1, h2⟩
    rcases lt_or_gt_of_ne hne with hr | hr
    · rw [R.kernUp hr hs, ev_zero (R V W hr).1]
      exact (C.om_weil _ _ _ _ _ hs).rat γ hγ γ' hγ' _
    · rw [R.kernDn hr hs.symm, ev_zero (R W V hr).2.1]
      exact (C.om_weil _ _ _ _ _ hs.symm).rat γ' hγ' γ hγ _
  om_cont V W χ χ' hne h1 h2 Φ w := by
    have hs := (split_iff V W χ χ').2 ⟨h1, h2⟩
    rcases lt_or_gt_of_ne hne with hr | hr
    · obtain ⟨x, rfl⟩ := (kap V W).surjective w
      refine ((C.om_weil V W hr.le _ _ hs).cont (C.eUp V W hr.le Φ) x).congr fun p => ?_
      rw [← R.up hr hs p.1 p.2, ← (R V W hr).1]; rfl
    · obtain ⟨x, rfl⟩ := (kapT W V).surjective w
      refine (((C.om_weil W V hr.le _ _ hs.symm).cont (C.eDn W V hr Φ) x).comp continuous_swap).congr fun p => ?_
      have := congrFun ((R W V hr).2.1 (om V W χ χ' (p.1, p.2) Φ)) x
      rw [R.dn hr hs.symm p.2 p.1] at this
      exact this.symm
  om_unit V W χ χ' hne h1 h2 μ 𝓕 hμ hF p Φ := by
    have hs := (split_iff V W χ χ').2 ⟨h1, h2⟩
    rcases lt_or_gt_of_ne hne with hr | hr
    · refine (unit_iff (isChange_kap hr.le) (R V W hr).1 C.ψ_std.1 hr.le Φ (om V W χ χ' (p.1, p.2) Φ)).2 ?_ μ 𝓕 hμ hF
      rw [R.up hr hs]
      exact (C.om_weil _ _ _ _ _ hs).unitary _ _
    · refine (unit_iff (isChange_kapT hr) (R W V hr).2.1 C.ψ_std.1 hr.le Φ (om V W χ χ' (p.1, p.2) Φ)).2 ?_ μ 𝓕 hμ hF
      rw [R.dn hr hs.symm]
      exact (C.om_weil _ _ _ _ _ hs.symm).unitary _ _
  om_split V W χ χ' hne h1 h2 e he g h hg hh x y hx hy := by
    have hs := (split_iff V W χ χ').2 ⟨h1, h2⟩
    obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 he
    rcases lt_or_gt_of_ne hne with hr | hr
    · exact ⟨_, splitMod_pos he V W (g, h), (actsBy_iff (isChange_kap hr.le) (R V W hr).1 (R.up hr hs g h) e _).2
        (R.splitUp hr hs he hg hh hx hy)⟩
    · refine ⟨_, splitMod_pos he W V (h, g), ?_⟩
      rw [← splitFac_swap V W hne]
      exact (actsBy_iff (isChange_kapT hr) (R W V hr).2.1 (R.dn hr hs.symm h g) e _).2
        (R.splitUp hr hs.symm he hh hg hy hx)
  om_tw := R.twRule_iff.2 tw
  om_swap V W χ χ' hne h1 h2 g h Φ Φ' H := by
    have hs := (split_iff V W χ χ').2 ⟨h1, h2⟩
    rcases lt_or_gt_of_ne hne with hr | hr
    · rw [R.transpose_iff hr] at H ⊢
      rw [R.up hr hs, R.dn hr hs, H]
    · rw [R.transpose_iff' hr] at H ⊢
      rw [R.up hr hs.symm, R.dn hr hs.symm, H]
  th V W χ χ' hne h1 h2 hsig μ 𝓕 hv Φ F h := by
    have hs := (split_iff V W χ χ').2 ⟨h1, h2⟩
    rcases lt_or_gt_of_ne hne with hr | hr
    · simp only [R.kernUp hr hs]
      exact ((C.thUp V W hr.le χ χ' hs hsig Φ F h).2 (μ, 𝓕) hv).2
    · simp only [R.kernDn hr hs.symm]
      exact ((C.thDn W V hr χ' χ hs.symm hsig Φ F h).2 (μ, 𝓕) hv).2

end Build

theorem exists_tied (C : SplittingKernelQuotients.Core T) (tw : Twist C) : ∃ Wl : WeilTied D X T, Match Wl C := by
  obtain ⟨ev, om, hi, R⟩ := exists_rel C
  exact ⟨R.tied hi tw, rfl, R⟩

theorem isWeil_of_tied (Wl : WeilTied D X T) (hm : ExactModulus Wl) {A B : HSp D} (hr : A.rank < B.rank) {χA χB}
    (hs : SplittingKernelQuotients.IsSplitting A B (T.eChr χA) (T.eChr χB)) {E : X.Sch A B ≃ₗ[ℂ] HeisenbergWeilMatrices.Theta Wl.ψ A B}
    (hE : ∀ Φ, Wl.evS A B Φ ∘ kap A B = E Φ) {N : SplittingKernelQuotients.Rep Wl.ψ A B}
    (hN : ∀ p Φ, E (Wl.om A B χA χB p Φ) = N p (E Φ)) : HeisenbergWeilMatrices.IsWeil Wl.ψ (T.eChr χA) (T.eChr χB) N := by
  have hκ := isChange_kap hr.le
  refine ⟨fun p => ?_, fun p f => ?_, fun f w => ?_, fun g hg h hh f => ?_, fun v e he p hg hh => ?_⟩
  · exact (impl_iff hκ hE (hN p) p.1 p.2).1 (Wl.om_heis A B χA χB hr.ne hs.resA hs.resB p.1 p.2)
  · obtain ⟨Φ, rfl⟩ := E.surjective f
    rw [← hN]
    exact (unit_iff hκ hE Wl.ψ_std.1 hr.le _ _).1 fun μ 𝓕 hμ hF =>
      Wl.om_unit A B χA χB hr.ne hs.resA hs.resB μ 𝓕 hμ hF p Φ
  · obtain ⟨Φ, rfl⟩ := E.surjective f
    refine (Wl.om_cont A B χA χB hr.ne hs.resA hs.resB Φ (kap A B w)).congr fun p => ?_
    rw [← hN, ← hE]; rfl
  · obtain ⟨Φ, rfl⟩ := E.surjective f
    rw [← hN]
    exact (ev_zero hE _).symm.trans ((Wl.om_aut A B χA χB hr.ne hs.resA hs.resB g hg h hh Φ).trans (ev_zero hE _))
  · obtain ⟨g, h⟩ := p
    rw [scalar_eq hr.le]
    exact (actsBy_iff hκ hE (hN _) e _).1 (hm A B χA χB hr hs.resA hs.resB v e he g h ((suppAt_iff he A g).2 hg)
      ((suppAt_iff he B h).2 hh) _ _ ((isDetAt_iff he.idem A g _).2 rfl) ((isDetAt_iff he.idem B h _).2 rfl))

theorem exists_core_with (Wl : WeilTied D X T) (hm : ExactModulus Wl) (hc : Converges Wl)
    {P : ∀ A B : HSp D, (X.Sch A B → WA A B → ℂ) → Prop} (he : EqualRankWith T Wl.ψ P) :
    ∃ C : SplittingKernelQuotients.Core T, Match Wl C ∧
      ∀ (A B : HSp D) (hr : A.rank = B.rank), P A B fun Φ => (C.eUp A B hr.le Φ : WA A B → ℂ) := by
  have h1 : ∀ A B : HSp D, A.rank ≤ B.rank → ∃ E : X.Sch A B ≃ₗ[ℂ] HeisenbergWeilMatrices.Theta Wl.ψ A B,
      (A.rank = B.rank → P A B fun Φ => (E Φ : WA A B → ℂ)) ∧
      (A.rank < B.rank → ∀ Φ, Wl.evS A B Φ ∘ kap A B = E Φ) ∧
      ∀ χA χB, SplittingKernelQuotients.IsSplitting A B (T.eChr χA) (T.eChr χB) → ∃ om : SplittingKernelQuotients.Rep Wl.ψ A B,
        (A.rank < B.rank → ∀ p Φ, E (Wl.om A B χA χB p Φ) = om p (E Φ)) ∧
        HeisenbergWeilMatrices.IsWeil Wl.ψ (T.eChr χA) (T.eChr χB) om ∧ (A.SigOK → ∀ (Φ : X.Sch A B) (φ : X.cusp A) (h : GA D B),
          SplittingKernelQuotients.IsQuotInt A (T.petC A) (fun g => SplittingKernelQuotients.kern om (E Φ) g h * T.ev A (φ : X.AF A) g)
            (T.ev B (X.th A B χA χB Φ φ) h)) := by
    intro A B hle
    rcases hle.eq_or_lt with hr | hr
    · obtain ⟨E, hP, hE⟩ := he A B hr
      refine ⟨E, fun _ => hP, fun h => absurd hr h.ne, fun χA χB hs => ?_⟩
      obtain ⟨om, ho⟩ := hE χA χB hs
      exact ⟨om, fun h => absurd hr h.ne, ho⟩
    · obtain ⟨E, hE⟩ := exists_equiv (isChange_kap hle) Wl.ψ_std.1.1 _ (Wl.evS_inj A B) (Wl.evS_range A B hr.ne)
      refine ⟨E, fun h => absurd h hr.ne, fun _ => hE, fun χA χB hs => ?_⟩
      obtain ⟨N, hN⟩ : ∃ N : SplittingKernelQuotients.Rep Wl.ψ A B, ∀ p Φ, E (Wl.om A B χA χB p Φ) = N p (E Φ) :=
        ⟨E.conjRingEquiv.toMonoidHom.comp (Wl.om A B χA χB), fun p Φ =>
          congrArg (fun y => E (Wl.om A B χA χB p y)) (E.symm_apply_apply Φ).symm⟩
      refine ⟨N, fun _ => hN, isWeil_of_tied Wl hm hr hs hE hN, fun hsig Φ φ h => ?_⟩
      have k : ∀ g, SplittingKernelQuotients.kern N (E Φ) g h = Wl.evS A B (Wl.om A B χA χB (g, h) Φ) 0 := fun g => by
        rw [ev_zero hE, hN]; rfl
      have c := hc A B χA χB hr.ne hs.resA hs.resB hsig
      simp only [k]
      exact ⟨c.1, fun m hv => ⟨c.2 m hv Φ φ h, Wl.th A B χA χB hr.ne hs.resA hs.resB hsig m.1 m.2 hv Φ φ h⟩⟩
  choose eUp h10 h11 om h12 h13 h14 using h1
  choose eDn h2 using fun (A B : HSp D) (hr : A.rank < B.rank) =>
    exists_equiv (isChange_kapT hr) Wl.ψ_std.1.1 _ (Wl.evS_inj B A) (Wl.evS_range B A hr.ne')
  have dn : ∀ (A B : HSp D) (hr : A.rank < B.rank) χA χB hs g h Φ,
      eDn A B hr (Wl.om B A χB χA (h, g) Φ) = om A B hr.le χA χB hs (g, h) (eDn A B hr Φ) := by
    intro A B hr χA χB hs g h Φ
    have t : ∀ Φ Φ', (∀ x : WA A B, Wl.evS B A Φ' xᵀ = Wl.evS A B Φ x) ↔ eDn A B hr Φ' = eUp A B hr.le Φ := by
      intro Φ Φ'
      rw [(kap A B).surjective.forall, Subtype.ext_iff, ← h11 A B hr.le hr, ← h2, funext_iff]
      rfl
    obtain ⟨Φ₀, h0⟩ := (eUp A B hr.le).surjective (eDn A B hr Φ)
    rw [← h0, ← h12 A B hr.le χA χB hs hr, ← t]
    exact Wl.om_swap A B χA χB hr.ne hs.resA hs.resB g h Φ₀ Φ ((t _ _).2 h0.symm)
  refine ⟨⟨Wl.ψ, (stdChar_iff _).1 Wl.ψ_std, eUp, eDn, om, h13, h14, fun A B hr χA χB hs hsig Φ G g => ?_⟩, ⟨rfl,
    fun A B hr => ⟨h11 A B hr.le hr, h2 A B hr, fun χA χB hs g h => ⟨?_, ?_⟩⟩⟩, fun A B hr => h10 A B hr.le hr⟩
  · have k : ∀ h, SplittingKernelQuotients.kern (om A B hr.le χA χB hs) (eDn A B hr Φ) g h = Wl.evS B A (Wl.om B A χB χA (h, g) Φ) 0 :=
      fun h => by rw [ev_zero (h2 A B hr), dn A B hr χA χB hs]; rfl
    have c := hc B A χB χA hr.ne' hs.resB hs.resA hsig
    simp only [k]
    exact ⟨c.1, fun m hv => ⟨c.2 m hv Φ G g, Wl.th B A χB χA hr.ne' hs.resB hs.resA hsig m.1 m.2 hv Φ G g⟩⟩
  · exact LinearMap.ext fun Φ => (LinearEquiv.eq_symm_apply _).2 (h12 A B hr.le χA χB hs hr _ Φ)
  · exact LinearMap.ext fun Φ => (LinearEquiv.eq_symm_apply _).2 (dn A B hr χA χB hs g h Φ)

theorem exists_core (Wl : WeilTied D X T) (hm : ExactModulus Wl) (hc : Converges Wl) (he : EqualRank T Wl.ψ) :
    ∃ C : SplittingKernelQuotients.Core T, Match Wl C :=
  (exists_core_with Wl hm hc (P := fun _ _ _ => True) fun A B hr => (he A B hr).imp fun _ h => ⟨trivial, h⟩).imp
    fun _ h => h.1

open Classical in

def junkSig (X : ThetaX D) (J : ∀ V W, X.Sch V W →ₗ[ℂ] X.cusp V →ₗ[ℂ] X.AF W) : ThetaX D :=
  { X with th := fun V W χ χ' => if V.SigOK then X.th V W χ χ' else J V W }

structure Beyond (Wl : WeilTied D X T) : Prop where
  modulus : ExactModulus Wl
  converges : Converges Wl
  equalRank : EqualRankPure T Wl.ψ
  fact : FactPure Wl
  offChars : SplittingKernelQuotients.OffChars T
  offSig : SplittingKernelQuotients.OffSig X

end GlobalTheory.WeilTieCompare

end
end
