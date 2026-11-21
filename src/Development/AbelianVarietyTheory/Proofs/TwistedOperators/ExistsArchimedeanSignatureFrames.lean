import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Adapted
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BranchingHypothesesGridParametersLargeScale
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbLEqEmbOptL
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsKStableOfMemLowKSub
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryEmbeddingStabilizer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryStabiliserEmbeddingNormLaws
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DKerHasCompactSupport

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PackFrame

open GlobalTheory.PackLoc

section Lin

variable {m N : ℕ} (e : Option (Fin m) ≃ Fin N)

theorem embOpt_mul (h k : Matrix (Fin m) (Fin m) ℂ) : embOpt e (h * k) = embOpt e h * embOpt e k := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [Matrix.mul_apply, ← e.sum_comp, Fintype.sum_option]
  cases a <;> cases b <;> simp [embOpt, Matrix.mul_apply]

theorem embOpt_ct (h : Matrix (Fin m) (Fin m) ℂ) : embOpt e hᴴ = (embOpt e h)ᴴ := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  cases a <;> cases b <;> simp [embOpt]

theorem embOpt_Jm {εA : Fin m → Bool} {ε : Fin N → Bool} (h0 : ε (e none) = true) (h1 : ∀ i, ε (e (some i)) = εA i) :
    Formalism.REAL.Jm ε = embOpt e (Formalism.REAL.Jm εA) := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  cases a <;> cases b <;> simp [embOpt, Formalism.REAL.Jm, Matrix.diagonal_apply, h0, h1]

theorem embOpt_unit {h : Matrix (Fin m) (Fin m) ℂ} (hh : IsUnit h) : IsUnit (embOpt e h) := by
  obtain ⟨k, hk⟩ := hh.exists_right_inv
  exact IsUnit.of_mul_eq_one (embOpt e k) (by rw [← embOpt_mul, hk, embOpt_one])

theorem embOpt_inv {h : Matrix (Fin m) (Fin m) ℂ} (hh : IsUnit h) : (embOpt e h)⁻¹ = embOpt e h⁻¹ :=
  Matrix.inv_eq_right_inv (by
    rw [← embOpt_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hh), embOpt_one])

theorem Jm_unit (ε : Fin m → Bool) : IsUnit (Formalism.REAL.Jm ε) := by
  refine IsUnit.of_mul_eq_one (Formalism.REAL.Jm ε) ?_
  rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext a; split_ifs <;> simp

def vecOpt (y : Fin m → ℂ) (a : ℂ) : Fin N → ℂ := fun b => (e.symm b).elim a y

theorem embOpt_vec (h : Matrix (Fin m) (Fin m) ℂ) (y : Fin m → ℂ) (a : ℂ) :
    embOpt e h *ᵥ vecOpt e y a = vecOpt e (h *ᵥ y) a := by
  funext b
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [Matrix.mulVec, dotProduct, ← e.sum_comp, Fintype.sum_option]
  cases b <;> simp [embOpt, vecOpt, Matrix.mulVec, dotProduct]

theorem eu_vecOpt (y : Fin m → ℂ) (a : ℂ) : eu (vecOpt e y a) ^ 2 = eu y ^ 2 + ‖a‖ ^ 2 := by
  unfold eu
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), ← e.sum_comp, Fintype.sum_option, add_comm]
  simp [vecOpt]

theorem vecOpt_zero_one : vecOpt e 0 1 = Pi.single (e none) 1 := by
  funext b
  obtain ⟨b, rfl⟩ := e.surjective b
  cases b <;> simp [vecOpt, Pi.single_apply]

def colM (F : Matrix (Fin N) (Fin m) ℂ) (z : Matrix (Fin N) (Fin 1) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i b => (e.symm b).elim (z i 0) (F i)

variable (F : Matrix (Fin N) (Fin m) ℂ) (z : Matrix (Fin N) (Fin 1) ℂ)

theorem colM_vec (y : Fin m → ℂ) (a : ℂ) : colM e F z *ᵥ vecOpt e y a = F *ᵥ y + a • fun i => z i 0 := by
  funext i
  rw [Matrix.mulVec, dotProduct, ← e.sum_comp, Fintype.sum_option]
  simp [colM, vecOpt, Matrix.mulVec, dotProduct, add_comm, mul_comm]

theorem mul_colM (g : Matrix (Fin N) (Fin N) ℂ) : g * colM e F z = colM e (g * F) (g * z) := by
  ext i b
  obtain ⟨b, rfl⟩ := e.surjective b
  cases b <;> simp [colM, Matrix.mul_apply]

theorem colM_mul (h : Matrix (Fin m) (Fin m) ℂ) : colM e F z * embOpt e h = colM e (F * h) z := by
  ext i b
  obtain ⟨b, rfl⟩ := e.surjective b
  rw [Matrix.mul_apply, ← e.sum_comp, Fintype.sum_option]
  cases b <;> simp [colM, embOpt, Matrix.mul_apply]

theorem colM_gram (J : Matrix (Fin N) (Fin N) ℂ) (h1 : Fᴴ * J * z = 0) (h2 : zᴴ * J * F = 0) (h3 : zᴴ * J * z = 1) :
    (colM e F z)ᴴ * J * colM e F z = embOpt e (Fᴴ * J * F) := by
  rw [Matrix.mul_assoc] at h1 h2 h3 ⊢
  rw [Matrix.mul_assoc, mul_colM]
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  cases a with
  | none => cases b with
    | none => simpa [colM, embOpt, Matrix.mul_apply (M := _ᴴ)] using congrFun (congrFun h3 0) 0
    | some b => simpa [colM, embOpt, Matrix.mul_apply (M := _ᴴ)] using congrFun (congrFun h2 0) b
  | some a => cases b with
    | none => simpa [colM, embOpt, Matrix.mul_apply (M := _ᴴ)] using congrFun (congrFun h1 a) 0
    | some b => simp [colM, embOpt, Matrix.mul_apply (M := _ᴴ)]

theorem exists_frame (J : Matrix (Fin N) (Fin N) ℂ) (h1 : Fᴴ * J * z = 0) (h2 : zᴴ * J * F = 0) (h3 : zᴴ * J * z = 1)
    (εA : Fin m → Bool) (A : Matrix (Fin m) (Fin m) ℂ) (ε : Fin N → Bool) (hA : IsUnit A)
    (hG : Aᴴ * Formalism.REAL.Jm εA * A = Fᴴ * J * F) (h0 : ε (e none) = true) (hε : ∀ i, ε (e (some i)) = εA i) :
    ∃ B : Matrix (Fin N) (Fin N) ℂ, IsUnit B ∧ Bᴴ * Formalism.REAL.Jm ε * B = J ∧
      (∀ (y : Fin m → ℂ) (a : ℂ), eu (B *ᵥ (F *ᵥ y + a • fun i => z i 0)) ^ 2 = eu (A *ᵥ y) ^ 2 + ‖a‖ ^ 2) ∧
      B *ᵥ (fun i => z i 0) = Pi.single (e none) 1 ∧
      ∀ (g : Matrix (Fin N) (Fin N) ℂ) (h : Matrix (Fin m) (Fin m) ℂ), g * F = F * h → g * z = z →
        B * g * B⁻¹ = embOpt e (A * h * A⁻¹) := by
  set M := colM e F z with hM
  set C := embOpt e A with hC
  have hCu : IsUnit C := embOpt_unit e hA
  have hg : Mᴴ * J * M = Cᴴ * Formalism.REAL.Jm ε * C := by
    rw [hM, colM_gram e F z J h1 h2 h3, ← hG, embOpt_mul, embOpt_mul, embOpt_ct, embOpt_Jm e h0 hε]
  have hMu : IsUnit M := by
    have : IsUnit (Mᴴ * J * M) := by
      rw [hg]; exact (((Matrix.isUnit_conjTranspose _).2 hCu).mul (Jm_unit ε)).mul hCu
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at this
    exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right this)
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hMu
  have hMi : IsUnit M⁻¹ := Matrix.isUnit_nonsing_inv_iff.2 hMu
  have key : ∀ y a, (C * M⁻¹) *ᵥ (F *ᵥ y + a • fun i => z i 0) = vecOpt e (A *ᵥ y) a := by
    intro y a
    rw [← colM_vec e, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul_cancel_right _ _ hd, embOpt_vec]
  refine ⟨C * M⁻¹, hCu.mul hMi, ?_, fun y a => ?_, ?_, fun g h e1 e2 => ?_⟩
  · calc (C * M⁻¹)ᴴ * Formalism.REAL.Jm ε * (C * M⁻¹) = (M⁻¹)ᴴ * (Cᴴ * Formalism.REAL.Jm ε * C) * M⁻¹ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (M * M⁻¹)ᴴ * J * (M * M⁻¹) := by
          rw [← hg, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Matrix.mul_nonsing_inv _ hd]; simp
  · rw [key, eu_vecOpt]
  · have := key 0 1
    simpa [vecOpt_zero_one] using this
  · have e3 : g * M = M * embOpt e h := by rw [hM, mul_colM, colM_mul, e1, e2]
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hd, embOpt_mul, embOpt_mul, ← embOpt_inv e hA, ← hC]
    calc C * M⁻¹ * g * (M * C⁻¹) = C * (M⁻¹ * (g * M)) * C⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [e3, Matrix.nonsing_inv_mul_cancel_left _ _ hd]

end Lin

variable {D : D7}

theorem map_cT_tau (τ : D.what₂.Tau) {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E) :
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X).map (tauE D τ) = (X.map (tauE D τ))ᴴ := by
  ext a b
  exact GlobalTheory.FockCompare.tauE_star τ _

theorem map_incA_tau {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E) :
    (X.map (incA D)).map ((θ τ).comp (infPart D)) = X.map (tauE D τ) := by
  ext a b
  exact GlobalTheory.FockCompare.comp_incA hθ τ _

theorem exists_adapted_frame : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (τ : D.what₂.Tau)
  (εA : Fin Y.rank → Bool) (A : Matrix (Fin Y.rank) (Fin Y.rank) ℂ) (ε : Fin V.rank → Bool)
  (e : Option (Fin Y.rank) ≃ Fin V.rank),
  IsUnit A → Aᴴ * Formalism.REAL.Jm εA * A = gramAt D Y τ → ε (e none) = true → (∀ i, ε (e (some i)) = εA i) →
  ∃ B : Matrix (Fin V.rank) (Fin V.rank) ℂ, IsUnit B ∧ Bᴴ * Formalism.REAL.Jm ε * B = gramAt D V τ ∧
    (∀ (y : Fin Y.rank → ℂ) (a : ℂ),
      eu (B *ᵥ ((frameMat V Y d.ι).map (tauE D τ) *ᵥ y + a • fun i => tauE D τ (zv d i))) ^ 2 = eu (A *ᵥ y) ^ 2 + ‖a‖ ^ 2) ∧
    B *ᵥ (fun i => tauE D τ (zv d i)) = Pi.single (e none) 1 ∧
    (∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ), GlobalTheory.PackLoc.embAt θ d τ h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) ∧
    ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ), B * GlobalTheory.PackLoc.embAt θ d τ h * B⁻¹ = GlobalTheory.PackLoc.embOpt e (A * h * A⁻¹) := by
  intro D θ hθ Y V d τ εA A ε e hA hG h0 hε
  have h1 := congrArg (fun X => X.map (tauE D τ)) d.perp
  have h2 := congrArg (fun X => X.map (tauE D τ)) (GlobalTheory.UnitaryEmbeddingGroup.perp' d)
  have h3 := congrArg (fun X => X.map (tauE D τ)) d.gram
  have h4 := congrArg (fun X => X.map (tauE D τ)) (GlobalTheory.AutFunCounterexample.gram_pull V Y d.ι d.isom)
  simp only [Matrix.map_mul, map_cT_tau, Matrix.map_zero _ (map_zero _)] at h1 h2 h3 h4
  have h5 : (antiDiagonalSignGramMatrix 1 (1 : D.host.E)).map (tauE D τ) = 1 := by
    ext a b
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]; simp [antiDiagonalSignGramMatrix]
  rw [h5] at h3
  obtain ⟨B, b1, b2, b3, b4, b5⟩ := exists_frame e _ _ _ h1 h2 h3 εA A ε hA (hG.trans h4.symm) h0 hε
  refine ⟨B, b1, b2, b3, b4, fun h _ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V _ τ, fun h hh => b5 _ h ?_ ?_⟩
  · have k1 := congrArg (fun X => X.map ((θ τ).comp (infPart D))) ((embRel_iff d (atTau θ Y τ h) _).2 rfl).1
    have k2 := (GlobalTheory.PointAtPlaceHom.atTau_spec hθ Y τ hh).2.1
    simp only [Matrix.map_mul, map_incA_tau hθ] at k1
    rw [GlobalTheory.FockCompare.RealAction.infMat_eq] at k2
    exact k1.trans (congrArg _ k2)
  · have k1 := congrArg (fun X => X.map ((θ τ).comp (infPart D))) (GlobalTheory.UnitaryEmbeddingGroup.unitaryEmbedding_fixes_vectors d (atTau θ Y τ h))
    simp only [Matrix.map_mul, map_incA_tau hθ] at k1
    exact k1

end GlobalTheory.PackFrame

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_signature_matrix_extension : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (τ : D.what₂.Tau)
  (εA : Fin Y.rank → Bool) (A : Matrix (Fin Y.rank) (Fin Y.rank) ℂ) (ε : Fin V.rank → Bool)
  (e : Option (Fin Y.rank) ≃ Fin V.rank),
  IsUnit A → Aᴴ * Formalism.REAL.Jm εA * A = gramAt D Y τ → ε (e none) = true → (∀ i, ε (e (some i)) = εA i) →
  ∃ B : Matrix (Fin V.rank) (Fin V.rank) ℂ, IsUnit B ∧ Bᴴ * Formalism.REAL.Jm ε * B = gramAt D V τ ∧
    (∀ (y : Fin Y.rank → ℂ) (a : ℂ),
      eu (B *ᵥ ((frameMat V Y d.ι).map (tauE D τ) *ᵥ y + a • fun i => tauE D τ (zv d i))) ^ 2 = eu (A *ᵥ y) ^ 2 + ‖a‖ ^ 2) ∧
    B *ᵥ (fun i => tauE D τ (zv d i)) = Pi.single (e none) 1 ∧
    (∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ), GlobalTheory.PackLoc.embAt θ d τ h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) ∧
    ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ), B * GlobalTheory.PackLoc.embAt θ d τ h * B⁻¹ = GlobalTheory.PackLoc.embOpt e (A * h * A⁻¹) := by
  atlas_forward_decl GlobalTheory.PackFrame.exists_adapted_frame
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HaarRev

theorem haar_rev : ∀ (m : ℕ) (ε : Fin m → Bool), ∃ lam : ℝ, 0 < lam ∧
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Matrix (Fin m) (Fin m) ℂ → E),
    (Integrable (fun u : Formalism.REAL.UJ ε => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) (Formalism.REAL.muG ε) ↔
      Integrable (fun h : Formalism.REAL.UJ (fun a => ε a.rev) => F (Formalism.MainNotions.S.umat h)) (Formalism.REAL.muG (fun a => ε a.rev))) ∧
    ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG ε) =
      lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG (fun a => ε a.rev)) := by
  intro m ε
  set ε' : Fin m → Bool := fun a => ε a.rev with hε'
  have he : ∀ a, ε' a = ε a.rev := fun a => rfl
  let φ : Formalism.REAL.UJ ε ≃* Formalism.REAL.UJ ε' := GlobalTheory.ConjDS.rvU (GlobalTheory.ConjDS.sg_symm he)
  have hφ : Continuous φ := GlobalTheory.ConjDS.rvU_cont _
  have hφs : Continuous φ.symm := GlobalTheory.ConjDS.rvU_cont he
  haveI : ((Formalism.REAL.muG ε).map φ).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map _ φ hφ hφs
  set c := Measure.haarScalarFactor ((Formalism.REAL.muG ε).map φ) (Formalism.REAL.muG ε') with hc
  have hmap : (Formalism.REAL.muG ε).map φ = c • Formalism.REAL.muG ε' :=
    Measure.isMulLeftInvariant_eq_smul _ _
  have hc0 : c ≠ 0 := by
    intro h0
    have : (Formalism.REAL.muG ε).map φ = 0 := by rw [hmap, h0, zero_smul]
    exact (Measure.IsHaarMeasure.toIsOpenPosMeasure (μ := (Formalism.REAL.muG ε).map φ)).open_pos _ isOpen_univ
      Set.univ_nonempty (by rw [this]; rfl)
  let e : Formalism.REAL.UJ ε ≃ᵐ Formalism.REAL.UJ ε' :=
    { toEquiv := φ.toEquiv, measurable_toFun := hφ.measurable, measurable_invFun := hφs.measurable }
  have he' : ⇑e = ⇑φ := rfl
  refine ⟨(c : ℝ), by positivity, ?_⟩
  intro E _ _ F
  have hcomp : (fun u : Formalism.REAL.UJ ε => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) =
      (fun h : Formalism.REAL.UJ ε' => F (Formalism.MainNotions.S.umat h)) ∘ e := rfl
  constructor
  · rw [hcomp, ← integrable_map_equiv e, he', hmap, ENNReal.smul_def]
    exact integrable_smul_measure (by simpa using hc0) ENNReal.coe_ne_top
  · show ∫ u, F (Formalism.MainNotions.S.umat (e u)) ∂(Formalism.REAL.muG ε) = _
    rw [← integral_map_equiv e (fun h : Formalism.REAL.UJ ε' => F (Formalism.MainNotions.S.umat h)), he', hmap, integral_smul_nnreal_measure, NNReal.smul_def]

end GlobalTheory.HaarRev
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_haar_coordinate_reversal_positive_multiple : ∀ (m : ℕ) (ε : Fin m → Bool), ∃ lam : ℝ, 0 < lam ∧
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Matrix (Fin m) (Fin m) ℂ → E),
    (Integrable (fun u : Formalism.REAL.UJ ε => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) (Formalism.REAL.muG ε) ↔
      Integrable (fun h : Formalism.REAL.UJ (fun a => ε a.rev) => F (Formalism.MainNotions.S.umat h)) (Formalism.REAL.muG (fun a => ε a.rev))) ∧
    ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG ε) =
      lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG (fun a => ε a.rev)) := by
  atlas_forward_decl GlobalTheory.HaarRev.haar_rev
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PackLip

theorem integral_translate_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [SecondCountableTopology G] (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (f D : G → ℂ) (γ : ℝ → G) (h0 : γ 0 = 1) (hD : Integrable D μ)
    (hc : Continuous fun p : ℝ × G => D (γ p.1 * p.2))
    (hd : ∀ h t, HasDerivAt (fun t => f (γ t * h)) (D (γ t * h)) t) (s : ℝ) :
    ∫ h, ‖f (γ s * h) - f h‖ ∂μ ≤ |s| * ∫ h, ‖D h‖ ∂μ := by
  have hmeas : Measurable fun p : G × ℝ => ‖D (γ p.2 * p.1)‖ₑ :=
    (hc.comp (continuous_snd.prodMk continuous_fst)).measurable.enorm
  have hpt : ∀ h, ‖f (γ s * h) - f h‖ₑ ≤ ∫⁻ t in Set.uIoc (0:ℝ) s, ‖D (γ t * h)‖ₑ := by
    intro h
    have hcont : Continuous fun t => D (γ t * h) := hc.comp (continuous_id.prodMk continuous_const)
    have hF : ∫ t in (0:ℝ)..s, D (γ t * h) = f (γ s * h) - f (γ 0 * h) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd h t) (hcont.intervalIntegrable 0 s)
    rw [h0, one_mul] at hF
    rw [← hF, ← ofReal_norm_eq_enorm, intervalIntegral.norm_integral_eq_norm_integral_uIoc, ofReal_norm_eq_enorm]
    exact enorm_integral_le_lintegral_enorm _
  have hswap : ∫⁻ h, (∫⁻ t in Set.uIoc (0:ℝ) s, ‖D (γ t * h)‖ₑ) ∂μ =
      ∫⁻ t in Set.uIoc (0:ℝ) s, ∫⁻ h, ‖D (γ t * h)‖ₑ ∂μ :=
    lintegral_lintegral_swap hmeas.aemeasurable
  have hvol : volume (Set.uIoc (0:ℝ) s) = ENNReal.ofReal |s| := by
    rw [Set.uIoc, Real.volume_Ioc]
    congr 1
    rcases le_total 0 s with hs | hs <;> simp [hs, abs_of_nonneg, abs_of_nonpos]
  have hinv : ∀ t, ∫⁻ h, ‖D (γ t * h)‖ₑ ∂μ = ∫⁻ h, ‖D h‖ₑ ∂μ := fun t =>
    lintegral_mul_left_eq_self (fun h => ‖D h‖ₑ) (γ t)
  have hDfin : ∫⁻ h, ‖D h‖ₑ ∂μ ≠ ⊤ := ne_of_lt hD.2
  by_cases hI : Integrable (fun h => ‖f (γ s * h) - f h‖) μ
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        hI.aestronglyMeasurable, integral_norm_eq_lintegral_enorm hD.aestronglyMeasurable,
      ← ENNReal.toReal_ofReal (abs_nonneg s), ← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDfin) ?_
    calc ∫⁻ h, ENNReal.ofReal ‖f (γ s * h) - f h‖ ∂μ = ∫⁻ h, ‖f (γ s * h) - f h‖ₑ ∂μ := by
          simp only [ofReal_norm_eq_enorm]
      _ ≤ ∫⁻ h, (∫⁻ t in Set.uIoc (0:ℝ) s, ‖D (γ t * h)‖ₑ) ∂μ := lintegral_mono hpt
      _ = ENNReal.ofReal |s| * ∫⁻ h, ‖D h‖ₑ ∂μ := by
          rw [hswap]
          simp only [hinv]
          rw [setLIntegral_const, hvol, mul_comm]
  · rw [integral_undef hI]
    exact mul_nonneg (abs_nonneg _) (integral_nonneg fun _ => norm_nonneg _)

private theorem jm_sq_lemma {k : ℕ} (δ : Fin k → Bool) : Formalism.REAL.Jm δ * Formalism.REAL.Jm δ = 1 := by
  rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private theorem exp_preserves_Jm_of_skew {k : ℕ} (δ : Fin k → Bool) (A : Matrix (Fin k) (Fin k) ℂ)
    (hA : Aᴴ * Formalism.REAL.Jm δ + Formalism.REAL.Jm δ * A = 0) :
    (NormedSpace.exp A)ᴴ * Formalism.REAL.Jm δ * NormedSpace.exp A = Formalism.REAL.Jm δ := by
  set J := Formalism.REAL.Jm δ with hJdef
  have hJ : J * J = 1 := jm_sq_lemma δ
  have hJi : J⁻¹ = J := Matrix.inv_eq_left_inv hJ
  have hJu : IsUnit J := ⟨⟨J, J, hJ, hJ⟩, rfl⟩
  have hAc : Aᴴ = J * (-A) * J⁻¹ := by
    rw [hJi]
    calc Aᴴ = Aᴴ * (J * J) := by rw [hJ, mul_one]
      _ = (Aᴴ * J + J * A) * J - J * A * J := by noncomm_ring
      _ = J * (-A) * J := by rw [hA]; noncomm_ring
  have h2 : NormedSpace.exp (-A) * NormedSpace.exp A = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl A).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  rw [← Matrix.exp_conjTranspose, hAc, Matrix.exp_conj _ _ hJu, hJi]
  calc J * NormedSpace.exp (-A) * J * J * NormedSpace.exp A
      = J * (NormedSpace.exp (-A) * (J * J) * NormedSpace.exp A) := by simp only [mul_assoc]
    _ = J := by rw [hJ, mul_one, h2, mul_one]

section Rep

open Formalism.MainNotions.S GlobalTheory.Ell

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem exp_mem' {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ lieOf (Formalism.REAL.Jm ε)) (t : ℝ) :
    NormedSpace.exp (t • Y) ∈ UJset ε := by
  have hY0 : Yᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * Y = 0 := hY
  show (NormedSpace.exp (t • Y))ᴴ * Formalism.REAL.Jm ε * NormedSpace.exp (t • Y) = Formalism.REAL.Jm ε
  apply exp_preserves_Jm_of_skew
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hY0, smul_zero]

theorem rep_mul' (hπ : IsURepOn (UJset ε) π) {g g' : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hg' : g' ∈ UJset ε)
    (w : H) : π (g * g') w = π g (π g' w) := by
  obtain ⟨⟨-, hm⟩, -, -⟩ := id hπ
  rw [hm g hg g' hg', ContinuousLinearMap.comp_apply]

theorem exp_add' (Y : Matrix (Fin n) (Fin n) ℂ) (a b : ℝ) :
    NormedSpace.exp ((a + b) • Y) = NormedSpace.exp (a • Y) * NormedSpace.exp (b • Y) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left a).smul_right b)

theorem inner_exp (hπ : IsURepOn (UJset ε) π) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ lieOf (Formalism.REAL.Jm ε)) (t : ℝ)
    (u w : H) : ⟪u, π (NormedSpace.exp (t • Y)) w⟫_ℂ = ⟪π (NormedSpace.exp ((-t) • Y)) u, w⟫_ℂ := by
  obtain ⟨⟨hone, -⟩, hiso, -⟩ := id hπ
  have hm1 : NormedSpace.exp ((-t) • Y) * NormedSpace.exp (t • Y) = 1 := by
    rw [← exp_add', neg_add_cancel, zero_smul, NormedSpace.exp_zero]
  have hw : π (NormedSpace.exp ((-t) • Y)) (π (NormedSpace.exp (t • Y)) w) = w := by
    rw [← rep_mul' hπ (exp_mem' hY (-t)) (exp_mem' hY t), hm1, hone]
    rfl
  let T : H →ₗᵢ[ℂ] H :=
    { toLinearMap := (π (NormedSpace.exp ((-t) • Y)) : H →ₗ[ℂ] H)
      norm_map' := hiso _ (exp_mem' hY (-t)) }
  have key := T.inner_map_map u (π (NormedSpace.exp (t • Y)) w)
  change ⟪π (NormedSpace.exp ((-t) • Y)) u, π (NormedSpace.exp ((-t) • Y)) (π (NormedSpace.exp (t • Y)) w)⟫_ℂ
    = _ at key
  rw [hw] at key
  exact key.symm

theorem hasDerivAt_coef (hπ : IsURepOn (UJset ε) π) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ lieOf (Formalism.REAL.Jm ε))
    {v : H} (hv : SmV (lieOf (Formalism.REAL.Jm ε)) π v) (w : H) (t : ℝ) :
    HasDerivAt (fun r : ℝ => ⟪v, π (NormedSpace.exp (r • Y)) w⟫_ℂ)
      (-⟪dR π Y v, π (NormedSpace.exp (t • Y)) w⟫_ℂ) t := by
  have hsm := hv 1 ![Y] (fun i => by rw [Fin.fin_one_eq_zero i]; exact hY)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => π (NormedSpace.exp (s • Y)) v) := by
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => (fun _ : Fin 1 => s)) := contDiff_pi.2 fun _ => contDiff_id
    convert hsm.comp hc using 1
    funext s
    simp [List.ofFn_succ]
  have hdiff : Differentiable ℝ (fun s : ℝ => π (NormedSpace.exp (s • Y)) v) := hφ.differentiable (by simp)
  have hd0 : HasDerivAt (fun s : ℝ => π (NormedSpace.exp (s • Y)) v) (dR π Y v) 0 := (hdiff 0).hasDerivAt
  have hφs : ∀ s : ℝ, HasDerivAt (fun s : ℝ => π (NormedSpace.exp (s • Y)) v)
      (π (NormedSpace.exp (s • Y)) (dR π Y v)) s := by
    intro s
    have ha : HasDerivAt (fun r : ℝ => π (NormedSpace.exp (s • Y)) (π (NormedSpace.exp (r • Y)) v))
        (π (NormedSpace.exp (s • Y)) (dR π Y v)) (s - s) := by
      rw [sub_self]
      exact (((π (NormedSpace.exp (s • Y))).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt 0 hd0
    refine (ha.comp_sub_const s s).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    show π (NormedSpace.exp (x • Y)) v = π (NormedSpace.exp (s • Y)) (π (NormedSpace.exp ((x - s) • Y)) v)
    rw [← rep_mul' hπ (exp_mem' hY s) (exp_mem' hY (x - s)), ← exp_add', add_sub_cancel]
  have hneg : HasDerivAt (fun r : ℝ => π (NormedSpace.exp ((-r) • Y)) v)
      (-(π (NormedSpace.exp ((-t) • Y)) (dR π Y v))) t := by
    have := (hφs (-t)).scomp t (hasDerivAt_neg t)
    simpa [Function.comp_def] using this
  have hin := hneg.inner ℂ (hasDerivAt_const t w)
  have hfun : (fun r : ℝ => ⟪v, π (NormedSpace.exp (r • Y)) w⟫_ℂ) =
      fun r => ⟪π (NormedSpace.exp ((-r) • Y)) v, w⟫_ℂ := funext fun r => inner_exp hπ hY r v w
  rw [hfun]
  refine hin.congr_deriv ?_
  rw [inner_exp hπ hY t (dR π Y v) w]
  simp

end Rep

theorem hsn_smul {m : ℕ} (a : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) : GlobalTheory.SepReal.hsn (a • X) = |a| * GlobalTheory.SepReal.hsn X := by
  unfold GlobalTheory.SepReal.hsn
  have hent : ∀ i j, ‖(a • X) i j‖ ^ 2 = a ^ 2 * ‖X i j‖ ^ 2 := fun i j => by
    rw [Matrix.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp_rw [hent, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

theorem eq_zero_of_hsn {m : ℕ} {X : Matrix (Fin m) (Fin m) ℂ} (h : GlobalTheory.SepReal.hsn X = 0) : X = 0 := by
  unfold GlobalTheory.SepReal.hsn at h
  have hs : ∑ a, ∑ b, ‖X a b‖ ^ 2 = 0 := by
    rwa [Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)).1 hs i (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 h1 j (Finset.mem_univ _)
  simpa using h2

private theorem real_smul_mem_lieOf {m : ℕ} {G X : Matrix (Fin m) (Fin m) ℂ} (hX : X ∈ GlobalTheory.Ell.lieOf G) (r : ℝ) :
    r • X ∈ GlobalTheory.Ell.lieOf G := by
  have hX0 : Xᴴ * G + G * X = 0 := hX
  show (r • X)ᴴ * G + G * (r • X) = 0
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX0, smul_zero]

private theorem embOpt_mul' {m N : ℕ} (e : Option (Fin m) ≃ Fin N) (h k : Matrix (Fin m) (Fin m) ℂ) :
    GlobalTheory.PackLoc.embOpt e (h * k) = GlobalTheory.PackLoc.embOpt e h * GlobalTheory.PackLoc.embOpt e k := by
  ext a b
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨y, rfl⟩ := e.surjective b
  rw [Matrix.mul_apply, ← e.sum_comp, Fintype.sum_option]
  cases x <;> cases y <;> simp [GlobalTheory.PackLoc.embOpt, Matrix.mul_apply]

private theorem embOpt_conjTranspose {m N : ℕ} (e : Option (Fin m) ≃ Fin N) (h : Matrix (Fin m) (Fin m) ℂ) :
    (GlobalTheory.PackLoc.embOpt e h)ᴴ = GlobalTheory.PackLoc.embOpt e hᴴ := by
  ext a b
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨y, rfl⟩ := e.surjective b
  cases x <;> cases y <;> simp [GlobalTheory.PackLoc.embOpt, Matrix.conjTranspose_apply]

private theorem Jm_eq_embOpt_Jm {m N : ℕ} (e : Option (Fin m) ≃ Fin N) {ε : Fin N → Bool} {ε' : Fin m → Bool}
    (h0 : ε (e none) = true) (h1 : ∀ i, ε (e (some i)) = ε' i) :
    Formalism.REAL.Jm ε = GlobalTheory.PackLoc.embOpt e (Formalism.REAL.Jm ε') := by
  ext a b
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨y, rfl⟩ := e.surjective b
  cases x <;> cases y <;> simp [GlobalTheory.PackLoc.embOpt, Formalism.REAL.Jm, Matrix.diagonal_apply, h0, h1]

private theorem embOpt_mem_UJset {m N : ℕ} (e : Option (Fin m) ≃ Fin N) {ε : Fin N → Bool} {ε' : Fin m → Bool}
    (h0 : ε (e none) = true) (h1 : ∀ i, ε (e (some i)) = ε' i) {g : Matrix (Fin m) (Fin m) ℂ}
    (hg : g ∈ Formalism.MainNotions.S.UJset ε') : GlobalTheory.PackLoc.embOpt e g ∈ Formalism.MainNotions.S.UJset ε := by
  have hg' : gᴴ * Formalism.REAL.Jm ε' * g = Formalism.REAL.Jm ε' := hg
  show (GlobalTheory.PackLoc.embOpt e g)ᴴ * Formalism.REAL.Jm ε * GlobalTheory.PackLoc.embOpt e g = Formalism.REAL.Jm ε
  rw [Jm_eq_embOpt_Jm e h0 h1, embOpt_conjTranspose, ← embOpt_mul', ← embOpt_mul', hg']

private theorem embOptL_mem_lieOf_Jm {m N : ℕ} (e : Option (Fin m) ≃ Fin N) {ε : Fin N → Bool} {ε' : Fin m → Bool}
    (h0 : ε (e none) = true) (h1 : ∀ i, ε (e (some i)) = ε' i) {X : Matrix (Fin m) (Fin m) ℂ}
    (hX : X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε')) : GlobalTheory.PackLoc.embOptL e X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε) := by
  have hX' : Xᴴ * Formalism.REAL.Jm ε' + Formalism.REAL.Jm ε' * X = 0 := hX
  show (GlobalTheory.PackLoc.embOptL e X)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * GlobalTheory.PackLoc.embOptL e X = 0
  ext a b
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨y, rfl⟩ := e.surjective b
  rcases x with _ | i <;> rcases y with _ | j
  · simp [GlobalTheory.PackLoc.embOptL, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  · simp [GlobalTheory.PackLoc.embOptL, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  · simp [GlobalTheory.PackLoc.embOptL, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  · have hij := congrFun (congrFun hX' i) j
    simp [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] at hij
    simpa [GlobalTheory.PackLoc.embOptL, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.conjTranspose_apply, h1] using hij

private theorem embOpt_exp_smul {m N : ℕ} (e : Option (Fin m) ≃ Fin N) (t : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) :
    GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (t • X)) = NormedSpace.exp (t • GlobalTheory.PackLoc.embOptL e X) := by
  obtain rfl : N = m + 1 := by simpa using (Fintype.card_congr e).symm
  have hL := (GlobalTheory.SepReal.embLaws m e (fun _ => true) (fun _ => true) ⟨rfl, fun _ => rfl⟩).2.2.2.2.2.2.2.1 t X
  rw [← GlobalTheory.PackLoc.embH_eq_embOpt, ← GlobalTheory.PackLoc.embL_eq_embOptL, hL]

private theorem continuous_embOpt {m N : ℕ} (e : Option (Fin m) ≃ Fin N) : Continuous (GlobalTheory.PackLoc.embOpt e) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  obtain ⟨x, rfl⟩ := e.surjective a
  obtain ⟨y, rfl⟩ := e.surjective b
  cases x <;> cases y <;> simp [GlobalTheory.PackLoc.embOpt] <;>
    first | fun_prop | exact (continuous_apply _).comp (continuous_apply _)

private theorem continuous_exp_real_smul' {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    Continuous fun t : ℝ => NormedSpace.exp (t • X) := by
  have hc : Continuous (NormedSpace.exp : Matrix (Fin m) (Fin m) ℂ → Matrix (Fin m) (Fin m) ℂ) := by
    exact @NormedSpace.exp_continuous (Matrix (Fin m) (Fin m) ℂ) Matrix.linftyOpNormedRing
      Matrix.linftyOpNormedAlgebra (by exact (inferInstance : CompleteSpace (Matrix (Fin m) (Fin m) ℂ)))
  exact hc.comp (continuous_id.smul continuous_const)

theorem lip_core : ∀ (m N : ℕ) (e : Option (Fin m) ≃ Fin N) (ε : Fin N → Bool) (ε' : Fin m → Bool)
  (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (v : H) (K : ℝ),
  Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) π → ε (e none) = true → (∀ i, ε (e (some i)) = ε' i) →
  GlobalTheory.Ell.SmV (GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε)) π v →
  (∀ g ∈ Formalism.MainNotions.S.UJset ε,
    Integrable (fun h => ⟪v, π (g * GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ) (Formalism.REAL.muG ε')) →
  (∀ X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε'), GlobalTheory.SepReal.hsn X ≤ 1 →
    Integrable (fun h => ⟪GlobalTheory.Ell.dR π (GlobalTheory.PackLoc.embOptL e X) v, π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ)
      (Formalism.REAL.muG ε') ∧
    ∫ h, ‖⟪GlobalTheory.Ell.dR π (GlobalTheory.PackLoc.embOptL e X) v, π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ε') ≤ K) →
  ∀ X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε'), ∀ s : ℝ,
    Integrable (fun h => ‖⟪v, π (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
      ⟪v, π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖) (Formalism.REAL.muG ε') ∧
    ∫ h, ‖⟪v, π (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
      ⟪v, π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ε') ≤ K * |s| * GlobalTheory.SepReal.hsn X := by
  intro m N e ε ε' H _ _ π v K hπ h0 h1 hv hI hK X hX s
  obtain ⟨-, -, hπcont⟩ := id hπ
  have hmem : ∀ g ∈ Formalism.MainNotions.S.UJset ε', GlobalTheory.PackLoc.embOpt e g ∈ Formalism.MainNotions.S.UJset ε :=
    fun g hg => embOpt_mem_UJset e h0 h1 hg
  have hone : (1 : Matrix (Fin N) (Fin N) ℂ) ∈ Formalism.MainNotions.S.UJset ε := by
    show (1 : Matrix (Fin N) (Fin N) ℂ)ᴴ * Formalism.REAL.Jm ε * 1 = Formalism.REAL.Jm ε
    simp
  have hint : Integrable (fun h : Formalism.REAL.UJ ε' =>
      ‖⟪v, π (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
        ⟪v, π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖) (Formalism.REAL.muG ε') := by
    have hA := hI _ (hmem _ (exp_mem' hX s))
    have hB := hI 1 hone
    refine (hA.sub hB).norm.congr (Filter.Eventually.of_forall fun h => ?_)
    simp only [Pi.sub_apply, embOpt_mul', one_mul]
  refine ⟨hint, ?_⟩
  by_cases hX0 : X = 0
  · subst hX0
    simp [GlobalTheory.SepReal.hsn]
  have hpos : 0 < GlobalTheory.SepReal.hsn X :=
    lt_of_le_of_ne (Real.sqrt_nonneg _) (fun h => hX0 (eq_zero_of_hsn h.symm))
  set c := GlobalTheory.SepReal.hsn X with hc
  have hX'lie : c⁻¹ • X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε') := real_smul_mem_lieOf hX c⁻¹
  have hX'n : GlobalTheory.SepReal.hsn (c⁻¹ • X) = 1 := by
    rw [hsn_smul, abs_inv, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']
  obtain ⟨hDi, hDb⟩ := hK _ hX'lie hX'n.le
  have hZ : GlobalTheory.PackLoc.embOptL e (c⁻¹ • X) ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε) := embOptL_mem_lieOf_Jm e h0 h1 hX'lie
  let u : ℝ → (Matrix (Fin m) (Fin m) ℂ)ˣ := fun t =>
    ⟨NormedSpace.exp (t • c⁻¹ • X), NormedSpace.exp ((-t) • c⁻¹ • X),
      by rw [← exp_add', add_neg_cancel, zero_smul, NormedSpace.exp_zero],
      by rw [← exp_add', neg_add_cancel, zero_smul, NormedSpace.exp_zero]⟩
  let γ : ℝ → Formalism.REAL.UJ ε' := fun t => ⟨u t, exp_mem' hX'lie t⟩
  let f : Formalism.REAL.UJ ε' → ℂ := fun h => ⟪v, π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ
  let D : Formalism.REAL.UJ ε' → ℂ := fun h =>
    -⟪GlobalTheory.Ell.dR π (GlobalTheory.PackLoc.embOptL e (c⁻¹ • X)) v, π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ
  have hkey : ∀ (t : ℝ) (h : Formalism.REAL.UJ ε'),
      π (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (t • c⁻¹ • X) * Formalism.MainNotions.S.umat h)) v =
        π (NormedSpace.exp (t • GlobalTheory.PackLoc.embOptL e (c⁻¹ • X))) (π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v) := by
    intro t h
    rw [embOpt_mul', embOpt_exp_smul,
      rep_mul' hπ (exp_mem' hZ t) (hmem _ h.2)]
  have hγ0 : γ 0 = 1 := by
    apply Subtype.ext
    apply Units.ext
    show NormedSpace.exp ((0:ℝ) • c⁻¹ • X) = 1
    rw [zero_smul, NormedSpace.exp_zero]
  have hd : ∀ (h : Formalism.REAL.UJ ε') (t : ℝ), HasDerivAt (fun t => f (γ t * h)) (D (γ t * h)) t := by
    intro h t
    have H1 := hasDerivAt_coef hπ hZ hv (π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v) t
    have e1 : (fun t => f (γ t * h)) = fun r : ℝ =>
        ⟪v, π (NormedSpace.exp (r • GlobalTheory.PackLoc.embOptL e (c⁻¹ • X)))
          (π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v)⟫_ℂ := by
      funext r
      show ⟪v, π (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (r • c⁻¹ • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ = _
      rw [hkey]
    have e2 : D (γ t * h) = -⟪GlobalTheory.Ell.dR π (GlobalTheory.PackLoc.embOptL e (c⁻¹ • X)) v,
        π (NormedSpace.exp (t • GlobalTheory.PackLoc.embOptL e (c⁻¹ • X)))
          (π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v)⟫_ℂ := by
      show -⟪_, π (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (t • c⁻¹ • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ = _
      rw [hkey]
    rw [e1, e2]
    exact H1
  have hcD : Continuous fun p : ℝ × Formalism.REAL.UJ ε' => D (γ p.1 * p.2) := by
    have hum : Continuous fun h : Formalism.REAL.UJ ε' => Formalism.MainNotions.S.umat h :=
      Units.continuous_val.comp continuous_subtype_val
    have hg : Continuous fun p : ℝ × Formalism.REAL.UJ ε' =>
        GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (p.1 • c⁻¹ • X) * Formalism.MainNotions.S.umat p.2) :=
      (continuous_embOpt e).comp (((continuous_exp_real_smul' (c⁻¹ • X)).comp continuous_fst).mul (hum.comp continuous_snd))
    have hπc : Continuous fun p : ℝ × Formalism.REAL.UJ ε' =>
        π (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (p.1 • c⁻¹ • X) * Formalism.MainNotions.S.umat p.2)) v :=
      (hπcont v).comp_continuous hg fun p => hmem _ (γ p.1 * p.2).2
    exact (continuous_const.inner hπc).neg
  have hmain := integral_translate_le (Formalism.REAL.muG ε') f D γ hγ0 hDi.neg hcD hd (s * c)
  have hsX : (s * c) • c⁻¹ • X = s • X := by
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ hpos.ne', mul_one]
  have hDn : ∫ h, ‖D h‖ ∂(Formalism.REAL.muG ε') ≤ K := by simpa only [D, norm_neg] using hDb
  calc _ = ∫ h, ‖f (γ (s * c) * h) - f h‖ ∂(Formalism.REAL.muG ε') := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
        show _ = ‖⟪v, π (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp ((s * c) • c⁻¹ • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
          ⟪v, π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖
        rw [hsX]
    _ ≤ |s * c| * ∫ h, ‖D h‖ ∂(Formalism.REAL.muG ε') := hmain
    _ ≤ |s * c| * K := mul_le_mul_of_nonneg_left hDn (abs_nonneg _)
    _ = K * |s| * c := by rw [abs_mul, abs_of_pos hpos]; ring

end GlobalTheory.PackLip

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vector_matrixCoeff_integrable : ∀ (m N : ℕ) (e : Option (Fin m) ≃ Fin N) (ε : Fin N → Bool) (ε' : Fin m → Bool)
  (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (v : H) (K : ℝ),
  Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) π → ε (e none) = true → (∀ i, ε (e (some i)) = ε' i) →
  GlobalTheory.Ell.SmV (GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε)) π v →
  (∀ g ∈ Formalism.MainNotions.S.UJset ε,
    Integrable (fun h => ⟪v, π (g * GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ) (Formalism.REAL.muG ε')) →
  (∀ X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε'), GlobalTheory.SepReal.hsn X ≤ 1 →
    Integrable (fun h => ⟪GlobalTheory.Ell.dR π (GlobalTheory.PackLoc.embOptL e X) v, π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ)
      (Formalism.REAL.muG ε') ∧
    ∫ h, ‖⟪GlobalTheory.Ell.dR π (GlobalTheory.PackLoc.embOptL e X) v, π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ε') ≤ K) →
  ∀ X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε'), ∀ s : ℝ,
    Integrable (fun h => ‖⟪v, π (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
      ⟪v, π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖) (Formalism.REAL.muG ε') ∧
    ∫ h, ‖⟪v, π (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
      ⟪v, π (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ε') ≤ K * |s| * GlobalTheory.SepReal.hsn X := by
  atlas_forward_decl GlobalTheory.PackLip.lip_core
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameDecay

section Frob
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing

theorem hs_eq_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) = ‖A‖ := by
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact (Real.rpow_natCast _ 2).symm

theorem hsn_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.SepPer.hsn (A * B) ≤ GlobalTheory.SepPer.hsn A * GlobalTheory.SepPer.hsn B := by
  unfold GlobalTheory.SepPer.hsn
  rw [hs_eq_norm, hs_eq_norm, hs_eq_norm]
  exact Matrix.frobenius_norm_mul A B

end Frob

theorem hsn_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ GlobalTheory.SepPer.hsn A := Real.sqrt_nonneg _

theorem one_le_hsn_of_mem {n : ℕ} (ε : Fin n → Bool) (i : Fin n) (y : Matrix (Fin n) (Fin n) ℂ)
    (hy : y ∈ Formalism.MainNotions.S.UJset ε) : 1 ≤ GlobalTheory.SepPer.hsn y := by
  have hy' : yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε := hy
  have h := congrFun (congrFun hy' i) i
  have e1 : (yᴴ * Formalism.REAL.Jm ε * y) i i = ∑ k, star (y k i) * ((if ε k then 1 else -1) * y k i) := by
    simp only [Formalism.REAL.Jm]
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    ring
  have e2 : ‖Formalism.REAL.Jm ε i i‖ = 1 := by
    by_cases hi : ε i = true <;> simp [Formalism.REAL.Jm, hi]
  have hcol : 1 ≤ ∑ k, ‖y k i‖ ^ 2 := by
    rw [← e2, ← h, e1]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
    by_cases hk : ε k = true <;> simp [hk, norm_mul, sq]
  have hall : ∑ k, ‖y k i‖ ^ 2 ≤ ∑ a, ∑ b, ‖y a b‖ ^ 2 :=
    Finset.sum_le_sum fun a _ =>
      Finset.single_le_sum (f := fun b => ‖y a b‖ ^ 2) (fun b _ => by positivity) (Finset.mem_univ i)
  unfold GlobalTheory.SepPer.hsn
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt (hcol.trans hall)

end GlobalTheory.FrameDecay

namespace GlobalTheory.FrameDecay

theorem coef_frame_decay : ∀ (m N : ℕ), N = m + 1 → ∀ (ε : Fin N → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (π : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (v₀ : H) (g₀ F G : Matrix (Fin N) (Fin N) ℂ) (A₀ : ℝ),
  Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) π → g₀ ∈ Formalism.MainNotions.S.UJset ε → IsUnit F → Fᴴ * Formalism.REAL.Jm ε * F = G →
  (∀ g ∈ Formalism.MainNotions.S.UJset ε, ‖⟪π g₀ v₀, π g (π g₀ v₀)⟫_ℂ‖ ≤ A₀ * GlobalTheory.SepReal.hsn g ^ (-(20 * ((m : ℝ) + 1) ^ 2))) →
  ∃ C : ℝ, ∀ g ∈ Formalism.QuantumDeterminants.UH G, ‖⟪v₀, π (F * g * F⁻¹) v₀⟫_ℂ‖ * (1 + GlobalTheory.SepPer.hsn g) ^ (2 * N ^ 2 + 1) ≤ C := by
  intro m N hN ε H instH instI π v₀ g₀ F G A₀ hπ hg₀ hF hG hdec
  obtain ⟨⟨_, hmul⟩, hiso, -⟩ := hπ
  have hg₀' : g₀ᴴ * Formalism.REAL.Jm ε * g₀ = Formalism.REAL.Jm ε := hg₀
  have hJJ := Formalism.REAL.Jm_mul_self ε

  have hleft : (Formalism.REAL.Jm ε * g₀ᴴ * Formalism.REAL.Jm ε) * g₀ = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc g₀ᴴ, hg₀', hJJ]
  have hinv : g₀⁻¹ = Formalism.REAL.Jm ε * g₀ᴴ * Formalism.REAL.Jm ε := Matrix.inv_eq_left_inv hleft
  have hl : g₀⁻¹ * g₀ = 1 := by rw [hinv, hleft]
  have hr : g₀ * g₀⁻¹ = 1 := Matrix.mul_nonsing_inv g₀ (Matrix.isUnit_det_of_left_inverse hleft)
  have hmemMul : ∀ a ∈ Formalism.MainNotions.S.UJset ε, ∀ b ∈ Formalism.MainNotions.S.UJset ε, a * b ∈ Formalism.MainNotions.S.UJset ε := by
    intro a ha b hb
    have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
    have hb' : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := hb
    show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
    calc (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [ha', hb']
  have hinvMem : g₀⁻¹ ∈ Formalism.MainNotions.S.UJset ε := by
    show (g₀⁻¹)ᴴ * Formalism.REAL.Jm ε * g₀⁻¹ = Formalism.REAL.Jm ε
    conv_lhs => rw [← hg₀']
    rw [show (g₀⁻¹)ᴴ * (g₀ᴴ * Formalism.REAL.Jm ε * g₀) * g₀⁻¹ = (g₀ * g₀⁻¹)ᴴ * Formalism.REAL.Jm ε * (g₀ * g₀⁻¹) by
      rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc], hr]
    simp

  have hFd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).mp hF
  have hFl : F⁻¹ * F = 1 := Matrix.nonsing_inv_mul F hFd
  have hFr : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv F hFd

  have hkeep : ∀ u w : H, ⟪π g₀ u, π g₀ w⟫_ℂ = ⟪u, w⟫_ℂ := by
    intro u w
    let T : H →ₗᵢ[ℂ] H := ⟨(π g₀ : H →ₗ[ℂ] H), fun v => hiso g₀ hg₀ v⟩
    exact T.inner_map_map u w
  set k : ℝ := 20 * ((m : ℝ) + 1) ^ 2 with hk
  set e : ℕ := 2 * N ^ 2 + 1 with he
  have hek : (e : ℝ) ≤ k := by
    have h1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    rw [he, hk, hN]; push_cast; nlinarith
  set c₁ : ℝ := GlobalTheory.SepPer.hsn (F⁻¹ * g₀⁻¹) * GlobalTheory.SepPer.hsn (g₀ * F) with hc₁
  have hc₁0 : 0 ≤ c₁ := mul_nonneg (hsn_nonneg _) (hsn_nonneg _)
  refine ⟨|A₀| * (1 + c₁) ^ e, fun g hg => ?_⟩
  have hg' : gᴴ * G * g = G := hg
  set x := F * g * F⁻¹ with hx
  have hxMem : x ∈ Formalism.MainNotions.S.UJset ε := by
    show xᴴ * Formalism.REAL.Jm ε * x = Formalism.REAL.Jm ε
    have : xᴴ * Formalism.REAL.Jm ε * x = (F⁻¹)ᴴ * (gᴴ * (Fᴴ * Formalism.REAL.Jm ε * F) * g) * F⁻¹ := by
      rw [hx, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [this, hG, hg', ← hG]
    have hFH : (F⁻¹)ᴴ * Fᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hFr, Matrix.conjTranspose_one]
    calc (F⁻¹)ᴴ * (Fᴴ * Formalism.REAL.Jm ε * F) * F⁻¹ = ((F⁻¹)ᴴ * Fᴴ) * Formalism.REAL.Jm ε * (F * F⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hFH, hFr, Matrix.one_mul, Matrix.mul_one]
  set y := g₀ * x * g₀⁻¹ with hy
  have hyMem : y ∈ Formalism.MainNotions.S.UJset ε := hmemMul _ (hmemMul _ hg₀ _ hxMem) _ hinvMem

  have hco : ⟪v₀, π x v₀⟫_ℂ = ⟪π g₀ v₀, π y (π g₀ v₀)⟫_ℂ := by
    have h1 : π y (π g₀ v₀) = π g₀ (π x v₀) := by
      have h2 : y * g₀ = g₀ * x := by rw [hy, Matrix.mul_assoc, hl, Matrix.mul_one]
      rw [← ContinuousLinearMap.comp_apply, ← hmul _ hyMem _ hg₀, h2, hmul _ hg₀ _ hxMem,
        ContinuousLinearMap.comp_apply]
    rw [h1, hkeep]

  set s := GlobalTheory.SepPer.hsn y with hs
  set t := GlobalTheory.SepPer.hsn g with ht
  have hs1 : 1 ≤ s := one_le_hsn_of_mem ε ⟨0, by omega⟩ y hyMem
  have hs0 : 0 < s := by linarith
  have hts : t ≤ c₁ * s := by
    have hgeq : g = (F⁻¹ * g₀⁻¹) * y * (g₀ * F) := by
      have : (F⁻¹ * g₀⁻¹) * y * (g₀ * F) = (F⁻¹ * F) * g * (F⁻¹ * F) := by
        rw [hy, hx]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc g₀⁻¹ g₀, hl, Matrix.one_mul,
          ← Matrix.mul_assoc g₀⁻¹ g₀, hl, Matrix.one_mul]
      rw [this, hFl, Matrix.one_mul, Matrix.mul_one]
    rw [ht, hgeq, hc₁]
    calc GlobalTheory.SepPer.hsn ((F⁻¹ * g₀⁻¹) * y * (g₀ * F))
        ≤ GlobalTheory.SepPer.hsn ((F⁻¹ * g₀⁻¹) * y) * GlobalTheory.SepPer.hsn (g₀ * F) := hsn_mul_le _ _
      _ ≤ (GlobalTheory.SepPer.hsn (F⁻¹ * g₀⁻¹) * s) * GlobalTheory.SepPer.hsn (g₀ * F) :=
          mul_le_mul_of_nonneg_right (hsn_mul_le _ _) (hsn_nonneg _)
      _ = GlobalTheory.SepPer.hsn (F⁻¹ * g₀⁻¹) * GlobalTheory.SepPer.hsn (g₀ * F) * s := by ring
  have hbd := hdec y hyMem
  have hsame : GlobalTheory.SepReal.hsn y = s := rfl
  rw [hsame, ← hco] at hbd
  have hpow : s ^ (-k) ≤ (s ^ e)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hs0.le]
    exact Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
  have hz : ‖⟪v₀, π x v₀⟫_ℂ‖ ≤ |A₀| * (s ^ e)⁻¹ :=
    hbd.trans ((mul_le_mul_of_nonneg_right (le_abs_self A₀) (Real.rpow_nonneg hs0.le _)).trans
      (mul_le_mul_of_nonneg_left hpow (abs_nonneg _)))
  have hT : (1 + t) ^ e ≤ (1 + c₁) ^ e * s ^ e := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by linarith [hsn_nonneg g]) ?_ e
    nlinarith
  have hse : 0 < s ^ e := pow_pos hs0 e
  calc ‖⟪v₀, π x v₀⟫_ℂ‖ * (1 + t) ^ e ≤ (|A₀| * (s ^ e)⁻¹) * ((1 + c₁) ^ e * s ^ e) :=
        mul_le_mul hz hT (pow_nonneg (by linarith [hsn_nonneg g]) _)
          (mul_nonneg (abs_nonneg _) (inv_nonneg.mpr hse.le))
    _ = |A₀| * (1 + c₁) ^ e := by field_simp

end GlobalTheory.FrameDecay
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_coefficient_decay_in_frame_of_translate_decay : ∀ (m N : ℕ), N = m + 1 → ∀ (ε : Fin N → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (π : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (v₀ : H) (g₀ F G : Matrix (Fin N) (Fin N) ℂ) (A₀ : ℝ),
  Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) π → g₀ ∈ Formalism.MainNotions.S.UJset ε → IsUnit F → Fᴴ * Formalism.REAL.Jm ε * F = G →
  (∀ g ∈ Formalism.MainNotions.S.UJset ε, ‖⟪π g₀ v₀, π g (π g₀ v₀)⟫_ℂ‖ ≤ A₀ * GlobalTheory.SepReal.hsn g ^ (-(20 * ((m : ℝ) + 1) ^ 2))) →
  ∃ C : ℝ, ∀ g ∈ Formalism.QuantumDeterminants.UH G, ‖⟪v₀, π (F * g * F⁻¹) v₀⟫_ℂ‖ * (1 + GlobalTheory.SepPer.hsn g) ^ (2 * N ^ 2 + 1) ≤ C := by
  atlas_forward_decl GlobalTheory.FrameDecay.coef_frame_decay
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjSmooth

open GlobalTheory.ConjDS

theorem conj_list_prod {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    A * l.prod * A⁻¹ = (l.map fun x => A * x * A⁻¹).prod := by
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).1 hA)
  have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).1 hA)
  induction l with
  | nil => simp [h1]
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ← ih]
    calc A * (x * l.prod) * A⁻¹ = A * x * (A⁻¹ * A) * l.prod * A⁻¹ := by rw [h2]; noncomm_ring
      _ = A * x * A⁻¹ * (A * l.prod * A⁻¹) := by noncomm_ring

theorem cj_mem_sm : ∀ (D : D7) (Y : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel Y S) (τ : D.what₂.Tau)
  (w : (GlobalTheory.ConjDS.conjModel M).H τ),
  GlobalTheory.Ell.SmV (GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M).ε τ))) ((GlobalTheory.ConjDS.conjModel M).σ τ) w →
  GlobalTheory.ConjDS.cj (M.H τ) w ∈ M.sm τ := by
  intro D Y S M τ w hw
  apply Submodule.subset_span
  intro k Xs hXs
  set A := (conjModel M).fr τ with hAdef
  have hA : IsUnit A := (conjModel M).fr_unit τ
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdet

  have hrep : ∀ g, M.rep τ g (cj (M.H τ) w) = cj (M.H τ) ((conjModel M).σ τ (A * g * A⁻¹) w) := by
    intro g
    have e : rv ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g *
        ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹) = M.fr τ * g * (M.fr τ)⁻¹ := by
      rw [inv_submatrix_equiv]
      have : (M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g * (M.fr τ)⁻¹.submatrix (Equiv.refl _) Fin.revPerm =
          rv (M.fr τ * g * (M.fr τ)⁻¹) := by
        ext i j
        simp [rv, Matrix.mul_apply]
      rw [this, rv_rv]
    show M.σ τ (M.fr τ * g * (M.fr τ)⁻¹) (cj (M.H τ) w) = M.σ τ (rv ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _) * g *
        ((M.fr τ).submatrix Fin.revPerm (Equiv.refl _))⁻¹)) (cj (M.H τ) w)
    rw [e]

  have hX' : ∀ i, A * Xs i * A⁻¹ ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((conjModel M).ε τ)) := by
    intro i
    have hg : Aᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) * A = gramAt D Y τ := (conjModel M).fr_gram τ
    have hi : (Xs i)ᴴ * gramAt D Y τ + gramAt D Y τ * Xs i = 0 := hXs i
    have h3 : (A⁻¹)ᴴ * Aᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    show (A * Xs i * A⁻¹)ᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) + Formalism.REAL.Jm ((conjModel M).ε τ) * (A * Xs i * A⁻¹) = 0
    rw [← hg] at hi
    have : (A * Xs i * A⁻¹)ᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) + Formalism.REAL.Jm ((conjModel M).ε τ) * (A * Xs i * A⁻¹) =
        (A⁻¹)ᴴ * ((Xs i)ᴴ * (Aᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) * A) + (Aᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) * A) * Xs i) * A⁻¹ := by
      simp only [Matrix.conjTranspose_mul]
      calc _ = (A⁻¹)ᴴ * (Xs i)ᴴ * Aᴴ * Formalism.REAL.Jm ((conjModel M).ε τ) + 1 * Formalism.REAL.Jm ((conjModel M).ε τ) * (A * Xs i * A⁻¹) := by
              rw [Matrix.one_mul]; noncomm_ring
        _ = _ := by rw [← h3]; simp only [Matrix.mul_assoc, h1, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul]
    rw [this, hi, Matrix.mul_zero, Matrix.zero_mul]
  have hprod : ∀ t : Fin k → ℝ, A * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * A⁻¹ =
      (List.ofFn fun i => NormedSpace.exp (t i • (A * Xs i * A⁻¹))).prod := by
    intro t
    rw [conj_list_prod hA, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.2 (funext fun i => ?_)
    simp only [Function.comp]
    rw [← Matrix.exp_conj A _ hA, Matrix.mul_smul, Matrix.smul_mul]
  have hc := hw k (fun i => A * Xs i * A⁻¹) hX'
  let L : Cj (M.H τ) →L[ℝ] M.H τ :=
    { toFun := cj (M.H τ)
      map_add' := map_add (cj (M.H τ))
      map_smul' := fun r x => by
        rw [← Complex.coe_smul, ← Complex.coe_smul, LinearIsometryEquiv.map_smulₛₗ, Complex.conj_ofReal]
        rfl
      cont := (cj (M.H τ)).continuous }
  have hL := L.contDiff.comp hc
  convert hL using 1
  funext t
  simp only [Function.comp]
  rw [hrep, hprod]
  rfl

end GlobalTheory.ConjSmooth

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_smooth_vector_conjugate_model_mem_smooth : ∀ (D : D7) (Y : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel Y S) (τ : D.what₂.Tau)
  (w : (GlobalTheory.ConjDS.conjModel M).H τ),
  GlobalTheory.Ell.SmV (GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M).ε τ))) ((GlobalTheory.ConjDS.conjModel M).σ τ) w →
  GlobalTheory.ConjDS.cj (M.H τ) w ∈ M.sm τ := by
  atlas_forward_decl GlobalTheory.ConjSmooth.cj_mem_sm
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PackLoc

lemma inUJ_mul' {n : ℕ} {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ}
    (ha : a ∈ Formalism.MainNotions.S.UJset ε) (hb : b ∈ Formalism.MainNotions.S.UJset ε) : a * b ∈ Formalism.MainNotions.S.UJset ε := by
  have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
  have hb' : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := hb
  show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
  rw [conjTranspose_mul]
  calc bᴴ * aᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha', hb']

theorem mco_frame : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
  (B g₀' : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v₀ : M.H τ),
  IsUnit B → Bᴴ * Formalism.REAL.Jm (M.ε τ) * B = gramAt D V τ → g₀' ∈ Formalism.MainNotions.S.UJset (M.ε τ) →
  B⁻¹ * g₀' * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧
  ∀ x ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), GlobalTheory.PackLoc.mco M τ (B⁻¹ * g₀' * M.fr τ) v₀ x =
    ⟪M.σ τ g₀' v₀, M.σ τ (B * x * B⁻¹) (M.σ τ g₀' v₀)⟫_ℂ := by
  intro D V S M τ B g v₀ hB hBg hg
  set F := M.fr τ with hFdef
  set J := Formalism.REAL.Jm (M.ε τ) with hJdef
  set G := gramAt D V τ with hGdef
  have hFd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).mp (M.fr_unit τ)
  have hBd : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hB
  have hFg : Fᴴ * J * F = G := M.fr_gram τ
  have hg' : gᴴ * J * g = J := hg
  have hBH : (B⁻¹)ᴴ * Bᴴ = 1 := by
    rw [← conjTranspose_mul, Matrix.mul_nonsing_inv B hBd, conjTranspose_one]
  have hFH : (F⁻¹)ᴴ * Fᴴ = 1 := by
    rw [← conjTranspose_mul, Matrix.mul_nonsing_inv F hFd, conjTranspose_one]
  have hBinv : (B⁻¹)ᴴ * G * B⁻¹ = J := by
    rw [← hBg]
    calc (B⁻¹)ᴴ * (Bᴴ * J * B) * B⁻¹ = ((B⁻¹)ᴴ * Bᴴ) * J * (B * B⁻¹) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hBH, Matrix.mul_nonsing_inv B hBd]; simp
  have hFinv : (F⁻¹)ᴴ * G * F⁻¹ = J := by
    rw [← hFg]
    calc (F⁻¹)ᴴ * (Fᴴ * J * F) * F⁻¹ = ((F⁻¹)ᴴ * Fᴴ) * J * (F * F⁻¹) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hFH, Matrix.mul_nonsing_inv F hFd]; simp
  refine ⟨?_, ?_⟩
  · show (B⁻¹ * g * F)ᴴ * G * (B⁻¹ * g * F) = G
    rw [conjTranspose_mul, conjTranspose_mul]
    calc Fᴴ * (gᴴ * (B⁻¹)ᴴ) * G * (B⁻¹ * g * F) = Fᴴ * (gᴴ * ((B⁻¹)ᴴ * G * B⁻¹) * g) * F := by
          simp only [Matrix.mul_assoc]
      _ = G := by rw [hBinv, hg', hFg]
  · intro x hx
    have hx' : xᴴ * G * x = G := hx
    obtain ⟨⟨_, hmul⟩, hiso, _⟩ := (M.ds τ).2.2.1
    have hk : F * B⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) := by
      show (F * B⁻¹)ᴴ * J * (F * B⁻¹) = J
      rw [conjTranspose_mul]
      calc (B⁻¹)ᴴ * Fᴴ * J * (F * B⁻¹) = (B⁻¹)ᴴ * (Fᴴ * J * F) * B⁻¹ := by simp only [Matrix.mul_assoc]
        _ = J := by rw [hFg, hBinv]
    have hy : B * x * B⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) := by
      show (B * x * B⁻¹)ᴴ * J * (B * x * B⁻¹) = J
      rw [conjTranspose_mul, conjTranspose_mul]
      calc (B⁻¹)ᴴ * (xᴴ * Bᴴ) * J * (B * x * B⁻¹) = (B⁻¹)ᴴ * (xᴴ * (Bᴴ * J * B) * x) * B⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = J := by rw [hBg, hx', hBinv]
    have hz : F * x * F⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) := by
      show (F * x * F⁻¹)ᴴ * J * (F * x * F⁻¹) = J
      rw [conjTranspose_mul, conjTranspose_mul]
      calc (F⁻¹)ᴴ * (xᴴ * Fᴴ) * J * (F * x * F⁻¹) = (F⁻¹)ᴴ * (xᴴ * (Fᴴ * J * F) * x) * F⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = J := by rw [hFg, hx', hFinv]
    have e1 : F * (B⁻¹ * g * F) * F⁻¹ = F * B⁻¹ * g := by
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv F hFd, Matrix.mul_one]
    have e2 : F * x * F⁻¹ * (F * B⁻¹ * g) = F * B⁻¹ * (B * x * B⁻¹ * g) := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left F _ hFd,
        Matrix.nonsing_inv_mul_cancel_left B _ hBd]
    have hkg := inUJ_mul' hk hg
    have hyg := inUJ_mul' hy hg
    unfold mco DSModel.rep
    rw [← hFdef, e1, ← ContinuousLinearMap.comp_apply, ← hmul _ hz _ hkg, e2,
      hmul _ hk _ hyg, hmul _ hk _ hg, hmul _ hy _ hg]
    simp only [ContinuousLinearMap.comp_apply]
    let L : M.H τ →ₗᵢ[ℂ] M.H τ := ⟨(M.σ τ (F * B⁻¹)).toLinearMap, hiso _ hk⟩
    exact L.inner_map_map _ _

end GlobalTheory.PackLoc
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translated_matrix_coefficient_in_adapted_frame : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
  (B g₀' : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v₀ : M.H τ),
  IsUnit B → Bᴴ * Formalism.REAL.Jm (M.ε τ) * B = gramAt D V τ → g₀' ∈ Formalism.MainNotions.S.UJset (M.ε τ) →
  B⁻¹ * g₀' * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧
  ∀ x ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), GlobalTheory.PackLoc.mco M τ (B⁻¹ * g₀' * M.fr τ) v₀ x =
    ⟪M.σ τ g₀' v₀, M.σ τ (B * x * B⁻¹) (M.σ τ g₀' v₀)⟫_ℂ := by
  atlas_forward_decl GlobalTheory.PackLoc.mco_frame
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PackLocFacts

variable {n : ℕ}

theorem conj_mem_lie {F J G X : Matrix (Fin n) (Fin n) ℂ} (hF : IsUnit F) (hG : Fᴴ * J * F = G)
    (hX : Xᴴ * G + G * X = 0) : (F * X * F⁻¹)ᴴ * J + J * (F * X * F⁻¹) = 0 := by
  have hd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).1 hF
  have h1 : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv F hd
  have h2 : (F⁻¹)ᴴ * Fᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have e : (F * X * F⁻¹)ᴴ * J + J * (F * X * F⁻¹) = (F⁻¹)ᴴ * (Xᴴ * G + G * X) * F⁻¹ := by
    rw [← hG]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    congr 1
    · rw [h1, Matrix.mul_one]
    · rw [← Matrix.mul_assoc (F⁻¹)ᴴ Fᴴ, h2, Matrix.one_mul]
  rw [e, hX, Matrix.mul_zero, Matrix.zero_mul]

theorem ofFr_mem_UH {F J G g : Matrix (Fin n) (Fin n) ℂ} (hF : IsUnit F) (hG : Fᴴ * J * F = G)
    (hg : gᴴ * J * g = J) : F⁻¹ * g * F ∈ Formalism.QuantumDeterminants.UH G := by
  have hd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).1 hF
  have h1 : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv F hd
  have h2 : (F⁻¹)ᴴ * Fᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq]
  rw [← hG]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (F⁻¹)ᴴ Fᴴ, h2, Matrix.one_mul, ← Matrix.mul_assoc F F⁻¹, h1, Matrix.one_mul,
    ← Matrix.mul_assoc J g F, ← Matrix.mul_assoc gᴴ (J * g) F, ← Matrix.mul_assoc gᴴ J g, hg]

theorem rev_conj (F g : Matrix (Fin n) (Fin n) ℂ) :
    F.submatrix Fin.revPerm (Equiv.refl _) * g * (F.submatrix Fin.revPerm (Equiv.refl _))⁻¹ =
      GlobalTheory.ConjDS.rv (F * g * F⁻¹) := by
  rw [Matrix.inv_submatrix_equiv]
  ext i j
  simp [GlobalTheory.ConjDS.rv, Matrix.mul_apply]

theorem frame_facts : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel Y S) (τ : D.what₂.Tau),
  (∀ u : Formalism.REAL.UJ (M.ε τ), GlobalTheory.PackLoc.ptY M τ u ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ) ∧
    (GlobalTheory.ConjDS.conjModel M).fr τ * GlobalTheory.PackLoc.ptY M τ u * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ =
      GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u) ∧
    M.rep τ (GlobalTheory.PackLoc.ptY M τ u) = M.σ τ (Formalism.MainNotions.S.umat u)) ∧
  ∀ X ∈ lieAt Y τ,
    (GlobalTheory.ConjDS.conjModel M).fr τ * X * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ ∈
      GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M).ε τ)) ∧
    ∀ s : ℝ, cmp θ τ (oneP θ Y τ X s) ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ) ∧
      (GlobalTheory.ConjDS.conjModel M).fr τ * cmp θ τ (oneP θ Y τ X s) * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ =
        NormedSpace.exp (s • ((GlobalTheory.ConjDS.conjModel M).fr τ * X * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹)) := by
  intro D θ hθ Y S M τ
  have hF : IsUnit (M.fr τ) := M.fr_unit τ
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 hF
  have hA : ∀ g, (GlobalTheory.ConjDS.conjModel M).fr τ * g * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ =
      GlobalTheory.ConjDS.rv (M.fr τ * g * (M.fr τ)⁻¹) := fun g => rev_conj (M.fr τ) g
  have hcan : ∀ U : Matrix (Fin Y.rank) (Fin Y.rank) ℂ, M.fr τ * ((M.fr τ)⁻¹ * U * M.fr τ) * (M.fr τ)⁻¹ = U := by
    intro U
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  refine ⟨fun u => ⟨?_, ?_, ?_⟩, fun X hX => ⟨?_, fun s => ?_⟩⟩
  · exact ofFr_mem_UH hF (M.fr_gram τ) u.2
  · show _ * ((M.fr τ)⁻¹ * Formalism.MainNotions.S.umat u * M.fr τ) * _ = _
    rw [hA, hcan]
  · show M.σ τ (M.fr τ * ((M.fr τ)⁻¹ * Formalism.MainNotions.S.umat u * M.fr τ) * (M.fr τ)⁻¹) = _
    rw [hcan]
  · exact conj_mem_lie ((GlobalTheory.ConjDS.conjModel M).fr_unit τ) ((GlobalTheory.ConjDS.conjModel M).fr_gram τ) hX
  · have hmem : NormedSpace.exp (s • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ) :=
      GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit Y τ) hX s
    have hc : cmp θ τ (oneP θ Y τ X s) = NormedSpace.exp (s • X) :=
      (GlobalTheory.PointAtPlaceHom.atTau_spec hθ Y τ hmem).2.1
    rw [hc]
    refine ⟨hmem, ?_⟩
    rw [← Matrix.exp_conj _ _ ((GlobalTheory.ConjDS.conjModel M).fr_unit τ), Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.PackLocFacts

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_model_frame_matrix_facts_at_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel Y S) (τ : D.what₂.Tau),
  (∀ u : Formalism.REAL.UJ (M.ε τ), GlobalTheory.PackLoc.ptY M τ u ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ) ∧
    (GlobalTheory.ConjDS.conjModel M).fr τ * GlobalTheory.PackLoc.ptY M τ u * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ =
      GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u) ∧
    M.rep τ (GlobalTheory.PackLoc.ptY M τ u) = M.σ τ (Formalism.MainNotions.S.umat u)) ∧
  ∀ X ∈ lieAt Y τ,
    (GlobalTheory.ConjDS.conjModel M).fr τ * X * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ ∈
      GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M).ε τ)) ∧
    ∀ s : ℝ, cmp θ τ (oneP θ Y τ X s) ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ) ∧
      (GlobalTheory.ConjDS.conjModel M).fr τ * cmp θ τ (oneP θ Y τ X s) * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ =
        NormedSpace.exp (s • ((GlobalTheory.ConjDS.conjModel M).fr τ * X * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹)) := by
  atlas_forward_decl GlobalTheory.PackLocFacts.frame_facts
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PackLoc

theorem farClause : ∀ (D : D7) (θ : InfFam D) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S')
  (MP : DSModel V S) (τ : D.what₂.Tau) (e : Option (Fin Y.rank) ≃ Fin V.rank) (v₀ v : MP.H τ)
  (g₀ B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (c₁ lam q Cb : ℝ) (k : ℕ),
  IsUnit B → Bᴴ * Formalism.REAL.Jm (MP.ε τ) * B = gramAt D V τ → B *ᵥ (fun i => tauE D τ (zv d i)) = Pi.single (e none) 1 →
  V.rank = k + 1 →
  (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ u, GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)) =
    ⟪v, MP.σ τ (B * g * B⁻¹ * GlobalTheory.PackLoc.embOpt e (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℂ,
    Integrable (fun u : Formalism.REAL.UJ (M₀.ε τ) => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) (Formalism.REAL.muG (M₀.ε τ)) ↔
      Integrable (fun h => F (Formalism.MainNotions.S.umat h)) (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℝ, ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG (M₀.ε τ)) =
    lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  0 < c₁ → 0 < lam → Cb ≤ Real.exp q →
  (∀ g ∈ Formalism.MainNotions.S.UJset (MP.ε τ),
    Integrable (fun h => ⟪v, MP.σ τ (g * GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ)
      (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ∧
    ∫ h, ‖⟪v, MP.σ τ (g * GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ≤
      c₁ * Cb * Real.sqrt (∑ a, ‖g a (e none)‖ ^ 2) ^ (-(2 * (k : ℝ) + 7))) →
  ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
    Integrable (fun u => GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)))
      (Formalism.REAL.muG (M₀.ε τ)) ∧
    (∫ u, ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ))) *
      eu (B *ᵥ (g *ᵥ fun i => tauE D τ (zv d i))) ^ (2 * V.rank + 5) ≤ Real.exp q * ‖((lam * c₁ : ℝ) : ℂ)‖ := by
  intro D θ Y V d S S' M₀ MP τ e v₀ v g₀ B c₁ lam q Cb k hB hBJ hBz hk hmco hint hInt hc₁ hlam hCb hb g hg
  set z : Fin V.rank → ℂ := fun i => tauE D τ (zv d i) with hz
  have hBinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  have hBinv' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  have hg' : B * g * B⁻¹ ∈ Formalism.MainNotions.S.UJset (MP.ε τ) := by
    have hg0 : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
    show (B * g * B⁻¹)ᴴ * Formalism.REAL.Jm (MP.ε τ) * (B * g * B⁻¹) = Formalism.REAL.Jm (MP.ε τ)
    have hBi : (B⁻¹)ᴴ * Bᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hBinv', Matrix.conjTranspose_one]
    calc (B * g * B⁻¹)ᴴ * Formalism.REAL.Jm (MP.ε τ) * (B * g * B⁻¹)
        = (B⁻¹)ᴴ * (gᴴ * (Bᴴ * Formalism.REAL.Jm (MP.ε τ) * B) * g) * B⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (B⁻¹)ᴴ * (Bᴴ * Formalism.REAL.Jm (MP.ε τ) * B) * B⁻¹ := by rw [hBJ, hg0]
      _ = ((B⁻¹)ᴴ * Bᴴ) * Formalism.REAL.Jm (MP.ε τ) * (B * B⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (MP.ε τ) := by rw [hBi, hBinv']; simp
  obtain ⟨hbI, hbB⟩ := hb _ hg'
  set F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℂ :=
    fun x => ⟪v, MP.σ τ (B * g * B⁻¹ * GlobalTheory.PackLoc.embOpt e x) v⟫_ℂ with hF
  have hfun : (fun u => GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)))
      = fun u => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) := funext (hmco g hg)
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact (hint F).mpr hbI
  ·
    have hcol : B *ᵥ (g *ᵥ z) = fun a => (B * g * B⁻¹) a (e none) := by
      funext a
      have : (B * g * B⁻¹) *ᵥ (B *ᵥ z) = B *ᵥ (g *ᵥ z) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (B * g), hBinv, Matrix.mul_one, ← Matrix.mulVec_mulVec]
      rw [← this, hBz]
      simp [Matrix.mulVec_single]
    set L := eu (B *ᵥ (g *ᵥ z)) with hL
    have hLdef : L = Real.sqrt (∑ a, ‖(B * g * B⁻¹) a (e none)‖ ^ 2) := by
      rw [hL, hcol]; rfl
    have hI : (∫ u, ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ)))
        = lam * ∫ h, ‖F (Formalism.MainNotions.S.umat h)‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) := by
      have := hInt (fun x => ‖F x‖)
      rw [smul_eq_mul] at this
      rw [← this]
      congr 1
      funext u
      rw [hmco g hg u]
    have hL0 : 0 ≤ L := Real.sqrt_nonneg _
    have hexp : 2 * V.rank + 5 = 2 * k + 7 := by omega
    have hnorm : ‖((lam * c₁ : ℝ) : ℂ)‖ = lam * c₁ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hlam hc₁)]
    rw [hI, hnorm, hexp]
    have hInn : 0 ≤ ∫ h, ‖F (Formalism.MainNotions.S.umat h)‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) :=
      integral_nonneg (fun _ => norm_nonneg _)
    rcases hL0.lt_or_eq with hLp | hLz
    · have hbB' : ∫ h, ‖F (Formalism.MainNotions.S.umat h)‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))
          ≤ c₁ * Cb * L ^ (-(2 * (k : ℝ) + 7)) := by rw [hLdef]; exact hbB
      have hpow : L ^ (-(2 * (k : ℝ) + 7)) * L ^ (2 * k + 7) = 1 := by
        rw [Real.rpow_neg hL0, ← Real.rpow_natCast]
        push_cast
        exact inv_mul_cancel₀ (Real.rpow_pos_of_pos hLp _).ne'
      have hLn : 0 ≤ L ^ (2 * k + 7) := pow_nonneg hL0 _
      calc lam * (∫ h, ‖F (Formalism.MainNotions.S.umat h)‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) * L ^ (2 * k + 7)
          ≤ lam * (c₁ * Cb * L ^ (-(2 * (k : ℝ) + 7))) * L ^ (2 * k + 7) := by
            gcongr
        _ = lam * c₁ * Cb * (L ^ (-(2 * (k : ℝ) + 7)) * L ^ (2 * k + 7)) := by ring
        _ = lam * c₁ * Cb := by rw [hpow, mul_one]
        _ ≤ lam * c₁ * Real.exp q := by
            exact mul_le_mul_of_nonneg_left hCb (mul_pos hlam hc₁).le
        _ = Real.exp q * (lam * c₁) := by ring
    · rw [← hLz, zero_pow (by omega), mul_zero]
      exact mul_nonneg (Real.exp_pos q).le (mul_pos hlam hc₁).le

end GlobalTheory.PackLoc
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transversal_coefficient_decay_at_real_place : ∀ (D : D7) (θ : InfFam D) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S')
  (MP : DSModel V S) (τ : D.what₂.Tau) (e : Option (Fin Y.rank) ≃ Fin V.rank) (v₀ v : MP.H τ)
  (g₀ B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (c₁ lam q Cb : ℝ) (k : ℕ),
  IsUnit B → Bᴴ * Formalism.REAL.Jm (MP.ε τ) * B = gramAt D V τ → B *ᵥ (fun i => tauE D τ (zv d i)) = Pi.single (e none) 1 →
  V.rank = k + 1 →
  (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ u, GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)) =
    ⟪v, MP.σ τ (B * g * B⁻¹ * GlobalTheory.PackLoc.embOpt e (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℂ,
    Integrable (fun u : Formalism.REAL.UJ (M₀.ε τ) => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) (Formalism.REAL.muG (M₀.ε τ)) ↔
      Integrable (fun h => F (Formalism.MainNotions.S.umat h)) (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℝ, ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG (M₀.ε τ)) =
    lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  0 < c₁ → 0 < lam → Cb ≤ Real.exp q →
  (∀ g ∈ Formalism.MainNotions.S.UJset (MP.ε τ),
    Integrable (fun h => ⟪v, MP.σ τ (g * GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ)
      (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ∧
    ∫ h, ‖⟪v, MP.σ τ (g * GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ≤
      c₁ * Cb * Real.sqrt (∑ a, ‖g a (e none)‖ ^ 2) ^ (-(2 * (k : ℝ) + 7))) →
  ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
    Integrable (fun u => GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)))
      (Formalism.REAL.muG (M₀.ε τ)) ∧
    (∫ u, ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ))) *
      eu (B *ᵥ (g *ᵥ fun i => tauE D τ (zv d i))) ^ (2 * V.rank + 5) ≤ Real.exp q * ‖((lam * c₁ : ℝ) : ℂ)‖ := by
  atlas_forward_decl GlobalTheory.PackLoc.farClause
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.PackLoc.lipAt : ∀ (D : D7) (θ : InfFam D) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S')
  (MP : DSModel V S) (τ : D.what₂.Tau) (e : Option (Fin Y.rank) ≃ Fin V.rank) (v₀ v : MP.H τ)
  (g₀ : Matrix (Fin V.rank) (Fin V.rank) ℂ) (A : Matrix (Fin Y.rank) (Fin Y.rank) ℂ) (K lam q : ℝ) (c : ℂ),
  (∀ u, GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)) =
    ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ) →
  (∀ X ∈ lieAt Y τ, ∀ (s : ℝ) u,
    GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) =
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • (A * X * A⁻¹)) * GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ) →
  (∀ X ∈ lieAt Y τ, A * X * A⁻¹ ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  (∀ X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M₀).ε τ)), ∀ s : ℝ,
    Integrable (fun h => ‖⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖) (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ∧
    ∫ h, ‖⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ≤
        K * |s| * GlobalTheory.SepReal.hsn X) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℝ,
    (Integrable (fun u : Formalism.REAL.UJ (M₀.ε τ) => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) (Formalism.REAL.muG (M₀.ε τ)) ↔
      Integrable (fun h => F (Formalism.MainNotions.S.umat h)) (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) ∧
    ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG (M₀.ε τ)) =
      lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  0 < lam → lam * K ≤ Real.exp q * ‖c‖ →
  ∀ X ∈ lieAt Y τ, ∀ s : ℝ,
    Integrable (fun u => ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) -
      GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖) (Formalism.REAL.muG (M₀.ε τ)) ∧
    ∫ u, ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) -
      GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ)) ≤
      Real.exp q * ‖c‖ * |s| * hsn (A * X * A⁻¹) := by
  intro D θ Y V d S S' M₀ MP τ e v₀ v g₀ A K lam q c hB hA hL hK hH hlam hlk X hX s
  set X' := A * X * A⁻¹ with hX'
  have hX'L := hL X hX
  set F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℝ := fun x =>
    ‖⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X') * x)) v⟫_ℂ -
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e x) v⟫_ℂ‖ with hF
  have hfun : (fun u => ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) -
      GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖) =
      fun u => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) := by
    funext u
    rw [hA X hX s u, hB u]
  obtain ⟨hint, hbd⟩ := hK X' hX'L s
  obtain ⟨hiff, heq⟩ := hH F
  have hsnEq : GlobalTheory.SepReal.hsn X' = hsn X' := rfl
  have hsn0 : 0 ≤ hsn X' := Real.sqrt_nonneg _
  rw [hfun]
  refine ⟨hiff.2 hint, ?_⟩
  rw [heq, smul_eq_mul]
  have h1 : lam * ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ≤
      lam * (K * |s| * hsn X') := by
    rw [← hsnEq]
    exact mul_le_mul_of_nonneg_left hbd hlam.le
  have h2 : lam * (K * |s| * hsn X') ≤ Real.exp q * ‖c‖ * |s| * hsn X' := by
    have hm : 0 ≤ |s| * hsn X' := mul_nonneg (abs_nonneg s) hsn0
    calc lam * (K * |s| * hsn X') = (lam * K) * (|s| * hsn X') := by ring
      _ ≤ (Real.exp q * ‖c‖) * (|s| * hsn X') := mul_le_mul_of_nonneg_right hlk hm
      _ = Real.exp q * ‖c‖ * |s| * hsn X' := by ring
  exact h1.trans h2
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_coefficient_lipschitz_at_real_place : ∀ (D : D7) (θ : InfFam D) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S')
  (MP : DSModel V S) (τ : D.what₂.Tau) (e : Option (Fin Y.rank) ≃ Fin V.rank) (v₀ v : MP.H τ)
  (g₀ : Matrix (Fin V.rank) (Fin V.rank) ℂ) (A : Matrix (Fin Y.rank) (Fin Y.rank) ℂ) (K lam q : ℝ) (c : ℂ),
  (∀ u, GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)) =
    ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ) →
  (∀ X ∈ lieAt Y τ, ∀ (s : ℝ) u,
    GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) =
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • (A * X * A⁻¹)) * GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ) →
  (∀ X ∈ lieAt Y τ, A * X * A⁻¹ ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  (∀ X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M₀).ε τ)), ∀ s : ℝ,
    Integrable (fun h => ‖⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖) (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ∧
    ∫ h, ‖⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ≤
        K * |s| * GlobalTheory.SepReal.hsn X) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℝ,
    (Integrable (fun u : Formalism.REAL.UJ (M₀.ε τ) => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) (Formalism.REAL.muG (M₀.ε τ)) ↔
      Integrable (fun h => F (Formalism.MainNotions.S.umat h)) (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) ∧
    ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG (M₀.ε τ)) =
      lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  0 < lam → lam * K ≤ Real.exp q * ‖c‖ →
  ∀ X ∈ lieAt Y τ, ∀ s : ℝ,
    Integrable (fun u => ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) -
      GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖) (Formalism.REAL.muG (M₀.ε τ)) ∧
    ∫ u, ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) -
      GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ)) ≤
      Real.exp q * ‖c‖ * |s| * hsn (A * X * A⁻¹) := by
  atlas_forward_decl GlobalTheory.PackLoc.lipAt
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PackLoc

theorem isEnum_cast' {S : SPar} {n k : ℕ} (h : k = n) {lam : Fin n → ℝ} {ε : Fin n → Bool} (hE : IsEnum S lam ε) :
    IsEnum S (fun i : Fin k => lam (Fin.cast h i)) (fun i => ε (Fin.cast h i)) := by
  subst h
  simpa using hE

theorem UH_mul' {n : ℕ} {H a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Formalism.QuantumDeterminants.UH H) (hb : b ∈ Formalism.QuantumDeterminants.UH H) :
    a * b ∈ Formalism.QuantumDeterminants.UH H := by
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  show (a * b)ᴴ * H * (a * b) = H
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha', hb']

theorem conj_mul' {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ} (hB : IsUnit B) (x y : Matrix (Fin n) (Fin n) ℂ) :
    B * (x * y) * B⁻¹ = B * x * B⁻¹ * (B * y * B⁻¹) := by
  have hBi : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).1 hB)
  calc B * (x * y) * B⁻¹ = B * x * (B⁻¹ * B) * y * B⁻¹ := by rw [hBi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = B * x * B⁻¹ * (B * y * B⁻¹) := by simp only [Matrix.mul_assoc]

end GlobalTheory.PackLoc

end
end
