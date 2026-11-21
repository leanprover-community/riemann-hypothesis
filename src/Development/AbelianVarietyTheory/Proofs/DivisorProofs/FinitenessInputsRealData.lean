import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedThetaLiftInnerProductFormulaOfHyp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLiftMemCuspFormMultiplicitySpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftRowsAntitoneSignatureRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFormMinorProductEqProdHookProducts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardMeasureUnitaryPQEqVolumeSmulCompactDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeCoefficientsSqIntegrable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSignatureBlocksOfVectorAndFrame
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPsiOfOverK
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAdjointScalarParts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.VolUFactProdMulLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryLatticeStabilizerDetRoot
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.Monomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.MassNumeric
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.HostTorsionOrderLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfHom
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKTranslate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasDerivAtLogCosh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MatrixEntryNormSumUpperRightBlockElementPLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.T2SpaceIsNonarchimedeanLocalFieldSingleBlock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivEqZeroOfEven
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorMatrixCoefficientFormula
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLevelIndexMulSchwartzNormFormula
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDatumSourceLevelCharacterLaw
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteZetaIntegralThetaLiftEqPartialLValue

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockForm_minorProduct_eq_prod_hookProducts : ∀ (D : D7) (m n : ℕ) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ), (∀ τ, p τ + q τ ≤ m) → (∀ τ, p τ ≤ n ∧ q τ ≤ n) → (∀ τ, Antitone (ap τ) ∧ Antitone (am τ)) → Formalism.E.fock (Formalism.IndefR.Datum.delta (D := D) (m := m) (n := n) p q ap am) (Formalism.IndefR.Datum.delta p q ap am) = ∏ τ, ((hookOf (p τ) (ap τ) : ℂ) * (hookOf (q τ) (am τ) : ℂ)) := by
  first | exact @GlobalTheory.LowRowFock.fock_delta | exact GlobalTheory.LowRowFock.fock_delta | (intros; apply GlobalTheory.LowRowFock.fock_delta <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardMeasure_unitaryPQ_eq_volume_smul_compactDual : ∀ (cd : CDHaar) (p q : ℕ) (m : Measure (UpqT p q)), Lev.IsMinf m → m = ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU (p + q)) • cd.cd p q := by
  first | exact @GlobalTheory.LowRow.CompactDualScale.isMinf_eq_volU_smul_cd | exact GlobalTheory.LowRow.CompactDualScale.isMinf_eq_volU_smul_cd | (intros; apply GlobalTheory.LowRow.CompactDualScale.isMinf_eq_volU_smul_cd <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRow.CompactDualCoef

open GlobalTheory.RealCoefSq GlobalTheory.Mem.Vol.Scale GlobalTheory.Mem.Vol GlobalTheory.AdelicScalar

section Perm

variable {p q n : ℕ} {ε : Fin n → Bool}

def permFrame (e : Fin p ⊕ Fin q ≃ Fin n) : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ :=
  (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix id e.symm

theorem mul_permFrame (e : Fin p ⊕ Fin q ≃ Fin n) (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    X * permFrame e = X.submatrix id e.symm := by
  ext i j
  simp [permFrame, Matrix.mul_apply, Matrix.one_apply]

theorem permFrame_conjTranspose_mul (e : Fin p ⊕ Fin q ≃ Fin n) (Y : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) :
    (permFrame e)ᴴ * Y = Y.submatrix e.symm id := by
  ext i j
  simp [permFrame, Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply]

theorem permFrame_herm {e : Fin p ⊕ Fin q ≃ Fin n} (h : Sorts ε e) :
    (permFrame e)ᴴ * Formalism.UG.Jpq p q * permFrame e = Formalism.REAL.Jm ε := by
  rw [Matrix.mul_assoc, mul_permFrame, permFrame_conjTranspose_mul, ← h.reindex_Jpq, Matrix.reindex_apply,
    Matrix.submatrix_submatrix]
  rfl

theorem frameInv_permFrame {e : Fin p ⊕ Fin q ≃ Fin n} (h : Sorts ε e)
    (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    frameInv ε (permFrame e) * X * permFrame e = Matrix.reindex e e X := by
  have : frameInv ε (permFrame e) * X * permFrame e =
      Formalism.REAL.Jm ε * ((permFrame e)ᴴ * (Formalism.UG.Jpq p q * X * permFrame e)) := by
    simp only [frameInv, Matrix.mul_assoc]
  rw [this, mul_permFrame, permFrame_conjTranspose_mul, Matrix.submatrix_submatrix,
    show (e.symm ∘ id : Fin n → Fin p ⊕ Fin q) = e.symm from rfl,
    show (id ∘ e.symm : Fin n → Fin p ⊕ Fin q) = e.symm from rfl,
    ← Matrix.submatrix_mul_equiv (Formalism.UG.Jpq p q) X e.symm e.symm e.symm,
    ← Matrix.reindex_apply, h.reindex_Jpq, ← Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.one_mul,
    Matrix.reindex_apply]

end Perm

theorem map_frameEquiv_cd (cd : CDHaar) {p q n : ℕ} {ε : Fin n → Bool} (B : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ)
    (hB : Bᴴ * Formalism.UG.Jpq p q * B = Formalism.REAL.Jm ε) (hn : p + q = n) :
    (cd.cd p q).map (frameEquiv B hB hn) = (trueScale cd n ε : ENNReal) • Formalism.REAL.muG ε := by
  classical
  let e₀ : Fin p ⊕ Fin q ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  let ε₀ : Fin n → Bool := fun i => (e₀.symm i).isLeft
  have h₀ : Sorts ε₀ e₀ := ⟨fun i => by simp [ε₀], fun j => by simp [ε₀]⟩
  have hC : (B.submatrix e₀.symm id)ᴴ * Formalism.REAL.Jm ε₀ * B.submatrix e₀.symm id = Formalism.REAL.Jm ε := by
    rw [← h₀.reindex_Jpq, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, hB]
    rfl
  have hcount : Nat.card {a // ε a = true} = p := (GlobalTheory.SignCount.card_true_eq _ hC).symm.trans h₀.card_true
  obtain ⟨P, Q, e, he⟩ := exists_sorts ε
  have hP : P = p := he.card_true.symm.trans hcount
  have hQ : Q = q := by have := Sorts.add_eq e; omega
  subst hP hQ
  have hBp := permFrame_herm he
  have hfun : (frameEquiv (permFrame e) hBp hn : UpqT P Q → Formalism.REAL.UJ ε) = he.equiv := funext fun b =>
    umat_injective (by rw [umat_frameEquiv, frameInv_permFrame he, he.umat_equiv])
  have hmap0 : (cd.cd P Q).map (frameEquiv (permFrame e) hBp hn) =
      (trueScale cd n ε : ENNReal) • Formalism.REAL.muG ε := by
    rw [hfun]
    ext A hA
    rw [Measure.map_apply he.measurable_equiv hA, ← he.set_eq]
    exact (cdScaleIs_trueScale cd n ε P Q e he.1 he.2 A hA).symm
  exact map_frameEquiv hBp hB hn (cd.cd P Q) _ hmap0

end GlobalTheory.LowRow.CompactDualCoef

namespace GlobalTheory.LowRow.CompactDualCoef

open GlobalTheory.RealCoefSq GlobalTheory.Mem.Vol.Scale GlobalTheory.Mem.Vol GlobalTheory.AdelicScalar

theorem inv_integral_coef_sq : GlobalTheory.Published.FormalDegreeCompactDual → ∀ (cd : CDHaar) {D : D7} (W : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel W S) (Fr : Frames W), IsFrames W Fr → (∀ ρ, (W.sig (tauE D ρ)).1 + (W.sig (tauE D ρ)).2 = W.rank) → ∀ ρ, StrictAnti (M.lam ρ) → (∀ a, ∃ z : ℤ, M.lam ρ a - ((W.rank : ℝ) - 1) / 2 = (z : ℝ)) → ∀ w : M.H ρ, ‖w‖ = 1 → Integrable (fun b : Upq W ρ => ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2) (cd.cd _ _) ∧ (∫ b : Upq W ρ, ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2 ∂(cd.cd _ _))⁻¹ = (∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), |M.lam ρ a - M.lam ρ b|) / ∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  intro hHC cd D W S M Fr hFr hsig ρ hanti hhalf w hw
  classical
  haveI : BorelSpace (Upq W ρ) := ⟨rfl⟩
  have hn := hsig ρ
  have hmap := map_frameEquiv_cd cd _ (frame_herm M hFr ρ) hn
  have hme : MeasurableEmbedding (frameEquiv _ (frame_herm M hFr ρ) hn) :=
    (frameEquiv _ (frame_herm M hFr ρ) hn).toHomeomorph.measurableEmbedding
  have hk : (fun b : Upq W ρ => ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2) =
      (fun g : Formalism.REAL.UJ (M.ε ρ) => ‖⟪w, M.σ ρ (umat g) w⟫_ℂ‖ ^ 2) ∘ frameEquiv _ (frame_herm M hFr ρ) hn :=
    funext fun b => by simp only [Function.comp_apply, rep_realMat M hFr ρ hn b]
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have hpr := hHC cd (trueScale cd) (cdScaleIs_trueScale cd) W.rank (M.ε ρ) (M.lam ρ) ⟨hanti, hhalf⟩ (M.H ρ)
    (M.σ ρ) w (M.ds ρ) hw0
  rw [hw, one_pow, one_div] at hpr
  have hpos : 0 < (∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), |M.lam ρ a - M.lam ρ b|) /
      ∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
    refine div_pos (Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_)
      (Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_)
    · exact abs_pos.2 (sub_ne_zero.2 (hanti.injective.ne (ne_of_lt (Finset.mem_filter.1 hb).2)))
    · have := (Finset.mem_filter.1 hb).2
      exact sub_pos.2 (by exact_mod_cast this)
  have hint : Integrable (fun g : Formalism.REAL.UJ (M.ε ρ) => ‖⟪w, M.σ ρ (umat g) w⟫_ℂ‖ ^ 2)
      ((trueScale cd W.rank (M.ε ρ) : ENNReal) • Formalism.REAL.muG (M.ε ρ)) := by
    by_contra hni
    rw [integral_undef hni, _root_.inv_zero] at hpr
    exact hpos.ne hpr
  rw [← hmap] at hint
  rw [hk]
  refine ⟨hme.integrable_map_iff.1 hint, ?_⟩
  rw [show (∫ b, ((fun g : Formalism.REAL.UJ (M.ε ρ) => ‖⟪w, M.σ ρ (umat g) w⟫_ℂ‖ ^ 2) ∘
      frameEquiv _ (frame_herm M hFr ρ) hn) b ∂(cd.cd _ _)) =
      ∫ g, ‖⟪w, M.σ ρ (umat g) w⟫_ℂ‖ ^ 2 ∂((trueScale cd W.rank (M.ε ρ) : ENNReal) • Formalism.REAL.muG (M.ε ρ)) by
    rw [← hmap, hme.integral_map]; rfl]
  exact hpr

end GlobalTheory.LowRow.CompactDualCoef
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_integral_sq_discreteSeries_coefficient_compactDual : GlobalTheory.Published.FormalDegreeCompactDual → ∀ (cd : CDHaar) {D : D7} (W : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel W S) (Fr : Frames W), IsFrames W Fr → (∀ ρ, (W.sig (tauE D ρ)).1 + (W.sig (tauE D ρ)).2 = W.rank) → ∀ ρ, StrictAnti (M.lam ρ) → (∀ a, ∃ z : ℤ, M.lam ρ a - ((W.rank : ℝ) - 1) / 2 = (z : ℝ)) → ∀ w : M.H ρ, ‖w‖ = 1 → Integrable (fun b : Upq W ρ => ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2) (cd.cd _ _) ∧ (∫ b : Upq W ρ, ‖⟪w, M.rep ρ (realMat W Fr ρ b) w⟫_ℂ‖ ^ 2 ∂(cd.cd _ _))⁻¹ = (∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), |M.lam ρ a - M.lam ρ b|) / ∏ a : Fin W.rank, ∏ b ∈ Finset.univ.filter (fun b : Fin W.rank => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  atlas_forward_decl GlobalTheory.LowRow.CompactDualCoef.inv_integral_coef_sq
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow.ParWidth

theorem mem_holPar_kapW {Rk : Ranks} (h : HCParam Rk) (p q : ℕ) (hpq : Odd (p + q)) {x : ℚ} {b : Bool}
    (hx : (x, b) ∈ Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW h p q)) :
    ∃ n < p + q, x = Formalism.L2.NTheta.lamAt h n := by
  unfold Formalism.L2.NTheta.holPar at hx
  obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hx
  have e := Formalism.L2.NTheta.holEnt_kapW h p q hpq a
  have hx' : x = Formalism.L2.NTheta.holEnt p q (Formalism.L2.NTheta.kapW h p q) a := (congrArg Prod.fst ha).symm
  rcases a with i | c
  · exact ⟨i, by omega, hx'.trans (by simpa using e)⟩
  · exact ⟨p + c, by omega, hx'.trans (by simpa using e)⟩

theorem lamAt_anti {Rk : Ranks} (h : HCParam Rk) {n n' : ℕ} (hnn : n ≤ n') (hn : n' < Rk.r) :
    Formalism.L2.NTheta.lamAt h n' ≤ Formalism.L2.NTheta.lamAt h n := by
  have mono : ∀ d : ℕ, n + d < Rk.r → Formalism.L2.NTheta.lamAt h (n + d) ≤ Formalism.L2.NTheta.lamAt h n := by
    intro d
    induction d with
    | zero => intro _; exact le_rfl
    | succ d ih =>
      intro hd
      exact (Formalism.L2.NTheta.lamAt_lt h (n + d) (by omega)).le.trans (ih (by omega))
  have := mono (n' - n) (by omega)
  rwa [show n + (n' - n) = n' by omega] at this

theorem lamAt_b {Rk : Ranks} (h : HCParam Rk) (c : ℕ) (hc : c < Rk.m) :
    Formalism.L2.NTheta.lamAt h (Rk.k - 1 + c) = -h.b ⟨c, hc⟩ := by
  unfold Formalism.L2.NTheta.lamAt
  rw [dif_neg (by omega), dif_pos (by omega)]
  simp

theorem le_toNat_floor (x : ℚ) : x ≤ ((⌊x⌋.toNat : ℕ) : ℚ) + 1 := by
  have h1 := Int.lt_floor_add_one x
  have h2 : ((⌊x⌋ : ℤ) : ℚ) ≤ (((⌊x⌋.toNat : ℕ) : ℤ) : ℚ) := by exact_mod_cast Int.self_le_toNat _
  rw [Int.cast_natCast] at h2
  linarith

end GlobalTheory.LowRow.ParWidth

namespace GlobalTheory.LowRow.ParWidth

theorem width_le (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) 0 - Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) (D.R.r - 1) ≤
      (degAt D i σ ρ : ℚ) + D.R.nV + 1 := by
  have hsig : (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
  have hp : pW D i ρ = D.R.k + i := by simp only [pW, hsig, Ranks.sigW]; omega
  have hq : qW D i ρ = D.R.m - (i + 1) := by simp only [qW, hsig, Ranks.sigW]
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  set h := D.hc (lab σ ρ) with hh
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hnV : (D.R.nV : ℚ) = (D.R.k : ℚ) + D.R.m - 1 + D.R.t := by
    simp only [Ranks.nV, Ranks.r]; push_cast [show 1 ≤ D.R.k + D.R.m by omega]; ring

  have hP0 : (aPlAt D i σ ρ 0 : ℚ) + 1 ≥
      Formalism.L2.NTheta.lamAt h 0 + h.e i - ((D.R.k + i : ℕ) - (0 + 1) : ℚ) - ((D.R.t : ℚ) + 1) / 2 := by
    have := le_toNat_floor (Formalism.L2.NTheta.lamAt h 0 + h.e i - ((D.R.k + i : ℕ) - ((0 : ℕ) + 1) : ℚ) - ((D.R.t : ℚ) + 1) / 2)
    unfold aPlAt aPl
    rw [hp, if_pos (by omega)]
    simpa using this
  have hdeg : (aPlAt D i σ ρ 0 : ℚ) + (if 0 < qW D i ρ then (aMiAt D i σ ρ 0 : ℚ) else 0) ≤ degAt D i σ ρ := by
    have e1 : aPlAt D i σ ρ 0 ≤ ∑ n ∈ Finset.range (pW D i ρ), aPlAt D i σ ρ n :=
      Finset.single_le_sum (f := aPlAt D i σ ρ) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
    have e2 : (if 0 < qW D i ρ then aMiAt D i σ ρ 0 else 0) ≤ ∑ n ∈ Finset.range (qW D i ρ), aMiAt D i σ ρ n := by
      split_ifs with hq0
      · exact Finset.single_le_sum (f := aMiAt D i σ ρ) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hq0)
      · exact Nat.zero_le _
    have e3 := Nat.add_le_add e1 e2
    unfold degAt
    have : ((aPlAt D i σ ρ 0 + (if 0 < qW D i ρ then aMiAt D i σ ρ 0 else 0) : ℕ) : ℚ) ≤
        ((∑ n ∈ Finset.range (pW D i ρ), aPlAt D i σ ρ n + ∑ n ∈ Finset.range (qW D i ρ), aMiAt D i σ ρ n : ℕ) : ℚ) := by
      exact_mod_cast e3
    push_cast at this
    split_ifs at this ⊢ <;> simpa using this
  by_cases hq0 : (i : ℕ) + 1 < D.R.m
  · have hqpos : 0 < qW D i ρ := by rw [hq]; omega
    rw [if_pos hqpos] at hdeg
    have hM0 : (aMiAt D i σ ρ 0 : ℚ) + 1 ≥
        -(h.e i + Formalism.L2.NTheta.lamAt h (D.R.r - 1) + ((D.R.m - (i + 1) : ℕ) : ℚ) + ((D.R.t : ℚ) - 1) / 2) := by
      have := le_toNat_floor (-(h.e i + Formalism.L2.NTheta.lamAt h (D.R.r - 1) + ((D.R.m - (i + 1) : ℕ) : ℚ) + ((D.R.t : ℚ) - 1) / 2))
      unfold aMiAt aMi
      rw [hp, hq, if_pos (by omega), show D.R.k + ↑i + (D.R.m - (↑i + 1) - 0) - 1 = D.R.r - 1 by omega]
      simpa using this
    have c1 : (((D.R.k + i : ℕ) : ℚ)) = D.R.k + (i : ℚ) := by push_cast; ring
    have c2 : (((D.R.m - (i + 1) : ℕ) : ℚ)) = D.R.m - (i : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [c1] at hP0
    rw [c2] at hM0
    rw [hnV]
    linarith
  · have him : (i : ℕ) = D.R.m - 1 := by omega
    rw [if_neg (by rw [hq]; omega), add_zero] at hdeg
    have hb : Formalism.L2.NTheta.lamAt h (D.R.r - 1) = -h.b i := by
      rw [show D.R.r - 1 = D.R.k - 1 + (i : ℕ) by omega, lamAt_b h i i.2]
    have hg := h.gap_be i
    have c1 : (((D.R.k + i : ℕ) : ℚ)) = D.R.k + (i : ℚ) := by push_cast; ring
    rw [c1] at hP0
    have hmi : (i : ℚ) = D.R.m - 1 := by
      rw [him, Nat.cast_sub (by omega)]; simp
    rw [hnV, hb]
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    linarith

end GlobalTheory.LowRow.ParWidth

open GlobalTheory.LowRow.ParWidth in

theorem GlobalTheory.LowRow.lam_par_width : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ i σ s, IsEmbOverK D σ s → ∀ ρ, StrictAnti ((R.MW i σ).lam ρ) ∧ (∀ a, ∃ z : ℤ, (R.MW i σ).lam ρ a - (((Wc D i).rank : ℝ) - 1) / 2 = (z : ℝ)) ∧ ∀ a b, |(R.MW i σ).lam ρ a - (R.MW i σ).lam ρ b| ≤ (degAt D i σ ρ : ℝ) + D.R.nV + 3 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _hC i σ s hσ ρ
  have hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ := hσ.2
  have hat : labE σ (lab σ ρ) = tauE D ρ := ((GlobalTheory.GalLift.labels_overK σ).1 hK).2 ρ
  obtain ⟨hanti, qv, hqv, hS⟩ := (R.MW i σ).enum ρ
  have hpar : parAt (Wc D i) σ ρ = Formalism.L2.NTheta.holPar _ _ (kapAt (Wc D i) σ ρ) := if_pos hat
  have hsig : (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  have hr : ((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2 = D.R.r := by
    rw [hsig]; simp only [Ranks.sigW, Ranks.r]; omega
  have hrodd : Odd D.R.r := by
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have hodd : Odd (((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2) := hr ▸ hrodd
  have hent : ∀ a, ∃ n < D.R.r, (R.MW i σ).lam ρ a = ((Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) n : ℚ) : ℝ) := by
    intro a
    have hmem : (qv a, (R.MW i σ).ε ρ a) ∈ parAt (Wc D i) σ ρ := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rw [hpar] at hmem
    obtain ⟨n, hn, e⟩ := mem_holPar_kapW _ _ _ hodd hmem
    exact ⟨n, hr ▸ hn, by rw [hqv a, e]⟩
  have hrank : (Wc D i).rank = D.R.r := by
    rw [← hr]; exact (Formalism.BasicNotions.sig_sum _ (D.sp.W_sig _) _).symm
  refine ⟨hanti, fun a => ?_, fun a b => ?_⟩
  · obtain ⟨n, -, e⟩ := hent a
    obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int (D.hc (lab σ ρ)) n
    obtain ⟨w, hw⟩ := hrodd
    refine ⟨z - w, ?_⟩
    rw [e, hz, hrank, hw]
    push_cast
    ring
  · obtain ⟨n, hn, ea⟩ := hent a
    obtain ⟨n', hn', eb⟩ := hent b
    have hW := width_le D i σ ρ
    have l1 := lamAt_anti (D.hc (lab σ ρ)) (Nat.zero_le n) hn
    have l2 := lamAt_anti (D.hc (lab σ ρ)) (Nat.zero_le n') hn'
    have u1 := lamAt_anti (D.hc (lab σ ρ)) (show n ≤ D.R.r - 1 by omega) (by omega)
    have u2 := lamAt_anti (D.hc (lab σ ρ)) (show n' ≤ D.R.r - 1 by omega) (by omega)
    have key : |Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) n - Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) n'| ≤
        (degAt D i σ ρ : ℚ) + D.R.nV + 3 := by
      rw [abs_sub_le_iff]; constructor <;> linarith
    rw [ea, eb, ← Rat.cast_sub, ← Rat.cast_abs]
    exact_mod_cast key
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftModelParameter_decreasing_halfIntegral_width : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ i σ s, IsEmbOverK D σ s → ∀ ρ, StrictAnti ((R.MW i σ).lam ρ) ∧ (∀ a, ∃ z : ℤ, (R.MW i σ).lam ρ a - (((Wc D i).rank : ℝ) - 1) / 2 = (z : ℝ)) ∧ ∀ a b, |(R.MW i σ).lam ρ a - (R.MW i σ).lam ρ b| ≤ (degAt D i σ ρ : ℝ) + D.R.nV + 3 := by
  atlas_forward_decl GlobalTheory.LowRow.lam_par_width
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow

theorem volU_ge_inv_pow_of_formalDeg (r : ℕ) (hr : 1 ≤ r) :
    (((r : ℝ) ^ r)⁻¹) ^ r ≤ ReciprocityTheory.ChartRestriction.DS.volU r := by
  unfold ReciprocityTheory.ChartRestriction.DS.volU
  have hrpos : (0 : ℝ) < (r : ℝ) ^ r := by positivity
  rw [show (((r : ℝ) ^ r)⁻¹) ^ r = ∏ _i ∈ Finset.range r, ((r : ℝ) ^ r)⁻¹ by
    rw [Finset.prod_const, Finset.card_range]]
  apply Finset.prod_le_prod
  · intro i _; positivity
  · intro i hi
    have hi' : i < r := Finset.mem_range.mp hi
    have hfac : (i.factorial : ℝ) ≤ (r : ℝ) ^ r := by
      have h1 : i.factorial ≤ r.factorial := Nat.factorial_le hi'.le
      have h2 : r.factorial ≤ r ^ r := Nat.factorial_le_pow r
      exact_mod_cast h1.trans h2
    have hfpos : (0 : ℝ) < (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
    have hpi : (1 : ℝ) ≤ 2 * Real.pi ^ (i + 1) := by
      have : (1 : ℝ) ≤ Real.pi ^ (i + 1) := one_le_pow₀ (by linarith [Real.pi_gt_three])
      linarith
    calc ((r : ℝ) ^ r)⁻¹ ≤ (i.factorial : ℝ)⁻¹ := inv_anti₀ hfpos hfac
      _ = 1 / (i.factorial : ℝ) := by rw [one_div]
      _ ≤ 2 * Real.pi ^ (i + 1) / (i.factorial : ℝ) := by gcongr

theorem formalDeg_div_volU_log_bound : ∀ (r n : ℕ) (d : ℝ) (lam : Fin r → ℝ), 1 ≤ r → 3 ≤ n → 0 ≤ d → StrictAnti lam → (∀ a b, |lam a - lam b| ≤ d + n + 3) → 0 < ReciprocityTheory.ChartRestriction.DS.volU r ∧ 0 < (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|) / (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) ∧ Real.log ((∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|) / (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) / ReciprocityTheory.ChartRestriction.DS.volU r) ≤ 2 + (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2)) := by
  intro r n d lam hr hn hd hlam hbd
  set P : ℝ := ∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b| with hPdef
  set D : ℝ := ∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) with hDdef
  set V : ℝ := ReciprocityTheory.ChartRestriction.DS.volU r with hVdef
  set M : ℝ := d + n + 3 with hMdef
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hM1 : (1 : ℝ) ≤ M := by rw [hMdef]; linarith
  have hVlow := volU_ge_inv_pow_of_formalDeg r hr
  have hVpos : 0 < V := lt_of_lt_of_le (by positivity) hVlow
  have hPpos : 0 < P := by
    apply Finset.prod_pos
    intro a _
    apply Finset.prod_pos
    intro b hb
    have hab : a < b := (Finset.mem_filter.mp hb).2
    exact abs_pos.mpr (sub_ne_zero.mpr (hlam hab).ne')
  have hD1 : 1 ≤ D := by
    have : (∏ _a : Fin r, ∏ _b ∈ Finset.univ.filter (fun b : Fin r => _a < b), (1 : ℝ)) ≤ D := by
      apply Finset.prod_le_prod
      · intro a _; positivity
      · intro a _
        apply Finset.prod_le_prod
        · intro b _; positivity
        · intro b hb
          have hab : a < b := (Finset.mem_filter.mp hb).2
          have : (a : ℕ) + 1 ≤ (b : ℕ) := hab
          have : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast this
          linarith
    simpa using this
  have hDpos : 0 < D := lt_of_lt_of_le one_pos hD1
  have hPle : P ≤ M ^ (r * r) := by
    have : P ≤ ∏ _a : Fin r, M ^ r := by
      apply Finset.prod_le_prod
      · intro a _; exact Finset.prod_nonneg (fun b _ => abs_nonneg _)
      · intro a _
        calc (∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|)
            ≤ ∏ _b ∈ Finset.univ.filter (fun b : Fin r => a < b), M :=
              Finset.prod_le_prod (fun b _ => abs_nonneg _) (fun b _ => hbd a b)
          _ = M ^ (Finset.univ.filter (fun b : Fin r => a < b)).card := Finset.prod_const _
          _ ≤ M ^ r := by
              apply pow_le_pow_right₀ hM1
              calc (Finset.univ.filter (fun b : Fin r => a < b)).card ≤ (Finset.univ : Finset (Fin r)).card :=
                    Finset.card_filter_le _ _
                _ = r := by simp
    calc P ≤ ∏ _a : Fin r, M ^ r := this
      _ = M ^ (r * r) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  have hVinv : V⁻¹ ≤ (r : ℝ) ^ (r * r) := by
    have h := inv_anti₀ (by positivity) hVlow
    rw [inv_pow, inv_inv, ← pow_mul] at h
    exact h
  have hQpos : 0 < P / D / V := by positivity
  have hQle : P / D / V ≤ (M * r) ^ (r * r) := by
    calc P / D / V ≤ P / V := by
          gcongr
          exact div_le_self hPpos.le hD1
      _ = P * V⁻¹ := div_eq_mul_inv _ _
      _ ≤ M ^ (r * r) * (r : ℝ) ^ (r * r) := by
          apply mul_le_mul hPle hVinv (by positivity) (by positivity)
      _ = (M * r) ^ (r * r) := (mul_pow _ _ _).symm
  refine ⟨hVpos, div_pos hPpos hDpos, ?_⟩
  have hsq : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hMn : M ≤ n * (d + 2) := by
    rw [hMdef]; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ n - 1) hd]
  have hr2 : (r : ℝ) ≤ 2 * Real.sqrt 2 * (r : ℝ) ^ 2 := by nlinarith
  have hX : M * r ≤ 2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2) := by
    calc M * r ≤ (n * (d + 2)) * (2 * Real.sqrt 2 * (r : ℝ) ^ 2) :=
          mul_le_mul hMn hr2 (by positivity) (by positivity)
      _ = 2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2) := by ring
  have hMr : 0 < M * r := by positivity
  calc Real.log (P / D / V) ≤ Real.log ((M * r) ^ (r * r)) := Real.log_le_log hQpos hQle
    _ = ((r * r : ℕ) : ℝ) * Real.log (M * r) := Real.log_pow _ _
    _ = (r : ℝ) ^ 2 * Real.log (M * r) := by push_cast; ring
    _ ≤ (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2)) := by
        gcongr
    _ ≤ 2 + (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2)) := by linarith

end GlobalTheory.LowRow
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalDegree_div_volume_unitaryGroup_log_bound : ∀ (r n : ℕ) (d : ℝ) (lam : Fin r → ℝ), 1 ≤ r → 3 ≤ n → 0 ≤ d → StrictAnti lam → (∀ a b, |lam a - lam b| ≤ d + n + 3) → 0 < ReciprocityTheory.ChartRestriction.DS.volU r ∧ 0 < (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|) / (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) ∧ Real.log ((∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), |lam a - lam b|) / (∏ a : Fin r, ∏ b ∈ Finset.univ.filter (fun b : Fin r => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) / ReciprocityTheory.ChartRestriction.DS.volU r) ≤ 2 + (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (d + 2)) := by
  atlas_forward_decl GlobalTheory.LowRow.formalDeg_div_volU_log_bound
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow

theorem formalDegreeUpperC_of_hypotheses : GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), FormalDegreeUpperC R F := by
  intro hp D G _ _ Pl0 T A Ks _ _ _ R F
  intro i t σ s P cμ cη m ω BW f₀ f c io hL
  obtain ⟨hcore, -, hσ, -⟩ := hL
  have h5 : GlobalTheory.Core5 R F := ⟨hcore.lev, hcore.grp, hcore.fam, hcore.models, hcore.thP⟩
  intro Fr hFr ρ mR hmR e he
  dsimp only
  obtain ⟨hanti, hhalf, hwid⟩ := GlobalTheory.T.liftModelParameter_decreasing_halfIntegral_width R F h5 i σ s hσ ρ
  have hsig : ∀ ρ', ((Wc D i).sig (tauE D ρ')).1 + ((Wc D i).sig (tauE D ρ')).2 = (Wc D i).rank :=
    fun ρ' => (GlobalTheory.T.liftRows_antitone_signature_rank D i σ ρ').2.2.1
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have h1 : 1 ≤ (Wc D i).rank := by
    rw [hrk]; have := D.R.m_add_three_le_k; have := D.R.two_le_m
    simp only [Formalism.BasicNotions.Ranks.r]; omega
  have h3 : 3 ≤ D.R.nV := by
    have := D.R.m_add_three_le_k; have := D.R.two_le_m; have := D.R.three_m_lt_t
    simp only [Formalism.BasicNotions.Ranks.nV, Formalism.BasicNotions.Ranks.r]; omega
  obtain ⟨hint, hinv⟩ := GlobalTheory.T.inv_integral_sq_discreteSeries_coefficient_compactDual hp D.cd (Wc D i) _ (R.MW i σ) Fr hFr hsig ρ hanti hhalf _ he
  have hm := GlobalTheory.T.standardMeasure_unitaryPQ_eq_volume_smul_compactDual D.cd _ _ mR hmR
  rw [hsig ρ] at hm
  obtain ⟨hvol, hQpos, hlog⟩ := GlobalTheory.T.formalDegree_div_volume_unitaryGroup_log_bound (Wc D i).rank D.R.nV (degAt D i σ ρ) ((R.MW i σ).lam ρ) h1 h3
    (by positivity) hanti hwid
  have e1 : (((Wc D i).rank : ℕ) : ℝ) = (D.R.r : ℝ) := by exact_mod_cast hrk
  rw [e1] at hlog
  subst hm
  refine ⟨hint.smul_measure ENNReal.ofReal_ne_top, ?_, ?_⟩
  · rw [integral_smul_measure, ENNReal.toReal_ofReal hvol.le, smul_eq_mul]
    refine mul_pos hvol ?_
    have : 0 < (∫ b : Upq (Wc D i) ρ, ‖⟪((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
        (R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ b) ((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ‖ ^ 2 ∂(D.cd.cd _ _))⁻¹ := by
      rw [hinv]; exact hQpos
    exact inv_pos.mp this
  · rw [integral_smul_measure, ENNReal.toReal_ofReal hvol.le, smul_eq_mul, mul_inv, hinv, mul_comm, ← div_eq_mul_inv]
    exact hlog

end GlobalTheory.LowRow
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalDegreeRealPlaceUpperBound_of_harishChandra : GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), FormalDegreeUpperC R F := by
  atlas_forward_decl GlobalTheory.LowRow.formalDegreeUpperC_of_hypotheses
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow.SignedPerm

section General

variable {K : Type} [Field K] [NumberField K]

end General

section Host

theorem finite_and_ncard_le : ∀ (D : D7) (n : ℕ),
    {g : Matrix (Fin n) (Fin n) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)}.Finite ∧
    {g : Matrix (Fin n) (Fin n) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)}.ncard
      ≤ NumberField.Units.torsionOrder D.host.E ^ n * n.factorial := by
  intro D n
  have hcm := D.host.isCMField_hostE
  exact UpperTheory.Mu.unitary_integral_finite_and_ncard_le
    (fun φ x => IsCMField.complexEmbedding_complexConj D.host.E φ x) n

end Host

end GlobalTheory.LowRow.SignedPerm
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_unitary_matrices_finite_card_le : ∀ (D : D7) (n : ℕ), {g : Matrix (Fin n) (Fin n) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)}.Finite ∧ {g : Matrix (Fin n) (Fin n) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)}.ncard ≤ NumberField.Units.torsionOrder D.host.E ^ n * n.factorial := by
  atlas_forward_decl GlobalTheory.LowRow.SignedPerm.finite_and_ncard_le
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRow.StdMass

variable {D : D7}

theorem coord_isIntegral (V : HSp D) (hL : V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame))
    {x : Fin V.rank → D.host.E} (hx : x ∈ L0c D V) (k : Fin V.rank) : IsIntegral ℤ (x k) := by
  have key : ∀ y ∈ V.L0, ∃ a : 𝓞 D.host.E, (a : D.host.E) = V.frame.repr y k := by
    intro y hy
    rw [hL] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      by_cases h : j = k
      · exact ⟨1, by simp [h]⟩
      · exact ⟨0, by simp [Finsupp.single_apply, h]⟩
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, ha⟩ := hy
      obtain ⟨b, hb⟩ := hz
      exact ⟨a + b, by simp [ha, hb]⟩
    | smul r y _ hy =>
      obtain ⟨a, ha⟩ := hy
      refine ⟨r * a, ?_⟩
      rw [← algebraMap_smul D.host.E r y, map_smul]
      simp [ha, Algebra.smul_def]
  have hx' : ∑ i, x i • V.frame i ∈ V.L0 := hx
  obtain ⟨a, ha⟩ := key _ hx'
  have e : V.frame.repr (∑ i, x i • V.frame i) k = x k := by
    rw [← Module.Basis.equivFun_symm_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [← e, ← ha]
  exact RingOfIntegers.isIntegral_coe a

theorem mem_lattice_of_rational_mem_completion (V : HSp D) (v : Fin V.rank → D.host.E)
    (h : (fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] v k) ∈ latHat D.host.F D.host.E (L0c D V)) : v ∈ L0c D V := by
  let f := V.frame.equivFun.toLinearMap
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := V.L0.map (f.restrictScalars (𝓞 D.host.E))
  have hL : (L : Set (Fin V.rank → D.host.E)) = L0c D V := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ∑ i, V.frame.equivFun x i • V.frame i ∈ V.L0
      rwa [V.frame.sum_equivFun]
    · intro hw
      refine ⟨V.frame.equivFun.symm w, ?_, V.frame.equivFun.apply_symm_apply w⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact hw
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective w
    have hx : x ∈ Submodule.span D.host.E (V.L0 : Set V.V) := by
      rw [V.standardTuple_isLattice.span_eq_top]; trivial
    have := Submodule.mem_map_of_mem (f := f) hx
    rw [Submodule.map_span] at this
    exact this
  have hr := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank L (V.standardTuple_isLattice.fg.map _) hsp).1 v
  rw [← hL]
  refine hr.1 ?_
  have hle : latHat D.host.F D.host.E (L0c D V) ≤ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin V.rank → D.host.E)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, x, hx, rfl⟩
    rw [← hL] at hx
    exact AddSubgroup.subset_closure ⟨a, fun w => ha w, x, hx, rfl⟩
  exact hle h

theorem card_stab_le (V : HSp D) (hg : V.gram = 1)
    (hL : V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame)) :
    Nat.card (Formalism.UG.stabAt (GlobalTheory.Mass.ratIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)
      (GlobalTheory.Mass.Levels.latStab V) 1) ≤ NumberField.Units.torsionOrder D.host.E ^ V.rank * V.rank.factorial := by
  obtain ⟨hSf, hSc⟩ := GlobalTheory.T.integral_unitary_matrices_finite_card_le D V.rank
  have hx : ∀ x : Formalism.UG.stabAt (GlobalTheory.Mass.ratIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)
      (GlobalTheory.Mass.Levels.latStab V) 1, ∃ u : GL (Fin V.rank) D.host.E,
        u ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram ∧
        Formalism.UG.bc (inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) u =
          HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram x.1.1 := fun x => by
    obtain ⟨u, hu, e⟩ := Subgroup.mem_map.1 x.1.2
    exact ⟨u, hu, e⟩
  choose u hu hue using hx
  have hunit : ∀ x, (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E)ᴴ * (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 :=
    fun x => by
    have h := hu x
    change Formalism.UG.cT _ (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = V.gram at h
    rw [hg, Matrix.mul_one] at h
    convert h using 2
    ext a b
    rfl
  have hint : ∀ x a b, IsIntegral ℤ ((u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b) := fun x a b => by
    have hK : x.1.1 ∈ GlobalTheory.Mass.Levels.latStab V := by
      have := x.2
      simpa [Formalism.UG.stabAt] using this
    have hej : (Pi.single b 1 : Fin V.rank → D.host.E) ∈ L0c D V := by
      show ∑ i, (Pi.single b (1 : D.host.E) : Fin V.rank → D.host.E) i • V.frame i ∈ V.L0
      rw [Finset.sum_eq_single b (fun c _ hc => by simp [hc]) (by simp), hL]
      rw [Pi.single_eq_same, one_smul]
      exact Submodule.subset_span ⟨b, rfl⟩
    have hy : (fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (Pi.single b (1 : D.host.E) : Fin V.rank → D.host.E) k) ∈
        latHat D.host.F D.host.E (L0c D V) :=
      AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, _, hej, rfl⟩
    have h2 := ((GlobalTheory.Mass.Levels.mem_latStab V x.1.1).1 hK _).1 hy
    have e : (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram x.1.1).1 *ᵥ
        (fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (Pi.single b (1 : D.host.E) : Fin V.rank → D.host.E) k) =
        fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) k b := by
      rw [← hue x]
      funext k
      change ((u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) *ᵥ
        ((inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) ∘ (Pi.single b 1))) k =
          (inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) ((u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) k b)
      rw [← RingHom.map_mulVec]
      simp [Matrix.mulVec_single_one]
    rw [e] at h2
    exact coord_isIntegral V hL (mem_lattice_of_rational_mem_completion V _ h2) a
  let f : Formalism.UG.stabAt (GlobalTheory.Mass.ratIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)
      (GlobalTheory.Mass.Levels.latStab V) 1 →
      {g : Matrix (Fin V.rank) (Fin V.rank) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)} :=
    fun x => ⟨(u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E), hunit x, hint x⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = u y := congrArg Subtype.val hxy
    have h2 : u x = u y := Units.ext h1
    have h3 : HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram x.1.1 =
        HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram y.1.1 := by
      rw [← hue x, ← hue y, h2]
    have h4 : x.1.1 = y.1.1 := Subtype.ext h3
    exact Subtype.ext (Subtype.ext h4)
  haveI := hSf.to_subtype
  calc Nat.card _ ≤ Nat.card {g : Matrix (Fin V.rank) (Fin V.rank) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)} :=
        Nat.card_le_card_of_injective f hf
    _ = Set.ncard {g : Matrix (Fin V.rank) (Fin V.rank) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)} :=
        Nat.card_coe_set_eq _
    _ ≤ _ := hSc

theorem massLower_of_stdV : ∀ D : D7, StdV D → MassLower D := by
  intro D hS i _
  obtain ⟨h1, h2⟩ := hS i
  have hg : (Vc D i).gram = 1 := Matrix.ext fun a b => by
    rw [Matrix.one_apply]
    exact h1 a b
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have e : gramAt D (Vc D i) τ = 1 := Matrix.ext fun a b => by
      simp [gramAt, hg, Matrix.one_apply]
    rw [e]
    exact Matrix.PosDef.one
  have hK := GlobalTheory.Mass.Levels.latStab_compact_open (Vc D i)
  have hfc := GlobalTheory.Mass.finiteClasses_unitary (GlobalTheory.DefiniteQuotient.cmExt D)
    (GlobalTheory.DefiniteQuotient.gram_hermND (Vc D i)) (GlobalTheory.DefiniteQuotient.isTotDef_of_posDef (Vc D i) hpd) hK.1 hK.2
  have hle := hfc.inv_card_le 1
  have hpos := hfc.stabOrder_pos (DoubleCoset.mk _ _ 1)
  rw [GlobalTheory.Mass.stabOrder_mk] at hpos
  have hc := card_stab_le (Vc D i) hg h2
  have hr : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  unfold GlobalTheory.Mass.unitaryMass
  refine le_trans ?_ hle
  rw [one_div, ← hr]
  exact inv_anti₀ (by exact_mod_cast hpos) (by exact_mod_cast hc)

end GlobalTheory.LowRow.StdMass
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryMassLowerBound_of_orthonormalLatticeFrames : ∀ D : D7, StdV D → MassLower D := by
  atlas_forward_decl GlobalTheory.LowRow.StdMass.massLower_of_stdV
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRow

variable {D : D7}

section Main

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem inner_HW_lowC {F : Face D A} (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (x y : (R.HW i σ).H) :
    inner ℂ x y = ((∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℝ) : ℝ) : ℂ) *
      ipM (R.MW i σ) (R.νW i) (R.fdW i) ((R.HW i σ).e x) ((R.HW i σ).e y) := by
  rw [(hR.models.HW i σ).2.2, ipAt]
  push_cast
  rfl

theorem exists_frames_lowC {F : Face D A} (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) :
    ∃ Fr : Frames (Wc D i), IsFrames (Wc D i) Fr ∧ ∃ mR : ∀ ρ, Measure (Upq (Wc D i) ρ), ∀ ρ, Lev.IsMinf (mR ρ) := by
  obtain ⟨⟨Fr, h1⟩, h2⟩ := (hR.models.νW i).1.2.2 R.θ hR.models.inf
  exact ⟨Fr, h1, (h2 Fr h1).1⟩

variable {R} {F : Face D A} {i : Fin D.R.m} {t : T} {σ : D.what₂.LL →+* ℂ} {s : ℂ ≃+* ℂ} {P : LevelP R.Pg D.R.r ℂ}
    {cμ cη : (AE D)ˣ →* Circle} {m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ)}
    {BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ} {f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ}
    {c : CoefA (Vc D i)} {io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank}
    (hd : IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io)
    {ν : Measure (GA D (Vc D i))} {𝓕 : Set (GA D (Vc D i))} (hν : IsMeasDef (Vc D i) (levV R i t P m) ν 𝓕)

include hd in
open Datum in
theorem exists_covol_lowC : ∃ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))),
    IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 := by
  obtain ⟨p, hp⟩ := hd.2.2.2.2.2.2.2.1.1.2.norm.1
  exact ⟨p.1, p.2, hp⟩

include hd hν in

theorem scalar_bound_lowC (h7 : LevelIndexNormC R F) (h8 : MassLower D) (h9 : FormalDegreeUpperC R F) {b : ℝ} (hb : Sizes D i b)
    {μ : @Measure (Datum.WO (Vc D i) (Wc D i)) (Datum.measMx _ _)} {𝓧 : Set (Datum.WO (Vc D i) (Wc D i))}
    (hμ : Datum.IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧) {Fr : Frames (Wc D i)} (hFr : IsFrames (Wc D i) Fr)
    {mR : ∀ ρ, Measure (Upq (Wc D i) ρ)} (hmR : ∀ ρ, Lev.IsMinf (mR ρ)) (v : ∀ ρ, lowT (R.MW i σ) ρ)
    (hv : ∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) (x : HeightOneSpectrum (𝓞 D.host.E) → Fin D.R.r → ℂ)
    (hx : ∀ w a, ‖x w a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2 - (1 + (D.R.t : ℝ)) / 2))
    (dim : ℝ) (hdim : 1 ≤ dim) (l : ℝ)
    (hl : l = (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℝ)) * dim * (ν 𝓕).toReal *
      (∏ ρ, ((hookOf (pW D i ρ) (aPlAt D i σ ρ) : ℝ) * (hookOf (qW D i ρ) (aMiAt D i σ ρ) : ℝ))) * Datum.nrm2 μ 𝓧 f /
      dOff D (finS R t) * (∏ ρ, ∫ b, ‖⟪((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
        (R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ b) ((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ‖ ^ 2 ∂(mR ρ)) *
      ‖eulerOff D (finS R t) x‖) :
    0 < l ∧ mainTerm D i σ - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lp D b ≤ Real.log l := by
  obtain ⟨a1, a2⟩ := h7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd
  have a3 := a2 μ 𝓧 hμ
  rw [Finset.prod_inv_distrib] at a3
  have hS := dLoc_bound (finS R t)
  have a4 : (levV R i t P m).relIndex (GlobalTheory.Mass.Levels.latLev (Vc D i)) ≠ 0 := fun h => by
    rw [h, Nat.cast_zero, zero_mul] at a3
    exact (inv_pos.2 hS.1).ne a3
  have hp := hd.1.models.vpos i
  have a5 := GlobalTheory.VolIndex.vol_eq_index_mul_mass D (Vc D i) _ ν 𝓕 (D.sp.V_sig _) hp a1 a4 (isOpen_level _ _ _) hν
  obtain ⟨s1, s2, s3, s4, s5⟩ := GlobalTheory.AdelicScalar.SizeBounds.sizes D i b hb
  have a6 := fun ρ => h9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd Fr hFr ρ (mR ρ) (hmR ρ) (v ρ) (hv ρ)
  have r1 := D.R.rank_add_five_le
  have r2 := D.R.m_add_three_le_k
  have r3 := D.R.two_le_m
  rw [hl, a5]
  exact UpperTheory.Mu.numeric_bound D.R.f D.R.nV D.R.r D.what₂.card_Tau (Lp D b) (3 * (D.R.r : ℝ) * b) _ dim _ _ _ _ _ _ _ _
    (fun ρ => (degAt D i σ ρ : ℝ)) (by unfold Ranks.nV Ranks.r; omega) (by unfold Ranks.nV Ranks.r; omega)
    (by unfold Ranks.r; omega) (UpperTheory.Mu.one_le_f D.R) s1 s2
    (by positivity) s4 (NumberField.Units.torsionOrder_pos _) (UpperTheory.Mu.host_torsionOrder_le D.host) (h8 i hp) hdim a3 (eulerOff_lower _ x hx) (dOff_bound _) hS
    (fun ρ => mul_pos (Nat.cast_pos.2 (hookOf_pos _ _)) (Nat.cast_pos.2 (hookOf_pos _ _)))
    (fun ρ => by exact_mod_cast one_le_dimK i σ ρ) (fun ρ => (a6 ρ).2.1) (fun ρ => ⟨Nat.cast_nonneg _, s5 σ ρ⟩)
    fun ρ => (a6 ρ).2.2

include hd hν in

theorem term_eval_lowC (h3 : InnerProductFormulaC R F) (h4 : FockCoefficientC R F)
    {μ : @Measure (Datum.WO (Vc D i) (Wc D i)) (Datum.measMx _ _)} {𝓧 : Set (Datum.WO (Vc D i) (Wc D i))}
    (hμ : Datum.IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧) {Fr : Frames (Wc D i)} (hFr : IsFrames (Wc D i) Fr)
    {mR : ∀ ρ, Measure (Upq (Wc D i) ρ)} (hmR : ∀ ρ, Lev.IsMinf (mR ρ)) (v : ∀ ρ, lowT (R.MW i σ) ρ)
    (U₁ U₂ : (R.HW i σ).H) (w : c.W) (hw : ‖w‖ = 1) (z : ℂ)
    (hZ : ∀ v₁ v₂ : (R.MW i σ).Vec, HasSum (fun y : FinCos (Wc D i) (levW R i) =>
        @l2 _ (Datum.measMx _ _) μ 𝓧 (ω (1, y.rep) f) f *
          starRingEnd ℂ (petW R i (rTr (Wc D i) y.rep ((R.HW i σ).e U₁ v₁)) ((R.HW i σ).e U₂ v₂)))
      (z * starRingEnd ℂ (petW R i ((R.HW i σ).e U₁ v₁) ((R.HW i σ).e U₂ v₂)))) :
    l2 ν 𝓕 (upLift R i ω (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e U₁ fun ρ => v ρ))
        (upLift R i ω (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e U₂ fun ρ => v ρ)) =
      ((ν 𝓕).toReal : ℂ) * (Formalism.E.fock (deltaAtEmb D i σ) (deltaAtEmb D i σ) * z *
        starRingEnd ℂ (ipM (R.MW i σ) (R.νW i) (R.fdW i) ((R.HW i σ).e U₂) ((R.HW i σ).e U₁)) *
        ((∏ ρ, ∫ b, ‖⟪((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
          (R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ b) ((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ‖ ^ 2 ∂(mR ρ) : ℝ) : ℂ)) := by
  have m1 := HMod_mem (hd.1.models.HW i σ) U₁
  have a1 := (h3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd ν 𝓕 hν μ 𝓧 hμ Fr hFr mR hmR _ m1 _ (HMod_mem (hd.1.models.HW i σ) U₂) v v
    (io (PiTensorProduct.tprod ℂ v) w) (io (PiTensorProduct.tprod ℂ v) w)).2.2.2
  have a2 := h4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd μ 𝓧 hμ
  have e : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw]; simp
  refine a1.trans (congrArg _ ?_)
  exact @zeta_eval D (Vc D i) (Wc D i) _ _ _ _ (R.HW i σ) _ (inner_HW_lowC R hd.1 i σ) R.θ _ _ U₁ U₂ m1 (fun ρ => v ρ) (levW R i) _
    (Datum.measMx _ _) μ 𝓧 ω _ f Fr (realMat_mem i hFr) mR hmR _ z (fun x hx g hg => e ▸ a2 x hx g hg v v w w) hZ

end Main

section Final

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
  {F : Face D A} {i : Fin D.R.m} {t : T} {σ : D.what₂.LL →+* ℂ} {s : ℂ ≃+* ℂ} {P : LevelP R.Pg D.R.r ℂ}
    {cμ cη : (AE D)ˣ →* Circle} {m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ)}
    {BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ} {f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ}
    {c : CoefA (Vc D i)} {io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank}
    (hd : IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io)
    {ν : Measure (GA D (Vc D i))} {𝓕 : Set (GA D (Vc D i))} (hν : IsMeasDef (Vc D i) (levV R i t P m) ν 𝓕)
    {I : Type} [Fintype I] {y : I → Bridge.Gf (Vc D i)} (HV : HMod (Bridge.Gf (Vc D i) → c.W))
    (hV : HV.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m))
        (chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)))
      (Bridge.adInner (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)) y))

include hd hν hV in
theorem integrableOn_isLift_lowC (x : HV.H) (v : ∀ ρ, lowT (R.MW i σ) ρ) (g : GA D (Wc D i)) :
    IntegrableOn (fun h => Datum.thetaKO ω h g (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ v) (c.ext (HV.e x) h)))) 𝓕 ν := by
  have := integrableOn_lift hd.2.2.2.2.2.1 (D.sp.V_sig _) (hd.1.models.vpos i) c hd.2.2.2.2.2.2.2.2.2.1 _ _ (HMod_mem hV x)
      (ptL R i σ BW f (io (PiTensorProduct.tprod ℂ v))) (fun w => by rw [ptL_apply]; exact hd.2.2.2.2.2.2.2.2.1 _) hν g
  simp only [ptL_apply] at this
  convert this using 10

include hd hν hV in

theorem exists_isLift_lowC (h1 : LiftIsCuspC R F) : ∃ th, IsLift R i σ ω (ptAt R i σ BW f) c io ν 𝓕 HV th := by
  refine exists_linear_lift ν 𝓕 (R.HW i σ).e (fun (v : ∀ ρ, lowT (R.MW i σ) ρ) (g : GA D (Wc D i)) U => U (fun ρ => v ρ) g)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) HV.e c.ext
    (fun v g h w => Datum.thetaKO ω h g (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ v) w))) (fun v g h w w' => ?_)
    (fun v g h a w => ?_) (integrableOn_isLift_lowC hd hν HV hV) fun x => ?_
  · rw [← ptL_apply, map_add, Datum.thetaKO, map_add]
    rfl
  · rw [← ptL_apply, map_smul, thetaKO_smul]
    rfl
  · refine (h1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd ν 𝓕 hν _ (HMod_mem hV x)).elim fun U hU => ?_
    refine (HMod_onto (hd.1.models.HW i σ) hU.1).elim fun u hu => ⟨u, fun v g => ?_⟩
    refine (congrFun (congrFun (congrArg DFunLike.coe hu) _) g).trans ((hU.2 v g).trans ?_)
    unfold Lift.thetaPInt
    rfl

include hd hν hV in
set_option maxHeartbeats 800000 in

theorem form_key_lowC (hy : Bridge.IsReps (Bridge.ratF (Vc D i)) (grpOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m)) y)
    (h2 : SourceLevelLawC R F) (h3 : InnerProductFormulaC R F)
    (th : HV.H →ₗ[ℂ] (R.HW i σ).H) (hth : IsLift R i σ ω (ptAt R i σ BW f) c io ν 𝓕 HV th) (v : ∀ ρ, lowT (R.MW i σ) ρ)
    (hv : ∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) (U₁ U₂ : (R.HW i σ).H) {κ : Type} [Fintype κ]
    (b : OrthonormalBasis κ ℂ c.W) {μ : @Measure (Datum.WO (Vc D i) (Wc D i)) (Datum.measMx _ _)}
    {𝓧 : Set (Datum.WO (Vc D i) (Wc D i))} (hμ : Datum.IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧) {Fr : Frames (Wc D i)}
    (hFr : IsFrames (Wc D i) Fr) {mR : ∀ ρ, Measure (Upq (Wc D i) ρ)} (hmR : ∀ ρ, Lev.IsMinf (mR ρ)) :
    inner ℂ (LinearMap.adjoint th U₁) (LinearMap.adjoint th U₂) =
      ((∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℝ) : ℝ) : ℂ) ^ 2 * ∑ k,
        l2 ν 𝓕 (upLift R i ω (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ v) (b k))) ((R.HW i σ).e U₁ fun ρ => v ρ))
          (upLift R i ω (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ v) (b k))) ((R.HW i σ).e U₂ fun ρ => v ρ)) := by
  have hc : c.Is := hd.2.2.2.2.2.2.2.2.2.1
  have hio := hd.2.2.2.2.2.2.2.2.2.2
  have hm := HMod_mem (hd.1.models.HW i σ)
  have hR := fun U₁ U₂ Q₁ Q₂ => h3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd ν 𝓕 hν μ 𝓧 hμ Fr hFr mR hmR _ (hm U₁) _ (hm U₂) v v Q₁ Q₂
  have hφ := ptL_apply R i σ BW f (io (PiTensorProduct.tprod ℂ v))
  have a1 : ∀ w, Datum.IsThetaFunO R.ψ (Vc D i) (Wc D i) (ptL R i σ BW f (io (PiTensorProduct.tprod ℂ v)) w) := fun w => by rw [hφ]; exact hd.2.2.2.2.2.2.2.2.1 _
  have a2 : ∀ u ∈ GinfC (Vc D i), ∀ w, ω (u, 1) (ptL R i σ BW f (io (PiTensorProduct.tprod ℂ v)) w) = ptL R i σ BW f (io (PiTensorProduct.tprod ℂ v)) (c.ρ u w) := fun u hu w => by rw [hφ, hφ]; exact hio.1 u hu _ w
  have a3 : ∀ κ ∈ Lev.levA (Vc D i) (lev D.sp.cm (Vc D i).gram (R.βV i) (datV i R.Pg (R.Q t) P m)), ∀ w,
      ω (κ, 1) (ptL R i σ BW f (io (PiTensorProduct.tprod ℂ v)) w) = (Lev.levChi (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m) κ)⁻¹ • ptL R i σ BW f (io (PiTensorProduct.tprod ℂ v)) w :=
    fun κ hκ w => by rw [hφ]; exact h2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd κ hκ _
  have a4 : ∀ x g, (R.HW i σ).e (th x) (fun ρ => v ρ) g = ∫ h in 𝓕, Datum.thetaKO ω h g (ptL R i σ BW f (io (PiTensorProduct.tprod ℂ v)) (c.ext (HV.e x) h)) ∂ν :=
    fun x g => by simp only [hφ]; exact (hth x v g).2
  have a5 : ∀ (U : (R.HW i σ).H) w h, IntegrableOn (fun g => Datum.thetaKO ω h g (ptL R i σ BW f (io (PiTensorProduct.tprod ℂ v)) w) *
      starRingEnd ℂ ((R.HW i σ).e U (fun ρ => v ρ) g)) (R.fdW i) (R.νW i) :=
    fun U w h => by rw [hφ]; exact (hR U U (io (PiTensorProduct.tprod ℂ v) w) 0).1 h
  have a6 : ∀ k, IntegrableOn (fun h =>
      l2 (R.νW i) (R.fdW i) (fun g => Datum.thetaKO ω h g (ptL R i σ BW f (io (PiTensorProduct.tprod ℂ v)) (b k))) ((R.HW i σ).e U₁ fun ρ => v ρ) *
      starRingEnd ℂ (l2 (R.νW i) (R.fdW i) (fun g => Datum.thetaKO ω h g (ptL R i σ BW f (io (PiTensorProduct.tprod ℂ v)) (b k))) ((R.HW i σ).e U₂ fun ρ => v ρ))) 𝓕 ν :=
    fun k => by
      rw [hφ]
      exact (hR U₁ U₂ (io (PiTensorProduct.tprod ℂ v) (b k)) (io (PiTensorProduct.tprod ℂ v) (b k))).2.1
  clear hR
  have key := form_eq_sum hd.2.2.2.2.2.1 c hc (R.βV i) (datV i R.Pg (R.Q t) P m) (ptL R i σ BW f (io (PiTensorProduct.tprod ℂ v))) a1 a2 a3 (R.HW i σ) (inner_HW_lowC R hd.1 i σ)
    hν hy HV hV (fun ρ => v ρ) hv th a4 a5 U₁ U₂ b a6
  simp only [hφ] at key
  exact key

end Final

section Scalar

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
  {F : Face D A} {i : Fin D.R.m} {t : T} {σ : D.what₂.LL →+* ℂ} {s : ℂ ≃+* ℂ} {P : LevelP R.Pg D.R.r ℂ}
    {cμ cη : (AE D)ˣ →* Circle} {m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ)}
    {BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ} {f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ}
    {c : CoefA (Vc D i)} {io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank}
    (hd : IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io)
    {ν : Measure (GA D (Vc D i))} {𝓕 : Set (GA D (Vc D i))} (hν : IsMeasDef (Vc D i) (levV R i t P m) ν 𝓕)

include hd hν in

theorem scalar_of_form_key_lowC (h3 : InnerProductFormulaC R F) (h4 : FockCoefficientC R F) (h5 : DeltaNorm D)
    (h6 : FiniteZetaC R F) (h7 : LevelIndexNormC R F) (h8 : MassLower D) (h9 : FormalDegreeUpperC R F) {b : ℝ} (hb : Sizes D i b)
    {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] (th : X →ₗ[ℂ] (R.HW i σ).H)
    (key : ∀ {μ : @Measure (Datum.WO (Vc D i) (Wc D i)) (Datum.measMx _ _)} {𝓧 : Set (Datum.WO (Vc D i) (Wc D i))}
      (_ : Datum.IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧) {Fr : Frames (Wc D i)} (_ : IsFrames (Wc D i) Fr)
      {mR : ∀ ρ, Measure (Upq (Wc D i) ρ)} (_ : ∀ ρ, Lev.IsMinf (mR ρ)) (v : ∀ ρ, lowT (R.MW i σ) ρ) (_ : ∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) (U₁ U₂ : (R.HW i σ).H)
      {κ : Type} [Fintype κ] (b : OrthonormalBasis κ ℂ c.W), inner ℂ (LinearMap.adjoint th U₁) (LinearMap.adjoint th U₂) =
      ((∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℝ) : ℝ) : ℂ) ^ 2 * ∑ k,
        l2 ν 𝓕 (upLift R i ω (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ v) (b k))) ((R.HW i σ).e U₁ fun ρ => v ρ))
          (upLift R i ω (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ v) (b k))) ((R.HW i σ).e U₂ fun ρ => v ρ)))
    (ev : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) (hev : typePart R i σ t P ev ≠ ⊥) :
    ∃ l : ℝ, 0 < l ∧ (∀ x ∈ typePart R i σ t P ev, th (adjLev P th x) = (l : ℂ) • x) ∧
      mainTerm D i σ - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lp D b ≤ Real.log l := by
  have hc : c.Is := hd.2.2.2.2.2.2.2.2.2.1
  obtain ⟨v, -, hv, -⟩ := hd.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨μ, 𝓧, hμ⟩ := exists_covol_lowC hd
  obtain ⟨Fr, hFr, mR, hmR⟩ := exists_frames_lowC R hd.1 i
  obtain ⟨x, hx, hZ⟩ := h6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd μ 𝓧 hμ ev hev
  have hdim : (1 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℂ c.W)) : ℕ) := by
    have := hc.2.2.2.1
    rw [Fintype.card_fin]
    exact_mod_cast Module.finrank_pos
  obtain ⟨b1, b2⟩ := scalar_bound_lowC hd hν h7 h8 h9 hb hμ hFr hmR v hv x hx _ hdim _ rfl
  refine ⟨_, b1, scalar_adjLev P th _ hev _ _ b1 fun U₁ hU₁ U₂ => ?_, b2⟩
  refine form_algebra _ _ _ _ _ _ _ _ _ _ _ _ _ ((h5 i σ).trans ?_) (key hμ hFr hmR v hv U₁ U₂ (stdOrthonormalBasis ℂ c.W))
    (fun k => term_eval_lowC hd hν h3 h4 hμ hFr hmR v U₁ U₂ _ ((stdOrthonormalBasis ℂ c.W).orthonormal.1 k) _
      (hZ _ hU₁ _ (HMod_mem (hd.1.models.HW i σ) U₂))) (eq_of_value (R.HW i σ) (inner_HW_lowC R hd.1 i σ) U₁ U₂)
  push_cast
  rfl

end Scalar

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem adelC_of_innerProductFormula (R : RealDat D A Ks) (F : Face D A) :
    LiftIsCuspC R F → SourceLevelLawC R F → InnerProductFormulaC R F → FockCoefficientC R F → DeltaNorm D →
      FiniteZetaC R F → LevelIndexNormC R F → MassLower D → FormalDegreeUpperC R F → AdelC R F := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 hR i b hb t ht σ s hσ P hP cμ cη m hm ω hω BW hBW f₀ f hf hpt c hc io hio ν 𝓕 hν I _ y hy
    HV hV
  have hd : IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io := ⟨hR, ht, hσ, hP, hm, hω, hBW, hf, hpt, hc, hio⟩
  exact ⟨exists_isLift_lowC hd hν HV hV h1, fun th hth =>
    scalar_of_form_key_lowC hd hν h3 h4 h5 h6 h7 h8 h9 hb th fun {_ _} hμ {_} hFr {_} hmR v hv U₁ U₂ {_} _ b =>
      form_key_lowC hd hν HV hV hy h2 h3 th hth v hv U₁ U₂ b hμ hFr hmR⟩

end GlobalTheory.LowRow
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLift_scalar_of_innerProductFormula : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), LiftIsCuspC R F → SourceLevelLawC R F → InnerProductFormulaC R F → FockCoefficientC R F → DeltaNorm D → FiniteZetaC R F → LevelIndexNormC R F → MassLower D → FormalDegreeUpperC R F → AdelC R F := by
  atlas_forward_decl GlobalTheory.LowRow.adelC_of_innerProductFormula
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow.ZetaProd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem prod_fin_getD_list (f : ℂˣ → ℂ) : ∀ l : List ℂˣ, ∏ a : Fin l.length, f (l.getD a 1) = (l.map f).prod
  | [] => by simp
  | b :: l => by
    rw [List.length_cons, Fin.prod_univ_succ]
    simp [prod_fin_getD_list f l]

theorem prod_fin_getD (m : Multiset ℂˣ) {n : ℕ} (hn : m.card = n) (f : ℂˣ → ℂ) :
    ∏ a : Fin n, f (m.toList.getD a 1) = (m.map f).prod := by
  have hl : m.toList.length = n := (Multiset.length_toList m).trans hn
  subst hl
  rw [prod_fin_getD_list]
  conv_rhs => rw [← Multiset.coe_toList m]
  rw [Multiset.map_coe, Multiset.prod_coe]

variable {D : D7}

open Classical in

def zetaParams (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (B : GlobalTheory.LFun.Fam D.host.E) (cμ : (AE D)ˣ →* Circle) :
    HeightOneSpectrum (𝓞 D.host.E) → Fin D.R.r → ℂ := fun w a =>
  if OffS D S w then
    (((B w).toList.getD a 1 : ℂˣ) : ℂ) * ((((GlobalTheory.LFun.val cμ)⁻¹ w : ℂˣ)) : ℂ) * GlobalTheory.LFun.npow w (-((1 + (D.R.t : ℂ)) / 2))
  else 0

theorem re_neg_half : (-((1 + (D.R.t : ℂ)) / 2)).re = -((1 + (D.R.t : ℝ)) / 2) := by
  rw [show -((1 + (D.R.t : ℂ)) / 2) = ((-((1 + (D.R.t : ℝ)) / 2) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]

theorem norm_zetaParams_le {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {B : GlobalTheory.LFun.Fam D.host.E} (cμ : (AE D)ˣ →* Circle)
    (hcard : ∀ w, OffS D S w → (B w).card = D.R.r)
    (hb : ∀ w, OffS D S w → ∀ β ∈ B w, ‖(β : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (a : Fin D.R.r) :
    ‖zetaParams S B cμ w a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2 - (1 + (D.R.t : ℝ)) / 2) := by
  unfold zetaParams
  split_ifs with hw
  · have ha : (a : ℕ) < (B w).toList.length := by rw [Multiset.length_toList, hcard w hw]; exact a.2
    have hβ : (B w).toList.getD a 1 ∈ B w := by
      rw [List.getD_eq_getElem _ _ ha]
      exact Multiset.mem_toList.1 (List.getElem_mem ha)
    have hN : (0 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by
      have := two_le_absNorm w
      linarith
    rw [norm_mul, norm_mul, Pi.inv_apply, Units.val_inv_eq_inv_val, norm_inv, GlobalTheory.LFun.norm_val, inv_one, mul_one,
      GlobalTheory.LFun.norm_npow, re_neg_half, sub_eq_add_neg, Real.rpow_add hN]
    exact mul_le_mul_of_nonneg_right (hb w hw _ hβ) (Real.rpow_nonneg hN.le _)
  · rw [norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem eulerOff_zetaParams {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} {B : GlobalTheory.LFun.Fam D.host.E} (cμ : (AE D)ˣ →* Circle)
    (hcard : ∀ w, OffS D S w → (B w).card = D.R.r)
    (hb : ∀ w, OffS D S w → ∀ β ∈ B w, ‖(β : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2)) :
    eulerOff D S (zetaParams S B cμ) = GlobalTheory.LFun.LSD D S B cμ ((1 + (D.R.t : ℂ)) / 2) := by
  set x := zetaParams S B cμ with hxdef
  have hx := norm_zetaParams_le cμ hcard hb
  obtain ⟨h1, h2, -⟩ := sum_bound (OffS D S) (κ := Fin D.R.r) (fun a => ‖x a.1.1 a.2‖) (fun _ => norm_nonneg _) fun a => by
    refine (hx _ _).trans ?_
    have ht : (D.R.r : ℝ) + 5 ≤ D.R.t := by exact_mod_cast D.R.rank_add_five_le
    have := two_le_absNorm a.1.1
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
  have hm : Multipliable fun p : {w // OffS D S w} × Fin D.R.r => (1 - x p.1.1 p.2)⁻¹ := by
    have := multipliable_one_add_of_summable (f := fun p : {w // OffS D S w} × Fin D.R.r => (1 - x p.1.1 p.2)⁻¹ - 1)
      (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) (h2.mul_left 2))
    · simpa using this
    · have hx2 : ‖x p.1.1 p.2‖ ≤ 1 / 2 := h1 p
      have h3 : 1 / 2 ≤ ‖1 - x p.1.1 p.2‖ := by
        have := norm_sub_norm_le (1 : ℂ) (x p.1.1 p.2)
        rw [norm_one] at this
        linarith
      have hne : 1 - x p.1.1 p.2 ≠ 0 := fun h => by rw [h, norm_zero] at h3; linarith
      have e : (1 - x p.1.1 p.2)⁻¹ - 1 = x p.1.1 p.2 * (1 - x p.1.1 p.2)⁻¹ := by
        field_simp
        ring
      have h4 : ‖1 - x p.1.1 p.2‖⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) two_pos]
        linarith
      rw [e, norm_mul, norm_inv]
      nlinarith [norm_nonneg (x p.1.1 p.2)]
  have hp := hm.hasProd.prod_fiberwise fun b => hasProd_fintype _
  rw [eulerOff, ← hp.tprod_eq]
  show _ = GlobalTheory.LFun.eulerProd (GlobalTheory.LFun.above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F))))
    (GlobalTheory.LFun.twist B (GlobalTheory.LFun.val cμ)⁻¹) ((1 + (D.R.t : ℂ)) / 2)
  rw [GlobalTheory.LFun.eulerProd]
  let e : {w // OffS D S w} ≃ {w // w ∉ GlobalTheory.LFun.above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F)))} :=
    Equiv.subtypeEquivRight fun w => (GlobalTheory.IndefiniteRowSideFullHecke.ThetaAdjointScalarOnComponents.offS_iff S w).trans (by simp [GlobalTheory.LFun.above])
  rw [← e.tprod_eq]
  refine tprod_congr fun w => ?_
  show _ = GlobalTheory.LFun.locL _ w.1 _
  rw [GlobalTheory.LFun.locL_twist, ← prod_fin_getD (B w.1) (hcard w.1 w.2)]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp only [hxdef, zetaParams, if_pos w.2]

end GlobalTheory.LowRow.ZetaProd

namespace GlobalTheory.LowRow

theorem finiteZetaC_of_finiteZetaL : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    FiniteZetaL R F → FiniteZetaC R F := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hZ i t σ s P cμ cη m ω BW f₀ f c io hd μ 𝓧 hμ ev hne
  obtain ⟨B, hsys, hb, -, hsum⟩ := hZ i t σ s P cμ cη m ω BW f₀ f c io hd μ 𝓧 hμ ev hne
  have hcard : ∀ w, OffS D (finS R t) w → (B w).card = D.R.r := fun w hw => by
    have hv : w.under (𝓞 D.host.F) ∉ ((finS R t : Finset _) : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
      simpa using (GlobalTheory.IndefiniteRowSideFullHecke.ThetaAdjointScalarOnComponents.offS_iff _ w).1 hw
    rcases hsys _ hv w rfl with ⟨-, h, -⟩ | ⟨-, τ, ϖ, α, -, -, h, -⟩
    · exact h
    · rw [h]
      exact GlobalTheory.LGrp.card_bcParam _ α
  refine ⟨ZetaProd.zetaParams (finS R t) B cμ, ZetaProd.norm_zetaParams_le cμ hcard hb, fun U₁ h₁ U₂ h₂ v₁ v₂ => ?_⟩
  rw [ZetaProd.eulerOff_zetaParams cμ hcard hb]
  exact hsum U₁ h₁ U₂ h₂ v₁ v₂

end GlobalTheory.LowRow

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteZetaIntegral_eulerProduct_of_partialL : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), FiniteZetaL R F → FiniteZetaC R F := by
  atlas_forward_decl GlobalTheory.LowRow.finiteZetaC_of_finiteZetaL
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRowAdel

theorem deltaNorm_all (D : D7) : DeltaNorm D := by
  intro i σ
  have h := GlobalTheory.T.fockForm_minorProduct_eq_prod_hookProducts D (Wc D i).rank (Vc D i).rank (pW D i) (qW D i) (aPlAt D i σ) (aMiAt D i σ)
    (fun ρ => (GlobalTheory.T.liftRows_antitone_signature_rank D i σ ρ).2.2.1.le)
    (fun ρ => by
      obtain ⟨-, -, hpq, hWV⟩ := GlobalTheory.T.liftRows_antitone_signature_rank D i σ ρ
      exact ⟨by omega, by omega⟩)
    (fun ρ => ⟨(GlobalTheory.T.liftRows_antitone_signature_rank D i σ ρ).1, (GlobalTheory.T.liftRows_antitone_signature_rank D i σ ρ).2.1⟩)
  simpa [deltaAtEmb] using h

theorem adelC_of_siegelWeil_of_doubling : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent →
    GlobalTheory.Published.DoublingMethod → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → StdV D → AdelC R F := by
  intro hCusp hWS _hSWc hDbl hUnr hBZ hFD D G _ _ Pl0 T A Ks _ _ _ R F hL hStd
  have hHM : GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts.HarmonicModule :=
    GlobalTheory.HarmModule.harmonicModule_of GlobalTheory.FockDecay.harmonicDecay GlobalTheory.CartanInt.coshIntegral
  have hLoc : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock := GlobalTheory.SingleBlock.localIntegralSingleBlock
  have hPM : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D := GlobalTheory.PlaceTensor.placeModels D
  exact GlobalTheory.T.adelicLift_scalar_of_innerProductFormula R F (GlobalTheory.T.adelicLift_mem_cuspForm_multiplicitySpace hCusp R F) (GlobalTheory.T.finiteDatum_sourceLevelCharacter_law hLoc R F hPM)
    (GlobalTheory.T.twistedThetaLift_innerProductFormula_of_hypotheses hCusp hWS (GlobalTheory.Published.siegelEisensteinContinuation_of_doublingMethod hDbl) R F hL)
    (GlobalTheory.T.fockVector_matrixCoefficient_formula hHM R F hPM) (deltaNorm_all D)
    (GlobalTheory.T.finiteZetaIntegral_eulerProduct_of_partialL R F (GlobalTheory.T.finiteZetaIntegral_thetaLift_eq_partialLValue hCusp hBZ hUnr R F)) (GlobalTheory.T.thetaLevelIndex_mul_schwartzNorm_formula hLoc R F hPM)
    (GlobalTheory.T.unitaryMassLowerBound_of_orthonormalLatticeFrames D hStd) (GlobalTheory.T.formalDegreeRealPlaceUpperBound_of_harishChandra hFD R F)

end GlobalTheory.LowRowAdel
end
