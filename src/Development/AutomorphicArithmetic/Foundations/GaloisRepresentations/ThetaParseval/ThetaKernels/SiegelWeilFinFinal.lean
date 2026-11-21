import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilStandard.SiegelWeilStd
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BaseKnownTheoremsS
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilStandard.SiegelWeilStdOfCt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilFinPre
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylIntegralCovariance.IntEqFour
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylIntegralCovariance.RpSmulLeft
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTbijChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitMeasND
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylIntegralCovariance.IntegralCovGen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitMeasTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKTunitMeas
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTwSt
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CtSplitOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.IndepDom
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilActCut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PhzLeftInvK
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.LocCompactNA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnipotentFirstMatrix
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PhzJLeftInv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.AbsConvK
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PsiTContPer
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PhzEqFlatK
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PadZeroMemNilradical
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PadMatrixLowerBlockZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SecUnfOfCLawK

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.TW.Twp
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
open PositivityTheory.SiegelWeilFormula.TBij.Adp
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def rp_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Y W : Matrix (Fin d.m) (Fin d.n) E) : F := Algebra.trace F E (Yᵀ * d.A.J * W.map σ).trace
def eq_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (q : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) : Matrix (Fin d.m) (Fin d.n) E := Matrix.of fun i j => if (i, j) = (q.1, q.2.1) then d.bs q.2.2 else 0
def rc_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Matrix (Fin d.m) (Fin d.n) E ≃ₗ[F] (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → F) where
  toFun Y k := d.bs.repr (Y k.1 k.2.1) k.2.2
  invFun a := Matrix.of fun i j => ∑ k, a (i, j, k) • d.bs k
  left_inv Y := by
    ext i j
    simp only [Matrix.of_apply]
    exact d.bs.sum_repr (Y i j)
  right_inv a := by
    funext ⟨i, j, k⟩
    simp only [Matrix.of_apply]
    exact congrFun (d.bs.repr_sum_self fun k' => a (i, j, k')) k
  map_add' Y Y' := by funext k; simp
  map_smul' c Y := by funext k; simp
theorem rp_add_left_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Y Y' W : Matrix (Fin d.m) (Fin d.n) E) : _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k d (Y + Y') W = _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k d Y W + _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k d Y' W := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k, Matrix.transpose_add, Matrix.add_mul, Matrix.trace_add, map_add]
theorem rp_smul_left_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (c : F) (Y W : Matrix (Fin d.m) (Fin d.n) E) : _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k d (c • Y) W = c * _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k d Y W := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k, Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul, map_smul, smul_eq_mul]
def Lm_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ) : (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → F) →ₗ[F] (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → F) where
  toFun a q := ((ε : ℤ) : F) * _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k d ((_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rc_k d).symm a) (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.eq_k d q)
  map_add' a b := by
    funext q
    simp only [map_add, _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_add_left_k, Pi.add_apply]
    ring
  map_smul' c a := by
    funext q
    simp only [map_smul, _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_smul_left_k, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
theorem ek_eq_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (q : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek d q = incM F (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.eq_k d q) := by
  obtain ⟨i0, j0, k0⟩ := q
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, incM, Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.eq_k, Matrix.of_apply]
  show _ = (1 : AF F) ⊗ₜ[F] _
  by_cases h : (i, j) = (i0, j0)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rw [if_pos rfl, Finset.sum_eq_single k0]
    · simp
    · intro b _ hb
      have : ((i, j, k0) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) ≠ (i, j, b) := fun e => hb (by simp at e; exact e.symm)
      simp [this]
    · simp
  · rw [if_neg h, TensorProduct.tmul_zero]
    refine Finset.sum_eq_zero fun k _ => ?_
    have : ((i0, j0, k0) : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) ≠ (i, j, k) := fun e => h (by simp at e; rw [e.1, e.2.1])
    simp [this]
theorem crd_eq_sum_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Z : Mx F E d.m d.n) : Z = ∑ q, d.crd Z q • incM F (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.eq_k d q) := by
  conv_lhs => rw [← _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd d Z, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_sum]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.ek_eq_k]
def ttL_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X : Mx F E d.m d.n) : Mx F E d.m d.n →ₗ[AF F] AF F where
  toFun Z := d.tt (d.gram X Z)
  map_add' Z Z' := by
    have e : (Z + Z').map (cA σ) = Z.map (cA σ) + Z'.map (cA σ) := Matrix.map_add _ (map_add _) _ _
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, e, Matrix.mul_add, Matrix.trace_add, map_add]
  map_smul' a Z := by
    have e : (a • Z).map (cA σ) = a • Z.map (cA σ) := Matrix.map_smul _ a (fun x => map_smul (cA σ) a x) _
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, e, Matrix.mul_smul, Matrix.trace_smul, map_smul, RingHom.id_apply]
theorem tt_gram_sum_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X : Mx F E d.m d.n) (c : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → AF F) (W : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → Mx F E d.m d.n) :
    d.tt (d.gram X (∑ q, c q • W q)) = ∑ q, c q * d.tt (d.gram X (W q)) := by
  have h := map_sum (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.ttL_k d X) (fun q => c q • W q) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h
theorem tt_gram_inc_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Y W : Matrix (Fin d.m) (Fin d.n) E) :
    d.tt (d.gram (incM F Y) (incM F W)) = algebraMap F (AF F) (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k d Y W) := by
  have e : d.gram (incM F Y) (incM F W) = incM F (Yᵀ * d.A.J * W.map σ) := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, PositivityTheory.SiegelWeilFormula.TBij.cA_incM, ← PositivityTheory.SiegelWeilFormula.TBij.incM_transpose, ← PositivityTheory.SiegelWeilFormula.TBij.incM_mul,
      ← PositivityTheory.SiegelWeilFormula.TBij.incM_mul]
  rw [e, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k]
  have h2 : (incM F (Yᵀ * d.A.J * W.map σ)).trace = (1 : AF F) ⊗ₜ[F] (Yᵀ * d.A.J * W.map σ).trace := by
    simp only [Matrix.trace, incM, Matrix.diag_apply, Matrix.map_apply, TensorProduct.tmul_sum]
    rfl
  rw [h2, trace_tmul', one_mul]
theorem pair_eq_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ) (Y : Matrix (Fin d.m) (Fin d.n) E) (Z : Mx F E d.m d.n) :
    ((ε : ℤ) : AF F) * d.tt (d.gram (incM F Y) Z) = ∑ q, d.crd Z q * algebraMap F (AF F) (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.Lm_k d ε (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rc_k d Y) q) := by
  conv_lhs => rw [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.crd_eq_sum_k d Z]
  rw [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.tt_gram_sum_k, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.tt_gram_inc_k]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.Lm_k, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.symm_apply_apply, map_mul, map_intCast]
  ring
theorem tr_single_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (M : Matrix (Fin d.n) (Fin d.m) E) (i : Fin d.m) (j : Fin d.n) (k : Fin 2) :
    (M * (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.eq_k d (i, j, k)).map σ).trace = M j i * σ (d.bs k) := by
  rw [Matrix.trace, Finset.sum_eq_single j]
  · rw [Matrix.diag_apply, Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.eq_k]
    · intro b _ hb; simp [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.eq_k, hb]
    · simp
  · intro b _ hb
    rw [Matrix.diag_apply, Matrix.mul_apply]
    exact Finset.sum_eq_zero fun c _ => by simp [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.eq_k, hb]
  · simp
theorem rp_eq_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Y : Matrix (Fin d.m) (Fin d.n) E) (i : Fin d.m) (j : Fin d.n) (k : Fin 2) :
    _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k d Y (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.eq_k d (i, j, k)) = Algebra.trace F E ((Yᵀ * d.A.J) j i * σ (d.bs k)) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k, _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.tr_single_k]
theorem rp_nondeg_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Y : Matrix (Fin d.m) (Fin d.n) E) (h : ∀ q, _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_k d Y (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.eq_k d q) = 0) : Y = 0 := by
  have hσ : Function.Surjective σ := (AlgHom.bijective σ).2
  have key : ∀ (i : Fin d.m) (j : Fin d.n), (Yᵀ * d.A.J) j i = 0 := by
    intro i j
    refine (traceForm_nondegenerate F E).1 _ fun z => ?_
    obtain ⟨e, rfl⟩ := hσ z
    rw [Algebra.traceForm_apply, ← d.bs.sum_repr e, map_sum, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [AlgHom.map_smul_of_tower, mul_smul_comm, map_smul, ← _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_eq_k, h, smul_zero]
  have hdet : IsUnit d.A.J.det := isUnit_iff_ne_zero.2 (_root_.PositivityTheory.SiegelWeilFormula.KWhit.meas_detA_k d)
  have h0 : Yᵀ * d.A.J = 0 := by ext j i; exact key i j
  have h1 : Yᵀ = 0 := by
    have := congrArg (· * d.A.J⁻¹) h0
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one, Matrix.zero_mul] at this
    exact this
  rw [← Matrix.transpose_transpose Y, h1, Matrix.transpose_zero]
theorem Lm_inj_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ) : Function.Injective (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.Lm_k d ε) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have hε : ((ε : ℤ) : F) ≠ 0 := by
    rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
  have hY : (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rc_k d).symm a = 0 := by
    refine _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rp_nondeg_k d _ fun q => ?_
    have := congrFun ha q
    simp only [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.Lm_k, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left hε
  simpa using congrArg (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rc_k d) hY
end PositivityTheory.SiegelWeilFormula.TW.Twp
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
set_option linter.style.haveILetI false
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.TW.Twp
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
open PositivityTheory.SiegelWeilFormula.TBij.Adp
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem ratM_iff_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X : Mx F E d.m d.n) :
    X ∈ d.ratM ↔ d.crd X ∈ GroundTheory.Automorphic.FourierWhittaker.vecLattice F (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) := by
  let c : Mx F E d.m d.n →+ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → AF F) :=
    { toFun := d.crd, map_zero' := by funext k; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd], map_add' := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_add d }
  constructor
  · intro hX
    have hle : d.ratM ≤ (GroundTheory.Automorphic.FourierWhittaker.vecLattice F (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d)).comap c := by
      refine (AddSubgroup.closure_le _).mpr ?_
      rintro _ ⟨M, rfl⟩
      refine ⟨fun k => d.bs.repr (M k.1 k.2.1) k.2.2, ?_⟩
      funext k
      exact (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_incM d M k).symm
    exact hle hX
  · rintro ⟨ξ, hξ⟩
    let M : Matrix (Fin d.m) (Fin d.n) E := Matrix.of fun i j => ∑ k, ξ (i, j, k) • d.bs k
    have e1 : d.crd (incM F M) = d.crd X := by
      funext k
      rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_incM d _ k]
      have h2 := congrFun hξ k
      simp only [AddMonoidHom.compLeft, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply] at h2
      rw [← h2]
      show _ = algebraMap F (AF F) (ξ k)
      congr 1
      exact congrFun (d.bs.repr_sum_self fun k' => ξ (k.1, k.2.1, k')) k.2.2
    have e2 : incM F M = X := by
      rw [← _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd d (incM F _), e1, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd]
    rw [← e2]
    exact AddSubgroup.subset_closure ⟨_, rfl⟩
theorem integral_cov_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ν : Measure (Mx F E d.m d.n)) (hν : d.IsCov ν) (h : Mx F E d.m d.n → ℂ) :
    ∫ Z, h Z ∂ν = ∫ c, h (d.cmb c) ∂(GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F (ι := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d)) := by
  obtain ⟨hT, hLC, hSC, hB, hC⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.meas_mx_top'_k d
  haveI := hT; haveI := hLC; haveI := hSC; haveI := hB; haveI := hC
  obtain ⟨hH, 𝓕, h𝓕, h1⟩ := hν
  haveI := hH
  exact integral_cov_gen (hBor := hB) (hνH := hH) d.ratM (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cEquiv_k d (Equiv.refl (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d))) (fun X => _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.ratM_iff_k d X) ν 𝓕 h𝓕 h1 h
end PositivityTheory.SiegelWeilFormula.TW.Twp
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.TW.Twp
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
open PositivityTheory.SiegelWeilFormula.TBij.Adp
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem int_eq_four_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ν : Measure (Mx F E d.m d.n)) (hν : d.IsCov ν) (ε : ℤˣ) (f : Mx F E d.m d.n → ℂ)
    (Y : Matrix (Fin d.m) (Fin d.n) E) :
    ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram (incM F Y) Z)) * f Z ∂ν =
      GroundTheory.Automorphic.GJMatrix.adelicFourierPi F (fun c => f (d.cmb c))
        (fun q => algebraMap F (AF F) (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.Lm_k d ε (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rc_k d Y) q)) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.integral_cov_k d ν hν, GroundTheory.Automorphic.GJMatrix.adelicFourierPi]
  congr 1
  funext c
  rw [_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.pair_eq_k d ε Y (d.cmb c), _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_cmb, GlobalTheory.AdelicSvN.Weyl.isStd_eq d.ok.good.std, mul_comm]
theorem poisson_k : _root_.PositivityTheory.SiegelWeilFormula.TW.Poisson_k := by
  intro F E _ _ _ _ _ σ d ν hν ε f hf
  have hg : (fun c => f (d.cmb c)) ∈ schA F (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) := Submodule.mem_comap.1 hf
  have hθ := GlobalTheory.TowU.FourWeyl.theta_four hg
  refine (tsum_congr fun X => _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.int_eq_four_k d ν hν ε f X).trans ?_
  refine ((_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rc_k d).toEquiv.tsum_eq (fun a => GroundTheory.Automorphic.GJMatrix.adelicFourierPi F (fun c => f (d.cmb c))
      (fun q => algebraMap F (AF F) (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.Lm_k d ε a q)))).trans ?_
  refine ((LinearEquiv.ofInjectiveEndo (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.Lm_k d ε) (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.Lm_inj_k d ε)).toEquiv.tsum_eq
      (fun a => GroundTheory.Automorphic.GJMatrix.adelicFourierPi F (fun c => f (d.cmb c)) (fun q => algebraMap F (AF F) (a q)))).trans ?_
  refine hθ.trans ?_
  show ∑' ξ : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → F, f (d.cmb fun q => algebraMap F (AF F) (ξ q)) = _
  have e : ∀ X : Matrix (Fin d.m) (Fin d.n) E, f (incM F X) = f (d.cmb fun q => algebraMap F (AF F) (_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rc_k d X q)) := by
    intro X
    congr 1
    rw [← _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd d (incM F X)]
    congr 1
    funext q
    rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_incM]
    rfl
  simp_rw [e]
  exact ((_root_.PositivityTheory.SiegelWeilFormula.TW.Twp.rc_k d).toEquiv.tsum_eq (fun a => f (d.cmb fun q => algebraMap F (AF F) (a q)))).symm
end PositivityTheory.SiegelWeilFormula.TW.Twp
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.Fin
theorem siegelWeilStd_of_ct_k (hCT : _root_.PositivityTheory.SiegelWeilFormula.CTSplit_k) : _root_.GlobalTheory.ThK.Dbl.SiegelWeilStd_k := _root_.PositivityTheory.SiegelWeilFormula.Fin.siegelWeilStd_pre_k _root_.PositivityTheory.SiegelWeilFormula.TW.Twp.poisson_k hCT
end PositivityTheory.SiegelWeilFormula.Fin
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem isClosed_nA_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : IsClosed (nA σ d.Y d.b : Set (Matrix (Fin d.n) (Fin d.n) (AE F E))) := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have hc : Continuous (cA σ : AE F E → AE F E) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have e : (nA σ d.Y d.b : Set (Matrix (Fin d.n) (Fin d.n) (AE F E))) =
      {β | βᵀ = -((((ε : ℤ) : AE F E)) • β.map (cA σ))} := Set.ext fun β => kunf.mem_nA_iff hε β
  rw [e]
  exact isClosed_eq continuous_id.matrix_transpose (((continuous_id.matrix_map hc).const_smul (((ε : ℤ) : AE F E))).neg)
instance locCompact_nA_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : LocallyCompactSpace (nA σ d.Y d.b) :=
  haveI : LocallyCompactSpace (Matrix (Fin d.n) (Fin d.n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin d.n → Fin d.n → AE F E))
  (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.isClosed_nA_k d).isClosedEmbedding_subtypeVal.locallyCompactSpace
theorem coef_periodic_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb : nA σ d.Y d.b → d.G} (hN : IsNMap d.b nb) (φ : d.G → ℂ)
    (hφ : ∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) (T : nF σ d.Y d.b) (g : d.G) (β₀ : nF σ d.Y d.b)
    (β : nA σ d.Y d.b) :
    φ (nb (β₀ +ᵥ β) * g) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * (β₀ +ᵥ β).1)))) =
      φ (nb β * g) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) := by
  have e1 : (β₀ +ᵥ β : nA σ d.Y d.b) = β₀.1 + β := rfl
  have e2 : ((β₀.1 + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = β₀.1.1 + β.1 := rfl
  rw [e1, kunf.nb_add hN, mul_assoc, hφ _ (kunf.nb_rat hN β₀.2), e2, Matrix.mul_add, Matrix.trace_add, map_add, neg_add,
    AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, kunf.psi_rat d.ok.good.std T β₀, inv_one, one_mul]
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
theorem cj_mp_k {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (h : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
    {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) {v : Fin L.n → AE F E} (hv : v ∈ L.ratV) :
    MeasurePreserving (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 v) lam lam := by
  have := h.2.1
  refine ⟨(_root_.PositivityTheory.SiegelWeilFormula.Act.C1.continuous_cj_k hU h.1 v).measurable, ?_⟩
  have hl := latHaar (nA σ d.Y d.b) lam (nF σ d.Y d.b) (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cjE_k hU h.1 v) (fun x => ⟨fun hx => ?_, fun hx => _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_rat_k hU h.1 hv hx⟩)
    𝓖 h.2.2.1 (by rw [h.2.2.2]; exact one_ne_zero) (by rw [h.2.2.2]; exact ENNReal.one_ne_top)
  · exact hl
  · have := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_rat_k hU h.1 (neg_mem hv) hx
    rwa [show _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-v) (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cjE_k hU h.1 v x) = x from _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k hU h.1 v x] at this
theorem fc_conj_k {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (h : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
    {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) (φ : d.G → ℂ) (hφ : ∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g)
    {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T') {u : Fin L.n → AE F E} (hu : u ∈ L.ratV) (g : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * g) = fc d.B.ψ d.b nb lam 𝓖 φ T g := by
  have := h.2.1
  have : VAddInvariantMeasure (nF σ d.Y d.b) (nA σ d.Y d.b) lam := ⟨fun c s _ => measure_preimage_add lam c.1 s⟩
  let H : nA σ d.Y d.b → ℂ := fun β =>
    φ (nb β * g) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
  have e1 : ∀ β, φ (nb β * (uM u * g)) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) =
      H (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u β) := by
    intro β
    have e : nb β * (uM u * g) = uM u * (nb (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u β) * g) := by rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.nb_cj_k hU h.1 u β]; group
    simp only [H]
    rw [e, hφ _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_rat_k hU hu), _root_.PositivityTheory.SiegelWeilFormula.Act.C1.trace_cj_k hU h.1 hT]
  have hme : MeasurableEmbedding (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u) := (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cjE_k hU h.1 u).toHomeomorph.measurableEmbedding
  have himg : (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u) '' 𝓖 = (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u)) ⁻¹' 𝓖 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u) (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u x) ∈ 𝓖
      rwa [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k]
    · intro hy
      refine ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u) y, hy, ?_⟩
      simpa using _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k hU h.1 (-u) y
  have hfd : IsAddFundamentalDomain (nF σ d.Y d.b) ((_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u)) ⁻¹' 𝓖) lam := by
    refine h.2.2.1.preimage_of_equiv (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_mp_k h hU (neg_mem hu)).quasiMeasurePreserving
      (e := fun γ => ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u γ.1, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_rat_k hU h.1 hu γ.2⟩) ⟨fun γ γ' hγ => ?_, fun γ => ?_⟩ fun γ x => ?_
    · have := congrArg (fun y : nF σ d.Y d.b => _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u) y.1) hγ
      simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k] at this
      exact Subtype.ext this
    · refine ⟨⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u) γ.1, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_rat_k hU h.1 (neg_mem hu) γ.2⟩, Subtype.ext ?_⟩
      simpa using _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k hU h.1 (-u) γ.1
    · show _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u) ((_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u γ.1) + x) = γ.1 + _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u) x
      rw [map_add, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k]
  unfold fc
  simp_rw [e1]
  rw [← (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_mp_k h hU hu).setIntegral_image_emb hme H 𝓖, himg,
    hfd.setIntegral_eq h.2.2.1 (fun β₀ β => _root_.PositivityTheory.SiegelWeilFormula.Act.C1.coef_periodic_k d h.1 φ hφ T g β₀ β)]
end PositivityTheory.SiegelWeilFormula.Act.C1
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem range_or_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u : Fin d.n ⊕ Fin d.n) :
    (∃ u', Sum.map L.em L.em u' = u) ∨ u ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n)) := by
  rcases u with a | a <;>
  · by_cases ha : a = L.i₀
    · right; simp [ha]
    · obtain ⟨a', rfl⟩ := (L.rng a).1 ha
      left; first | exact ⟨Sum.inl a', rfl⟩ | exact ⟨Sum.inr a', rfl⟩
theorem j_par_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {p : G2 σ L.Y} (hp : p ∈ par2 σ L.Y) : L.j p ∈ par2 σ d.Y := by
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame]
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block L.sd.ok.frame] at hp
  ext a c
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply]
  rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C1.range_or_k L (Sum.inr a) with ⟨u', hu'⟩ | hu
  · rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C1.range_or_k L (Sum.inl c) with ⟨v', hv'⟩ | hv
    · rcases u' with a' | a'
      · simp at hu'
      rcases v' with c' | c'
      · have h1 := congrFun (congrFun (L.j_in p) (Sum.inr a')) (Sum.inl c')
        simp only [Matrix.submatrix_apply, Sum.map_inr, Sum.map_inl] at h1
        simp only [Sum.map_inr, Sum.inr.injEq] at hu'
        simp only [Sum.map_inl, Sum.inl.injEq] at hv'
        rw [← hu', ← hv', h1]
        exact congrFun (congrFun hp a') c'
      · simp at hv'
    · rw [(L.j_out p _ hv (Sum.inr a)).2]
      simp
  · rw [(L.j_out p _ hu (Sum.inl c)).1]
    simp
theorem j_rat_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {p : G2 σ L.Y} (hp : p ∈ rat2 σ L.Y) : L.j p ∈ rat2 σ d.Y := by
  obtain ⟨g, hg⟩ := hp
  have hm : mat2 p = incM F g.1 := (congrArg Units.val hg).symm
  have hL : inFrame L.b p = incM F ((L.b⁻¹).1 * g.1 * L.b.1) := by
    rw [kunf.incM_mul', kunf.incM_mul', ← hm]; rfl
  let M' := (L.b⁻¹).1 * g.1 * L.b.1
  let M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E := fun u v =>
    if hu : ∃ u', Sum.map L.em L.em u' = u then
      if hv : ∃ v', Sum.map L.em L.em v' = v then M' hu.choose hv.choose else (1 : Matrix _ _ E) u v
    else (1 : Matrix _ _ E) u v
  refine kunf.rat_of_inFrame (b := d.b) (M := M) ?_
  ext u v
  show inFrame d.b (L.j p) u v = inclR (F := F) (AF F) (M u v)
  dsimp only [M]
  by_cases hu : ∃ u', Sum.map L.em L.em u' = u
  · by_cases hv : ∃ v', Sum.map L.em L.em v' = v
    · rw [dif_pos hu, dif_pos hv]
      have h1 := congrFun (congrFun (L.j_in p) hu.choose) hv.choose
      simp only [Matrix.submatrix_apply, hu.choose_spec, hv.choose_spec] at h1
      rw [h1, hL]
      rfl
    · rw [dif_pos hu, dif_neg hv]
      have hv' := (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.range_or_k L v).resolve_left hv
      rw [(L.j_out p _ hv' u).2]
      simp [Matrix.one_apply, apply_ite]
  · rw [dif_neg hu]
    have hu' := (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.range_or_k L u).resolve_left hu
    rw [(L.j_out p _ hu' v).1]
    simp [Matrix.one_apply, apply_ite]
theorem phz_j_leftInv_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) (x : d.G) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (par2 σ L.Y ⊓ rat2 σ L.Y)
      (fun g : G2 σ L.Y => ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s₁) * f (L.j g * x)) := by
  intro p hp g
  show _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (L.j (p * g) * x) = _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (L.j g * x)
  rw [map_mul, mul_assoc]
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.C1.phz_leftInv_k d hf z (L.j p) ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C1.j_par_k L hp.1, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.j_rat_k L hp.2⟩ _
end PositivityTheory.SiegelWeilFormula.Act.C1
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act
theorem indepDom_k : _root_.PositivityTheory.SiegelWeilFormula.Act.IndepDom_k := by
  intro F E _ _ _ _ _ σ d L s₁ f hf z
  have hE := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.eis_leftInv_k d hf z
  refine ⟨fun nb lam 𝓖 𝓖₀ h h₀ uM ν 𝓤 𝓤₀ hU hU₀ T T' hT x => ?_, fun nb' lam' 𝓖' 𝓖'₀ h' h'₀ T' x => ?_⟩
  · have step1 : ∀ g, fc d.B.ψ d.b nb lam 𝓖 (d.eis f s₁ z) T g = fc d.B.ψ d.b nb lam 𝓖₀ (d.eis f s₁ z) T g :=
      fun g => _root_.PositivityTheory.SiegelWeilFormula.Act.C1.fc_dom_k d h h₀ _ hE T g
    simp_rw [step1]
    have := hU.2.1
    have : VAddInvariantMeasure L.ratV (Fin L.n → AE F E) ν := ⟨fun c s _ => measure_preimage_add ν c.1 s⟩
    have : Countable L.ratV := by
      have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
      refine Function.Surjective.countable (f := fun v : Fin L.n → E =>
        (⟨GlobalTheory.ThK.incV F v, AddSubgroup.subset_closure ⟨v, rfl⟩⟩ : L.ratV)) fun u => ?_
      obtain ⟨v, hv⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.ratV_inc_k u.2
      exact ⟨v, Subtype.ext hv.symm⟩
    refine hU.2.2.1.setIntegral_eq hU₀.2.2.1 fun u₀ u => ?_
    show fc d.B.ψ d.b nb lam 𝓖₀ (d.eis f s₁ z) T (uM (u₀.1 + u) * x) = fc d.B.ψ d.b nb lam 𝓖₀ (d.eis f s₁ z) T (uM u * x)
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_add_k hU, mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.fc_conj_k h₀ hU _ hE hT u₀.2]
  · exact _root_.PositivityTheory.SiegelWeilFormula.Act.C1.fc_dom_k L.sd h' h'₀ _ (GlobalTheory.Eis.leftInv_cosetSum (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.phz_j_leftInv_k L hf z x)) T' 1
end PositivityTheory.SiegelWeilFormula.Act
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def padZeroAlt (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  fun i k => if h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k then β h.1.choose h.2.choose else 0
theorem pad_zero_embedding (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (a c : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β (L.em a) (L.em c) = β a c := by
  have h : (∃ a', L.em a' = L.em a) ∧ ∃ c', L.em c' = L.em c := ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt, dif_pos h]
  rw [L.inj h.1.choose_spec, L.inj h.2.choose_spec]
theorem pad_zero_outside (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (i k : Fin d.n)
    (h : ¬ ((∃ a, L.em a = i) ∧ ∃ c, L.em c = k)) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β i k = 0 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt, dif_neg h]
theorem pad_zero_cases (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (P : AE F E → AE F E → Prop) (h0 : P 0 0)
    (h1 : ∀ a c, P (β a c) (β c a)) (i k : Fin d.n) : P (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β i k) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β k i) := by
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_embedding, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_embedding]
    exact h1 a c
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_outside L β i k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_outside L β k i (fun h' => h ⟨h'.2, h'.1⟩)]
    exact h0
theorem eps_common_k : ∃ ε : ℤˣ, d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 ∧
    L.b.1ᵀ * dbl L.Y.J * L.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee : ε = ε' := _root_.PositivityTheory.SiegelWeilFormula.Afc.eps_eq_k L hε hε'
  subst hee
  exact ⟨ε, hε, hε'⟩
theorem pad_zero_mem_unipotent (β : nA σ L.Y L.b) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β.1 ∈ nA σ d.Y d.b := by
  obtain ⟨ε, hε, hε'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.eps_common_k L
  rw [kunf.mem_nA_iff hε]
  have hβ := (kunf.mem_nA_iff hε' β.1).1 β.2
  ext i k
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply]
  refine _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_cases L β.1 (fun u v => v = -((((ε : ℤ) : AE F E)) • cA σ u)) (by simp) (fun a c => ?_) i k
  have := congrFun (congrFun hβ a) c
  simpa only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply] using this
def padN_k : nA σ L.Y L.b →+ nA σ d.Y d.b where
  toFun β := ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β.1, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_mem_unipotent L β⟩
  map_zero' := by
    apply Subtype.ext
    ext i k
    refine _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_cases L (0 : nA σ L.Y L.b).1 (fun u _ => u = (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) i k) rfl
      (fun a c => rfl) i k
  map_add' β β' := by
    apply Subtype.ext
    ext i k
    by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
    · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
      simp only [AddSubgroup.coe_add, Matrix.add_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_embedding]
    · simp only [AddSubgroup.coe_add, Matrix.add_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_outside L _ i k h, add_zero]
theorem prj_padN_k (β : nA σ L.Y L.b) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padN_k L β) = β := by
  apply Subtype.ext
  ext a c
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_val_k, Matrix.submatrix_apply]
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_embedding L β.1 a c
theorem continuous_padN_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padN_k L) := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun i => continuous_pi fun k => ?_
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_embedding]
    exact (continuous_apply c).comp ((continuous_apply a).comp continuous_subtype_val)
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_zero_outside L _ i k h]
    exact continuous_const
theorem prj_nF_k {β : nA σ d.Y d.b} (h : β ∈ nF σ d.Y d.b) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β ∈ nF σ L.Y L.b := by
  obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 h
  refine kunf.mem_nF_iff.2 ⟨T.submatrix L.em L.em, ?_⟩
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_val_k, hT]
  rfl
theorem padN_nF_k {β : nA σ L.Y L.b} (h : β ∈ nF σ L.Y L.b) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padN_k L β ∈ nF σ d.Y d.b := by
  obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 h
  refine kunf.mem_nF_iff.2 ⟨Matrix.of fun i k => if h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k then
    T h.1.choose h.2.choose else 0, ?_⟩
  ext i k
  show _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt L β.1 i k = _
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt, dif_pos h, hT]
    simp only [incM, Matrix.map_apply, Matrix.of_apply, dif_pos h]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padZeroAlt, dif_neg h]
    simp only [incM, Matrix.map_apply, Matrix.of_apply, dif_neg h, map_zero]
theorem fiber_k {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {nb' : nA σ L.Y L.b → G2 σ L.Y} {lam' : Measure (nA σ L.Y L.b)}
    {𝓖' : Set (nA σ L.Y L.b)} (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖')
    (G : nA σ L.Y L.b → ℂ) (hG : Continuous G) (hper : ∀ β₀ ∈ nF σ L.Y L.b, ∀ β', G (β₀ + β') = G β') :
    ∫ β in 𝓖, G (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β) ∂lam = ∫ β' in 𝓖', G β' ∂lam' := by
  obtain ⟨ε, hε, hε'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.eps_common_k L
  obtain ⟨h1, h2⟩ := nA_inst d.n d.Y d.b ε hε
  obtain ⟨h3, h4⟩ := nA_inst L.n L.Y L.b ε hε'
  exact GlobalTheory.T.haar_measure_split_exact_sequence (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padN_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.continuous_prj_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.continuous_padN_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_padN_k L)
    (nF σ d.Y d.b) (nF σ L.Y L.b) (countable_nF _ _ _) (countable_nF _ _ _) (fun γ hγ => _root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_nF_k L hγ)
    (fun γ hγ => _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padN_nF_k L hγ) lam lam' hc.2.1 hc'.2.1 𝓖 𝓖' hc.2.2.1 hc.2.2.2 hc'.2.2.1 hc'.2.2.2 G hG
    (fun γ hγ x => hper γ hγ x)
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
instance countableCs_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Countable (_root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) := by
  have : Countable (rat2 σ d.Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ d.Y
  infer_instance
theorem cont_E_k {s₁ z : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f)
    (hmaj : ∀ C : Set d.G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets (par2 σ d.Y) (rat2 σ d.Y) → ℝ, Summable u ∧ ∀ g ∈ C, ∀ q,
      ‖GlobalTheory.Eis.term (par2 σ d.Y) (rat2 σ d.Y) (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x) g q‖ ≤ u q)
    {nb' : nA σ L.Y L.b → G2 σ L.Y} (hnb' : IsNMap L.b nb') (x : d.G) :
    Continuous fun β' : nA σ L.Y L.b => ∑' q' : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' * nb' β') * x) := by
  obtain ⟨e, he⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.cos_bij_k L
  have hphz : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.phz_eq_flat_k]
    exact continuous_flat hf.cont (_root_.PositivityTheory.SiegelWeilFormula.kunf.continuous_a_k d) (_root_.PositivityTheory.SiegelWeilFormula.kunf.a_pos_k d) z
  have hg : Continuous fun β' : nA σ L.Y L.b => L.j (nb' β') * x :=
    (L.cont.comp (kunf.continuous_nb hnb')).mul continuous_const
  have hterm : ∀ q' β', _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' * nb' β') * x) =
      _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e q').1 * (L.j (nb' β') * x)) := by
    intro q' β'
    obtain ⟨p₀, hp₀, hr₀, hrep⟩ := he q'
    rw [hrep, mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.phz_rat_k hf z hp₀ hr₀, map_mul, mul_assoc]
  refine continuous_iff_continuousAt.2 fun β₀ => ?_
  obtain ⟨C, hCc, hC⟩ := exists_compact_mem_nhds (L.j (nb' β₀) * x)
  obtain ⟨u, hu, hbd⟩ := hmaj C hCc
  have hN : (fun β' : nA σ L.Y L.b => L.j (nb' β') * x) ⁻¹' C ∈ 𝓝 β₀ := hg.continuousAt.preimage_mem_nhds hC
  refine (continuousOn_tsum (u := u ∘ Subtype.val ∘ e) (fun q' => ?_) (hu.comp_injective
    (Subtype.val_injective.comp e.injective)) (fun q' β' hβ' => ?_)).continuousAt hN
  · exact (hphz.comp ((L.cont.comp (continuous_const.mul (kunf.continuous_nb hnb'))).mul continuous_const)).continuousOn
  · rw [hterm]
    exact hbd _ hβ' _
theorem per_E_k {s₁ z : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) {nb' : nA σ L.Y L.b → G2 σ L.Y} (hnb' : IsNMap L.b nb')
    (x : d.G) (β₀ : nA σ L.Y L.b) (h₀ : β₀ ∈ nF σ L.Y L.b) (β' : nA σ L.Y L.b) :
    ∑' q' : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' * nb' (β₀ + β')) * x) =
      ∑' q' : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' * nb' β') * x) := by
  have hinv : GlobalTheory.AutomorphicL2Unitary.LeftInv (par2 σ L.Y ⊓ rat2 σ L.Y) (fun y : G2 σ L.Y => _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (L.j y * x)) := by
    intro γ hγ g
    simp only [map_mul, mul_assoc]
    exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.phz_rat_k hf z (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_par_k L (Subgroup.mem_inf.1 hγ).1) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L (Subgroup.mem_inf.1 hγ).2) _
  have h := GlobalTheory.Eis.leftInv_cosetSum hinv (nb' β₀) (kunf.nb_rat hnb' h₀) (nb' β')
  simp only [GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term] at h
  rw [kunf.nb_add hnb']
  exact h
theorem psiT_cont_per_k (T' : nF σ L.Y L.b) :
    Continuous (fun β' : nA σ L.Y L.b => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * β'.1))))) ∧
    ∀ β₀ ∈ nF σ L.Y L.b, ∀ β' : nA σ L.Y L.b,
      d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * (β₀ + β').1)))) =
        d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * β'.1)))) := by
  have hstd := d.ok.good.std
  refine ⟨?_, fun β₀ h₀ β' => ?_⟩
  · have : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
    have htr : Continuous (Algebra.trace (AF F) (AE F E)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF F) (AE F E))
    exact hstd.1.comp (htr.comp ((continuous_const.matrix_mul continuous_subtype_val).matrix_trace)).neg
  · have h1 := kunf.psi_rat hstd T' ⟨β₀, h₀⟩
    rw [AddSubgroup.coe_add, Matrix.mul_add, Matrix.trace_add, map_add, neg_add, AddChar.map_add_eq_mul,
      AddChar.map_neg_eq_inv, h1, inv_one, one_mul]
theorem firstEq_of_k : _root_.PositivityTheory.SiegelWeilFormula.Act.AbsConv_k → _root_.PositivityTheory.SiegelWeilFormula.Act.FirstEq_k := by
  intro hA F E _ _ _ _ _ σ d L s₁ f hf he
  obtain ⟨t₁, ht₁⟩ := hA F E σ d L s₁ f hf he
  obtain ⟨U, p, Ê, t₂, -, -, -, -, -, -, -, hmaj⟩ := he 0
  refine ⟨max t₁ t₂, fun z hz nb lam 𝓖 hc hGc nb' lam' 𝓖' hc' hGc' uM ν 𝓤 hU hUc T T' hT x => ?_⟩
  have hz₁ : t₁ < z.re := lt_of_le_of_lt (le_max_left _ _) hz
  have hz₂ : t₂ < z.re := lt_of_le_of_lt (le_max_right _ _) hz
  obtain ⟨hint, hsum⟩ := ht₁ z hz₁ nb lam 𝓖 hc hGc uM ν 𝓤 hU hUc T x
  obtain ⟨e, he'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.cos_bij_k L
  haveI : IsFiniteMeasure (lam.restrict 𝓖) := ⟨by rw [Measure.restrict_apply_univ, hc.2.2.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (ν.restrict 𝓤) := ⟨by rw [Measure.restrict_apply_univ, hU.2.2.2]; exact ENNReal.one_lt_top⟩
  set ψT : nA σ L.Y L.b → ℂ := fun β' => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * β'.1))))
    with hψT
  set H : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd → nA σ L.Y L.b → ℂ := fun q' β' => _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' * nb' β') * x) * ψT β' with hH
  have hpt : ∀ q' (pr : (Fin L.n → AE F E) × nA σ d.Y d.b),
      _root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e q').1) x pr = H q' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L pr.2) := by
    rintro q' ⟨u, β⟩
    obtain ⟨p₀, hp₀, hr₀, hrep⟩ := he' q'
    obtain ⟨p₁, t, hp₁, hdet, hid⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.key_id_k L hc.1 hc'.1 hU (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q') β u x
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k, hH, hψT]
    rw [hrep, mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.phz_rat_k hf z hp₀ hr₀, hid, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.phz_par_k hf z hp₁ hdet, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.tr_sub_k L hT β]
  have hν1 : (ν.restrict 𝓤).real Set.univ = 1 := by
    simp [Measure.real, hU.2.2.2]
  have hkq : ∀ q', _root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e q').1) x = fun pr => H q' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L pr.2) := fun q' => funext (hpt q')
  have htm : ∀ q', _root_.PositivityTheory.SiegelWeilFormula.Act.tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤 (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e q').1) x = ∫ β in 𝓖, H q' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β) ∂lam := by
    intro q'
    have h1 : ∀ u, fc d.B.ψ d.b nb lam 𝓖 (fun g => _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e q').1 * g)) T (uM u * x) =
        ∫ β in 𝓖, H q' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β) ∂lam := by
      intro u
      refine integral_congr_ae (Filter.Eventually.of_forall fun β => ?_)
      exact hpt q' (u, β)
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.tm_k, h1]
    rw [setIntegral_const]
    simp [Measure.real, hU.2.2.2]
  have hint' : ∀ q', Integrable (fun β => H q' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) (lam.restrict 𝓖) := by
    intro q'
    have h1 := (hint (e q').1).integral_prod_right
    rw [hkq] at h1
    simpa only [integral_const, hν1, one_smul] using h1
  have hnorm : ∀ q', ∫ pr, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e q').1) x pr‖ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) =
      ∫ β in 𝓖, ‖H q' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)‖ ∂lam := by
    intro q'
    have hI := (hint (e q').1).norm
    rw [integral_prod _ hI]
    simp only [hkq, integral_const, hν1, one_smul]
  have hsum' : Summable fun q' => ∫ β in 𝓖, ‖H q' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)‖ ∂lam := by
    have h2 := hsum.comp_injective (Subtype.val_injective.comp e.injective)
    exact h2.congr fun q' => hnorm q'
  set G : nA σ L.Y L.b → ℂ := fun β' => (∑' q' : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q' * nb' β') * x)) * ψT β' with hG
  have hHG : ∀ β', ∑' q', H q' β' = G β' := fun β' => tsum_mul_right
  have hGc : Continuous G := by
    refine (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.cont_E_k L hf (hmaj z hz₂).1 hc'.1 x).mul (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.psiT_cont_per_k L T').1
  have hGp : ∀ β₀ ∈ nF σ L.Y L.b, ∀ β', G (β₀ + β') = G β' := by
    intro β₀ h₀ β'
    simp only [hG, hψT]
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.per_E_k L hf hc'.1 x β₀ h₀ β', (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.psiT_cont_per_k L T').2 β₀ h₀ β']
  calc ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, _root_.PositivityTheory.SiegelWeilFormula.Act.tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤 (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1) x
      = ∑' q', _root_.PositivityTheory.SiegelWeilFormula.Act.tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤 (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e q').1) x :=
        (e.tsum_eq (fun q => _root_.PositivityTheory.SiegelWeilFormula.Act.tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤 (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1) x)).symm
    _ = ∑' q', ∫ β in 𝓖, H q' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β) ∂lam := tsum_congr htm
    _ = ∫ β in 𝓖, ∑' q', H q' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β) ∂lam := by
        haveI : Countable (_root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd) := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.countableCs_k L.sd
        exact integral_tsum_of_summable_integral_norm hint' hsum'
    _ = ∫ β in 𝓖, G (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β) ∂lam := by simp only [hHG]
    _ = ∫ β' in 𝓖', G β' ∂lam' := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.fiber_k L hc hc' G hGc hGp
    _ = _root_.PositivityTheory.SiegelWeilFormula.Act.first_k L f s₁ z nb' lam' 𝓖' T' x := by
        simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.first_k, fc, GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term, mul_one, hG, hψT]
        rfl
end PositivityTheory.SiegelWeilFormula.Act.C4
namespace PositivityTheory.SiegelWeilFormula.Act
theorem firstEq_k : _root_.PositivityTheory.SiegelWeilFormula.Act.FirstEq_k := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.firstEq_of_k _root_.PositivityTheory.SiegelWeilFormula.Act.absConv_k
end PositivityTheory.SiegelWeilFormula.Act
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.SiegelWeilFormula.Act
theorem ctSplit_of_k : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.CoefEx_k → _root_.PositivityTheory.SiegelWeilFormula.CTSplit_k := fun _ _ =>
  _root_.PositivityTheory.SiegelWeilFormula.Act.ctSplit_of_parts_k _root_.PositivityTheory.SiegelWeilFormula.Act.indepDom_k _root_.PositivityTheory.SiegelWeilFormula.Act.cptDom_k _root_.PositivityTheory.SiegelWeilFormula.Act.absConv_k _root_.PositivityTheory.SiegelWeilFormula.Act.firstEq_k (_root_.PositivityTheory.SiegelWeilFormula.Act.secLaw_of_k (_root_.PositivityTheory.SiegelWeilFormula.Act.secUnf_of_k _root_.PositivityTheory.SiegelWeilFormula.Act.absConv_k))
end PositivityTheory.SiegelWeilFormula.Act
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.Fin
theorem siegelWeilStd_k : _root_.GlobalTheory.ThK.Dbl.SiegelWeilStd_k := _root_.PositivityTheory.SiegelWeilFormula.Fin.siegelWeilStd_of_ct_k (_root_.PositivityTheory.SiegelWeilFormula.Act.ctSplit_of_k _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds _root_.PositivityTheory.SiegelWeilFormula.kfour.coefEx_k)
end PositivityTheory.SiegelWeilFormula.Fin
end
end
