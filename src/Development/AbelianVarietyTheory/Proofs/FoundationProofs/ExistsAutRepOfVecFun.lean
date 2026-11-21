import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAutFormUCoef
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeightModuleFiniteContinuous
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphicRepDualPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenericDetPowMulHw
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBilinearFischerPairingMatrixEntryPolynomia
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensor
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualWeylModuleTensorCoefficientUniversal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqBotOrTopOfTensor

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_rep_dual_pairing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ), (∀ u v, star (B u v) = B v u) → (∀ v, 0 ≤ (B v v).re) → (∀ v, B v v = 0 → v = 0) → (∀ g u v, B (autRep E n g u) (autRep E n g v) = B u v) → ∀ (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S), Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ f : S →ₗ[ℂ] (UA E n → ℂ), f ≠ 0 → (∀ v, IsAutFormU (f v)) → (∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)) → ∃ π, IsAutRepU π ∧ ∃ f' : S →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ v, f' v ∈ π) ∧ (∀ (x : infU E n) v, f' (ρ x v) = RU E n x (f' v)) ∧ ∀ (κ : Type) (R : Finset κ) (s : κ → UA E n) (c : ℂ), (∀ i ∈ R, s i ∈ finU E n) → (∀ v, ∑ i ∈ R, RU E n (s i) (f v) = c • f v) → ∀ v, ∑ i ∈ R, RU E n (s i) (f' v) = c • f' v := by
  first | exact @GlobalTheory.FrameAut.VecProj.exists_autRep_projection | exact GlobalTheory.FrameAut.VecProj.exists_autRep_projection | (intros; apply GlobalTheory.FrameAut.VecProj.exists_autRep_projection <;> assumption)
end

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

noncomputable section

namespace GlobalTheory.Branching

def lastNat {n : ℕ} (ν : Fin n → ℕ) : ℕ := if h : 0 < n then ν ⟨n - 1, by omega⟩ else 0

theorem natW_add_lastNat {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n)
    (h : ∀ a, lam.w a = (ν a : ℤ) + c) (a : Fin n) : lam.natW a + lastNat ν = ν a := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) a.2
  have ha : a ≤ (⟨n - 1, by omega⟩ : Fin n) := Fin.le_def.2 (by have := a.2; simp only; omega)
  have hl := lam.anti ha
  rw [h, h] at hl
  simp only [DomWeight.natW, DomWeight.detShift, lastNat, dif_pos hn, h]
  omega

theorem antitone_of_weight_eq {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n)
    (h : ∀ a, lam.w a = (ν a : ℤ) + c) : Antitone ν := fun a b hab => by
  have := lam.anti hab
  rw [h, h] at this
  omega

theorem detPow_detShift_eq {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n)
    (h : ∀ a, lam.w a = (ν a : ℤ) + c) (g : GL (Fin n) ℂ) :
    detPow ℂ n g lam.detShift = detPow ℂ n g c * (g : Matrix (Fin n) (Fin n) ℂ).det ^ lastNat ν := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : Matrix.GeneralLinearGroup.det g = 1 := Units.ext (by simp)
    simp [detPow, h1, lastNat]
  · have hs : lam.detShift = (lastNat ν : ℤ) + c := by simp [DomWeight.detShift, lastNat, hn, h]
    rw [hs, detPow, detPow, zpow_add, Units.val_mul, zpow_natCast, mul_comm]
    simp

theorem detPowMul_mem {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n)
    (h : ∀ a, lam.w a = (ν a : ℤ) + c) (v : nablaSq ℂ n lam) :
    Formalism.GradedWeylDivisibility.lpMinor ℂ n le_rfl le_rfl ^ lastNat ν * (v : MvPolynomial (Fin n × Fin n) ℂ) ∈
      Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν := by
  have hm := (genericDet_pow_mul n (lastNat ν) lam.natW).1 v v.2
  have e : (fun i => lam.natW i + lastNat ν) = ν := funext (natW_add_lastNat ν c lam h)
  rwa [e] at hm

def detPowMul {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n) (h : ∀ a, lam.w a = (ν a : ℤ) + c) :
    nablaSq ℂ n lam →ₗ[ℂ] Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν :=
  LinearMap.codRestrict _ ((LinearMap.mulLeft ℂ (Formalism.GradedWeylDivisibility.lpMinor ℂ n le_rfl le_rfl ^ lastNat ν)).comp
    (nablaSq ℂ n lam).subtype) (detPowMul_mem ν c lam h)

theorem detPowMul_coe {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n) (h : ∀ a, lam.w a = (ν a : ℤ) + c)
    (v : nablaSq ℂ n lam) : (detPowMul ν c lam h v : MvPolynomial (Fin n × Fin n) ℂ) =
      Formalism.GradedWeylDivisibility.lpMinor ℂ n le_rfl le_rfl ^ lastNat ν * (v : MvPolynomial (Fin n × Fin n) ℂ) := rfl

theorem detPowMul_sqRep {n : ℕ} (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n) (h : ∀ a, lam.w a = (ν a : ℤ) + c)
    (g : GL (Fin n) ℂ) (v : nablaSq ℂ n lam) :
    (detPowMul ν c lam h (GlobalTheory.Branching.sqRep ℂ n lam g v) : MvPolynomial (Fin n × Fin n) ℂ) =
      detPow ℂ n g c • Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose
        (detPowMul ν c lam h v : MvPolynomial (Fin n × Fin n) ℂ) := by
  rw [detPowMul_coe, detPowMul_coe, sqRep_coe, sqAct, (genericDet_pow_mul n (lastNat ν) (fun _ => 0)).2.1,
    Matrix.det_transpose, detPow_detShift_eq ν c lam h, mul_smul_comm, smul_smul]

end GlobalTheory.Branching

namespace GlobalTheory.Branching

theorem exists_surjective_detPowMul_dualWeyl : ∀ (n : ℕ) (ν : Fin n → ℕ) (c : ℤ) (lam : DomWeight n), (∀ a, lam.w a = (ν a : ℤ) + c) → ∃ e : nablaSq ℂ n lam →ₗ[ℂ] Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν, Function.Surjective e ∧ ∀ (g : GL (Fin n) ℂ) v, (e (GlobalTheory.Branching.sqRep ℂ n lam g v) : MvPolynomial (Fin n × Fin n) ℂ) = detPow ℂ n g c • Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose (e v : MvPolynomial (Fin n × Fin n) ℂ) := by
  intro n ν c lam h
  refine ⟨detPowMul ν c lam h, ?_, detPowMul_sqRep ν c lam h⟩
  let M : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ) :=
    (LinearMap.range (detPowMul ν c lam h)).map (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν).subtype
  have hU : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ M, Formalism.GradedWeylDivisibility.rowAct ℂ u f ∈ M := by
    rintro u hu _ ⟨_, ⟨v, rfl⟩, rfl⟩
    let t : Matrix.unitaryGroup (Fin n) ℂ := Matrix.UnitaryGroup.transpose ⟨u, hu⟩
    have h1 : (detPowMul ν c lam h (sqRep ℂ n lam (unitaryIncl n t) v) : MvPolynomial (Fin n × Fin n) ℂ) ∈ M :=
      ⟨_, ⟨_, rfl⟩, rfl⟩
    rw [detPowMul_sqRep] at h1
    have e : ((unitaryIncl n t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).transpose = u := by
      simp [t]
    rw [e] at h1
    exact (M.smul_mem_iff (Units.ne_zero _)).1 h1
  have hcl := rowDivClosed_of_rowAct_stable M (rowAct_mem_of_unitary_stable M hU)
  have hν := antitone_of_weight_eq ν c lam h
  have hle : M ≤ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν := Submodule.map_subtype_le _ _
  have hne : M ≠ ⊥ := by
    intro e0
    have ha : Antitone lam.natW := fun i j hij => by
      have := lam.anti hij
      simp only [DomWeight.natW]
      omega
    let v : nablaSq ℂ n lam := ⟨_, Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl _ ha⟩
    have hm : (detPowMul ν c lam h v : MvPolynomial (Fin n × Fin n) ℂ) ∈ M := ⟨_, ⟨v, rfl⟩, rfl⟩
    have e : (fun i => lam.natW i + lastNat ν) = ν := funext (natW_add_lastNat ν c lam h)
    rw [e0, Submodule.mem_bot, detPowMul_coe] at hm
    change Formalism.GradedWeylDivisibility.lpMinor ℂ n le_rfl le_rfl ^ lastNat ν * Formalism.GradedWeylDivisibility.hw ℂ le_rfl lam.natW = 0 at hm
    rw [genericDet_pow_mul_hw, e] at hm
    exact Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl ν hm
  have hall := dualWeyl_le_of_rowDivClosed le_rfl ν hν M hle hcl hne
  intro y
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hall y.2
  exact ⟨x, Subtype.ext hx⟩

end GlobalTheory.Branching
end
end

section
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

noncomputable section

namespace GlobalTheory.FischerInvariance

open MvPolynomial GlobalTheory.DefLift.BilFischer

theorem rowAct_eq_lin {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) g =
      lin (fun v w : Fin n × Fin n => if w.2 = v.2 then g v.1 w.1 else 0) := by
  unfold Formalism.GradedWeylDivisibility.rowAct lin
  congr 1
  funext v
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single v.2]
  · simp [smul_eq_C_mul]
  · intro s _ hs
    simp [hs]
  · simp

theorem rowAct_comp {n : ℕ} (g h : Matrix (Fin n) (Fin n) ℂ) :
    (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) g).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) h) =
      Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (h * g) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.rowAct, aeval_X, map_sum, map_mul, aeval_C,
    Matrix.mul_apply, map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  simp [Algebra.algebraMap_eq_smul_one, mul_assoc]

theorem rowAct_inv_cancel {n : ℕ} (g : GL (Fin n) ℂ) (u : MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ)
      (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) u) = u := by
  have h := congrArg (fun φ => φ u) (rowAct_comp (n := n) (g : Matrix (Fin n) (Fin n) ℂ)
    ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
  simp only [AlgHom.comp_apply] at h
  rw [h, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have : Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (1 : Matrix (Fin n) (Fin n) ℂ) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.one_apply]
  rw [this, AlgHom.id_apply]

theorem pair_conj_self {σ : Type} [Fintype σ] (u : MvPolynomial σ ℂ) :
    pair (map (starRingEnd ℂ) u) u =
      ((∑ α ∈ u.support, (∏ i, ((α i).factorial : ℝ)) * Complex.normSq (coeff α u) : ℝ) : ℂ) := by
  have hv : map (starRingEnd ℂ) u = ∑ α ∈ u.support, monomial α (starRingEnd ℂ (coeff α u)) := by
    conv_lhs => rw [u.as_sum]
    rw [map_sum]
    simp only [map_monomial]
  rw [hv, map_sum, LinearMap.sum_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [pair_monomial, Complex.ofReal_mul, Complex.ofReal_prod, wt]
  push_cast
  rw [← Complex.mul_conj]
  ring

theorem pair_conj_self_ne_zero {σ : Type} [Fintype σ] (u : MvPolynomial σ ℂ) (hu : u ≠ 0) :
    pair (map (starRingEnd ℂ) u) u ≠ 0 := by
  rw [pair_conj_self, Ne, Complex.ofReal_eq_zero]
  apply ne_of_gt
  apply Finset.sum_pos
  · intro α hα
    apply mul_pos
    · exact Finset.prod_pos fun i _ => Nat.cast_pos.2 (Nat.factorial_pos _)
    · exact Complex.normSq_pos.2 (mem_support_iff.1 hα)
  · exact support_nonempty.2 hu

theorem fischer_dualWeyl_invariant (n : ℕ) (ν : Fin n → ℕ) :
    ∃ b : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] ℂ,
      (∀ u ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν, u ≠ 0 → ∃ v ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν, b v u ≠ 0) ∧
      ∀ (g : GL (Fin n) ℂ) v u,
        b (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose v)
          (Formalism.UG.dwAct ℂ n n g u) = b v u := by
  refine ⟨pair, fun u hu hu0 => ⟨map (starRingEnd ℂ) u, GlobalTheory.SemilinTransport.map_mem _ hu,
    pair_conj_self_ne_zero u hu0⟩, fun g v u => ?_⟩
  rw [rowAct_eq_lin, pair_lin]
  have hT : (fun v w : Fin n × Fin n =>
      if v.2 = w.2 then (g : Matrix (Fin n) (Fin n) ℂ).transpose w.1 v.1 else 0) =
      fun v w => if w.2 = v.2 then (g : Matrix (Fin n) (Fin n) ℂ) v.1 w.1 else 0 := by
    funext v w
    by_cases h : v.2 = w.2
    · simp [h, Matrix.transpose_apply]
    · simp [h, Ne.symm h]
  rw [hT, ← rowAct_eq_lin]
  unfold Formalism.UG.dwAct
  rw [rowAct_inv_cancel]

end GlobalTheory.FischerInvariance

end
end

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_weyl_invariant_pairing : ∀ (n : ℕ) (ν : Fin n → ℕ), ∃ b : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] ℂ, (∀ u ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν, u ≠ 0 → ∃ v ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν, b v u ≠ 0) ∧ ∀ (g : GL (Fin n) ℂ) v u, b (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose v) (Formalism.UG.dwAct ℂ n n g u) = b v u := by
  atlas_forward_decl GlobalTheory.FischerInvariance.fischer_dualWeyl_invariant
end

section
section
namespace GlobalTheory

open Module

theorem pairing_surjective_of_separating {M N : Type} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] [FiniteDimensional ℂ N] (b : M →ₗ[ℂ] N →ₗ[ℂ] ℂ)
    (hb : ∀ u, u ≠ 0 → ∃ v, b v u ≠ 0) : Function.Surjective b := by
  rw [← LinearMap.range_eq_top]
  have hco : (LinearMap.range b).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Submodule.mem_dualCoannihilator] at hu
    by_contra h0
    obtain ⟨v, hv⟩ := hb u h0
    exact hv (hu _ ⟨v, rfl⟩)
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range b), hco,
    Submodule.dualAnnihilator_bot]

theorem tensor_pairing_separating : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M N : ι → Type)
    [∀ τ, AddCommGroup (M τ)] [∀ τ, Module ℂ (M τ)] [∀ τ, AddCommGroup (N τ)]
    [∀ τ, Module ℂ (N τ)] [∀ τ, FiniteDimensional ℂ (N τ)] (b : ∀ τ, M τ →ₗ[ℂ] N τ →ₗ[ℂ] ℂ),
    (∀ τ u, u ≠ 0 → ∃ v, b τ v u ≠ 0) →
    ∃ B : MultilinearMap ℂ M (Module.Dual ℂ (PiTensorProduct ℂ N)),
      (∀ v x, B v (PiTensorProduct.tprod ℂ x) = ∏ τ, b τ (v τ) (x τ)) ∧
      ∀ u, u ≠ 0 → ∃ v, B v u ≠ 0 := by
  intro ι _ _ M N _ _ _ _ _ b hb
  refine ⟨(PiTensorProduct.dualDistrib (R := ℂ) (M := N)).compMultilinearMap
    ((PiTensorProduct.tprod ℂ).compLinearMap b), ?_, ?_⟩
  · intro v x
    simp [PiTensorProduct.dualDistrib_apply]
  · intro u hu
    let e : ∀ τ, Basis (Fin (finrank ℂ (N τ))) ℂ (N τ) := fun τ => Module.finBasis ℂ (N τ)
    let E := Basis.piTensorProduct e
    obtain ⟨k, hk⟩ : ∃ k, E.repr u k ≠ 0 := by
      by_contra h
      push_neg at h
      exact hu (E.repr.injective (by ext k; simp [h k]))
    have hs : ∀ τ, ∃ v, b τ v = (e τ).coord (k τ) := fun τ =>
      pairing_surjective_of_separating (b τ) (hb τ) _
    choose v hv using hs
    refine ⟨v, ?_⟩
    have key : (PiTensorProduct.dualDistrib (R := ℂ) (M := N))
        (PiTensorProduct.tprod ℂ fun τ => b τ (v τ)) = E.coord k := by
      apply E.ext
      intro j
      simp only [hv, E, Basis.piTensorProduct_apply, PiTensorProduct.dualDistrib_apply,
        Basis.coord_apply, Basis.repr_self]
      rw [← Basis.piTensorProduct_apply, Basis.repr_self]
      simp only [Finsupp.single_apply]
      by_cases hjk : j = k
      · subst hjk; simp
      · rw [if_neg hjk]
        obtain ⟨τ, hτ⟩ : ∃ τ, j τ ≠ k τ := by
          by_contra h; push_neg at h; exact hjk (funext h)
        exact Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ)
    simpa [key] using hk

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_product_nondegenerate_pairing : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M N : ι → Type) [∀ τ, AddCommGroup (M τ)] [∀ τ, Module ℂ (M τ)] [∀ τ, AddCommGroup (N τ)] [∀ τ, Module ℂ (N τ)] [∀ τ, FiniteDimensional ℂ (N τ)] (b : ∀ τ, M τ →ₗ[ℂ] N τ →ₗ[ℂ] ℂ), (∀ τ u, u ≠ 0 → ∃ v, b τ v u ≠ 0) → ∃ B : MultilinearMap ℂ M (Module.Dual ℂ (PiTensorProduct ℂ N)), (∀ v x, B v (PiTensorProduct.tprod ℂ x) = ∏ τ, b τ (v τ) (x τ)) ∧ ∀ u, u ≠ 0 → ∃ v, B v u ≠ 0 := by
  atlas_forward_decl GlobalTheory.tensor_pairing_separating
end

section
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

noncomputable section

namespace GlobalTheory.AutPairing

set_option maxHeartbeats 1000000 in

theorem exists_invariant_pairing : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ)
    (lam : ι → DomWeight n), (∀ τ a, (lam τ).w a = (mu τ a : ℤ) + sh τ) →
    ∃ B : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] NablaT ℂ n mu →ₗ[ℂ] ℂ, (∀ u, u ≠ 0 → ∃ v, B v u ≠ 0) ∧
      ∀ (g : ι → GL (Fin n) ℂ) v u, B (Formalism.L2.DIV.rhoK lam g v) (wtOp ℂ n mu sh g u) = B v u := by
  intro n ι _ _ mu sh lam hlam
  have hE : ∀ τ, ∃ e : nablaSq ℂ n (lam τ) →ₗ[ℂ] Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)),
      Function.Surjective e ∧ ∀ (g : GL (Fin n) ℂ) v,
        (e (GlobalTheory.Branching.sqRep ℂ n (lam τ) g v) : MvPolynomial (Fin n × Fin n) ℂ) =
          detPow ℂ n g (sh τ) • Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose
            (e v : MvPolynomial (Fin n × Fin n) ℂ) :=
    fun τ => GlobalTheory.Branching.exists_surjective_detPowMul_dualWeyl n (Formalism.CohomologicalDescent.LD.res n (mu τ)) (sh τ) (lam τ) (fun a => hlam τ a)
  choose e he_surj he_eq using hE
  have hF : ∀ τ, ∃ b : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] ℂ,
      (∀ u ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)), u ≠ 0 →
        ∃ v ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)), b v u ≠ 0) ∧
      ∀ (g : GL (Fin n) ℂ) v u, b (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose v)
        (Formalism.UG.dwAct ℂ n n g u) = b v u :=
    fun τ => GlobalTheory.T.dual_weyl_invariant_pairing n (Formalism.CohomologicalDescent.LD.res n (mu τ))
  choose b hb_sep hb_inv using hF
  let bt : ∀ τ, nablaSq ℂ n (lam τ) →ₗ[ℂ] Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)) →ₗ[ℂ] ℂ :=
    fun τ => ((b τ).compl₂ (Submodule.subtype _)).comp ((Submodule.subtype _).comp (e τ))
  have bt_apply : ∀ τ v u, bt τ v u =
      b τ (e τ v : MvPolynomial (Fin n × Fin n) ℂ) (u : MvPolynomial (Fin n × Fin n) ℂ) := fun _ _ _ => rfl
  have bt_sep : ∀ τ u, u ≠ 0 → ∃ v, bt τ v u ≠ 0 := by
    intro τ u hu
    have hu' : (u : MvPolynomial (Fin n × Fin n) ℂ) ≠ 0 := fun h => hu (Subtype.ext h)
    obtain ⟨v, hv, hne⟩ := hb_sep τ u u.2 hu'
    obtain ⟨w, hw⟩ := he_surj τ ⟨v, hv⟩
    exact ⟨w, by rw [bt_apply, hw]; exact hne⟩
  have bt_inv : ∀ τ (g : GL (Fin n) ℂ) v u,
      bt τ (GlobalTheory.Branching.sqRep ℂ n (lam τ) g v) (Formalism.UG.dualWeylRep ℂ n n _ g u) =
        detPow ℂ n g (sh τ) * bt τ v u := by
    intro τ g v u
    rw [bt_apply, bt_apply, he_eq]
    have h1 : (Formalism.UG.dualWeylRep ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)) g u : MvPolynomial (Fin n × Fin n) ℂ) =
        Formalism.UG.dwAct ℂ n n g u := rfl
    rw [h1, map_smul, LinearMap.smul_apply, hb_inv, smul_eq_mul]
  haveI : ∀ τ, FiniteDimensional ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ))) :=
    (GlobalTheory.T.weight_module_finite_continuous n ι mu sh).1
  obtain ⟨Bm, hBm, hBm_sep⟩ := GlobalTheory.T.tensor_product_nondegenerate_pairing ι (fun τ => nablaSq ℂ n (lam τ))
    (fun τ => Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ))) bt bt_sep
  obtain ⟨B, hB, -⟩ := GlobalTheory.CoefIrred.vv_universal ι n lam (Module.Dual ℂ (NablaT ℂ n mu)) Bm
  refine ⟨B, fun u hu => ?_, fun g => ?_⟩
  · obtain ⟨v, hv⟩ := hBm_sep u hu
    exact ⟨GlobalTheory.CoefIrred.tenMul lam v, by rw [hB]; exact hv⟩
  · have hc : ((∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ (-sh τ) : ℂˣ) : ℂ) *
        ∏ τ, detPow ℂ n (g τ) (sh τ) = 1 := by
      simp only [detPow]
      rw [← Units.coe_prod, ← Units.val_mul, ← Finset.prod_mul_distrib]
      simp [← zpow_add]
    have hpure : ∀ x y, B (Formalism.L2.DIV.rhoK lam g (GlobalTheory.CoefIrred.tenMul lam x))
        (wtOp ℂ n mu sh g (PiTensorProduct.tprod ℂ y)) = B (GlobalTheory.CoefIrred.tenMul lam x) (PiTensorProduct.tprod ℂ y) := by
      intro x y
      rw [GlobalTheory.DefU.rhoK_tenMul, hB, hB, wtOp_apply, GlobalTheory.SemilinTransport.grp_tprod, map_smul, hBm, hBm, smul_eq_mul]
      simp_rw [bt_inv]
      rw [Finset.prod_mul_distrib, ← mul_assoc, hc, one_mul]
    have hten : ∀ x u, B (Formalism.L2.DIV.rhoK lam g (GlobalTheory.CoefIrred.tenMul lam x)) (wtOp ℂ n mu sh g u) =
        B (GlobalTheory.CoefIrred.tenMul lam x) u := by
      intro x u
      induction u using PiTensorProduct.induction_on with
      | smul_tprod c y => rw [map_smul, map_smul, map_smul, hpure]
      | add a a' ha ha' => rw [map_add, map_add, map_add, ha, ha']
    have h1 : ∀ x, ((B.comp (Formalism.L2.DIV.rhoK lam g)).compl₂ (wtOp ℂ n mu sh g)) (GlobalTheory.CoefIrred.tenMul lam x) = Bm x := by
      intro x
      refine LinearMap.ext fun u => ?_
      rw [LinearMap.compl₂_apply, LinearMap.comp_apply, hten, hB]
    have h2 := (GlobalTheory.CoefIrred.vv_universal ι n lam (Module.Dual ℂ (NablaT ℂ n mu)) Bm).unique h1 hB
    intro v u
    have := LinearMap.congr_fun (LinearMap.congr_fun h2 v) u
    simpa using this

end GlobalTheory.AutPairing

end
end

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_module_invariant_pairing : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ) (lam : ι → DomWeight n), (∀ τ a, (lam τ).w a = (mu τ a : ℤ) + sh τ) → ∃ B : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] NablaT ℂ n mu →ₗ[ℂ] ℂ, (∀ u, u ≠ 0 → ∃ v, B v u ≠ 0) ∧ ∀ (g : ι → GL (Fin n) ℂ) v u, B (Formalism.L2.DIV.rhoK lam g v) (wtOp ℂ n mu sh g u) = B v u := by
  atlas_forward_decl GlobalTheory.AutPairing.exists_invariant_pairing
end

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

noncomputable section

namespace GlobalTheory.RealSpan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ι : Type} [Fintype ι]



end GlobalTheory.RealSpan

end
end

section
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

namespace GlobalTheory.DefU.EquivWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem cEmb_eq_one_of_mem_embU {τ τ' : E →+* ℂ} (h : InfinitePlace.mk τ' ≠ InfinitePlace.mk τ) {x : UA E n}
    (hx : x ∈ embU n τ) : cEmb τ' x = 1 := by
  have h1 := (Subgroup.mem_inf.1 hx).2
  rw [Subgroup.mem_iInf] at h1
  have h2 := h1 τ'
  rw [Subgroup.mem_iInf] at h2
  exact h2 h

theorem rhoK_tenMul_update {ι : Type} [Fintype ι] [DecidableEq ι] (σ : ι → (E →+* ℂ)) (lam : ι → DomWeight n)
    (hσ : Function.Injective (fun τ => InfinitePlace.mk (σ τ))) (τ₀ : ι) {x : UA E n} (hx : x ∈ embU n (σ τ₀))
    (e : ∀ τ, nablaSq ℂ n (lam τ)) (a : nablaSq ℂ n (lam τ₀)) :
    Formalism.L2.DIV.rhoK (K := ℂ) lam ((MonoidHom.pi fun τ => cEmb (E := E) (n := n) (σ τ)) x)
              (GlobalTheory.CoefIrred.tenMul lam (Function.update e τ₀ a)) =
      GlobalTheory.CoefIrred.tenMul lam (Function.update e τ₀ (GlobalTheory.Branching.sqRep ℂ n (lam τ₀) (cEmb (σ τ₀) x) a)) := by
  rw [rhoK_tenMul]
  congr 1
  funext τ
  by_cases h : τ = τ₀
  · subst h
    simp only [Function.update_self]
    rfl
  · have hne : InfinitePlace.mk (σ τ) ≠ InfinitePlace.mk (σ τ₀) := fun e' => h (hσ e')
    simp only [Function.update_of_ne h, MonoidHom.pi_apply, cEmb_eq_one_of_mem_embU hne hx, map_one,
      Module.End.one_apply]

theorem hasWeightAt_of_equivariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ι : Type) [Fintype ι]
    (σ : ι → (E →+* ℂ)) (lam : ι → DomWeight n), Function.Injective (fun τ => InfinitePlace.mk (σ τ)) →
    ∀ (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ (f : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] (UA E n → ℂ)), f ≠ 0 →
    (∀ v, f v ∈ π) → (∀ (x : infU E n) v, f (((Formalism.L2.DIV.rhoK (K := ℂ) lam).comp
      ((MonoidHom.pi fun τ => cEmb (E := E) (n := n) (σ τ)).comp (infU E n).subtype)) x v) = RU E n x (f v)) →
    ∀ τ, HasWeightAt π (σ τ) (lam τ) ∧ HasWeightAt π (ComplexEmbedding.conjugate (σ τ)) (lam τ).dual := by
  intro E _ _ _ n ι _ σ lam hσ π hπ f hf0 hfπ hfeq τ₀
  classical
  obtain ⟨e, he⟩ : ∃ e, f (GlobalTheory.CoefIrred.tenMul lam e) ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h1 := (GlobalTheory.T.dualWeylModule_tensor_coefficient_universal ι n lam (UA E n → ℂ) 0).unique (y₁ := f) (y₂ := 0)
      (fun u => hc u) (fun u => rfl)
    exact hf0 h1
  have h1 : HasWeightAt π (σ τ₀) (lam τ₀) := by
    refine ⟨isIrreducible_sqRep n (lam τ₀), f ∘ₗ (GlobalTheory.CoefIrred.tenMul lam).toLinearMap e τ₀, fun h0 => he ?_,
      fun a => hfπ _, fun x a => ?_⟩
    · have := LinearMap.congr_fun h0 (e τ₀)
      simpa [MultilinearMap.toLinearMap] using this
    · have hx : x.1 ∈ infU E n := embU_le_infU _ x.2
      have h2 := hfeq ⟨x.1, hx⟩ (GlobalTheory.CoefIrred.tenMul lam (Function.update e τ₀ a))
      change f (Formalism.L2.DIV.rhoK (K := ℂ) lam ((MonoidHom.pi fun τ => cEmb (E := E) (n := n) (σ τ)) x.1) _) = _ at h2
      rw [rhoK_tenMul_update σ lam hσ τ₀ x.2] at h2
      exact h2
  refine ⟨h1, ?_⟩
  have h3 : (AU.mk (⟨π, hπ⟩ : AutSub E n)).HasWt (σ τ₀) (lam τ₀) := (AU.hasWt_mk _ _ _).2 h1
  exact (AU.hasWt_mk _ _ _).1 h3.conjugate

end GlobalTheory.DefU.EquivWt

end
end

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_rep_weight_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ι : Type) [Fintype ι] (σ : ι → (E →+* ℂ)) (lam : ι → DomWeight n), Function.Injective (fun τ => InfinitePlace.mk (σ τ)) → ∀ (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ (f : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] (UA E n → ℂ)), f ≠ 0 → (∀ v, f v ∈ π) → (∀ (x : infU E n) v, f (((Formalism.L2.DIV.rhoK (K := ℂ) lam).comp ((MonoidHom.pi fun τ => cEmb (E := E) (n := n) (σ τ)).comp (infU E n).subtype)) x v) = RU E n x (f v)) → ∀ τ, HasWeightAt π (σ τ) (lam τ) ∧ HasWeightAt π (ComplexEmbedding.conjugate (σ τ)) (lam τ).dual := by
  atlas_forward_decl GlobalTheory.DefU.EquivWt.hasWeightAt_of_equivariant
end

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AutRec

theorem continuous_coord_emb {E : Type} [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ) :
    Continuous (coord (E := E) τ) := by
  unfold coord
  split_ifs
  · exact continuous_apply _
  · exact Complex.continuous_conj.comp (continuous_apply _)

theorem continuous_cEmb_emb {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (τ : E →+* ℂ) :
    Continuous (cEmb (E := E) (n := n) τ) :=
  (Continuous.units_map _ (continuous_id.matrix_map (continuous_coord_emb τ))).comp GlobalTheory.DefU.continuous_cInf


end GlobalTheory.AutRec

end
end
