import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalDstOfIsSst
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodRingGaloisInvariantsIffConst
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonVEqZeroIffExistsCrisIncl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusTensorCrisToSemistableComm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableDieudonneModuleSpansTensorPeriodRing

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_Dst_of_isSst' : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P ρ → FiniteDimensional ℚ_[l] ↥(Dst P ρ) := by
  first | exact @GlobalTheory.Pst.finiteDimensional_Dst_of_isSst | exact GlobalTheory.Pst.finiteDimensional_Dst_of_isSst | (intros; apply GlobalTheory.Pst.finiteDimensional_Dst_of_isSst <;> assumption)
end

section
section
open TensorProduct Module

namespace GlobalTheory

theorem finrank_add_finrank_le_finrank_inf_comap_sub_id :
    ∀ (k : Type) [Field k] (M W : Type) [AddCommGroup M] [Module k M] [AddCommGroup W] [Module k W] (D R : Submodule k M) [FiniteDimensional k ↥D] (F : M →ₗ[k] M) (B : M →ₗ[k] W →ₗ[k] k), R ≤ D → (∀ x ∈ D, F x ∈ D) → (∀ x ∈ R, ∀ w, B x w = 0) → (∀ x ∈ D, ∀ w, B (F x) w = B x w) → (∀ w, (∀ x ∈ D, B x w = 0) → w = 0) → finrank k W + finrank k ↥R ≤ finrank k ↥(D ⊓ R.comap (F - LinearMap.id)) := by
  intro k _ M W _ _ _ _ D R _ F B hRD hFD hBR hBF hnd

  let RV : Submodule k ↥D := R.comap D.subtype
  let T : ↥D →ₗ[k] ↥D := F.restrict hFD - LinearMap.id
  let Q : ↥D →ₗ[k] ↥D ⧸ RV := RV.mkQ ∘ₗ T

  let P : W →ₗ[k] Module.Dual k ↥D := (B ∘ₗ D.subtype).flip
  have hP : ∀ w, P w ∈ RV.dualAnnihilator := by
    intro w
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    exact hBR x.1 hx w
  let L : W →ₗ[k] Module.Dual k (↥D ⧸ RV) :=
    RV.dualCopairing ∘ₗ P.codRestrict RV.dualAnnihilator hP
  have hL : ∀ w (x : ↥D), L w (RV.mkQ x) = B x.1 w := fun _ _ => rfl

  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    apply hnd
    intro x hx
    have h := LinearMap.congr_fun hw (RV.mkQ ⟨x, hx⟩)
    rw [hL, LinearMap.zero_apply] at h
    exact h

  have hLQ : ∀ w, L w ∈ (LinearMap.range Q).dualAnnihilator := by
    intro w
    rw [Submodule.mem_dualAnnihilator]
    rintro _ ⟨x, rfl⟩
    have hTx : ((T x : ↥D) : M) = F x.1 - x.1 := rfl
    show L w (RV.mkQ (T x)) = 0
    rw [hL, hTx, map_sub, LinearMap.sub_apply, hBF x.1 x.2, sub_self]
  have hW : finrank k W ≤ finrank k (LinearMap.range Q).dualAnnihilator :=
    LinearMap.finrank_le_finrank_of_injective (f := L.codRestrict _ hLQ)
      (fun a b h => hLinj (congrArg Subtype.val h))

  have hker : LinearMap.ker Q = (D ⊓ R.comap (F - LinearMap.id)).comap D.subtype := by
    ext x
    constructor
    · intro h
      have h' : T x ∈ RV := (Submodule.Quotient.mk_eq_zero RV).mp h
      exact ⟨x.2, h'⟩
    · intro h
      exact (Submodule.Quotient.mk_eq_zero RV).mpr h.2
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range Q)
  have h2 := Submodule.finrank_quotient_add_finrank RV
  have h3 := LinearMap.finrank_range_add_finrank_ker Q
  have h4 : finrank k ↥RV = finrank k ↥R := (Submodule.comapSubtypeEquivOfLe hRD).finrank_eq
  have h5 : finrank k ↥(LinearMap.ker Q) = finrank k ↥(D ⊓ R.comap (F - LinearMap.id)) := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq
  omega

end GlobalTheory
end

open TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_add_finrank_le_finrank_inf_comap_sub_id' : ∀ (k : Type) [Field k] (M W : Type) [AddCommGroup M] [Module k M] [AddCommGroup W] [Module k W] (D R : Submodule k M) [FiniteDimensional k ↥D] (F : M →ₗ[k] M) (B : M →ₗ[k] W →ₗ[k] k), R ≤ D → (∀ x ∈ D, F x ∈ D) → (∀ x ∈ R, ∀ w, B x w = 0) → (∀ x ∈ D, ∀ w, B (F x) w = B x w) → (∀ w, (∀ x ∈ D, B x w = 0) → w = 0) → finrank k W + finrank k ↥R ≤ finrank k ↥(D ⊓ R.comap (F - LinearMap.id)) := by
  atlas_forward_decl GlobalTheory.finrank_add_finrank_le_finrank_inf_comap_sub_id
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem exists_phiSt_invariant_nondegenerate_linearForm :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), ∃ lam : Bst P →ₗ[ℚ_[l]] ℚ_[l], (∀ c : ↥(K0 K), lam (phiSt P (Polynomial.C (algebraMap ↥(K0 K) P.R.B c))) = lam (Polynomial.C (algebraMap ↥(K0 K) P.R.B c))) ∧ ∀ c : ↥(K0 K), (∀ c' : ↥(K0 K), lam (Polynomial.C (algebraMap ↥(K0 K) P.R.B c') * Polynomial.C (algebraMap ↥(K0 K) P.R.B c)) = 0) → c = 0 := by
  intro l _ P K
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀
  haveI : Nontrivial P.R.B := by
    refine ⟨⟨(P.PD K).t, 0, fun h => (P.PD K).not_mem_filtration_two ?_⟩⟩
    rw [h, map_zero]
    exact Submodule.zero_mem _

  let ι : ↥(K0 K) →ₗ[ℚ_[l]] Bst P :=
    ((Polynomial.monomial 0 : P.R.B →ₗ[P.R.B] Polynomial P.R.B).restrictScalars ℚ_[l]).comp
      (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.B).toLinearMap
  have hι : ∀ c, ι c = Polynomial.C (algebraMap ↥(K0 K) P.R.B c) := fun c => by
    simp [ι, Polynomial.monomial_zero_left]
  have hinj : Function.Injective ι := by
    intro a b hab
    rw [hι, hι] at hab
    exact (algebraMap ↥(K0 K) P.R.B).injective (Polynomial.C_injective hab)

  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective ι (LinearMap.ker_eq_bot.mpr hinj)
  have hgι : ∀ c, g (ι c) = c := fun c => LinearMap.congr_fun hg c
  refine ⟨(Algebra.trace ℚ_[l] ↥(K0 K)).comp g, ?_, ?_⟩
  ·
    intro c
    have hφ : phiSt P (Polynomial.C (algebraMap ↥(K0 K) P.R.B c)) = ι ((P.PD K).σ c) := by
      have hC : ∀ b : P.R.B, phiSt P (Polynomial.C b) = Polynomial.C (P.φB b) := fun b => by
        simp [phiSt, stHom]
      rw [hC, ← P.PD_φ K, (P.PD K).φ_K₀, hι]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hφ, ← hι, hgι, hgι]
    exact Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective (P.PD K).σ (P.PD K).σ_bij) c
  ·
    intro c h
    by_contra hc
    have h1 := h c⁻¹
    rw [← map_mul, ← map_mul, ← hι, LinearMap.comp_apply, hgι, inv_mul_cancel₀ hc] at h1
    have h2 : Algebra.trace ℚ_[l] ↥(K0 K) 1 = (Module.finrank ℚ_[l] ↥(K0 K) : ℚ_[l]) := by
      rw [← map_one (algebraMap ℚ_[l] ↥(K0 K)), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
    rw [h2] at h1
    exact (Nat.cast_ne_zero.mpr Module.finrank_pos.ne') h1

end GlobalTheory.PMon
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearForm_semistable_extending_trace : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), ∃ lam : Bst P →ₗ[ℚ_[l]] ℚ_[l], (∀ c : ↥(K0 K), lam (phiSt P (Polynomial.C (algebraMap ↥(K0 K) P.R.B c))) = lam (Polynomial.C (algebraMap ↥(K0 K) P.R.B c))) ∧ ∀ c : ↥(K0 K), (∀ c' : ↥(K0 K), lam (Polynomial.C (algebraMap ↥(K0 K) P.R.B c') * Polynomial.C (algebraMap ↥(K0 K) P.R.B c)) = 0) → c = 0 := by
  atlas_forward_decl GlobalTheory.PMon.exists_phiSt_invariant_nondegenerate_linearForm
end

section
open TensorProduct Module

namespace GlobalTheory

theorem rTensor_pairing_eq_zero_of_flip_injective : ∀ (F : Type) [Field F] (B : Type) [AddCommGroup B] [Module F B] (V V' : Type) [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (m : V →ₗ[F] V' →ₗ[F] F), (∀ y, (∀ x, m x y = 0) → y = 0) → ∀ y : V' ⊗[F] B, (∀ v : V, TensorProduct.lid F B (LinearMap.rTensor B (m v) y) = 0) → y = 0 := by
  intro F _ B _ _ V V' _ _ _ _ _ m hm y hy
  have hinj : Function.Injective m.flip :=
    (injective_iff_map_eq_zero m.flip).2 fun z h =>
      hm z fun x => by simpa using LinearMap.congr_fun h x
  have hsurj : Function.Surjective m := LinearMap.flip_injective_iff₂.1 hinj
  let b := Module.finBasis F V'
  have key : ∀ z : V' ⊗[F] B,
      z = ∑ j, b j ⊗ₜ (TensorProduct.lid F B (LinearMap.rTensor B (b.coord j) z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v w =>
      simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Basis.coord_apply]
      simp_rw [← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, b.sum_repr]
    | add z₁ z₂ h₁ h₂ =>
      conv_lhs => rw [h₁, h₂]
      simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
  rw [key y]
  refine Finset.sum_eq_zero fun j _ => ?_
  obtain ⟨v, hv⟩ := hsurj (b.coord j)
  rw [← hv, hy v, TensorProduct.tmul_zero]

end GlobalTheory

alias _root_.GlobalTheory.T.eq_zero_of_rTensor_pairing_eq_zero := _root_.GlobalTheory.rTensor_pairing_eq_zero_of_flip_injective
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon.StPairing

section

variable {F : Type} [Field F] {B : Type} [CommRing B] [Algebra F B]
  {V V' : Type} [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V']

def tensorPairing (m : V →ₗ[F] V' →ₗ[F] F) : V ⊗[F] B →ₗ[F] V' ⊗[F] B →ₗ[F] B :=
  (TensorProduct.map₂ m (LinearMap.mul F B)).compr₂ (TensorProduct.lid F B).toLinearMap

@[simp] theorem tensorPairing_tmul (m : V →ₗ[F] V' →ₗ[F] F) (v : V) (a : B) (v' : V') (b : B) :
    tensorPairing m (v ⊗ₜ[F] a) (v' ⊗ₜ[F] b) = m v v' • (a * b) := by
  simp [tensorPairing, TensorProduct.map₂_apply_tmul]

theorem tensorPairing_one (m : V →ₗ[F] V' →ₗ[F] F) (v : V) (y : V' ⊗[F] B) :
    tensorPairing m (v ⊗ₜ[F] (1 : B)) y = TensorProduct.lid F B (LinearMap.rTensor B (m v) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b => simp [tensorPairing_tmul]
  | add y y' hy hy' => simp only [map_add, hy, hy']

theorem induction_two {p : V ⊗[F] B → V' ⊗[F] B → Prop} (h0 : ∀ y, p 0 y) (h0' : ∀ x, p x 0)
    (ht : ∀ v a v' b, p (v ⊗ₜ[F] a) (v' ⊗ₜ[F] b))
    (ha : ∀ x x' y, p x y → p x' y → p (x + x') y)
    (ha' : ∀ x y y', p x y → p x y' → p x (y + y')) (x : V ⊗[F] B) (y : V' ⊗[F] B) : p x y := by
  induction x using TensorProduct.induction_on with
  | zero => exact h0 y
  | tmul v a =>
    induction y using TensorProduct.induction_on with
    | zero => exact h0' _
    | tmul v' b => exact ht v a v' b
    | add y y' hy hy' => exact ha' _ _ _ hy hy'
  | add x x' hx hx' => exact ha _ _ _ hx hx'

end

theorem exists_stPairing : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), IsDual1 (P.PD K) ρ ρ' m → ∃ pr : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] Bst P, (∀ x y, pr (phiV P ℚ_[l] V x) (phiV P ℚ_[l] V' y) = phiSt P (pr x y)) ∧ (∀ x y, pr (monV P ℚ_[l] V x) y + pr x (monV P ℚ_[l] V' y) = monSt P (pr x y)) ∧ (∀ (g : ↥(GK K)) x y, pr (stRep P ρ g x) (stRep P ρ' g y) = ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) • actSt P (g : GQ l) (pr x y)) ∧ (∀ a x y, pr (onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) x) y = a * pr x y) ∧ ∀ y, (∀ v : V, pr (v ⊗ₜ[ℚ_[l]] (1 : Bst P)) y = 0) → y = 0 := by
  intro l _ P K V _ _ _ V' _ _ _ ρ ρ' m hm
  obtain ⟨hg, -, hr, -⟩ := hm
  have hcyc : ∀ g : ↥(GK K), ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) =
      ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) := fun g => by
    have h := P.PD_χ K g
    simp [cycLL, h]
  refine ⟨tensorPairing m, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    refine induction_two (p := fun x y => tensorPairing m (phiV P ℚ_[l] V x) (phiV P ℚ_[l] V' y) =
      phiSt P (tensorPairing m x y)) (by simp) (by simp) ?_ ?_ ?_ x y
    · intro v a v' b
      simp [tensorPairing_tmul, map_mul, map_smul]
    · intro x x' y hx hx'
      simp only [map_add, LinearMap.add_apply, hx, hx']
    · intro x y y' hy hy'
      simp only [map_add, hy, hy']
  · intro x y
    refine induction_two (p := fun x y => tensorPairing m (monV P ℚ_[l] V x) y +
      tensorPairing m x (monV P ℚ_[l] V' y) = monSt P (tensorPairing m x y)) (by simp) (by simp) ?_ ?_ ?_ x y
    · intro v a v' b
      simp only [monV_tmul, tensorPairing_tmul]
      rw [map_smul, ← smul_add]
      congr 1
      simp only [monSt_apply, Polynomial.derivative_mul]
      ring
    · intro x x' y hx hx'
      simp only [map_add, LinearMap.add_apply, ← hx, ← hx']
      abel
    · intro x y y' hy hy'
      simp only [map_add, ← hy, ← hy']
      abel
  · intro g x y
    refine induction_two (p := fun x y => tensorPairing m (stRep P ρ g x) (stRep P ρ' g y) =
      ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) • actSt P (g : GQ l) (tensorPairing m x y))
      (by simp) (by simp) ?_ ?_ ?_ x y
    · intro v a v' b
      rw [stRep_tmul, stRep_tmul, tensorPairing_tmul, tensorPairing_tmul, hg, hcyc, map_smul, map_mul,
        smul_smul]
    · intro x x' y hx hx'
      simp only [map_add, LinearMap.add_apply, hx, hx', smul_add]
    · intro x y y' hy hy'
      simp only [map_add, hy, hy', smul_add]
  · intro a x y
    refine induction_two (p := fun x y => tensorPairing m (onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) x) y =
      a * tensorPairing m x y) (by simp) (by simp) ?_ ?_ ?_ x y
    · intro v b v' c
      rw [onB_tmul, tensorPairing_tmul, tensorPairing_tmul, LinearMap.mulLeft_apply, mul_smul_comm,
        mul_assoc]
    · intro x x' y hx hx'
      simp only [map_add, LinearMap.add_apply, hx, hx', mul_add]
    · intro x y y' hy hy'
      simp only [map_add, hy, hy', mul_add]
  · intro y hy
    refine GlobalTheory.T.eq_zero_of_rTensor_pairing_eq_zero ℚ_[l] (Bst P) V V' m hr y fun v => ?_
    rw [← tensorPairing_one]
    exact hy v

end GlobalTheory.PMon.StPairing
end
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semistable_tensor_pairing_of_dual : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), IsDual1 (P.PD K) ρ ρ' m → ∃ pr : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] Bst P, (∀ x y, pr (phiV P ℚ_[l] V x) (phiV P ℚ_[l] V' y) = phiSt P (pr x y)) ∧ (∀ x y, pr (monV P ℚ_[l] V x) y + pr x (monV P ℚ_[l] V' y) = monSt P (pr x y)) ∧ (∀ (g : ↥(GK K)) x y, pr (stRep P ρ g x) (stRep P ρ' g y) = ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) • actSt P (g : GQ l) (pr x y)) ∧ (∀ a x y, pr (onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) x) y = a * pr x y) ∧ ∀ y, (∀ v : V, pr (v ⊗ₜ[ℚ_[l]] (1 : Bst P)) y = 0) → y = 0 := by
  atlas_forward_decl GlobalTheory.PMon.StPairing.exists_stPairing
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem onB_mulLeft_mem_Dst_of_fixed {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V)
    (a : Bst P) (ha : ∀ g : ↥(GK K), actSt P (g : GQ l) a = a) (x : V ⊗[ℚ_[l]] Bst P)
    (hx : x ∈ Dst P ρ) : onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) x ∈ Dst P ρ := by
  rw [mem_Dst] at hx ⊢
  intro g
  have h : stRep P ρ g * onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) =
      onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) * stRep P ρ g :=
    end_ext P fun v b => by
      simp only [End.mul_apply, onB_tmul, stRep_tmul, LinearMap.mulLeft_apply, map_mul, ha]
  rw [← End.mul_apply, h, End.mul_apply, hx]

theorem exists_pairing_Dst_Dcris_phi_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), IsDual1 (P.PD K) ρ ρ' m → IsSst P ρ → ∃ B : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] ↥(Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)) →ₗ[ℚ_[l]] ℚ_[l], (∀ x ∈ Dst P ρ, ∀ w, B (monV P ℚ_[l] V x) w = 0) ∧ (∀ x ∈ Dst P ρ, ∀ w, B ((l : ℚ_[l]) • phiV P ℚ_[l] V x) w = B x w) ∧ ∀ w, (∀ x ∈ Dst P ρ, B x w = 0) → w = 0 := by
  intro l _ P AI T K V _ _ _ V' _ _ _ ρ ρ' m hd hs
  obtain ⟨pr, hφ, hN, hg, hmul, hnd⟩ := GlobalTheory.T.exists_semistable_tensor_pairing_of_dual l P K V V' ρ ρ' m hd
  obtain ⟨lam, hlφ, hlnd⟩ := GlobalTheory.T.exists_linearForm_semistable_extending_trace l P K
  let W := Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)
  let j : ↥W →ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bst P := (crisIncl P ℚ_[l] V') ∘ₗ W.subtype
  have hj : ∀ w : ↥W, j w = crisIncl P ℚ_[l] V' (w : V' ⊗[ℚ_[l]] P.R.B) := fun _ => rfl
  have hjg : ∀ (w : ↥W) g, stRep P ρ' g (j w) = j w := by
    intro w g
    have h1 := w.2.1
    have h2 : actVB (P.PD K) ρ' g (w : V' ⊗[ℚ_[l]] P.R.B) = w := by
      have := (Submodule.mem_iInf _).mp h1 g
      rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    rw [hj, stRep_crisIncl, h2]
  have hjN : ∀ w : ↥W, monV P ℚ_[l] V' (j w) = 0 := fun w =>
    (GlobalTheory.T.monV_eq_zero_iff_mem_range_crisIncl' l P V' _).mpr ⟨_, (hj w).symm⟩
  have hjφ : ∀ w : ↥W, phiV P ℚ_[l] V' (j w) = j w := by
    intro w
    have h2 : φVB (P.PD K) (LL := ℚ_[l]) (V := V') (w : V' ⊗[ℚ_[l]] P.R.B) = w := by
      have := w.2.2
      rwa [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
        sub_eq_zero] at this
    rw [hj, GlobalTheory.T.frobeniusTensor_crisToSemistable_comm l P K, h2]
  have hinv : ∀ x ∈ Dst P ρ, ∀ w : ↥W, ∃ c : ↥(K0 K), Polynomial.C P.tB * pr x (j w) =
      Polynomial.C (algebraMap ↥(K0 K) P.R.B c) := by
    intro x hx w
    refine (GlobalTheory.T.semistablePeriodRing_galois_invariants_iff_const l P AI T K _).mp fun g => ?_
    have h1 := hg g x (j w)
    rw [(mem_Dst P ρ).mp hx g, hjg] at h1
    rw [map_mul, actSt_C, localPrime_galoisAction_periodT, ← Polynomial.smul_C, smul_mul_assoc, ← mul_smul_comm, ← h1]
  let B : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] ↥W →ₗ[ℚ_[l]] ℚ_[l] :=
    (pr.compl₂ j).compr₂ (lam ∘ₗ LinearMap.mulLeft ℚ_[l] (Polynomial.C P.tB))
  have hB : ∀ x w, B x w = lam (Polynomial.C P.tB * pr x (j w)) := fun _ _ => rfl
  refine ⟨B, fun x hx w => ?_, fun x hx w => ?_, fun w hw => ?_⟩
  · obtain ⟨c, hc⟩ := hinv x hx w
    have h1 := hN x (j w)
    rw [hjN, map_zero, add_zero] at h1
    rw [hB, h1, ← monSt_C_mul, hc, (monSt_eq_zero_iff P _).mpr ⟨_, rfl⟩, map_zero]
  · obtain ⟨c, hc⟩ := hinv x hx w
    have h1 := hφ x (j w)
    rw [hjφ] at h1
    rw [hB, hB, map_smul, LinearMap.smul_apply, h1, mul_smul_comm, ← smul_mul_assoc,
      Polynomial.smul_C, ← localPrime_frobenius_periodT, ← phiSt_C, ← map_mul, hc, hlφ]
  · have h0 : ∀ x ∈ Dst P ρ, pr x (j w) = 0 := by
      intro x hx
      obtain ⟨c, hc⟩ := hinv x hx w
      have hc0 : c = 0 := by
        refine hlnd c fun c' => ?_
        have h2 := hw _ (onB_mulLeft_mem_Dst_of_fixed P ρ _
          ((GlobalTheory.T.semistablePeriodRing_galois_invariants_iff_const l P AI T K _).mpr ⟨c', rfl⟩) x hx)
        rw [hB, hmul, mul_left_comm, hc] at h2
        exact h2
      rw [hc0, map_zero, map_zero] at hc
      exact ((isUnit_tB P).map Polynomial.C).mul_right_eq_zero.mp hc
    have h1 : j w = 0 := by
      refine hnd _ fun v => ?_
      obtain ⟨k, a, x, hx, hv⟩ := GlobalTheory.T.semistableDieudonneModule_spans_tensor_periodRing l P AI T K V ρ hs v
      rw [hv, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hmul, h0 _ (hx i), mul_zero]
    apply Subtype.ext
    apply crisIncl_injective P (LL := ℚ_[l])
    rw [← hj, h1]
    simp

end GlobalTheory.PMon
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pairing_Dst_Dcris_frobenius_fixed : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), IsDual1 (P.PD K) ρ ρ' m → IsSst P ρ → ∃ B : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] ↥(Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)) →ₗ[ℚ_[l]] ℚ_[l], (∀ x ∈ Dst P ρ, ∀ w, B (monV P ℚ_[l] V x) w = 0) ∧ (∀ x ∈ Dst P ρ, ∀ w, B ((l : ℚ_[l]) • phiV P ℚ_[l] V x) w = B x w) ∧ ∀ w, (∀ x ∈ Dst P ρ, B x w = 0) → w = 0 := by
  atlas_forward_decl GlobalTheory.PMon.exists_pairing_Dst_Dcris_phi_one
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory

theorem finrank_dcris_phi_fixed_add_finrank_mon_le : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), IsDual1 (P.PD K) ρ ρ' m → IsSst P ρ → finrank ℚ_[l] ↥(Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)) + finrank ℚ_[l] ↥((Dst P ρ).map (monV P ℚ_[l] V)) ≤ finrank ℚ_[l] ↥(Dst P ρ ⊓ ((Dst P ρ).map (monV P ℚ_[l] V)).comap ((l : ℚ_[l]) • phiV P ℚ_[l] V - LinearMap.id)) := by
  intro l _ P AI T K V _ _ _ V' _ _ _ ρ ρ' m hD hS
  obtain ⟨B, h1, h2, h3⟩ := GlobalTheory.T.exists_pairing_Dst_Dcris_frobenius_fixed l P AI T K V V' ρ ρ' m hD hS
  haveI := GlobalTheory.T.finiteDimensional_Dst_of_isSst' l P K V ρ hS
  refine GlobalTheory.T.finrank_add_finrank_le_finrank_inf_comap_sub_id' ℚ_[l] _ _ (Dst P ρ) ((Dst P ρ).map (monV P ℚ_[l] V))
    ((l : ℚ_[l]) • phiV P ℚ_[l] V) B ?_ ?_ ?_ ?_ h3
  · rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_Dst] at hx
    rw [mem_Dst]
    intro g
    rw [← Module.End.mul_apply, ← monV_stRep, Module.End.mul_apply, hx g]
  · intro x hx
    rw [mem_Dst] at hx ⊢
    intro g
    rw [LinearMap.smul_apply, map_smul, ← Module.End.mul_apply, ← phiV_stRep, Module.End.mul_apply,
      hx g]
  · rintro _ ⟨x, hx, rfl⟩ w
    exact h1 x hx w
  · intro x hx w
    exact h2 x hx w

end GlobalTheory
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_dcris_phi_fixed_add_finrank_mon_le_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), IsDual1 (P.PD K) ρ ρ' m → IsSst P ρ → finrank ℚ_[l] ↥(Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)) + finrank ℚ_[l] ↥((Dst P ρ).map (monV P ℚ_[l] V)) ≤ finrank ℚ_[l] ↥(Dst P ρ ⊓ ((Dst P ρ).map (monV P ℚ_[l] V)).comap ((l : ℚ_[l]) • phiV P ℚ_[l] V - LinearMap.id)) := by
  atlas_forward_decl GlobalTheory.finrank_dcris_phi_fixed_add_finrank_mon_le
end
