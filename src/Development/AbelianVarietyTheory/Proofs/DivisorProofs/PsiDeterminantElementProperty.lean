import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDetEltOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfElementThetaCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeadDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeadMulUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTensorExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOfPadic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumScalarActionStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantFrameComparison
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantValuationOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumEigenMultiplicityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaProjectionSurjectiveEigen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerMapsEigenspacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomsDvrCardEqFinrank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeLatticeElementProperty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerMapSubsetImMap

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem exists_isMat_of_equivariant (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (ρ ρ' : Λ → Matrix (Fin h) (Fin h) (Ainf p O)) (e e' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) (X : Matrix (Fin h) (Fin h) (Ainf p O)) :
    IsFrame ρ e → IsFrame ρ' e' → (∀ l, X * ρ l = ρ' l * X) → ∃ Y, IsMat e e' X Y := by
  intro he he' hX
  let L' : (Fin N → RL p O Λ) →ₗ[Ainf p O] (Fin N → RL p O Λ) :=
    e'.symm.toLinearMap ∘ₗ (Matrix.mulVecLin X) ∘ₗ e.toLinearMap
  have hL' : ∀ w, e' (L' w) = X *ᵥ e w := by
    intro w; simp [L']
  have hl : ∀ (l : Λ) w, L' (((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) • w) = ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) • L' w := by
    intro l w
    apply e'.injective
    rw [hL', he, he', hL', Matrix.mulVec_mulVec, hX, ← Matrix.mulVec_mulVec]
  have hs : ∀ (r : RL p O Λ) w, L' (r • w) = r • L' w := by
    intro r w
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul a l =>
      have : (a ⊗ₜ[ℤ_[p]] l : RL p O Λ) = algebraMap (Ainf p O) (RL p O Λ) a * ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) := by
        simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
      rw [this, mul_smul, mul_smul, algebraMap_smul, algebraMap_smul, L'.map_smul, hl]
    | add x y hx hy => rw [add_smul, add_smul, L'.map_add, hx, hy]
  let L : (Fin N → RL p O Λ) →ₗ[RL p O Λ] (Fin N → RL p O Λ) :=
    { toFun := L'
      map_add' := L'.map_add
      map_smul' := hs }
  refine ⟨LinearMap.toMatrix' L, fun w => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  exact (hL' w).symm

end GlobalTheory.DetInv
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matrix_of_intertwiner : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (ρ ρ' : Λ → Matrix (Fin h) (Fin h) (Ainf p O)) (e e' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) (X : Matrix (Fin h) (Fin h) (Ainf p O)), IsFrame ρ e → IsFrame ρ' e' → (∀ l, X * ρ l = ρ' l * X) → ∃ Y, IsMat e e' X Y := by
  atlas_forward_decl GlobalTheory.DetInv.exists_isMat_of_equivariant
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem isMat_calculus : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (e e' e'' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)), (∀ X X' Y Y', IsMat e e' X Y → IsMat e' e'' X' Y' → IsMat e e'' (X' * X) (Y' * Y)) ∧ (∀ X Y Y', IsMat e e' X Y → IsMat e e' X Y' → Y = Y') ∧ ∀ c : Ainf p O, IsMat e e (c • (1 : Matrix (Fin h) (Fin h) (Ainf p O))) ((inA c : RL p O Λ) • (1 : Matrix (Fin N) (Fin N) (RL p O Λ))) := by
  intro p _ O _ _ _ Λ _ _ N h e e' e''
  refine ⟨?_, ?_, ?_⟩
  · intro X X' Y Y' h1 h2 w
    rw [← Matrix.mulVec_mulVec, h1 w, h2 (Y *ᵥ w), Matrix.mulVec_mulVec]
  · intro X Y Y' h1 h2
    have key : ∀ w, Y *ᵥ w = Y' *ᵥ w := fun w => e'.injective ((h1 w).symm.trans (h2 w))
    ext i j
    have := congrFun (key (Pi.single j 1)) i
    simpa using this
  · intro c w
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      ← map_smul, algebraMap_smul]

end GlobalTheory.DetInv
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_matrix_composition_unique : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (e e' e'' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)), (∀ X X' Y Y', IsMat e e' X Y → IsMat e' e'' X' Y' → IsMat e e'' (X' * X) (Y' * Y)) ∧ (∀ X Y Y', IsMat e e' X Y → IsMat e e' X Y' → Y = Y') ∧ ∀ c : Ainf p O, IsMat e e (c • (1 : Matrix (Fin h) (Fin h) (Ainf p O))) ((inA c : RL p O Λ) • (1 : Matrix (Fin N) (Fin N) (RL p O Λ))) := by
  atlas_forward_decl GlobalTheory.DetInv.isMat_calculus
end

section
section
noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv.Twist

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]

def phiR : RL p O Λ →+* RL p O Λ :=
  (Algebra.TensorProduct.map (PsiPhi.frobAlg (p := p) (O := O)) (AlgHom.id ℤ_[p] Λ)).toRingHom

def psiR : RL p O Λ →+* RL p O Λ :=
  (Algebra.TensorProduct.map (PsiPhi.phiInvAlg (p := p) (O := O)) (AlgHom.id ℤ_[p] Λ)).toRingHom

theorem phiR_tmul (a : Ainf p O) (l : Λ) : phiR (a ⊗ₜ[ℤ_[p]] l) = WittVector.frobenius a ⊗ₜ l := rfl

theorem psiR_tmul (a : Ainf p O) (l : Λ) : psiR (a ⊗ₜ[ℤ_[p]] l) = phiInv p O a ⊗ₜ l := rfl

theorem eq_psiR {ψ : RL p O Λ →+* RL p O Λ} (hψ : IsPsi ψ) (r : RL p O Λ) : ψ r = psiR r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a l => rw [hψ, psiR_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem phiR_psiR (r : RL p O Λ) : phiR (psiR r) = r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a l => rw [psiR_tmul, phiR_tmul, PsiPhi.frobenius_phiInv']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem psiR_phiR (r : RL p O Λ) : psiR (phiR r) = r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a l => rw [phiR_tmul, psiR_tmul, PsiPhi.phiInv_frobenius']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem phiR_smul (a : Ainf p O) (r : RL p O Λ) :
    phiR (a • r) = WittVector.frobenius a • phiR r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul x l => rw [TensorProduct.smul_tmul', phiR_tmul, phiR_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem phiR_one_tmul_mul (l : Λ) (r : RL p O Λ) :
    phiR (((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) * r) = ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) * phiR r := by
  rw [map_mul, phiR_tmul, map_one]

variable {N h : ℕ}

def twist (e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) :
    (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O) where
  toFun w := fun j => phiInv p O (e (fun i => phiR (w i)) j)
  invFun v := fun i => psiR (e.symm (fun j => WittVector.frobenius (v j)) i)
  map_add' x y := by
    funext j
    simp only [Pi.add_apply, map_add]
    rw [show (fun i => phiR (x i) + phiR (y i)) = (fun i => phiR (x i)) + fun i => phiR (y i) from rfl,
      map_add, Pi.add_apply, map_add]
  map_smul' a x := by
    funext j
    simp only [Pi.smul_apply, RingHom.id_apply, phiR_smul, smul_eq_mul]
    rw [show (fun i => WittVector.frobenius a • phiR (x i)) =
      WittVector.frobenius a • (fun i => phiR (x i)) from rfl, map_smul, Pi.smul_apply, smul_eq_mul,
      map_mul, PsiPhi.phiInv_frobenius']
  left_inv w := by
    funext i
    simp only [PsiPhi.frobenius_phiInv']
    rw [show (fun j => e (fun i => phiR (w i)) j) = e (fun i => phiR (w i)) from rfl,
      LinearEquiv.symm_apply_apply, psiR_phiR]
  right_inv v := by
    funext j
    simp only [phiR_psiR]
    rw [show (fun i => e.symm (fun j => WittVector.frobenius (v j)) i) =
      e.symm (fun j => WittVector.frobenius (v j)) from rfl, LinearEquiv.apply_symm_apply,
      PsiPhi.phiInv_frobenius']

theorem twist_apply (e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) (w) :
    twist e w = fun j => phiInv p O (e (fun i => phiR (w i)) j) := rfl

end GlobalTheory.DetInv.Twist

namespace GlobalTheory.DetInv

open Twist in

theorem frame_twist : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ)
    (ψ : RL p O Λ →+* RL p O Λ) (ρ : Λ → Matrix (Fin h) (Fin h) (Ainf p O))
    (e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)), IsPsi ψ → IsFrame ρ e →
    ∃ e' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O),
      IsFrame (fun l => (ρ l).map (phiInv p O)) e' ∧
        ∀ w, e' (fun i => ψ (w i)) = fun j => phiInv p O (e w j) := by
  intro p _ O _ _ _ Λ _ _ N h ψ ρ e hψ he
  refine ⟨twist e, fun l w => ?_, fun w => ?_⟩
  · rw [twist_apply, twist_apply]
    have h1 : (fun i => phiR ((((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) • w) i)) =
        ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) • fun i => phiR (w i) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, phiR_one_tmul_mul]
    rw [h1, he]
    funext j
    have := RingHom.map_mulVec (phiInv p O) (ρ l) (e (fun i => phiR (w i))) j
    exact this
  · rw [twist_apply]
    funext j
    simp only [eq_psiR hψ, phiR_psiR]

end GlobalTheory.DetInv
end
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobenius_twisted_frame : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (ψ : RL p O Λ →+* RL p O Λ) (ρ : Λ → Matrix (Fin h) (Fin h) (Ainf p O)) (e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)), IsPsi ψ → IsFrame ρ e → ∃ e' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O), IsFrame (fun l => (ρ l).map (phiInv p O)) e' ∧ ∀ w, e' (fun i => ψ (w i)) = fun j => phiInv p O (e w j) := by
  atlas_forward_decl GlobalTheory.DetInv.frame_twist
end

section
section
noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem frame_psi_eq_phiInv : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (ψ : RL p O Λ →+* RL p O Λ) (e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)), IsPsi ψ → (∀ (i : Fin N) (l : Λ), ∃ t : Fin h → ℤ_[p], e (Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l)) = fun j => ofPadic p O (t j)) → ∀ w, e (fun i => ψ (w i)) = fun j => phiInv p O (e w j) := by
  intro p _ O _ _ _ Λ _ _ N h ψ e hψ ht w
  have key : ∀ (i : Fin N) (r : RL p O Λ),
      e (Pi.single i (ψ r)) = fun j => phiInv p O (e (Pi.single i r) j) := by
    intro i r
    induction r using TensorProduct.induction_on with
    | zero => funext j; simp
    | tmul a l =>
      rw [hψ]
      have h1 : ∀ b : Ainf p O, (Pi.single i (b ⊗ₜ[ℤ_[p]] l) : Fin N → RL p O Λ) =
          b • Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) := by
        intro b
        ext k
        rcases eq_or_ne k i with rfl | hk
        · simp [TensorProduct.smul_tmul']
        · simp [hk]
      obtain ⟨t, ht'⟩ := ht i l
      rw [h1 (phiInv p O a), h1 a, map_smul, map_smul, ht']
      funext j
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, PsiPhi.phiInv_ofPadic]
    | add x y hx hy =>
      rw [map_add ψ, Pi.single_add, map_add e, hx, hy, Pi.single_add, map_add e]
      funext j
      simp only [Pi.add_apply, map_add]
  have hw : (fun i => ψ (w i)) = ∑ i, Pi.single i (ψ (w i)) := (Finset.univ_sum_single _).symm
  rw [hw, map_sum]
  conv_rhs => rw [← Finset.univ_sum_single w, map_sum]
  funext j
  simp only [Finset.sum_apply, key, map_sum]

end GlobalTheory.DetInv
end
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_psi_coordinates_padic : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (ψ : RL p O Λ →+* RL p O Λ) (e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)), IsPsi ψ → (∀ (i : Fin N) (l : Λ), ∃ t : Fin h → ℤ_[p], e (Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l)) = fun j => ofPadic p O (t j)) → ∀ w, e (fun i => ψ (w i)) = fun j => phiInv p O (e w j) := by
  atlas_forward_decl GlobalTheory.DetInv.frame_psi_eq_phiInv
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem isMat_twist : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (ψ : RL p O Λ →+* RL p O Λ) (e e' t t' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) (X : Matrix (Fin h) (Fin h) (Ainf p O)) (Y : Matrix (Fin N) (Fin N) (RL p O Λ)), Function.Surjective ψ → (∀ w, t (fun i => ψ (w i)) = fun j => phiInv p O (e w j)) → (∀ w, t' (fun i => ψ (w i)) = fun j => phiInv p O (e' w j)) → IsMat e e' X Y → IsMat t t' (X.map (phiInv p O)) (Y.map ψ) := by
  intro p _ O _ _ _ Λ _ _ N h ψ e e' t t' X Y hψ ht ht' hXY v
  obtain ⟨w, rfl⟩ : ∃ w : Fin N → RL p O Λ, (fun i => ψ (w i)) = v :=
    ⟨fun i => (hψ (v i)).choose, funext fun i => (hψ (v i)).choose_spec⟩
  have hY : Y.map ψ *ᵥ (fun i => ψ (w i)) = fun i => ψ ((Y *ᵥ w) i) := by
    funext i
    exact (RingHom.map_mulVec ψ Y w i).symm
  rw [hY, ht, ht', ← hXY w]
  funext j
  exact (RingHom.map_mulVec (phiInv p O) X (e w) j).symm

end GlobalTheory.DetInv
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_transition_psi_matrix : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (ψ : RL p O Λ →+* RL p O Λ) (e e' t t' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) (X : Matrix (Fin h) (Fin h) (Ainf p O)) (Y : Matrix (Fin N) (Fin N) (RL p O Λ)), Function.Surjective ψ → (∀ w, t (fun i => ψ (w i)) = fun j => phiInv p O (e w j)) → (∀ w, t' (fun i => ψ (w i)) = fun j => phiInv p O (e' w j)) → IsMat e e' X Y → IsMat t t' (X.map (phiInv p O)) (Y.map ψ) := by
  atlas_forward_decl GlobalTheory.DetInv.isMat_twist
end

section
section
noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem exists_freeForm : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (N h : ℕ) , h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → Nonempty (FreeForm D N ψ) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ N h hh D ψ hψ
  obtain ⟨eT, eM, hT, hM, hrat⟩ := GlobalTheory.T.determinant_frame_comparison p C v O hv ε hε Λ N h hh D
  obtain ⟨tM, htM, htw⟩ := GlobalTheory.T.exists_frobenius_twisted_frame p O Λ N h ψ D.ρM eM hψ hM
  have hTw := GlobalTheory.T.frame_psi_coordinates_padic p O Λ N h ψ eT hψ hrat
  obtain ⟨hscal, hFG, hG, hΨ, hΨ'⟩ := GlobalTheory.T.sandwich_datum_scalar_action p C v O hv ε hε Λ h D
  obtain ⟨-, -, ψ₀, φ₀, hψ₀, -, -, hφψ⟩ := GlobalTheory.DetInv.psi_phi_tensor p O Λ
  have hψeq : ∀ r, ψ r = ψ₀ r := by
    intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul a l => rw [hψ, hψ₀]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hsurj : Function.Surjective ψ := fun r => ⟨φ₀ r, by rw [hψeq, hφψ]⟩
  have calc₁ := fun (e e' e'' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) =>
    GlobalTheory.T.frame_matrix_composition_unique p O Λ N h e e' e''
  obtain ⟨F, hF⟩ := GlobalTheory.T.exists_matrix_of_intertwiner p O Λ N h (rhoTA D) D.ρM eT eM D.F hT hM (fun l => D.F_act l)
  obtain ⟨G, hGm⟩ := GlobalTheory.T.exists_matrix_of_intertwiner p O Λ N h D.ρM (rhoTA D) eM eT D.G hM hT hG
  obtain ⟨Ψ, hΨm⟩ := GlobalTheory.T.exists_matrix_of_intertwiner p O Λ N h (fun l => (D.ρM l).map (phiInv p O)) D.ρM tM eM D.Ψ
    htM hM hΨ
  obtain ⟨Ψ', hΨ'm⟩ := GlobalTheory.T.exists_matrix_of_intertwiner p O Λ N h D.ρM (fun l => (D.ρM l).map (phiInv p O)) eM tM D.Ψ'
    hM htM hΨ'
  have hFψ := GlobalTheory.T.frame_transition_psi_matrix p O Λ N h ψ eT eM eT tM D.F F hsurj hTw htw hF
  refine ⟨⟨eT, eM, F, G, Ψ, Ψ', hT, hM, hF, hGm, ?_, ?_, ?_, ?_⟩⟩
  · have h1 := (calc₁ eT eM eT).1 _ _ _ _ hF hGm
    rw [D.G_mul_F] at h1
    exact (calc₁ eT eT eT).2.1 _ _ _ h1 ((calc₁ eT eT eT).2.2 (mu ε))
  · have h1 := (calc₁ eM eT eM).1 _ _ _ _ hGm hF
    rw [hFG] at h1
    exact (calc₁ eM eM eM).2.1 _ _ _ h1 ((calc₁ eM eM eM).2.2 (mu ε))
  · have h1 := (calc₁ eT tM eM).1 _ _ _ _ hFψ hΨm
    rw [← D.F_eq] at h1
    exact (calc₁ eT eM eM).2.1 _ _ _ hF h1
  · have h1 := (calc₁ eM tM eM).1 _ _ _ _ hΨ'm hΨm
    rw [D.Ψ_mul] at h1
    exact (calc₁ eM eM eM).2.1 _ _ _ h1 ((calc₁ eM eM eM).2.2 (xi ε))

end GlobalTheory.DetInv
end
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_frame_comparison_unit : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (N h : ℕ) , h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → Nonempty (FreeForm D N ψ) := by
  atlas_forward_decl GlobalTheory.DetInv.exists_freeForm
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory

theorem detLine_coord : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h N : ℕ) (ρ : Λ → Matrix (Fin h) (Fin h) O) (σ : Λ →+* O) (q : eig C ρ σ ≃ₗ[C] (Fin N → C)), (∀ x, x ∈ quotLattice C ρ σ ↔ ∀ i, q x i ∈ (algebraMap O C).range) → ∃ δ : detLine C ρ σ N ≃ₗ[C] C, (∀ x : Fin N → eig C ρ σ, δ (exteriorPower.ιMulti C N x) = (Matrix.of fun i => q (x i)).det) ∧ ∀ w, w ∈ detLattice C ρ σ N ↔ δ w ∈ (algebraMap O C).range := by
  intro C _ O _ _ Λ _ h N ρ σ q hq
  let b : Module.Basis (Fin N) C (eig C ρ σ) := Module.Basis.ofEquivFun q
  have hbq : ∀ v i, b.repr v i = q v i := fun v i => by
    simp only [b, Module.Basis.ofEquivFun_repr_apply]
  let f : detLine C ρ σ N →ₗ[C] C := exteriorPower.alternatingMapLinearEquiv b.det
  have hdet : ∀ x : Fin N → eig C ρ σ, f (exteriorPower.ιMulti C N x) = b.det x := fun x =>
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _
  have hfx : ∀ x : Fin N → eig C ρ σ,
      f (exteriorPower.ιMulti C N x) = (Matrix.of fun i => q (x i)).det := by
    intro x
    rw [hdet, Module.Basis.det_apply, ← Matrix.det_transpose]
    congr 1
  have hfb : f (exteriorPower.ιMulti C N b) = 1 := by rw [hdet, Module.Basis.det_self]
  have hall : ∀ w, f w • exteriorPower.ιMulti C N b = w := by
    intro w
    have hw : w ∈ Submodule.span C (exteriorPower.ιMulti C N ''
        {a : Fin N → eig C ρ σ | Set.range a ⊆ Set.range b}) := by
      rw [exteriorPower.ιMulti_span_of_span C N (eig C ρ σ) b.span_eq]; trivial
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      have hv : ∀ i, ∃ j, b j = a i := fun i => ha ⟨i, rfl⟩
      choose v hv using hv
      have hav : a = b ∘ v := funext fun i => (hv i).symm
      subst hav
      rw [hdet]
      by_cases hinj : Function.Injective v
      · let e : Equiv.Perm (Fin N) := Equiv.ofBijective v (Finite.injective_iff_bijective.mp hinj)
        have hve : (⇑b ∘ v) = ⇑b ∘ ⇑e := rfl
        rw [hve, AlternatingMap.map_perm, AlternatingMap.map_perm, Module.Basis.det_self]
        simp
      · rw [AlternatingMap.map_eq_zero_of_not_injective _ _ (fun h => hinj (Function.Injective.of_comp h)),
          AlternatingMap.map_eq_zero_of_not_injective _ _ (fun h => hinj (Function.Injective.of_comp h)),
          zero_smul]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, add_smul, hx, hy]
    | smul a x _ hx => rw [map_smul, smul_eq_mul, mul_smul, hx]
  let δ : detLine C ρ σ N ≃ₗ[C] C :=
    { f with
      invFun := fun c => c • exteriorPower.ιMulti C N b
      left_inv := hall
      right_inv := fun c => by
        show f (c • exteriorPower.ιMulti C N b) = c
        rw [map_smul, hfb, smul_eq_mul, mul_one] }
  refine ⟨δ, hfx, fun w => ⟨fun hw => ?_, fun hw => ?_⟩⟩
  · induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      have hy' : ∀ i j, ∃ o : O, algebraMap O C o = q (y i) j := fun i j => (hq (y i)).1 (hy i) j
      choose g hg using hy'
      show f _ ∈ _
      rw [hfx]
      refine ⟨(Matrix.of g).det, ?_⟩
      rw [RingHom.map_det]
      congr 1
      ext i j
      simp [RingHom.mapMatrix_apply, hg]
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      rw [map_add]; exact Subring.add_mem _ hx hy
    | smul a x _ hx =>
      rw [← algebraMap_smul C a x, map_smul, smul_eq_mul]
      exact Subring.mul_mem _ ⟨a, rfl⟩ hx
  · obtain ⟨o, ho⟩ := hw
    have hb : ∀ i, b i ∈ quotLattice C ρ σ := by
      intro i
      refine (hq (b i)).2 fun j => ?_
      rw [← hbq, Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩
    have hw' : w = o • exteriorPower.ιMulti C N b := by
      rw [← algebraMap_smul C o, ho]
      exact (hall w).symm
    rw [hw']
    exact Submodule.smul_mem _ o (Submodule.subset_span ⟨b, hb, rfl⟩)

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_det_line_coordinate_iso : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h N : ℕ) (ρ : Λ → Matrix (Fin h) (Fin h) O) (σ : Λ →+* O) (q : eig C ρ σ ≃ₗ[C] (Fin N → C)), (∀ x, x ∈ quotLattice C ρ σ ↔ ∀ i, q x i ∈ (algebraMap O C).range) → ∃ δ : detLine C ρ σ N ≃ₗ[C] C, (∀ x : Fin N → eig C ρ σ, δ (exteriorPower.ιMulti C N x) = (Matrix.of fun i => q (x i)).det) ∧ ∀ w, w ∈ detLattice C ρ σ N ↔ δ w ∈ (algebraMap O C).range := by
  atlas_forward_decl GlobalTheory.detLine_coord
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem scalar_of_lattice_image : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (V W : Type) [AddCommGroup V] [Module C V] [AddCommGroup W] [Module C W] (LV : Set V) (LW : Set W) (δ : V ≃ₗ[C] C) (δ' : W ≃ₗ[C] C) (ι : V →ₗ[C] W) (lam : C), v.Integers O → (∀ w, w ∈ LV ↔ δ w ∈ (algebraMap O C).range) → (∀ w, w ∈ LW ↔ δ' w ∈ (algebraMap O C).range) → ι '' LV = (fun w => lam • w) '' LW → ∃ l₀ : C, v l₀ = v lam ∧ ∀ w, δ' (ι w) = l₀ * δ w := by
  intro C _ v O _ _ V W _ _ _ _ LV LW δ δ' ι lam hO hV hW himg
  have hdec : ∀ u : V, u = (δ u) • δ.symm 1 := by
    intro u; apply δ.injective; simp
  refine ⟨δ' (ι (δ.symm 1)), ?_, ?_⟩
  · have h1 : δ.symm 1 ∈ LV := by
      rw [hV]; exact ⟨1, by simp⟩
    have h2 : ι (δ.symm 1) ∈ (fun w => lam • w) '' LW := himg ▸ Set.mem_image_of_mem ι h1
    obtain ⟨w', hw', hw'eq⟩ := h2
    rw [hW] at hw'
    obtain ⟨o, ho⟩ := hw'
    have e1 : δ' (ι (δ.symm 1)) = lam * algebraMap O C o := by
      rw [← hw'eq]; simp only [map_smul, smul_eq_mul, ho]
    have h3 : δ'.symm 1 ∈ LW := by
      rw [hW]; exact ⟨1, by simp⟩
    have h4 : lam • δ'.symm 1 ∈ ι '' LV := himg ▸ ⟨_, h3, rfl⟩
    obtain ⟨u, hu, hueq⟩ := h4
    rw [hV] at hu
    obtain ⟨o', ho'⟩ := hu
    have e2 : lam = δ' (ι (δ.symm 1)) * algebraMap O C o' := by
      have h5 : δ' (ι u) = lam := by rw [hueq]; simp
      rw [← h5, hdec u, map_smul, map_smul, smul_eq_mul, ← ho']
      ring
    apply le_antisymm
    · rw [e1, map_mul]; exact mul_le_of_le_one_right zero_le' (hO.map_le_one o)
    · rw [e2, map_mul]; exact mul_le_of_le_one_right zero_le' (hO.map_le_one o')
  · intro w
    calc δ' (ι w) = δ' (ι ((δ w) • δ.symm 1)) := by rw [← hdec w]
      _ = δ' (ι (δ.symm 1)) * δ w := by rw [map_smul, map_smul, smul_eq_mul, mul_comm]

end GlobalTheory.DetInv
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_scaling_valuation_eq : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (V W : Type) [AddCommGroup V] [Module C V] [AddCommGroup W] [Module C W] (LV : Set V) (LW : Set W) (δ : V ≃ₗ[C] C) (δ' : W ≃ₗ[C] C) (ι : V →ₗ[C] W) (lam : C), v.Integers O → (∀ w, w ∈ LV ↔ δ w ∈ (algebraMap O C).range) → (∀ w, w ∈ LW ↔ δ' w ∈ (algebraMap O C).range) → ι '' LV = (fun w => lam • w) '' LW → ∃ l₀ : C, v l₀ = v lam ∧ ∀ w, δ' (ι w) = l₀ * δ w := by
  atlas_forward_decl GlobalTheory.DetInv.scalar_of_lattice_image
end

section
section
noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem iotaScalar_of_freeForm : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (N h : ℕ) , h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (ψ : RL p O Λ →+* RL p O Λ) (Φ : FreeForm D N ψ) (τ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta τ f → ∀ ι (lam : C), IsIota C D τ N ι → ι '' (detLattice C (actT D) τ N : Set (detLine C (actT D) τ N)) = (fun w => lam • w) '' (detLattice C (actH D) τ N : Set (detLine C (actH D) τ N)) → ∃ l₀ : C, v l₀ = v lam ∧ IotaScalar (Φ.F.map ((algebraMap O C).comp f)) (Φ.G.map ((algebraMap O C).comp f)) (D.lieRank τ) l₀ := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ N h hh D ψ Φ τ f hf ι lam hι hlat
  obtain ⟨-, -, -, hθs, -, -, -⟩ := GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := hθs y
    exact ⟨a ⊗ₜ 1, by rw [hf]; simp⟩
  obtain ⟨⟨-, hTtop, hTrk⟩, ⟨-, hHtop, hHrk⟩⟩ := GlobalTheory.T.sandwich_datum_eigen_multiplicity p C v O hv ε hε Λ N h hh D
  obtain ⟨πT, hπT⟩ := GlobalTheory.T.exists_theta_projection p O C Λ N h τ f Φ.eT hf
  obtain ⟨πH, hπH⟩ := GlobalTheory.T.exists_theta_projection p O C Λ N h τ f Φ.eM hf
  obtain ⟨qT, hqT, hqTL⟩ : ∃ q : eig C (actT D) τ ≃ₗ[C] (Fin N → C), (∀ x, q x = πT x) ∧
      ∀ x, x ∈ quotLattice C (actT D) τ ↔ ∀ i, q x i ∈ (algebraMap O C).range :=
    GlobalTheory.T.theta_projection_surjective_eigen p O C Λ N h τ f (rhoTA D) Φ.eT πT hinj hθs hfs hf Φ.frameT hπT hTtop (hTrk τ)
  obtain ⟨qH, hqH, hqHL⟩ : ∃ q : eig C (actH D) τ ≃ₗ[C] (Fin N → C), (∀ x, q x = πH x) ∧
      ∀ x, x ∈ quotLattice C (actH D) τ ↔ ∀ i, q x i ∈ (algebraMap O C).range :=
    GlobalTheory.T.theta_projection_surjective_eigen p O C Λ N h τ f D.ρM Φ.eM πH hinj hθs hfs hf Φ.frameM hπH hHtop (hHrk τ)
  obtain ⟨δT, hδT, hδTL⟩ := GlobalTheory.T.exists_det_line_coordinate_iso C O Λ h N (actT D) τ qT hqTL
  obtain ⟨δH, hδH, hδHL⟩ := GlobalTheory.T.exists_det_line_coordinate_iso C O Λ h N (actH D) τ qH hqHL
  obtain ⟨l₀, hl₀v, hl₀⟩ := GlobalTheory.T.lattice_scaling_valuation_eq C v O _ _
    (detLattice C (actT D) τ N : Set (detLine C (actT D) τ N))
    (detLattice C (actH D) τ N : Set (detLine C (actH D) τ N)) δT δH ι lam hv
    (fun w => hδTL w) (fun w => hδHL w) hlat
  obtain ⟨-, -, hGρ, -, -⟩ := GlobalTheory.T.sandwich_datum_scalar_action p C v O hv ε hε Λ h D
  have hG : ∀ l, D.G.map (WittVector.fontaineTheta O p) * actH D l =
      actT D l * D.G.map (WittVector.fontaineTheta O p) := by
    intro l
    have e := congrArg (fun M => M.map (WittVector.fontaineTheta O p)) (hGρ l)
    simpa [Matrix.map_mul, actH, actT, rhoTA, Matrix.map_map, padicToO] using e
  have hF : ∀ l, D.F.map (WittVector.fontaineTheta O p) * actT D l =
      actH D l * D.F.map (WittVector.fontaineTheta O p) := by
    intro l
    have e := congrArg (fun M => M.map (WittVector.fontaineTheta O p)) (D.F_act l)
    simpa [Matrix.map_mul, actH, actT, Matrix.map_map, padicToO] using e
  have hbmem : ∀ y : eig C (actH D) τ, bC C D y ∈ eig C (actT D) τ := by
    intro y
    apply (GlobalTheory.T.intertwiner_maps_eigenspaces C O Λ h (actH D) (actT D) _ hG).1 τ
    exact ⟨y, y.2, rfl⟩
  have hamem : ∀ x : eig C (actT D) τ, alC C D x ∈ eig C (actH D) τ := by
    intro x
    apply (GlobalTheory.T.intertwiner_maps_eigenspaces C O Λ h (actT D) (actH D) _ hF).1 τ
    exact ⟨x, x.2, rfl⟩
  refine ⟨l₀, hl₀v, ?_⟩
  intro X Y hX hY
  have h1 : ∀ i : Fin N, (i : ℕ) < D.lieRank τ →
      ((qT.symm (X i) : eig C (actT D) τ) : Fin h → C) = bC C D (qH.symm (Y i)) := by
    intro i hi
    have hz : qT ⟨bC C D (qH.symm (Y i)), hbmem _⟩ = X i := by
      rw [hqT]
      show πT (redC C D.G (qH.symm (Y i))) = X i
      rw [GlobalTheory.T.theta_projection_intertwining p O C Λ N h f Φ.eM Φ.eT πH πT D.G Φ.G hπH hπT Φ.matG, ← hqH,
        qH.apply_symm_apply, hX i hi]
    rw [← hz, qT.symm_apply_apply]
  have h2 : ∀ i : Fin N, D.lieRank τ ≤ (i : ℕ) →
      ((qH.symm (Y i) : eig C (actH D) τ) : Fin h → C) = alC C D (qT.symm (X i)) := by
    intro i hi
    have hz : qH ⟨alC C D (qT.symm (X i)), hamem _⟩ = Y i := by
      rw [hqH]
      show πH (redC C D.F (qT.symm (X i))) = Y i
      rw [GlobalTheory.T.theta_projection_intertwining p O C Λ N h f Φ.eT Φ.eM πT πH D.F Φ.F hπT hπH Φ.matF, ← hqT,
        qT.apply_symm_apply, hY i hi]
    rw [← hz, qH.symm_apply_apply]
  have e := hl₀ (exteriorPower.ιMulti C N fun i => qT.symm (X i))
  rw [hι _ _ h1 h2, hδH, hδT] at e
  simpa using e

end GlobalTheory.DetInv
end
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_valuation_order_sum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (N h : ℕ) , h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (ψ : RL p O Λ →+* RL p O Λ) (Φ : FreeForm D N ψ) (τ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta τ f → ∀ ι (lam : C), IsIota C D τ N ι → ι '' (detLattice C (actT D) τ N : Set (detLine C (actT D) τ N)) = (fun w => lam • w) '' (detLattice C (actH D) τ N : Set (detLine C (actH D) τ N)) → ∃ l₀ : C, v l₀ = v lam ∧ IotaScalar (Φ.F.map ((algebraMap O C).comp f)) (Φ.G.map ((algebraMap O C).comp f)) (D.lieRank τ) l₀ := by
  atlas_forward_decl GlobalTheory.DetInv.iotaScalar_of_freeForm
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem eq_of_isTheta_of_isTheta {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]
    {σ : Λ →+* O} {f g : RL p O Λ →+* O} (hf : IsTheta σ f) (hg : IsTheta σ g) : f = g := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a l => rw [hf, hg]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem exists_sep_theta : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ τ : Λ →+* O, ∃ s : RL p O Λ, (∀ f, IsTheta τ f → f s ≠ 0) ∧ (∀ σ f, σ ≠ τ → IsTheta σ f → f s = 0) ∧ ∀ f, IsTheta τ f → ∀ r, f r = 0 → (inA (xi ε) : RL p O Λ) ∣ s * r := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ τ
  haveI : NoZeroDivisors O := hv.hom_inj.noZeroDivisors _ (map_zero _) (map_mul _)
  haveI : Nontrivial O := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact (Fact.out : ¬IsUnit (p : O)) (isUnit_of_subsingleton _)
  haveI : Finite (Λ →+* O) := (GlobalTheory.card_ringHom_to_integers_eq_finrank p C v O hv Λ).1
  letI : Fintype (Λ →+* O) := Fintype.ofFinite _
  have hsurj := (GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε).2.2.2.1
  have hl : ∀ σ : Λ →+* O, σ ≠ τ → ∃ l : Λ, σ l ≠ τ l := by
    intro σ h
    by_contra hc
    push_neg at hc
    exact h (RingHom.ext hc)
  classical
  choose! l hl using hl
  choose a ha using fun σ : Λ →+* O => hsurj (σ (l σ))
  let S : Finset (Λ →+* O) := Finset.univ.filter (· ≠ τ)
  let fac : (Λ →+* O) → RL p O Λ := fun σ => (1 : Ainf p O) ⊗ₜ[ℤ_[p]] l σ - a σ ⊗ₜ[ℤ_[p]] (1 : Λ)
  have hfac : ∀ (ρ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta ρ f → ∀ σ, f (fac σ) = ρ (l σ) - σ (l σ) := by
    intro ρ f hf σ
    simp only [fac]
    rw [map_sub, hf, hf, ha, map_one, map_one, one_mul, mul_one]
  refine ⟨∏ σ ∈ S, fac σ, ?_, ?_, ?_⟩
  · intro f hf
    rw [map_prod]
    refine Finset.prod_ne_zero_iff.mpr fun σ hσ => ?_
    rw [hfac τ f hf σ]
    have hστ : σ ≠ τ := (Finset.mem_filter.mp hσ).2
    exact sub_ne_zero.mpr (hl σ hστ).symm
  · intro σ f hστ hf
    rw [map_prod]
    refine Finset.prod_eq_zero (i := σ) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hστ⟩) ?_
    rw [hfac σ f hf σ, sub_self]
  · intro f hf r hr
    apply GlobalTheory.T.relative_lattice_element_property p C v O hv ε hε Λ
    intro σ g hg
    by_cases hστ : σ = τ
    · subst hστ
      rw [eq_of_isTheta_of_isTheta hg hf, map_mul, hr, mul_zero]
    · rw [map_mul, map_prod]
      rw [Finset.prod_eq_zero (i := σ) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hστ⟩)
        (by rw [hfac σ g hg σ, sub_self]), zero_mul]

end GlobalTheory.DetInv
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_embedding_ring_hom_property : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ τ : Λ →+* O, ∃ s : RL p O Λ, (∀ f, IsTheta τ f → f s ≠ 0) ∧ (∀ σ f, σ ≠ τ → IsTheta σ f → f s = 0) ∧ ∀ f, IsTheta τ f → ∀ r, f r = 0 → (inA (xi ε) : RL p O Λ) ∣ s * r := by
  atlas_forward_decl GlobalTheory.DetInv.exists_sep_theta
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv.ScalarEx

theorem det_add_rows {C : Type} [Field C] {N : ℕ} (S : Fin N → Prop) [DecidablePred S]
    (W : Submodule C (Fin N → C)) (hW : Module.finrank C W = Fintype.card {i // S i})
    (r s : Fin N → Fin N → C) (hr : ∀ i, S i → r i ∈ W) (hd0 : ∀ i, S i → s i = r i)
    (hd : ∀ i, ¬ S i → s i - r i ∈ W) :
    (Matrix.of s).det = (Matrix.of r).det := by
  classical
  by_cases hli : LinearIndependent C (fun i : {i // S i} => r i)
  · have hspan : Submodule.span C (Set.range (fun i : {i // S i} => r i)) = W := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hr i i.2
      · rw [finrank_span_eq_card hli, hW]
    have hc : ∀ j, ∃ c : {i // S i} → C, (S j → c = 0) ∧ ∑ i, c i • r i = s j - r j := by
      intro j
      by_cases hj : S j
      · exact ⟨0, fun _ => rfl, by simp [hd0 j hj]⟩
      · have h1 := hd j hj
        rw [← hspan] at h1
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 h1
        exact ⟨c, fun h => absurd h hj, hc⟩
    choose c hc0 hc using hc
    let Q : Matrix {i // S i} (Fin N) C := Matrix.of fun i l => if i.1 = l then 1 else 0
    have hQ : ∀ {κ : Type} (M : Matrix (Fin N) κ C) (i : {i // S i}) (k : κ),
        (Q * M) i k = M i k := by
      intro κ M i k
      simp [Q, Matrix.mul_apply]
    have h1 : Matrix.of s = (1 + Matrix.of c * Q) * Matrix.of r := by
      ext j k
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.add_apply, Matrix.mul_apply]
      have h2 := congrFun (hc j) k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h2
      simp only [hQ, Matrix.of_apply, h2]
      ring
    have h2 : Q * Matrix.of c = 0 := by
      ext i k
      rw [hQ]
      simp [hc0 i.1 i.2]
    rw [h1, Matrix.det_mul, Matrix.det_one_add_mul_comm, h2]
    simp
  · have h1 : (Matrix.of r).det = 0 := by
      by_contra h
      exact hli ((Matrix.linearIndependent_rows_of_det_ne_zero h).comp _ Subtype.val_injective)
    have h2 : (Matrix.of s).det = 0 := by
      by_contra h
      have h3 := (Matrix.linearIndependent_rows_of_det_ne_zero h).comp _
        (Subtype.val_injective (p := S))
      apply hli
      have h4 : (fun i : {i // S i} => r i) = (fun i => Matrix.of s i) ∘ Subtype.val :=
        funext fun i => (hd0 i.1 i.2).symm
      rw [h4]
      exact h3
    rw [h1, h2]

theorem exists_ginv {C V : Type} [Field C] [AddCommGroup V] [Module C V] (f : V →ₗ[C] V) :
    ∃ g : V →ₗ[C] V, ∀ z, f (g (f z)) = f z := by
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective f.rangeRestrict
    (LinearMap.range_rangeRestrict f)
  obtain ⟨t, ht⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range f).subtype
    (Submodule.ker_subtype _)
  refine ⟨s ∘ₗ t, fun z => ?_⟩
  have h1 : t (f z) = f.rangeRestrict z := LinearMap.congr_fun ht (f.rangeRestrict z)
  have h2 := congrArg Subtype.val (LinearMap.congr_fun hs (f.rangeRestrict z))
  rw [LinearMap.comp_apply, h1]
  exact h2

theorem card_lt {N a : ℕ} (h : a ≤ N) : Fintype.card {i : Fin N // (i : ℕ) < a} = a := by
  rw [Fintype.card_subtype, Fin.card_filter_val_lt]
  exact min_eq_right h

theorem exists_iotaScalar (C : Type) [Field C] (N : ℕ) (α β : Matrix (Fin N) (Fin N) C)
    (hab : α * β = 0) (hba : β * α = 0) (hex : ∀ x, α *ᵥ x = 0 → ∃ y, x = β *ᵥ y) :
    ∃ lam : C, lam ≠ 0 ∧ IotaScalar α β β.rank lam := by
  classical
  set U : Submodule C (Fin N → C) := LinearMap.range β.mulVecLin with hUdef
  have hU : Module.finrank C U = β.rank := rfl
  have haN : β.rank ≤ N := by simpa using Matrix.rank_le_width β
  have hUker : ∀ z, z ∈ U ↔ α *ᵥ z = 0 := by
    intro z
    constructor
    · rintro ⟨y, rfl⟩
      simp [Matrix.mulVec_mulVec, hab]
    · intro h
      obtain ⟨y, rfl⟩ := hex z h
      exact ⟨y, rfl⟩
  have hker : LinearMap.ker α.mulVecLin = U := by
    ext z
    rw [hUker]; simp
  have hkerβ : LinearMap.range α.mulVecLin = LinearMap.ker β.mulVecLin := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨y, rfl⟩
      simp [Matrix.mulVec_mulVec, hba]
    · have h1 := LinearMap.finrank_range_add_finrank_ker α.mulVecLin
      have h2 := LinearMap.finrank_range_add_finrank_ker β.mulVecLin
      rw [hker] at h1
      rw [← hUdef] at h2
      omega
  obtain ⟨F, hF⟩ := Submodule.exists_isCompl U
  have hFr : Module.finrank C F = Fintype.card {i : Fin N // ¬ (i : ℕ) < β.rank} := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hF
    rw [Fintype.card_subtype_compl, card_lt haN]
    simp only [Module.finrank_fintype_fun_eq_card] at h1
    omega
  obtain ⟨q, hqF, hqU⟩ : ∃ q : (Fin N → C) →ₗ[C] (Fin N → C),
      (∀ z, q z ∈ F) ∧ ∀ z, z - q z ∈ U := by
    refine ⟨F.subtype ∘ₗ F.projectionOnto U hF.symm, fun z => Subtype.prop _, fun z => ?_⟩
    refine (Submodule.ker_projectionOnto hF.symm).le ?_
    rw [LinearMap.mem_ker, map_sub, LinearMap.comp_apply, Submodule.subtype_apply,
      Submodule.projectionOnto_apply_left, sub_self]
  obtain ⟨g, hg⟩ := exists_ginv α.mulVecLin
  simp only [Matrix.mulVecLin_apply] at hg
  let Θ : (Fin N → C) →ₗ[C] (Fin N → C) := β.mulVecLin + q ∘ₗ g
  have hΘ : ∀ z, Θ z = β *ᵥ z + q (g z) := fun z => rfl
  have hq : ∀ z, α *ᵥ q z = α *ᵥ z := by
    intro z
    have h1 := (hUker _).1 (hqU z)
    rw [Matrix.mulVec_sub, sub_eq_zero] at h1
    exact h1.symm
  have hΘα : ∀ z, Θ (α *ᵥ z) = q (g (α *ᵥ z)) := by
    intro z
    rw [hΘ, Matrix.mulVec_mulVec, hba, Matrix.zero_mulVec, zero_add]
  let M := LinearMap.toMatrix' Θ
  have hM : ∀ z, M *ᵥ z = Θ z := fun z => LinearMap.toMatrix'_mulVec Θ z
  have hdet : M.det ≠ 0 := by
    intro h
    obtain ⟨z, hz, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    apply hz
    rw [hM] at h0
    have h1 : β *ᵥ z ∈ F := by
      have h2 : β *ᵥ z = - q (g z) := eq_neg_of_add_eq_zero_left (by rw [← hΘ, h0])
      rw [h2]; exact F.neg_mem (hqF _)
    have h2 : β *ᵥ z = 0 := (Submodule.disjoint_def.1 hF.disjoint) _ ⟨z, rfl⟩ h1
    have h3 : z ∈ LinearMap.range α.mulVecLin := by rw [hkerβ]; exact h2
    obtain ⟨w, rfl⟩ := h3
    simp only [Matrix.mulVecLin_apply] at h0 ⊢
    rw [← hg, ← hq, ← hΘα, h0, Matrix.mulVec_zero]
  refine ⟨M.det⁻¹, inv_ne_zero hdet, fun x y hx hy => ?_⟩
  let m : Fin N → Fin N → C := fun i => if (i : ℕ) < β.rank then x i else Θ (y i)
  have h1 : (Matrix.of x).det = (Matrix.of m).det := by
    refine det_add_rows (fun i => (i : ℕ) < β.rank) U (by rw [card_lt haN, hU]) m x ?_ ?_ ?_
    · intro i hi
      simp only [m, if_pos hi]
      exact ⟨y i, (hx i hi).symm⟩
    · intro i hi
      simp only [m, if_pos hi]
    · intro i hi
      simp only [m, if_neg hi]
      rw [hUker, hy i (not_lt.1 hi), hΘα, Matrix.mulVec_sub, hq, hg, sub_self]
  have h2 : (Matrix.of fun i => Θ (y i)).det = (Matrix.of m).det := by
    refine det_add_rows (fun i => ¬ (i : ℕ) < β.rank) F hFr m _ ?_ ?_ ?_
    · intro i hi
      simp only [m, if_neg hi]
      rw [hy i (not_lt.1 hi), hΘα]
      exact hqF _
    · intro i hi
      simp only [m, if_neg hi]
    · intro i hi
      have hi' := not_not.1 hi
      simp only [m, if_pos hi']
      rw [hΘ, hx i hi', add_sub_cancel_left]
      exact hqF _
  have h3 : (Matrix.of fun i => Θ (y i)) = Matrix.of y * Mᵀ := by
    ext i k
    rw [Matrix.of_apply, ← hM]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  rw [h3, Matrix.det_mul, Matrix.det_transpose, ← h1] at h2
  rw [← h2]
  field_simp

end GlobalTheory.DetInv.ScalarEx
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iota_scalar_exact_pair : ∀ (C : Type) [Field C] (N : ℕ) (α β : Matrix (Fin N) (Fin N) C), α * β = 0 → β * α = 0 → (∀ x, α *ᵥ x = 0 → ∃ y, x = β *ᵥ y) → ∃ lam : C, lam ≠ 0 ∧ IotaScalar α β β.rank lam := by
  atlas_forward_decl GlobalTheory.DetInv.ScalarEx.exists_iotaScalar
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem lead_det_all : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (N h : ℕ) , h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (ψ : RL p O Λ →+* RL p O Λ) (Φ : FreeForm D N ψ) (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → D.lieRank σ ≤ N ∧ ∃ c : C, c ≠ 0 ∧ Lead ((algebraMap O C).comp f) (inA (xi ε)) Φ.F.det (D.lieRank σ) c := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ N h hh D ψ Φ σ f hf
  obtain ⟨-, -, hker, hsurj, hnu, hxi, -⟩ := GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε
  have hA : ∀ a : Ainf p O, f (inA a) = WittVector.fontaineTheta O p a := by
    intro a
    show f (algebraMap (Ainf p O) (RL p O Λ) a) = _
    rw [Algebra.TensorProduct.algebraMap_apply, hf]
    simp
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  set g : RL p O Λ →+* C := (algebraMap O C).comp f with hg
  have hgf : ∀ r, g r = algebraMap O C (f r) := fun r => rfl
  have hf0 : ∀ r, g r = 0 → f r = 0 := fun r hr => hinj (by rw [← hgf, hr, map_zero])
  have hgxi : g (inA (xi ε)) = 0 := by
    rw [hgf, hA]
    have : xi ε ∈ RingHom.ker (WittVector.fontaineTheta O p) := by
      rw [hker]; exact Ideal.subset_span rfl
    rw [RingHom.mem_ker.mp this, map_zero]
  have hgnu : g (inA (nu ε)) ≠ 0 := by
    intro h0; apply hnu; rw [← hA]; exact hf0 _ h0
  have hfs : ∀ o : O, ∃ r, f r = o := by
    intro o; obtain ⟨a, rfl⟩ := hsurj o; exact ⟨inA a, hA a⟩
  have hmu : (inA (mu ε) : RL p O Λ) = (inA (xi ε) : RL p O Λ) * inA (nu ε) := by
    rw [← map_mul, xi_mul_nu]
  have hFG : Φ.F * Φ.G = ((inA (xi ε) : RL p O Λ) * inA (nu ε)) • (1 : Matrix (Fin N) (Fin N) (RL p O Λ)) := by
    rw [Φ.F_mul_G, hmu]
  have hGF : Φ.G * Φ.F = ((inA (xi ε) : RL p O Λ) * inA (nu ε)) • (1 : Matrix (Fin N) (Fin N) (RL p O Λ)) := by
    rw [Φ.G_mul_F, hmu]
  have hαβ : Φ.F.map g * Φ.G.map g = 0 := by
    rw [← Matrix.map_mul, hFG]
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_mul, hgxi, zero_mul, zero_mul,
      Matrix.zero_apply]
  have hβα : Φ.G.map g * Φ.F.map g = 0 := by
    rw [← Matrix.map_mul, hGF]
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_mul, hgxi, zero_mul, zero_mul,
      Matrix.zero_apply]
  have hξreg : (inA (xi ε) : RL p O Λ) ∈ nonZeroDivisors (RL p O Λ) :=
    GlobalTheory.T.ainf_element_theta_compatible p C v O hv ε hε Λ (xi ε) hxi
  have hquot : ∀ c : C, ∃ s t : RL p O Λ, g s ≠ 0 ∧ c * g s = g t := by
    intro c
    by_cases hc : v c ≤ 1
    · obtain ⟨o, ho⟩ := hv.exists_of_le_one hc
      obtain ⟨t, ht⟩ := hfs o
      exact ⟨1, t, by simp, by rw [map_one, mul_one, hgf, ht, ho]⟩
    · by_cases hc0 : c = 0
      · exact ⟨1, 0, by simp, by simp [hc0]⟩
      have h1 : v c⁻¹ ≤ 1 := by
        rw [map_inv₀]
        exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp hc))
      obtain ⟨o, ho⟩ := hv.exists_of_le_one h1
      obtain ⟨s, hs⟩ := hfs o
      refine ⟨s, 1, ?_, ?_⟩
      · rw [hgf, hs, ho]; exact inv_ne_zero hc0
      · rw [hgf, hs, ho, map_one, mul_inv_cancel₀ hc0]
  have hK : ∃ s : RL p O Λ, g s ≠ 0 ∧ ∀ r, g r = 0 → (inA (xi ε) : RL p O Λ) ∣ s * r := by
    obtain ⟨s, hs1, -, hs3⟩ := GlobalTheory.T.dvr_embedding_ring_hom_property p C v O hv ε hε Λ σ
    refine ⟨s, ?_, fun r hr => hs3 f hf r (hf0 r hr)⟩
    intro h0; exact hs1 f hf (hf0 s h0)
  have hexact : ∀ x : Fin N → C, Φ.F.map g *ᵥ x = 0 → ∃ y, x = Φ.G.map g *ᵥ y :=
    ker_map_subset_im_map (RL p O Λ) C g (inA (xi ε) : RL p O Λ) (inA (nu ε)) N Φ.F Φ.G hξreg hgnu hquot hK hGF
  obtain ⟨lam, hlam, hiota⟩ := GlobalTheory.T.exists_iota_scalar_exact_pair C N (Φ.F.map g) (Φ.G.map g) hαβ hβα hexact
  have hlead := GlobalTheory.LeadDet.lead_det (RL p O Λ) C g (inA (xi ε) : RL p O Λ) (inA (nu ε)) N Φ.F Φ.G lam hFG hiota
  have hrank : (Φ.G.map g).rank = D.lieRank σ :=
    GlobalTheory.T.determinant_valuation_order p C v O hv ε hε Λ N h hh D ψ Φ σ f hf
  rw [hrank] at hlead
  refine ⟨?_, lam * g (inA (nu ε)) ^ D.lieRank σ, mul_ne_zero hlam (pow_ne_zero _ hgnu), hlead⟩
  rw [← hrank]
  exact Matrix.rank_le_width _

end GlobalTheory.DetInv
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_valuation_iota_scalar : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (N h : ℕ) , h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (ψ : RL p O Λ →+* RL p O Λ) (Φ : FreeForm D N ψ) (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → D.lieRank σ ≤ N ∧ ∃ c : C, c ≠ 0 ∧ Lead ((algebraMap O C).comp f) (inA (xi ε)) Φ.F.det (D.lieRank σ) c := by
  atlas_forward_decl GlobalTheory.DetInv.lead_det_all
end

section
section
noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem isTheta_unique {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]
    {σ : Λ →+* O} {f f' : RL p O Λ →+* O} (hf : IsTheta σ f) (hf' : IsTheta σ f') : f = f' := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a l => rw [hf, hf']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem exists_detElt_lieRank : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (τ : Λ →+* O) ι (lam : C), IsIota C D τ N ι → ι '' (detLattice C (actT D) τ N : Set (detLine C (actT D) τ N)) = (fun w => lam • w) '' (detLattice C (actH D) τ N : Set (detLine C (actH D) τ N)) → ∃ (Δ : RL p O Λ) (c : (Λ →+* O) → C), IsDetElt ε ψ N Δ ∧ HasOrders C ε N Δ D.lieRank c ∧ v (c τ) = v lam * v (algebraMap O C (WittVector.fontaineTheta O p (nu ε))) ^ D.lieRank τ := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ ψ hψ N h hh D τ ι lam hι hlat
  classical
  obtain ⟨Φ⟩ := GlobalTheory.T.determinant_frame_comparison_unit p C v O hv ε hε Λ N h hh D ψ hψ
  obtain ⟨-, -, -, -, -, hxi, -⟩ := GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε
  let c : (Λ →+* O) → C := fun σ =>
    if hσ : ∃ f, IsTheta σ f then
      Classical.choose (GlobalTheory.T.determinant_valuation_iota_scalar p C v O hv ε hε Λ N h hh D ψ Φ σ hσ.choose hσ.choose_spec).2
    else 0
  have hc : ∀ σ f, IsTheta σ f → D.lieRank σ ≤ N ∧ c σ ≠ 0 ∧
      Lead ((algebraMap O C).comp f) (inA (xi ε)) Φ.F.det (D.lieRank σ) (c σ) := by
    intro σ f hf
    have hσ : ∃ f, IsTheta σ f := ⟨f, hf⟩
    have hfe : hσ.choose = f := isTheta_unique hσ.choose_spec hf
    have H := GlobalTheory.T.determinant_valuation_iota_scalar p C v O hv ε hε Λ N h hh D ψ Φ σ hσ.choose hσ.choose_spec
    have hcs := Classical.choose_spec H.2
    have hcσ : c σ = Classical.choose H.2 := by simp only [c, dif_pos hσ]
    rw [hcσ]
    refine ⟨H.1, hcs.1, ?_⟩
    rw [← hfe]
    exact hcs.2
  have hψdet : ψ Φ.F.det = (Φ.F.map ψ).det := by rw [RingHom.map_det]; rfl
  refine ⟨Φ.F.det, c, ⟨⟨Φ.G.det, ?_⟩, Φ.Ψ.det, ?_, ⟨Φ.Ψ'.det, ?_⟩⟩, fun σ f hf => hc σ f hf, ?_⟩
  · rw [← Matrix.det_mul, Φ.F_mul_G, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  · rw [hψdet, ← Matrix.det_mul, ← Φ.F_eq]
  · rw [← Matrix.det_mul, Φ.Ψ_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  · obtain ⟨f, hf, -, -, -⟩ := theta_tensor_exists p C v O hv ε hε Λ τ
    obtain ⟨l₀, hl₀, hiota⟩ := GlobalTheory.T.determinant_valuation_order_sum p C v O hv ε hε Λ N h hh D ψ Φ τ f hf ι lam hι hlat
    have hrank := GlobalTheory.T.determinant_valuation_order p C v O hv ε hε Λ N h hh D ψ Φ τ f hf
    have hmu : (inA (mu ε) : RL p O Λ) = (inA (xi ε) : RL p O Λ) * inA (nu ε) := by
      rw [← map_mul, xi_mul_nu]
    have hFG : Φ.F * Φ.G =
        ((inA (xi ε) : RL p O Λ) * inA (nu ε)) • (1 : Matrix (Fin N) (Fin N) (RL p O Λ)) := by
      rw [Φ.F_mul_G, hmu]
    rw [← hrank] at hiota
    have hlead := GlobalTheory.LeadDet.lead_det (RL p O Λ) C ((algebraMap O C).comp f) (inA (xi ε))
      (inA (nu ε)) N Φ.F Φ.G l₀ hFG hiota
    rw [hrank] at hlead
    obtain ⟨-, -, hcl⟩ := hc τ f hf
    have hξreg : (inA (xi ε) : RL p O Λ) ∈ nonZeroDivisors (RL p O Λ) :=
      GlobalTheory.T.ainf_element_theta_compatible p C v O hv ε hε Λ (xi ε) hxi
    have heq := GlobalTheory.DetInv.lead_mul_unique (RL p O Λ) C ((algebraMap O C).comp f) (inA (xi ε))
      Φ.F.det 1 (D.lieRank τ) _ (c τ) hξreg hlead (by rwa [one_mul])
    have hA : f (inA (nu ε)) = WittVector.fontaineTheta O p (nu ε) := by
      show f (algebraMap (Ainf p O) (RL p O Λ) (nu ε)) = _
      rw [Algebra.TensorProduct.algebraMap_apply, hf]
      simp
    rw [heq, map_one, one_mul, map_mul, map_pow, hl₀, RingHom.comp_apply, hA]

end GlobalTheory.DetInv
end
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_determinant_element_property : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (τ : Λ →+* O) ι (lam : C), IsIota C D τ N ι → ι '' (detLattice C (actT D) τ N : Set (detLine C (actT D) τ N)) = (fun w => lam • w) '' (detLattice C (actH D) τ N : Set (detLine C (actH D) τ N)) → ∃ (Δ : RL p O Λ) (c : (Λ →+* O) → C), IsDetElt ε ψ N Δ ∧ HasOrders C ε N Δ D.lieRank c ∧ v (c τ) = v lam * v (algebraMap O C (WittVector.fontaineTheta O p (nu ε))) ^ D.lieRank τ := by
  atlas_forward_decl GlobalTheory.DetInv.exists_detElt_lieRank
end
