import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodChevalley
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompletelyReducibleToMatrixIffIsSemisimpleRepresStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGroupHomRangeEqOfAutStable
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import BuildAid.ForwardExisting

section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemisimpleRepresentation_tprod_chevalley : ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ' : Representation ℂ G W) [FiniteDimensional ℂ V] [FiniteDimensional ℂ W], ρ.IsSemisimpleRepresentation → ρ'.IsSemisimpleRepresentation → (ρ.tprod ρ').IsSemisimpleRepresentation := by
  first | exact @GlobalTheory.ClassFin.isSemisimpleRepresentation_tprod | exact GlobalTheory.ClassFin.isSemisimpleRepresentation_tprod | (intros; apply GlobalTheory.ClassFin.isSemisimpleRepresentation_tprod <;> assumption)
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private noncomputable def dotPerp (U : Submodule ℂ (ι → ℂ)) : Submodule ℂ (ι → ℂ) :=
  U.dualAnnihilator.comap (dotProductEquiv ℂ ι).toLinearMap

private theorem mem_dotPerp (U : Submodule ℂ (ι → ℂ)) (v : ι → ℂ) :
    v ∈ dotPerp U ↔ ∀ w ∈ U, v ⬝ᵥ w = 0 := by
  simp [dotPerp, Submodule.mem_dualAnnihilator, dotProductEquiv]

private theorem dotPerp_isCompl {U U' : Submodule ℂ (ι → ℂ)} (h : IsCompl U U') :
    IsCompl (dotPerp U) (dotPerp U') :=
  (Submodule.orderIsoMapComap (dotProductEquiv ℂ ι)).symm.isCompl (Subspace.isCompl_dualAnnihilator h)

private theorem dotPerp_dotPerp (U : Submodule ℂ (ι → ℂ)) : dotPerp (dotPerp U) = U := by
  ext v
  constructor
  · intro hv
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := U), Submodule.mem_dualCoannihilator]
    intro φ hφ
    obtain ⟨w, rfl⟩ := (dotProductEquiv ℂ ι).surjective φ
    have h := (mem_dotPerp _ v).1 hv w hφ
    rw [dotProduct_comm] at h
    simpa [dotProductEquiv] using h
  · intro hv
    rw [mem_dotPerp]
    intro w hw
    rw [dotProduct_comm]
    exact (mem_dotPerp _ w).1 hw v hv

private theorem dotPerp_invariant (U : Submodule ℂ (ι → ℂ)) (g : Matrix ι ι ℂ)
    (h : ∀ v ∈ U, g *ᵥ v ∈ U) : ∀ v ∈ dotPerp U, gᵀ *ᵥ v ∈ dotPerp U := by
  intro v hv
  rw [mem_dotPerp] at hv ⊢
  intro w hw
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  exact hv _ (h w hw)

theorem ss_transpose :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), SS Γ → SS (Matrix.transpose '' Γ) := by
  intro ι _ _ Γ hΓ W hW
  obtain ⟨U', hU', hc⟩ := hΓ (dotPerp W) (fun g hg => by
    simpa using dotPerp_invariant W gᵀ (hW _ ⟨g, hg, rfl⟩))
  refine ⟨dotPerp U', ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact dotPerp_invariant U' g (hU' g hg)
  · have := dotPerp_isCompl hc
    rwa [dotPerp_dotPerp] at this

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompletelyReducibleMatrixSet_transpose_image : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), SS Γ → SS (Matrix.transpose '' Γ) := by
  atlas_forward_decl GlobalTheory.ClassFin.ss_transpose
end

section
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_semisimple_rep_tpow {ι : Type} [Fintype ι] [DecidableEq ι] {G : Type} [Group G]
    (ρ : G →* Matrix ι ι ℂ) (h : SS (Set.range ρ)) (n : ℕ) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (r : Representation ℂ G V)
      (b : Module.Basis (Fin n → ι) ℂ V),
      r.IsSemisimpleRepresentation ∧ ∀ g, LinearMap.toMatrix b b (r g) = tpow n (ρ g) := by
  induction n with
  | zero =>
    have hm : ∀ g : G, LinearMap.toMatrix (Pi.basisFun ℂ (Fin 0 → ι)) (Pi.basisFun ℂ (Fin 0 → ι))
        (Representation.trivial ℂ G ((Fin 0 → ι) → ℂ) g) = 1 := by
      intro g
      have : Representation.trivial ℂ G ((Fin 0 → ι) → ℂ) g = LinearMap.id := by
        ext v; simp
      rw [this, LinearMap.toMatrix_id]
    refine ⟨(Fin 0 → ι) → ℂ, inferInstance, inferInstance, Representation.trivial ℂ G _,
      Pi.basisFun ℂ _, ?_, ?_⟩
    · rw [← GlobalTheory.T.completelyReducible_toMatrix_iff_isSemisimpleRepresentation (Fin 0 → ι) G _ _ (Pi.basisFun ℂ _)]
      intro W _
      obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
      refine ⟨W', ?_, hW'⟩
      rintro _ ⟨g, rfl⟩ v hv
      simpa only [hm, Matrix.one_mulVec] using hv
    · intro g
      rw [hm]
      ext a b
      have : a = b := Subsingleton.elim _ _
      subst this
      simp [tpow]
  | succ n ih =>
    obtain ⟨V, _, _, r, b, hr, hb⟩ := ih
    let r₁ : Representation ℂ G (ι → ℂ) :=
      (Matrix.toLinAlgEquiv' (R := ℂ) (n := ι)).toAlgHom.toMonoidHom.comp ρ
    have h₁ : ∀ g, LinearMap.toMatrix (Pi.basisFun ℂ ι) (Pi.basisFun ℂ ι) (r₁ g) = ρ g := by
      intro g
      change LinearMap.toMatrix (Pi.basisFun ℂ ι) (Pi.basisFun ℂ ι) (Matrix.toLin' (ρ g)) = ρ g
      rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
    have hs₁ : r₁.IsSemisimpleRepresentation := by
      rw [← GlobalTheory.T.completelyReducible_toMatrix_iff_isSemisimpleRepresentation ι G _ _ (Pi.basisFun ℂ _)]
      simpa only [h₁] using h
    haveI : FiniteDimensional ℂ V := Module.Finite.of_basis b
    let e : ι × (Fin n → ι) ≃ (Fin (n + 1) → ι) := Fin.consEquiv fun _ => ι
    refine ⟨(ι → ℂ) ⊗[ℂ] V, inferInstance, inferInstance, r₁.tprod r,
      ((Pi.basisFun ℂ ι).tensorProduct b).reindex e,
      GlobalTheory.T.isSemisimpleRepresentation_tprod_chevalley G _ r₁ V r hs₁ hr, ?_⟩
    intro g
    have ht : LinearMap.toMatrix ((Pi.basisFun ℂ ι).tensorProduct b) ((Pi.basisFun ℂ ι).tensorProduct b)
        ((r₁.tprod r) g) = ρ g ⊗ₖ tpow n (ρ g) := by
      rw [Representation.tprod_apply, TensorProduct.toMatrix_map, h₁, hb]
    ext a c
    have := congrFun (congrFun ht (e.symm a)) (e.symm c)
    rw [LinearMap.toMatrix_apply] at this ⊢
    rw [Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply, this]
    simp [e, tpow, Fin.prod_univ_succ, Fin.consEquiv, Fin.tail]

theorem ss_tpow_transpose : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)),
    IsPre Γ → SS Γ → ∀ n : ℕ, SS ((fun g => (tpow n g)ᵀ) '' Γ) := by
  intro ι _ _ Γ hΓ hs n
  obtain ⟨G, _, ρ, rfl⟩ := GlobalTheory.T.exists_group_hom_range_eq_of_isPre ι Γ hΓ
  obtain ⟨V, _, _, r, b, hr, hb⟩ := exists_semisimple_rep_tpow ρ hs n
  have h := GlobalTheory.T.isCompletelyReducibleMatrixSet_transpose_image _ _ ((GlobalTheory.T.completelyReducible_toMatrix_iff_isSemisimpleRepresentation _ G V r b).2 hr)
  simp only [hb] at h
  rw [← Set.range_comp] at h ⊢
  exact h

end GlobalTheory.ClassFin
end

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completelyReducible_kroneckerPower_transpose : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∀ n : ℕ, SS ((fun g => (tpow n g)ᵀ) '' Γ) := by
  atlas_forward_decl GlobalTheory.ClassFin.ss_tpow_transpose
end
