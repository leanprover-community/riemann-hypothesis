import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonomialsSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOrthogonalIdempotentsHeckeSpanRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDetGenericSumMemHeckeAlgebra
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetOneAddSmulBlkMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDetPencilMemHeckeAlgebra
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentRankConstOfCharpolyInLocalFunctions
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeckeSpanCorrectionDistinctEigenvalues
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankIdempotentBlockCharPolyOfProjection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixRankMapField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDecompositionBaseChange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDvrExtensionForMonicFamily
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentBlockRootFactorsRankOneDomain
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjOnCharValuesAndLengthQuotient
import Development.AutomorphicArithmetic.CyclotomicBounds.FactorizationConductorLeLocalLevel

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_repMatrix_eq_top_of_absIrreducible : ∀ {Γ k : Type} [Group Γ] [Field k] {r : ℕ} (ρ : Γ →* GL (Fin r) k), AbsIrrSub ρ ⊤ → Submodule.span k (Set.range (mat ρ)) = ⊤ := by
  first | exact @GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub | exact GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub | (intros; apply GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub <;> assumption)
end

section
namespace GlobalTheory.SpanOfResidue

theorem mem_smul_top_of_entries {A : Type} [CommRing A] {r : ℕ} (I : Ideal A)
    (d : Matrix (Fin r) (Fin r) A) (hd : ∀ i j, d i j ∈ I) :
    d ∈ I • (⊤ : Submodule A (Matrix (Fin r) (Fin r) A)) := by
  rw [Matrix.matrix_eq_sum_single d]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have h : Matrix.single i j (d i j) = d i j • Matrix.single i j (1 : A) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [h]
  exact Submodule.smul_mem_smul (hd i j) Submodule.mem_top

theorem span_eq_top_of_residue {ι A : Type} [CommRing A] [IsLocalRing A] {r : ℕ}
    (f : ι → Matrix (Fin r) (Fin r) A)
    (h : Submodule.span (IsLocalRing.ResidueField A)
      (Set.range fun (i : ι) ↦ Matrix.map (f i)
        (⇑(IsLocalRing.residue A) : A → IsLocalRing.ResidueField A)) = ⊤) :
    Submodule.span A (Set.range f) = ⊤ := by
  have key : ∀ y ∈ Submodule.span (IsLocalRing.ResidueField A)
      (Set.range fun (i : ι) ↦ Matrix.map (f i)
        (⇑(IsLocalRing.residue A) : A → IsLocalRing.ResidueField A)),
      ∃ n ∈ Submodule.span A (Set.range f),
        Matrix.map n (⇑(IsLocalRing.residue A) : A → IsLocalRing.ResidueField A) = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨f i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
    | zero =>
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      ext i j
      simp
    | add x y _ _ hx hy =>
      obtain ⟨n, hn, rfl⟩ := hx
      obtain ⟨m, hm, rfl⟩ := hy
      refine ⟨n + m, Submodule.add_mem _ hn hm, ?_⟩
      ext i j
      simp
    | smul c x _ hx =>
      obtain ⟨n, hn, rfl⟩ := hx
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
      refine ⟨a • n, Submodule.smul_mem _ a hn, ?_⟩
      ext i j
      simp
  rw [eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal A)
    Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) ?_
  intro x _
  obtain ⟨n, hn, hnx⟩ := key (Matrix.map x (IsLocalRing.residue A)) (h ▸ Submodule.mem_top)
  have hx : x = n + (x - n) := by abel
  rw [hx]
  refine Submodule.add_mem_sup hn (mem_smul_top_of_entries _ _ fun i j => ?_)
  rw [← IsLocalRing.residue_eq_zero_iff, Matrix.sub_apply, map_sub, sub_eq_zero]
  exact (congrFun (congrFun hnx i) j).symm

end GlobalTheory.SpanOfResidue
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory

theorem span_matrix_eq_top_of_residue_span {ι A : Type} [CommRing A] [IsLocalRing A] {r : ℕ}
    (f : ι → Matrix (Fin r) (Fin r) A)
    (h : Submodule.span (IsLocalRing.ResidueField A)
      (Set.range (fun i => (f i).map (IsLocalRing.residue A))) = ⊤) :
    Submodule.span A (Set.range f) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue
  | exact _root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue
  | (apply _root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpanOfResidue.span_eq_top_of_residue ..)

theorem span_mat_eq_top_of_residue {Γ A : Type} [Group Γ] [CommRing A] [IsLocalRing A] {r : ℕ}
    (ρ : Γ →* GL (Fin r) A)
    (h : Submodule.span (IsLocalRing.ResidueField A)
      (Set.range (mat (mapRep (IsLocalRing.residue A) ρ))) = ⊤) :
    Submodule.span A (Set.range (mat ρ)) = ⊤ :=
  span_matrix_eq_top_of_residue_span (mat ρ) h

end GlobalTheory
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_repMatrix_eq_top_of_residue_span_eq_top : ∀ {Γ A : Type} [Group Γ] [CommRing A] [IsLocalRing A] {r : ℕ} (ρ : Γ →* GL (Fin r) A), Submodule.span (IsLocalRing.ResidueField A) (Set.range (mat (mapRep (IsLocalRing.residue A) ρ))) = ⊤ → Submodule.span A (Set.range (mat ρ)) = ⊤ := by
  atlas_forward_decl GlobalTheory.span_mat_eq_top_of_residue
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.SpanRing

theorem blockDet_mem : ∀ {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ} (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)), CharPolyIn T rep → ∀ (g : ℕ) (Θ : Fin g → Fin g → X → Matrix (Fin n) (Fin n) O), (∀ p q, InRing T rep (Θ p q)) → (fun x => Matrix.det (Matrix.of fun (pa qb : Fin g × Fin n) => Θ pa.1 qb.1 x pa.2 qb.2)) ∈ T := by
  intro Γ X O _ _ n T rep hc g Θ hΘ
  exact GlobalTheory.BlockDet.main T n (ringR T rep)
    (fun m a ha d => GlobalTheory.T.coeff_det_generic_sum_mem_heckeAlgebra T rep hc m a (fun k => (mem_ringR T rep _).1 (ha k)) d)
    g Θ (fun p q => (mem_ringR T rep _).2 (hΘ p q))

end GlobalTheory.SpanRing
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockDet_mem_heckeAlgebra_of_heckeSpan : ∀ {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ} (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)), CharPolyIn T rep → ∀ (g : ℕ) (Θ : Fin g → Fin g → X → Matrix (Fin n) (Fin n) O), (∀ p q, InRing T rep (Θ p q)) → (fun x => Matrix.det (Matrix.of fun (pa qb : Fin g × Fin n) => Θ pa.1 qb.1 x pa.2 qb.2)) ∈ T := by
  atlas_forward_decl GlobalTheory.SpanRing.blockDet_mem
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_det_pencil_mem_heckeAlgebra : ∀ {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ} (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)), CharPolyIn T rep → ∀ a b : X → Matrix (Fin n) (Fin n) O, InRing T rep a → InRing T rep b → ∀ j : ℕ, (fun x => (Matrix.det ((Polynomial.X : Polynomial O) • (a x).map (Polynomial.C (R := O)) + (b x).map (Polynomial.C (R := O)))).coeff j) ∈ T := by
  first | exact @GlobalTheory.SpanRing.coeff_det_pencil_mem | exact GlobalTheory.SpanRing.coeff_det_pencil_mem | (intros; apply GlobalTheory.SpanRing.coeff_det_pencil_mem <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_rank_const_of_charpoly_in_local_functions : ∀ {X O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {n : ℕ} (T : Subalgebra O (X → O)) (e : X → Matrix (Fin n) (Fin n) O), IsLocalRing T → e * e = e → (∀ j : ℕ, (fun x => (e x).charpoly.coeff j) ∈ T) → ∀ x y, ((e x).map (toFr O)).rank = ((e y).map (toFr O)).rank := by
  first | exact @GlobalTheory.IdemConstRank.rank_const | exact GlobalTheory.IdemConstRank.rank_const | (intros; apply GlobalTheory.IdemConstRank.rank_const <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_idempotentBlockCharPoly_of_projection : ∀ {K : Type} [Field K] {n r t : ℕ} (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))) (E M : Matrix (Fin n) (Fin n) K) (d : Fin t → K), (∀ u, e (E.mulVec u) = (0, (e u).2)) → (∀ u, e (M.mulVec u) = (0, fun c => d c * (e u).2 c)) → E.rank = t ∧ blockPol E M = ∏ c, (Polynomial.X - Polynomial.C (d c)) := by
  first | exact @GlobalTheory.CharBlock.rank_blockPol_proj | exact GlobalTheory.CharBlock.rank_blockPol_proj | (intros; apply GlobalTheory.CharBlock.rank_blockPol_proj <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory

theorem _root_.GlobalTheory.rank_eq_of_acts_through_first_block {K : Type} [Field K] {n r t : ℕ}
    (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))) (F : Matrix (Fin n) (Fin n) K)
    (ε : Matrix (Fin r) (Fin r) K) (h : ∀ u, e (F.mulVec u) = (ε.mulVec (e u).1, 0)) :
    F.rank = ε.rank := by
  have key : (LinearMap.range F.mulVecLin).map (e : (Fin n → K) →ₗ[K] _) =
      (LinearMap.range ε.mulVecLin).map (LinearMap.inl K (Fin r → K) (Fin t → K)) := by
    ext ⟨a, b⟩
    simp only [Submodule.mem_map, LinearMap.mem_range, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨_, ⟨u, rfl⟩, hx⟩
      rw [LinearEquiv.coe_coe, h] at hx
      exact ⟨_, ⟨(e u).1, rfl⟩, by simpa using hx⟩
    · rintro ⟨_, ⟨v, rfl⟩, hx⟩
      refine ⟨_, ⟨e.symm (v, 0), rfl⟩, ?_⟩
      rw [LinearEquiv.coe_coe, h]
      simpa using hx
  unfold Matrix.rank
  rw [← LinearEquiv.finrank_map_eq e, key]
  exact (Submodule.equivMapOfInjective _ LinearMap.inl_injective _).finrank_eq.symm

end GlobalTheory
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_eq_of_mulVec_through_first_block : ∀ {K : Type} [Field K] {n r t : ℕ} (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))) (F : Matrix (Fin n) (Fin n) K) (ε : Matrix (Fin r) (Fin r) K), (∀ u, e (F.mulVec u) = (ε.mulVec (e u).1, 0)) → F.rank = ε.rank := by
  atlas_forward_decl GlobalTheory.rank_eq_of_acts_through_first_block
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_map_ringHom : ∀ {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : ℕ} (M : Matrix (Fin n) (Fin n) K), (M.map φ).rank = M.rank := by
  first | exact @GlobalTheory.matrix_rank_map_field | exact GlobalTheory.matrix_rank_map_field | (intros; apply GlobalTheory.matrix_rank_map_field <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_mulVec_decomposition_map_of_decomposition : ∀ {K L : Type} [Field K] [Field L] (φ : K →+* L) {n r t : ℕ} (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))), ∃ e' : (Fin n → L) ≃ₗ[L] ((Fin r → L) × (Fin t → L)), ∀ (M : Matrix (Fin n) (Fin n) K) (P : Matrix (Fin r) (Fin r) K) (d : Fin t → K), (∀ u, e (M.mulVec u) = (P.mulVec (e u).1, fun c => d c * (e u).2 c)) → ∀ u, e' ((M.map φ).mulVec u) = ((P.map φ).mulVec (e' u).1, fun c => φ (d c) * (e' u).2 c) := by
  first | exact @GlobalTheory.blockDecomposition_baseChange | exact GlobalTheory.blockDecomposition_baseChange | (intros; apply GlobalTheory.blockDecomposition_baseChange <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory

theorem exists_injective_roots_of_ncard_rootSet {A O : Type} [CommRing A] [IsDomain A] [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Algebra A O] (t : ℕ) (P : Polynomial A) (α : Fin t → FractionRing O)
    (hinj : Function.Injective (algebraMap A O))
    (hcard : ((P.map (toFr A)).rootSet (AlgebraicClosure (FractionRing A))).ncard = t)
    (hP : P.map ((toFr O).comp (algebraMap A O)) = ∏ c, (Polynomial.X - Polynomial.C (α c))) :
    ∃ β : Fin t → O, Function.Injective β ∧ P.map (algebraMap A O) = ∏ c, (Polynomial.X - Polynomial.C (β c)) := by
  classical
  have hO : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective _ _
  have hA : Function.Injective (algebraMap A (FractionRing A)) := IsFractionRing.injective _ _
  set g : A →+* FractionRing O := (algebraMap O (FractionRing O)).comp (algebraMap A O) with hg
  have hgi : Function.Injective g := hO.comp hinj
  change P.map g = _ at hP
  change ((P.map (algebraMap A (FractionRing A))).rootSet _).ncard = t at hcard
  have hmon' : (P.map g).Monic := by
    rw [hP]; exact Polynomial.monic_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C _)
  have hmon : P.Monic := Polynomial.monic_of_injective hgi hmon'
  have hdeg : P.natDegree = t := by
    rw [← hmon.natDegree_map g, hP, Polynomial.natDegree_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C _)]
    simp
  have hsep : (P.map (algebraMap A (FractionRing A))).Separable := by
    have hne : P.map (algebraMap A (FractionRing A)) ≠ 0 := (hmon.map _).ne_zero
    rw [← Polynomial.card_rootSet_eq_natDegree_iff_of_splits (K := AlgebraicClosure (FractionRing A)) hne (IsAlgClosed.splits _), hmon.natDegree_map, hdeg, ← hcard, Set.ncard_eq_toFinset_card', Set.toFinset_card]
  obtain ⟨φ, hφ⟩ : ∃ φ : FractionRing A →+* FractionRing O, φ.comp (algebraMap A (FractionRing A)) = g :=
    ⟨IsFractionRing.lift hgi, RingHom.ext fun a => IsFractionRing.lift_algebraMap (K := FractionRing A) hgi a⟩
  have hsep2 : (P.map g).Separable := by
    rw [← hφ, ← Polynomial.map_map]; exact hsep.map
  have hα : Function.Injective α := by
    rw [hP] at hsep2
    exact Polynomial.separable_prod_X_sub_C_iff.mp hsep2
  have hint : ∀ c, ∃ b : O, algebraMap O (FractionRing O) b = α c := by
    intro c
    apply IsIntegrallyClosed.algebraMap_eq_of_integral
    refine ⟨P.map (algebraMap A O), hmon.map _, ?_⟩
    rw [← Polynomial.eval_map, Polynomial.map_map, ← hg, hP, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ c) (by simp)
  choose β hβ using hint
  refine ⟨β, fun c d h => hα (by rw [← hβ, ← hβ, h]), ?_⟩
  apply Polynomial.map_injective _ hO
  rw [Polynomial.map_map, ← hg, hP, Polynomial.map_prod]
  simp [hβ]

end GlobalTheory
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_roots_of_ncard_rootSet' : ∀ {A O : Type} [CommRing A] [IsDomain A] [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Algebra A O] (t : ℕ) (P : Polynomial A) (α : Fin t → FractionRing O), Function.Injective (algebraMap A O) → ((P.map (toFr A)).rootSet (AlgebraicClosure (FractionRing A))).ncard = t → P.map ((toFr O).comp (algebraMap A O)) = ∏ c, (Polynomial.X - Polynomial.C (α c)) → ∃ β : Fin t → O, Function.Injective β ∧ P.map (algebraMap A O) = ∏ c, (Polynomial.X - Polynomial.C (β c)) := by
  atlas_forward_decl GlobalTheory.exists_injective_roots_of_ncard_rootSet
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_extension_for_monic_family : ∀ (l : ℕ) [Fact l.Prime] {A ι : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A] [Algebra ℤ_[l] A] [Module.Finite ℤ_[l] A] [Finite ι] (t : ℕ) (P : ι → Polynomial A), (∀ i, ((P i).map (toFr A)).Monic ∧ ((P i).map (toFr A)).natDegree = t) → ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B) (_ : Algebra A B), Module.Finite A B ∧ Function.Injective (algebraMap A B) ∧ ∀ i, ∃ α : Fin t → FractionRing B, (P i).map ((toFr B).comp (algebraMap A B)) = ∏ c, (Polynomial.X - Polynomial.C (α c)) := by
  first | exact @GlobalTheory.exists_finite_dvr_splitting | exact GlobalTheory.exists_finite_dvr_splitting | (intros; apply GlobalTheory.exists_finite_dvr_splitting <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.RootFactorProduct

private lemma map_sub_smul_E_mulVec_eq {O : Type} [CommRing O] [IsDomain O] {n r t : ℕ}
    (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O]
      ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    (E X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O)
    (hE : ∀ u, e ((E.map (toFr O)).mulVec u) = (0, (e u).2))
    (hX : ∀ u, e ((X₀.map (toFr O)).mulVec u) =
      (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1)) * (e u).2 c))
    (a : ℕ) (v : Fin n → FractionRing O) :
    e (((X₀ - ρ a • E).map (toFr O)).mulVec v) =
      (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1) - ρ a) * (e v).2 c) := by
  have hm : (X₀ - ρ a • E).map (toFr O) = X₀.map (toFr O) - toFr O (ρ a) • E.map (toFr O) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, map_mul]
  have hs : ((toFr O (ρ a)) • E.map (toFr O)).mulVec v = toFr O (ρ a) • (E.map (toFr O)).mulVec v := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum,
      mul_assoc]
  rw [hm, Matrix.sub_mulVec, hs, map_sub, map_smul, hX, hE]
  refine Prod.ext (by simp) ?_
  funext c
  simp only [Prod.snd_sub, Prod.smul_snd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub]
  ring

theorem prod_cons_action {O : Type} [CommRing O] [IsDomain O] {n r t : ℕ}
    (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O]
      ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    (E X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O)
    (hE : ∀ u, e ((E.map (toFr O)).mulVec u) = (0, (e u).2))
    (hX : ∀ u, e ((X₀.map (toFr O)).mulVec u) =
      (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1)) * (e u).2 c))
    (s : List ℕ) : ∀ (a : ℕ) (u : Fin n → FractionRing O),
      e (((((a :: s).map fun c => X₀ - ρ c • E).prod).map (toFr O)).mulVec u) =
        (0, fun c : Fin t =>
          toFr O (((a :: s).map fun c' => ρ ((c : ℕ) + 1) - ρ c').prod) * (e u).2 c) := by
  induction s with
  | nil =>
    intro a u
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact map_sub_smul_E_mulVec_eq e E X₀ ρ hE hX a u
  | cons b s ih =>
    intro a u
    rw [List.map_cons, List.prod_cons, Matrix.map_mul, ← Matrix.mulVec_mulVec,
      map_sub_smul_E_mulVec_eq e E X₀ ρ hE hX a, ih b u]
    refine Prod.ext rfl ?_
    funext c
    simp only [List.map_cons, List.prod_cons, map_mul, mul_assoc]

private lemma list_prod_range'_eq_prod_Ico {M : Type} [CommMonoid M] (g : ℕ → M) (n : ℕ) :
    ∀ m : ℕ, ((List.range' m n).map g).prod = ∏ k ∈ Finset.Ico m (m + n), g k := by
  induction n with
  | zero => intro m; simp
  | succ n ih =>
    intro m
    rw [List.range'_succ, List.map_cons, List.prod_cons, ih, show m + (n + 1) = m + 1 + n by omega,
      Finset.prod_eq_prod_Ico_succ_bot (show m < m + 1 + n by omega)]

theorem prod_other_factors_action {O : Type} [CommRing O] [IsDomain O] {n r t : ℕ}
    (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O]
      ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    (E X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O) (ht : 2 ≤ t)
    (hE : ∀ u, e ((E.map (toFr O)).mulVec u) = (0, (e u).2))
    (hX : ∀ u, e ((X₀.map (toFr O)).mulVec u) =
      (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1)) * (e u).2 c)) (u : Fin n → FractionRing O) :
    e (((((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • E).prod).map (toFr O)).mulVec u) =
      (0, fun c : Fin t => if (c : ℕ) = 0 then
        toFr O (∏ c' ∈ Finset.Ioc 1 t, (ρ 1 - ρ c')) * (e u).2 c else 0) := by
  have hl : List.range' 2 (t - 1) = 2 :: List.range' 3 (t - 2) := by
    rw [show t - 1 = (t - 2) + 1 by omega, List.range'_succ]
  rw [hl, prod_cons_action e E X₀ ρ hE hX, ← hl]
  refine Prod.ext rfl ?_
  funext c
  dsimp only
  split_ifs with h0
  · simp only [h0, zero_add]
    congr 2
    all_goals
      rw [list_prod_range'_eq_prod_Ico]
      apply Finset.prod_congr _ (fun _ _ => rfl)
      ext x
      simp only [Finset.mem_Ico, Finset.mem_Ioc]
      omega
  · have hc := c.isLt
    rw [List.prod_eq_zero, map_zero, zero_mul]
    exact List.mem_map.2 ⟨(c : ℕ) + 1, List.mem_range'_1.2 ⟨by omega, by omega⟩, sub_self _⟩

end GlobalTheory.RootFactorProduct
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_other_root_factors_action_first_coordinate : ∀ {O : Type} [CommRing O] [IsDomain O] {n r t : ℕ} (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))) (E X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O), 2 ≤ t → (∀ u, e ((E.map (toFr O)).mulVec u) = (0, (e u).2)) → (∀ u, e ((X₀.map (toFr O)).mulVec u) = (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1)) * (e u).2 c)) → ∀ u, e (((((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • E).prod).map (toFr O)).mulVec u) = (0, fun c : Fin t => if (c : ℕ) = 0 then toFr O (∏ c' ∈ Finset.Ioc 1 t, (ρ 1 - ρ c')) * (e u).2 c else 0) := by
  atlas_forward_decl GlobalTheory.RootFactorProduct.prod_other_factors_action
end

section
section
noncomputable section

namespace GlobalTheory.SpanBlockAction

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

section

variable {O : Type} [CommRing O] {n r t : ℕ}

def ActsAs (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    (M : Matrix (Fin n) (Fin n) O) (P : Matrix (Fin r) (Fin r) O) (d : Fin t → O) : Prop :=
  ∀ u, e ((M.map (toFr O)).mulVec u) =
    ((P.map (toFr O)).mulVec (e u).1, fun c : Fin t => toFr O (d c) * (e u).2 c)

theorem map_smul_toFr {k : ℕ} (c : O) (M : Matrix (Fin k) (Fin k) O) :
    (c • M).map (toFr O) = toFr O c • M.map (toFr O) := by
  ext i j
  simp [smul_eq_mul]

theorem map_sum_toFr {k m : ℕ} (M : Fin m → Matrix (Fin k) (Fin k) O) :
    (∑ i, M i).map (toFr O) = ∑ i, (M i).map (toFr O) := by
  ext i j
  simp [Matrix.sum_apply]

private theorem sum_mulVec_eq {K : Type} [CommRing K] {k m : ℕ} (A : Fin m → Matrix (Fin k) (Fin k) K)
    (v : Fin k → K) : (∑ i, A i).mulVec v = ∑ i, (A i).mulVec v := by
  ext a
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

private theorem smul_mulVec_eq' {K : Type} [CommRing K] {k : ℕ} (a : K) (A : Matrix (Fin k) (Fin k) K)
    (v : Fin k → K) : (a • A).mulVec v = a • A.mulVec v := by
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem actsAs_sum
    (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    {m : ℕ} (c : Fin m → O) (M : Fin m → Matrix (Fin n) (Fin n) O) (P : Fin m → Matrix (Fin r) (Fin r) O)
    (d : Fin m → Fin t → O) (h : ∀ k, ActsAs e (M k) (P k) (d k)) :
    ActsAs e (∑ k, c k • M k) (∑ k, c k • P k) (fun j => ∑ k, c k * d k j) := by
  unfold ActsAs at h ⊢
  intro u
  rw [map_sum_toFr, map_sum_toFr]
  simp only [map_smul_toFr, sum_mulVec_eq, smul_mulVec_eq', map_sum, map_smul, h]
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum]
  · funext j
    simp [Prod.snd_sum, Finset.sum_apply, Finset.sum_mul, mul_assoc]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Algebra.smul_def]

theorem ActsAs.unique
    {e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))}
    {M : Matrix (Fin n) (Fin n) O} {P P' : Matrix (Fin r) (Fin r) O} {d d' : Fin t → O}
    (h : ActsAs e M P d) (h' : ActsAs e M P' d') : P = P' := by
  have hv : ∀ v : Fin r → FractionRing O, (P.map (toFr O)).mulVec v = (P'.map (toFr O)).mulVec v := by
    intro v
    have h1 := h (e.symm (v, 0))
    have h2 := h' (e.symm (v, 0))
    rw [h1] at h2
    simpa using congrArg Prod.fst h2
  have hm : P.map (toFr O) = P'.map (toFr O) := by
    apply Matrix.toLin'.injective
    exact LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using hv v
  ext i j
  apply IsFractionRing.injective O (FractionRing O)
  have := congrFun (congrFun hm i) j
  simpa [toFr] using this

end

theorem actsAs_mat {Γ O : Type} [Group Γ] [CommRing O] [IsDomain O] {n r t : ℕ}
    {σ : Γ →* GL (Fin n) O} {ρ : Γ →* GL (Fin r) O} {χ : ℕ → (Γ →* Oˣ)}
    {e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))}
    (h : IsDecomp (t := t) σ ρ χ e) (g : Γ) :
    ActsAs e (mat σ g) (mat ρ g) (fun c => ((χ ((c : ℕ) + 1) g : Oˣ) : O)) := by
  unfold ActsAs
  intro u
  simpa [overK, matRep, mapM, mat] using h g u

theorem exists_block_action {Γ X O : Type} [Group Γ] [CommRing O] [IsDomain O] {n r t : ℕ}
    (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)) (ρ : Γ →* GL (Fin r) O) (χ : ℕ → (Γ →* Oˣ))
    (π : X)
    (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    (hspan : Submodule.span O (Set.range (mat ρ)) = ⊤) (hdec : IsDecomp (t := t) (rep π) ρ χ e) :
    ∃ (ψρ : (X → Matrix (Fin n) (Fin n) O) → Matrix (Fin r) (Fin r) O)
      (ψχ : Fin t → (X → Matrix (Fin n) (Fin n) O) → O),
      (∀ a, InRing T rep a → ∀ u, e (((a π).map (toFr O)).mulVec u) =
        (((ψρ a).map (toFr O)).mulVec (e u).1, fun c : Fin t => toFr O (ψχ c a) * (e u).2 c)) ∧
      ∀ P : Matrix (Fin r) (Fin r) O, ∃ a, InRing T rep a ∧ ψρ a = P := by
  classical
  have hact : ∀ M ∈ Submodule.span O (Set.range (mat (rep π))),
      ∃ p : Matrix (Fin r) (Fin r) O × (Fin t → O), ActsAs e M p.1 p.2 := by
    intro M hM
    obtain ⟨m, c, g, rfl⟩ := Submodule.mem_span_set'.mp hM
    have hg : ∀ k, ∃ γ, mat (rep π) γ = (g k : Matrix (Fin n) (Fin n) O) := fun k => (g k).2
    choose γ hγ using hg
    refine ⟨(∑ k, c k • mat ρ (γ k), fun j => ∑ k, c k * ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)), ?_⟩
    have := actsAs_sum e c (fun k => mat (rep π) (γ k)) (fun k => mat ρ (γ k))
      (fun k j => ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)) (fun k => actsAs_mat hdec (γ k))
    simpa only [hγ] using this
  refine ⟨fun a => if h : ∃ p : Matrix (Fin r) (Fin r) O × (Fin t → O), ActsAs e (a π) p.1 p.2
      then h.choose.1 else 0,
    fun j a => if h : ∃ p : Matrix (Fin r) (Fin r) O × (Fin t → O), ActsAs e (a π) p.1 p.2
      then h.choose.2 j else 0, ?_, ?_⟩
  · intro a ha u
    have hex := hact (a π) (eval_mem_span ha π)
    simp only [dif_pos hex]
    exact hex.choose_spec u
  · intro P
    have hP : P ∈ Submodule.span O (Set.range (mat ρ)) := hspan ▸ Submodule.mem_top
    obtain ⟨m, c, g, hsum⟩ := Submodule.mem_span_set'.mp hP
    have hg : ∀ k, ∃ γ, mat ρ γ = (g k : Matrix (Fin r) (Fin r) O) := fun k => (g k).2
    choose γ hγ using hg
    refine ⟨∑ k, c k • (fun x => mat (rep x) (γ k)), ?_, ?_⟩
    · exact inRing_sum _ fun k _ => inRing_smul (c k) (inRing_mat (γ k))
    · have hev : (∑ k, c k • (fun x => mat (rep x) (γ k))) π = ∑ k, c k • mat (rep π) (γ k) := by
        simp [Finset.sum_apply]
      have hA : ActsAs e ((∑ k, c k • (fun x => mat (rep x) (γ k))) π) (∑ k, c k • mat ρ (γ k))
          (fun j => ∑ k, c k * ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)) := by
        rw [hev]
        exact actsAs_sum e c (fun k => mat (rep π) (γ k)) (fun k => mat ρ (γ k))
          (fun k j => ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)) (fun k => actsAs_mat hdec (γ k))
      have hex : ∃ p : Matrix (Fin r) (Fin r) O × (Fin t → O),
          ActsAs e ((∑ k, c k • (fun x => mat (rep x) (γ k))) π) p.1 p.2 :=
        ⟨(∑ k, c k • mat ρ (γ k), fun j => ∑ k, c k * ((χ ((j : ℕ) + 1) (γ k) : Oˣ) : O)), hA⟩
      simp only [dif_pos hex]
      rw [ActsAs.unique hex.choose_spec hA, ← hsum]
      simp only [hγ]

end GlobalTheory.SpanBlockAction

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_block_action_of_decomposition : ∀ {Γ X O : Type} [Group Γ] [CommRing O] [IsDomain O] {n r t : ℕ} (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)) (ρ : Γ →* GL (Fin r) O) (χ : ℕ → (Γ →* Oˣ)) (π : X) (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))), Submodule.span O (Set.range (mat ρ)) = ⊤ → IsDecomp (t := t) (rep π) ρ χ e → ∃ (ψρ : (X → Matrix (Fin n) (Fin n) O) → Matrix (Fin r) (Fin r) O) (ψχ : Fin t → (X → Matrix (Fin n) (Fin n) O) → O), (∀ a, InRing T rep a → ∀ u, e (((a π).map (toFr O)).mulVec u) = (((ψρ a).map (toFr O)).mulVec (e u).1, fun c : Fin t => toFr O (ψχ c a) * (e u).2 c)) ∧ ∀ P : Matrix (Fin r) (Fin r) O, ∃ a, InRing T rep a ∧ ψρ a = P := by
  atlas_forward_decl GlobalTheory.SpanBlockAction.exists_block_action
end

section
namespace GlobalTheory.SpanMapTop

theorem map_mem_span {Γ A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}
    (f : Γ → Matrix (Fin r) (Fin r) A) (M : Matrix (Fin r) (Fin r) A)
    (hM : M ∈ Submodule.span A (Set.range f)) :
    M.map (algebraMap A B) ∈
      Submodule.span B (Set.range fun g => (f g).map (algebraMap A B)) := by
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact Submodule.subset_span ⟨g, rfl⟩
  | zero =>
    have : (0 : Matrix (Fin r) (Fin r) A).map (algebraMap A B) = 0 := by
      ext i j; simp
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : (x + y).map (algebraMap A B) = x.map (algebraMap A B) + y.map (algebraMap A B) := by
      ext i j; simp
    rw [this]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have : (a • x).map (algebraMap A B) = (algebraMap A B a) • x.map (algebraMap A B) := by
      ext i j; simp
    rw [this]; exact Submodule.smul_mem _ _ hx

theorem span_map_eq_top {Γ A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}
    (f : Γ → Matrix (Fin r) (Fin r) A) (h : Submodule.span A (Set.range f) = ⊤) :
    Submodule.span B (Set.range fun g => (f g).map (algebraMap A B)) = ⊤ := by
  rw [eq_top_iff]
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have h1 := map_mem_span (B := B) f (Matrix.single i j 1) (h ▸ Submodule.mem_top)
  have h2 : Matrix.single i j (M i j) =
      M i j • (Matrix.single i j (1 : A)).map (algebraMap A B) := by
    ext a b
    simp only [Matrix.single, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  rw [h2]
  exact Submodule.smul_mem _ _ h1

theorem span_mapRep_eq_top {Γ A : Type} [Group Γ] [CommRing A] {r : ℕ} {B : Type} [CommRing B]
    [Algebra A B] {ρ : Γ →* GL (Fin r) A}
    (h : Submodule.span A (Set.range (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat ρ)) = ⊤) :
    Submodule.span B
      (Set.range (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (Formalism.MainNotions.N.mapRep (algebraMap A B) ρ))) = ⊤ :=
  span_map_eq_top (B := B) (fun g => GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat ρ g) h

end GlobalTheory.SpanMapTop
end

section
noncomputable section

namespace GlobalTheory.ConsExists

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

section Base

theorem charZero_of_finite (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] : CharZero O := by
  have hinj : Function.Injective (algebraMap ℤ_[l] O) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra h
    have hp : (RingHom.ker (algebraMap ℤ_[l] O)).IsPrime := RingHom.ker_isPrime _
    have hm : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsMaximal := Ideal.IsPrime.isMaximal hp h
    have := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ_[l]) (⊥ : Ideal O) hm
    exact IsDiscreteValuationRing.not_isField O (Ring.isField_iff_maximal_bot.2 this)
  exact charZero_of_injective_algebraMap hinj

variable {Γ X A : Type} [Group Γ] [CommRing A] {n r t : ℕ}

theorem blockPol_map {B : Type} [CommRing B] (f : A →+* B) (e M : Matrix (Fin n) (Fin n) A) :
    (blockPol e M).map f = blockPol (e.map f) (M.map f) := by
  unfold blockPol
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h, Matrix.one_apply]

theorem overK_apply {k : ℕ} (σ : Γ →* GL (Fin k) A) (g : Γ) (u : Fin k → FractionRing A) :
    overK σ g u = ((mat σ g).map (toFr A)).mulVec u := rfl

theorem blockPol_coeff_mem {T : Subalgebra A (X → A)} {rep : X → (Γ →* GL (Fin n) A)}
    (hT : CharPolyIn T rep) {e M : X → Matrix (Fin n) (Fin n) A} (he : InRing T rep e)
    (hM : InRing T rep M) (j : ℕ) : (fun x => (blockPol (e x) (M x)).coeff j) ∈ T := by
  have := GlobalTheory.T.coeff_det_pencil_mem_heckeAlgebra T rep hT e (1 - e - M) he (inRing_sub (inRing_sub inRing_one he) hM) j
  convert this using 4 with x
  unfold blockPol
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h, Matrix.one_apply] <;> ring

theorem rank_const [IsDomain A] [IsLocalRing A] {T : Subalgebra A (X → A)}
    {rep : X → (Γ →* GL (Fin n) A)} (hl : IsLocalRing T)
    (hT : CharPolyIn T rep) {e : X → Matrix (Fin n) (Fin n) A} (he : InRing T rep e) (hee : e * e = e)
    (x y : X) : ((e x).map (toFr A)).rank = ((e y).map (toFr A)).rank := by
  refine GlobalTheory.T.idempotent_rank_const_of_charpoly_in_local_functions T e hl hee (fun j => ?_) x y
  have := blockPol_coeff_mem hT inRing_one he j
  convert this using 3 with x
  unfold blockPol Matrix.charpoly Matrix.charmatrix
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h, Matrix.one_apply]

theorem corner_act {K : Type} [Field K] (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K)))
    {E G : Matrix (Fin n) (Fin n) K} {P : Matrix (Fin r) (Fin r) K} {d : Fin t → K}
    (hE : ∀ u, e (E.mulVec u) = (0, (e u).2))
    (hG : ∀ u, e (G.mulVec u) = (P.mulVec (e u).1, fun c => d c * (e u).2 c)) (u : Fin n → K) :
    e ((E * G * E).mulVec u) = (0, fun c => d c * (e u).2 c) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hE, hG, hE]

theorem choice_facts [IsDomain A] [IsLocalRing A] {T : Subalgebra A (X → A)}
    {rep : X → (Γ →* GL (Fin n) A)} {ρ : X → (Γ →* GL (Fin r) A)} {χ : ℕ → (Γ →* Aˣ)} {π : X} {g0 : Γ}
    {L : ℕ} {eB e1 X0 : X → Matrix (Fin n) (Fin n) A} (hl : IsLocalRing T) (hT : CharPolyIn T rep)
    (h : IsChoice t T rep ρ χ π g0 L eB e1 X0) :
    (∀ x, ((eB x).map (toFr A)).rank = t) ∧ (∀ x, ((e1 x).map (toFr A)).rank = 1) ∧
    InRing T rep X0 ∧ eB * X0 = X0 ∧ X0 * eB = X0 ∧
    ∃ e, IsDecomp (t := t) (rep π) (ρ π) χ e ∧
      (∀ u, e (((eB π).map (toFr A)).mulVec u) = (0, (e u).2)) ∧
      ∀ u, e (((X0 π).map (toFr A)).mulVec u) =
        (0, fun c : Fin t => toFr A ((χ ((c : ℕ) + 1) g0 : Aˣ) : A) * (e u).2 c) := by
  obtain ⟨⟨hB, h1, hBB, h11, -, -⟩, ⟨e, hd, heB, ε, hε, he1⟩, ⟨ϖ, s, -, hs, hX⟩, -⟩ := h
  have hBx : ∀ x, eB x * eB x = eB x := congrFun hBB
  have hact : ∀ u, e (((X0 π).map (toFr A)).mulVec u) =
      (0, fun c : Fin t => toFr A ((χ ((c : ℕ) + 1) g0 : Aˣ) : A) * (e u).2 c) := by
    intro u
    have : X0 π = eB π * mat (rep π) g0 * eB π := by
      rw [hX]; simp [InMatrixCongruenceModule.eval_eq_zero hs]
    rw [this, Matrix.map_mul, Matrix.map_mul]
    exact corner_act e heB (hd g0) u
  refine ⟨fun x => ?_, fun x => ?_, ?_, ?_, ?_, e, hd, heB, hact⟩
  · rw [rank_const hl hT hB hBB x π]
    exact (GlobalTheory.T.rank_idempotentBlockCharPoly_of_projection e _ _ _ heB hact).1
  · rw [rank_const hl hT h1 h11 x π, GlobalTheory.T.rank_eq_of_mulVec_through_first_block e _ ε he1, hε]
  · rw [hX]
    exact inRing_add (inRing_mul (inRing_mul hB (inRing_mat g0)) hB) (inRing_smul _ (InMatrixCongruenceModule.inRing hB hs))
  · funext x
    rw [hX]
    simp only [Pi.mul_apply, mul_add, Matrix.mul_smul, (InMatrixCongruenceModule.corner hBB hs x).1, ← mul_assoc, hBx]
  · funext x
    rw [hX]
    simp only [Pi.mul_apply, add_mul, Matrix.smul_mul, (InMatrixCongruenceModule.corner hBB hs x).2, mul_assoc, hBx]

theorem span_top [IsLocalRing A] {ρ : Γ →* GL (Fin r) A}
    (h : AbsIrrSub (mapRep (IsLocalRing.residue A) ρ) ⊤) :
    Submodule.span A (Set.range (mat ρ)) = ⊤ :=
  GlobalTheory.T.span_repMatrix_eq_top_of_residue_span_eq_top ρ (GlobalTheory.T.span_repMatrix_eq_top_of_absIrreducible _ h)

theorem exists_choice (l : ℕ) [Fact l.Prime] [Finite X] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra ℤ_[l] A] [Module.Finite ℤ_[l] A] {T : Subalgebra A (X → A)} {Z : Finset X}
    {rep : X → (Γ →* GL (Fin n) A)} {ρ : X → (Γ →* GL (Fin r) A)} {χ : ℕ → (Γ →* Aˣ)}
    (hr : 2 ≤ r) (hS : HidaSetting t T Z rep ρ χ) {π : X} (hπ : π ∈ Z) (g0 : Γ)
    (hinj : Function.Injective fun c : Fin t => ((χ ((c : ℕ) + 1) g0 : Aˣ) : A)) (L : ℕ) :
    ∃ eB e1 X0, IsChoice t T rep ρ χ π g0 L eB e1 X0 := by
  haveI := charZero_of_finite l A
  obtain ⟨hl, hsep, -, hT, hirr, -, hdec, habs⟩ := hS
  obtain ⟨e, hd⟩ := hdec π hπ
  obtain ⟨eB, e1, hid, heB, he1⟩ := GlobalTheory.T.exists_orthogonal_idempotents_heckeSpan_rep l T rep (ρ π) χ π e hr (span_top (habs π hπ)) hd
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hat := GlobalTheory.T.rank_idempotentBlockCharPoly_of_projection e _ _ _ heB (corner_act e heB (hd g0))
  obtain ⟨s, hs, hroots⟩ := GlobalTheory.T.exists_heckeSpan_correction_distinct_eigenvalues (t := t) T rep π g0 eB (ϖ ^ L) (pow_ne_zero _ hϖ.ne_zero) hsep hirr
    hid.1 hid.2.2.1 (fun x => by rw [rank_const hl hT hid.1 hid.2.2.1 x π]; exact hat.1) (by
      rw [blockPol_map, Matrix.map_mul, Matrix.map_mul]
      refine hat.2 ▸ Polynomial.separable_prod_X_sub_C_iff.2 ?_
      exact (IsFractionRing.injective A (FractionRing A)).comp hinj)
  exact ⟨eB, e1, _, hid, ⟨e, hd, heB, he1⟩, ⟨ϖ, s, hϖ, hs, rfl⟩, hroots⟩

theorem blockPol_monic [IsDomain A] {e M : Matrix (Fin n) (Fin n) A} (hee : e * e = e)
    (hr : (e.map (toFr A)).rank = t) (h1 : e * M = M) (h2 : M * e = M) :
    ((blockPol e M).map (toFr A)).Monic ∧ ((blockPol e M).map (toFr A)).natDegree = t := by
  obtain ⟨a, b, -, -, h⟩ := GlobalTheory.T.idempotentBlockCharPoly_eq_charpoly_image (e.map (toFr A)) (by rw [← Matrix.map_mul, hee]) hr
  have := h (M.map (toFr A))
  rw [← Matrix.map_mul, ← Matrix.map_mul, h1, h2] at this
  rw [blockPol_map, this]
  exact ⟨Matrix.charpoly_monic _, by simp⟩

variable {B : Type} [CommRing B] [Algebra A B]

theorem inRing_map {T : Subalgebra A (X → A)} {T' : Subalgebra B (X → B)}
    {rep : X → (Γ →* GL (Fin n) A)} (hT : ∀ f ∈ T, (fun x => algebraMap A B (f x)) ∈ T')
    {a : X → Matrix (Fin n) (Fin n) A} (ha : InRing T rep a) :
    InRing T' (fun x => mapRep (algebraMap A B) (rep x)) (fun x => (a x).map (algebraMap A B)) := by
  obtain ⟨m, f, h, hf, rfl⟩ := ha
  refine ⟨m, fun k x => algebraMap A B (f k x), h, fun k => hT _ (hf k), ?_⟩
  funext x
  ext i j
  simp [Matrix.sum_apply, mat, mapRep]
  exact Finset.sum_congr rfl fun k _ => (Algebra.smul_def _ _).symm

theorem charPolyIn_map {T : Subalgebra A (X → A)} {T' : Subalgebra B (X → B)}
    {rep : X → (Γ →* GL (Fin n) A)} (hT : ∀ f ∈ T, (fun x => algebraMap A B (f x)) ∈ T')
    (h : CharPolyIn T rep) : CharPolyIn T' (fun x => mapRep (algebraMap A B) (rep x)) := by
  intro g d
  convert hT _ (h g d) using 2 with x
  rw [← Polynomial.coeff_map]
  congr 1
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases hab : a = b <;> simp [hab, Matrix.one_apply, mat, mapRep]

theorem span_top_map {ρ : Γ →* GL (Fin r) A} (h : Submodule.span A (Set.range (mat ρ)) = ⊤) :
    Submodule.span B (Set.range (mat (mapRep (algebraMap A B) ρ))) = ⊤ :=
  _root_.GlobalTheory.SpanMapTop.span_mapRep_eq_top h

end Base

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)

theorem two_le_r (R : Ranks) : 2 ≤ R.r := by
  have := R.two_le_m; have := R.m_add_three_le_k; unfold Ranks.r; omega

theorem two_le_ranks_t (R : Ranks) : 2 ≤ R.t := by
  have := R.rank_add_five_le; omega

theorem character_values_injective_length {g0 : GE N} (hg : IsInertiaCyclotomicGeneratorElement N i g0) :
    Set.InjOn (fun c => ((N.chi i c g0 : (N.O i)ˣ) : N.O i)) (Finset.Icc 1 R.t : Set ℕ) ∧
    lenUnit (O := N.O i) (N.l i) (N.O i ⧸ Ideal.span {∏ c ∈ Finset.Ioc 1 R.t,
      (((N.chi i 1 g0 : (N.O i)ˣ) : N.O i) - ((N.chi i c g0 : (N.O i)ˣ) : N.O i))}) = N.vdel i := by
  haveI := charZero_of_finite (N.l i) (N.O i)
  obtain ⟨-, v, hv⟩ := hg
  refine GlobalTheory.T.injOn_charValues_and_length_quotient (N.l i) (N.s0 i) R.t (cycZ (F := H.E) (Ω := N.Om) (N.l i) g0) v
    (fun c => N.chi i c g0) ?_ ?_ hv ?_
  · exact UpperTheory.KStar.S0.one_le_localLevel N i
  · exact UpperTheory.KStar.S0.two_le_localLevel_of_eq_two N i
  · intro c h1 h2
    rw [N.chi_def i c h1 h2]
    simp

def root {X O : Type} [Zero O] {t : ℕ} (β : X → Fin t → O) (c : ℕ) (x' : X × Equiv.Perm (Fin t)) : O :=
  if h : c - 1 < t then β x'.1 (x'.2 ⟨c - 1, h⟩) else 0

theorem root_succ {X O : Type} [Zero O] {t : ℕ} (β : X → Fin t → O) (c : Fin t)
    (x' : X × Equiv.Perm (Fin t)) : root β ((c : ℕ) + 1) x' = β x'.1 (x'.2 c) := by
  simp [root]

theorem exists_succ {t c : ℕ} (hc : c ∈ Finset.Icc 1 t) : ∃ a : Fin t, c = (a : ℕ) + 1 := by
  rw [Finset.mem_Icc] at hc
  exact ⟨⟨c - 1, by omega⟩, by simp; omega⟩

theorem prod_Icc_eq {M : Type} [CommMonoid M] (t : ℕ) (f : ℕ → M) :
    ∏ c ∈ Finset.Icc 1 t, f c = ∏ a : Fin t, f ((a : ℕ) + 1) := by
  rw [Fin.prod_univ_eq_prod_range (fun a => f (a + 1)) t, Finset.range_eq_Ico,
    Finset.prod_Ico_add' f 0 t 1]
  rfl

theorem exists_good (rep : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i) (g0 : GE N) (hg : IsInertiaCyclotomicGeneratorElement N i g0)
    (eB e1 X0 : N.X i → MatN N i) (hT : CharPolyIn (N.T i) rep)
    (hspan : Submodule.span (N.O i) (Set.range (mat (ρ π))) = ⊤)
    (hid : InRing (N.T i) rep eB ∧ InRing (N.T i) rep e1 ∧ eB * eB = eB ∧ e1 * e1 = e1 ∧ eB * e1 = 0 ∧
      e1 * eB = 0 ∧ (∀ x, ((eB x).map (toK N i)).rank = R.t) ∧ (∀ x, ((e1 x).map (toK N i)).rank = 1))
    (e : (Fin R.nV → KK N i) ≃ₗ[KK N i] ((Fin R.r → KK N i) × (Fin R.t → KK N i)))
    (hd : IsDecomp (t := R.t) (rep π) (ρ π) (N.chi i) e)
    (heB : ∀ u, e (((eB π).map (toK N i)).mulVec u) = (0, (e u).2))
    (hX : InRing (N.T i) rep X0) (hX1 : eB * X0 = X0) (hX2 : X0 * eB = X0)
    (hXπ : ∀ u, e (((X0 π).map (toK N i)).mulVec u) =
      (0, fun c : Fin R.t => toK N i ((N.chi i ((c : ℕ) + 1) g0 : (N.O i)ˣ) : N.O i) * (e u).2 c))
    (hβ : ∀ x, ∃ β : Fin R.t → N.O i, Function.Injective β ∧
      blockPol (eB x) (X0 x) = ∏ c, (Polynomial.X - Polynomial.C (β c))) :
    ∃ S : IdempotentChoiceData N i, S.g0 = g0 ∧ S.eB = eB ∧ S.e1 = e1 ∧ S.X0 = X0 ∧ GoodCongruenceObjects N rep ρ π S := by
  classical
  obtain ⟨hinjχ, hvdel⟩ := character_values_injective_length N i hg

  have hβ' : ∀ x, ∃ β : Fin R.t → N.O i, Function.Injective β ∧
      blockPol (eB x) (X0 x) = ∏ c, (Polynomial.X - Polynomial.C (β c)) ∧
      (x = π → ∀ c, β c = ((N.chi i ((c : ℕ) + 1) g0 : (N.O i)ˣ) : N.O i)) := by
    intro x
    by_cases hx : x = π
    · subst hx
      refine ⟨fun c => ((N.chi i ((c : ℕ) + 1) g0 : (N.O i)ˣ) : N.O i), fun a b hab => ?_, ?_,
        fun _ _ => rfl⟩
      · have := hinjχ (x₁ := (a : ℕ) + 1) (by simp) (x₂ := (b : ℕ) + 1) (by simp) hab
        exact Fin.ext (by omega)
      · apply Polynomial.map_injective (toK N i) (IsFractionRing.injective _ _)
        rw [blockPol_map, (GlobalTheory.T.rank_idempotentBlockCharPoly_of_projection e _ _ _ heB hXπ).2, Polynomial.map_prod]
        simp
    · obtain ⟨β, h1, h2⟩ := hβ x
      exact ⟨β, h1, h2, fun h => absurd h hx⟩
  choose β hβi hβp hβπ using hβ'
  have hrπ : ∀ c ∈ Finset.Icc 1 R.t, root β c (π, 1) = ((N.chi i c g0 : (N.O i)ˣ) : N.O i) := by
    intro c hc
    obtain ⟨a, rfl⟩ := exists_succ hc
    rw [root_succ]
    exact hβπ π rfl a
  have hset : (fun c => root β c) '' (Finset.Icc 1 R.t : Set ℕ) =
      Set.range fun c : Fin R.t => fun x' : N.X i × Equiv.Perm (Fin R.t) => β x'.1 (x'.2 c) := by
    ext f
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨a, rfl⟩ := exists_succ hc
      exact ⟨a, funext fun x' => (root_succ β a x').symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(a : ℕ) + 1, by simp, funext fun x' => root_succ β a x'⟩
  let T' : Subalgebra (N.O i) (N.X i × Equiv.Perm (Fin R.t) → N.O i) :=
    Algebra.adjoin (N.O i) ((fun f : N.X i → N.O i => fun x' => f x'.1) '' (N.T i : Set _) ∪
      (fun c => root β c) '' (Finset.Icc 1 R.t : Set ℕ))
  have hTT : ∀ f ∈ N.T i, (fun x' : N.X i × Equiv.Perm (Fin R.t) => f x'.1) ∈ T' :=
    fun f hf => Algebra.subset_adjoin (Or.inl ⟨f, hf, rfl⟩)
  have hT' : CharPolyIn T' (fun x' => rep x'.1) := fun h d => hTT _ (hT h d)
  obtain ⟨ψρ, ψχ, hψ, hψs⟩ := GlobalTheory.T.exists_block_action_of_decomposition T' (fun x' => rep x'.1) (ρ π) (N.chi i) (π, 1) e hspan hd
  have hpol : ∀ x' : N.X i × Equiv.Perm (Fin R.t),
      ∏ c ∈ Finset.Icc 1 R.t, (Polynomial.X - Polynomial.C (root β c x')) =
        blockPol (eB x'.1) (X0 x'.1) := by
    intro x'
    rw [prod_Icc_eq, hβp, ← Equiv.prod_comp x'.2 (fun c => Polynomial.X - Polynomial.C (β x'.1 c))]
    simp only [root_succ]
  have hE := fun x' : N.X i × Equiv.Perm (Fin R.t) =>
    GlobalTheory.T.idempotentBlock_rootFactors_rank_one_domain R.nV R.t (eB x'.1) (X0 x'.1) (fun c => root β c x') (two_le_ranks_t R)
      (congrFun hid.2.2.1 _) (congrFun hX1 _) (congrFun hX2 _) (by
        intro c hc c' hc' h
        obtain ⟨a, rfl⟩ := exists_succ hc
        obtain ⟨a', rfl⟩ := exists_succ hc'
        simp only [root_succ] at h
        rw [x'.2.injective (hβi _ h)]) (hpol x')
  refine ⟨{ eB := eB, e1 := e1, g0 := g0, X0 := X0, X' := N.X i × Equiv.Perm (Fin R.t), p := Prod.fst,
            T' := T', rr := root β, π' := (π, 1), e := e, ψρ := ψρ, ψχ := ψχ }, rfl, rfl, rfl, rfl,
    hid, hd, hψ, hψs, hg.1, hg.2, ⟨hX, hX1, hX2, hXπ⟩, ⟨hTT, ?_, rfl, ?_, ?_⟩, hpol, ⟨rfl, hrπ⟩,
    ⟨fun x' => (hE x').1, fun x' => (hE x').2, ?_, ?_⟩, GlobalTheory.T.coeff_det_generic_sum_mem_heckeAlgebra T' _ hT', GlobalTheory.T.blockDet_mem_heckeAlgebra_of_heckeSpan T' _ hT'⟩
  · exact fun c hc => Algebra.subset_adjoin (Or.inr ⟨c, hc, rfl⟩)
  · have := GlobalTheory.SplittingAlgebra.main (N.T i) R.t β hβi (N.T_sep i) (fun j => by
      simpa only [hβp] using blockPol_coeff_mem hT hid.1 hX j)
    simp only [← hset] at this
    exact this
  · intro x
    have : {x' : N.X i × Equiv.Perm (Fin R.t) // x'.1 = x} ≃ Equiv.Perm (Fin R.t) :=
      { toFun := fun a => a.1.2
        invFun := fun σ => ⟨(x, σ), rfl⟩
        left_inv := by rintro ⟨⟨y, σ⟩, rfl⟩; rfl
        right_inv := fun _ => rfl }
    exact (Nat.card_congr this).trans (by simp [Fintype.card_perm])
  · refine GlobalTheory.T.prod_other_root_factors_action_first_coordinate e (eB π) (X0 π) (fun c => root β c (π, 1)) (two_le_ranks_t R) heB (fun u => ?_)
    rw [hXπ]
    congr 1
    funext c
    rw [hrπ _ (by simp)]
  · rw [← hvdel]
    have : del51 N (⟨eB, e1, g0, X0, N.X i × Equiv.Perm (Fin R.t), Prod.fst, T', root β, (π, 1), e, ψρ, ψχ⟩ :
        IdempotentChoiceData N i) (π, 1) = ∏ c ∈ Finset.Ioc 1 R.t,
        (((N.chi i 1 g0 : (N.O i)ˣ) : N.O i) - ((N.chi i c g0 : (N.O i)ˣ) : N.O i)) := by
      refine Finset.prod_congr rfl fun c hc => ?_
      have h2 := two_le_ranks_t R
      show root β 1 (π, 1) - root β c (π, 1) = _
      rw [hrπ 1 (by simp; omega), hrπ c (Finset.Ioc_subset_Icc_self hc)]
    exact congrArg (fun z => lenUnit (O := N.O i) (N.l i) (N.O i ⧸ Ideal.span {z})) this

theorem consExist : ConsExist N i := by
  intro rep ρ A _ _ _ _ _ _ _ TA repA ρA χA _ hE hS
  obtain ⟨hinj, hTO, hrep, hρ, hχ⟩ := hE
  haveI := charZero_of_finite (N.l i) A
  refine ⟨fun π hπ g0 hg L => ?_, fun g0 L eB e1 X0 h => ?_, fun π hπ g0 L eB e1 X0 hg hc hroot => ?_⟩
  · refine exists_choice (N.l i) (two_le_r R) hS hπ g0 (fun a b hab => ?_) L
    have := (character_values_injective_length N i hg).1 (x₁ := (a : ℕ) + 1) (by simp) (x₂ := (b : ℕ) + 1) (by simp) (by
      simp only
      rw [hχ _ (by omega) (by omega), hχ _ (by omega) (by omega)]
      exact congrArg _ hab)
    exact Fin.ext (by omega)
  · obtain ⟨B, i1, i2, i3, i4, h1, h2, h3⟩ := GlobalTheory.T.exists_dvr_extension_for_monic_family (N.l i) (ι := N.Z i × N.X i) R.t
      (fun p => blockPol (eB p.1 p.2) (X0 p.1 p.2)) (fun p => by
        have hc := (h p.1 p.1.2).2
        obtain ⟨hr, -, -, hX1, hX2, -⟩ := choice_facts hS.1 hS.2.2.2.1 hc
        exact blockPol_monic (congrFun hc.1.2.2.1 _) (hr _) (congrFun hX1 _) (congrFun hX2 _))
    exact ⟨B, i1, i2, i3, i4, h1, h2, fun π hπ x => h3 (⟨π, hπ⟩, x)⟩
  · obtain ⟨hrB, hr1, hX, hX1, hX2, e, hd, heB, hXπ⟩ := choice_facts hS.1 hS.2.2.2.1 hc
    obtain ⟨⟨hB, h1, hBB, h11, hB1, h1B⟩, -, -, hdist⟩ := hc
    let φ : FractionRing A →+* KK N i := IsFractionRing.lift (g := (toK N i).comp (algebraMap A (N.O i)))
      ((IsFractionRing.injective (N.O i) (KK N i)).comp hinj)
    have hφ : ∀ a : A, φ (toFr A a) = toK N i (algebraMap A (N.O i) a) := fun a =>
      IsFractionRing.lift_algebraMap _ a
    have hφM : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin k) A),
        (M.map (algebraMap A (N.O i))).map (toK N i) = (M.map (toFr A)).map φ := by
      intro k M
      ext a b
      exact (hφ _).symm
    obtain ⟨e', he'⟩ := GlobalTheory.T.block_mulVec_decomposition_map_of_decomposition φ e
    have hTT : ∀ f ∈ TA, (fun x => algebraMap A (N.O i) (f x)) ∈ N.T i := by
      intro f hf
      rw [← Subalgebra.mem_toSubmodule, hTO]
      exact Submodule.subset_span ⟨f, hf, rfl⟩
    obtain rfl : rep = fun x => mapRep (algebraMap A (N.O i)) (repA x) := funext hrep
    have hmul : ∀ {a b c : N.X i → Matrix (Fin R.nV) (Fin R.nV) A}, a * b = c →
        (fun x => (a x).map (algebraMap A (N.O i))) * (fun x => (b x).map (algebraMap A (N.O i))) =
          fun x => (c x).map (algebraMap A (N.O i)) := by
      rintro a b c rfl
      funext x
      simp [Matrix.map_mul]
    obtain ⟨S, s0, s1, s2, s3, hG⟩ := exists_good N i _ ρ π g0 hg
      (fun x => (eB x).map (algebraMap A (N.O i))) (fun x => (e1 x).map (algebraMap A (N.O i)))
      (fun x => (X0 x).map (algebraMap A (N.O i))) (charPolyIn_map hTT hS.2.2.2.1)
      (by rw [hρ π hπ]; exact span_top_map (span_top (hS.2.2.2.2.2.2.2 π hπ)))
      ⟨inRing_map hTT hB, inRing_map hTT h1, hmul hBB, hmul h11,
        (hmul hB1).trans (by funext x; simp), (hmul h1B).trans (by funext x; simp),
        fun x => by rw [hφM, GlobalTheory.T.rank_map_ringHom, hrB], fun x => by rw [hφM, GlobalTheory.T.rank_map_ringHom, hr1]⟩
      e' (by
        intro g u
        rw [hρ π hπ, overK_apply, overK_apply]
        have := he' ((mat (repA π) g).map (toFr A)) ((mat (ρA π) g).map (toFr A)) _ (hd g) u
        rw [← hφM, ← hφM] at this
        refine this.trans ?_
        congr 1
        funext c
        rw [hφ, hχ _ (by omega) (by omega)])
      (by
        intro u
        have := he' ((eB π).map (toFr A)) 0 (fun _ => 1) (fun u => by rw [heB]; simp) u
        rw [← hφM] at this
        simpa using this)
      (inRing_map hTT hX) (hmul hX1) (hmul hX2)
      (by
        intro u
        have := he' ((X0 π).map (toFr A)) 0 _ (fun u => by rw [hXπ]; simp; rfl) u
        rw [← hφM] at this
        refine this.trans ?_
        congr 1
        · simp
        · funext c
          rw [hφ, hχ _ (by omega) (by omega)])
      (fun x => by
        obtain ⟨α, hα⟩ := hroot x
        obtain ⟨β, hβ, hP⟩ := GlobalTheory.T.exists_injective_roots_of_ncard_rootSet' R.t _ α hinj (hdist x) hα
        exact ⟨β, hβ, by rw [← blockPol_map, hP]⟩)
    exact ⟨S, s0, congrFun s1, congrFun s2, congrFun s3, hG⟩

end Record

end GlobalTheory.ConsExists

end
end
