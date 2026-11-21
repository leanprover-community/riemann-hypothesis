import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen
open scoped ENNReal TensorProduct

namespace GlobalTheory.TwSys.Test

section Ord
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]




end Ord

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

open Classical in

theorem exists_isCoord (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (M : ℕ) : ∃ d, IsCoord Y i M d := by
  let c : ∀ (Q : Finset (PlE D.host)) (P : PlE D.host), P ∈ Q → (GE N →* Multiplicative (ZMod (X.l i ^ M))) :=
    fun Q P hP => (AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ : ↥Q => ZMod (X.l i ^ M)) ⟨P, hP⟩)).comp
      (Y.delU i Q M)
  refine ⟨fun P => if h : ∃ Q, ConjCl (D := D) Q ∧ P ∈ Q then c h.choose P h.choose_spec.2 else 1, ?_⟩
  intro Q hQ P hP σ
  have h : ∃ Q, ConjCl (D := D) Q ∧ P ∈ Q := ⟨Q, hQ, hP⟩
  simp only [dif_pos h]
  have hU : ConjCl (D := D) (Q ∪ h.choose) := by
    intro P hP P' hc
    rcases Finset.mem_union.1 hP with h1 | h1
    · exact Finset.mem_union_left _ (hQ P h1 P' hc)
    · exact Finset.mem_union_right _ (h.choose_spec.1 P h1 P' hc)
  rw [Y.delU_res i M Q (Q ∪ h.choose) Finset.subset_union_left hQ hU σ P hP]
  exact (Y.delU_res i M h.choose (Q ∪ h.choose) Finset.subset_union_right h.choose_spec.1 hU σ P h.choose_spec.2).symm

open Classical in
theorem toLam_surjective (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] : Function.Surjective (toLam X i M ι) := by
  have hl : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ (Fact.out : (X.l i).Prime).ne_zero⟩
  have key : ∀ g : Del X i M ι, MonoidAlgebra.of (X.O0 i) (Del X i M ι) g ∈ (toLam X i M ι).range := by
    intro g
    refine ⟨∏ q, (1 + MvPolynomial.X q) ^ (Multiplicative.toAdd g q).val, ?_⟩
    simp only [toLam, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_prod, map_pow, map_add, map_one, MvPolynomial.aeval_X, add_sub_cancel]
    simp only [← map_pow, ← map_prod]
    congr 1
    apply Multiplicative.toAdd.injective
    ext q
    simp only [toAdd_prod, toAdd_pow, toAdd_ofAdd, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero]
    simp [nsmul_eq_mul]
  intro x
  have : x ∈ (toLam X i M ι).range := by
    induction x using MonoidAlgebra.induction_on with
    | of g => exact key g
    | add f g hf hg => exact add_mem hf hg
    | smul r f hf => exact Subalgebra.smul_mem _ hf r
  exact this


end GlobalTheory.TwSys.Test

end
