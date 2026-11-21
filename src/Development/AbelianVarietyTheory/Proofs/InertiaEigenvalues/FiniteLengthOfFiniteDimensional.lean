import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CharPolyRootsConstruction
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLocalHomAndIsAdicCompleteOfFiniteDvr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AutCongrContinuousCycInertia
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SemisimplificationConstituents
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstituentShape
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyEqOfSemisimplification
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsSemisimplificationOf
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfSimpleSSup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleSpanAfterMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbeddingIntegralContinuous
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusSplitPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeriesOfExact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepresentationDensityOfIsInternalConstituent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDecompositionBaseChange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDvrExtensionForMonicFamily
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixRankMapField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentRankConstOfCharpolyInLocalFunctions
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankIdempotentBlockCharPolyOfProjection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDetPencilMemHeckeAlgebra
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentBlockCharPolyEqCharpolyImage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducible
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsoluteIrreducibilitySpan

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_eq_of_semisimplification : ∀ {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (s : Representation k Γ W) (ρ : Representation k Γ V), GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s ρ → ∀ g, LinearMap.charpoly (s g) = LinearMap.charpoly (ρ g) := by
  first | exact @GlobalTheory.SemisimplificationCharpoly.charpoly_eq | exact GlobalTheory.SemisimplificationCharpoly.charpoly_eq | (intros; apply GlobalTheory.SemisimplificationCharpoly.charpoly_eq <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semisimplification' : ∀ {k Γ : Type} [Field k] [Group Γ] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k Γ V), ∃ s : Representation k Γ V, GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s ρ := by
  first | exact @GlobalTheory.Proof.exists_semisimplification'.exists_isSemisimplificationOf | exact GlobalTheory.Proof.exists_semisimplification'.exists_isSemisimplificationOf | (intros; apply GlobalTheory.Proof.exists_semisimplification'.exists_isSemisimplificationOf <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

noncomputable def bnMatRep {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W]
    [Module k W] {a : ℕ} (b : Module.Basis (Fin a) k W) (s : Representation k Γ W) :
    Γ →* GL (Fin a) k :=
  MonoidHom.toHomUnits
    (((LinearMap.toMatrixAlgEquiv b).toAlgHom.toRingHom.toMonoidHom).comp s)

theorem bnMatRep_val {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W]
    [Module k W] {a : ℕ} (b : Module.Basis (Fin a) k W) (s : Representation k Γ W) (g : Γ) :
    ((bnMatRep b s g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)
      = LinearMap.toMatrix b b (s g) := rfl

theorem bnMatRep_mulVec {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W]
    [Module k W] {a : ℕ} (b : Module.Basis (Fin a) k W) (s : Representation k Γ W) (g : Γ)
    (v : W) :
    ((bnMatRep b s g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).mulVec (b.equivFun v)
      = b.equivFun (s g v) := by
  rw [bnMatRep_val]
  exact LinearMap.toMatrix_mulVec_repr b b (s g) v

theorem bnMatRep_isSSRep {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W]
    [Module k W] {a : ℕ} (b : Module.Basis (Fin a) k W) (s : Representation k Γ W)
    (hs : IsSS s) : IsSSRep (bnMatRep b s) := by
  intro U hU
  obtain ⟨U', hU', hc⟩ := hs (U.comap (b.equivFun : W →ₗ[k] (Fin a → k))) (by
    intro g v hv
    have := hU g _ hv
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at this ⊢
    rw [← bnMatRep_mulVec]
    exact this)
  refine ⟨U'.map (b.equivFun : W →ₗ[k] (Fin a → k)), ?_, ?_⟩
  · rintro g _ ⟨v, hv, rfl⟩
    refine ⟨s g v, hU' g v hv, ?_⟩
    exact (bnMatRep_mulVec b s g v).symm
  · have h := (Submodule.orderIsoMapComap b.equivFun).isCompl hc
    have h1 : (Submodule.orderIsoMapComap b.equivFun)
        (U.comap (b.equivFun : W →ₗ[k] (Fin a → k))) = U :=
      Submodule.map_comap_eq_of_surjective b.equivFun.surjective U
    rw [h1] at h
    exact h

theorem brauerNesbitt_abstract_of_matrix : (∀ (Γ k : Type) [Group Γ] [Field k] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) k), IsSSRep ρ → IsSSRep ρ' → (∀ g, ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly = ((ρ' g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly) → ∃ h : GL (Fin a) k, ∀ g, ρ' g = h * ρ g * h⁻¹) → ∀ {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (s : Representation k Γ W) (s' : Representation k Γ V), IsSS s → IsSS s' → (∀ g, LinearMap.charpoly (s g) = LinearMap.charpoly (s' g)) → ∃ e : W ≃ₗ[k] V, ∀ g v, e (s g v) = s' g (e v) := by
  intro H k Γ _ _ W _ _ _ V _ _ _ s s' hs hs' hc
  have hdim : Module.finrank k V = Module.finrank k W := by
    rw [← LinearMap.charpoly_natDegree (s 1), ← LinearMap.charpoly_natDegree (s' 1), hc]
  let b : Module.Basis (Fin (Module.finrank k W)) k W := Module.finBasis k W
  let b' : Module.Basis (Fin (Module.finrank k W)) k V := Module.finBasisOfFinrankEq k V hdim
  obtain ⟨h, hh⟩ := H Γ k _ (bnMatRep b s) (bnMatRep b' s') (bnMatRep_isSSRep b s hs)
    (bnMatRep_isSSRep b' s' hs') (by
      intro g
      rw [bnMatRep_val, bnMatRep_val, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix, hc])
  let m : (Fin (Module.finrank k W) → k) ≃ₗ[k] (Fin (Module.finrank k W) → k) :=
    (Matrix.GeneralLinearGroup.toLin h).toLinearEquiv
  have hm : ∀ x, m x = (h : Matrix _ _ k).mulVec x := fun x => rfl
  refine ⟨b.equivFun.trans (m.trans b'.equivFun.symm), fun g v => ?_⟩
  apply b'.equivFun.injective
  rw [← bnMatRep_mulVec]
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, hm]
  rw [← bnMatRep_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul,
    ← Units.val_mul, hh g, inv_mul_cancel_right]

end GlobalTheory
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semisimplification_unique_up_to_conj : (∀ (Γ k : Type) [Group Γ] [Field k] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) k), IsSSRep ρ → IsSSRep ρ' → (∀ g, ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly = ((ρ' g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly) → ∃ h : GL (Fin a) k, ∀ g, ρ' g = h * ρ g * h⁻¹) → ∀ {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (s : Representation k Γ W) (s' : Representation k Γ V), IsSS s → IsSS s' → (∀ g, LinearMap.charpoly (s g) = LinearMap.charpoly (s' g)) → ∃ e : W ≃ₗ[k] V, ∀ g v, e (s g v) = s' g (e v) := by
  atlas_forward_decl GlobalTheory.brauerNesbitt_abstract_of_matrix
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem isSemisimplificationOf_of_equiv : ∀ {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W] {W' : Type} [AddCommGroup W'] [Module k W'] [FiniteDimensional k W'] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (s : Representation k Γ W) (s' : Representation k Γ W') (ρ : Representation k Γ V) (e : W ≃ₗ[k] W'), (∀ g v, e (s g v) = s' g (e v)) → GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s' ρ → GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s ρ := by
  intro k Γ _ _ W _ _ _ W' _ _ _ V _ _ _ s s' ρ e he h
  obtain ⟨hss, m, Ws, f, hst, hint, hfil⟩ := h
  let o : Submodule k W' ≃o Submodule k W := Submodule.orderIsoMapComap e.symm
  have ho : ∀ (U : Submodule k W') (v : W), v ∈ o U ↔ e v ∈ U := by
    intro U v
    change v ∈ U.map (e.symm : W' →ₗ[k] W) ↔ _
    rw [Submodule.mem_map_equiv]
    simp
  have ho' : ∀ (U : Submodule k W) (v : W), e v ∈ o.symm U ↔ v ∈ U := by
    intro U v
    rw [← ho, o.apply_symm_apply]
  have hstab : ∀ U, Stable s' U → Stable s (o U) := by
    intro U hU g v hv
    rw [ho] at hv ⊢
    rw [he]
    exact hU g _ hv
  refine ⟨?_, m, fun j => o (Ws j), e.trans f, fun j => hstab _ (hst j), ?_, ?_⟩
  · intro U hU
    have hU' : Stable s' (o.symm U) := by
      intro g w hw
      obtain ⟨v, rfl⟩ := e.surjective w
      rw [← he, ho']
      exact hU g v ((ho' U v).1 hw)
    obtain ⟨U', h1, h2⟩ := hss _ hU'
    refine ⟨o U', hstab _ h1, ?_⟩
    have := o.isCompl h2
    rwa [o.apply_symm_apply] at this
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hint ⊢
    refine ⟨iSupIndep.map_orderIso o hint.1, ?_⟩
    rw [← o.map_iSup, hint.2, o.map_top]
  · intro j g v hv
    rw [ho] at hv
    obtain ⟨w, hw, hw'⟩ := hfil j g _ hv
    refine ⟨e.symm w, ?_, ?_⟩
    · have : (⨆ j' ∈ Set.Iio j, o (Ws j')) = o (⨆ j' ∈ Set.Iio j, Ws j') := by
        simp only [o.map_iSup]
      change e.symm w ∈ (⨆ j' ∈ Set.Iio j, o (Ws j'))
      rw [this, ho]
      simpa using hw
    · simpa [he] using hw'

end GlobalTheory
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semisimplification_of_linear_equiv : ∀ {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W] {W' : Type} [AddCommGroup W'] [Module k W'] [FiniteDimensional k W'] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (s : Representation k Γ W) (s' : Representation k Γ W') (ρ : Representation k Γ V) (e : W ≃ₗ[k] W'), (∀ g v, e (s g v) = s' g (e v)) → GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s' ρ → GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s ρ := by
  atlas_forward_decl GlobalTheory.isSemisimplificationOf_of_equiv
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semisimple_of_simple_sSup : ∀ {k Γ : Type} [Field k] [Group Γ] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k Γ V) (S : Set (Submodule k V)), (∀ U ∈ S, Stable ρ U ∧ ∀ U' : Submodule k V, U' ≤ U → Stable ρ U' → U' = ⊥ ∨ U' = U) → sSup S = ⊤ → IsSS ρ := by
  first | exact @GlobalTheory.isSS_of_sSup_irreducible_eq_top | exact GlobalTheory.isSS_of_sSup_irreducible_eq_top | (intros; apply GlobalTheory.isSS_of_sSup_irreducible_eq_top <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem isSS_blockSum_of_isIrred {k Γ : Type} [Field k] [Group Γ] {r t : ℕ}
    (ρ : Γ →* Matrix (Fin r) (Fin r) k) (χ : Fin t → (Γ →* kˣ))
    (hρ : GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsIrred (matRep ρ)) : IsSS (GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum ρ χ) := by
  classical
  refine isSS_of_sSup_irreducible_eq_top _
    ({LinearMap.range (LinearMap.inl k (Fin r → k) (Fin t → k))} ∪
      Set.range fun c : Fin t =>
        Submodule.span k {((0, Pi.single c 1) : (Fin r → k) × (Fin t → k))}) ?_ ?_
  · rintro U (rfl | ⟨c, rfl⟩)
    · have key : ∀ g (v : Fin r → k), GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum ρ χ g
          (LinearMap.inl k (Fin r → k) (Fin t → k) v) =
          LinearMap.inl k (Fin r → k) (Fin t → k) (matRep ρ g v) := by
        intro g v
        rw [GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum_apply]
        refine Prod.ext rfl (funext fun c => ?_)
        simp
      refine ⟨?_, fun U' hle hU' => ?_⟩
      · rintro g _ ⟨v, rfl⟩
        exact ⟨_, (key g v).symm⟩
      · have hst : Stable (matRep ρ) (U'.comap (LinearMap.inl k (Fin r → k) (Fin t → k))) := by
          intro g v hv
          rw [Submodule.mem_comap, ← key]
          exact hU' g _ hv
        have hmap := Submodule.map_comap_eq_self hle
        rcases hρ.2 _ hst with h | h
        · left
          rw [← hmap, h, Submodule.map_bot]
        · right
          rw [← hmap, h, Submodule.map_top]
    · refine ⟨?_, fun U' hle _ => ?_⟩
      · intro g v hv
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
        refine Submodule.mem_span_singleton.2 ⟨a * ((χ c g : kˣ) : k), ?_⟩
        rw [GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum_apply]
        refine Prod.ext ?_ (funext fun c' => ?_)
        · simp
        · by_cases h : c' = c
          · subst h
            simp [mul_comm]
          · simp [h]
      · have hne : ((0, Pi.single c 1) : (Fin r → k) × (Fin t → k)) ≠ 0 := by
          intro h
          have := congrFun (congrArg Prod.snd h) c
          simp at this
        exact (nonzero_span_atom _ hne).le_iff.1 hle
  · rw [eq_top_iff]
    rintro ⟨v, w⟩ -
    have hdec : ((v, w) : (Fin r → k) × (Fin t → k)) =
        LinearMap.inl k (Fin r → k) (Fin t → k) v +
          ∑ c : Fin t, w c • ((0, Pi.single c 1) : (Fin r → k) × (Fin t → k)) := by
      refine Prod.ext ?_ (funext fun c' => ?_)
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    rw [hdec]
    refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_)
    · exact Submodule.mem_sSup.2 fun N hN => hN _ (Or.inl rfl) ⟨v, rfl⟩
    · exact Submodule.mem_sSup.2 fun N hN =>
        hN _ (Or.inr ⟨c, rfl⟩) (Submodule.mem_span_singleton_self _)

end GlobalTheory
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_sum_semisimple : ∀ {k Γ : Type} [Field k] [Group Γ] {r t : ℕ} (ρ : Γ →* Matrix (Fin r) (Fin r) k) (χ : Fin t → (Γ →* kˣ)), GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsIrred (matRep ρ) → IsSS (GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum ρ χ) := by
  atlas_forward_decl GlobalTheory.isSS_blockSum_of_isIrred
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_span_after_map : ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) (hW : Stable (matRep ((Units.coeHom _).comp ρ)) W), W ≠ ⊥ → Submodule.span k (Set.range fun g => (matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) = ⊤ → IsIrrSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k)))) := by
  first | exact @GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top | exact GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top | (intros; apply GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.Proof.span_restrict_eq_top_of_simple

theorem span_eq_top_of_equivariant {k Γ : Type} [Field k] [Group Γ] {V : Type} [AddCommGroup V]
    [Module k V] {Y : Type} [AddCommGroup Y] [Module k Y] (ρ : Representation k Γ V)
    (σ : Γ → (Y →ₗ[k] Y)) (hσ : Submodule.span k (Set.range σ) = ⊤)
    (p : V →ₗ[k] Y) (hp : ∀ g v, p (ρ g v) = σ g (p v))
    (W : Submodule k V) (hW : Stable ρ W) (w0 : V) (hw0 : w0 ∈ W) (hpw : p w0 ≠ 0)
    (hirr : ∀ U : Submodule k V, U ≤ W → Stable ρ U → U = ⊥ ∨ U = W) :
    Submodule.span k (Set.range fun g => (ρ g).restrict (hW g)) = ⊤ := by
  have hker : W ⊓ LinearMap.ker p = ⊥ := by
    rcases hirr (W ⊓ LinearMap.ker p) inf_le_left (by
      intro g v hv
      refine ⟨hW g v hv.1, ?_⟩
      have h2 : p v = 0 := hv.2
      show p (ρ g v) = 0
      rw [hp, h2, map_zero]) with h | h
    · exact h
    · exfalso
      apply hpw
      have : w0 ∈ W ⊓ LinearMap.ker p := by rw [h]; exact hw0
      exact this.2
  have hinj : Function.Injective (p.domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro w hw
    have h1 : (w : V) ∈ W ⊓ LinearMap.ker p := ⟨w.2, hw⟩
    rw [hker] at h1
    exact Subtype.ext h1
  have hsurj : Function.Surjective (p.domRestrict W) := by
    intro y
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hpw
    have key : ∀ f ∈ Submodule.span k (Set.range σ), f (p w0) ∈ LinearMap.range (p.domRestrict W) := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        exact ⟨⟨ρ g w0, hW g w0 hw0⟩, hp g w0⟩
      | zero => exact Submodule.zero_mem _
      | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
      | smul a x _ hx => exact Submodule.smul_mem _ a hx
    have := key (φ.smulRight y) (by rw [hσ]; trivial)
    simpa [hφ] using this
  let e : W ≃ₗ[k] Y := LinearEquiv.ofBijective (p.domRestrict W) ⟨hinj, hsurj⟩
  have he : ∀ g, e.symm.conj (σ g) = (ρ g).restrict (hW g) := by
    intro g
    ext1 w
    apply e.injective
    rw [LinearEquiv.conj_apply_apply]
    simp only [LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
    exact (hp g w).symm
  have hr : (Set.range fun g => (ρ g).restrict (hW g))
      = (e.symm.conj : Module.End k Y →ₗ[k] Module.End k W) '' Set.range σ := by
    rw [← Set.range_comp]
    congr 1
    funext g
    exact (he g).symm
  rw [hr, ← Submodule.map_span, hσ, Submodule.map_top, LinearEquiv.range]

theorem span_restrict_eq_top_of_irreducible : ∀ {k Γ : Type} [Field k] [Group Γ] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k Γ V), AbsIrrDistinct ρ → ∀ (W : Submodule k V) (hW : Stable ρ W), W ≠ ⊥ → (∀ U : Submodule k V, U ≤ W → Stable ρ U → U = ⊥ ∨ U = W) → Submodule.span k (Set.range fun g => (ρ g).restrict (hW g)) = ⊤ := by
  intro k Γ _ _ V _ _ _ ρ h W hW hne hirr
  obtain ⟨ι, _, _, Vs, hs, hI, -, hspan, -⟩ := h
  let D := LinearEquiv.ofBijective (DirectSum.coeLinearMap Vs) hI
  let p : ∀ j, V →ₗ[k] Vs j := fun j =>
    (DirectSum.component k ι (fun j => Vs j) j).comp D.symm.toLinearMap
  have hpdef : ∀ j v, p j v = D.symm v j := fun _ _ => rfl
  have hp : ∀ j g v, p j (ρ g v) = (ρ g).restrict (hs j g) (p j v) := by
    intro j g v
    have hv : v ∈ ⨆ i, Vs i := by rw [hI.submodule_iSup_eq_top]; trivial
    induction hv using Submodule.iSup_induction' with
    | mem i x hx =>
      by_cases hij : i = j
      · subst hij
        rw [hpdef, hpdef, hI.ofBijective_coeLinearMap_of_mem hx,
          hI.ofBijective_coeLinearMap_of_mem (hs i g x hx)]
        rfl
      · rw [hpdef, hpdef, hI.ofBijective_coeLinearMap_of_mem_ne hij hx,
          hI.ofBijective_coeLinearMap_of_mem_ne hij (hs i g x hx), map_zero]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
  obtain ⟨w0, hw0, hw0'⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have : ∃ j, p j w0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hw0'
    have : D.symm w0 = 0 := DFinsupp.ext hcon
    simpa using this
  obtain ⟨j, hj⟩ := this
  exact span_eq_top_of_equivariant ρ _ (hspan j) (p j) (hp j) W hW w0 hw0 hj hirr

end GlobalTheory.Proof.span_restrict_eq_top_of_simple
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_restrict_eq_top_of_simple : ∀ {k Γ : Type} [Field k] [Group Γ] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (ρ : Representation k Γ V), AbsIrrDistinct ρ → ∀ (W : Submodule k V) (hW : Stable ρ W), W ≠ ⊥ → (∀ U : Submodule k V, U ≤ W → Stable ρ U → U = ⊥ ∨ U = W) → Submodule.span k (Set.range fun g => (ρ g).restrict (hW g)) = ⊤ := by
  atlas_forward_decl GlobalTheory.Proof.span_restrict_eq_top_of_simple.span_restrict_eq_top_of_irreducible
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.IrredOfAbsIrred

theorem isIrred_of_absIrrSub :
    ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k), AbsIrrSub ρ ⊤ → GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsIrred (matRep ((Units.coeHom _).comp ρ)) := by
  intro k Γ _ _ a ρ h
  classical
  obtain ⟨h0, -, h2⟩ := h
  set K := AlgebraicClosure k
  set f := algebraMap k K with hf
  have hinj : Function.Injective f := f.injective
  refine ⟨fun hb => h0 ?_, fun U hU => ?_⟩
  · rw [hb, Submodule.span_eq_bot]
    rintro _ ⟨v, hv, rfl⟩
    have : v = 0 := by simpa using hv
    subst this
    ext x
    simp
  · have hst : IsInv (mapRep f ρ) (Submodule.span K ((fun v : Fin a → k => f ∘ v) '' (U : Set (Fin a → k)))) := by
      intro g v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨u, hu, rfl⟩ := hx
        refine Submodule.subset_span ⟨(ρ g : Matrix (Fin a) (Fin a) k).mulVec u, hU g u hu, ?_⟩
        ext p
        exact RingHom.map_mulVec f _ u p
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx
    rcases h2 _ (Submodule.span_mono (Set.image_mono (fun _ _ => trivial))) hst with h1 | h1
    · left
      rw [Submodule.span_eq_bot] at h1
      rw [eq_bot_iff]
      intro v hv
      have := h1 _ ⟨v, hv, rfl⟩
      rw [Submodule.mem_bot]
      ext p
      apply hinj
      simpa using congrFun this p
    · right
      by_contra hne
      obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
      let F : (Fin a → K) →ₗ[K] K :=
        { toFun := fun X => ∑ i, X i * f (φ (Pi.single i 1))
          map_add' := fun X Y => by simp [add_mul, Finset.sum_add_distrib]
          map_smul' := fun c X => by
            simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
            exact (Finset.mul_sum _ _ _).symm }
      have hF : ∀ X : Fin a → k, F (f ∘ X) = f (φ X) := by
        intro X
        conv_rhs => rw [← Finset.univ_sum_single X]
        simp only [map_sum]
        change ∑ i, f (X i) * f (φ (Pi.single i 1)) = _
        refine Finset.sum_congr rfl fun i _ => ?_
        have : Pi.single i (X i) = X i • (Pi.single i (1 : k) : Fin a → k) := by
          rw [← Pi.single_smul, smul_eq_mul, mul_one]
        rw [this, map_smul, smul_eq_mul, map_mul]
      have hker : Submodule.span K ((fun v : Fin a → k => f ∘ v) '' (U : Set (Fin a → k))) ≤
          LinearMap.ker F := by
        rw [Submodule.span_le]
        rintro _ ⟨u, hu, rfl⟩
        have : φ u = 0 := hφ hu
        simp only [SetLike.mem_coe, LinearMap.mem_ker, hF, this, map_zero]
      apply hφ0
      refine LinearMap.ext fun X => ?_
      have h3 : F (f ∘ X) = 0 := hker (by rw [h1]; exact Submodule.subset_span ⟨X, trivial, rfl⟩)
      rw [hF] at h3
      exact hinj (by rw [h3]; simp)

end GlobalTheory.IrredOfAbsIrred
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIrred_of_absIrr : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k), AbsIrrSub ρ ⊤ → GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsIrred (matRep ((Units.coeHom _).comp ρ)) := by
  atlas_forward_decl GlobalTheory.IrredOfAbsIrred.isIrred_of_absIrrSub
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem absIrrDistinct_of_semilinearEquiv {k L Γ V V' : Type} [Field k] [Field L] [Group Γ]
    [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module L V']
    {σ : k →+* L} {τ : L →+* k} [RingHomInvPair σ τ] [RingHomInvPair τ σ]
    (ρ : Representation k Γ V) (ρ' : Representation L Γ V') (E : V ≃ₛₗ[σ] V')
    (hE : ∀ g v, E (ρ g v) = ρ' g (E v)) (h : AbsIrrDistinct ρ) : AbsIrrDistinct ρ' := by
  obtain ⟨ι, hι, hd, Vs, hs, hint, hne, hspan, hdist⟩ := h
  have hs' : ∀ j, Stable ρ' ((Vs j).map (E : V →ₛₗ[σ] V')) := by
    rintro j g _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, hs j g v hv, hE g v⟩
  have hcomm : ∀ j g (v : Vs j), E.submoduleMap (Vs j) ((ρ g).restrict (hs j g) v)
      = (ρ' g).restrict (hs' j g) (E.submoduleMap (Vs j) v) := by
    intro j g v
    apply Subtype.ext
    exact hE g v
  refine ⟨ι, hι, hd, fun j => (Vs j).map (E : V →ₛₗ[σ] V'), hs', ?_, ?_, ?_, ?_⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hint ⊢
    refine ⟨hint.1.map_orderIso (Submodule.orderIsoMapComap E), ?_⟩
    rw [← Submodule.map_iSup, hint.2, Submodule.map_top, LinearEquiv.range]
  · intro j hj
    exact hne j ((Submodule.orderIsoMapComap E).injective (by simpa using hj))
  · intro j
    have hc : ∀ g, (E.submoduleMap (Vs j)).conj ((ρ g).restrict (hs j g))
        = (ρ' g).restrict (hs' j g) := by
      intro g
      ext1 w
      obtain ⟨v, rfl⟩ := (E.submoduleMap (Vs j)).surjective w
      rw [← hcomm]
      simp [LinearEquiv.conj_apply]
    have h1 := congrArg (Submodule.map ((E.submoduleMap (Vs j)).conj : Module.End k (Vs j) →ₛₗ[σ]
      Module.End L ((Vs j).map (E : V →ₛₗ[σ] V')))) (hspan j)
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range, ← Set.range_comp] at h1
    rw [← h1]
    congr 2
    funext g
    exact (hc g).symm
  · intro j j' hjj e he
    refine hdist j j' hjj
      (((E.submoduleMap (Vs j)).trans e).trans (E.submoduleMap (Vs j')).symm) ?_
    intro g v
    apply (E.submoduleMap (Vs j')).injective
    rw [hcomm]
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [hcomm, he]

theorem absIrrDistinct_matRep_mapM_of_surjective : ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L), Function.Surjective f → ∀ {a : ℕ} (M : Γ →* Matrix (Fin a) (Fin a) k), AbsIrrDistinct (matRep M) → AbsIrrDistinct (matRep (mapM f M)) := by
  intro k Γ _ _ L _ f hf a M h
  let s : k ≃+* L := RingEquiv.ofBijective f ⟨f.injective, hf⟩
  haveI := RingHomInvPair.of_ringEquiv s
  haveI := RingHomInvPair.of_ringEquiv_symm s
  let E : (Fin a → k) ≃ₛₗ[(s : k →+* L)] (Fin a → L) :=
    { toFun := fun v i => s (v i)
      invFun := fun v i => s.symm (v i)
      map_add' := fun v w => by ext i; simp
      map_smul' := fun c v => by ext i; simp
      left_inv := fun v => by ext i; simp
      right_inv := fun v => by ext i; simp }
  refine absIrrDistinct_of_semilinearEquiv _ _ E ?_ h
  intro g v
  ext i
  exact RingHom.map_mulVec f (M g) v i

end GlobalTheory
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absIrrDistinct_map_surjective : ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L), Function.Surjective f → ∀ {a : ℕ} (M : Γ →* Matrix (Fin a) (Fin a) k), AbsIrrDistinct (matRep M) → AbsIrrDistinct (matRep (mapM f M)) := by
  atlas_forward_decl GlobalTheory.absIrrDistinct_matRep_mapM_of_surjective
end

section
section
namespace GlobalTheory

theorem continuous_of_continuous_mul_left_adic {O Γ : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O]
    (h : IsAdic (IsLocalRing.maximalIdeal O)) [TopologicalSpace Γ] {d : O} (hd : d ≠ 0)
    (f : Γ → O) (hf : Continuous fun g => d * f g) : Continuous f := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ
  rw [continuous_iff_continuousAt]
  intro g₀
  have h1 : Filter.Tendsto (fun g => (u * ϖ ^ m) * f g - (u * ϖ ^ m) * f g₀) (nhds g₀) (nhds 0) :=
    tendsto_sub_nhds_zero_iff.mpr (hf.tendsto g₀)
  have h2 : Filter.Tendsto (fun g => f g - f g₀) (nhds g₀) (nhds 0) := by
    rw [h.hasBasis_nhds_zero.tendsto_right_iff] at h1 ⊢
    intro k _
    filter_upwards [h1 (k + m) trivial] with g hg
    simp only [SetLike.mem_coe, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hg ⊢
    rw [← mul_sub, pow_add, mul_assoc, Units.dvd_mul_left, mul_comm (ϖ ^ k)] at hg
    exact (mul_dvd_mul_iff_left (pow_ne_zero m hϖ.ne_zero)).mp hg
  exact tendsto_sub_nhds_zero_iff.mp h2

theorem continuous_block_of_continuous_matrix : ∀ {O Γ : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ [TopologicalSpace Γ] {n r t : ℕ} (M : Γ → Matrix (Fin n) (Fin n) O) (P : Γ → Matrix (Fin r) (Fin r) O) (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))), Continuous M → (∀ g v, (e (((M g).map (algebraMap O (FractionRing O))).mulVec v)).1 = ((P g).map (algebraMap O (FractionRing O))).mulVec (e v).1) → Continuous P := by
  intro O Γ _ _ _ _ _ h _ n r t M P e hM hP
  refine continuous_matrix fun i j => ?_
  let v : Fin n → FractionRing O := e.symm (Pi.single j 1, 0)
  let w : Fin n → FractionRing O := fun k => (e (Pi.single k 1)).1 i
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) v
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) w
  choose v' hv' using hb
  choose w' hw' using hc
  have hφ : ∀ x : Fin n → FractionRing O, (e x).1 i = ∑ k, x k * w k := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ' x]
    simp [map_sum, Prod.fst_sum, Finset.sum_apply, w]
  have key : ∀ g, ((b : O) * (c : O)) * P g i j = ∑ k, (∑ l, M g k l * v' l) * w' k := by
    intro g
    apply IsFractionRing.injective O (FractionRing O)
    have h1 := congrFun (hP g v) i
    rw [hφ] at h1
    simp only [v, LinearEquiv.apply_symm_apply, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.map_apply] at h1
    simp only [map_mul, map_sum, hv', hw', ← h1, Algebra.smul_def, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [v]
    ring
  refine continuous_of_continuous_mul_left_adic h
    (mul_ne_zero (nonZeroDivisors.coe_ne_zero b) (nonZeroDivisors.coe_ne_zero c)) _ ?_
  simp only [key]
  fun_prop

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_decomposition_fraction_field : ∀ {O Γ : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ [TopologicalSpace Γ] {n r t : ℕ} (M : Γ → Matrix (Fin n) (Fin n) O) (P : Γ → Matrix (Fin r) (Fin r) O) (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))), Continuous M → (∀ g v, (e (((M g).map (algebraMap O (FractionRing O))).mulVec v)).1 = ((P g).map (algebraMap O (FractionRing O))).mulVec (e v).1) → Continuous P := by
  atlas_forward_decl GlobalTheory.continuous_block_of_continuous_matrix
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedding_integral_continuous : ∀ (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (ι : O →+* PadicAlgCl l), (∀ z : ℤ_[l], ι (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l])) → (∀ a, ‖ι a‖ ≤ 1) ∧ (∀ a ∈ IsLocalRing.maximalIdeal O, ‖ι a‖ < 1) ∧ Continuous ι := by
  first | exact @GlobalTheory.padicAlgCl_embedding_bounded_continuous | exact GlobalTheory.padicAlgCl_embedding_bounded_continuous | (intros; apply GlobalTheory.padicAlgCl_embedding_bounded_continuous <;> assumption)
end

section
section
namespace GlobalTheory

theorem exists_finiteDimensional_intermediateField_eq_range_fractionRing
    (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] (ι : FractionRing O →+* PadicAlgCl l)
    (hι : ∀ z : ℤ_[l], ι (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) =
      algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l])) :
    ∃ L : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] L ∧
      ∀ y, y ∈ L ↔ ∃ a, ι a = y := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := O)
  let f : O → PadicAlgCl l := fun o => ι (algebraMap O (FractionRing O) o)
  let S : Set (PadicAlgCl l) := f '' (s : Set O)
  haveI : Finite S := (s.finite_toSet.image f).to_subtype
  have hQ : ∀ x : ℚ_[l], algebraMap ℚ_[l] (PadicAlgCl l) x ∈ ι.fieldRange := by
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[l]) x
    rw [map_div₀]
    refine ι.fieldRange.div_mem ⟨_, hι a⟩ ⟨_, hι b⟩
  refine ⟨IntermediateField.adjoin ℚ_[l] S, ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[l]) x).isIntegral)
  · have hO : ∀ o : O, f o ∈ IntermediateField.adjoin ℚ_[l] S := by
      intro o
      have ho : o ∈ Submodule.span ℤ_[l] (s : Set O) := by rw [hs]; trivial
      induction ho using Submodule.span_induction with
      | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
      | zero => simp [f]
      | add x y _ _ hx hy =>
        simp only [f, map_add]
        exact add_mem hx hy
      | smul z x _ hx =>
        simp only [f, Algebra.smul_def, map_mul, hι]
        exact mul_mem (IntermediateField.algebraMap_mem _ _) hx
    intro y
    constructor
    · intro hy
      have hle : IntermediateField.adjoin ℚ_[l] S ≤ ι.fieldRange.toIntermediateField hQ := by
        rw [IntermediateField.adjoin_le_iff]
        rintro _ ⟨o, -, rfl⟩
        exact ⟨_, rfl⟩
      exact hle hy
    · rintro ⟨a, rfl⟩
      obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := O) a
      rw [map_div₀]
      exact div_mem (hO p) (hO q)

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.image_finite_extension : ∀ (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ι : FractionRing O →+* PadicAlgCl l), (∀ z : ℤ_[l], ι (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l])) → ∃ L : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] L ∧ ∀ y, y ∈ L ↔ ∃ a, ι a = y := by
  atlas_forward_decl GlobalTheory.exists_finiteDimensional_intermediateField_eq_range_fractionRing
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_frobenius_split_places : GlobalTheory.TwSys.Cheb → ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc), Dense {σ : GE N | ∃ w, SplitOut N i w ∧ ∃ B : ValuationSubring N.Om, Formalism.ConjugateSelfDual.IsPlaceOver (F := H.E) B w ∧ Formalism.ConjugateSelfDual.IsFrob (F := H.E) B (Formalism.ConjugateSelfDual.normV w) σ} := by
  first | exact @GlobalTheory.FrobDense.dense_frob | exact GlobalTheory.FrobDense.dense_frob | (intros; apply GlobalTheory.FrobDense.dense_frob <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.ConstituentsCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

open Polynomial Formalism.ConjugateSelfDual

def BrauerNesbitt : Prop :=
  ∀ (Γ k : Type) [Group Γ] [Field k] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) k), IsSSRep ρ → IsSSRep ρ' → (∀ g, ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly = ((ρ' g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly) → ∃ h : GL (Fin a) k, ∀ g, ρ' g = h * ρ g * h⁻¹

section Rep

variable {k Γ : Type} [Field k] [Group Γ]

theorem isSemisimplificationOf_iff (hBN : BrauerNesbitt) {W V : Type} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (s : Representation k Γ W) (ρ : Representation k Γ V) :
    IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s ρ ↔
      IsSS s ∧ ∀ g, LinearMap.charpoly (s g) = LinearMap.charpoly (ρ g) := by
  refine ⟨fun h => ⟨h.1, GlobalTheory.T.charpoly_eq_of_semisimplification s ρ h⟩, fun ⟨h1, h2⟩ => ?_⟩
  obtain ⟨s', hs'⟩ := GlobalTheory.T.exists_semisimplification' ρ
  obtain ⟨e, he⟩ := GlobalTheory.T.semisimplification_unique_up_to_conj hBN s s' h1 hs'.1 (fun g => (h2 g).trans (GlobalTheory.T.charpoly_eq_of_semisimplification s' ρ hs' g).symm)
  exact GlobalTheory.T.semisimplification_of_linear_equiv s s' ρ e he hs'

theorem charpoly_matRep {a : ℕ} (M : Γ →* Matrix (Fin a) (Fin a) k) (g : Γ) :
    LinearMap.charpoly (matRep M g) = (M g).charpoly :=
  Matrix.charpoly_toLin' (M g)

theorem charpoly_blockSum {r t : ℕ} (ρ : Γ →* Matrix (Fin r) (Fin r) k) (χ : Fin t → (Γ →* kˣ)) (g : Γ) :
    LinearMap.charpoly (IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum ρ χ g) =
      (ρ g).charpoly * ∏ c, (X - C ((χ c g : kˣ) : k)) := by
  have h : IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum ρ χ g =
      LinearMap.prodMap (matRep ρ g) (Matrix.toLin' (Matrix.diagonal fun c => ((χ c g : kˣ) : k))) := by
    refine LinearMap.ext fun u => ?_
    rw [IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum_apply]
    refine Prod.ext rfl (funext fun c => ?_)
    simp [Matrix.mulVec_diagonal]
  rw [h, LinearMap.charpoly_prodMap, charpoly_matRep, Matrix.charpoly_toLin', Matrix.charpoly_diagonal]

theorem absIrrSub_of_absIrrDistinct {a : ℕ} (ρ : Γ →* GL (Fin a) k)
    (h : AbsIrrDistinct (matRep ((Units.coeHom _).comp ρ))) (W : Submodule k (Fin a → k))
    (hW : IsIrrSub ρ W) : AbsIrrSub ρ W :=
  GlobalTheory.T.irreducible_span_after_map _ ρ W hW.2.1 hW.1 (GlobalTheory.T.span_restrict_eq_top_of_simple _ h W hW.2.1 hW.1 hW.2.2)

theorem isSSRep_map_of_absIrrDistinct {L : Type} [Field L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k)
    (h : AbsIrrDistinct (matRep ((Units.coeHom _).comp ρ))) : IsSSRep (mapRep f ρ) := by
  classical
  obtain ⟨ι, _, _, Vs, hs, hint, hne, hsp, -⟩ := h
  have key := GlobalTheory.T.semisimple_of_simple_sSup (matRep ((Units.coeHom _).comp (mapRep f ρ)))
    (Set.range fun j => Submodule.span L ((fun v => f ∘ v) '' (Vs j : Set (Fin a → k)))) ?_ ?_
  · exact key
  · rintro _ ⟨j, rfl⟩
    exact (GlobalTheory.T.irreducible_span_after_map f ρ (Vs j) (hs j) (hne j) (hsp j)).2
  · set U := sSup (Set.range fun j => Submodule.span L ((fun v => f ∘ v) '' (Vs j : Set (Fin a → k))))
    have hall : ∀ v : Fin a → k, (f ∘ v) ∈ U := by
      intro v
      have hv : v ∈ ⨆ j, Vs j := by rw [hint.submodule_iSup_eq_top]; trivial
      induction hv using Submodule.iSup_induction' with
      | mem j v hv => exact (le_sSup (Set.mem_range_self j) : _ ≤ U) (Submodule.subset_span ⟨v, hv, rfl⟩)
      | zero =>
        have : (f ∘ (0 : Fin a → k)) = 0 := by funext j; simp
        rw [this]; exact U.zero_mem
      | add x y _ _ hx hy =>
        have : (f ∘ (x + y)) = f ∘ x + f ∘ y := by funext j; simp
        rw [this]; exact U.add_mem hx hy
    rw [eq_top_iff, ← (Pi.basisFun L (Fin a)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have : (Pi.basisFun L (Fin a)) j = f ∘ (Pi.single j 1) := by
      funext j'; simp [Pi.single_apply]
    rw [this]; exact hall _

theorem charpoly_eq_of_dense {Y L : Type} [TopologicalSpace Y] [Field L] [Infinite L] [TopologicalSpace L]
    [IsTopologicalRing L] [T2Space L] {a : ℕ} (M M' : Y → Matrix (Fin a) (Fin a) L) (hM : Continuous M)
    (hM' : Continuous M') {S : Set Y} (hS : Dense S) (h : ∀ y ∈ S, (M y).charpoly = (M' y).charpoly) (y : Y) :
    (M y).charpoly = (M' y).charpoly := by
  refine Polynomial.funext fun c => ?_
  have := Continuous.ext_on hS (f := fun y => (Matrix.scalar (Fin a) c - M y).det)
    (g := fun y => (Matrix.scalar (Fin a) c - M' y).det)
    (continuous_const.sub hM).matrix_det (continuous_const.sub hM').matrix_det
    (fun y hy => by
      simp only [← Matrix.eval_charpoly]; rw [h y hy])
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly]
  exact congrFun this y

end Rep

section Loc

variable (D : D7) (i : D.nd.Loc)

def FrobDense : Prop :=
  Dense {σ : GE D.nd | ∃ w, SplitOut D.nd i w ∧ ∃ B : ValuationSubring D.nd.Om,
    IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ}

theorem iota_facts : (∀ a, ‖iotaOQ D.nd D.naut i a‖ ≤ 1) ∧
    (∀ a ∈ IsLocalRing.maximalIdeal (D.nd.O i), ‖iotaOQ D.nd D.naut i a‖ < 1) ∧
    Continuous (iotaOQ D.nd D.naut i) :=
  GlobalTheory.T.embedding_integral_continuous (D.nd.l i) (D.nd.O_adic i) _ (D.naut.iotaQ_alg i)

theorem iota_inj : Function.Injective (iotaOQ D.nd D.naut i) :=
  (D.naut.iotaQ i).injective.comp (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)))

theorem cpol_mapRep {Γ A B : Type} [Group Γ] [CommRing A] [CommRing B] {a : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin a) A) (g : Γ) :
    IndefiniteRowSideFullHecke.ResidualConstituentShape.cpol (mapRep f ρ) g = (IndefiniteRowSideFullHecke.ResidualConstituentShape.cpol ρ g).map f :=
  Matrix.charpoly_map ((ρ g : GL (Fin a) A) : Matrix (Fin a) (Fin a) A) f

theorem mapRep_mapRep {Γ A B C : Type} [Group Γ] [CommRing A] [CommRing B] [CommRing C] {a : ℕ} (f : A →+* B)
    (f' : B →+* C) (ρ : Γ →* GL (Fin a) A) : mapRep f' (mapRep f ρ) = mapRep (f'.comp f) ρ :=
  MonoidHom.ext fun _ => Units.ext rfl

theorem coe_mapRep {Γ A B : Type} [Group Γ] [CommRing A] [CommRing B] {a : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin a) A) : (Units.coeHom _).comp (mapRep f ρ) = mapM f ((Units.coeHom _).comp ρ) := rfl

variable {D i}

theorem cont_map {x : D.nd.X i} {r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)} (hr : IsHeckeGalois D.nd i x r) :
    Continuous fun g => ((mapRep (iotaOQ D.nd D.naut i) r g : GL _ _) :
      Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))) :=
  hr.1.matrix_map (iota_facts D i).2.2

theorem cpol_bar (hd : FrobDense D i) {x : D.nd.X i} {r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)}
    (hr : IsHeckeGalois D.nd i x r) {ρ : GE D.nd →* GL (Fin D.R.nV) (Qbar (D.nd.l i))}
    (hρ : IndefiniteRowSideFullHecke.ResidualConstituentShape.IsPointRepBar D.nd D.naut i x ρ) (g : GE D.nd) :
    IndefiniteRowSideFullHecke.ResidualConstituentShape.cpol ρ g = IndefiniteRowSideFullHecke.ResidualConstituentShape.cpol (mapRep (iotaOQ D.nd D.naut i) r) g := by
  refine charpoly_eq_of_dense _ _ hρ.1 (cont_map hr) hd ?_ g
  rintro σ ⟨w, hw, B, hB, hσ⟩
  refine (hρ.2.2 w hw B σ hB hσ).trans ?_
  rw [← hr.2.2 w hw B σ hB hσ]
  exact (cpol_mapRep _ r σ).symm

theorem cpol_point (hd : FrobDense D i) {x : D.nd.X i} {r r' : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)}
    (hr : IsHeckeGalois D.nd i x r) (hr' : IsHeckeGalois D.nd i x r') (g : GE D.nd) :
    IndefiniteRowSideFullHecke.ResidualConstituentShape.cpol r g = IndefiniteRowSideFullHecke.ResidualConstituentShape.cpol r' g := by
  apply Polynomial.map_injective _ (iota_inj D i)
  rw [← cpol_mapRep, ← cpol_mapRep]
  refine charpoly_eq_of_dense _ _ (cont_map hr) (cont_map hr') hd ?_ g
  rintro σ ⟨w, hw, B, hB, hσ⟩
  refine (cpol_mapRep _ r σ).trans (Eq.trans ?_ (cpol_mapRep _ r' σ).symm)
  exact congrArg _ ((hr.2.2 w hw B σ hB hσ).trans (hr'.2.2 w hw B σ hB hσ).symm)

theorem charpoly_redK {a : ℕ} (ρ : GE D.nd →* GL (Fin a) (D.nd.O i)) (g : GE D.nd) :
    LinearMap.charpoly (IndefiniteRowSideFullHecke.SemisimplificationConstituents.redK D i ρ g) = IndefiniteRowSideFullHecke.ResidualConstituentShape.cpol (redRep D.nd i ρ) g :=
  charpoly_matRep _ g

theorem residualSame_of_common (h : IndefiniteRowSideFullHecke.SemisimplificationConstituents.ResidualCommon D i) (r : IndefiniteRowSideFullHecke.SemisimplificationConstituents.RepFam D i)
    (hr : GoodR D.nd i r) : IndefiniteRowSideFullHecke.ResidualConstituentShape.ResidualSame D.nd i r := by
  obtain ⟨s, hs⟩ := h
  intro x y g
  rw [← charpoly_redK, ← charpoly_redK, ← GlobalTheory.T.charpoly_eq_of_semisimplification _ _ (hs r hr x) g, ← GlobalTheory.T.charpoly_eq_of_semisimplification _ _ (hs r hr y) g]

theorem residualCommon_iff (hBN : BrauerNesbitt) (hd : FrobDense D i) :
    IndefiniteRowSideFullHecke.SemisimplificationConstituents.ResidualCommon D i ↔
      ∀ r, GoodR D.nd i r → IndefiniteRowSideFullHecke.ResidualConstituentShape.ResidualSame D.nd i r := by
  refine ⟨residualSame_of_common, fun h => ?_⟩
  by_cases h0 : ∃ r₀, GoodR D.nd i r₀
  · obtain ⟨r₀, hr₀⟩ := h0
    obtain ⟨x₀⟩ : Nonempty (D.nd.X i) := inferInstance
    obtain ⟨s, hs⟩ := GlobalTheory.T.exists_semisimplification' (IndefiniteRowSideFullHecke.SemisimplificationConstituents.redK D i (r₀ x₀))
    refine ⟨s, fun r hr x => (isSemisimplificationOf_iff hBN _ _).2 ⟨hs.1, fun g => ?_⟩⟩
    rw [GlobalTheory.T.charpoly_eq_of_semisimplification _ _ hs g, charpoly_redK, charpoly_redK, h r₀ hr₀ x₀ x g]
    unfold redRep
    rw [cpol_mapRep, cpol_mapRep, cpol_point hd (hr₀ x) (hr x)]
  · exact ⟨1, fun r hr => absurd ⟨r, hr⟩ h0⟩

theorem coeffLarge_of (h1 : IndefiniteRowSideFullHecke.SemisimplificationConstituents.Realised D i) (h2 : IndefiniteRowSideFullHecke.SemisimplificationConstituents.ConstituentsAbsIrrDistinct D i) :
    IndefiniteRowSideFullHecke.ResidualConstituentShape.CoeffLarge D.nd i := by
  obtain ⟨r, hr⟩ := h1
  exact ⟨r, hr, fun x W hW => absIrrSub_of_absIrrDistinct (mapRep (toK D.nd i) (r x)) (h2 r hr x) W hW⟩

theorem enlargement_of (hBN : BrauerNesbitt) (hd : FrobDense D i) (r : IndefiniteRowSideFullHecke.SemisimplificationConstituents.RepFam D i)
    (hr : GoodR D.nd i r) (h : IndefiniteRowSideFullHecke.ResidualConstituentShape.ConstituentsOver D.nd i r) :
    IndefiniteRowSideFullHecke.ResidualConstituentShape.EnlargementAt D.nd D.naut i := by
  intro ρ hρ
  have hc : ∀ x g, IndefiniteRowSideFullHecke.ResidualConstituentShape.cpol (ρ x) g = (IndefiniteRowSideFullHecke.ResidualConstituentShape.cpol (r x) g).map (iotaOQ D.nd D.naut i) :=
    fun x g => (cpol_bar hd (hr x) (hρ x) g).trans (cpol_mapRep _ _ g)
  refine ⟨?_, fun x y g n => ?_⟩
  · obtain ⟨L, hL, hmem⟩ := GlobalTheory.T.image_finite_extension (D.nd.l i) (D.naut.iotaQ i) (D.naut.iotaQ_alg i)
    refine ⟨⟨L, hL⟩, fun a => (hmem _).2 ⟨a, rfl⟩, fun x => ?_⟩
    obtain ⟨f, hf, hfc⟩ : ∃ f : KK D.nd i →+* L, Function.Surjective f ∧
        (algebraMap L (Qbar (D.nd.l i))).comp f = D.naut.iotaQ i := by
      refine ⟨(D.naut.iotaQ i).codRestrict L.toSubfield.toSubring (fun a => (hmem _).2 ⟨a, rfl⟩), ?_,
        RingHom.ext fun _ => rfl⟩
      rintro ⟨y, hy⟩
      obtain ⟨a, rfl⟩ := (hmem y).1 hy
      exact ⟨a, rfl⟩
    have hA := GlobalTheory.T.absIrrDistinct_map_surjective f hf _ (h.1 x).2
    refine ⟨mapRep f (mapRep (toK D.nd i) (r x)), ?_, ?_⟩
    swap
    · rw [coe_mapRep, coe_mapRep]
      exact hA
    have hss : IsSSRep (mapRep (D.naut.iotaQ i) (mapRep (toK D.nd i) (r x))) :=
      isSSRep_map_of_absIrrDistinct _ _ (h.1 x).2
    rw [mapRep_mapRep] at hss
    replace hss : IsSSRep (mapRep (iotaOQ D.nd D.naut i) (r x)) := hss
    have hcp := fun g => cpol_bar hd (hr x) (hρ x) g
    unfold IndefiniteRowSideFullHecke.ResidualConstituentShape.cpol at hcp
    obtain ⟨P, hP⟩ := hBN (GE D.nd) (Qbar (D.nd.l i)) D.R.nV (ρ x) (mapRep (iotaOQ D.nd D.naut i) (r x))
      (hρ x).2.1 hss hcp
    refine ⟨P, fun g => ?_⟩
    rw [← hP g, mapRep_mapRep f, hfc, mapRep_mapRep]
    rfl
  · rw [hc, hc, Polynomial.coeff_map, Polynomial.coeff_map, ← map_sub]
    refine ⟨(iota_facts D i).1 _, (iota_facts D i).2.1 _ ?_⟩
    have := congrArg (fun p => Polynomial.coeff p n) (h.2 x y g)
    unfold redRep at this
    simp only [cpol_mapRep, Polynomial.coeff_map] at this
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, this, sub_self]

theorem constituentsAt_iff (hBN : BrauerNesbitt) (hd : FrobDense D i) :
    IndefiniteRowSideFullHecke.SemisimplificationConstituents.ConstituentsAt D i ↔
      IndefiniteRowSideFullHecke.ResidualConstituentShape.CoeffLarge D.nd i ∧ (IndefiniteRowSideFullHecke.ResidualConstituentShape.EnlargementAt D.nd D.naut i ∧
        (IndefiniteRowSideFullHecke.ResidualConstituentShape.CoeffLarge D.nd i → ∀ r, GoodR D.nd i r → IndefiniteRowSideFullHecke.ResidualConstituentShape.ConstituentsOver D.nd i r)) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hover : ∀ r, GoodR D.nd i r → IndefiniteRowSideFullHecke.ResidualConstituentShape.ConstituentsOver D.nd i r := fun r hr =>
      ⟨fun x => ⟨(hr x).2.1, h2 r hr x⟩, residualSame_of_common h3 r hr⟩
    refine ⟨coeffLarge_of h1 h2, ?_, fun _ => hover⟩
    obtain ⟨r, hr⟩ := h1
    exact enlargement_of hBN hd r hr (hover r hr)
  · rintro ⟨hO, -, h⟩
    have h := h hO
    obtain ⟨r, hr, -⟩ := hO
    exact ⟨⟨r, hr⟩, fun r hr x => ((h r hr).1 x).2,
      (residualCommon_iff hBN hd).2 fun r hr => (h r hr).2⟩

theorem offBlock_iff {r₀ : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)}
    (h₀ : Continuous fun g => ((r₀ g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)))
    (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) :
    IndefiniteRowSideFullHecke.SemisimplificationConstituents.OffBlock D i r₀ ρ ↔ IndefiniteRowSideFullHecke.ResidualConstituentShape.IsBlockComplement D.nd i r₀ ρ := by
  constructor
  · rintro ⟨-, e, he⟩
    exact ⟨e, fun g v => (he g v).trans (IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum_apply _ _ _ _)⟩
  · rintro ⟨e, he⟩
    refine ⟨GlobalTheory.T.block_decomposition_fraction_field (D.nd.O_adic i) _ _ e h₀ (fun g v => congrArg Prod.fst (he g v)), e, fun g v => ?_⟩
    rw [IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum_apply]
    exact he g v

theorem charpoly_residualBlockSum (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) (g : GE D.nd) :
    LinearMap.charpoly (IndefiniteRowSideFullHecke.SemisimplificationConstituents.residualBlockSum D i ρ g) = IndefiniteRowSideFullHecke.ResidualConstituentShape.cpol (redRep D.nd i ρ) g *
      ∏ c ∈ Finset.Icc 1 D.R.t,
        (X - C (IsLocalRing.residue (D.nd.O i) ((D.nd.chi i c g : (D.nd.O i)ˣ) : D.nd.O i))) := by
  refine (charpoly_blockSum _ _ g).trans ?_
  congr 1
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel,
    ← Fin.prod_univ_eq_prod_range (fun c => X - C (IsLocalRing.residue (D.nd.O i)
      ((D.nd.chi i (1 + c) g : (D.nd.O i)ˣ) : D.nd.O i)))]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [add_comm 1]
  rfl

theorem residualShape_iff (hBN : BrauerNesbitt) (r : IndefiniteRowSideFullHecke.SemisimplificationConstituents.RepFam D i)
    (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) :
    IndefiniteRowSideFullHecke.ResidualConstituentShape.ResidualShape D.nd i r ρ ↔
      IndefiniteRowSideFullHecke.SemisimplificationConstituents.ResidualShape D i r ρ ∧ AbsIrrSub (redRep D.nd i ρ) ⊤ := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hirr : IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsIrred (IndefiniteRowSideFullHecke.SemisimplificationConstituents.redK D i ρ) := GlobalTheory.T.isIrred_of_absIrr (redRep D.nd i ρ) h2
    refine ⟨⟨fun x => (isSemisimplificationOf_iff hBN _ _).2 ⟨GlobalTheory.T.block_sum_semisimple _ _ hirr, fun g => ?_⟩, hirr, h1⟩, h2⟩
    rw [charpoly_residualBlockSum, charpoly_redK, h3 x g]
  · rintro ⟨⟨h1, -, h3⟩, h4⟩
    refine ⟨h3, h4, fun x g => ?_⟩
    rw [← charpoly_residualBlockSum, ← charpoly_redK, GlobalTheory.T.charpoly_eq_of_semisimplification _ _ (h1 x) g]

end Loc

theorem typeStanding_iff (D : D7) : IndefiniteRowSideFullHecke.SemisimplificationConstituents.TypeHypothesis D ↔ IndefiniteRowSideFullHecke.ResidualConstituentShape.TypePrimeSizes D :=
  ⟨fun h => ⟨h.1, h.2, D.ntypes.BB_disj⟩, fun h => ⟨h.1, h.2.1⟩⟩

def CoeffTie (D : D7) : Prop := ∀ i, IndefiniteRowSideFullHecke.ResidualConstituentShape.CoeffLarge D.nd i

def LiftPointGood (D : D7) : Prop := ∀ i x, IndefiniteRowSideFullHecke.SemisimplificationConstituents.GoodRowPoint D i x → x ∈ D.nd.Zgood i

def GoodPointLift (D : D7) : Prop := ∀ i, ∀ x ∈ D.nd.Zgood i, IndefiniteRowSideFullHecke.SemisimplificationConstituents.GoodRowPoint D i x

def ResidualAbsIrr (D : D7) : Prop :=
  IndefiniteRowSideFullHecke.SemisimplificationConstituents.TypeHypothesis D → ∀ i r, GoodR D.nd i r → ∀ x₀ ∈ D.nd.Zgood i, ∀ ρ,
    IndefiniteRowSideFullHecke.SemisimplificationConstituents.OffBlock D i (r x₀) ρ → AbsIrrSub (redRep D.nd i ρ) ⊤

theorem constituents_iff (hBN : BrauerNesbitt) (D : D7) (hd : ∀ i, FrobDense D i) :
    IndefiniteRowSideFullHecke.SemisimplificationConstituents.Constituents_at D ↔ CoeffTie D ∧ IndefiniteRowSideFullHecke.ResidualConstituentShape.Constituents_at D := by
  unfold IndefiniteRowSideFullHecke.SemisimplificationConstituents.Constituents_at CoeffTie IndefiniteRowSideFullHecke.ResidualConstituentShape.Constituents_at
  rw [← forall_and]
  exact forall_congr' fun i => constituentsAt_iff hBN (hd i)

theorem shape_second_of_first (hBN : BrauerNesbitt) (D : D7) (hO : CoeffTie D) (hg : LiftPointGood D)
    (h : IndefiniteRowSideFullHecke.ResidualConstituentShape.ResidualShape_at D) : IndefiniteRowSideFullHecke.SemisimplificationConstituents.ResidualShape_at D := by
  intro hT i r hr x₀ hx₀
  obtain ⟨⟨ρ, hρ⟩, h2⟩ := h ((typeStanding_iff D).1 hT) i (hO i) r hr x₀ (hg i x₀ hx₀)
  exact ⟨⟨ρ, (offBlock_iff (hr x₀).1 ρ).2 hρ⟩, fun ρ hρ =>
    ((residualShape_iff hBN r ρ).1 (h2 ρ ((offBlock_iff (hr x₀).1 ρ).1 hρ))).1⟩

theorem residualAbsIrr_of_first (D : D7) (hO : CoeffTie D) (h : IndefiniteRowSideFullHecke.ResidualConstituentShape.ResidualShape_at D) :
    ResidualAbsIrr D := fun hT i r hr x₀ hx₀ ρ hρ =>
  ((h ((typeStanding_iff D).1 hT) i (hO i) r hr x₀ hx₀).2 ρ ((offBlock_iff (hr x₀).1 ρ).1 hρ)).2.1

theorem shape_first_of_second (hBN : BrauerNesbitt) (D : D7) (hg : GoodPointLift D)
    (h : IndefiniteRowSideFullHecke.SemisimplificationConstituents.ResidualShape_at D) (ha : ResidualAbsIrr D) : IndefiniteRowSideFullHecke.ResidualConstituentShape.ResidualShape_at D := by
  intro hT i _ r hr x₀ hx₀
  have hT' := (typeStanding_iff D).2 hT
  obtain ⟨⟨ρ, hρ⟩, h2⟩ := h hT' i r hr x₀ (hg i x₀ hx₀)
  refine ⟨⟨ρ, (offBlock_iff (hr x₀).1 ρ).1 hρ⟩, fun ρ hρ => ?_⟩
  have hρ' := (offBlock_iff (hr x₀).1 ρ).2 hρ
  exact (residualShape_iff hBN r ρ).2 ⟨h2 ρ hρ', ha hT' i r hr x₀ hx₀ ρ hρ'⟩

theorem compare (hBN : BrauerNesbitt) (hC : GlobalTheory.TwSys.Cheb) (D : D7) :
    (IndefiniteRowSideFullHecke.SemisimplificationConstituents.TypeHypothesis D ↔ IndefiniteRowSideFullHecke.ResidualConstituentShape.TypePrimeSizes D) ∧
    (IndefiniteRowSideFullHecke.SemisimplificationConstituents.Constituents_at D ↔ CoeffTie D ∧ IndefiniteRowSideFullHecke.ResidualConstituentShape.Constituents_at D) ∧
    (∀ i (r : IndefiniteRowSideFullHecke.SemisimplificationConstituents.RepFam D i), GoodR D.nd i r → ∀ x ρ,
      (IndefiniteRowSideFullHecke.SemisimplificationConstituents.OffBlock D i (r x) ρ ↔ IndefiniteRowSideFullHecke.ResidualConstituentShape.IsBlockComplement D.nd i (r x) ρ)) ∧
    (∀ i r ρ, IndefiniteRowSideFullHecke.ResidualConstituentShape.ResidualShape D.nd i r ρ ↔
      IndefiniteRowSideFullHecke.SemisimplificationConstituents.ResidualShape D i r ρ ∧ AbsIrrSub (redRep D.nd i ρ) ⊤) ∧
    (LiftPointGood D → CoeffTie D ∧ IndefiniteRowSideFullHecke.ResidualConstituentShape.ConstituentsAndShape_at D →
      IndefiniteRowSideFullHecke.SemisimplificationConstituents.ConstituentsAndShape_at D ∧ ResidualAbsIrr D) ∧
    (GoodPointLift D → IndefiniteRowSideFullHecke.SemisimplificationConstituents.ConstituentsAndShape_at D ∧ ResidualAbsIrr D →
      CoeffTie D ∧ IndefiniteRowSideFullHecke.ResidualConstituentShape.ConstituentsAndShape_at D) := by
  have hc := constituents_iff hBN D (fun i => GlobalTheory.T.dense_frobenius_split_places hC D.nd i)
  refine ⟨typeStanding_iff D, hc, fun i r hr x ρ => offBlock_iff (hr x).1 ρ,
    fun i r ρ => residualShape_iff hBN r ρ, ?_, ?_⟩
  · rintro hg ⟨hO, h1, h2⟩
    exact ⟨⟨hc.2 ⟨hO, h1⟩, shape_second_of_first hBN D hO hg h2⟩, residualAbsIrr_of_first D hO h2⟩
  · rintro hg ⟨⟨h1, h2⟩, ha⟩
    exact ⟨(hc.1 h1).1, (hc.1 h1).2, shape_first_of_second hBN D hg h2 ha⟩


end GlobalTheory.ConstituentsCompare

end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Polynomial

noncomputable section
namespace GlobalTheory.ConsCompare

section Factors
open GlobalTheory.AdmLoc
variable {k A : Type} [Field k] [Ring A] [Algebra k A]

theorem finiteLength_of_finiteDimensional (k : Type) [Field k] [Algebra k A] (M : Type) [AddCommGroup M]
    [Module k M] [Module A M] [IsScalarTower k A M] [FiniteDimensional k M] : IsFiniteLength A M := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩

theorem exists_semisimple_sameFactors : ∀ (d : ℕ) (M : Type) [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] [FiniteDimensional k M], Module.finrank k M = d →
    ∃ (S : Type) (_ : AddCommGroup S) (_ : Module k S) (_ : Module A S) (_ : IsScalarTower k A S)
      (_ : FiniteDimensional k S), IsSemisimpleModule A S ∧ SameFactors A M S := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro M _ _ _ _ _ hd
  have hfl := finiteLength_of_finiteDimensional (A := A) k M
  rcases subsingleton_or_nontrivial M with h0 | h0
  · exact ⟨M, _, _, _, inferInstance, inferInstance, (isSemisimpleModule_iff A M).2
      (have := (Submodule.subsingleton_iff A).2 h0; Subsingleton.instComplementedLattice),
      SameFactors.refl hfl⟩
  · haveI : IsNoetherian A M := isNoetherian_of_tower k inferInstance
    obtain ⟨N, hN, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule A M)).resolve_left bot_ne_top
    have hlt : Module.finrank k N < d := by
      rw [← hd]
      exact Submodule.finrank_lt (s := N.restrictScalars k) fun h => hN.1 (by simpa using h)
    obtain ⟨S, _, _, _, _, _, hS, hf⟩ := ih _ hlt N rfl
    haveI : IsSimpleModule A (M ⧸ N) := isSimpleModule_iff_isCoatom.2 hN
    exact ⟨S × (M ⧸ N), _, _, _, inferInstance, inferInstance,
      isSemisimpleModule_of_isSemisimpleModule_submodule' (p := fun b : Bool =>
        cond b (LinearMap.range (LinearMap.inl A S (M ⧸ N))) (LinearMap.range (LinearMap.inr A S (M ⧸ N))))
        (by rintro (_ | _) <;> exact IsSemisimpleModule.range _)
        (by rw [iSup_bool_eq]; exact LinearMap.sup_range_inl_inr),
      (SameFactors.sub_prod_quot hfl N).trans
        (hf.prod (SameFactors.refl (finiteLength_of_finiteDimensional k _)))⟩

theorem cpOn_eq_of_sameFactors (a : A) {M M' : Type} [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] [FiniteDimensional k M] [AddCommGroup M'] [Module k M'] [Module A M']
    [IsScalarTower k A M'] [FiniteDimensional k M'] (h : SameFactors A M M') : cpOn k a M = cpOn k a M' := by
  obtain ⟨s, t, h1, h2, h3, h4, f, hf⟩ := h
  rw [cpOn_series _ s h1 h2, cpOn_series _ t h3 h4]
  exact Fintype.prod_equiv f _ _ fun j => cpOn_congr _ (hf j).some

variable {Γ : Type} [Group Γ]

def repOf (k Γ S : Type) [Field k] [Group Γ] [AddCommGroup S] [Module k S] [Module (MonoidAlgebra k Γ) S]
    [IsScalarTower k (MonoidAlgebra k Γ) S] : Representation k Γ S :=
  (Algebra.lsmul k k S : MonoidAlgebra k Γ →ₐ[k] Module.End k S).toMonoidHom.comp (MonoidAlgebra.of k Γ)

theorem isSS_repOf {S : Type} [AddCommGroup S] [Module k S] [Module (MonoidAlgebra k Γ) S]
    [IsScalarTower k (MonoidAlgebra k Γ) S] [IsSemisimpleModule (MonoidAlgebra k Γ) S] :
    IsSS (repOf k Γ S) := fun W hW => by
  let W₁ : Submodule (MonoidAlgebra k Γ) S :=
    { W.toAddSubmonoid with
      smul_mem' := fun a v hv => by
        induction a using MonoidAlgebra.induction_on with
        | of g => exact hW g v hv
        | add a b ha hb => rw [add_smul]; exact W.add_mem ha hb
        | smul c a ha => rw [smul_assoc]; exact W.smul_mem c ha }
  obtain ⟨W₂, h⟩ := exists_isCompl W₁
  refine ⟨W₂.restrictScalars k, fun g v hv => W₂.smul_mem (MonoidAlgebra.of k Γ g) hv, ?_⟩
  exact (Submodule.isCompl_restrictScalars_iff k (s := W₁)).2 h

theorem sameSS_of_charpoly_eq (hBN : GlobalTheory.ConstituentsCompare.BrauerNesbitt) {V W : Type} [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k Γ V) (σ : Representation k Γ W)
    (h : ∀ g, LinearMap.charpoly (ρ g) = LinearMap.charpoly (σ g)) : GlobalTheory.IndefiniteRowSideFullHecke.CharPolyRootsConstruction.SameSS ρ σ := by
  have : FiniteDimensional k ρ.asModule := inferInstanceAs (FiniteDimensional k V)
  have : FiniteDimensional k σ.asModule := inferInstanceAs (FiniteDimensional k W)
  have e1 : ∀ g, LinearMap.charpoly (ρ g) = cpOn k (MonoidAlgebra.of k Γ g) ρ.asModule := fun g => by
    unfold cpOn
    rw [← LinearEquiv.charpoly_conj ρ.asModuleEquiv]
    congr 1
    ext v
    simp [LinearEquiv.conj_apply]
    rfl
  have e2 : ∀ g, LinearMap.charpoly (σ g) = cpOn k (MonoidAlgebra.of k Γ g) σ.asModule := fun g => by
    unfold cpOn
    rw [← LinearEquiv.charpoly_conj σ.asModuleEquiv]
    congr 1
    ext v
    simp [LinearEquiv.conj_apply]
    rfl
  obtain ⟨S, _, _, _, _, _, hS, hf⟩ :=
    exists_semisimple_sameFactors (k := k) (A := MonoidAlgebra k Γ) _ ρ.asModule rfl
  obtain ⟨S', _, _, _, _, _, hS', hf'⟩ :=
    exists_semisimple_sameFactors (k := k) (A := MonoidAlgebra k Γ) _ σ.asModule rfl
  obtain ⟨e, he⟩ := GlobalTheory.brauerNesbitt_abstract_of_matrix hBN (repOf k Γ S) (repOf k Γ S') isSS_repOf isSS_repOf
    fun g => ((cpOn_eq_of_sameFactors _ hf).symm.trans ((e1 g).symm.trans ((h g).trans (e2 g)))).trans
      (cpOn_eq_of_sameFactors _ hf')
  let e' : S ≃ₗ[MonoidAlgebra k Γ] S' :=
    { e.toAddEquiv with
      map_smul' := fun a v => by
        show e (a • v) = a • e v
        induction a using MonoidAlgebra.induction_on with
        | of g => exact he g v
        | add a b ha hb => rw [add_smul, add_smul, map_add, ha, hb]
        | smul c a ha => rw [smul_assoc, smul_assoc, map_smul, ha] }
  exact (hf.trans (SameFactors.of_equiv hf.finiteLength_right e')).trans hf'.symm

end Factors

section Distinct
open Matrix

end Distinct

section BaseChange
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

variable {Γ X A B : Type} [Group Γ] [CommRing A] [CommRing B] {n r t : ℕ}

variable [Algebra A B]

variable [IsDomain A] [IsDomain B]

variable [IsLocalRing A] [IsLocalRing B]

end BaseChange

end GlobalTheory.ConsCompare
end
end
