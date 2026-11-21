import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittSourceMixedCoordHeisenbergRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionMixedCoordsRankZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviFactorScalarsAutomorphicCharacters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpecialLinearGeneratedByTransvections
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StableRangeOneAdelesCmField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLoc
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinPartOneMulInvMemHeckeSplitCongruence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemClosureHeckeSplitCongruenceOfFinPartOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LeviFactorCharactersSplitPlace

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem halfMod_eq_detPow {D : D7} {ρ : ℕ} (n : ℕ) (a : GL (Fin ρ) (AE D)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod n a = GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n := rfl

theorem halfMod_rank_zero {D : D7} (n : ℕ) (a : GL (Fin 0) (AE D)) : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod n a = 1 := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, Subsingleton.elim a 1, map_one, map_one, NNReal.coe_one, Real.one_rpow]

theorem wittDecomposition_levi_emb_acts_isotropic {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (a : GL (Fin ρ) (AE D)) (g : GA D S₀) :
    mt S (d.levi a * d.emb0 g) ⬝ d.e.map (incA D) = d.e.map (incA D) ⬝ a.1 := by
  have e1 : d.e.map (incA D) = d.jX := rfl
  rw [e1, mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, d.levi_jX]

theorem wittDecomposition_levi_emb_acts_anisotropicCore {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (a : GL (Fin ρ) (AE D)) (g : GA D S₀) :
    mt S (d.levi a * d.emb0 g) ⬝ d.i₀.map (incA D) = d.i₀.map (incA D) ⬝ mt S₀ g := by
  have e2 : d.i₀.map (incA D) = d.j0 := rfl
  rw [e2, mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic]

theorem heisO_extX_zero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} (T : HSp D) {ρ : ℕ} (d : HypDec S S₀ ρ)
    (f : WO S T → ℂ) : heisO ψ S T (d.extX T 0) f = f := by
  funext w
  simp only [heisO, map_zero, add_zero, GlobalTheory.MixModel.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul]

theorem levi_origin_scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∃ (α : GL (Fin ρ) (AE D) →* Circle) (ξ : GA D S₀ →* Circle), Continuous α ∧ (∀ a : GL (Fin ρ) D.host.E, α (Matrix.GeneralLinearGroup.map (incA D) a) = 1) ∧ Continuous ξ ∧ (∀ γ ∈ GQ S₀, ξ γ = 1) ∧ ∀ a g f, IsThetaFunO ψ S T f → d.mixS T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) f) 0 = ((α a : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ) * (ξ g : ℂ)) • om₀ (g, 1) (d.mixS T ψ μ 𝓕 (f) 0) := by
  intro D ψ S S₀ T ρ d χS χT om om₀ hom hom₀ μ 𝓕 hμ
  rcases Nat.eq_zero_or_pos ρ with rfl | hρ
  · obtain ⟨hz, -, hl⟩ := GlobalTheory.T.wittDecomposition_mixedCoords_rank_zero D ψ
    obtain ⟨-, -, -, hiso⟩ := GlobalTheory.T.weil_datum_transport_source_rational_isometry D ψ S S₀ T d hom.std
    refine ⟨1, 1, continuous_const, fun _ => rfl, continuous_const, fun _ _ => rfl, fun a g f hf => ?_⟩
    rw [hz S S₀ T d μ 𝓕 hμ, hz S S₀ T d μ 𝓕 hμ, (hl S S₀ d).1, one_mul, hiso χS χT om om₀ hom hom₀ g 1 f hf,
      halfMod_rank_zero]
    simp
  · obtain ⟨hsp, hr, -, -, -, hm, -⟩ := GlobalTheory.T.wittSourceMixedCoord_heisenbergRestriction D ψ S S₀ T ρ d
    obtain ⟨α, ξ, hα, hξ, h⟩ := GlobalTheory.T.leviFactor_scalars_automorphicCharacters D S S₀ T ρ d.e d.i₀ (hsp hρ) ψ χS χT om hom χS χT om₀ hom₀
    refine ⟨α, ξ, hα.1, hα.2, hξ.1, hξ.2, fun a g f hf => ?_⟩
    have hμ' : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D T.rank ρ) μ 𝓕 := by rw [hr]; exact hμ
    rw [hm, hm, heisO_extX_zero, heisO_extX_zero, halfMod_eq_detPow]
    exact h μ 𝓕 hμ' a g (d.levi a * d.emb0 g) (wittDecomposition_levi_emb_acts_isotropic d a g) (wittDecomposition_levi_emb_acts_anisotropicCore d a g) f hf

end GlobalTheory.Unf
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilAction_levi_origin_eq_charScalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∃ (α : GL (Fin ρ) (AE D) →* Circle) (ξ : GA D S₀ →* Circle), Continuous α ∧ (∀ a : GL (Fin ρ) D.host.E, α (Matrix.GeneralLinearGroup.map (incA D) a) = 1) ∧ Continuous ξ ∧ (∀ γ ∈ GQ S₀, ξ γ = 1) ∧ ∀ a g f, IsThetaFunO ψ S T f → d.mixS T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) f) 0 = ((α a : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ) * (ξ g : ℂ)) • om₀ (g, 1) (d.mixS T ψ μ 𝓕 (f) 0) := by
  atlas_forward_decl GlobalTheory.Unf.levi_origin_scalar
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_linear_generated_by_transvections : ∀ (R : Type) [CommRing R], (∀ a b : R, IsCoprime a b → ∃ t : R, IsUnit (a + t * b)) → ∀ (n : ℕ) (H : Subgroup (GL (Fin n) R)), (∀ (i j : Fin n), i ≠ j → ∀ (t : R) (u : GL (Fin n) R), u.1 = Matrix.transvection i j t → u ∈ H) → ∀ a : GL (Fin n) R, Matrix.GeneralLinearGroup.det a = 1 → a ∈ H := by
  first | exact @GlobalTheory.GLGen.mem_of_det_eq_one | exact GlobalTheory.GLGen.mem_of_det_eq_one | (intros; apply GlobalTheory.GLGen.mem_of_det_eq_one <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableRangeOne_adeles_cmField : ∀ (D : D7) (a b : AE D), IsCoprime a b → ∃ t : AE D, IsUnit (a + t * b) := by
  first | exact @GlobalTheory.StableRange.adeles_stableRange_one | exact GlobalTheory.StableRange.adeles_stableRange_one | (intros; apply GlobalTheory.StableRange.adeles_stableRange_one <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory

theorem glChar_transvection {R : Type} [CommRing R] (h2 : IsUnit (2 : R)) {n : ℕ}
    (α : GL (Fin n) R →* Circle) (i j : Fin n) (hij : i ≠ j) (t : R)
    (u : GL (Fin n) R) (hu : u.1 = Matrix.transvection i j t) : α u = 1 := by
  obtain ⟨w, hw⟩ := h2
  let f : Fin n → R := Function.update 1 i 2
  let g : Fin n → R := Function.update 1 i (↑w⁻¹ : R)
  have hfg : ∀ k, f k * g k = 1 := by
    intro k
    by_cases hk : k = i
    · subst hk; simp [f, g, ← hw]
    · simp [f, g, hk]
  have hgf : ∀ k, g k * f k = 1 := fun k => by rw [mul_comm]; exact hfg k
  let d : GL (Fin n) R :=
    ⟨Matrix.diagonal f, Matrix.diagonal g,
      by rw [Matrix.diagonal_mul_diagonal]; simp [hfg],
      by rw [Matrix.diagonal_mul_diagonal]; simp [hgf]⟩
  have hcomm : d * u = u * u * d := by
    apply Units.ext
    have hfi : f i = 2 := by simp [f]
    have hfj : f j = 1 := by simp [f, hij.symm]
    change Matrix.diagonal f * u.1 = u.1 * u.1 * Matrix.diagonal f
    rw [hu, Matrix.transvection_mul_transvection_same _ _ hij]
    ext a b
    simp only [Matrix.transvection, Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul,
      Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply,
      Matrix.diagonal_apply, Matrix.one_apply]
    clear_value f g d
    clear hfg hgf
    split_ifs <;> subst_vars <;> simp_all <;> ring
  have h := congrArg α hcomm
  simp only [map_mul] at h
  have h' : α d * α u = α d * (α u * α u) := by rw [h]; exact mul_comm _ _ |>.trans (by rfl)
  have h'' := mul_left_cancel h'
  exact (mul_eq_left.mp h''.symm)

theorem glChar_eq_one_of_det_eq_one : ∀ (D : D7) (n : ℕ) (α : GL (Fin n) (AE D) →* Circle),
    Continuous α → ∀ a, Matrix.GeneralLinearGroup.det a = 1 → α a = 1 := by
  intro D n α _ a ha
  have h2 : IsUnit (2 : AE D) := by
    have h := (IsUnit.mk0 (2 : D.host.F) two_ne_zero).map (algebraMap D.host.F (AE D))
    rwa [map_ofNat] at h
  have := GlobalTheory.T.special_linear_generated_by_transvections (AE D) (GlobalTheory.T.stableRangeOne_adeles_cmField D) n α.ker
    (fun i j hij t u hu => MonoidHom.mem_ker.mpr (glChar_transvection h2 α i j hij t u hu)) a ha
  exact MonoidHom.mem_ker.mp this

end GlobalTheory
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_GL_circle_character_trivial_on_det_one : ∀ (D : D7) (n : ℕ) (α : GL (Fin n) (AE D) →* Circle), Continuous α → ∀ a, Matrix.GeneralLinearGroup.det a = 1 → α a = 1 := by
  first | exact @GlobalTheory.glChar_eq_one_of_det_eq_one | exact GlobalTheory.glChar_eq_one_of_det_eq_one | (intros; apply GlobalTheory.glChar_eq_one_of_det_eq_one <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.HeckeSplitAll

theorem char_trivial_modSet : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), Continuous ν →
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ GlobalTheory.HeckeSplitAll.modSet D N, ν x = 1 := by
  intro D ν hν
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D ν hν
  refine ⟨N, hN, fun x hx => ?_⟩
  obtain ⟨h1, ⟨r, hr, hxr⟩, h3⟩ := hx
  have hNr : (N : Af D.host.F ⊗[D.host.F] D.host.E) * r = N • r := (nsmul_eq_mul _ _).symm
  have hfin : finPart D (x : AE D) ∈ intAE D := by
    have : finPart D (x : AE D) = 1 + N • r := by rw [← hNr, ← hxr]; ring
    rw [this]
    exact add_mem (AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, 1, by simp [Algebra.TensorProduct.one_def]⟩) (nsmul_mem hr N)
  exact hker x ⟨h1, hfin, h3⟩ ⟨r, hr, by rw [hxr, hNr]⟩

end GlobalTheory.HeckeSplitAll
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_congruenceModulus_idelicCharacter_trivial : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), Continuous ν → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ GlobalTheory.HeckeSplitAll.modSet D N, ν x = 1 := by
  atlas_forward_decl GlobalTheory.HeckeSplitAll.char_trivial_modSet
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finPartOne_mul_inv_mem_heckeSplitCongruence : ∀ (D : D7) (N : ℕ), 0 < N → ∀ x : (AE D)ˣ, ∃ z : (AE D)ˣ, finPart D (z : AE D) = 1 ∧ x * z⁻¹ ∈ GlobalTheory.HeckeSplitAll.grpH D N := by
  first | exact @GlobalTheory.HeckeSplitAll.Fin.exists_finPart_eq_one_mul_inv_mem | exact GlobalTheory.HeckeSplitAll.Fin.exists_finPart_eq_one_mul_inv_mem | (intros; apply GlobalTheory.HeckeSplitAll.Fin.exists_finPart_eq_one_mul_inv_mem <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_heckeSplitCongruence_of_finPart_one : ∀ (D : D7) (N : ℕ), 0 < N → ∀ z : (AE D)ˣ, finPart D (z : AE D) = 1 → z ∈ closure (GlobalTheory.HeckeSplitAll.grpH D N : Set (AE D)ˣ) := by
  first | exact @GlobalTheory.HeckeSplitAll.mem_closure_grpH_of_finPart_eq_one | exact GlobalTheory.HeckeSplitAll.mem_closure_grpH_of_finPart_eq_one | (intros; apply GlobalTheory.HeckeSplitAll.mem_closure_grpH_of_finPart_eq_one <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.HeckeSplitAll

theorem heckeChar_eq_one_of_split : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), IsHeckeChar D ν → (∀ e, IsSplitIdem D e → ∀ x : (AE D)ˣ, (e + cA D e) * ((x : AE D) - 1) = (x : AE D) - 1 → ν x = 1) → ∀ x, ν x = 1 := by
  intro D ν hν hs
  obtain ⟨N, hN, hA⟩ := GlobalTheory.T.exists_congruenceModulus_idelicCharacter_trivial D ν hν.1
  have hH : grpH D N ≤ ν.ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ((⟨k, rfl⟩ | ⟨e, he, hx⟩) | hx)
    · exact hν.2 k
    · exact hs e he x hx
    · exact hA x hx
  have hcl : closure (grpH D N : Set (AE D)ˣ) ⊆ ν.ker := by
    refine closure_minimal hH ?_
    have : (ν.ker : Set (AE D)ˣ) = ν ⁻¹' {1} := rfl
    rw [this]
    exact isClosed_singleton.preimage hν.1
  intro x
  obtain ⟨z, hz, hxz⟩ := GlobalTheory.T.exists_finPartOne_mul_inv_mem_heckeSplitCongruence D N hN x
  have h1 : ν (x * z⁻¹) = 1 := hH hxz
  have h2 : ν z = 1 := hcl (GlobalTheory.T.mem_closure_heckeSplitCongruence_of_finPart_one D N hN z hz)
  have : x = x * z⁻¹ * z := by group
  rw [this, map_mul, h1, h2, one_mul]

end GlobalTheory.HeckeSplitAll
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacter_eq_one_of_trivial_splitPlaces : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), IsHeckeChar D ν → (∀ e, IsSplitIdem D e → ∀ x : (AE D)ˣ, (e + cA D e) * ((x : AE D) - 1) = (x : AE D) - 1 → ν x = 1) → ∀ x, ν x = 1 := by
  atlas_forward_decl GlobalTheory.HeckeSplitAll.heckeChar_eq_one_of_split
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviFactor_characters_splitPlace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ (α : GL (Fin ρ) (AE D) →* Circle) (ξ : GA D S₀ →* Circle), (∀ a g f, IsThetaFunO ψ S T f → d.mixS T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) f) 0 = ((α a : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ) * (ξ g : ℂ)) • om₀ (g, 1) (d.mixS T ψ μ 𝓕 (f) 0)) → ∀ e, IsSplitIdem D e → (∀ g, SuppAt e S₀ g → ξ g = 1) ∧ ∀ a : GL (Fin ρ) (AE D), (∀ i j, (e + cA D e) * (a.1 - 1) i j = (a.1 - 1) i j) → α a = (χT (Matrix.GeneralLinearGroup.det a))⁻¹ := by
  first | exact @GlobalTheory.LeviSplitChar.levi_chars_split | exact GlobalTheory.LeviSplitChar.levi_chars_split | (intros; apply GlobalTheory.LeviSplitChar.levi_chars_split <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.LeviOrigin

def diagAt {R : Type*} [CommRing R] (ρ : ℕ) (i : Fin ρ) : R →* Matrix (Fin ρ) (Fin ρ) R where
  toFun t := Matrix.diagonal (Function.update (1 : Fin ρ → R) i t)
  map_one' := by
    have h1 : Function.update (1 : Fin ρ → R) i 1 = 1 := by
      funext j; by_cases h : j = i
      · subst h; simp
      · simp [Function.update_of_ne h]
    show Matrix.diagonal (Function.update (1 : Fin ρ → R) i 1) = 1
    rw [h1]; exact Matrix.diagonal_one
  map_mul' s t := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne h]

def dgU {R : Type*} [CommRing R] (ρ : ℕ) (i : Fin ρ) : Rˣ →* GL (Fin ρ) R := Units.map (diagAt ρ i)

theorem det_dgU {R : Type*} [CommRing R] (ρ : ℕ) (i : Fin ρ) (t : Rˣ) :
    Matrix.GeneralLinearGroup.det (dgU ρ i t) = t := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (Matrix.diagonal (Function.update (1 : Fin ρ → R) i (t : R))).det = t
  rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp

theorem continuous_dgU {R : Type*} [CommRing R] [TopologicalSpace R] (ρ : ℕ) (i : Fin ρ) :
    Continuous (dgU (R := R) ρ i) := by
  apply Continuous.units_map
  show Continuous fun t : R => Matrix.diagonal (Function.update (1 : Fin ρ → R) i t)
  exact Continuous.matrix_diagonal (continuous_const.update i continuous_id)

theorem dgU_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (ρ : ℕ) (i : Fin ρ) (x : Rˣ) :
    dgU ρ i (Units.map f.toMonoidHom x) = Matrix.GeneralLinearGroup.map f (dgU ρ i x) := by
  ext k l
  show Matrix.diagonal (Function.update (1 : Fin ρ → S) i (f x)) k l =
    f (Matrix.diagonal (Function.update (1 : Fin ρ → R) i (x : R)) k l)
  simp only [Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    by_cases h' : k = i
    · subst h'; simp
    · simp [Function.update_of_ne h']
  · simp

theorem dgU_sub_one {R : Type*} [CommRing R] (ρ : ℕ) (i : Fin ρ) (x : Rˣ) (k l : Fin ρ) :
    ((dgU ρ i x).1 - 1) k l = if k = i ∧ l = i then (x : R) - 1 else 0 := by
  show Matrix.diagonal (Function.update (1 : Fin ρ → R) i (x : R)) k l - (1 : Matrix (Fin ρ) (Fin ρ) R) k l = _
  simp only [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : k = l
  · subst h
    by_cases h' : k = i
    · subst h'; simp
    · simp [Function.update_of_ne h', h']
  · simp [h]
    intro hk hl; exact absurd (hk.trans hl.symm) h

end GlobalTheory.LeviOrigin

theorem GlobalTheory.LeviOrigin.alpha_eq (D : D7) (ρ : ℕ) (α : GL (Fin ρ) (AE D) →* Circle) (χT : (AE D)ˣ →* Circle)
    (hαc : Continuous α) (hαr : ∀ a : GL (Fin ρ) D.host.E, α (Matrix.GeneralLinearGroup.map (incA D) a) = 1)
    (hα1 : ∀ a : GL (Fin ρ) (AE D), Matrix.GeneralLinearGroup.det a = 1 → α a = 1)
    (hχ : IsHeckeChar D χT)
    (hs : ∀ e, IsSplitIdem D e → ∀ a : GL (Fin ρ) (AE D), (∀ i j, (e + cA D e) * (a.1 - 1) i j = (a.1 - 1) i j) →
      α a = (χT (Matrix.GeneralLinearGroup.det a))⁻¹) :
    ∀ a : GL (Fin ρ) (AE D), α a = (χT (Matrix.GeneralLinearGroup.det a))⁻¹ := by
  rcases Nat.eq_zero_or_pos ρ with h0 | hpos
  · intro a
    have hd : Matrix.GeneralLinearGroup.det a = 1 := by
      ext; rw [Matrix.GeneralLinearGroup.val_det_apply]; subst h0; simp
    rw [hα1 a hd, hd, map_one, inv_one]
  obtain ⟨i0⟩ : Nonempty (Fin ρ) := ⟨⟨0, hpos⟩⟩
  have hhec : IsHeckeChar D (α.comp (GlobalTheory.LeviOrigin.dgU ρ i0) * χT) := by
    refine ⟨?_, ?_⟩
    · exact (hαc.comp (GlobalTheory.LeviOrigin.continuous_dgU ρ i0)).mul hχ.1
    · intro x
      rw [MonoidHom.mul_apply, MonoidHom.comp_apply, hχ.2 x, mul_one, GlobalTheory.LeviOrigin.dgU_map (incA D) ρ i0 x]
      exact hαr _
  have hν := GlobalTheory.T.heckeCharacter_eq_one_of_trivial_splitPlaces D _ hhec (by
    intro e he x hx
    have h2 := hs e he (GlobalTheory.LeviOrigin.dgU ρ i0 x) (by
      intro k l
      rw [GlobalTheory.LeviOrigin.dgU_sub_one]
      split_ifs
      · exact hx
      · exact mul_zero _)
    rw [MonoidHom.mul_apply, MonoidHom.comp_apply, h2, GlobalTheory.LeviOrigin.det_dgU, inv_mul_cancel])
  have hdg : ∀ t, α (GlobalTheory.LeviOrigin.dgU ρ i0 t) = (χT t)⁻¹ := by
    intro t
    have := hν t
    rw [MonoidHom.mul_apply, MonoidHom.comp_apply] at this
    exact eq_inv_of_mul_eq_one_left this
  intro a
  have hb : Matrix.GeneralLinearGroup.det (a * (GlobalTheory.LeviOrigin.dgU ρ i0 (Matrix.GeneralLinearGroup.det a))⁻¹) = 1 := by
    rw [map_mul, map_inv, GlobalTheory.LeviOrigin.det_dgU, mul_inv_cancel]
  have h1 := hα1 _ hb
  have h3 : α a = α (a * (GlobalTheory.LeviOrigin.dgU ρ i0 (Matrix.GeneralLinearGroup.det a))⁻¹) *
      α (GlobalTheory.LeviOrigin.dgU ρ i0 (Matrix.GeneralLinearGroup.det a)) := by
    rw [← map_mul, inv_mul_cancel_right]
  rw [h3, h1, one_mul]
  exact hdg _

theorem GlobalTheory.LeviOrigin.value_at_origin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → (∀ g, d.mixS T ψ μ 𝓕 (om (d.emb0 g, 1) f) 0 = om₀ (g, 1) (d.mixS T ψ μ 𝓕 (f) 0)) ∧ (∀ a : GL (Fin ρ) (AE D), Matrix.GeneralLinearGroup.det a = 1 → d.mixS T ψ μ 𝓕 (om (d.levi a, 1) f) 0 = d.mixS T ψ μ 𝓕 (f) 0) ∧ ∀ a : GL (Fin ρ) (AE D), d.mixS T ψ μ 𝓕 (om (d.levi a, 1) f) 0 = ((((χT (Matrix.GeneralLinearGroup.det a))⁻¹ : Circle) : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ)) • d.mixS T ψ μ 𝓕 (f) 0 := by
  intro D ψ S S₀ T ρ d χS χT om om₀ hW hW₀ μ 𝓕 hμ f hf
  obtain ⟨α, ξ, hαc, hαr, hξc, hξr, hmain⟩ := GlobalTheory.T.weilAction_levi_origin_eq_charScalar D ψ S S₀ T ρ d χS χT om om₀ hW hW₀ μ 𝓕 hμ
  have hsp := GlobalTheory.T.leviFactor_characters_splitPlace D ψ S S₀ T ρ d χS χT om om₀ hW hW₀ μ 𝓕 hμ α ξ hmain

  have hξ : ∀ g, ξ g = 1 :=
    GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split D S₀ ξ hξc hξr (fun e he => (hsp e he).1)

  have hα1 : ∀ a : GL (Fin ρ) (AE D), Matrix.GeneralLinearGroup.det a = 1 → α a = 1 :=
    GlobalTheory.T.adelic_GL_circle_character_trivial_on_det_one D ρ α hαc
  have hα := GlobalTheory.LeviOrigin.alpha_eq D ρ α χT hαc hαr hα1 hW.hecT (fun e he => (hsp e he).2)
  have hhalf : ∀ a : GL (Fin ρ) (AE D), Matrix.GeneralLinearGroup.det a = 1 →
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a = 1 := by
    intro a ha
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod
    rw [ha, MonoidHom.map_one (GlobalTheory.Doubling.absE D.host.F D.host.E)]
    simp
  have hom₀ : ∀ x, om₀ (1, 1) x = x := by
    intro x; rw [← Prod.one_eq_mk, map_one, Module.End.one_apply]
  have key : ∀ a, d.mixS T ψ μ 𝓕 (om (d.levi a, 1) f) 0 = ((((χT (Matrix.GeneralLinearGroup.det a))⁻¹ : Circle) : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ)) • d.mixS T ψ μ 𝓕 (f) 0 := by
    intro a
    have := hmain a 1 f hf
    rw [map_one, mul_one, hξ 1, hom₀, hα a] at this
    simpa using this
  refine ⟨?_, ?_, key⟩
  · intro g
    have := hmain 1 g f hf
    rw [map_one, one_mul, hξ g, map_one, hhalf 1 (map_one _)] at this
    simpa using this
  · intro a ha
    rw [key a, ha, map_one, inv_one, hhalf a ha]
    simp
end
end
