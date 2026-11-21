import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatAtIsCO
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCompChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarModulusProductFormulaTotallyReal
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.AdicFrames.SwmConeHaar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardCartanInvolutionCommuteCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionAdeleRealComponentsCmType
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentAtTauMemStabilizer

section
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.HeightNu
open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect

theorem exists_blocks {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    ∃ a b c d : Matrix (Fin n) (Fin n) R, M = blk4 a b c d := by
  refine ⟨(M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  unfold blk4
  rw [Matrix.fromBlocks_toBlocks]
  ext i j
  simp

theorem absA_det_ad {D : D7} {n : ℕ} (a : GL (Fin n) (AE D)) :
    absA D (Matrix.GeneralLinearGroup.det (ad a)) =
      (absA D (Matrix.GeneralLinearGroup.det a))⁻¹ := by
  have h : (Matrix.GeneralLinearGroup.det (ad a) : (AE D)ˣ) =
      (conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det a⁻¹ : (AE D)ˣ) : (AE D)ˣ) := by
    apply Units.ext
    change (adj (a⁻¹).1 : Mx D n n).det = _
    unfold adj
    rw [Matrix.det_transpose]
    exact (RingHom.map_det (cA D) (a⁻¹).1).symm
  rw [h, GlobalTheory.DiagThetaRule.absA_conj, map_inv, map_inv]

theorem levi_unip_blocks {D : D7} {n : ℕ} {p : G D n} (hp : p ∈ P D n) (a : GL (Fin n) (AE D))
    (ha : blkA (mat p) = a.1) : ∃ b, mat p = blk4 a.1 b 0 (adj (a⁻¹).1) := by
  obtain ⟨m, u, b, hpe, hm, hu⟩ := exists_levi_unip hp a ha
  refine ⟨a.1 * b, ?_⟩
  rw [hpe, mat_mul, hm, hu, submatrix_fromBlocks_mul]
  simp [-Matrix.coe_units_inv]

theorem mat_w_nb {D : D7} {n : ℕ} {nb : hermA D n → G D n} (hnb : IsNMap nb) {w : G D n}
    (hw : mat w = blk4 0 1 (-1) 0) (c : hermA D n) : mat (w * nb c) = blk4 0 1 (-1) (-c.1) := by
  rw [mat_mul, hw, hnb, submatrix_fromBlocks_mul]
  simp

theorem lower_row : ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0), IsHeight H → ∀ (nb : hermA D n → G D n), IsNMap nb → ∀ w : G D n, mat w = blk4 0 1 (-1) 0 → ∀ c : hermA D n, ∃ (d : GL (Fin n) (AE D)) (k : G D n) (k₁ k₂ k₃ k₄ : Mx D n n), k ∈ K D n ∧ mat k = blk4 k₁ k₂ k₃ k₄ ∧ d.1 * k₃ = -1 ∧ d.1 * k₄ = -c.1 ∧ (H (w * nb c))⁻¹ = absA D (Matrix.GeneralLinearGroup.det d) := by
  intro D n H hH nb hnb w hw c
  obtain ⟨p, hp, k, hk, e⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n (w * nb c)
  obtain ⟨a, ha⟩ := exists_blkA hp
  obtain ⟨b, hmp⟩ := levi_unip_blocks hp a ha
  obtain ⟨k₁, k₂, k₃, k₄, hk4⟩ := exists_blocks (mat k)
  have h2 := mat_w_nb hnb hw c
  rw [e, mat_mul, hmp, hk4, submatrix_fromBlocks_mul] at h2
  obtain ⟨-, -, h3, h4⟩ := blockMatrixTwoByTwoFin_injective h2
  rw [Matrix.zero_mul, zero_add] at h3 h4
  refine ⟨ad a, k, k₁, k₂, k₃, k₄, hk, hk4, h3, h4, ?_⟩
  rw [e, hH p hp a ha k hk, absA_det_ad]
end GlobalTheory.CompanionTheory.HeightNu
end
end

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_unipotent_iwasawa_height : ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0), IsHeight H → ∀ (nb : hermA D n → G D n), IsNMap nb → ∀ w : G D n, mat w = blk4 0 1 (-1) 0 → ∀ c : hermA D n, ∃ (d : GL (Fin n) (AE D)) (k : G D n) (k₁ k₂ k₃ k₄ : Mx D n n), k ∈ K D n ∧ mat k = blk4 k₁ k₂ k₃ k₄ ∧ d.1 * k₃ = -1 ∧ d.1 * k₄ = -c.1 ∧ (H (w * nb c))⁻¹ = absA D (Matrix.GeneralLinearGroup.det d) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.HeightNu.lower_row
end
end

section
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.MM.LowerRows

theorem block_mulVec_lower_rows {A : Type} [CommRing A] {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) A)
    (w : Fin (n + n) → A) (i : Fin n) :
    (blk4 a b c d *ᵥ w) (finSumFinEquiv (Sum.inr i)) =
      (c *ᵥ (fun j => w (finSumFinEquiv (Sum.inl j))) +
        d *ᵥ (fun j => w (finSumFinEquiv (Sum.inr j)))) i := by
  unfold blk4
  rw [Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_apply, Equiv.symm_apply_apply, Equiv.symm_symm, Matrix.fromBlocks_mulVec,
    Sum.elim_inr]
  rfl

def glue {A : Type} {n : ℕ} (y y' : Fin n → A) : Fin (n + n) → A :=
  fun i => Sum.elim y y' (finSumFinEquiv.symm i)

theorem glue_inl {A : Type} {n : ℕ} (y y' : Fin n → A) (j : Fin n) :
    glue y y' (finSumFinEquiv (Sum.inl j)) = y j := by
  simp only [glue, Equiv.symm_apply_apply, Sum.elim_inl]

theorem glue_inr {A : Type} {n : ℕ} (y y' : Fin n → A) (j : Fin n) :
    glue y y' (finSumFinEquiv (Sum.inr j)) = y' j := by
  simp only [glue, Equiv.symm_apply_apply, Sum.elim_inr]

theorem glue_mem {A : Type} {n : ℕ} {S : Set A} {y y' : Fin n → A} (hy : ∀ i, y i ∈ S)
    (hy' : ∀ i, y' i ∈ S) (i : Fin (n + n)) : glue y y' i ∈ S := by
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  rcases j with j | j
  · rw [glue_inl]; exact hy j
  · rw [glue_inr]; exact hy' j

theorem lower_image {A : Type} [CommRing A] (S : Subring A) {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) A)
    (g h : Matrix (Fin (n + n)) (Fin (n + n)) A) (hgh : g * h = 1) (hg : g = blk4 a b c d)
    (hs : ∀ y, (∀ i, y i ∈ S) ↔ ∀ i, (g *ᵥ y) i ∈ S) (x : Fin n → A) :
    (∃ y, (∀ i, y i ∈ S) ∧ ∃ y', (∀ i, y' i ∈ S) ∧ x = c *ᵥ y + d *ᵥ y') ↔ ∀ i, x i ∈ S := by
  constructor
  · rintro ⟨y, hy, y', hy', rfl⟩ i
    have h1 := (hs (glue y y')).1 (glue_mem (S := (S : Set A)) hy hy') (finSumFinEquiv (Sum.inr i))
    rw [hg, block_mulVec_lower_rows] at h1
    simpa only [glue_inl, glue_inr] using h1
  · intro hx
    set w : Fin (n + n) → A := h *ᵥ glue 0 x with hw
    have hgw : g *ᵥ w = glue 0 x := by
      rw [hw, Matrix.mulVec_mulVec, hgh, Matrix.one_mulVec]
    have hwS : ∀ i, w i ∈ S := (hs w).2 fun i => by
      rw [hgw]
      exact glue_mem (S := (S : Set A)) (fun _ => S.zero_mem) hx i
    refine ⟨fun j => w (finSumFinEquiv (Sum.inl j)), fun _ => hwS _,
      fun j => w (finSumFinEquiv (Sum.inr j)), fun _ => hwS _, funext fun i => ?_⟩
    rw [← block_mulVec_lower_rows a b c d w i, ← hg, hgw, glue_inr]

theorem lower_image_lat {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {n : ℕ}
    (a b c d : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    (g : GL (Fin (n + n)) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) (hg : g.1 = blk4 a b c d)
    (hs : ∀ y, y ∈ latLoc F (stdLattice E (n + n)) v ↔ g.1 *ᵥ y ∈ latLoc F (stdLattice E (n + n)) v) :
    {x | ∃ y ∈ latLoc F (stdLattice E n) v, ∃ y' ∈ latLoc F (stdLattice E n) v, x = c.mulVec y + d.mulVec y'} =
      (latLoc F (stdLattice E n) v : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) := by
  have hgh : g.1 * (g⁻¹).1 = 1 := by simp
  ext x
  have key := lower_image (intLoc F E v) a b c d g.1 (g⁻¹).1 hgh hg
    (fun y => by
      have := hs y
      rwa [mem_latLoc_stdLattice, mem_latLoc_stdLattice] at this) x
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, mem_latLoc_stdLattice]
  exact key

theorem blockMatrix_map {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {n : ℕ}
    (a b c d : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) :
    (blk4 a b c d).map (compFin F E v) =
      blk4 (PositivityTheory.SiegelWeilFormula.Gen.matV v a) (PositivityTheory.SiegelWeilFormula.Gen.matV v b)
        (PositivityTheory.SiegelWeilFormula.Gen.matV v c) (PositivityTheory.SiegelWeilFormula.Gen.matV v d) := by
  unfold blk4
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]
  rfl

theorem lowerRows_onto : ∀ (D : D7) (n : ℕ) (k : G D n) (k₁ k₂ k₃ k₄ : Mx D n n), k ∈ K D n → mat k = blk4 k₁ k₂ k₃ k₄ → ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), {x | ∃ y ∈ (latLoc D.host.F (stdLattice D.host.E n) v), ∃ y' ∈ (latLoc D.host.F (stdLattice D.host.E n) v), x = (PositivityTheory.SiegelWeilFormula.Gen.matV v k₃).mulVec y + (PositivityTheory.SiegelWeilFormula.Gen.matV v k₄).mulVec y'} = ((latLoc D.host.F (stdLattice D.host.E n) v) : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) := by
  intro D n k k₁ k₂ k₃ k₄ hk hm v
  have hlev : k ∈ levelOpen D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) :=
    (Subgroup.mem_inf.1 hk).1
  have hst := mem_stabLoc.1 (mem_levelOpen.1 hlev v)
  refine lower_image_lat v (PositivityTheory.SiegelWeilFormula.Gen.matV v k₁) (PositivityTheory.SiegelWeilFormula.Gen.matV v k₂)
    (PositivityTheory.SiegelWeilFormula.Gen.matV v k₃) (PositivityTheory.SiegelWeilFormula.Gen.matV v k₄) _ ?_ hst
  rw [matHom_proj, ← blockMatrix_map, ← hm]
  rfl

end GlobalTheory.CompanionTheory.MM.LowerRows
end
end

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_image_lower_blocks : ∀ (D : D7) (n : ℕ) (k : G D n) (k₁ k₂ k₃ k₄ : Mx D n n), k ∈ K D n → mat k = blk4 k₁ k₂ k₃ k₄ → ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), {x | ∃ y ∈ (latLoc D.host.F (stdLattice D.host.E n) v), ∃ y' ∈ (latLoc D.host.F (stdLattice D.host.E n) v), x = (PositivityTheory.SiegelWeilFormula.Gen.matV v k₃).mulVec y + (PositivityTheory.SiegelWeilFormula.Gen.matV v k₄).mulVec y'} = ((latLoc D.host.F (stdLattice D.host.E n) v) : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.MM.LowerRows.lowerRows_onto
end
end

section
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.LocalModule

open IsDedekindDomain NumberField

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Rv" => HeckeCharacterZeroLocus.SiegelWeilU.Fv F v
local notation "Av" => (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)

def mulVecA (g : GL (Fin n) Av) : (Fin n → Av) ≃ₗ[Av] (Fin n → Av) :=
  LinearEquiv.ofLinear (Matrix.toLin' g.1) (Matrix.toLin' (g⁻¹).1)
    (by rw [← Matrix.toLin'_mul]; simp)
    (by rw [← Matrix.toLin'_mul]; simp)

theorem absF_eq_nnnorm (x : Rv) : GroundTheory.Heights₂.Theta.IndefiniteRowSideFullHecke.WmSys.absF x = ‖x‖₊ := by
  by_cases hx : x = 0
  · simp [GroundTheory.Heights₂.Theta.IndefiniteRowSideFullHecke.WmSys.absF, hx]
  · have hu : IsUnit x := isUnit_iff_ne_zero.2 hx
    have h := GlobalTheory.GaugeProdFormula.modu_finite F v x hx
    rw [GlobalTheory.GaugeEx.modu, dif_pos hu] at h
    simp only [GroundTheory.Heights₂.Theta.IndefiniteRowSideFullHecke.WmSys.absF, dif_neg hx]
    apply NNReal.coe_injective
    rw [coe_nnnorm, ← h]
    congr 2
    exact Units.ext rfl

theorem det_mulVecA (g : GL (Fin n) Av) :
    LinearMap.det (((mulVecA v g).restrictScalars Rv : (Fin n → Av) ≃ₗ[Rv] (Fin n → Av)) :
      (Fin n → Av) →ₗ[Rv] (Fin n → Av)) = Algebra.norm Rv (g.1.det) := by
  have h := LinearMap.det_restrictScalars (R := Rv) (S := Av)
    (f := ((mulVecA v g : (Fin n → Av) ≃ₗ[Av] (Fin n → Av)) : (Fin n → Av) →ₗ[Av] (Fin n → Av)))
  have e : ((mulVecA v g : (Fin n → Av) ≃ₗ[Av] (Fin n → Av)) : (Fin n → Av) →ₗ[Av] (Fin n → Av)) =
      Matrix.toLin' g.1 := rfl
  rw [e, LinearMap.det_toLin'] at h
  exact h

theorem haar_mulVec_image (lam : Measure (Fin n → Av)) [lam.IsAddHaarMeasure] (g : GL (Fin n) Av)
    (S : Set (Fin n → Av)) :
    lam ((fun x => g.1.mulVec x) '' S) =
      (absEv F E v (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) * lam S := by
  haveI : IsModuleTopology Rv Av := ⟨rfl⟩
  haveI : SecondCountableTopology Rv :=
    GroundTheory.Heights₂.Theta.SwmCone.secondCountableTopology_adicCompletion v
  have hd := GroundTheory.Heights₂.Theta.SwmCone.not_discreteTopology_adicCompletion (K := F) v
  let L : (Fin n → Av) ≃ₗ[Rv] (Fin n → Av) := (mulVecA v g).restrictScalars Rv
  let H : (Fin n → Av) ≃ₜ+ (Fin n → Av) :=
    { L.toAddEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap L.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap L.symm.toLinearMap }
  have hc := GroundTheory.Heights₂.Theta.WmSysEquiv.addEquivAddHaarChar_eq_absF_det hd L H (fun _ => rfl)
  haveI : T2Space (Fin n → Av) := inferInstance
  haveI : SecondCountableTopology (Fin n → Av) := inferInstance
  haveI : LocallyCompactSpace (Fin n → Av) := inferInstance
  haveI : SigmaCompactSpace (Fin n → Av) := inferInstance
  haveI : TopologicalSpace.PseudoMetrizableSpace (Fin n → Av) := by
    haveI : T3Space (Fin n → Av) := inferInstance
    infer_instance
  haveI : lam.Regular := inferInstance
  have h := addEquivAddHaarChar_smul_preimage lam (X := H '' S) H
  rw [Set.preimage_image_eq S H.injective] at h
  change lam (H '' S) = _
  rw [← h, ENNReal.smul_def, smul_eq_mul, hc, det_mulVecA, absF_eq_nnnorm]
  rfl

end Gen

end GlobalTheory.CompanionTheory.LocalModule

theorem GlobalTheory.CompanionTheory.LocalModule.haar_mulVec_image_host : ∀ (D : D7) (n : ℕ) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)) (lam : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), lam.IsAddHaarMeasure → ∀ (g : GL (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) (S : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), lam ((fun x => g.1.mulVec x) '' S) = (absEv D.host.F D.host.E v (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) * lam S := by
  intro D n v lam hlam g S
  exact GlobalTheory.CompanionTheory.LocalModule.haar_mulVec_image v lam g S
end
end

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_image_GL_scaling : ∀ (D : D7) (n : ℕ) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)) (lam : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), lam.IsAddHaarMeasure → ∀ (g : GL (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) (S : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), lam ((fun x => g.1.mulVec x) '' S) = (absEv D.host.F D.host.E v (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) * lam S := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LocalModule.haar_mulVec_image_host
end
end

section
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.MM.NuFin

variable {R : Type} [CommRing R] {n : ℕ}

theorem image_eq (A Ai A' B Dm K3 K4 C : Matrix (Fin n) (Fin n) R) (O : AddSubgroup (Fin n → R))
    (hAiA : Ai * A = 1) (hC : A * C = B * A') (hD3 : Dm * K3 = -1) (hD4 : Dm * K4 = -C)
    (hset : {x | ∃ y ∈ O, ∃ y' ∈ O, x = K3 *ᵥ y + K4 *ᵥ y'} = (O : Set (Fin n → R))) :
    {x | ∃ y ∈ O.map (Matrix.mulVecLin A).toAddMonoidHom, ∃ y' ∈ O.map (Matrix.mulVecLin A').toAddMonoidHom,
        x = y + B *ᵥ y'} =
      (fun x => (A * Dm * Ai) *ᵥ x) '' (O.map (Matrix.mulVecLin A).toAddMonoidHom : Set (Fin n → R)) := by
  have hgA : (A * Dm * Ai) * A = A * Dm := by rw [mul_assoc, hAiA, mul_one]
  have hid : ∀ u u', (A * Dm * Ai) *ᵥ (A *ᵥ (-(K3 *ᵥ u + K4 *ᵥ u'))) = A *ᵥ u + B *ᵥ (A' *ᵥ u') := by
    intro u u'
    have e3 : (A * Dm) * K3 = -A := by rw [mul_assoc, hD3, mul_neg, mul_one]
    have e4 : (A * Dm) * K4 = -(B * A') := by rw [mul_assoc, hD4, mul_neg, hC]
    rw [Matrix.mulVec_mulVec, hgA, Matrix.mulVec_neg, Matrix.mulVec_add, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, e3, e4, Matrix.mulVec_mulVec, Matrix.neg_mulVec, Matrix.neg_mulVec]
    simp only [neg_add, neg_neg]
  have hK : ∀ u ∈ O, ∀ u' ∈ O, -(K3 *ᵥ u + K4 *ᵥ u') ∈ O := by
    intro u hu u' hu'
    have h1 : K3 *ᵥ u + K4 *ᵥ u' ∈ (O : Set (Fin n → R)) := by
      rw [← hset]
      exact ⟨u, hu, u', hu', rfl⟩
    exact neg_mem h1
  ext x
  constructor
  · rintro ⟨y, hy, y', hy', rfl⟩
    obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.1 hy
    obtain ⟨u', hu', rfl⟩ := AddSubgroup.mem_map.1 hy'
    exact ⟨A *ᵥ (-(K3 *ᵥ u + K4 *ᵥ u')), AddSubgroup.mem_map.2 ⟨_, hK u hu u' hu', rfl⟩, hid u u'⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.1 hy
    have h1 : -w ∈ (O : Set (Fin n → R)) := neg_mem hw
    rw [← hset] at h1
    obtain ⟨u, hu, u', hu', e⟩ := h1
    have hw' : w = -(K3 *ᵥ u + K4 *ᵥ u') := by rw [← e, neg_neg]
    refine ⟨A *ᵥ u, AddSubgroup.mem_map.2 ⟨u, hu, rfl⟩, A' *ᵥ u', AddSubgroup.mem_map.2 ⟨u', hu', rfl⟩, ?_⟩
    change (A * Dm * Ai) *ᵥ (A *ᵥ w) = _
    rw [hw']
    exact hid u u'

theorem map_neg_matrix {S T : Type} [Ring S] [Ring T] (f : S →+* T) (M : Matrix (Fin n) (Fin n) S) :
    (-M).map f = -(M.map f) := by
  ext i j
  simp

set_option maxHeartbeats 1600000 in

theorem local_haar_GL_image_eq_absValue_det : ∀ (D : D7) (n : ℕ) (a d : GL (Fin n) (AE D)) (b : hermA D n) (k₃ k₄ : Mx D n n) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)) (lam : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), lam.IsAddHaarMeasure → (∀ (g : GL (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) (S : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), lam ((fun x => g.1.mulVec x) '' S) = (absEv D.host.F D.host.E v (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) * lam S) → PositivityTheory.SiegelWeilFormula.Gen.IsCO (latAt a.1 v) → d.1 * k₃ = -1 → d.1 * k₄ = -(pull a b).1 → {x | ∃ y ∈ (latLoc D.host.F (stdLattice D.host.E n) v), ∃ y' ∈ (latLoc D.host.F (stdLattice D.host.E n) v), x = (PositivityTheory.SiegelWeilFormula.Gen.matV v k₃).mulVec y + (PositivityTheory.SiegelWeilFormula.Gen.matV v k₄).mulVec y'} = ((latLoc D.host.F (stdLattice D.host.E n) v) : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) → PositivityTheory.SiegelWeilFormula.Gen.nu2 lam (latAt a.1 v) (latAt (adj (a⁻¹).1) v) (PositivityTheory.SiegelWeilFormula.Gen.matV v b.1) = (absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v (Matrix.GeneralLinearGroup.det d)) : ℝ) := by
  intro D n a d b k₃ k₄ v lam hlam hscale hCO hk3 hk4 hset
  have matV_neg : ∀ M : Matrix (Fin n) (Fin n) (AE D), PositivityTheory.SiegelWeilFormula.Gen.matV v (-M) = -PositivityTheory.SiegelWeilFormula.Gen.matV v M := fun M =>
    map_neg_matrix (Algebra.TensorProduct.map ((HeckeCharacterZeroLocus.SiegelWeilU.evalV D.host.F v).comp (HeckeCharacterZeroLocus.SiegelWeilU.sndA D.host.F))
      (AlgHom.id D.host.F D.host.E)).toRingHom M
  let gv : GL (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E) :=
    Matrix.GeneralLinearGroup.map (compFin D.host.F D.host.E v) (a * d * a⁻¹)
  have hgv : gv.1 = PositivityTheory.SiegelWeilFormula.Gen.matV v a.1 * PositivityTheory.SiegelWeilFormula.Gen.matV v d.1 * PositivityTheory.SiegelWeilFormula.Gen.matV v (a⁻¹).1 := by
    have key : ∀ x y z : Matrix (Fin n) (Fin n) (AE D), PositivityTheory.SiegelWeilFormula.Gen.matV v (x * y * z) = PositivityTheory.SiegelWeilFormula.Gen.matV v x * PositivityTheory.SiegelWeilFormula.Gen.matV v y * PositivityTheory.SiegelWeilFormula.Gen.matV v z := by
      intro x y z
      rw [LatCO.matV_mul, LatCO.matV_mul]
    exact key a.1 d.1 (a⁻¹).1
  have hinv : a.1 * (a⁻¹).1 = 1 := by simp
  have hinv' : (a⁻¹).1 * a.1 = 1 := by simp
  have hAiA : PositivityTheory.SiegelWeilFormula.Gen.matV v (a⁻¹).1 * PositivityTheory.SiegelWeilFormula.Gen.matV v a.1 = 1 := by
    rw [← LatCO.matV_mul, hinv', LatCO.matV_one]
  have hC : PositivityTheory.SiegelWeilFormula.Gen.matV v a.1 * PositivityTheory.SiegelWeilFormula.Gen.matV v (pull a b).1 = PositivityTheory.SiegelWeilFormula.Gen.matV v b.1 * PositivityTheory.SiegelWeilFormula.Gen.matV v (adj (a⁻¹).1) := by
    have e : a.1 * (pull a b).1 = b.1 * adj (a⁻¹).1 := by
      change a.1 * ((a⁻¹).1 * b.1 * adj (a⁻¹).1) = _
      rw [← mul_assoc, ← mul_assoc, hinv, one_mul]
    rw [← LatCO.matV_mul, ← LatCO.matV_mul, e]
  have hD3 : PositivityTheory.SiegelWeilFormula.Gen.matV v d.1 * PositivityTheory.SiegelWeilFormula.Gen.matV v k₃ = -1 := by
    rw [← LatCO.matV_mul, hk3, matV_neg, LatCO.matV_one]
  have hD4 : PositivityTheory.SiegelWeilFormula.Gen.matV v d.1 * PositivityTheory.SiegelWeilFormula.Gen.matV v k₄ = -PositivityTheory.SiegelWeilFormula.Gen.matV v (pull a b).1 := by
    rw [← LatCO.matV_mul, hk4, matV_neg]
  have hS := image_eq (PositivityTheory.SiegelWeilFormula.Gen.matV v a.1) (PositivityTheory.SiegelWeilFormula.Gen.matV v (a⁻¹).1) (PositivityTheory.SiegelWeilFormula.Gen.matV v (adj (a⁻¹).1)) (PositivityTheory.SiegelWeilFormula.Gen.matV v b.1) (PositivityTheory.SiegelWeilFormula.Gen.matV v d.1)
    (PositivityTheory.SiegelWeilFormula.Gen.matV v k₃) (PositivityTheory.SiegelWeilFormula.Gen.matV v k₄) (PositivityTheory.SiegelWeilFormula.Gen.matV v (pull a b).1) (latLoc D.host.F (stdLattice D.host.E n) v).toAddSubgroup
    hAiA hC hD3 hD4 hset
  rw [← hgv] at hS
  have hdet : Matrix.GeneralLinearGroup.det gv = unitFin D.host.F D.host.E v (Matrix.GeneralLinearGroup.det d) := by
    have h1 : Matrix.GeneralLinearGroup.det (a * d * a⁻¹) = Matrix.GeneralLinearGroup.det d := by
      rw [map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det a), mul_inv_cancel_right]
    rw [← h1]
    exact Matrix.GeneralLinearGroup.map_det _ _
  have hm0 : lam (latAt a.1 v : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) ≠ 0 :=
    (hCO.1.measure_pos lam ⟨0, zero_mem _⟩).ne'
  have hmT : lam (latAt a.1 v : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) ≠ ⊤ :=
    hCO.2.measure_lt_top.ne
  have hval : lam {x | ∃ y ∈ latAt a.1 v, ∃ y' ∈ latAt (adj (a⁻¹).1) v, x = y + (PositivityTheory.SiegelWeilFormula.Gen.matV v b.1).mulVec y'} =
      (absEv D.host.F D.host.E v (Matrix.GeneralLinearGroup.det gv) : ℝ≥0∞) * lam (latAt a.1 v : Set _) := by
    rw [← hscale gv]
    exact congrArg lam hS
  unfold PositivityTheory.SiegelWeilFormula.Gen.nu2
  rw [hval, hdet, div_eq_mul_inv, mul_assoc, ENNReal.mul_inv_cancel hm0 hmT, mul_one, ENNReal.coe_toReal]

end GlobalTheory.CompanionTheory.MM.NuFin
end
end

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_haar_GL_image_scaling : ∀ (D : D7) (n : ℕ) (a d : GL (Fin n) (AE D)) (b : hermA D n) (k₃ k₄ : Mx D n n) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)) (lam : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), lam.IsAddHaarMeasure → (∀ (g : GL (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) (S : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), lam ((fun x => g.1.mulVec x) '' S) = (absEv D.host.F D.host.E v (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) * lam S) → PositivityTheory.SiegelWeilFormula.Gen.IsCO (latAt a.1 v) → d.1 * k₃ = -1 → d.1 * k₄ = -(pull a b).1 → {x | ∃ y ∈ (latLoc D.host.F (stdLattice D.host.E n) v), ∃ y' ∈ (latLoc D.host.F (stdLattice D.host.E n) v), x = (PositivityTheory.SiegelWeilFormula.Gen.matV v k₃).mulVec y + (PositivityTheory.SiegelWeilFormula.Gen.matV v k₄).mulVec y'} = ((latLoc D.host.F (stdLattice D.host.E n) v) : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) → PositivityTheory.SiegelWeilFormula.Gen.nu2 lam (latAt a.1 v) (latAt (adj (a⁻¹).1) v) (PositivityTheory.SiegelWeilFormula.Gen.matV v b.1) = (absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v (Matrix.GeneralLinearGroup.det d)) : ℝ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.MM.NuFin.local_haar_GL_image_eq_absValue_det
end
end

section
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.MM.KUnitary

theorem map_mul_conjTranspose_eq_one : ∀ (D : D7) (n : ℕ) (θ : InfFam D), IsInfFam θ → ∀ k ∈ K D n, ∀ τ, (mat k).map ((θ τ).comp (infPart D)) * ((mat k).map ((θ τ).comp (infPart D)))ᴴ = 1 := by
  intro D n θ hθ k hk τ
  have e1 : (mat k).map ((θ τ).comp (infPart D)) = Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig (Jst D n) (θ τ) k := rfl
  have e2 : θ τ = AdelicU.infProj (embOverOf D τ) := AdelicU.eq_infProj hθ (embOverOf D τ) rfl
  have hk' : k ∈ AdelicU.levelAll D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) 1 := hk
  have hw := (AdelicU.mem_levelAll.1 hk').2 (placeOf D τ)
  have hunit := (GlobalTheory.Doubling.mem_stabArch_iff_unitary (isCMExt_host D) (embOverOf D τ) (Jst D n) 1 k).1 hw
  rw [inv_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_one _ (map_zero _) (map_one _)] at hunit
  simp only [Matrix.one_mul, Matrix.mul_one] at hunit
  rw [← e2, ← e1] at hunit
  exact mul_eq_one_comm.1 hunit

end GlobalTheory.CompanionTheory.MM.KUnitary
end
end

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximal_compact_unitary_archimedean : ∀ (D : D7) (n : ℕ) (θ : InfFam D), IsInfFam θ → ∀ k ∈ K D n, ∀ τ, (mat k).map ((θ τ).comp (infPart D)) * ((mat k).map ((θ τ).comp (infPart D)))ᴴ = 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.MM.KUnitary.map_mul_conjTranspose_eq_one
end
end

section
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.MM.RealId

theorem lower_rows {n : ℕ} (p q r s : Matrix (Fin n) (Fin n) ℂ)
    (h : blk4 p q r s * (blk4 p q r s)ᴴ = 1) : r * rᴴ + s * sᴴ = 1 := by
  have h1 : Matrix.fromBlocks p q r s * (Matrix.fromBlocks p q r s)ᴴ = 1 := by
    have h2 := congrArg (fun M => Matrix.submatrix M (finSumFinEquiv (m := n) (n := n)) (finSumFinEquiv (m := n) (n := n))) h
    simpa [blk4, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_one_equiv] using h2
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one] at h1
  exact (Matrix.fromBlocks_inj.1 h1).2.2.2

theorem block_matrix_map {R S : Type} {n : ℕ} (f : R → S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  simp only [blk4]
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]

theorem map_adj (D : D7) (φ : AE D →+* ℂ) (hφ : ∀ z, φ (cA D z) = conj (φ z)) {m n : ℕ} (x : Mx D m n) :
    (adj x).map φ = (x.map φ)ᴴ := by
  ext i j
  simp [adj, Matrix.conjTranspose_apply, hφ]

theorem det_id {n : ℕ} (A B C Dm : Matrix (Fin n) (Fin n) ℂ) (hu : A * Aᴴ + B * Bᴴ = 1)
    (hA : Dm * A = -1) (hB : Dm * B = -C) (hC : Cᴴ = C) :
    (1 + C * C).det.re = ‖Dm.det‖ ^ 2 := by
  have e : Dm * Dmᴴ = 1 + C * C := by
    calc Dm * Dmᴴ = Dm * (A * Aᴴ + B * Bᴴ) * Dmᴴ := by rw [hu, mul_one]
      _ = (Dm * A) * (Dm * A)ᴴ + (Dm * B) * (Dm * B)ᴴ := by
        simp only [Matrix.conjTranspose_mul, mul_add, add_mul, mul_assoc]
      _ = 1 + C * C := by
        rw [hA, hB, Matrix.conjTranspose_neg, Matrix.conjTranspose_neg, hC]
        simp
  rw [← e, Matrix.det_mul, Matrix.det_conjTranspose]
  show (Dm.det * conj Dm.det).re = _
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem det_real_part_unitary_block_identity (D : D7) (n : ℕ) (φ : AE D →+* ℂ) (hconj : ∀ z, φ (cA D z) = conj (φ z))
    (a d : GL (Fin n) (AE D)) (b : hermA D n) (k₃ k₄ : Mx D n n)
    (hl : k₃.map φ * (k₃.map φ)ᴴ + k₄.map φ * (k₄.map φ)ᴴ = 1)
    (h3 : d.1 * k₃ = -1) (h4 : d.1 * k₄ = -(pull a b).1) :
    (1 + (((a⁻¹).1.map φ) * b.1.map φ * ((a⁻¹).1.map φ)ᴴ) * (((a⁻¹).1.map φ) * b.1.map φ * ((a⁻¹).1.map φ)ᴴ)).det.re
      = ‖φ (Matrix.GeneralLinearGroup.det d).1‖ ^ 2 := by
  have hmul : ∀ x y : Mx D n n, (x * y).map φ = x.map φ * y.map φ := fun x y => map_mul φ.mapMatrix x y
  have hneg : ∀ x : Mx D n n, (-x).map φ = -(x.map φ) := fun x => map_neg φ.mapMatrix x
  have hone : (1 : Mx D n n).map φ = 1 := map_one φ.mapMatrix
  have hC : ((pull a b).1).map φ = ((a⁻¹).1.map φ) * b.1.map φ * ((a⁻¹).1.map φ)ᴴ := by
    show ((a⁻¹).1 * b.1 * adj (a⁻¹).1).map φ = _
    rw [hmul, hmul, map_adj D φ hconj]
  have hherm : (((pull a b).1).map φ)ᴴ = ((pull a b).1).map φ := by
    rw [← map_adj D φ hconj]
    exact congrArg (fun M => Matrix.map M φ) (pull a b).2
  have hA : (d.1.map φ) * (k₃.map φ) = -1 := by
    rw [← hmul, h3, hneg, hone]
  have hB : (d.1.map φ) * (k₄.map φ) = -((pull a b).1.map φ) := by
    rw [← hmul, h4, hneg]
  rw [← hC, det_id _ _ _ _ hl hA hB hherm]
  have : (d.1.map φ).det = φ (Matrix.GeneralLinearGroup.det d).1 := (RingHom.map_det φ d.1).symm
  rw [this]

theorem det_one_add_sq : ∀ (D : D7) (n : ℕ) (θ : InfFam D), IsInfFam θ → ∀ (a d : GL (Fin n) (AE D)) (b : hermA D n) (k₁ k₂ k₃ k₄ : Mx D n n) (τ : D.what₂.Tau), (blk4 k₁ k₂ k₃ k₄).map ((θ τ).comp (infPart D)) * ((blk4 k₁ k₂ k₃ k₄).map ((θ τ).comp (infPart D)))ᴴ = 1 → d.1 * k₃ = -1 → d.1 * k₄ = -(pull a b).1 → (1 + (((gAt θ a τ)⁻¹).1 * (PositivityTheory.SiegelWeilFormula.Gen.matInf b.1).map (θ τ) * (((gAt θ a τ)⁻¹).1)ᴴ) * (((gAt θ a τ)⁻¹).1 * (PositivityTheory.SiegelWeilFormula.Gen.matInf b.1).map (θ τ) * (((gAt θ a τ)⁻¹).1)ᴴ)).det.re = ‖θ τ (infPart D (Matrix.GeneralLinearGroup.det d).1)‖ ^ 2 := by
  intro D n θ hθ a d b k₁ k₂ k₃ k₄ τ hu h3 h4
  have hconj : ∀ z, ((θ τ).comp (infPart D)) (cA D z) = conj (((θ τ).comp (infPart D)) z) :=
    fun z => (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.1 z τ
  have hg : ((gAt θ a τ)⁻¹).1 = (a⁻¹).1.map ((θ τ).comp (infPart D)) := by
    have : (gAt θ a τ)⁻¹ = Matrix.GeneralLinearGroup.map ((θ τ).comp (infPart D)) a⁻¹ :=
      (map_inv (Matrix.GeneralLinearGroup.map ((θ τ).comp (infPart D))) a).symm
    rw [this]; rfl
  have hb : (PositivityTheory.SiegelWeilFormula.Gen.matInf b.1).map (θ τ) = b.1.map ((θ τ).comp (infPart D)) := by
    ext i j; rfl
  rw [block_matrix_map] at hu
  have hl := lower_rows _ _ _ _ hu
  rw [hg, hb]
  exact det_real_part_unitary_block_identity D n _ hconj a d b k₃ k₄ hl h3 h4

end GlobalTheory.CompanionTheory.MM.RealId
end
end

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_height_determinant_formula : ∀ (D : D7) (n : ℕ) (θ : InfFam D), IsInfFam θ → ∀ (a d : GL (Fin n) (AE D)) (b : hermA D n) (k₁ k₂ k₃ k₄ : Mx D n n) (τ : D.what₂.Tau), (blk4 k₁ k₂ k₃ k₄).map ((θ τ).comp (infPart D)) * ((blk4 k₁ k₂ k₃ k₄).map ((θ τ).comp (infPart D)))ᴴ = 1 → d.1 * k₃ = -1 → d.1 * k₄ = -(pull a b).1 → (1 + (((gAt θ a τ)⁻¹).1 * (PositivityTheory.SiegelWeilFormula.Gen.matInf b.1).map (θ τ) * (((gAt θ a τ)⁻¹).1)ᴴ) * (((gAt θ a τ)⁻¹).1 * (PositivityTheory.SiegelWeilFormula.Gen.matInf b.1).map (θ τ) * (((gAt θ a τ)⁻¹).1)ᴴ)).det.re = ‖θ τ (infPart D (Matrix.GeneralLinearGroup.det d).1)‖ ^ 2 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.MM.RealId.det_one_add_sq
end
end

section
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM
namespace GlobalTheory.CompanionTheory.AbsProd

open NumberField

theorem absA_eq_prod : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ x : (AE D)ˣ, absA D x = (∏ τ, ‖θ τ (infPart D x.1)‖₊ ^ 2) * ∏ᶠ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v x) := by
  intro D θ hθ x
  have hcm := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).1
  haveI := hcm.1
  have hw : ∀ τ : D.what₂.Tau, absEw D.host.F D.host.E
      (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
      (unitInf D.host.F D.host.E _ x) = ‖θ τ (infPart D (x : AE D))‖₊ ^ 2 := by
    intro τ
    let t' : GlobalTheory.AdelicU.EmbOver D.host.E (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))) :=
      ⟨tauE D τ, (InfinitePlace.embedding_mk_eq_of_isReal
        (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))).symm⟩
    rw [absEw_eq_sq hcm t', GlobalTheory.AutFunCompare.isInfEmb_unique _ _ _ (hθ τ) (GlobalTheory.AdelicU.isInfEmb_infProj t')]
    exact congrArg (fun z : ℂ => ‖z‖₊ ^ 2) (GlobalTheory.HalfModTorus.compInf_eq _ t' _)
  have e2 : (∏ w, absEw D.host.F D.host.E w (unitInf D.host.F D.host.E w x)) =
      ∏ τ, ‖θ τ (infPart D (x : AE D))‖₊ ^ 2 := by
    rw [← (GlobalTheory.CMTypePlaces.places_bijective D).prod_comp
      (fun w => absEw D.host.F D.host.E w (unitInf D.host.F D.host.E w x))]
    exact Finset.prod_congr rfl fun τ _ => hw τ
  rw [absA, absE_apply, e2]

end GlobalTheory.CompanionTheory.AbsProd
end
end

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absValue_adelic_product_formula : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ x : (AE D)ˣ, absA D x = (∏ τ, ‖θ τ (infPart D x.1)‖₊ ^ 2) * ∏ᶠ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v x) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.AbsProd.absA_eq_prod
end
end

section
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.HeightNu
open IsDedekindDomain NumberField

set_option maxHeartbeats 2000000 in

theorem heightNu : ∀ (D : D7) (n : ℕ) (θ : InfFam D), IsInfFam θ → ∀ (H : G D n → ℝ≥0), IsHeight H → ∀ (nb : hermA D n → G D n), IsNMap nb → ∀ w : G D n, mat w = blk4 0 1 (-1) 0 → ∀ (a : GL (Fin n) (AE D)) (lamG : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), (∀ v, (lamG v).IsAddHaarMeasure) → ∀ b : hermA D n, PositivityTheory.SiegelWeilFormula.Gen.nuA θ (gAt θ a) lamG (latAt a.1) (latAt (adj (a⁻¹).1)) b.1 = ((H (w * nb (pull a b)) : ℝ≥0) : ℝ)⁻¹ := by
  intro D n θ hθ H hH nb hnb w hw a lamG hlam b
  obtain ⟨d, k, k₁, k₂, k₃, k₄, hk, hmk, h3, h4, hH'⟩ := GlobalTheory.T.weyl_unipotent_iwasawa_height D n H hH nb hnb w hw (pull a b)
  have hU := fun τ => GlobalTheory.T.maximal_compact_unitary_archimedean D n θ hθ k hk τ
  rw [hmk] at hU
  have hfin : ∀ v, PositivityTheory.SiegelWeilFormula.Gen.nu2 (lamG v) (latAt a.1 v) (latAt (adj (a⁻¹).1) v) (PositivityTheory.SiegelWeilFormula.Gen.matV v b.1) =
      (absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v (Matrix.GeneralLinearGroup.det d)) : ℝ) := fun v =>
    GlobalTheory.T.local_haar_GL_image_scaling D n a d b k₃ k₄ v (lamG v) (hlam v) (GlobalTheory.T.haar_image_GL_scaling D n v (lamG v) (hlam v)) (GlobalTheory.CompanionTheory.MM.latAt_isCO D n a v)
      h3 h4 (GlobalTheory.T.lattice_image_lower_blocks D n k k₁ k₂ k₃ k₄ hk hmk v)
  have hinf : PositivityTheory.SiegelWeilFormula.Gen.nuInf θ (gAt θ a) (PositivityTheory.SiegelWeilFormula.Gen.matInf b.1) =
      ((∏ τ, ‖θ τ (infPart D (Matrix.GeneralLinearGroup.det d).1)‖₊ ^ 2 : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [NNReal.coe_pow, coe_nnnorm]
    exact GlobalTheory.T.archimedean_height_determinant_formula D n θ hθ a d b k₁ k₂ k₃ k₄ τ (hU τ) h3 h4
  have hfp : ((∏ᶠ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v (Matrix.GeneralLinearGroup.det d)) : ℝ≥0) : ℝ) =
      ∏ᶠ v, ((absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v (Matrix.GeneralLinearGroup.det d)) : ℝ≥0) : ℝ) :=
    MonoidHom.map_finprod NNReal.toRealHom.toMonoidHom (finite_mulSupport_absEv _)
  have e : ((H (w * nb (pull a b)) : ℝ≥0) : ℝ)⁻¹ = ((absA D (Matrix.GeneralLinearGroup.det d) : ℝ≥0) : ℝ) := by
    rw [← NNReal.coe_inv, hH']
  rw [e, GlobalTheory.T.absValue_adelic_product_formula D θ hθ, NNReal.coe_mul, hfp, ← hinf]
  exact congrArg _ (finprod_congr hfin)

end GlobalTheory.CompanionTheory.HeightNu
end
end

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_haar_lattice_unipotent_integral : ∀ (D : D7) (n : ℕ) (θ : InfFam D), IsInfFam θ → ∀ (H : G D n → ℝ≥0), IsHeight H → ∀ (nb : hermA D n → G D n), IsNMap nb → ∀ w : G D n, mat w = blk4 0 1 (-1) 0 → ∀ (a : GL (Fin n) (AE D)) (lamG : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), (∀ v, (lamG v).IsAddHaarMeasure) → ∀ b : hermA D n, PositivityTheory.SiegelWeilFormula.Gen.nuA θ (gAt θ a) lamG (latAt a.1) (latAt (adj (a⁻¹).1)) b.1 = ((H (w * nb (pull a b)) : ℝ≥0) : ℝ)⁻¹ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.HeightNu.heightNu
end
end
