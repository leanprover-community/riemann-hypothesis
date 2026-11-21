import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjGLOfCharpolyEqOfSeparableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLCharpolyEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryConjIffExistsCentralizerNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjSelfReciprocalOfDvdEllipticPolynomialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormSolutionFields
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvolutionFixesPolynomialImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormAtSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotallyPositiveRealPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalNormOfLocalNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTransposeMulPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinprodNonsplitSignTotallyPositiveEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDetHermitianTotallyPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SesquilinearDetOrdSignOnKernelConjGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramKernelSignNonsplitBaseChangeEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalHermitianForm
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.HermitianLocalGlobalExistence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormSignatureRealisation
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.HermitianFormLocalGlobal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LandherrStandardDefiniteHermitianCmField

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.involution_fixes_polynomial_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → ∀ m : E[X], cT (IsCMField.complexConj E).toRingEquiv.toRingHom (aeval γ.val m) = aeval γ.val m → ∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r), Q.1 ∣ γ.val.charpoly → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) = (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) := by
  first | exact @GlobalTheory.NormHasseFixed.invol_mk_eq | (intros; apply GlobalTheory.NormHasseFixed.invol_mk_eq <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.nonsplit_centraliser_norm_element : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → ∀ m : E[X], (∀ w : Pl E, ¬ IsSplitAt w → ∃ c : Matrix (Fin n) (Fin n) (w.adicCompletion E), c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val * c ∧ cT (cj w) c * c = (aeval γ.val m).map (algebraMap E (w.adicCompletion E))) → ∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r), Q.1 ∣ γ.val.charpoly → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) = (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (∀ w w' : Pl E, w.under (𝓞 (maximalRealSubfield E)) = v → w'.under (𝓞 (maximalRealSubfield E)) = v → w = w') → ∃ z : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, z * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q _ z = 1 ⊗ₜ (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) := by
  first | exact @GlobalTheory.NormInert.main | exact GlobalTheory.NormInert.main | (intros; apply GlobalTheory.NormInert.main <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.global_norm_of_local_norms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r) (x : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q), GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q x = x → (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ z : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, z * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q _ z = 1 ⊗ₜ x) → (∀ v : InfinitePlace (maximalRealSubfield E), ∃ z : v.Completion ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, z * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q _ z = 1 ⊗ₜ x) → ∃ y : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, y * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q y = x := by
  first | exact @GlobalTheory.HasseFld.hasse_norm | (intros; apply GlobalTheory.HasseFld.hasse_norm <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.conj_transpose_mul_posDef : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (h : GL (Fin n) E) (τ : E →+* ℂ), ((cT (IsCMField.complexConj E).toRingEquiv.toRingHom (h⁻¹).val * (h⁻¹).val).map τ).PosDef := by
  first | exact @GlobalTheory.UnitaryClasses.posDef_cT_inv_mul_inv | (intros; apply GlobalTheory.UnitaryClasses.posDef_cT_inv_mul_inv <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.NormHasseCent

theorem inv_hh {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (k : GL (Fin n) K) : (k.val * cT σ k.val)⁻¹ = cT σ (k⁻¹).val * (k⁻¹).val :=
  Matrix.inv_eq_right_inv (by rw [Matrix.mul_assoc, cT_units_left', Units.mul_inv])

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ h : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → h⁻¹ * γ * h ∈ UE E n → (∀ w : Pl E, ¬ IsSplitAt w → ∃ c : Matrix (Fin n) (Fin n) (w.adicCompletion E), c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val * c ∧ cT (cj w) c * c = ((GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h).val * cT (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h).val)⁻¹) → ∃ c : Matrix (Fin n) (Fin n) E, c * γ.val = γ.val * c ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom c * c = (h.val * cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val)⁻¹ := by
  intro E _ _ _ hU n γ h hγ hP hconj hloc
  set σ := (IsCMField.complexConj E).toRingEquiv.toRingHom with hσdef
  have hσ : ∀ x, σ (σ x) = x := fun x => IsCMField.complexConj_apply_apply E x
  set N := cT σ (h⁻¹).val * (h⁻¹).val with hN
  have hγ' : cT σ γ.val * 1 * γ.val = 1 := hγ
  have hinv := inv_of_unit σ h γ hconj
  have hγγ : γ.val * cT σ γ.val = 1 := by
    rw [Matrix.mul_one] at hγ'; exact mul_eq_one_comm.1 hγ'
  have hcomm : γ.val * N = N * γ.val := by
    have := congrArg (γ.val * ·) hinv
    simp only [← Matrix.mul_assoc, hγγ, Matrix.one_mul] at this
    rw [hN]; simpa only [Matrix.mul_assoc] using this.symm
  obtain ⟨m, hm⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm γ.val N hP.2.2.1 hcomm
  have hherm : cT σ (aeval γ.val m) = aeval γ.val m := by
    rw [← hm]; exact herm_of σ hσ h
  have hM : (h.val * cT σ h.val)⁻¹ = aeval γ.val m := by rw [inv_hh, ← hN, hm]
  have hsr := GlobalTheory.T.isConjSelfReciprocal_of_dvd_elliptic_polynomial E n _ hP
  have hfix := GlobalTheory.T.involution_fixes_polynomial_image E n γ hγ hP m hherm
  have hloc' : ∀ w : Pl E, ¬ IsSplitAt w → ∃ c : Matrix (Fin n) (Fin n) (w.adicCompletion E), c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val * c ∧ cT (cj w) c * c = (aeval γ.val m).map (algebraMap E (w.adicCompletion E)) := (fun w hw => by
    obtain ⟨c, hc1, hc2⟩ := hloc w hw
    refine ⟨c, hc1, ?_⟩
    rw [hc2, inv_hh, ← hm, hN, ← map_inv]
    rw [Matrix.map_mul, cT_map hU w hw]; rfl)
  have hfin : ∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r), Q.1 ∣ γ.val.charpoly → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) = (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ z : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, z * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q _ z = 1 ⊗ₜ (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) := by
    intro r Q hQ hx v
    by_cases hs : ∃ w w' : Pl E, w ≠ w' ∧ w.under (𝓞 (maximalRealSubfield E)) = v ∧ w'.under (𝓞 (maximalRealSubfield E)) = v
    · exact GlobalTheory.T.local_norm_at_split_place E r Q _ hx v hs
    · refine GlobalTheory.T.nonsplit_centraliser_norm_element E hU n γ hγ hP m hloc' r Q hQ hx v (fun w w' hw hw' => ?_)
      by_contra hne
      exact hs ⟨w, w', hne, hw, hw'⟩
  have hinf := GlobalTheory.T.totally_positive_real_places E n γ hγ hP m (fun τ => by rw [← hm]; exact GlobalTheory.T.conj_transpose_mul_posDef E n h τ)
  obtain ⟨c, hc1, hc2⟩ := GlobalTheory.T.exists_norm_solution_fields E n γ hγ hP hsr m (fun r Q hQ =>
    GlobalTheory.T.global_norm_of_local_norms E r Q _ (hfix r Q hQ) (hfin r Q hQ (hfix r Q hQ)) (hinf r Q hQ (hfix r Q hQ)))
  exact ⟨c, hc1, by rw [hc2, hM]⟩

end GlobalTheory.NormHasseCent
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.nonsplit_place_norm_centraliser : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ h : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → h⁻¹ * γ * h ∈ UE E n → (∀ w : Pl E, ¬ IsSplitAt w → ∃ c : Matrix (Fin n) (Fin n) (w.adicCompletion E), c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val * c ∧ cT (cj w) c * c = ((GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h).val * cT (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h).val)⁻¹) → ∃ c : Matrix (Fin n) (Fin n) E, c * γ.val = γ.val * c ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom c * c = (h.val * cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val)⁻¹ := by
  first | exact @GlobalTheory.NormHasseCent.main | (intros; apply GlobalTheory.NormHasseCent.main <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.exists_global_hermitian_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∃ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ ∧ H₀.det ≠ 0 ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ ∧ (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) := by
  first | exact @GlobalTheory.RefForm.cT_mul | exact @GlobalTheory.RefForm.cT_cT_conj | exact @GlobalTheory.RefForm.det_cT_conj | exact @GlobalTheory.RefForm.cT_diag_mul_diag | exact @GlobalTheory.RefForm.assemble | exact @GlobalTheory.RefForm.exists_roots_enum | exact @GlobalTheory.RefForm.powBasis_apply | exact @GlobalTheory.RefForm.vandermonde_mul_compMat | exact @GlobalTheory.RefForm.charpoly_compMat | exact @GlobalTheory.RefForm.trace_semiconj | exact @GlobalTheory.RefForm.exists_model | exact @GlobalTheory.RefForm.map_cT_complexConj | exact @GlobalTheory.RefForm.exists_refForm | (intros; apply GlobalTheory.RefForm.exists_refForm <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.hermitian_local_global_existence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ H : ∀ w : Pl E, Matrix (Fin n) (Fin n) (w.adicCompletion E), (∀ w, ¬ IsSplitAt w → IsHerm (cj w) (H w) ∧ (H w).det ≠ 0 ∧ cT (cj w) (γ₀.val.map (algebraMap E (w.adicCompletion E))) * H w * γ₀.val.map (algebraMap E (w.adicCompletion E)) = H w) → (∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ k m : GL (Fin n) (w.adicCompletion E), k⁻¹ * GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * k ∈ GlobalTheory.LFun.KGL w n ∧ m ∈ GlobalTheory.LFun.KGL w n ∧ m.val = cT (cj w) k.val * H w * k.val) → (∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * γ₀.val.map (algebraMap E (w.adicCompletion E)) = γ₀.val.map (algebraMap E (w.adicCompletion E)) * c.val ∧ H w = cT (cj w) c.val * H₀.map (algebraMap E (w.adicCompletion E)) * c.val) := by first | exact @GlobalTheory.UsideLeaf.hermitian_local_global_existence.main | exact GlobalTheory.UsideLeaf.hermitian_local_global_existence.main
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_signature_realisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S → ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1) := by
  first | exact @GlobalTheory.UnitaryClasses.refSign_prod | exact GlobalTheory.UnitaryClasses.refSign_prod | (intros; apply GlobalTheory.UnitaryClasses.refSign_prod <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.hermitian_form_local_global : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S → ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1) → ∀ H : ∀ w : Pl E, Matrix (Fin n) (Fin n) (w.adicCompletion E), (∀ w, ¬ IsSplitAt w → IsHerm (cj w) (H w) ∧ (H w).det ≠ 0 ∧ cT (cj w) (γ₀.val.map (algebraMap E (w.adicCompletion E))) * H w * γ₀.val.map (algebraMap E (w.adicCompletion E)) = H w) → (∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * γ₀.val.map (algebraMap E (w.adicCompletion E)) = γ₀.val.map (algebraMap E (w.adicCompletion E)) * c.val ∧ H w = cT (cj w) c.val * H₀.map (algebraMap E (w.adicCompletion E)) * c.val) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H w) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1) → ∃ H' : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H' ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H' * γ₀.val = H' ∧ (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H'.map τ = cT (starRingEnd ℂ) Q * Q) ∧ ∀ w, ¬ IsSplitAt w → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * γ₀.val.map (algebraMap E (w.adicCompletion E)) = γ₀.val.map (algebraMap E (w.adicCompletion E)) * c.val ∧ H'.map (algebraMap E (w.adicCompletion E)) = cT (cj w) c.val * H w * c.val := by
  first | exact @PositivityTheory.BCUSide.L.hermitian_form_local_global | exact PositivityTheory.BCUSide.L.hermitian_form_local_global
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitaryClasses.ExistForm

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S → ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H : ∀ w : Pl E, Matrix (Fin n) (Fin n) (w.adicCompletion E), (∀ w, ¬ IsSplitAt w → IsHerm (cj w) (H w) ∧ (H w).det ≠ 0 ∧ cT (cj w) (γ₀.val.map (algebraMap E (w.adicCompletion E))) * H w * γ₀.val.map (algebraMap E (w.adicCompletion E)) = H w) → (∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ k m : GL (Fin n) (w.adicCompletion E), k⁻¹ * GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * k ∈ GlobalTheory.LFun.KGL w n ∧ m ∈ GlobalTheory.LFun.KGL w n ∧ m.val = cT (cj w) k.val * H w * k.val) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H w) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1) → ∃ H' : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H' ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H' * γ₀.val = H' ∧ (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H'.map τ = cT (starRingEnd ℂ) Q * Q) ∧ ∀ w, ¬ IsSplitAt w → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * γ₀.val.map (algebraMap E (w.adicCompletion E)) = γ₀.val.map (algebraMap E (w.adicCompletion E)) * c.val ∧ H'.map (algebraMap E (w.adicCompletion E)) = cT (cj w) c.val * H w * c.val := by
  intro E _ _ _ hU S hS n γ₀ hP H hH hlat hsg
  obtain ⟨H₀, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_global_hermitian_form E n γ₀ hP
  exact GlobalTheory.T.hermitian_form_local_global E hU S hS n γ₀ hP H₀ h1 h2 h3 h4 (GlobalTheory.T.hermitian_form_signature_realisation E hU S hS n γ₀ hP H₀ h1 h2 h3 h4) H hH
    (GlobalTheory.T.hermitian_local_global_existence E hU n γ₀ hP H₀ h1 h2 h3 H hH hlat) hsg

end GlobalTheory.UnitaryClasses.ExistForm
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.hermitian_local_data_almost_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S → ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H : ∀ w : Pl E, Matrix (Fin n) (Fin n) (w.adicCompletion E), (∀ w, ¬ IsSplitAt w → IsHerm (cj w) (H w) ∧ (H w).det ≠ 0 ∧ cT (cj w) (γ₀.val.map (algebraMap E (w.adicCompletion E))) * H w * γ₀.val.map (algebraMap E (w.adicCompletion E)) = H w) → (∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ k m : GL (Fin n) (w.adicCompletion E), k⁻¹ * GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * k ∈ GlobalTheory.LFun.KGL w n ∧ m ∈ GlobalTheory.LFun.KGL w n ∧ m.val = cT (cj w) k.val * H w * k.val) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H w) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1) → ∃ H' : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H' ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H' * γ₀.val = H' ∧ (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H'.map τ = cT (starRingEnd ℂ) Q * Q) ∧ ∀ w, ¬ IsSplitAt w → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * γ₀.val.map (algebraMap E (w.adicCompletion E)) = γ₀.val.map (algebraMap E (w.adicCompletion E)) * c.val ∧ H'.map (algebraMap E (w.adicCompletion E)) = cT (cj w) c.val * H w * c.val := by
  first | exact @GlobalTheory.UnitaryClasses.ExistForm.main | (intros; apply GlobalTheory.UnitaryClasses.ExistForm.main <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UnitaryClasses

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem conjGL : ∀ (K : Type) [Field K] (n : ℕ) (a b : GL (Fin n) K), a.val.charpoly = b.val.charpoly → a.val.charpoly.Separable → ∃ h : GL (Fin n) K, b = h⁻¹ * a * h := GlobalTheory.T.exists_conj_GL_of_charpoly_eq_of_separable

theorem companionEll : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), ∀ P ∈ Ell E n, ∃ a : GL (Fin n) E, a.val.charpoly = P := GlobalTheory.T.exists_GL_charpoly_eq_of_mem_Ell

theorem unitConj : ∀ (K : Type) [Field K] (σ : K →+* K) (n : ℕ) (γ h : GL (Fin n) K), (∃ g ∈ UJ σ (1 : Matrix (Fin n) (Fin n) K), h⁻¹ * γ * h = g⁻¹ * γ * g) ↔ ∃ c : Matrix (Fin n) (Fin n) K, c * γ.val = γ.val * c ∧ cT σ c * c = (h.val * cT σ h.val)⁻¹ := GlobalTheory.T.exists_unitary_conj_iff_exists_centralizer_norm

theorem normHasse : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ h : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → h⁻¹ * γ * h ∈ UE E n → (∀ w : Pl E, ¬ IsSplitAt w → ∃ c : Matrix (Fin n) (Fin n) (w.adicCompletion E), c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val * c ∧ cT (cj w) c * c = ((GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h).val * cT (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h).val)⁻¹) → ∃ c : Matrix (Fin n) (Fin n) E, c * γ.val = γ.val * c ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom c * c = (h.val * cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val)⁻¹ := GlobalTheory.T.nonsplit_place_norm_centraliser

theorem signProd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S → ∀ d : E, d ≠ 0 → (∀ τ : E →+* ℂ, ∃ r : ℝ, 0 < r ∧ τ d = r) → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else (-1) ^ ordL (algebraMap E (w.adicCompletion E) d)) = 1 := GlobalTheory.T.finprod_nonsplit_sign_totallyPositive_eq_one

theorem gramPos : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (V : Submodule E (Fin n → E)), (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det ≠ 0 ∧ ∀ τ : E →+* ℂ, ∃ r : ℝ, 0 < r ∧ τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det = r := GlobalTheory.T.gram_det_hermitian_totally_positive

theorem sgnConj : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K), (∀ x, Valued.v (σ x) = Valued.v x) → ∀ (n : ℕ) (Q : K[X]) (a k : GL (Fin n) K), sgnOn σ 1 Q (k⁻¹ * a * k).val = sgnOn σ (cT σ (k⁻¹).val * (k⁻¹).val) Q a.val := GlobalTheory.T.sesquilinearDetOrdSignOnKernel_conj_GL

theorem baseChangeSign : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (H A : Matrix (Fin n) (Fin n) E), (-1 : ℂ) ^ ordL (gramOn (cj w) (H.map (algebraMap E (w.adicCompletion E))) (LinearMap.ker (Matrix.toLin' (A.map (algebraMap E (w.adicCompletion E)))))).det = (-1) ^ ordL (algebraMap E (w.adicCompletion E) (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H (LinearMap.ker (Matrix.toLin' A))).det) := GlobalTheory.T.gramKernelSign_nonsplit_baseChange_eq

theorem existForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S → ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H : ∀ w : Pl E, Matrix (Fin n) (Fin n) (w.adicCompletion E), (∀ w, ¬ IsSplitAt w → IsHerm (cj w) (H w) ∧ (H w).det ≠ 0 ∧ cT (cj w) (γ₀.val.map (algebraMap E (w.adicCompletion E))) * H w * γ₀.val.map (algebraMap E (w.adicCompletion E)) = H w) → (∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ k m : GL (Fin n) (w.adicCompletion E), k⁻¹ * GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * k ∈ GlobalTheory.LFun.KGL w n ∧ m ∈ GlobalTheory.LFun.KGL w n ∧ m.val = cT (cj w) k.val * H w * k.val) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H w) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1) → ∃ H' : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H' ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H' * γ₀.val = H' ∧ (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H'.map τ = cT (starRingEnd ℂ) Q * Q) ∧ ∀ w, ¬ IsSplitAt w → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * γ₀.val.map (algebraMap E (w.adicCompletion E)) = γ₀.val.map (algebraMap E (w.adicCompletion E)) * c.val ∧ H'.map (algebraMap E (w.adicCompletion E)) = cT (cj w) c.val * H w * c.val := GlobalTheory.T.hermitian_local_data_almost_all

theorem landherrStd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) E), IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H.map τ = cT (starRingEnd ℂ) Q * Q) → (∀ w : Pl E, ¬ IsSplitAt w → ∃ g : Matrix (Fin n) (Fin n) (w.adicCompletion E), H.map (algebraMap E (w.adicCompletion E)) = cT (cj w) g * g) → ∃ h : GL (Fin n) E, H = cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val * h.val := GlobalTheory.T.landherr_standard_definite_hermitian_cmField

theorem part1 (hU : Unr E) {n : ℕ} {S : Set (Pl E)} (hS : IsSection S) {P : E[X]} (hP : P ∈ Ell E n) (γ γ' : UE E n)
    (h1 : γ.1.val.charpoly = P) (h2 : γ'.1.val.charpoly = P)
    (hloc : ∀ w ∈ S, ∃ g : UL n w, locPt w γ' = g⁻¹ * locPt w γ * g) : ∃ g : UE E n, γ' = g⁻¹ * γ * g := by
  obtain ⟨h, hh⟩ := conjGL E n γ.1 γ'.1 (h1.trans h2.symm) (h1 ▸ hP.2.2.1)
  have hγ' : h⁻¹ * γ.1 * h ∈ UE E n := hh ▸ γ'.2
  obtain ⟨c, hc1, hc2⟩ := normHasse E hU n γ.1 h γ.2 (h1 ▸ hP) hγ' (fun w hw => by
    obtain ⟨g, hg⟩ := hloc w (mem_S hS hw)
    have hUL : UL n w = UJ (cj w) 1 := by unfold UL; rw [if_neg hw]
    refine (unitConj _ (cj w) n _ _).1 ⟨g.1, hUL ▸ g.2, ?_⟩
    have := congrArg Subtype.val hg
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, locPt_val hU] at this
    rw [← map_inv, ← map_mul, ← map_mul, ← hh]; exact this)
  obtain ⟨g, hg, hgg⟩ := (unitConj E _ n γ.1 h).2 ⟨c, hc1, hc2⟩
  exact ⟨⟨g, hg⟩, Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; rw [hh, hgg])⟩

theorem part2 (hU : Unr E) {n : ℕ} {S : Set (Pl E)} (hS : IsSection S) (γ : UE E n) (P₁ : E[X]) :
    ∏ᶠ w ∈ S, kapSign n w (atPl w P₁) (locPt w γ).1 = 1 := by
  obtain ⟨hd0, hdpos⟩ := gramPos E n (LinearMap.ker (Matrix.toLin' (aeval γ.1.val P₁)))
  rw [← signProd E hU S hS _ hd0 hdpos]
  apply finprod_mem_congr rfl
  intro w _
  by_cases hw : IsSplitAt w
  · rw [if_pos hw]; unfold kapSign; rw [if_pos hw]
  · rw [if_neg hw, kapSign_eq w hw, locPt_val hU]
    unfold sgnOn
    have hA := aeval_map_mat w γ.1.val P₁
    have := baseChangeSign E hU w hw n 1 (aeval γ.1.val P₁)
    rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
    rw [← this, ← hA]
    rfl

theorem part3 (hU : Unr E) {n : ℕ} {S : Set (Pl E)} (hS : IsSection S) {P : E[X]} (hP : P ∈ Ell E n)
    (y : ∀ w : Pl E, UL n w) (hy : ∀ w, (y w).1.val.charpoly = atPl w P) (hK : ∀ᶠ w in cofinite, y w ∈ KL n w)
    (hsg : ∀ P₁ : E[X], P₁.Monic → P₁ ∣ P → ∏ᶠ w ∈ S, kapSign n w (atPl w P₁) (y w).1 = 1) :
    ∃ γ : UE E n, γ.1.val.charpoly = P ∧ ∀ w ∈ S, ∃ g : UL n w, locPt w γ = g⁻¹ * y w * g := by
  obtain ⟨γ₀, hγ₀⟩ := companionEll E n P hP
  have hAcp : ∀ w : Pl E, (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀).val.charpoly = atPl w P :=
    fun w => by rw [← hγ₀]; exact Matrix.charpoly_map _ _
  have hsep : ∀ w : Pl E, (atPl w P).Separable := fun w => hP.2.2.1.map
  have hk : ∀ w : Pl E, ∃ k : GLw n w,
      (y w).1 = k⁻¹ * GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * k := fun w =>
    conjGL _ n _ (y w).1 ((hAcp w).trans (hy w).symm) (hAcp w ▸ hsep w)
  choose k hk using hk
  have hinvol : ∀ w : Pl E, ∀ x, cj w (cj w x) = x := fun w => (GlobalTheory.ConjAtPlace.main E hU w).2.1
  have hval : ∀ w : Pl E, ∀ x, Valued.v (cj w x) = Valued.v x := fun w => (GlobalTheory.ConjAtPlace.main E hU w).2.2.1
  have hUL : ∀ w : Pl E, ¬ IsSplitAt w → UL n w = UJ (cj w) 1 := fun w hw => by unfold UL; rw [if_neg hw]
  have hyU : ∀ w : Pl E, ¬ IsSplitAt w → cT (cj w) (y w).1.val * 1 * (y w).1.val = 1 := fun w hw => by
    have h3 : ∀ z : GLw n w, z ∈ UL n w → cT (cj w) z.val * 1 * z.val = 1 := by
      intro z hz; unfold UL at hz; rw [if_neg hw] at hz; exact hz
    exact h3 _ (y w).2
  obtain ⟨H', hH'h, hH'i, hH'p, hH'l⟩ := existForm E hU S hS n γ₀ (hγ₀ ▸ hP)
    (fun w => cT (cj w) ((k w)⁻¹).val * ((k w)⁻¹).val)
    (fun w hw => ⟨herm_of _ (hinvol w) _, det_ne _ _,
      inv_of_unit _ (k w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀) (hk w ▸ hyU w hw)⟩)
    (hK.mono fun w hw _ => ⟨k w, 1, by rw [← hk w]; exact (Subgroup.mem_subgroupOf).1 hw, one_mem _,
      (one_of _ (k w)).symm⟩)
    (fun P₁ hm hd => by
      refine Eq.trans ?_ (hsg P₁ hm (hγ₀ ▸ hd))
      apply finprod_mem_congr rfl
      intro w _
      by_cases hw : IsSplitAt w
      · rw [if_pos hw]; unfold kapSign; rw [if_pos hw]
      · rw [if_neg hw, kapSign_eq w hw, hk w, sgnConj _ (cj w) (hval w)]
        rfl)
  obtain ⟨h, hh⟩ := landherrStd E hU n H' hH'h hH'p (fun w hw => by
    obtain ⟨c, -, hc⟩ := hH'l w hw
    exact ⟨((k w)⁻¹).val * c.val, by rw [hc, cT_mul]; simp only [Matrix.mul_assoc]⟩)
  have hγU : h * γ₀ * h⁻¹ ∈ UE E n := unit_of_form _ γ₀ h (by rw [← hh]; exact hH'i)
  refine ⟨⟨_, hγU⟩, ?_, fun w hwS => ?_⟩
  · show (h.val * γ₀.val * (h⁻¹).val).charpoly = P
    rw [Matrix.coe_units_inv, ← hγ₀]
    exact Matrix.charpoly_units_conj h γ₀.val
  · by_cases hw : IsSplitAt w
    · have hb : ((locPt w (⟨_, hγU⟩ : UE E n) : UL n w) : GLw n w).val.charpoly = (y w).1.val.charpoly := by
        rw [locPt_val hU, hy w, ← hAcp w]
        show ((h * γ₀ * h⁻¹ : GL (Fin n) E).val.map _).charpoly = (γ₀.val.map _).charpoly
        rw [Matrix.charpoly_map, Matrix.charpoly_map]
        congr 1
        show (h.val * γ₀.val * (h⁻¹).val).charpoly = _
        rw [Matrix.coe_units_inv]
        exact Matrix.charpoly_units_conj h γ₀.val
      obtain ⟨h', hh'⟩ := conjGL _ n (y w).1 _ hb.symm ((hy w) ▸ hsep w)
      have hmem : h' ∈ UL n w := by unfold UL; rw [if_pos hw]; trivial
      exact ⟨⟨h', hmem⟩, Subtype.ext (by simpa using hh')⟩
    · obtain ⟨c, hc1, hc2⟩ := hH'l w hw
      have hg : (k w)⁻¹ * c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h)⁻¹ ∈ UL n w := by
        rw [hUL w hw]
        refine unit_of_two _ (k w) c (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) h) _ hc2 ?_
        rw [hh, Matrix.map_mul, cT_map hU w hw]; rfl
      refine ⟨⟨_, hg⟩, Subtype.ext ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [locPt_val hU, hk w]
      have hcA : c * GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ =
          GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * c := Units.ext hc1
      have key : ∀ x : GLw n w, c⁻¹ * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * (c * x)) =
          GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * x := fun x => by
        rw [← mul_assoc _ c x, ← hcA, mul_assoc, inv_mul_cancel_left]
      show GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (h * γ₀ * h⁻¹) = _
      simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, key]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, (∀ γ γ' : UE E n, γ.1.val.charpoly = P → γ'.1.val.charpoly = P → (∀ w ∈ S, ∃ g : UL n w, locPt w γ' = g⁻¹ * locPt w γ * g) → ∃ g : UE E n, γ' = g⁻¹ * γ * g) ∧ (∀ γ : UE E n, γ.1.val.charpoly = P → ∀ P₁ : E[X], P₁.Monic → P₁ ∣ P → ∏ᶠ w ∈ S, kapSign n w (atPl w P₁) (locPt w γ).1 = 1) ∧ ∀ y : ∀ w : Pl E, UL n w, (∀ w, (y w).1.val.charpoly = atPl w P) → (∀ᶠ w in cofinite, y w ∈ KL n w) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ P → ∏ᶠ w ∈ S, kapSign n w (atPl w P₁) (y w).1 = 1) → ∃ γ : UE E n, γ.1.val.charpoly = P ∧ ∀ w ∈ S, ∃ g : UL n w, locPt w γ = g⁻¹ * y w * g := by
  intro E _ _ _ hU n _ S hS P hP
  exact ⟨fun γ γ' h1 h2 hl => part1 hU hS hP γ γ' h1 h2 hl, fun γ _ P₁ _ _ => part2 hU hS γ P₁,
    fun y hy hK hsg => part3 hU hS hP y hy hK hsg⟩

end GlobalTheory.UnitaryClasses
end
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.unitary_conjugacy_sign_product : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, (∀ γ γ' : UE E n, γ.1.val.charpoly = P → γ'.1.val.charpoly = P → (∀ w ∈ S, ∃ g : UL n w, locPt w γ' = g⁻¹ * locPt w γ * g) → ∃ g : UE E n, γ' = g⁻¹ * γ * g) ∧ (∀ γ : UE E n, γ.1.val.charpoly = P → ∀ P₁ : E[X], P₁.Monic → P₁ ∣ P → ∏ᶠ w ∈ S, kapSign n w (atPl w P₁) (locPt w γ).1 = 1) ∧ ∀ y : ∀ w : Pl E, UL n w, (∀ w, (y w).1.val.charpoly = atPl w P) → (∀ᶠ w in cofinite, y w ∈ KL n w) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ P → ∏ᶠ w ∈ S, kapSign n w (atPl w P₁) (y w).1 = 1) → ∃ γ : UE E n, γ.1.val.charpoly = P ∧ ∀ w ∈ S, ∃ g : UL n w, locPt w γ = g⁻¹ * y w * g := by
  first | exact @GlobalTheory.UnitaryClasses.main | (intros; apply GlobalTheory.UnitaryClasses.main <;> assumption)
end
