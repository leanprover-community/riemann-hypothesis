import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToDoubledFirstFactorBigCellInertPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAntiInvariantSignAdeleSplitPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMulFirstFactorLagrangianAl
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NablaUnipotentMemIntegralDoubledUnipotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrixMemIntegralSiegelPar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitDoublingTMatrixMulInverseEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorLiftedStatement

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitDblGenLeft

open GlobalTheory.InertDbl GlobalTheory.InertBigCell

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sq_smul_eq {n : Type} {v : Pl F} {c : AE F E} (hc : ∀ z : AE F E, At (evFin F v) z → c * c * z = z)
    {X : Matrix n n (AE F E)} (hX : At (evFin F v) X) : (c * c) • X = X := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul]
  exact hc _ fun u hu => by simpa using congrFun (congrFun (hX u hu) i) j

theorem inlD_mem_closure_of_split {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {d : ℕ} (W : Spc F E d) (v : Pl F)
    (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (k : UA σ W.J) (hk : k ∈ GlobalTheory.InertSph.KAt σ W v) :
    inlD σ W k ∈ Subgroup.closure (ParD σ W v ∪ NabD σ W v) := by
  obtain ⟨c, hcσ, hcat, hcsq, hclat⟩ := GlobalTheory.T.exists_antiInvariant_sign_adele_splitPlace F E σ B hB v hv
  obtain ⟨p, hp, hpm⟩ := GlobalTheory.T.exists_parD_matD_eq_diagonalFixingDoublingMatrix F E σ d W v h2 c hcσ hcat (hclat d W)
  obtain ⟨n, hn, hnm⟩ := GlobalTheory.T.nablaUnipotent_mem_integralDoubledUnipotent F E σ d W v h2 c hcσ (hclat d W) k hk
  have e1 : mat k * mat k⁻¹ = 1 := by
    show mat (k * k⁻¹) = 1
    rw [mul_inv_cancel]; rfl
  have e2 : mat k⁻¹ * mat k = 1 := by
    show mat (k⁻¹ * k) = 1
    rw [inv_mul_cancel]; rfl
  have hsq : (c * c) • (mat k - 1) = mat k - 1 := sq_smul_eq hcsq hk.1
  have hid := GlobalTheory.T.diagonalFixingDoublingMatrix_mul_fromBlocks_mul_diagCols F E d c (mat k) (mat k⁻¹) e1 e2 hsq
  have ht := GlobalTheory.T.splitDoublingTMatrix_mul_inverse_eq_one F E d c (mat k) (mat k⁻¹) e1 hsq
  let t : GL (Fin d) (AE F E) := ⟨GlobalTheory.SplitDblGen.tMat c (mat k), GlobalTheory.SplitDblGen.tMat c (mat k⁻¹), ht, mul_eq_one_comm.1 ht⟩
  have hq : n⁻¹ * (p * inlD σ W k) ∈ ParD σ W v := by
    refine ⟨KAtD_mul (KAtD_inv hn.1) (KAtD_mul hp.1 (inlD_mem hk)), t, ?_⟩
    have en : matD n⁻¹ * matD n = 1 := (n.1).inv_val
    show matD n⁻¹ * (matD p * matD (inlD σ W k)) * diagCols (Fin d) = diagCols (Fin d) * GlobalTheory.SplitDblGen.tMat c (mat k)
    rw [matD_inlD, hpm]
    rw [← hnm] at hid
    erw [Matrix.mul_assoc, hid, ← Matrix.mul_assoc, ← Matrix.mul_assoc, en, Matrix.one_mul]
    rfl
  have e : inlD σ W k = p⁻¹ * (n * (n⁻¹ * (p * inlD σ W k))) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inl hp)))
    (Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr hn)) (Subgroup.subset_closure (Or.inl hq)))

theorem inlD_mem_closure_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, GlobalTheory.InertDbl.inlD σ G.V' k ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.V' v ∪ GlobalTheory.InertDbl.NabD σ G.V' v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv _ h2 k hk
  exact inlD_mem_closure_of_split hT.base G.V' v hv h2 k hk

end GlobalTheory.SplitDblGenLeft
end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antidiagonalUnipotent_conj_siegel_square_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, GlobalTheory.InertDbl.inlD σ G.V' k ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.V' v ∪ GlobalTheory.InertDbl.NabD σ G.V' v) := by
  atlas_forward_decl GlobalTheory.SplitDblGenLeft.inlD_mem_closure_left
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitScalarV

theorem scalar_eq_one_split_left : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, ∀ c : ℂ, Acts (evFin F v) (om' (k, 1)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hsp hT hψ h2 hvac k hk c hc
  obtain ⟨d', hd', -, dd, omd, hdc, hws, hres⟩ := hTr.weil'.2.1
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (Fin a' × Fin (a + a')) v
  have hV := hTr.geo.hM'.vac v
  have hSB : G.M'.vac v ∈ SB _ := hV.1
  have hne : G.M'.vac v ≠ 0 := hV.2.1
  have hRv := hR _ hSB
  set Ψ := tens (evFin F v) (G.M'.vac v) R with hΨdef
  have hΨ : Ψ ∈ schA F _ := hRv.2
  have hΨ' : (fun x => star (Ψ x)) ∈ schA F _ := GlobalTheory.SchAConj.star_mem_schA F _ Ψ hΨ
  let H : Subgroup (GlobalTheory.InertDbl.UD σ G.V') :=
    { carrier := {g | omd g (GlobalTheory.InertDbl.dblFun Ψ) = GlobalTheory.InertDbl.dblFun Ψ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hgen := (GlobalTheory.T.antidiagonalUnipotent_conj_siegel_square_split) F E σ B a a' G X om om' hTr v hsp hψ h2 k hk
  have hle : Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.V' v ∪ GlobalTheory.InertDbl.NabD σ G.V' v) ≤ H := by
    rw [Subgroup.closure_le]
    rintro g (hg | hg)
    · exact (GlobalTheory.T.vacuum_split_place_indicator_dual_pair) hP F E σ B a a' G X om om' hTr v hsp hT hψ h2 hvac d' hd' dd omd hdc hws R hR0 hRv g hg
    · exact (GlobalTheory.T.vacuum_split_place_indicator_lifted) hP F E σ B a a' G X om om' hTr v hsp hT hψ h2 hvac d' hd' dd omd hdc hws R hR0 hRv g hg
  have hfix : omd (GlobalTheory.InertDbl.inlD σ G.V' k) (GlobalTheory.InertDbl.dblFun Ψ) = GlobalTheory.InertDbl.dblFun Ψ := hle hgen
  have hact : om' (k, 1) Ψ = c • Ψ := by
    rw [hΨdef, hc R hRv]
    funext x
    simp [tens, mul_assoc]
  have hr := hres k (GlobalTheory.InertDbl.inlD σ G.V' k) rfl Ψ hΨ (fun x => star (Ψ x)) hΨ'
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply] at hr
  rw [hact] at hr
  have key : c • GlobalTheory.InertDbl.dblFun Ψ = GlobalTheory.InertDbl.dblFun Ψ := by
    have e1 : omd (GlobalTheory.InertDbl.inlD σ G.V' k) (GlobalTheory.InertDbl.dblFun Ψ) = c • GlobalTheory.InertDbl.dblFun Ψ := by
      unfold GlobalTheory.InertDbl.dblFun
      rw [hr]
      funext x
      simp only [boxFun, Pi.smul_apply, smul_eq_mul]
      ring
    rw [← e1, hfix]
  obtain ⟨y, hy⟩ : ∃ y, G.M'.vac v y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  let x : Fin a' × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
  have hRx : R x = R 0 := by
    have := hRv.1 0 x (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
    simpa using this
  have hΨx : Ψ x ≠ 0 := by
    simp only [hΨdef, tens, x, GlobalTheory.LatVac.evFin_liftV, hRx]
    exact mul_ne_zero hy hR0
  have h2' := congrFun key (Sum.elim x x)
  simp only [GlobalTheory.InertDbl.dblFun, boxFun, Pi.smul_apply, smul_eq_mul] at h2'
  have hz : Ψ x * star (Ψ x) ≠ 0 := mul_ne_zero hΨx (star_ne_zero.mpr hΨx)
  have h3 : (Sum.elim x x ∘ Sum.inl : Fin a' × Fin (a + a') → AF F) = x := rfl
  have h4 : (Sum.elim x x ∘ Sum.inr : Fin a' × Fin (a + a') → AF F) = x := rfl
  rw [h3, h4] at h2'
  exact (mul_eq_right₀ hz).mp h2'

end GlobalTheory.SplitScalarV
end
end
