import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldCut
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelExistenceOfSiegel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelSmallK
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelExistenceOfSiegelSmall
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldSMod
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldMSpec
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldMCut
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.AdelicCoordinatesEvalZeroFormMemAdmissible
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.DiagonalColumnInclusion.IncMDiagCols
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.EDApply
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.EmbQMapApply
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SmallSTop
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SmallS
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SiegelP
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Siegel
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SiegelC
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldDefs

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem modelEx_of_k (hS : _root_.PositivityTheory.SiegelWeilFormula.Ald.SDarb_k) (hE : _root_.PositivityTheory.SiegelWeilFormula.Ald.SEv_k) (hB : _root_.PositivityTheory.SiegelWeilFormula.Ald.BigT_k) (hF : SliceFacts) (hO : OpBox) (hU : SubSplit)
    (hC : _root_.PositivityTheory.SiegelWeilFormula.Ald.ChartFacts_k) (hG : _root_.PositivityTheory.SiegelWeilFormula.Ald.SiegelSmall_k) (hA' : _root_.PositivityTheory.SiegelWeilFormula.Ald.SmallS_k) : _root_.PositivityTheory.SiegelWeilFormula.Ald.ModelEx_k := by
  intro hT hA F E _ _ _ _ _ σ d n h Y b j hn hs hb hε hj
  obtain ⟨ε, e1, e2⟩ := hε
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨dd0, had0, hr0⟩ := hS F E σ d.B d.bs d.m d.n d.A d.Y d.b ε d.r d.s d.ok.good d.ok.hm d.ok.hn d.ok.sign
    d.ok.frame e1
  obtain ⟨dd', had', hr'⟩ := hS F E σ d.B d.bs d.m n d.A Y b ε d.r d.s d.ok.good d.ok.hm hn hs hb e2
  obtain ⟨hev, hkill, htheta⟩ := hE F E σ d.B d.bs d.m n d.A Y b ε d.r d.s d.ok.good d.ok.hm hn hs hb e2 dd' had'
  obtain ⟨S0, S0', C, hC0, hop, hTf⟩ := hB hT hA F E σ d dd0 had0 hr0
  obtain ⟨c1, c2, c3, c4, -⟩ := hC F E σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had'
  let dd1 := GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm
  let S1 := GlobalTheory.TowU.RealComp.reix (eK d.m h) ∘ₗ S0
  let S1' := S0' ∘ₗ GlobalTheory.TowU.RealComp.reix (eK d.m h).symm
  have hop1 : GlobalTheory.TowU.IsOp d.B.ψ (fun w => dd1.e (d.dd.e.symm w)) S1 S1' :=
    GlobalTheory.TowU.RealComp.isOp_comp hop.1 (GlobalTheory.TowU.RealComp.isOp_reix d.B.ψ (eK d.m h))
  have hT1 : ∀ Φ ∈ d.sch, ∀ X, d.T Φ X = C * S1 Φ (crdB d.bs X ∘ eK d.m h) := fun Φ hΦ X => by
    rw [hTf Φ hΦ X]
    simp only [S1, LinearMap.comp_apply, GlobalTheory.TowU.RealComp.reix_apply]
    rw [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
  have hw := d.ok.dbl.weil
  obtain ⟨om1, hom1⟩ := projHom (G := d.G) (fun x => S1 ∘ₗ d.om x ∘ₗ S1')
    (fun x φ hφ => hop1.pres _ (hw.2.1.pres x _ (hop1.pres' φ hφ)))
    (fun φ hφ => by simp [hop1.right φ hφ])
    (fun x y φ hφ => by
      simp only [LinearMap.comp_apply, map_mul, Module.End.mul_apply]
      rw [hop1.left _ (hw.2.1.pres y _ (hop1.pres' φ hφ))])
  have hsp1 : IsUSplitting (adeleClass F) d.B.ψ dd1 (actB (cA σ)) om1 :=
    GlobalTheory.TowU.isUSplitting_of_isOp hψ (fun w => by simp) hop1 hom1 hw.2.1
  have hsr1 : SiegelRule (cA σ) (adeleClass F) d.B.ψ (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) dd1 d.χ
      (diagCols (Fin d.n)) om1 :=
    GlobalTheory.TowU.siegelRule_of_isOp (fun w => by simp) hop1 hom1 hw.2.2
  obtain ⟨hsl1, hsl2, ⟨φ₀, hφ₀, hφ₀0, hφ₀n⟩, -⟩ := hF F (Fin d.m × Fin n × Fin 2) (Fin d.m × Fin 2)
  have hbox := fun g => hO F d.B.ψ hψ _ _ _ _ dd1 d.G (actB (cA σ)) om1 hsp1.toIsSplitting c2 (j g) (c3 g) φ₀ hφ₀ hφ₀0
  let cg : G2 σ Y → ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ) →ₗ[ℂ] ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ) :=
    fun g => slice0 _ _ ∘ₗ om1 (j g) ∘ₗ PositivityTheory.ThKF0.Chr.boxL _ φ₀
  have hbx : ∀ φ' ∈ schA F (Fin d.m × Fin n × Fin 2), boxFun φ' φ₀ ∈ schA F (K1 d.m n) := fun φ' hφ' =>
    GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ' hφ' φ₀ hφ₀
  have hsl0 : ∀ φ' : (Fin d.m × Fin n × Fin 2 → AF F) → ℂ, slice0 _ _ (boxFun φ' φ₀) = φ' := fun φ' => by
    funext x
    simp [slice0, boxFun, hφ₀0]
  have hcg : ∀ g φ', cg g φ' = slice0 _ _ (om1 (j g) (boxFun φ' φ₀)) := fun g φ' => rfl
  have hboxc : ∀ g, ∀ φ' ∈ schA F (Fin d.m × Fin n × Fin 2),
      om1 (j g) (boxFun φ' φ₀) = boxFun (cg g φ') φ₀ := fun g φ' hφ' =>
    (hbox g).2 φ' hφ' φ₀ hφ₀
  obtain ⟨om', hom'⟩ := projHom cg
    (fun g φ' hφ' => hsl1 _ (hsp1.pres _ _ (hbx φ' hφ')))
    (fun φ' hφ' => by rw [hcg, map_one, map_one, Module.End.one_apply, hsl0])
    (fun g g' φ' hφ' => by
      rw [hcg, map_mul, map_mul, Module.End.mul_apply, hboxc g' φ' hφ', hcg g])
  have hboxom : ∀ g, ∀ φ' ∈ schA F (Fin d.m × Fin n × Fin 2), om1 (j g) (boxFun φ' φ₀) = boxFun (om' g φ') φ₀ :=
    fun g φ' hφ' => by rw [hom' g φ' hφ', hboxc g φ' hφ']
  have hsp' : IsUSplitting (adeleClass F) d.B.ψ dd' (actB (cA σ)) om' :=
    hU F d.B.ψ hψ _ _ _ _ _ _ dd1 dd' (emb h b d.b) c1 d.G (G2 σ Y) (actB (cA σ)) (actB (cA σ)) j hj.1 c4 om1 om' hsp1
      φ₀ hφ₀ hφ₀0 hφ₀n (fun g => ⟨φ₀, hφ₀, hφ₀0, fun _ _ => rfl, hboxom g⟩)
  have hsg' := hG F E σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had' om1 hsp1.toIsSplitting hsr1 φ₀ hφ₀ hφ₀0 om'
    hboxom
  obtain ⟨S', hS'1, hS'2⟩ := hA' hT F E σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had' S1 S1' C hC0 hop1 hT1
  refine ⟨Fin d.m × Fin n × Fin 2, inferInstance, dd', om', S', ev0 _,
    ⟨hr', ⟨isLagr_diagCols _ _, hsp', hsg'⟩, hS'1, hev, hkill, hS'2, htheta⟩, ?_⟩
  intro Φ hΦ Φ' hΦ' hres g X hX
  have hS1Φ : S1 Φ ∈ schA F (K1 d.m n) := hop1.pres Φ hΦ
  have hsl : Φ' = C • slice0 _ _ (S1 Φ) := by
    funext x
    obtain ⟨X', rfl⟩ := crdB_surj d.bs x
    have e := hres (ext0 h X') (extend_zero_column h X')
    rw [extension_zero_sub, tof_adapted d.bs d.B.ψ had', hT1 Φ hΦ, crdB_eK h d.bs _ (extend_zero_column h X'), extension_zero_sub] at e
    rw [e]
    rfl
  rw [tof_adapted d.bs d.B.ψ had', hom' g Φ' hΦ', hT1 _ (hw.2.1.pres (j g) Φ hΦ), crdB_eK h d.bs X hX]
  have e1' : S1 (d.om (j g) Φ) = om1 (j g) (S1 Φ) := by
    rw [hom1 (j g) _ hS1Φ]
    simp only [LinearMap.comp_apply]
    rw [hop1.left Φ hΦ]
  rw [e1', show (Sum.elim (crdB d.bs (X.submatrix id (em0 h))) 0 : K1 d.m n → AF F) =
    Sum.elim (crdB d.bs (X.submatrix id (em0 h))) 0 from rfl]
  have e2' := congrFun ((hbox g).1 (S1 Φ) hS1Φ) (crdB d.bs (X.submatrix id (em0 h)))
  simp only [slice0, LinearMap.coe_mk, AddHom.coe_mk] at e2'
  rw [e2', hcg, hsl]
  simp only [slice0, LinearMap.coe_mk, AddHom.coe_mk]
  rw [GlobalTheory.SchwartzBox.boxFun_smul_left, map_smul]
  rfl
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ldexa
open PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
set_option linter.unusedSectionVars false
theorem sEv_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.SEv_k := by
  intro F E _ _ _ _ _ σ B bs m n A Y b ε r s hB hm hn hsg hb hε dd hd
  refine ⟨adelicCoordinatesEvalZeroForm_mem_admissible _, fun z Φ _ => evaluation_zero_unipotent_kill bs A Y b hb dd hd B.ψ z Φ, fun Φ hΦ => ?_⟩
  have hψ : ∀ x : F, B.ψ (algebraMap F (AF F) x) = 1 := hB.std.2.1
  have hs := (summable_of_mem_schA F hΦ).hasSum
  have h := (Equiv.hasSum_iff (xiEquiv (m := m) bs b hb)).mpr hs
  have e1 : thetaSum F Φ = ∑' ξ : Fin m × Fin n × Fin 2 → F, Φ fun i => algebraMap F (AF F) (ξ i) := rfl
  rw [e1]
  convert h using 1
  funext y
  exact evaluation_zero_antisymmetric bs A Y b hb dd hd B.ψ hψ Φ y
end PositivityTheory.SiegelWeilFormula.Ldexa
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald.Asc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end PositivityTheory.SiegelWeilFormula.Ald.Asc
namespace PositivityTheory.SiegelWeilFormula.Ald
open Asc in
theorem bigT_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.BigT_k := by
  intro hT _hA F E _ _ _ _ _ σ d dd0 had hrat
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨S0, S0', hS⟩ := GlobalTheory.T.darbouxCoordinateChange_realised_with_double F E σ d.ok.good.cm d.B.ψ hψ (Fin d.m) (Fin d.n ⊕ Fin d.n) d.κ
    (Fin d.m × Fin d.n × Fin 2) _ d.dd dd0 (by exact d.ok.dbl.rat) (by exact hrat)
  have hop := hS.1
  have rhoS : ∀ w, ∀ φ ∈ schA F d.κ, S0 (d.dd.rho d.B.ψ w φ) = dd0.rho d.B.ψ w (S0 φ) := by
    intro w φ hφ
    simp only [Darboux.rho]
    rw [hop.Heisenberg₂ _ _ hφ]
    simp
  have rhoS' : ∀ w, ∀ φ ∈ schA F (Fin d.m × Fin d.n × Fin 2), S0' (dd0.rho d.B.ψ w φ) = d.dd.rho d.B.ψ w (S0' φ) := by
    intro w φ hφ
    have h1 := rhoS w (S0' φ) (hop.pres' φ hφ)
    rw [hop.right φ hφ] at h1
    have hm : d.dd.rho d.B.ψ w (S0' φ) ∈ schA F d.κ :=
      GlobalTheory.EvZeroUniq.schr_mem_schA d.B.ψ hψ _ (hop.pres' φ hφ)
    rw [← h1, hop.left _ hm]
  set l' : ((Fin d.m × Fin d.n × Fin 2 → AF F) → ℂ) →ₗ[ℂ] ℂ := d.l ∘ₗ S0' with hl'
  have hadm : l' ∈ (adeleClass F).adm (Fin d.m × Fin d.n × Fin 2) := hop.adm' d.l d.ok.dbl.adm
  have hsurj : ∀ y : Fin d.m × Fin d.n × Fin 2 → AF F, ∃ Z : Mx F E d.m d.n,
      dd0.e (Z * (incM F d.b.1.toCols₁)ᵀ) = (0, y) := by
    intro y
    obtain ⟨Z, X, hw⟩ := eq_split d.b (dd0.e.symm (0, y))
    have h1 := had Z X
    rw [← hw, LinearEquiv.apply_symm_apply] at h1
    have h2 := had Z 0
    rw [Matrix.zero_mul, add_zero, crdB_zero] at h2
    refine ⟨Z, h2.trans ?_⟩
    have h3 := congrArg Prod.snd h1
    simp only at h3
    rw [← h3]
  obtain ⟨t, ht0⟩ := d.ok.frame.2
  have ht : (d.b.1.toCols₁ : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) =
      (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * (t.1 : Matrix (Fin d.n) (Fin d.n) E) := ht0
  have hinv : ∀ (y : Fin d.m × Fin d.n × Fin 2 → AF F), ∀ φ ∈ schA F (Fin d.m × Fin d.n × Fin 2),
      l' (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = l' φ := by
    intro y φ hφ
    obtain ⟨Z, hZ⟩ := hsurj y
    have e1 : (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = dd0.rho d.B.ψ (Z * (incM F d.b.1.toCols₁)ᵀ) φ := by
      funext x
      simp [Darboux.rho, hZ, schr]
    rw [e1, hl', LinearMap.comp_apply, rhoS' _ φ hφ, LinearMap.comp_apply]
    have e2 : Z * (incM F d.b.1.toCols₁)ᵀ = ((Z * (incM F t.1)ᵀ : Mx F E d.m d.n)) *
        ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)))ᵀ := by
      rw [ht, incM_mul', incM_diagCols, Matrix.transpose_mul]
      exact (Matrix.mul_assoc _ _ _).symm
    rw [e2]
    exact d.ok.dbl.kill _ _ (hop.pres' φ hφ)
  obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F d.B.ψ hψ (Fin d.m × Fin d.n × Fin 2) l' hadm hinv
  have hform : ∀ Φ ∈ d.sch, ∀ X, d.T Φ X = c * S0 Φ (crdB d.bs X) := by
    intro Φ hΦ X
    have hΨ : d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ ∈ schA F d.κ :=
      GlobalTheory.EvZeroUniq.schr_mem_schA d.B.ψ hψ _ hΦ
    have h0 := had 0 X
    rw [Matrix.zero_mul, zero_add] at h0
    simp only [Bf_zero_left] at h0
    have e1 : d.T Φ X = l' (S0 (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ)) := by
      rw [hl', LinearMap.comp_apply, hop.left _ hΨ]
      rfl
    rw [e1, hc _ (hop.pres _ hΨ), rhoS _ _ hΦ]
    simp [Darboux.rho, h0, schr]
  refine ⟨S0, S0', c, ?_, hS, hform⟩
  rintro rfl
  obtain ⟨φ, hφ, hφ0⟩ := GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F d.κ
  have hz : d.T φ = 0 := by
    funext X
    rw [hform φ hφ X, zero_mul]
    rfl
  exact hφ0 (by rw [(hT.1 F E σ d).2.2 φ hφ hz]; rfl)
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem modelEx_wired_k (hD : _root_.PositivityTheory.SiegelWeilFormula.Ald.SDarb_k) (hP : PartCharInv) (hC : _root_.PositivityTheory.SiegelWeilFormula.Ald.ChartFacts_k) (hG : _root_.PositivityTheory.SiegelWeilFormula.Ald.SiegelSmall_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.Ald.SmallS_k) : _root_.PositivityTheory.SiegelWeilFormula.Ald.ModelEx_k :=
  _root_.PositivityTheory.SiegelWeilFormula.Ald.modelEx_of_k hD _root_.PositivityTheory.SiegelWeilFormula.Ldexa.sEv_k _root_.PositivityTheory.SiegelWeilFormula.Ald.bigT_k sliceFacts (opBox_of hP sliceFacts) (subSplit_of sliceFacts) hC hG hS
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ldexa
open PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {m n : ℕ}
theorem sDarb_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.SDarb_k := by
  intro F E _ _ _ _ _ σ B bs m n A Y b ε r s hB hm hn hsg hb hε
  haveI : FiniteDimensional F E := Module.Finite.of_basis bs
  have hσ : ∀ a, σ (σ a) = a := by
    obtain ⟨-, -, -, h⟩ := hB.cm
    intro a
    let τ : E →+* ℂ := Classical.arbitrary _
    apply τ.injective
    rw [h, h, star_star]
  obtain ⟨u, hsym, hεu, hJ⟩ : ∃ u : ℤ, (∀ i j, σ (A.J j i) = (u : E) * A.J i j) ∧ (ε : ℤ) * u = -1 ∧ A.J.det ≠ 0 := by
    rcases hsg with ⟨hA, hY⟩ | ⟨hA, hY⟩
    · refine ⟨1, fun i j => by simp [hA.herm], ?_, GlobalTheory.ThetaRatPair.det_ne_of_sig B A.J hA.sig⟩
      rw [eps_eq hσ Y.J (-1) (fun i j => by simp [hY]) b ε hε hn]
      norm_num
    · refine ⟨-1, fun i j => by simp [hA.skew], ?_, GlobalTheory.ThetaRatPair.det_ne_of_sig' B A.J hA.sig⟩
      rw [eps_eq hσ Y.J 1 (fun i j => by simp [hY]) b ε hε hn]
      norm_num
  have hP := Pm_unit (n := n) σ hσ A.J hJ bs
  let dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (Fin m × Fin n × Fin 2) :=
    ⟨eD σ A.J bs b hP, eD_form σ A.J bs Y.J b ε hε u (fun X Z => Bf_symm hσ A.J u hsym X Z) hεu hP⟩
  have hd : IsAdapted bs A Y b dd := fun Z X => eD_frame σ A.J bs b hP Z X
  refine ⟨dd, hd, fun x => ?_⟩
  obtain ⟨c, hc⟩ := e_rat bs A Y b dd hd x
  exact ⟨_, c, hc⟩
end PositivityTheory.SiegelWeilFormula.Ldexa
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem chartFacts_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.ChartFacts_k := by
  intro F E _ _ _ _ _ σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' h0 h'
  have rdE : ∀ w, (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e w = ((dd0.e w).1 ∘ eK d.m h, (dd0.e w).2 ∘ eK d.m h) :=
    fun w => by rw [GlobalTheory.TowU.reindexD_e, Equiv.symm_symm]
  have hfr : ∀ g, inFrame d.b (j g) = blk h (inFrame b g) 1 := fun g => eq_blk h _ _ (hj.2.1 g) (hj.2.2 g)
  refine ⟨fun w' => ?_, fun u v => ⟨_, LinearEquiv.apply_symm_apply _ _⟩, fun g w H1 H2 => ?_, fun g w' => ?_,
    fun u w' => ?_⟩
  ·
    rw [rdE, adapted_e h0, frQ_emb, embQ_toCols₁, embQ_toCols₂, adapted_e h']
    refine Prod.ext (funext fun q => ?_) (funext fun q => ?_)
    · rcases q with ⟨a, c, t⟩ | ⟨a, t⟩
      · exact crdB_col _ _ _ a _ c t (extend_zero_embedded_column h _ a c)
      · exact crdB_zero_col _ _ a _ t (extend_zero_last_column h _ a)
    · rcases q with ⟨a, c, t⟩ | ⟨a, t⟩
      · exact Bf_col _ _ _ _ a _ c t (fun p => extend_zero_embedded_column h _ p c)
      · exact Bf_zero_col _ _ _ a _ t (fun p => extend_zero_last_column h _ p)
  ·
    set Q := frQ d.b w with hQdef
    set Q' := Q.submatrix id (Sum.map (em0 h) (em0 h)) with hQ'def
    have hw := adapted_e h0 w
    have hz : dd0.e (embQ h Q' * (incM F d.b.1)ᵀ) = 0 := by
      rw [adapted_e h0, frQ_of, embQ_toCols₁, embQ_toCols₂]
      refine Prod.ext (funext fun q => ?_) (funext fun q => ?_)
      · obtain ⟨a, c, t⟩ := q
        by_cases hc : c = i0 h
        · subst hc
          exact crdB_zero_col _ _ a _ t (extend_zero_last_column h _ a)
        · obtain ⟨c', rfl⟩ := (ne_last_iff_mem_range h c).1 hc
          have e3 := congrFun H1 (a, c', t)
          rw [rdE, hw] at e3
          refine (crdB_col _ _ _ a _ _ t ?_).trans e3
          rw [extend_zero_embedded_column]
          rfl
      · obtain ⟨a, c, t⟩ := q
        by_cases hc : c = i0 h
        · subst hc
          exact Bf_zero_col _ _ _ a _ t (fun p => extend_zero_last_column h _ p)
        · obtain ⟨c', rfl⟩ := (ne_last_iff_mem_range h c).1 hc
          have e3 := congrFun H2 (a, c', t)
          rw [rdE, hw] at e3
          refine (Bf_col _ _ _ _ a _ _ t fun p => ?_).trans e3
          rw [extend_zero_embedded_column]
          rfl
    have hQ' : embQ h Q' = 0 := by
      have := (LinearEquiv.map_eq_zero_iff dd0.e).1 hz
      rw [← frQ_of d.b (embQ h Q'), this, frQ, Matrix.zero_mul]
    have hQv : ∀ a v', Q a (Sum.map (em0 h) (em0 h) v') = 0 := fun a v' => by
      have := congrFun (congrFun hQ' a) (Sum.map (em0 h) (em0 h) v')
      rwa [embQ_map_apply] at this
    apply frQ_injective d.b
    show frQ d.b (w * ((j g).1.1)ᵀ) = frQ d.b w
    rw [frQ_mul_mat, hfr, ← hQdef]
    ext a u
    rw [Matrix.mul_apply]
    have hterm : ∀ v, Q a v * (blk h (inFrame b g) 1)ᵀ v u = Q a v * (1 : Matrix (Fin d.n ⊕ Fin d.n) _ (AE F E)) u v := by
      intro v
      rcases idx_cases h v with ⟨v', rfl⟩ | hv | hv
      · rw [hQv, zero_mul, zero_mul]
      · rw [Matrix.transpose_apply, (blk_out h _ v (by rw [hv]; exact Or.inl rfl) u).2]
      · rw [Matrix.transpose_apply, (blk_out h _ v (by rw [hv]; exact Or.inr rfl) u).2]
    rw [Finset.sum_congr rfl fun v _ => hterm v]
    simp [Matrix.one_apply]
  ·
    apply frQ_injective d.b
    show frQ d.b (emb h b d.b w' * ((j g).1.1)ᵀ) = frQ d.b (emb h b d.b (w' * (g.1.1)ᵀ))
    rw [frQ_mul_mat, frQ_emb, frQ_emb, frQ_mul_mat, hfr, embQ_mul_blk]
  ·
    rw [emb_eq, emb_eq, frQ_left, ← embQ_mul_left, Matrix.mul_assoc]
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem modelExists_of_smallness (hG : _root_.PositivityTheory.SiegelWeilFormula.Ald.SiegelSmall_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.Ald.SmallS_k) : _root_.PositivityTheory.SiegelWeilFormula.Ald.ModelEx_k :=
  _root_.PositivityTheory.SiegelWeilFormula.Ald.modelEx_wired_k _root_.PositivityTheory.SiegelWeilFormula.Ldexa.sDarb_k partCharInv _root_.PositivityTheory.SiegelWeilFormula.Ald.chartFacts_k hG hS
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F : Type} [Field F] [NumberField F]
theorem smallS_of_k (hC : _root_.PositivityTheory.SiegelWeilFormula.Ald.ChartFacts_k) (hF : SliceFacts) (hU : SubSplit) (hH : HaarLc) : _root_.PositivityTheory.SiegelWeilFormula.Ald.SmallS_k := by
  intro hT F E _ _ _ _ _ σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had' S1 S1' C hC0 hop hTf
  have hψ : IsStd d.B.ψ := d.ok.good.std
  have hcm : IsCMExt F E σ := d.ok.good.cm
  have hJ : d.A.J.det ≠ 0 := by
    rcases d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩
    · exact (GlobalTheory.T.isUnit_det_gram_of_hermitianSelfDualLatticeSpace F E σ d.B d.m d.A d.r d.s hA).ne_zero
    · exact (GlobalTheory.T.isUnit_det_gram_skewHermitian_signature F E σ d.B d.m d.A d.r d.s hA).ne_zero
  obtain ⟨hc1, -, -, -, hc5⟩ := hC F E σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had'
  have hlin := d.ok.dbl.lin
  have pres1 : ∀ u : UA σ d.A.J, ∀ φ ∈ schA F (K1 d.m n), (S1 ∘ₗ d.S u ∘ₗ S1') φ ∈ schA F (K1 d.m n) :=
    fun u φ hφ => hop.pres _ (hlin.pres u _ (hop.pres' φ hφ))
  have one1 : ∀ φ ∈ schA F (K1 d.m n), (S1 ∘ₗ d.S 1 ∘ₗ S1') φ = φ := fun φ hφ => by
    simp only [LinearMap.coe_comp, Function.comp_apply, map_one, Module.End.one_apply]
    exact hop.right φ hφ
  have mul1 : ∀ u v : UA σ d.A.J, ∀ φ ∈ schA F (K1 d.m n),
      (S1 ∘ₗ d.S (u * v) ∘ₗ S1') φ = (S1 ∘ₗ d.S u ∘ₗ S1') ((S1 ∘ₗ d.S v ∘ₗ S1') φ) := fun u v φ hφ => by
    simp only [LinearMap.coe_comp, Function.comp_apply, map_mul, Module.End.mul_apply]
    rw [hop.left _ (hlin.pres v _ (hop.pres' φ hφ))]
  obtain ⟨SA1, hSA1⟩ := projHom (fun u => S1 ∘ₗ d.S u ∘ₗ S1') pres1 one1 mul1
  have hsplit : IsUSplitting (adeleClass F) d.B.ψ (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm)
      (fun (g : UA σ d.A.J) (x : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) => mat g * x) SA1 :=
    GlobalTheory.TowU.isUSplitting_of_isOp hψ (fun w => by simp) hop hSA1 hlin
  have hexp : ∀ u : UA σ d.A.J, ∀ Ψ ∈ schA F (K1 d.m n), ∀ x : K1 d.m n → AF F,
      SA1 u Ψ x = Ψ (Sum.elim (Lk d.bs (mat u⁻¹) (x ∘ Sum.inl)) (Lc d.bs (mat u⁻¹) (x ∘ Sum.inr))) := by
    intro u Ψ hΨ x
    set X : Mx F E d.m d.n := cmbB d.bs (x ∘ (eK d.m h).symm) with hX
    have hx : crdB d.bs X ∘ eK d.m h = x := by
      rw [hX, crdB_cmbB]; funext k; simp
    have hΦ : S1' Ψ ∈ d.sch := hop.pres' Ψ hΨ
    have hTP := (hT.2.1 F E σ d (S1' Ψ) hΦ).2.2 u X
    rw [hTf _ (hlin.pres u _ hΦ), hTf _ hΦ, hop.right Ψ hΨ] at hTP
    have key := mul_left_cancel₀ hC0 hTP
    calc SA1 u Ψ x = S1 (d.S u (S1' Ψ)) x := by rw [hSA1 u Ψ hΨ]; rfl
      _ = S1 (d.S u (S1' Ψ)) (crdB d.bs X ∘ eK d.m h) := by rw [hx]
      _ = Ψ (crdB d.bs (mat u⁻¹ * X) ∘ eK d.m h) := key
      _ = _ := by rw [← Lk_crdB, hX, crdB_cmbB, Lk_eK]
  have hbox : ∀ u : UA σ d.A.J, ∀ φ' ∈ schA F (Fin d.m × Fin n × Fin 2), ∀ φ'' ∈ schA F (Fin d.m × Fin 2),
      SA1 u (boxFun φ' φ'') = boxFun (φ' ∘ Lk d.bs (mat u⁻¹)) (φ'' ∘ Lc d.bs (mat u⁻¹)) := by
    intro u φ' h' φ'' h''
    funext x
    rw [hexp u _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ' h' φ'' h'')]
    rfl
  obtain ⟨φ₀, hφ₀, hφ₀1, hφ₀n⟩ := (hF F (Fin d.m × Fin n × Fin 2) (Fin d.m × Fin 2)).2.2.1
  obtain ⟨φa, hφa, hφa1, -⟩ := (hF F (Fin d.m × Fin 2) (Fin d.m × Fin n × Fin 2)).2.2.1
  let c : UA σ d.A.J → ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ) →ₗ[ℂ] ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ) :=
    fun u => LinearMap.funLeft ℂ ℂ (Lk d.bs (mat u⁻¹))
  have hc : ∀ u φ, c u φ = φ ∘ Lk d.bs (mat u⁻¹) := fun _ _ => rfl
  have presS : ∀ u, ∀ φ ∈ schA F (Fin d.m × Fin n × Fin 2), c u φ ∈ schA F (Fin d.m × Fin n × Fin 2) := by
    intro u φ hφ
    have := (hF F (Fin d.m × Fin n × Fin 2) (Fin d.m × Fin 2)).1 _
      (hsplit.pres u _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ hφ φ₀ hφ₀))
    rw [hbox u φ hφ φ₀ hφ₀, slice0_box, Function.comp_apply, Lc_zero, hφ₀1, one_smul] at this
    exact this
  have oneS : ∀ φ ∈ schA F (Fin d.m × Fin n × Fin 2), c 1 φ = φ := by
    intro φ _
    have hm : mat (1 : UA σ d.A.J)⁻¹ = 1 := by rw [inv_one]; rfl
    rw [hc, hm]
    funext x
    simp only [Function.comp_apply, Lk_one]
  have mulS : ∀ u v, ∀ φ ∈ schA F (Fin d.m × Fin n × Fin 2), c (u * v) φ = c u (c v φ) := by
    intro u v φ _
    rw [hc, hc, hc, mul_inv_rev, show mat (v⁻¹ * u⁻¹) = mat v⁻¹ * mat u⁻¹ from rfl]
    funext x
    simp only [Function.comp_apply, Lk_mul]
  obtain ⟨S', hS'⟩ := projHom c presS oneS mulS
  have hφ₁ : ∀ g : UA σ d.A.J, φ₀ ∘ Lc d.bs (mat g⁻¹) ∈ schA F (Fin d.m × Fin 2) := by
    intro g
    have := sliceL_mem hF (hsplit.pres g _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φa hφa φ₀ hφ₀))
    rw [hbox g φa hφa φ₀ hφ₀] at this
    convert this using 1
    funext x''
    simp only [boxFun, Function.comp_apply, Sum.elim_comp_inl, Sum.elim_comp_inr, Lk_zero, hφa1, one_mul]
  have hsplitS : IsUSplitting (adeleClass F) d.B.ψ dd' (fun (g : UA σ d.A.J) x => mat g * x) S' :=
    hU F d.B.ψ hψ (Fin d.m × Fin n × Fin 2) (Fin d.m × Fin 2) (Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E))
      (Matrix (Fin d.m) (Fin n ⊕ Fin n) (AE F E)) _ _ (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm) dd' (emb h b d.b) hc1
      (UA σ d.A.J) (UA σ d.A.J) (fun g x => mat g * x) (fun g x => mat g * x) (MonoidHom.id _) continuous_id
      (fun g w' => hc5 g w') SA1 S' hsplit φ₀ hφ₀ hφ₀1 hφ₀n (fun g => ⟨φ₀ ∘ Lc d.bs (mat g⁻¹), hφ₁ g,
        by rw [Function.comp_apply, Lc_zero, hφ₀1],
        fun μ'' hμ'' => hH F E σ hcm d.m d.A.J hJ d.bs g⁻¹ μ'' hμ'' (fun x => ‖φ₀ x‖ₑ ^ 2),
        fun φ' hφ' => by
          show SA1 g (boxFun φ' φ₀) = _
          rw [hbox g φ' hφ' φ₀ hφ₀, hS' g φ' hφ', hc]⟩)
  refine ⟨S', hsplitS, fun g Φ hΦ => ?_⟩
  show S' g Φ 0 = Φ 0
  rw [hS' g Φ hΦ, hc, Function.comp_apply, Lk_zero]
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem smallS_of'_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.ChartFacts_k → SliceFacts → _root_.PositivityTheory.SiegelWeilFormula.Ald.SmallS_k := fun hC hF => _root_.PositivityTheory.SiegelWeilFormula.Ald.smallS_of_k hC hF (subSplit_of hF) haarLc
end PositivityTheory.SiegelWeilFormula.Ald
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem modelExists_of_siegelSmall (hG : _root_.PositivityTheory.SiegelWeilFormula.Ald.SiegelSmall_k) : _root_.PositivityTheory.SiegelWeilFormula.Ald.ModelEx_k := _root_.PositivityTheory.SiegelWeilFormula.Ald.modelExists_of_smallness hG (_root_.PositivityTheory.SiegelWeilFormula.Ald.smallS_of'_k _root_.PositivityTheory.SiegelWeilFormula.Ald.chartFacts_k sliceFacts)
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
set_option linter.unusedSimpArgs false
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem jPar_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b)
    {j : G2 σ Y →* d.G} (hj : _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j) (p : G2 σ Y) (t : GL (Fin n) (AE F E))
    (hpt : p.1.1 * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) =
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * t.1) :
    ∃ t' : GL (Fin d.n) (AE F E), (j p).1.1 * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) =
      (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) * t'.1 ∧
      Matrix.GeneralLinearGroup.det t' = Matrix.GeneralLinearGroup.det t := by
  obtain ⟨tb, hTb⟩ := frame_fromRows hb
  obtain ⟨td, hTd⟩ := frame_fromRows d.ok.frame
  set P := inFrame b p with hPdef
  set R0 := Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (0 : Matrix (Fin n) (Fin n) (AE F E)) with hR0
  set R0N := Matrix.fromRows (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) with hR0N
  set A : Matrix (Fin n) (Fin n) (AE F E) := incM F (tb⁻¹).1 * t.1 * incM F tb.1 with hA
  have hDn := diag_of_frame b tb hTb
  have hDN := diag_of_frame d.b td hTd
  have hp := mat_of_inFrame b p
  have hP : P * R0 = R0 * A := by
    have e := hpt
    rw [hp, hDn] at e
    have e2 : incM F b.1 * (P * R0) * incM F (tb⁻¹).1 = incM F b.1 * (R0 * A) * incM F (tb⁻¹).1 := by
      rw [hA]
      calc incM F b.1 * (P * R0) * incM F (tb⁻¹).1
          = incM F b.1 * P * incM F (b⁻¹).1 * (incM F b.1 * R0 * incM F (tb⁻¹).1) := by
            simp only [Matrix.mul_assoc, cancel_l, incM_mul_inv, incM_inv_mul, Matrix.mul_one]
        _ = incM F b.1 * R0 * incM F (tb⁻¹).1 * t.1 := e
        _ = incM F b.1 * (R0 * (incM F (tb⁻¹).1 * t.1 * incM F tb.1)) * incM F (tb⁻¹).1 := by
            simp only [Matrix.mul_assoc, cancel_l', incM_mul_inv, incM_inv_mul, Matrix.mul_one]
    have e3 := congrArg (fun X => incM F (b⁻¹).1 * X * incM F tb.1) e2
    simpa only [Matrix.mul_assoc, cancel_l, cancel_l', incM_mul_inv, incM_inv_mul, Matrix.mul_one] using e3
  have hblk := blk_fromRows h P A hP
  have hjp : inFrame d.b (j p) = blk h P 1 := eq_blk h _ _ (hj.2.1 p) (hj.2.2 p)
  have hjm := mat_of_inFrame d.b (j p)
  rw [hjp] at hjm
  set blkA := (Matrix.fromBlocks A 0 0 1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) (AE F E)).submatrix (eI h) (eI h)
    with hblkA
  set T : Matrix (Fin d.n) (Fin d.n) (AE F E) := incM F td.1 * blkA * incM F (td⁻¹).1 with hT
  have hdet : T.det = t.1.det := by
    rw [hT, det_conj, hblkA, det_blkA, hA, det_conj']
  have hu : IsUnit T.det := by
    rw [hdet, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.isUnit _
  refine ⟨Matrix.nonsingInvUnit T hu, ?_, ?_⟩
  · show (j p).1.1 * _ = _ * T
    rw [hjm, hDN]
    calc incM F d.b.1 * blk h P 1 * incM F (d.b⁻¹).1 * (incM F d.b.1 * R0N * incM F (td⁻¹).1)
        = incM F d.b.1 * (blk h P 1 * R0N) * incM F (td⁻¹).1 := by simp only [Matrix.mul_assoc, cancel_l, incM_mul_inv, incM_inv_mul, Matrix.mul_one]
      _ = incM F d.b.1 * (R0N * blkA) * incM F (td⁻¹).1 := by rw [hblk]
      _ = incM F d.b.1 * R0N * incM F (td⁻¹).1 * T := by
          rw [hT]; simp only [Matrix.mul_assoc, cancel_l, incM_mul_inv, incM_inv_mul, Matrix.mul_one]
  · ext
    simp only [Matrix.GeneralLinearGroup.val_det_apply]
    exact hdet
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F : Type} [Field F] [NumberField F]
theorem siegelSmall_of_k (hF : SliceFacts) (hAC : AdaptedChar) : _root_.PositivityTheory.SiegelWeilFormula.Ald.SiegelSmall_k := by
  intro F E _ _ _ _ _ σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had' om1 hsp1 hsr1 φ₀ hφ₀ h0 om' hbox
  intro l hl hinv p t hpt φ hφ
  have hψ : IsStd d.B.ψ := d.ok.good.std
  have hchar : ∀ (y : Fin d.m × Fin n × Fin 2 → AF F), ∀ φ ∈ schA F (Fin d.m × Fin n × Fin 2),
      l (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = l φ := by
    intro y φ hφ
    obtain ⟨z, hz⟩ := (hAC F E σ d.m n d.bs d.A Y b dd' had' hb).2 y
    have := hinv z φ hφ
    rw [Darboux.rho, hz, schr_zero_fst] at this
    exact this
  obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F d.B.ψ hψ (Fin d.m × Fin n × Fin 2) l hl hchar
  have hbm : boxFun φ φ₀ ∈ schA F (K1 d.m n) := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ hφ φ₀ hφ₀
  have hb1 := hbox p φ hφ
  have hm1 : boxFun (om' p φ) φ₀ ∈ schA F (K1 d.m n) := hb1 ▸ hsp1.pres (j p) _ hbm
  have hmem : om' p φ ∈ schA F (Fin d.m × Fin n × Fin 2) := by
    have := (hF F _ _).1 _ hm1
    rwa [slice0_box_one _ h0] at this
  rw [hc _ hmem, hc _ hφ]
  have hv : om' p φ 0 = ev0 (K1 d.m n) (om1 (j p) (boxFun φ φ₀)) := by
    rw [hb1]
    simp [ev0, boxFun, h0]
  obtain ⟨t', ht', hdet⟩ := _root_.PositivityTheory.SiegelWeilFormula.Ald.jPar_k d h hb hj p t hpt
  have hkill : ∀ (z : Matrix (Fin d.m) (Fin d.n) (AE F E)), ∀ Ψ ∈ schA F (K1 d.m n),
      ev0 (K1 d.m n) ((GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).rho d.B.ψ
        (z * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))ᵀ) Ψ) = ev0 (K1 d.m n) Ψ := by
    intro z Ψ _
    have h1 := (hAC F E σ d.m d.n d.bs d.A d.Y d.b dd0 had0 d.ok.frame).1 z
    rw [Darboux.rho, GlobalTheory.TowU.reindexD_e, h1]
    simp [ev0, schr]
  have key := hsr1 (ev0 (K1 d.m n)) (evalZero_mem_adelicSchwartzAdmittedForms _) hkill (j p) t' ht' (boxFun φ φ₀) hbm
  rw [hv, key, hdet]
  simp [ev0, boxFun, h0]
  ring
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem siegelSmall_of_slice_k (hF : SliceFacts) : _root_.PositivityTheory.SiegelWeilFormula.Ald.SiegelSmall_k := _root_.PositivityTheory.SiegelWeilFormula.Ald.siegelSmall_of_k hF Ldx.adaptedChar
end PositivityTheory.SiegelWeilFormula.Ald
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem modelEx_k : _root_.PositivityTheory.SiegelWeilFormula.Ald.ModelEx_k := _root_.PositivityTheory.SiegelWeilFormula.Ald.modelExists_of_siegelSmall (_root_.PositivityTheory.SiegelWeilFormula.Ald.siegelSmall_of_slice_k sliceFacts)
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end
