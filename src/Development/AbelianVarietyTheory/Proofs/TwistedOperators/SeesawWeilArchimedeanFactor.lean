import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawFramesWeilEquivalenceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupWPairVWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalAtFinitePlaceUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsDoublingFrameStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaResidueStatement

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LocalDescent

theorem descend {A A' P : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A'] [AddCommGroup P]
    [Module ℂ P] (S : Submodule ℂ A) (S' : Submodule ℂ A') (p : A →ₗ[ℂ] P) (p' : A' →ₗ[ℂ] P)
    (hp : S.map p = ⊤) (hp' : S'.map p' = ⊤) (r : A → A → Prop) (r' : A' → A' → Prop)
    (hex : ∀ x ∈ S, ∃ y ∈ S, r x y) (hex' : ∀ x ∈ S', ∃ y ∈ S', r' x y)
    (hlin : ∀ x ∈ S, ∀ z ∈ S, ∀ y w, r x y → r z w → ∀ s t : ℂ, r (s • x + t • z) (s • y + t • w))
    (heq : ∀ x ∈ S, ∀ x' ∈ S', ∀ y ∈ S, ∀ y' ∈ S', r x y → r' x' y' → p x = p' x' → p y = p' y') :
    ∃ T : Module.End ℂ P, (∀ x ∈ S, ∀ y ∈ S, r x y → p y = T (p x)) ∧
      ∀ x ∈ S', ∀ y ∈ S', r' x y → p' y = T (p' x) := by
  have hwd : ∀ x ∈ S, ∀ z ∈ S, ∀ y ∈ S, ∀ w ∈ S, r x y → r z w → p x = p z → p y = p w := by
    intro x hx z hz y hy w hw h1 h2 h3
    obtain ⟨x', hx', e⟩ : p x ∈ S'.map p' := hp' ▸ Submodule.mem_top
    obtain ⟨y', hy', h'⟩ := hex' x' hx'
    rw [heq x hx x' hx' y hy y' hy' h1 h' e.symm, heq z hz x' hx' w hw y' hy' h2 h' (h3.symm.trans e.symm)]
  have hsec : ∀ ξ : P, ∃ x ∈ S, ∃ y ∈ S, p x = ξ ∧ r x y := by
    intro ξ
    obtain ⟨x, hx, e⟩ : ξ ∈ S.map p := hp ▸ Submodule.mem_top
    obtain ⟨y, hy, h⟩ := hex x hx
    exact ⟨x, hx, y, hy, e, h⟩
  choose f hf g hg hfp hfg using hsec
  have hcomb : ∀ (ξ η : P) (s t : ℂ), p (g (s • ξ + t • η)) = s • p (g ξ) + t • p (g η) := by
    intro ξ η s t
    have := hwd _ (hf (s • ξ + t • η)) _ (add_mem (S.smul_mem s (hf ξ)) (S.smul_mem t (hf η))) _ (hg _) _
      (add_mem (S.smul_mem s (hg ξ)) (S.smul_mem t (hg η))) (hfg _)
      (hlin _ (hf ξ) _ (hf η) _ _ (hfg ξ) (hfg η) s t) (by rw [hfp, map_add, map_smul, map_smul, hfp, hfp])
    rw [this, map_add, map_smul, map_smul]
  let T : Module.End ℂ P :=
    { toFun := fun ξ => p (g ξ)
      map_add' := fun ξ η => by simpa using hcomb ξ η 1 1
      map_smul' := fun s ξ => by simpa using hcomb ξ ξ s 0 }
  refine ⟨T, fun x hx y hy h => ?_, fun x hx y hy h => ?_⟩
  · exact hwd x hx _ (hf (p x)) y hy _ (hg _) h (hfg _) (hfp _).symm
  · exact (heq _ (hf (p' x)) x hx _ (hg _) y hy (hfg _) h (hfp _)).symm

theorem acts_comb {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hex : ∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → Fv F v),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) T φ φ₁)
    {φ ψ φ₁ ψ₁ : (κ → Fv F v) → ℂ} (hφ : φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) (hψ : ψ ∈ GlobalTheory.WeilM.SB (κ → Fv F v))
    (h₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) T φ φ₁)
    (h₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) T ψ ψ₁) (s t : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) T (s • φ + t • ψ) (s • φ₁ + t • ψ₁) := by
  have hs : s • φ + t • ψ ∈ GlobalTheory.WeilM.SB (κ → Fv F v) :=
    add_mem ((GlobalTheory.WeilM.SB _).smul_mem s hφ) ((GlobalTheory.WeilM.SB _).smul_mem t hψ)
  obtain ⟨χ, -, hχ⟩ := hex _ hs
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  have e : ∀ α β : (κ → Fv F v) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) (s • α + t • β) R =
      s • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) α R + t • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) β R := by
    intro α β
    funext x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have key : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) χ R =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) (s • φ₁ + t • ψ₁) R := by
    rw [← hχ R (hR _ hs), e, map_add, map_smul, map_smul, h₁ R (hR φ hφ), h₂ R (hR ψ hψ), e]
  have hχe : χ = s • φ₁ + t • ψ₁ := by
    funext y
    have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (fun i => GlobalTheory.LatVac.liftV v (y i)) := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    have hRz : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0 := by
      simpa using (hR φ hφ).1 0 _ hz
    have := congrFun key (fun i => GlobalTheory.LatVac.liftV v (y i))
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, GlobalTheory.LatVac.evFin_liftV, hRz] at this
    exact mul_right_cancel₀ hR0 this
  rw [← hχe]
  exact hχ

theorem exists_localOp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (a a' : ℕ)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ hv ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.W (GlobalTheory.AdelicU.evFin F v),
    ∃ T : Module.End ℂ (Rf.Pi v),
      (∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, hv)) φ φ₁ → Rf.p v φ₁ = T (Rf.p v φ)) ∧
      ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (1, hv)) φ φ₁ → Rf.p' v φ₁ = T (Rf.p' v φ) := by
  intro F E _ _ _ _ _ σ a a' Bs Γ Xc om om' R Rf hM v h hh
  have hex := GlobalTheory.T.weilRepresentationLocality_unitaryGroupW_pairVW F E σ Bs a a' Γ Xc om om' hM.triple v h hh
  have hex' := GlobalTheory.T.weilRepresentation_localAtFinitePlace_unitaryGroupW F E σ Bs a a' Γ Xc om om' hM.triple v h hh
  exact descend _ _ (Rf.p v) (Rf.p' v) (hM.fin.onto v) (hM.fin.onto' v)
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, h))) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (1, h)))
    hex hex' (fun x hx z hz y w h1 h2 s t => acts_comb v (om (1, h)) hex hx hz h1 h2 s t) (hM.fin.equiv v h hh)

end GlobalTheory.LocalDescent
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localOperator_thetaQuotient_finitePlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (a a' : ℕ)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ hv ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.W (GlobalTheory.AdelicU.evFin F v),
    ∃ T : Module.End ℂ (Rf.Pi v),
      (∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, hv)) φ φ₁ → Rf.p v φ₁ = T (Rf.p v φ)) ∧
      ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (1, hv)) φ φ₁ → Rf.p' v φ₁ = T (Rf.p' v φ) := by
  atlas_forward_decl GlobalTheory.LocalDescent.exists_localOp
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleAssembly.EqFin

theorem liftPure_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    (ψ : AddChar (AF F) ℂ) (hM : M.IsGood ψ) {P : Type} [AddCommGroup P] [Module ℂ P]
    (pr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    {N : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F → Type} [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (pv : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] N v) (s : ∀ v, N v)
    (hs : ∀ᶠ v in Filter.cofinite, pv v (M.vac v) = s v) (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ) (hφ : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _)
    (hφv : ∀ᶠ v in Filter.cofinite, φ v = M.vac v) :
    GlobalTheory.TripleAssembly.liftPure M pr pv s (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) =
      pr f ⊗ₜ GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ v)) := by
  have H := GlobalTheory.PureLift.exists_pureLift σ Y Z M ψ hM P pr N pv s hs
  unfold GlobalTheory.TripleAssembly.liftPure
  rw [dif_pos H]
  exact H.choose_spec f φ hφ hφv

theorem darbAlg_stable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w) (hM : M.IsGood ψ)
    {P : Type} [AddCommGroup P] [Module ℂ P] (pr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    {N : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F → Type} [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (pv : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] N v) (s : ∀ v, N v)
    (hs : ∀ᶠ v in Filter.cofinite, pv v (M.vac v) = s v)
    (O : Module.End ℂ ((Fin n × Fin d → AF F) → ℂ)) (T₀ : Module.End ℂ (GlobalTheory.SmallThetaModules.RTens s))
    (hgen : ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      ∃ φ₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ,
        (∀ v, φ₁ v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ₁ v = M.vac v) ∧
        O (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ₁ ∧
        GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ₁ v)) = T₀ (GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ v)))) :
    ∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg M ψ τ, O Ψ ∈ GlobalTheory.TripleAssembly.darbAlg M ψ τ ∧
      GlobalTheory.TripleAssembly.liftPure M pr pv s (O Ψ) = LinearMap.lTensor P T₀ (GlobalTheory.TripleAssembly.liftPure M pr pv s Ψ) := by
  intro Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hf, hφ, hφv, rfl⟩ := hx
    obtain ⟨φ₁, h1, h1v, hO, hT⟩ := hgen f φ hφ hφv
    refine ⟨?_, ?_⟩
    · rw [hO]; exact Submodule.subset_span ⟨f, φ₁, hf, h1, h1v, rfl⟩
    · rw [hO, liftPure_pure M ψ hM pr pv s hs f φ₁ h1 h1v, liftPure_pure M ψ hM pr pv s hs f φ hφ hφv,
        LinearMap.lTensor_tmul, hT]
  | zero => simp
  | add x y _ _ hx hy =>
    refine ⟨?_, ?_⟩
    · rw [map_add]; exact Submodule.add_mem _ hx.1 hy.1
    · simp only [map_add, hx.2, hy.2]
  | smul c x _ hx =>
    refine ⟨?_, ?_⟩
    · rw [map_smul]; exact Submodule.smul_mem _ c hx.1
    · simp only [map_smul, hx.2]

end GlobalTheory.TripleAssembly.EqFin

namespace GlobalTheory.TripleAssembly.EqFin

set_option maxHeartbeats 2000000 in

theorem mapA_mapB_equivariant_fin : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        (∀ g ∈ GfC X, ∀ Φ ∈ algF ψ θ true A B, GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (ωA (1, g) Φ) = GlobalTheory.TripleAssembly.opFin ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) g (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ)) ∧
          ∀ g ∈ GfC X, ∀ Φ ∈ algF ψ θ false A₁ B, GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf (ωB (1, g) Φ) = GlobalTheory.TripleAssembly.opFin ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) g (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ) := by
  intro hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨oA, -⟩ := GlobalTheory.T.algF_map_mapA_and_mapB_eq_top hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨⟨dA, rA⟩, ⟨dB, rB⟩⟩ :=
    GlobalTheory.T.seesaw_weil_zeta_residue hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h hTA hTB R Rf hM
  have gM : Γ.M.IsGood Bs.ψ := hM.triple.geo.hM
  have gM' : Γ.M'.IsGood Bs.ψ := hM.triple.geo.hM'
  have c1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW 1 = 1 := Subtype.ext ((congrArg _ (map_one (matHom W))).trans (map_one _))
  have c1' : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁ 1 = 1 := Subtype.ext ((congrArg _ (map_one (matHom W₁))).trans (map_one _))
  have hsA : ∀ᶠ v in Filter.cofinite, Rf.p v (Γ.M.vac v) = GlobalTheory.TripleAssembly.vacIm Γ Rf v :=
    Filter.Eventually.of_forall fun v => rfl
  have hsB : ∀ᶠ v in Filter.cofinite, Rf.p' v (Γ.M'.vac v) = GlobalTheory.TripleAssembly.vacIm Γ Rf v := by
    refine Filter.eventually_cofinite.2 ((Xc.T.finite_toSet).subset fun v hv => ?_)
    by_contra hn
    exact hv (hM.fin.sph v hn).1.symm
  have key : ∀ g ∈ GfC X, ∃ T : Module.End ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf),
      (∀ Φ ∈ algF ψ θ true A B, GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (ωA (1, g) Φ) =
        T (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ)) ∧
      ∀ Φ ∈ algF ψ θ false A₁ B, GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf (ωB (1, g) Φ) =
        T (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ) := by
    intro g hg
    obtain ⟨hv, hvU, fA, fB⟩ := GlobalTheory.T.matched_maps_doubling_frame hP D W W₁ X e Bs Γ Xc om om' R Rf hM h.JX g hg
    choose a ha using fun v => GlobalTheory.T.exists_localOperator_thetaQuotient_finitePlace D.sp.cm.sig W.rank W₁.rank Bs Γ Xc om om' R Rf hM v (hv v) (hvU v)
    obtain ⟨T₀, hT₀⟩ := GlobalTheory.TripleAssembly.exists_rtensOp (GlobalTheory.TripleAssembly.vacIm Γ Rf) a
    refine ⟨LinearMap.lTensor R.Pi T₀, ?_, ?_⟩
    · have st := GlobalTheory.TripleAssembly.EqFin.darbAlg_stable Γ.M Bs.ψ Bs.emb gM R.p Rf.p (GlobalTheory.TripleAssembly.vacIm Γ Rf) hsA
        (om (1, GlobalTheory.TripleRead.toUX X e h.JX g)) T₀ (fun f φ hφ hφv => by
          obtain ⟨φ₁, h1, h1v, hAct, hO⟩ := fA f φ hφ hφv
          refine ⟨φ₁, h1, h1v, hO, ?_⟩
          rw [hT₀ _ (Filter.eventually_cofinite.1 ((hφv.and hsA).mono fun v hv' => by rw [hv'.1, hv'.2]))]
          congr 1
          funext v
          exact (ha v).1 (φ v) (hφ v) (φ₁ v) (h1 v) (hAct v))
      intro Φ hΦ
      obtain ⟨Ψ, hΨ, rfl⟩ := rA Φ hΦ
      have hs := GlobalTheory.TripleAssembly.darbAlg_le_schA D.sp.cm.sig Γ.V Γ.W Γ.M Bs.ψ Bs.emb gM hΨ
      have e1 := hTA Ψ hs 1 g
      rw [c1] at e1
      have s1 := (st Ψ hΨ).1
      have s2 := (st Ψ hΨ).2
      have d1 := dA _ s1
      have d2 := dA Ψ hΨ
      have x1 := congrArg (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) e1.symm
      have x2 := congrArg (LinearMap.lTensor R.Pi T₀) d2.symm
      exact x1.trans (d1.trans (s2.trans x2))
    · have st := GlobalTheory.TripleAssembly.EqFin.darbAlg_stable Γ.M' Bs.ψ Bs.emb gM' R.p' Rf.p' (GlobalTheory.TripleAssembly.vacIm Γ Rf) hsB
        (om' (1, GlobalTheory.TripleRead.toUX X e h.JX g)) T₀ (fun f φ hφ hφv => by
          obtain ⟨φ₁, h1, h1v, hAct, hO⟩ := fB f φ hφ hφv
          refine ⟨φ₁, h1, h1v, hO, ?_⟩
          rw [hT₀ _ (Filter.eventually_cofinite.1 ((hφv.and hsB).mono fun v hv' => by rw [hv'.1, hv'.2]))]
          congr 1
          funext v
          exact (ha v).2 (φ v) (hφ v) (φ₁ v) (h1 v) (hAct v))
      intro Φ hΦ
      obtain ⟨Ψ, hΨ, rfl⟩ := rB Φ hΦ
      have hs := GlobalTheory.TripleAssembly.darbAlg_le_schA D.sp.cm.sig Γ.V' Γ.W Γ.M' Bs.ψ Bs.emb gM' hΨ
      have e1 := hTB Ψ hs 1 g
      rw [c1'] at e1
      exact (congrArg (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf) e1.symm).trans ((dB _ (st Ψ hΨ).1).trans
        (((st Ψ hΨ).2).trans (congrArg (LinearMap.lTensor R.Pi T₀) (dB Ψ hΨ).symm)))
  have opEq : ∀ g, ∀ T : Module.End ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf),
      (∀ Φ ∈ algF ψ θ true A B, GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (ωA (1, g) Φ) =
        T (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ)) →
      GlobalTheory.TripleAssembly.opFin ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) g = T := by
    intro g T hTg
    have H : ∃ T : Module.End ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf), ∀ Φ ∈ algF ψ θ true A B,
        GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (ωA (1, g) Φ) = T (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ) := ⟨T, hTg⟩
    unfold GlobalTheory.TripleAssembly.opFin
    rw [dif_pos H]
    apply LinearMap.ext
    intro y
    have hy : y ∈ (algF ψ θ true A B).map (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) := by rw [oA]; trivial
    obtain ⟨Φ, hΦ, rfl⟩ := hy
    rw [← H.choose_spec Φ hΦ, hTg Φ hΦ]
  refine ⟨fun g hg Φ hΦ => ?_, fun g hg Φ hΦ => ?_⟩
  · obtain ⟨T, h1, -⟩ := key g hg
    rw [opEq g T h1]
    exact h1 Φ hΦ
  · obtain ⟨T, h1, h2⟩ := key g hg
    rw [opEq g T h1]
    exact h2 Φ hΦ

end GlobalTheory.TripleAssembly.EqFin

end
end
