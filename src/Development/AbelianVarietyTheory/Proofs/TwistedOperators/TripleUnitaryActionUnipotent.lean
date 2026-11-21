import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DarbouxModelAlgebraicVectorsLeAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryFactorFiniteSetOfPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetAdelicUnitaryPreservesLatticeAlmostA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoUnitaryGroupIdempotentLocalizationFiniteS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedPlacesVacuumFixedStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_adelicUnitary_preserves_lattice_almost_all : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n), X.L.IsLattice E → ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J,
    ∃ S₁ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ w ∉ S₁, ∀ z ∈ GlobalTheory.InertSph.latAt X w,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g *ᵥ z ∈ GlobalTheory.InertSph.latAt X w ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt X w := by
  first | exact @GlobalTheory.LatAlmostAll.exists_finset_keeps | exact GlobalTheory.LatAlmostAll.exists_finset_keeps | (intros; apply GlobalTheory.LatAlmostAll.exists_finset_keeps <;> assumption)
end

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

namespace GlobalTheory.PlaceProd

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {X : Spc F E n}

theorem mat_injOne (g : UA σ X.J) (h : mat g = 1) : g = 1 := Subtype.ext (Units.ext h)

theorem mat_mul' (g k : UA σ X.J) : mat (g * k) = mat g * mat k := rfl

theorem mat_one' : mat (1 : UA σ X.J) = 1 := rfl

theorem mat_inv_mul' (g : UA σ X.J) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul', inv_mul_cancel, mat_one']

theorem one_mem_UAt {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ X.J) ∈ UAt σ X ev := by
  intro u _
  rw [mat_one', sub_self, smul_zero]

end GlobalTheory.PlaceProd

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaceProd GlobalTheory.AdelicU in

theorem GlobalTheory.PlaceProd.pure_of_finSupp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) (gS : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J),
      (∀ u : AF F, (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w u = 0) → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS - 1) = 0) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ,
        (∀ v, φ' v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) ∧ (∀ v ∉ S, φ' v = φ v) ∧
        (∀ v, φ' v - φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om v) ∧
        om (gS, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ' := by
  classical
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP S
  have hstd := hP.good.std
  induction S using Finset.induction_on with
  | empty =>
    intro gS hgS f φ hSB _
    have h1 : mat gS = 1 := by
      have := hgS 1 (by simp)
      rwa [one_smul, sub_eq_zero] at this
    have hg : gS = 1 := mat_injOne gS h1
    refine ⟨φ, hSB, fun _ _ => rfl, fun v => by simp, ?_⟩
    subst hg
    rw [show ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 from rfl, map_one]
    rfl
  | @insert v S' hv ih =>
    intro gS hgS f φ hSB hvac
    obtain ⟨g1, k, hgk, h2, h3, -, -⟩ := GlobalTheory.T.exists_adelicUnitary_factor_finiteSetOfPlaces σ X gS {v}
    have hg1 : g1 ∈ UAt σ X (evFin F v) := fun u hu =>
      h2 u (fun w hw => by rw [Finset.mem_singleton.1 hw]; exact hu)
    have hk : ∀ u : AF F, (∀ w ∈ S', evFin F w u = 0) → u • (mat k - 1) = 0 := by
      intro u hu
      set e : AF F := GlobalTheory.LatVac.liftV v (1 : Fv F v) with he
      have hsplit : u = e * u + (1 - e) * u := by ring
      have ha : (e * u) • (mat k - 1) = 0 := by
        apply h3 v (Finset.mem_singleton_self v)
        rw [he, GlobalTheory.ThK.LocalOps.liftV_one_mul]
        intro u' hu'
        exact GlobalTheory.LatVac.at_liftV v _ u' hu'
      have hb : ((1 - e) * u) • (mat k - 1) = 0 := by
        set u' : AF F := (1 - e) * u with hu'def
        have hv' : evFin F v u' = 0 := by
          simp [hu'def, he, map_mul, map_sub, GlobalTheory.LatVac.evFin_liftV]
        have hS : u' • (mat gS - 1) = 0 := hgS u' (by
          intro w hw
          rcases Finset.mem_insert.1 hw with rfl | hw
          · exact hv'
          · simp [hu'def, map_mul, hu w hw])
        have hg1' : u' • (mat g1 - 1) = 0 := hg1 u' hv'
        have hkk : k = g1⁻¹ * gS := by rw [hgk, inv_mul_cancel_left]
        have hkdef : mat k - 1 = mat g1⁻¹ * (mat gS - 1) - mat g1⁻¹ * (mat g1 - 1) := by
          rw [hkk, mat_mul', Matrix.mul_sub, Matrix.mul_sub, mat_inv_mul', Matrix.mul_one]
          abel
        rw [hkdef, smul_sub, ← Matrix.mul_smul, ← Matrix.mul_smul, hS, hg1', Matrix.mul_zero, sub_self]
      rw [hsplit, add_smul, ha, hb, add_zero]
    obtain ⟨φ₁, hSB1, hoff1, haug1, hom1⟩ := ih k hk f φ hSB hvac
    obtain ⟨φ₂, hSB2, hact⟩ :=
      GlobalTheory.ThK.LocalOps.acts_exists hP v (g1, 1) hg1 (one_mem_UAt (evFin F v)) (φ₁ v) (hSB1 v)
    have hnot : ∀ᶠ w in Filter.cofinite, w ∉ S' :=
      Filter.eventually_cofinite.2 (S'.finite_toSet.subset fun x hx => by simpa using hx)
    have hstd1 : ∀ᶠ w in Filter.cofinite,
        φ₁ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
      filter_upwards [hvac, hstd, hnot] with w h1 h2 h3
      rw [hoff1 w h3, h1, h2]
    have hpure := GlobalTheory.TensUniq.pure_mem_schA f φ₁ hSB1 hstd1
    have hstep := GlobalTheory.ThK.LocalOps.acts_pure v (om (g1, 1)) f φ₁ φ₂ hpure
      (GlobalTheory.PureFactor.mulSupport_finite φ₁ hstd1) hact
    refine ⟨Function.update φ₁ v φ₂, ?_, ?_, ?_, ?_⟩
    · intro w
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]; exact hSB2
      · rw [Function.update_of_ne hw]; exact hSB1 w
    · intro w hw
      have hwv : w ≠ v := fun h => hw (h ▸ Finset.mem_insert_self _ _)
      have hwS : w ∉ S' := fun h => hw (Finset.mem_insert_of_mem h)
      rw [Function.update_of_ne hwv]; exact hoff1 w hwS
    · intro w
      by_cases hw : w = v
      · subst hw
        rw [Function.update_self, ← hoff1 w hv]
        exact Submodule.subset_span ⟨g1, hg1, φ₁ w, hSB1 w, φ₂, hSB2, hact, rfl⟩
      · rw [Function.update_of_ne hw]; exact haug1 w
    · rw [hgk, show ((g1 * k, 1) : UA σ X.J × UA σ W.J) = (g1, 1) * (k, 1) by simp, map_mul,
        Module.End.mul_apply, hom1, hstep]
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
theorem _root_.GlobalTheory.T.finiteSupport_unitaryPoint_replaces_pureTensorFactors : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) (gS : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J),
      (∀ u : AF F, (∀ w ∈ S, GlobalTheory.AdelicU.evFin F w u = 0) → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat gS - 1) = 0) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ,
        (∀ v, φ' v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) ∧ (∀ v ∉ S, φ' v = φ v) ∧
        (∀ v, φ' v - φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om v) ∧
        om (gS, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ' := by
  atlas_forward_decl GlobalTheory.PlaceProd.pure_of_finSupp
end

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

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp

namespace GlobalTheory.SphGlobX

theorem loc_mem_KAt' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}
    (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (K : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)
    (hK : ∀ z ∈ GlobalTheory.InertSph.latAt W v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat K *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat K⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    GlobalTheory.FinDecomp.loc (GlobalTheory.FinDecomp.idem F v) (GlobalTheory.FinDecomp.idem_mul_self v) K ∈ GlobalTheory.InertSph.KAt σ W v := by
  have hfix : ∀ z ∈ GlobalTheory.InertSph.latAt W v, GlobalTheory.FinDecomp.idem F v • z = z := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, -, y, -, rfl⟩ := hz
      rw [smul_smul, GlobalTheory.FinDecomp.idem_mul_of_at ha]
    | zero => simp
    | add z z' _ _ h h' => rw [smul_add, h, h']
    | neg z _ h => rw [smul_neg, h]
  have hphi : ∀ (M : Matrix (Fin d) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), ∀ z ∈ GlobalTheory.InertSph.latAt W v,
      GlobalTheory.FinDecomp.phi (GlobalTheory.FinDecomp.idem F v) M *ᵥ z = M *ᵥ z := by
    intro M z hz
    have h1 : (1 - GlobalTheory.FinDecomp.idem F v) • z = 0 := by rw [sub_smul, one_smul, hfix z hz, sub_self]
    rw [GlobalTheory.FinDecomp.phi, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h1, zero_add,
      ← Matrix.mulVec_smul, hfix z hz]
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · show u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.FinDecomp.loc _ _ K) - 1) = 0
    rw [GlobalTheory.FinDecomp.mat_loc, GlobalTheory.FinDecomp.phi_sub_one, smul_smul, GlobalTheory.FinDecomp.mul_idem_of_evFin hu, zero_smul]
  · rw [GlobalTheory.FinDecomp.mat_loc, GlobalTheory.FinDecomp.mat_loc_inv, hphi _ z hz, hphi _ z hz]
    exact hK z hz

open scoped Classical in

theorem ev_mem_adm' {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (GlobalTheory.WeilM.adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • (BoundedContinuousFunction.evalCLM ℂ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [LinearMap.proj_apply, GlobalTheory.WeilM.pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  rw [mul_comm]

theorem fixes_pure_left : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F),
    (∀ v ∉ S, ∀ k ∈ GlobalTheory.InertSph.KAt σ X v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (k, 1)) (M.vac v) (M.vac v)) →
    ∀ k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J,
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∉ S, ∀ z ∈ GlobalTheory.InertSph.latAt X w,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k *ᵥ z ∈ GlobalTheory.InertSph.latAt X w ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt X w) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w)) → (∀ w ∉ S, φ w = M.vac w) →
      om (k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  classical
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP S hAct k hinf hS hlat f φ hSB hφ
  have hM := hP.good
  have hw := hP.weil
  have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    filter_upwards [hM.std, S.finite_toSet.eventually_cofinite_notMem] with w hw hwS
    rw [hφ w hwS, hw]
  set Φ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ with hΦ
  have hloc : ∀ v, v ∉ S → ∀ h ∈ GlobalTheory.InertSph.KAt σ X v, om (h, 1) Φ = Φ := by
    intro v hv h hh
    obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
    have e1 : Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) (φ v) r := by rw [hΦ, hrt, Function.update_eq_self]
    have hRest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) (φ v) r :=
      ⟨hr, by rw [← e1]; exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
    have hA := hAct v hv h hh
    rw [← hφ v hv] at hA
    rw [e1, hA r hRest]
  have hcut : ∀ v, v ∉ S → loc (idem F v) (idem_mul_self v) k ∈ GlobalTheory.InertSph.KAt σ X v :=
    fun v hv => loc_mem_KAt' σ X v k (hlat v hv)
  have hcutS : ∀ v ∈ S, loc (idem F v) (idem_mul_self v) k = 1 := by
    intro v hv
    apply ua_ext
    rw [mat_loc, mat_one, ← sub_eq_zero, phi_sub_one]
    exact hS v hv _ fun u hu => by rw [smul_eq_mul, mul_idem_of_evFin hu]
  have hone : ∀ v, om (loc (idem F v) (idem_mul_self v) k, 1) Φ = Φ := by
    intro v
    by_cases hv : v ∈ S
    · rw [hcutS v hv]; show om 1 Φ = Φ; rw [map_one]; rfl
    · exact hloc v hv _ (hcut v hv)
  have hlist : ∀ l : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F),
      om ((l.map fun v => loc (idem F v) (idem_mul_self v) k).prod, 1) Φ = Φ := by
    intro l
    induction l with
    | nil => show om 1 Φ = Φ; rw [map_one]; rfl
    | cons v t ih =>
      rw [List.map_cons, List.prod_cons]
      have : (loc (idem F v) (idem_mul_self v) k * (t.map fun v => loc (idem F v) (idem_mul_self v) k).prod,
          (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)) =
          (loc (idem F v) (idem_mul_self v) k, 1) * ((t.map fun v => loc (idem F v) (idem_mul_self v) k).prod, 1) := by
        simp
      rw [this, map_mul, Module.End.mul_apply, ih, hone]
  have hT : ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), om (loc (idemS F T) (idemS_mul_self T) k, 1) Φ = Φ := by
    intro T
    have e : loc (idemS F T) (idemS_mul_self T) k = (T.toList.map fun v => loc (idem F v) (idem_mul_self v) k).prod := by
      apply ua_ext
      rw [mat_prod_loc k _ T.nodup_toList, Finset.toList_toFinset, mat_loc]
    rw [e]; exact hlist _
  have hcont := hw.2.2
  have hΦA : Φ ∈ (GlobalTheory.WeilM.adeleClass F).sp (Fin n × Fin d) := GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd
  funext x
  have hc := hcont _ (ev_mem_adm' x) Φ hΦA
  have ht : Filter.Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) =>
      (loc (idemS F T) (idemS_mul_self T) k, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J))) Filter.atTop (nhds (k, 1)) :=
    (GlobalTheory.T.tendsto_unitaryGroupIdempotentLocalization_finiteSets F E σ n X.J k hinf).prodMk_nhds tendsto_const_nhds
  have hlim : Filter.Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) =>
      (LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) (om (loc (idemS F T) (idemS_mul_self T) k, 1) Φ))
      Filter.atTop (nhds ((LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) (om (k, 1) Φ))) :=
    (hc.tendsto _).comp ht
  have hconst : (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) =>
      (LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) (om (loc (idemS F T) (idemS_mul_self T) k, 1) Φ)) =
      fun _ => Φ x := by
    funext T; rw [hT T]; rfl
  rw [hconst] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

end GlobalTheory.SphGlobX
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
theorem _root_.GlobalTheory.T.latticeStabilizers_fix_vacua_fixes_pureTensor_left : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F),
    (∀ v ∉ S, ∀ k ∈ GlobalTheory.InertSph.KAt σ X v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (k, 1)) (M.vac v) (M.vac v)) →
    ∀ k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J,
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∉ S, ∀ z ∈ GlobalTheory.InertSph.latAt X w,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k *ᵥ z ∈ GlobalTheory.InertSph.latAt X w ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt X w) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w)) → (∀ w ∉ S, φ w = M.vac w) →
      om (k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  atlas_forward_decl GlobalTheory.SphGlobX.fixes_pure_left
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.LocActV

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.WeilM

theorem finite_point_acts_placewise : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    (∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V.J,
      (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g - 1) = 0) →
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) →
        ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ,
          (∀ v, φ' v ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v)) ∧ (∀ᶠ v in Filter.cofinite, φ' v = G.M.vac v) ∧
          (∀ v, φ' v - φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om v) ∧
          om (g, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ') ∧
    ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.V'.J,
      (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat g - 1) = 0) →
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v) →
        ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ,
          (∀ v, φ' v ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v)) ∧ (∀ᶠ v in Filter.cofinite, φ' v = G.M'.vac v) ∧
          (∀ v, φ' v - φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om' v) ∧
          om' (g, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ' := by
  intro hPr F E _ _ _ _ _ σ B a a' G X om om' hT
  obtain ⟨S₀, hS₀⟩ := GlobalTheory.T.unramified_places_vacuum_fixed hPr F E σ B a a' G X om om' hT
  have key : ∀ {n : ℕ} (Y : Spc F E n) (M : Model σ Y G.W) (χX χW : Chr F E) (ω : Rep σ Y G.W) (r s r' s' : ℕ),
      GlobalTheory.ThK.IsPair B M χX χW ω r s r' s' →
      (∀ v ∉ S₀, ∀ k ∈ GlobalTheory.InertSph.KAt σ Y v, Acts (evFin F v) (ω (k, 1)) (M.vac v) (M.vac v)) →
      ∀ g : UA σ Y.J, (∀ u : AF F, At (evI F) u → u • (mat g - 1) = 0) →
      ∀ (f : SInf F (Fin n × Fin (a + a'))) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin (a + a') → Fv F v) → ℂ),
        (∀ v, φ v ∈ SB (Fin n × Fin (a + a') → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∃ φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin (a + a') → Fv F v) → ℂ,
          (∀ v, φ' v ∈ SB (Fin n × Fin (a + a') → Fv F v)) ∧ (∀ᶠ v in Filter.cofinite, φ' v = M.vac v) ∧
          (∀ v, φ' v - φ v ∈ augAt ω v) ∧ ω (g, 1) (pure f φ) = pure f φ' := by
    intro n Y M χX χW ω r s r' s' hP hsph g hg f φ hφ hvac
    classical
    obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.exists_finset_adelicUnitary_preserves_lattice_almost_all σ Y hP.herm.lat g
    have hfin := Filter.eventually_cofinite.1 hvac
    set S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) := S₀ ∪ S₁ ∪ hfin.toFinset with hSdef
    obtain ⟨gS, k, hgk, hgS, hkS, hkI, hkL⟩ := GlobalTheory.T.exists_adelicUnitary_factor_finiteSetOfPlaces σ Y g S
    obtain ⟨φ', hφ'SB, hφ'off, hφ'aug, hφ'eq⟩ := GlobalTheory.T.finiteSupport_unitaryPoint_replaces_pureTensorFactors σ B Y G.W M χX χW ω r s r' s' hP S gS hgS f φ hφ hvac
    have hk : ω (k, 1) (pure f φ) = pure f φ := by
      refine GlobalTheory.T.latticeStabilizers_fix_vacua_fixes_pureTensor_left σ B Y G.W M χX χW ω r s r' s' hP S (fun v hv => hsph v (fun h => hv (by simp [hSdef, h])))
        k (fun u hu => by rw [hkI u hu]; exact hg u hu) hkS (fun w hw z hz => ?_) f φ hφ (fun w hw => ?_)
      · have hw1 : w ∉ S₁ := fun h => hw (by simp [hSdef, h])
        rw [(hkL w hw z hz).1, (hkL w hw z hz).2]
        exact hS₁ w hw1 z hz
      · by_contra hne
        exact hw (by simp [hSdef, hne])
    refine ⟨φ', hφ'SB, ?_, hφ'aug, ?_⟩
    · filter_upwards [hvac, S.finite_toSet.compl_mem_cofinite] with v hv hvS
      rw [hφ'off v hvS, hv]
    · have e : ((g, 1) : UA σ Y.J × UA σ G.W.J) = (gS, 1) * (k, 1) := by
        rw [hgk, Prod.mk_mul_mk, one_mul]
      rw [e, map_mul, Module.End.mul_apply, hk, hφ'eq]
  exact ⟨fun g hg f φ hφ hvac => key G.V G.M _ _ om _ _ _ _ (GlobalTheory.ThK.Inhab.pairV hT) (fun v hv => (hS₀ v hv).1) g hg f φ hφ hvac,
    fun g hg f φ hφ hvac => key G.V' G.M' _ _ om' _ _ _ _ (GlobalTheory.ThK.Inhab.pairV' hT) (fun v hv => (hS₀ v hv).2) g hg f φ hφ hvac⟩

end GlobalTheory.LocActV
end
