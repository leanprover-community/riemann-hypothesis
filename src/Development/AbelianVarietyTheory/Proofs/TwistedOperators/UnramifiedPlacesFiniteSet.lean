import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchFiniteSetVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedPlacesInvariantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedPlacesSphericalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryProdLocalPointsMulLatticeStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertSphericalStabilizerPreservesLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoUnitaryGroupIdempotentLocalizationFiniteS

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp
noncomputable section

namespace GlobalTheory.LatExtract

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Spc latAtV incM At)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def mulL {d : ℕ} (c : E) : (Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) →+ (Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) where
  toFun z := fun j => inclR (F := F) (AF F) c * z j
  map_zero' := by ext j; simp
  map_add' z z' := by ext j; simp [mul_add]

lemma mulL_apply {d : ℕ} (c : E) (z : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) (j : Fin d) :
    mulL (F := F) c z j = inclR (F := F) (AF F) c * z j := rfl

lemma mulL_int_mem {d : ℕ} (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (o : 𝓞 E)
    {z : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E}
    (hz : z ∈ GlobalTheory.InertSph.latAt W v) : mulL (F := F) (o : E) z ∈ GlobalTheory.InertSph.latAt W v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hai, o • y, W.L.smul_mem o hy, ?_⟩
    ext j
    simp only [mulL_apply, Pi.smul_apply]
    rw [Algebra.smul_def (A := E) o (y j), map_mul, mul_smul_comm]
  | zero => simpa using (GlobalTheory.InertSph.latAt W v).zero_mem
  | add z z' _ _ h h' => rw [map_add]; exact (GlobalTheory.InertSph.latAt W v).add_mem h h'
  | neg z _ h => rw [map_neg]; exact (GlobalTheory.InertSph.latAt W v).neg_mem h

end GlobalTheory.LatExtract

namespace GlobalTheory.LatExtract

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Spc latAtV incM At)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rowL {n d : ℕ} (i₀ : Fin n) (c : E) :
    Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) →+ (Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) where
  toFun Γ := fun j => inclR (F := F) (AF F) c * Γ i₀ j
  map_zero' := by ext j; simp
  map_add' z z' := by ext j; simp [mul_add]

lemma rowL_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (i₀ : Fin n) (c : E)
    (hc : ∀ x ∈ X.L, ∃ o : 𝓞 E, (o : E) = c * x i₀)
    {Γ : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)} (hΓ : Γ ∈ latAtV X W v) :
    rowL (F := F) i₀ c Γ ∈ GlobalTheory.InertSph.latAt W v := by
  induction hΓ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, x, hx, y, hy, rfl⟩ := hz
    obtain ⟨o, ho⟩ := hc x hx
    refine AddSubgroup.subset_closure ⟨a, ha, hai, o • y, W.L.smul_mem o hy, ?_⟩
    ext j
    show inclR (F := F) (AF F) c * (a • incM F (Matrix.vecMulVec x y)) i₀ j = _
    simp only [Matrix.smul_apply, Pi.smul_apply, incM, Matrix.map_apply, Matrix.vecMulVec_apply]
    rw [Algebra.smul_def (A := E) o (y j), mul_smul_comm, ← map_mul, ← mul_assoc]
    congr 2
    rw [← ho]
  | zero => simpa using (GlobalTheory.InertSph.latAt W v).zero_mem
  | add z z' _ _ h h' => rw [map_add]; exact (GlobalTheory.InertSph.latAt W v).add_mem h h'
  | neg z _ h => rw [map_neg]; exact (GlobalTheory.InertSph.latAt W v).neg_mem h

lemma rowL_vecMulVec {n d : ℕ} (i₀ : Fin n) (c : E) (x : Fin n → E) (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) :
    rowL (F := F) i₀ c (Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q) = mulL (F := F) (c * x i₀) q := by
  ext j
  simp only [rowL, mulL, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.vecMulVec_apply, map_mul, mul_assoc]

end GlobalTheory.LatExtract

namespace GlobalTheory.LatExtract

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Spc latAtV incM At)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def coefSub {d : ℕ} (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) :
    Submodule (𝓞 E) E where
  carrier := {c | mulL (F := F) c q ∈ GlobalTheory.InertSph.latAt W v}
  zero_mem' := by
    change mulL (F := F) (0 : E) q ∈ GlobalTheory.InertSph.latAt W v
    have : mulL (F := F) (0 : E) q = 0 := by ext j; simp [mulL_apply]
    rw [this]; exact (GlobalTheory.InertSph.latAt W v).zero_mem
  add_mem' {a b} ha hb := by
    change mulL (F := F) (a + b) q ∈ GlobalTheory.InertSph.latAt W v
    have : mulL (F := F) (a + b) q = mulL (F := F) a q + mulL (F := F) b q := by
      ext j; simp [mulL_apply, add_mul]
    rw [this]; exact (GlobalTheory.InertSph.latAt W v).add_mem ha hb
  smul_mem' o c hc := by
    change mulL (F := F) (o • c) q ∈ GlobalTheory.InertSph.latAt W v
    have : mulL (F := F) (o • c) q = mulL (F := F) (o : E) (mulL (F := F) c q) := by
      ext j; simp only [mulL_apply, Algebra.smul_def, map_mul, mul_assoc]
    rw [this]; exact mulL_int_mem W v o hc

theorem extract (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) (hn : 0 < n) (hL : X.L.IsLattice E)
    (h : ∀ x ∈ X.L, Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (x i)) q ∈ latAtV X W v) :
    q ∈ GlobalTheory.InertSph.latAt W v := by
  set i₀ : Fin n := ⟨0, hn⟩
  let b₀ : Submodule (𝓞 E) E := X.L.map (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin n => E) i₀)
  have hfg : b₀.FG := hL.fg.map _
  let 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨b₀, FractionalIdeal.isFractional_of_fg hfg⟩
  have hmem : ∀ b, b ∈ 𝔟 ↔ ∃ x ∈ X.L, x i₀ = b := fun b => by
    rw [← FractionalIdeal.mem_coe]; exact Submodule.mem_map
  have hne : 𝔟 ≠ 0 := by
    intro h0
    have hle : Submodule.span E (X.L : Set (Fin n → E)) ≤ LinearMap.ker (LinearMap.proj (R := E) (φ := fun _ : Fin n => E) i₀) := by
      rw [Submodule.span_le]
      intro x hx
      have : x i₀ ∈ 𝔟 := (hmem _).2 ⟨x, hx, rfl⟩
      rw [h0, FractionalIdeal.mem_zero_iff] at this
      simpa using this
    rw [hL.span_eq_top] at hle
    have := hle (Submodule.mem_top (x := Pi.single i₀ (1 : E)))
    simp at this
  have hone : (1 : E) ∈ ((𝔟⁻¹ * 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) := by
    rw [inv_mul_cancel₀ hne, FractionalIdeal.mem_coe]; exact FractionalIdeal.one_mem_one _
  have hle : ((𝔟⁻¹ * 𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) ≤ coefSub W v q := by
    rw [FractionalIdeal.coe_mul, Submodule.mul_le]
    intro c hc b hb
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_inv_iff hne] at hc
    rw [FractionalIdeal.mem_coe, hmem] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    have hc' : ∀ x ∈ X.L, ∃ o : 𝓞 E, (o : E) = c * x i₀ := by
      intro x hx
      obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 (hc _ ((hmem _).2 ⟨x, hx, rfl⟩))
      exact ⟨o, ho⟩
    change mulL (F := F) (c * x i₀) q ∈ GlobalTheory.InertSph.latAt W v
    rw [← rowL_vecMulVec]
    exact rowL_mem X W v i₀ c hc' (h x hx)
  have h1 : mulL (F := F) (1 : E) q ∈ GlobalTheory.InertSph.latAt W v := hle hone
  have : mulL (F := F) (1 : E) q = q := by ext j; simp [mulL_apply]
  rwa [this] at h1

end GlobalTheory.LatExtract

theorem GlobalTheory.LatExtract.main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E), 0 < n → X.L.IsLattice E →
    (∀ x ∈ X.L, Matrix.vecMulVec (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (x i)) q ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W v) →
    q ∈ GlobalTheory.InertSph.latAt W v := fun F E _ _ _ _ _ n d X W v q hn hL h =>
  GlobalTheory.LatExtract.extract n d X W v q hn hL h
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_adelicLatticeAtPlace_of_tensor_with_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E), 0 < n → X.L.IsLattice E →
    (∀ x ∈ X.L, Matrix.vecMulVec (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (x i)) q ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W v) →
    q ∈ GlobalTheory.InertSph.latAt W v := by
  first | exact @GlobalTheory.LatExtract.main | exact GlobalTheory.LatExtract.main | (intros; apply GlobalTheory.LatExtract.main <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp

namespace GlobalTheory.SphGlob

theorem loc_mem_KAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (K : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J),
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat K *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat K⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    GlobalTheory.FinDecomp.loc (GlobalTheory.FinDecomp.idem F v) (GlobalTheory.FinDecomp.idem_mul_self v) K ∈ GlobalTheory.InertSph.KAt σ W v := by
  intro F E _ _ _ _ _ σ d W v K hK

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

end GlobalTheory.SphGlob

namespace GlobalTheory.SphGlob

open scoped Classical in

theorem ev_mem_adm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (GlobalTheory.WeilM.adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • (BoundedContinuousFunction.evalCLM ℂ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [LinearMap.proj_apply, GlobalTheory.WeilM.pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  rw [mul_comm]

end GlobalTheory.SphGlob

open GlobalTheory.SphGlob in

theorem GlobalTheory.SphGlob.fixes_pure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)),
    0 < n → X.L.IsLattice E → W.L.IsLattice E → M.IsGood ψ → M.IsWeil ψ χX χW om →
    (∀ v, v ∉ S → ∀ k ∈ GlobalTheory.InertSph.KAt σ W v,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, k)) (M.vac v) (M.vac v)) →
    ∀ k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J,
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w, w ∉ S → ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w)) → (∀ w, w ∉ S → φ w = M.vac w) →
      om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  classical
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om S hn hXL hWL hM hw hAct k hinf hS hlat f φ hSB hφ

  have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    filter_upwards [hM.std, S.finite_toSet.eventually_cofinite_notMem] with w hw hwS
    rw [hφ w hwS, hw]
  set Φ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ with hΦ

  have hloc : ∀ v, v ∉ S → ∀ h ∈ GlobalTheory.InertSph.KAt σ W v, om (1, h) Φ = Φ := by
    intro v hv h hh
    obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
    have e1 : Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) (φ v) r := by rw [hΦ, hrt, Function.update_eq_self]
    have hRest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) (φ v) r :=
      ⟨hr, by rw [← e1]; exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
    have hA := hAct v hv h hh
    rw [← hφ v hv] at hA
    rw [e1, hA r hRest]

  have hcut : ∀ v, v ∉ S → loc (idem F v) (idem_mul_self v) k ∈ GlobalTheory.InertSph.KAt σ W v := by
    intro v hv
    refine loc_mem_KAt F E σ d W v k fun z hz => ⟨?_, ?_⟩
    · refine GlobalTheory.T.mem_adelicLatticeAtPlace_of_tensor_with_lattice F E n d X W v _ hn hXL fun x hx => ?_
      have h0 := GlobalTheory.InertSphStab.vecMulVec_mem X W v hx hz
      rw [← GlobalTheory.InertSphStab.vecMulVec_mul_transpose]
      exact (hlat v hv _).2 h0
    · refine GlobalTheory.T.mem_adelicLatticeAtPlace_of_tensor_with_lattice F E n d X W v _ hn hXL fun x hx => ?_
      have h0 := GlobalTheory.InertSphStab.vecMulVec_mem X W v hx hz
      refine (hlat v hv _).1 ?_
      rw [GlobalTheory.InertSphStab.vecMulVec_mul_transpose, Matrix.mulVec_mulVec, mat_mul_inv, Matrix.one_mulVec]
      exact h0
  have hcutS : ∀ v ∈ S, loc (idem F v) (idem_mul_self v) k = 1 := by
    intro v hv
    apply ua_ext
    rw [mat_loc, mat_one, ← sub_eq_zero, phi_sub_one]
    exact hS v hv _ fun u hu => by rw [smul_eq_mul, mul_idem_of_evFin hu]
  have hone : ∀ v, om (1, loc (idem F v) (idem_mul_self v) k) Φ = Φ := by
    intro v
    by_cases hv : v ∈ S
    · rw [hcutS v hv]; show om 1 Φ = Φ; rw [map_one]; rfl
    · exact hloc v hv _ (hcut v hv)
  have hlist : ∀ l : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F),
      om (1, (l.map fun v => loc (idem F v) (idem_mul_self v) k).prod) Φ = Φ := by
    intro l
    induction l with
    | nil => show om 1 Φ = Φ; rw [map_one]; rfl
    | cons v t ih =>
      rw [List.map_cons, List.prod_cons]
      have : ((1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J), loc (idem F v) (idem_mul_self v) k *
          (t.map fun v => loc (idem F v) (idem_mul_self v) k).prod) =
          (1, loc (idem F v) (idem_mul_self v) k) * (1, (t.map fun v => loc (idem F v) (idem_mul_self v) k).prod) := by
        simp
      rw [this, map_mul, Module.End.mul_apply, ih, hone]
  have hT : ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), om (1, loc (idemS F T) (idemS_mul_self T) k) Φ = Φ := by
    intro T
    have e : loc (idemS F T) (idemS_mul_self T) k = (T.toList.map fun v => loc (idem F v) (idem_mul_self v) k).prod := by
      apply ua_ext
      rw [mat_prod_loc k _ T.nodup_toList, Finset.toList_toFinset, mat_loc]
    rw [e]; exact hlist _

  have hcont := hw.2.2
  have hΦA : Φ ∈ (GlobalTheory.WeilM.adeleClass F).sp (Fin n × Fin d) := GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd
  funext x
  have hc := hcont _ (ev_mem_adm x) Φ hΦA
  have ht : Filter.Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) =>
      ((1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J), loc (idemS F T) (idemS_mul_self T) k)) Filter.atTop (nhds (1, k)) :=
    tendsto_const_nhds.prodMk_nhds (GlobalTheory.T.tendsto_unitaryGroupIdempotentLocalization_finiteSets F E σ d W.J k hinf)
  have hlim : Filter.Tendsto (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) =>
      (LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) (om (1, loc (idemS F T) (idemS_mul_self T) k) Φ))
      Filter.atTop (nhds ((LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) (om (1, k) Φ))) :=
    (hc.tendsto _).comp ht
  have hconst : (fun T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) =>
      (LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) (om (1, loc (idemS F T) (idemS_mul_self T) k) Φ)) =
      fun _ => Φ x := by
    funext T; rw [hT T]; rfl
  rw [hconst] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeStabilizers_fix_vacua_fixes_pureTensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)),
    0 < n → X.L.IsLattice E → W.L.IsLattice E → M.IsGood ψ → M.IsWeil ψ χX χW om →
    (∀ v, v ∉ S → ∀ k ∈ GlobalTheory.InertSph.KAt σ W v,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, k)) (M.vac v) (M.vac v)) →
    ∀ k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J,
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w, w ∉ S → ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W w) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w)) → (∀ w, w ∉ S → φ w = M.vac w) →
      om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  atlas_forward_decl GlobalTheory.SphGlob.fixes_pure
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SphFix

theorem fixes_pure_vacua : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), S₀ ⊆ S → ∀ k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J,
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
    (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w) →
    (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w) →
    (∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a × Fin (a + a') → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F w)) → (∀ w ∉ S, φ w = G.M.vac w) →
      om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∧
    (∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a' × Fin (a + a') → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ w ∉ S, φ w = G.M'.vac w) →
      om' (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) := by
  classical
  intro P F E _ _ _ _ _ σ B a a' G X om om' hT
  obtain ⟨S₁, h₁⟩ := GlobalTheory.T.unramified_places_invariant P F E σ B a a' G X om om' hT
  obtain ⟨S₂, h₂⟩ := GlobalTheory.T.unramified_places_spherical P F E σ B a a' G X om om' hT
  refine ⟨S₁ ∪ S₂, fun S hS k hinf hSk hl hl' => ⟨fun f φ hφ hv => ?_, fun f φ hφ hv => ?_⟩⟩
  · exact GlobalTheory.T.latticeStabilizers_fix_vacua_fixes_pureTensor F E σ a (a + a') G.V G.W G.M B.ψ X.β (X.β / X.α) om S (Nat.zero_lt_of_lt hT.geo.lt)
      hT.geo.hV.lat hT.geo.hW.lat hT.geo.hM hT.weil
      (fun v hv k hk => h₁ v (fun h => hv (hS (Finset.mem_union_left _ h))) k hk) k hinf hSk hl f φ hφ hv
  · exact GlobalTheory.T.latticeStabilizers_fix_vacua_fixes_pureTensor F E σ a' (a + a') G.V' G.W G.M' B.ψ X.α (X.α / X.β) om' S
      (lt_of_le_of_lt (Nat.zero_le _) hT.geo.aBig) hT.geo.hV'.lat hT.geo.hW.lat hT.geo.hM' hT.weil'
      (fun v hv k hk => h₂ v (fun h => hv (hS (Finset.mem_union_right _ h))) k hk) k hinf hSk hl' f φ hφ hv

end GlobalTheory.SphFix

end
end
