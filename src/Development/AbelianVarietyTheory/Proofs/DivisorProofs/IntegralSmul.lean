import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralPullThird
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarSumLeibniz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarPullbackHolomorphicZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFormsMulClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSmoothPartitionUnityHolAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIntegralFinSumCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDelChartSupportedMulFormEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasDelFinsetSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOfValuesSesq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcFormLocFormChernFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernAtOneEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormsFrameIndependentClosed

section
section
open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.CxForm

theorem contDiffOn_dbar_const_dir {n : ℕ} {f : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (w : V n) : ContDiffOn ℝ ∞ (fun v => GlobalTheory.dbar f v w) U := by
  have h : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  simp only [GlobalTheory.dbar_apply]
  exact ContDiffOn.const_smul _ ((h.clm_apply contDiffOn_const).add
    (ContDiffOn.const_smul _ (h.clm_apply contDiffOn_const)))

theorem contDiffOn_repr_dbarAt {n : ℕ} {γ : V n → Alt n} {U : Set (V n)} (hU : IsOpen U)
    (hγ : ∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (γ v) S) U) (T : Finset (Fin (n + n))) :
    ContDiffOn ℝ ∞ (fun v => (bas n).repr (dbarAt γ v) T) U := by
  have key : (fun v => (bas n).repr (dbarAt γ v) T) = fun v => ∑ a, ∑ S,
      GlobalTheory.dbar (fun x => (bas n).repr (γ x) S) v (coordVec a) * (bas n).repr (dzb a * bas n S) T := by
    funext v
    simp only [dbarAt, coefwise, map_sum, Finset.mul_sum, mul_smul_comm, map_smul,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [key]
  exact ContDiffOn.sum fun a _ => ContDiffOn.sum fun S _ =>
    (contDiffOn_dbar_const_dir hU (hγ S) _).mul contDiffOn_const

end GlobalTheory.CxForm
end

open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_dbar_coefficients : ∀ {n : ℕ} {γ : V n → Alt n} {U : Set (V n)}, IsOpen U → (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (γ v) S) U) → ∀ (T : Finset (Fin (n + n))), ContDiffOn ℝ ∞ (fun v => (bas n).repr (dbarAt γ v) T) U := by
  atlas_forward_decl GlobalTheory.CxForm.contDiffOn_repr_dbarAt
end

section
open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_sum_leibniz : ∀ {n : ℕ} {ι : Type} [Fintype ι] {c : ι → V n → ℂ} {F : ι → V n → Alt n} {v : V n}, (∀ i, DifferentiableAt ℝ (c i) v) → (∀ i S, DifferentiableAt ℝ (fun x => (bas n).repr (F i x) S) v) → dbarAt (fun x => ∑ i, c i x • F i x) v = ∑ i, ((∑ a, GlobalTheory.dbar (c i) v (coordVec a) • dzb a) * F i v + c i v • dbarAt (F i) v) := by
  first | exact @GlobalTheory.CxForm.dbarAt_sum_smul | exact GlobalTheory.CxForm.dbarAt_sum_smul | (intros; apply GlobalTheory.CxForm.dbarAt_sum_smul <;> assumption)
end

section
section
open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.CxForm

theorem sum_dbar_comp_smul_dzb {n m : ℕ} {φ : V n → V m} {c : V m → ℂ} {v : V n}
    (hφ : DifferentiableAt ℂ φ v) (hc : DifferentiableAt ℝ c (φ v)) :
    ∑ a, GlobalTheory.dbar (fun x => c (φ x)) v (coordVec a) • dzb a =
      pull (fderiv ℂ φ v) (∑ b, GlobalTheory.dbar c (φ v) (coordVec b) • dzb b) := by
  have key (w : V m) : GlobalTheory.dbar c (φ v) w = ∑ b, GlobalTheory.dbar c (φ v) (coordVec b) * conj (w b) := by
    have hw : w = ∑ b, w b • coordVec b := by
      simpa using ((EuclideanSpace.basisFun (Fin m) ℂ).sum_repr w).symm
    conv_lhs => rw [hw]
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smulₛₗ, smul_eq_mul, mul_comm]
  rw [map_sum]
  simp only [map_smul, (pull_dz _ _).2, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [GlobalTheory.dbar_comp_holo hc hφ, key, Finset.sum_smul]

end GlobalTheory.CxForm
end

open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_comp_holomorphic : ∀ {n m : ℕ} {φ : V n → V m} {c : V m → ℂ} {v : V n}, DifferentiableAt ℂ φ v → DifferentiableAt ℝ c (φ v) → ∑ a, GlobalTheory.dbar (fun x => c (φ x)) v (coordVec a) • dzb a = pull (fderiv ℂ φ v) (∑ b, GlobalTheory.dbar c (φ v) (coordVec b) • dzb b) := by
  atlas_forward_decl GlobalTheory.CxForm.sum_dbar_comp_smul_dzb
end

section
section
set_option autoImplicit false

open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.PullCoefDiff

theorem repr_mul_eq_sum {n : ℕ} (x y : Alt n) (S : Finset (Fin (n + n))) :
    (bas n).repr (x * y) S =
      ∑ A, ∑ B, (bas n).repr x A * (bas n).repr y B * (bas n).repr (bas n A * bas n B) S := by
  conv_lhs => rw [← (bas n).sum_repr x, ← (bas n).sum_repr y]
  rw [Finset.sum_mul_sum]
  simp only [map_sum, Finsupp.finset_sum_apply, smul_mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem ι_eq_sum {m : ℕ} (u : Fin m ⊕ Fin m → ℂ) :
    ExteriorAlgebra.ι ℂ u = ∑ a, u (.inl a) • dz a + ∑ a, u (.inr a) • dzb a := by
  simp only [dz, dzb, ← map_smul, ← map_sum, ← map_add]
  refine congrArg _ (funext ?_)
  rintro (b | b) <;> simp [Pi.single_apply, Finset.sum_apply]

theorem differentiableAt_repr_pull {n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : E → V n →L[ℂ] V m} {v : E} (hL : ∀ b a, DifferentiableAt ℝ (fun x => L x (coordVec b) a) v)
    (θ : Alt m) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun x => (bas n).repr (pull (L x) θ) S) v := by
  induction θ using ExteriorAlgebra.induction generalizing S with
  | algebraMap r => simp only [AlgHom.commutes]; exact differentiableAt_const _
  | ι u =>
    rw [ι_eq_sum]
    simp only [map_add, map_sum, map_smul, (pull_dz _ _).1, (pull_dz _ _).2, Finsupp.add_apply,
      Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
    refine DifferentiableAt.add ?_ ?_
    · exact DifferentiableAt.fun_sum fun a _ => (DifferentiableAt.fun_sum fun b _ => (hL b a).mul_const _).const_mul _
    · refine DifferentiableAt.fun_sum fun a _ => (DifferentiableAt.fun_sum fun b _ =>
        DifferentiableAt.mul_const ?_ _).const_mul _
      exact Complex.conjCLE.differentiableAt.comp v (hL b a)
  | mul a b ha hb =>
    simp only [map_mul, repr_mul_eq_sum (pull _ a)]
    exact DifferentiableAt.fun_sum fun A _ => DifferentiableAt.fun_sum fun B _ => ((ha A).mul (hb B)).mul_const _
  | add a b ha hb =>
    simp only [map_add, Finsupp.add_apply]
    exact (ha S).add (hb S)

theorem differentiableAt_repr_pull_fderiv : ∀ {n m : ℕ} {φ : V n → V m} {U : Set (V n)}, IsOpen U →
    DifferentiableOn ℂ φ U → ∀ {v : V n}, v ∈ U → ∀ (θ : Alt m) (S : Finset (Fin (n + n))),
    DifferentiableAt ℝ (fun x => (bas n).repr (pull (fderiv ℂ φ x) θ) S) v := by
  intro n m φ U hU hφ v hv θ S
  refine differentiableAt_repr_pull (fun b a => ?_) θ S
  have h₁ : ContDiffAt ℂ 2 φ v := GlobalTheory.SCV.contDiffAt_of_differentiableOn hφ (hU.mem_nhds hv) 2
  have h₂ : DifferentiableAt ℂ (fderiv ℂ φ) v :=
    (h₁.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h₃ : DifferentiableAt ℂ (fun x => fderiv ℂ φ x (coordVec b)) v := h₂.clm_apply (differentiableAt_const _)
  have h₄ : DifferentiableAt ℂ (fun x => fderiv ℂ φ x (coordVec b) a) v :=
    (EuclideanSpace.proj (𝕜 := ℂ) a).differentiableAt.comp v h₃
  exact h₄.restrictScalars ℝ

end GlobalTheory.PullCoefDiff
end

open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableAt_pullback_form : ∀ {n m : ℕ} {φ : V n → V m} {U : Set (V n)}, IsOpen U → DifferentiableOn ℂ φ U → ∀ {v : V n}, v ∈ U → ∀ (θ : Alt m) (S : Finset (Fin (n + n))), DifferentiableAt ℝ (fun x => (bas n).repr (pull (fderiv ℂ φ x) θ) S) v := by
  atlas_forward_decl GlobalTheory.PullCoefDiff.differentiableAt_repr_pull_fderiv
end

section
open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_pullback_holomorphic_zero : ∀ {n m : ℕ} {φ : V n → V m} {U : Set (V n)}, IsOpen U → DifferentiableOn ℂ φ U → ∀ {v : V n}, v ∈ U → ∀ (θ : Alt m), dbarAt (fun x => pull (fderiv ℂ φ x) θ) v = 0 := by
  first | exact @GlobalTheory.CxForm.PullClosed.dbarAt_pull_fderiv | exact GlobalTheory.CxForm.PullClosed.dbarAt_pull_fderiv | (intros; apply GlobalTheory.CxForm.PullClosed.dbarAt_pull_fderiv <;> assumption)
end

section
section
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
open Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.CxForm

theorem dbarAt_congr {n : ℕ} {γ δ : V n → Alt n} {v : V n} (h : γ =ᶠ[𝓝 v] δ) :
    dbarAt γ v = dbarAt δ v := by
  unfold dbarAt coefwise
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  have hS : (fun x => (bas n).repr (γ x) S) =ᶠ[𝓝 v] fun x => (bas n).repr (δ x) S := h.mono fun x hx => congrArg (fun y => (bas n).repr y S) hx
  show GlobalTheory.dbar _ v (coordVec a) • _ = GlobalTheory.dbar _ v (coordVec a) • _
  rw [GlobalTheory.dbar_congr hS]

theorem dbarAt_eq_sum {n : ℕ} (β : V n → Alt n) (w : V n) :
    dbarAt β w = ∑ S, (∑ b, GlobalTheory.dbar (fun y => (bas n).repr (β y) S) w (coordVec b) • dzb b) * bas n S := by
  simp only [dbarAt, coefwise, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  exact Finset.sum_comm

theorem dbarAt_pull_comp {n m : ℕ} {φ : V n → V m} {U : Set (V n)} (hU : IsOpen U)
    (hφ : DifferentiableOn ℂ φ U) {v : V n} (hv : v ∈ U) {β : V m → Alt m}
    (hβ : ∀ S, DifferentiableAt ℝ (fun w => (bas m).repr (β w) S) (φ v)) :
    dbarAt (fun x => pull (fderiv ℂ φ x) (β (φ x))) v = pull (fderiv ℂ φ v) (dbarAt β (φ v)) := by
  have hφv : DifferentiableAt ℂ φ v := hφ.differentiableAt (hU.mem_nhds hv)
  have e1 : (fun x => pull (fderiv ℂ φ x) (β (φ x))) =
      fun x => ∑ S, (fun S y => (bas m).repr (β (φ y)) S) S x • (fun S y => pull (fderiv ℂ φ y) (bas m S)) S x := by
    funext x
    conv_lhs => rw [← (bas m).sum_repr (β (φ x)), map_sum]
    exact Finset.sum_congr rfl fun S _ => map_smul _ _ _
  rw [e1, GlobalTheory.T.dbar_sum_leibniz (c := fun S y => (bas m).repr (β (φ y)) S) (F := fun S y => pull (fderiv ℂ φ y) (bas m S)) (fun S => (hβ S).comp v (hφv.restrictScalars ℝ))
    (fun S T => GlobalTheory.T.differentiableAt_pullback_form hU hφ hv _ T)]
  simp only [GlobalTheory.T.dbar_pullback_holomorphic_zero hU hφ hv, smul_zero, add_zero]
  rw [dbarAt_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [GlobalTheory.T.dbar_comp_holomorphic hφv (hβ S), map_mul]

theorem isForm_dbar {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) (α : A.Fld)
    (h : A.IsForm α) : A.IsForm (A.dbar α) := by
  have hloc : ∀ i, ∀ v ∈ (A.e i).target, A.loc (A.dbar α) i v = dbarAt (A.loc α i) v := by
    intro i v hv
    rw [HolAtlas.loc, dif_pos hv]
    show dbarAt (A.loc α i) ((A.e i) ((A.e i).symm v)) = _
    rw [(A.e i).right_inv hv]
  refine ⟨fun i S => ?_, fun x x' hxx' => ?_⟩
  · exact (GlobalTheory.T.contDiffOn_dbar_coefficients (A.e i).open_target (h.smooth i) S).congr fun v hv => by rw [hloc i v hv]
  · have hU : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) :=
      x.ch.isOpen_inter_preimage_symm x'.ch.open_source
    have hφ : DifferentiableOn ℂ (x'.ch ∘ x.ch.symm) (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) :=
      A.holo x.1.1 x'.1.1
    have e : x.ch.symm (x.ch x.pt) = x'.pt := (x.ch.left_inv x.2).trans hxx'
    have hv0 : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source := by
      refine ⟨x.ch.map_source x.2, ?_⟩
      show x.ch.symm (x.ch x.pt) ∈ x'.ch.source
      rw [e]
      exact x'.2
    have hφv0 : (x'.ch ∘ x.ch.symm) x.crd = x'.crd := by
      show x'.ch (x.ch.symm (x.ch x.pt)) = x'.ch x'.pt
      rw [e]
    have key : ∀ v ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source,
        A.loc α x.1.1 v = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) v) (A.loc α x'.1.1 ((x'.ch ∘ x.ch.symm) v)) := by
      intro v hv
      rw [HolAtlas.loc, dif_pos hv.1]
      have := h.compat ⟨(x.1.1, x.ch.symm v), x.ch.map_target hv.1⟩ ⟨(x'.1.1, x.ch.symm v), hv.2⟩ rfl
      have e2 : x.ch (x.ch.symm v) = v := x.ch.right_inv hv.1
      simp only [HolAtlas.Pt.crd, HolAtlas.Pt.ch, HolAtlas.Pt.pt] at this
      rw [this, e2]
      exact congrArg _ (HolAtlas.loc_crd A α ⟨(x'.1.1, x.ch.symm v), hv.2⟩).symm
    show dbarAt (A.loc α x.1.1) x.crd = pull _ (dbarAt (A.loc α x'.1.1) x'.crd)
    rw [dbarAt_congr (Filter.eventuallyEq_of_mem (hU.mem_nhds hv0) key),
      dbarAt_pull_comp hU hφ hv0 (β := A.loc α x'.1.1) (fun S => ?_), hφv0]
    rw [hφv0]
    exact ((h.smooth x'.1.1 S).contDiffAt (x'.ch.open_target.mem_nhds (x'.ch.map_source x'.2))).differentiableAt
      (by simp)

end GlobalTheory.CxForm
end

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isForm_dbar' : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld), A.IsForm α → A.IsForm (A.dbar α) := by
  atlas_forward_decl GlobalTheory.CxForm.isForm_dbar
end

section
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isForm_mul_of_isForm_of_isForm : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α β : A.Fld), A.IsForm α → A.IsForm β → A.IsForm (α * β) := by
  first | exact @GlobalTheory.CxForm.FormMul.isForm_mul | exact GlobalTheory.CxForm.FormMul.isForm_mul | (intros; apply GlobalTheory.CxForm.FormMul.isForm_mul <;> assumption)
end

section
section
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.CxForm.DelClosed

theorem del_mul_of_del_eq_zero : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n)
    (α β : A.Fld), A.IsForm α → A.IsForm β → A.del β = 0 → A.del (α * β) = A.del α * β := by
  intro M _ n A α β hα hβ hdβ
  funext x
  have hl : A.loc (α * β) x.1.1 = fun v => A.loc α x.1.1 v * A.loc β x.1.1 v :=
    funext (FormMul.loc_mul A α β _)
  obtain ⟨y, hy⟩ := FormMul.delAt_mul (FormMul.differentiableAt_coef hα x) (FormMul.differentiableAt_coef hβ x)
  have h2 : delAt (A.loc β x.1.1) x.crd = 0 := congrFun hdβ x
  show delAt (A.loc (α * β) x.1.1) x.crd = delAt (A.loc α x.1.1) x.crd * β x
  rw [hl, hy, h2, mul_zero, add_zero, HolAtlas.loc_crd]

end GlobalTheory.CxForm.DelClosed
end

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.del_mul_of_del_eq_zero' : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α β : A.Fld), A.IsForm α → A.IsForm β → A.del β = 0 → A.del (α * β) = A.del α * β := by
  atlas_forward_decl GlobalTheory.CxForm.DelClosed.del_mul_of_del_eq_zero
end

section
section
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

namespace GlobalTheory.CxForm.SmulForm

theorem loc_smul {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) (c : ℂ) (α : A.Fld) (i : A.ι)
    (v : ReciprocityTheory.L2DbarEstimates.V n) : A.loc (c • α) i v = c • A.loc α i v := by
  unfold HolAtlas.loc
  split_ifs
  · rfl
  · exact (smul_zero c).symm

theorem isForm_smul_and_del_smul {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (c : ℂ)
    (α : A.Fld) (h : A.IsForm α) : A.IsForm (c • α) ∧ A.del (c • α) = c • A.del α := by
  have hc (i : A.ι) (S : Finset (Fin (n + n))) : (fun v => (bas n).repr (A.loc (c • α) i v) S) =
      fun v => c • (bas n).repr (A.loc α i v) S := by
    funext v
    rw [loc_smul, map_smul, Finsupp.smul_apply]
  refine ⟨⟨fun i S => ?_, fun x x' e => ?_⟩, funext fun x => ?_⟩
  · rw [hc]
    exact (h.smooth i S).const_smul c
  · rw [Pi.smul_apply, Pi.smul_apply, map_smul, ← h.compat x x' e]
  · have hd (S : Finset (Fin (n + n))) :
        DifferentiableAt ℝ (fun v => (bas n).repr (A.loc α x.1.1 v) S) x.crd :=
      ((h.smooth x.1.1 S).contDiffAt (x.ch.open_target.mem_nhds (x.ch.map_source x.2))).differentiableAt (by simp)
    rw [Pi.smul_apply, HolAtlas.del, HolAtlas.del, delAt, delAt, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← mul_smul_comm, coefwise, coefwise, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [hc, GlobalTheory.del_const_smul c (hd S), ContinuousLinearMap.smul_apply, smul_assoc]

end GlobalTheory.CxForm.SmulForm
end

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isForm_smul_del_smul : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (c : ℂ) (α : A.Fld), A.IsForm α → A.IsForm (c • α) ∧ A.del (c • α) = c • A.del α := by
  atlas_forward_decl GlobalTheory.CxForm.SmulForm.isForm_smul_and_del_smul
end

section
section
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

namespace GlobalTheory.CxFormStokes

theorem integral_ddc_mul_eq_zero : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M]
    [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (η Z : A.Fld), A.IsForm η → A.IsForm Z → A.del Z = 0 →
    A.dbar Z = 0 → A.integral (A.ddc η * Z) = 0 := by
  intro M _ _ _ _ _ _ n A η Z hη hZ hdZ _
  have hdη := GlobalTheory.T.isForm_dbar' A η hη
  have hγ := GlobalTheory.T.isForm_mul_of_isForm_of_isForm A _ _ hdη hZ
  obtain ⟨hγ', hdel⟩ := GlobalTheory.T.isForm_smul_del_smul A GlobalTheory.HermFrame.kappa _ hγ
  have e1 : A.ddc η * Z = A.del (GlobalTheory.HermFrame.kappa • (A.dbar η * Z)) := by
    rw [hdel, GlobalTheory.T.del_mul_of_del_eq_zero' A _ _ hdη hZ hdZ, GlobalTheory.CxForm.HolAtlas.ddc, smul_mul_assoc]
  rw [e1]
  set γ := GlobalTheory.HermFrame.kappa • (A.dbar η * Z)
  obtain ⟨N, c, χ, hχs, hχt, hχ1⟩ := GlobalTheory.T.exists_finite_smooth_partition_unity_holAtlas A
  have hf : ∀ j, A.IsForm (A.fn (χ j) * γ) := fun j => GlobalTheory.T.isForm_mul_of_isForm_of_isForm A _ _ (A.isForm_fn (hχs j)) hγ'
  have hsum : γ = ∑ j, A.fn (χ j) * γ := by
    rw [← Finset.sum_mul]
    funext x
    simp only [Finset.sum_apply, Pi.mul_apply, GlobalTheory.CxForm.HolAtlas.fn, ← map_sum]
    rw [show (∑ j, ((χ j x.pt : ℝ) : ℂ)) = 1 by exact_mod_cast hχ1 x.pt, map_one, one_mul]
  rw [hsum, GlobalTheory.T.holAtlas_del_finset_sum A _ hf, GlobalTheory.T.holAtlas_integral_fin_sum_compact A _ fun j => GlobalTheory.T.holAtlas_isForm_del A _ (hf j)]
  exact Finset.sum_eq_zero fun j _ => GlobalTheory.T.integral_del_chartSupported_mul_form_eq_zero A γ (χ j) (c j) hγ' (hχs j) (hχt j)

end GlobalTheory.CxFormStokes
end

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_ddc_closed_form_zero : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M]
    [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (η Z : A.Fld), A.IsForm η → A.IsForm Z → A.del Z = 0 →
    A.dbar Z = 0 → A.integral (A.ddc η * Z) = 0 := by
  atlas_forward_decl GlobalTheory.CxFormStokes.integral_ddc_mul_eq_zero
end

section
section
set_option autoImplicit false

noncomputable section

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexOrder

namespace GlobalTheory.FlagChernWeil

open GlobalTheory.CxForm

variable {M : Type} [TopologicalSpace M] {n : ℕ}

end GlobalTheory.FlagChernWeil

namespace GlobalTheory.FlagChernWeil

open GlobalTheory.CxForm Filter Topology

variable {M : Type} [TopologicalSpace M] {n : ℕ}

end GlobalTheory.FlagChernWeil

namespace GlobalTheory.FlagChernWeil

open GlobalTheory.CxForm

variable {M : Type} [TopologicalSpace M] {n : ℕ} {A : HolAtlas M n}

end GlobalTheory.FlagChernWeil

namespace GlobalTheory.FlagChernWeil

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

theorem evalF_sub {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {ι : Type} (w : ι → A.Pt → Ev n)
    (P Q : MvPolynomial ι ℝ) : evalF A w (P - Q) = evalF A w P - evalF A w Q := by
  funext x
  simp only [evalF, fld, map_sub, Pi.sub_apply, AddSubgroupClass.coe_sub]

theorem evalF_mul {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {ι : Type} (w : ι → A.Pt → Ev n)
    (P Q : MvPolynomial ι ℝ) : evalF A w (P * Q) = evalF A w P * evalF A w Q := by
  funext x
  simp only [evalF, fld, map_mul, Pi.mul_apply, MulMemClass.coe_mul]

theorem integral_evalForm_flag_family_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsRegVar p D) (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2) (A : HermLB p) (σ : k →+* ℂ)
    (Z Z' : MvPolynomial (Fin 4) ℝ),
    (MvPolynomial.X 3 - MvPolynomial.X 1 * MvPolynomial.X 2 : MvPolynomial (Fin 4) ℝ) ∣ Z - Z' →
      (hX.atlas σ).integral (evalF (hX.atlas σ) (fam4 hX σ H fl A) Z) =
        (hX.atlas σ).integral (evalF (hX.atlas σ) (fam4 hX σ H fl A) Z') := by
  intro k _ X _ p D hX E h H fl A σ Z Z' ⟨W, hW⟩
  haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ hX.isProjOver
  haveI : T2Space (CxPts p σ) := CxPts.t2Space_cxPts_of_isProjOver σ hX.isProjOver
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  obtain ⟨hL, hE, -⟩ := GlobalTheory.T.firstChern_form_properties k X p D hX σ
  obtain ⟨hω, hc, hc₁, hc₂, -, -, -, hd⟩ := hE E h H fl fl
  have hev := (GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ D (hX.atlas σ)).2.2.2.1 (Fin 4) (fam4 hX σ H fl A)
  have f0 : ∀ i, (hX.atlas σ).IsForm (fld _ (fam4 hX σ H fl A i)) := by
    intro i
    fin_cases i
    exacts [(hL _ A).1.1, (hL _ A).1.1, (hL _ A).1.1, hc.1]
  have f1 : ∀ i, (hX.atlas σ).del (fld _ (fam4 hX σ H fl A i)) = 0 := by
    intro i
    fin_cases i
    exacts [(hL _ A).2.1, (hL _ A).2.1, (hL _ A).2.1, hc₁]
  have f2 : ∀ i, (hX.atlas σ).dbar (fld _ (fam4 hX σ H fl A i)) = 0 := by
    intro i
    fin_cases i
    exacts [(hL _ A).2.2.1, (hL _ A).2.2.1, (hL _ A).2.2.1, hc₂]
  have hX3 : evalF (hX.atlas σ) (fam4 hX σ H fl A) (MvPolynomial.X 3 - MvPolynomial.X 1 * MvPolynomial.X 2) =
      (hX.atlas σ).ddc (fld _ (omF hX σ h fl)) := by
    rw [hd]
    funext x
    simp only [evalF, fld, map_sub, map_mul, map_X, aeval_X]
    rfl
  have e := GlobalTheory.T.integral_sub_of_isForm' (hX.atlas σ) _ _ (hev Z f0).1 (hev Z' f0).1
  rw [← evalF_sub, hW, evalF_mul, hX3,
    GlobalTheory.T.integral_ddc_closed_form_zero (hX.atlas σ) _ _ hω.1 (hev W f0).1 ((hev W f0).2.1 f1) ((hev W f0).2.2 f2)] at e
  linarith

end GlobalTheory.FlagChernWeil
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_evalForm_mod_relation_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2) (A : HermLB p) (σ : k →+* ℂ)
    (Z Z' : MvPolynomial (Fin 4) ℝ), (MvPolynomial.X 3 - MvPolynomial.X 1 * MvPolynomial.X 2 : MvPolynomial (Fin 4) ℝ) ∣ Z - Z' →
      (hX.atlas σ).integral (evalF (hX.atlas σ) (fam4 hX σ H fl A) Z) = (hX.atlas σ).integral (evalF (hX.atlas σ) (fam4 hX σ H fl A) Z') := by
  atlas_forward_decl GlobalTheory.FlagChernWeil.integral_evalForm_flag_family_eq
end

section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineGysin

section Atlas

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem fld_add (u v : A.Pt → Ev n) : fld A (u + v) = fld A u + fld A v := by
  funext x; simp [fld]

theorem evalF_add {ι : Type} (w : ι → A.Pt → Ev n) (P Q : MvPolynomial ι ℝ) :
    evalF A w (P + Q) = evalF A w P + evalF A w Q := by
  funext x; simp [evalF, fld]

theorem evalF_mul {ι : Type} (w : ι → A.Pt → Ev n) (P Q : MvPolynomial ι ℝ) :
    evalF A w (P * Q) = evalF A w P * evalF A w Q := by
  funext x; simp [evalF, fld]

theorem evalF_C {ι : Type} (w : ι → A.Pt → Ev n) (a : ℝ) :
    evalF A w (C a) = ((a : ℂ)) • (1 : A.Fld) := by
  funext x
  simp only [evalF, fld, map_C, aeval_C, Pi.smul_apply, Pi.one_apply]
  first
  | (rw [Subalgebra.coe_algebraMap, Algebra.algebraMap_eq_smul_one]; rfl)
  | (rw [Subalgebra.coe_algebraMap, Algebra.algebraMap_eq_smul_one, Complex.coe_algebraMap])
  | (simp [Algebra.algebraMap_eq_smul_one, -Complex.coe_smul])

theorem evalF_X {ι : Type} (w : ι → A.Pt → Ev n) (i : ι) : evalF A w (X i) = fld A (w i) := by
  funext x; simp [evalF, fld]

theorem evalF_one {ι : Type} (w : ι → A.Pt → Ev n) : evalF A w 1 = 1 := by
  funext x; simp [evalF, fld]

theorem evalF_rename {ι κ : Type} (w : κ → A.Pt → Ev n) (e : ι → κ) (P : MvPolynomial ι ℝ) :
    evalF A w (rename e P) = evalF A (fun i => w (e i)) P := by
  funext x; simp [evalF, fld, map_rename, aeval_rename, Function.comp_def]

end Atlas

end GlobalTheory.LineGysin

namespace GlobalTheory.LineGysin

section Int

variable {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] {n : ℕ} (A : HolAtlas M n)

theorem integral_add {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) :
    A.integral (α + β) = A.integral α + A.integral β := by
  have L := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous M n A
  rw [← wInt_one, ← wInt_one, ← wInt_one]
  refine (L.2.1 _ α β hα hβ (fun ε => ?_) (fun ε => ?_)).2
  · haveI := L.1 α hα ε; exact integrable_const _
  · haveI := L.1 β hβ ε; exact integrable_const _

theorem integral_smul (t : ℝ) {α : A.Fld} (hα : A.IsForm α) :
    A.integral ((t : ℂ) • α) = t * A.integral α := by
  have L := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous M n A
  rw [← wInt_one, ← wInt_one]
  exact L.2.2.1 _ t α hα

end Int

end GlobalTheory.LineGysin

namespace GlobalTheory.LineGysin

theorem dvd_swap (t : ℝ) (T : MvPolynomial (Fin 3) ℝ) :
    (X 3 - X 1 * X 2 : MvPolynomial (Fin 4) ℝ) ∣
      rename (![1, 2, 0] : Fin 3 → Fin 4) (C t * X 0 * aeval ![X 0 + X 1, X 0 * X 1, X 2] T) -
        C t * X 1 * aeval ![X 1 + X 2, X 3, X 0] T := by
  set I : Ideal (MvPolynomial (Fin 4) ℝ) := Ideal.span {X 3 - X 1 * X 2}
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, ← Ideal.Quotient.mkₐ_eq_mk ℝ]
  have h1 : ∀ g : Fin 3 → MvPolynomial (Fin 4) ℝ,
      Ideal.Quotient.mkₐ ℝ I (aeval g T) = aeval (fun j => Ideal.Quotient.mkₐ ℝ I (g j)) T := fun g => by
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have h2 : ∀ g : Fin 3 → MvPolynomial (Fin 3) ℝ,
      rename (![1, 2, 0] : Fin 3 → Fin 4) (aeval g T) = aeval (fun j => rename (![1, 2, 0] : Fin 3 → Fin 4) (g j)) T :=
    fun g => by rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have h3 : Ideal.Quotient.mkₐ ℝ I (X 1 * X 2) = Ideal.Quotient.mkₐ ℝ I (X 3) := by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton.2 ⟨-1, by ring⟩
  simp only [map_mul, rename_C, rename_X, h2]
  rw [h1, h1]
  congr 1
  refine congrArg (fun f => aeval f T) ?_
  funext j
  fin_cases j
  · simp
  · simpa [Ideal.Quotient.mkₐ_eq_mk] using h3
  · simp

theorem gysin : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ (t : ℝ) (T : MvPolynomial (Fin 3) ℝ),
      (hY.atlas σ).integral (evalF (hY.atlas σ) (fun i => c1F hY σ (![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] i))
          (C t * X 0 * aeval ![X 0 + X 1, X 0 * X 1, X 2] T)) =
        -t * (hB.atlas σ).integral (evalF (hB.atlas σ) (fam4 hB σ H flB A) (aeval ![X 1 + X 2, X 3, X 0] T)) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl _ A σ t T
  haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ hY.isProjOver
  haveI : T2Space (CxPts p σ) := CxPts.t2Space_cxPts_of_isProjOver σ hY.isProjOver
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  obtain ⟨bB1, bB2, bB3⟩ := GlobalTheory.T.firstChern_form_properties k B q d hB σ
  obtain ⟨bY1, bY2, -⟩ := GlobalTheory.T.firstChern_form_properties k Y p (d + 1) hY σ
  obtain ⟨hol, hc1, hE⟩ := bB3 Y p (d + 1) hY π w
  obtain ⟨hc2, hsum⟩ := hE E h H flB fl
  have cB := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)
  have cY := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hY.atlas σ)
  have pl := cB.2.2.2.2 _ _ (hY.atlas σ) _ hol
  simp only [pullF] at hc1 hc2
  have gens : ∀ i : Fin 3, evalF (hY.atlas σ) (fam4 hY σ (H.pull π w) fl (A.pull π w)) (![X 1 + X 2, X 3, X 0] i) =
      pullF hB hY σ π w (evalF (hB.atlas σ) (fam4 hB σ H flB A) (![X 1 + X 2, X 3, X 0] i)) := by
    intro i
    simp only [pullF]
    fin_cases i
    · change evalF _ _ (X 1 + X 2) = (hB.atlas σ).pullback _ _ (evalF _ _ (X 1 + X 2))
      rw [evalF_add,
        evalF_add, evalF_X, evalF_X, evalF_X, evalF_X]
      change fld _ (c1F hY σ (VMetric.grLB fl 0 (H.pull π w))) + fld _ (c1F hY σ (VMetric.grLB fl 1 (H.pull π w))) =
        (hB.atlas σ).pullback _ _ (fld _ (c1F hB σ (VMetric.grLB flB 0 H)) + fld _ (c1F hB σ (VMetric.grLB flB 1 H)))
      rw [← fld_add, hsum, fld_add, hc1, hc1, (pl.2 0 _ _).1]
    · change evalF _ _ (X 3) = (hB.atlas σ).pullback _ _ (evalF _ _ (X 3))
      rw [evalF_X, evalF_X]
      exact hc2
    · change evalF _ _ (X 0) = (hB.atlas σ).pullback _ _ (evalF _ _ (X 0))
      rw [evalF_X, evalF_X]
      exact hc1 A
  have hpull : ∀ P : MvPolynomial (Fin 3) ℝ,
      evalF (hY.atlas σ) (fam4 hY σ (H.pull π w) fl (A.pull π w)) (aeval ![X 1 + X 2, X 3, X 0] P) =
        pullF hB hY σ π w (evalF (hB.atlas σ) (fam4 hB σ H flB A) (aeval ![X 1 + X 2, X 3, X 0] P)) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a =>
      simp only [aeval_C, MvPolynomial.algebraMap_eq, evalF_C, pullF]
      rw [(pl.2 _ 1 1).2.2.1, pl.1]
    | add P Q hP hQ =>
      rw [map_add, evalF_add, evalF_add, hP, hQ]
      simp only [pullF]
      rw [(pl.2 0 _ _).1]
    | mul_X P i hP =>
      rw [map_mul, evalF_mul, evalF_mul, hP, aeval_X, gens i]
      simp only [pullF]
      rw [(pl.2 0 _ _).2.1]
  have e3 : (fun i => c1F hY σ (![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] i)) =
      fun i => fam4 hY σ (H.pull π w) fl (A.pull π w) ((![1, 2, 0] : Fin 3 → Fin 4) i) := by
    funext i; fin_cases i <;> rfl
  rw [e3, ← evalF_rename,
    GlobalTheory.T.integral_evalForm_mod_relation_eq k Y p (d + 1) hY _ (h.pull π w) (H.pull π w) fl (A.pull π w) σ _ _ (dvd_swap t T),
    evalF_mul, evalF_mul, evalF_C, evalF_X, hpull]

  have hcB : ∀ i, (hB.atlas σ).IsForm (fld (hB.atlas σ) (fam4 hB σ H flB A i)) := by
    intro i
    fin_cases i
    · exact (bB1 A A).1.1
    · exact (bB1 _ A).1.1
    · exact (bB1 _ A).1.1
    · exact (bB2 E h H flB flB).2.1.1
  have hφ := (cB.2.2.2.1 (Fin 4) _ (aeval ![X 1 + X 2, X 3, X 0] T) hcB).1
  have hpφ : (hY.atlas σ).IsForm (pullF hB hY σ π w (evalF (hB.atlas σ) (fam4 hB σ H flB A) (aeval ![X 1 + X 2, X 3, X 0] T))) :=
    ((pl.2 0 _ 0).2.2.2 hφ).1
  have hx0 : (hY.atlas σ).IsForm (fld (hY.atlas σ) (c1F hY σ (fam5 π w H flB fl A 0))) := (bY1 _ (A.pull π w)).1.1
  have hom : (hY.atlas σ).IsForm (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl)) :=
    (bY2 _ (h.pull π w) (H.pull π w) fl fl).1.1
  have G := GlobalTheory.T.flag_bundle_chern_integral_pull_third k B Y q p d hB hY π w E h H flB fl ‹_› A σ _ hφ
  have G1 := (G 1).1
  have G0 := (G 0).2
  rw [hs, pow_zero, mul_one] at G0
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.choose_zero_right, mul_one, Nat.cast_one, map_one,
    Nat.sub_zero, Nat.mul_zero, Nat.zero_sub, Nat.choose_self, one_mul, evalF_one, CharP.cast_eq_zero, zero_add,
    div_one, MvPolynomial.C_1] at G0
  rw [pow_one] at G1
  set x0 := fld (hY.atlas σ) (c1F hY σ (fam5 π w H flB fl A 0))
  set om := fld (hY.atlas σ) (omF hY σ (h.pull π w) fl)
  set pφ := pullF hB hY σ π w (evalF (hB.atlas σ) (fam4 hB σ H flB A) (aeval ![X 1 + X 2, X 3, X 0] T))
  have key : (t : ℂ) • (1 : (hY.atlas σ).Fld) * fld (hY.atlas σ) (fam4 hY σ (H.pull π w) fl (A.pull π w) 1) * pφ =
      (t : ℂ) • ((x0 + om) * pφ + ((-1 : ℝ) : ℂ) • (om * pφ)) := by
    rw [smul_mul_assoc, one_mul, smul_mul_assoc]
    congr 1
    rw [add_mul]
    simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul, add_neg_cancel_right]
    rfl
  have f1 : (hY.atlas σ).IsForm ((x0 + om) * pφ) := (cY.2.1 0 _ _ (cY.2.1 0 _ _ hx0 hom).1 hpφ).2.1
  have f2 : (hY.atlas σ).IsForm (om * pφ) := (cY.2.1 0 _ _ hom hpφ).2.1
  have f3 : (hY.atlas σ).IsForm (((-1 : ℝ) : ℂ) • (om * pφ)) := (cY.2.1 _ _ _ f2 f2).2.2.1
  have f4 : (hY.atlas σ).IsForm ((x0 + om) * pφ + ((-1 : ℝ) : ℂ) • (om * pφ)) := (cY.2.1 0 _ _ f1 f3).1
  rw [key, integral_smul _ _ f4, integral_add _ f1 f3, integral_smul _ _ f2, G1, G0]
  ring

end GlobalTheory.LineGysin
end
end
