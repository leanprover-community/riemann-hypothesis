import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLinearLocalStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarChainRuleHolomorphicPullback

section
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false

namespace GlobalTheory.CxForm.SmoothCoef

theorem contDiffOn_del_dir {n : ℕ} {s : Set (V n)} {f : V n → ℂ} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (e : V n) :
    ContDiffOn ℝ ∞ (fun v => del f v e) s := by
  have h : ContDiffOn ℝ ∞ (fun v => fderiv ℝ f v) s := hf.fderiv_of_isOpen hs (by simp)
  simp only [del_apply]
  exact ((h.clm_apply contDiffOn_const).sub ((h.clm_apply contDiffOn_const).const_smul _)).const_smul _

theorem contDiffOn_dbar_dir {n : ℕ} {s : Set (V n)} {f : V n → ℂ} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (e : V n) :
    ContDiffOn ℝ ∞ (fun v => dbar f v e) s := by
  have h : ContDiffOn ℝ ∞ (fun v => fderiv ℝ f v) s := hf.fderiv_of_isOpen hs (by simp)
  simp only [dbar_apply]
  exact ((h.clm_apply contDiffOn_const).add ((h.clm_apply contDiffOn_const).const_smul _)).const_smul _

theorem contDiffOn_coef : ∀ (n : ℕ) (s : Set (V n)) (F : V n → Alt n), IsOpen s →
    (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (F v) S) s) →
    ∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (delAt F v) S) s ∧
      ContDiffOn ℝ ∞ (fun v => (bas n).repr (dbarAt F v) S) s := by
  intro n s F hs hF U
  constructor
  · simp only [delAt, coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.coe_finset_sum,
      Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    exact ContDiffOn.sum fun a _ => ContDiffOn.sum fun S _ => (contDiffOn_del_dir hs (hF S) _).mul contDiffOn_const
  · simp only [dbarAt, coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.coe_finset_sum,
      Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    exact ContDiffOn.sum fun a _ => ContDiffOn.sum fun S _ => (contDiffOn_dbar_dir hs (hF S) _).mul contDiffOn_const

end GlobalTheory.CxForm.SmoothCoef
end

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_coefficients_delOperator_dbarOperator : ∀ (n : ℕ) (s : Set (V n)) (F : V n → Alt n), IsOpen s →
    (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (F v) S) s) →
    ∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (delAt F v) S) s ∧ ContDiffOn ℝ ∞ (fun v => (bas n).repr (dbarAt F v) S) s := by
  atlas_forward_decl GlobalTheory.CxForm.SmoothCoef.contDiffOn_coef
end

section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false

namespace GlobalTheory.CxForm.HolAtlas

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem loc_eventuallyEq_pull {α : A.Fld} (hα : A.IsForm α) (x x' : A.Pt) (h : x.pt = x'.pt) :
    A.loc α x.1.1 =ᶠ[𝓝 x.crd] fun y => pull (fderiv ℂ (x'.ch ∘ x.ch.symm) y) (A.loc α x'.1.1 ((x'.ch ∘ x.ch.symm) y)) := by
  have hU : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) :=
    x.ch.isOpen_inter_preimage_symm x'.ch.open_source
  have hxU : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source :=
    ⟨x.ch.map_source x.2, by simp only [Set.mem_preimage, x.ch.left_inv x.2, h]; exact x'.2⟩
  refine Filter.eventually_of_mem (hU.mem_nhds hxU) fun y hy => ?_
  show A.loc α x.1.1 y = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) y) (A.loc α x'.1.1 ((x'.ch ∘ x.ch.symm) y))
  let p : A.Pt := ⟨(x.1.1, x.ch.symm y), x.ch.map_target hy.1⟩
  let p' : A.Pt := ⟨(x'.1.1, x.ch.symm y), hy.2⟩
  have e1 : A.loc α x.1.1 y = α p := by rw [HolAtlas.loc, dif_pos hy.1]
  have e2 : A.loc α x'.1.1 ((x'.ch ∘ x.ch.symm) y) = α p' := A.loc_crd α p'
  have e3 : p.crd = y := x.ch.right_inv hy.1
  rw [e1, e2, hα.compat p p' rfl]
  show pull (fderiv ℂ (x'.ch ∘ x.ch.symm) p.crd) (α p') = _
  rw [e3]

theorem chg_facts (x x' : A.Pt) (h : x.pt = x'.pt) :
    IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) ∧ x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source ∧
    DifferentiableOn ℂ (x'.ch ∘ x.ch.symm) (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) ∧
    (x'.ch ∘ x.ch.symm) x.crd = x'.crd :=
  ⟨x.ch.isOpen_inter_preimage_symm x'.ch.open_source,
    ⟨x.ch.map_source x.2, by simp only [Set.mem_preimage, x.ch.left_inv x.2, h]; exact x'.2⟩,
    A.holo x.1.1 x'.1.1, by simp only [Function.comp_apply, x.ch.left_inv x.2, h]⟩

theorem loc_diffAt {α : A.Fld} (hα : A.IsForm α) (x : A.Pt) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun y => (bas n).repr (A.loc α x.1.1 y) S) x.crd :=
  ((hα.smooth x.1.1 S).contDiffAt (x.ch.open_target.mem_nhds (x.ch.map_source x.2))).differentiableAt (by simp)

theorem isForm_del_dbar {α : A.Fld} (hα : A.IsForm α) : A.IsForm (A.del α) ∧ A.IsForm (A.dbar α) := by
  have hloc : ∀ (T : (V n → Alt n) → V n → Alt n) (i : A.ι) (v : V n), v ∈ (A.e i).target →
      A.loc (fun x => T (A.loc α x.1.1) x.crd) i v = T (A.loc α i) v := by
    intro T i v hv
    rw [HolAtlas.loc, dif_pos hv]
    show T (A.loc α i) ((A.e i) ((A.e i).symm v)) = _
    rw [(A.e i).right_inv hv]
  refine ⟨⟨fun i S => ?_, fun x x' h => ?_⟩, ⟨fun i S => ?_, fun x x' h => ?_⟩⟩
  · exact ((GlobalTheory.T.contDiffOn_coefficients_delOperator_dbarOperator n _ (A.loc α i) (A.e i).open_target (hα.smooth i) S).1).congr fun v hv => by
      rw [show A.del α = fun x => delAt (A.loc α x.1.1) x.crd from rfl, hloc delAt i v hv]
  · obtain ⟨hU, hxU, hτ, hτx⟩ := chg_facts A x x' h
    have hβ : ∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (A.loc α x'.1.1 y) S) ((x'.ch ∘ x.ch.symm) x.crd) := by
      rw [hτx]; exact loc_diffAt A hα x'
    show delAt (A.loc α x.1.1) x.crd = pull _ (delAt (A.loc α x'.1.1) x'.crd)
    rw [((GlobalTheory.T.delOperatorAt_dbarOperatorAt_linear_local n x.crd).2.2.2.1 _ _ (loc_eventuallyEq_pull A hα x x' h)).1,
      (GlobalTheory.T.del_dbar_chainRule_holomorphicPullback n n _ _ _ x.crd hU hxU hτ hβ).1, hτx]
  · exact ((GlobalTheory.T.contDiffOn_coefficients_delOperator_dbarOperator n _ (A.loc α i) (A.e i).open_target (hα.smooth i) S).2).congr fun v hv => by
      rw [show A.dbar α = fun x => dbarAt (A.loc α x.1.1) x.crd from rfl, hloc dbarAt i v hv]
  · obtain ⟨hU, hxU, hτ, hτx⟩ := chg_facts A x x' h
    have hβ : ∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (A.loc α x'.1.1 y) S) ((x'.ch ∘ x.ch.symm) x.crd) := by
      rw [hτx]; exact loc_diffAt A hα x'
    show dbarAt (A.loc α x.1.1) x.crd = pull _ (dbarAt (A.loc α x'.1.1) x'.crd)
    rw [((GlobalTheory.T.delOperatorAt_dbarOperatorAt_linear_local n x.crd).2.2.2.1 _ _ (loc_eventuallyEq_pull A hα x x' h)).2,
      (GlobalTheory.T.del_dbar_chainRule_holomorphicPullback n n _ _ _ x.crd hU hxU hτ hβ).2, hτx]

end GlobalTheory.CxForm.HolAtlas

theorem GlobalTheory.CxForm.isForm_del_dbar : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (α : A.Fld), A.IsForm α →
    A.IsForm (A.del α) ∧ A.IsForm (A.dbar α) :=
  fun _ _ _ A _ hα => A.isForm_del_dbar hα
end
