import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPosFrameQuotIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubquotientCurvatureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcEqOfLocalEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernIsometricEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoFlagRationalSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernOneEqNegDdcLogDet

section
section
set_option autoImplicit false

noncomputable section

open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.SecForm

theorem extTrace_midIn_indep {M : Type} [TopologicalSpace M] {n : ℕ} {A : HolAtlas M n} (T : HermSeq A 1 1)
    (a b : T.κ) (i : A.ι) {v : V n} (hv : v ∈ chartSet T a i ∩ chartSet T b i) :
    extTrace (midIn T a i) v = extTrace (midIn T b i) v := by
  have hh := trans_eventually T a b i hv
  have e : midIn T b i =ᶠ[𝓝 v] fun w => chg (gIn T a b i w) (midIn T a i w) := hh.mono fun w hw => hw.2.2.1
  have hK : MContDiffAt 1 (midIn T a i) v := (isPosFrame_midIn T a i).isHermFrame.one hv.1
  have hp : ∀ᶠ x in 𝓝 v, (midIn T a i x).PosDef :=
    mem_of_superset ((isOpen_chartSet T a i).mem_nhds hv.1) fun x hx => (isPosFrame_midIn T a i).posDef x hx
  have hg := holo_gIn T a b i hv
  have hA : MContDiffAt 1 (gIn T a b i) v := hg.1.of_le (by norm_cast)
  have hA0 : ∀ η, mdbar (gIn T a b i) v η = 0 := hg.2.self_of_nhds
  have ht : ∀ᶠ x in 𝓝 v, (gIn T a b i x).toBlocks₂₁ = 0 := hh.mono fun w hw => hw.2.2.2.2
  have hu : IsUnit (gIn T a b i v).det := by
    have ha : (A.e i).symm v ∈ T.U a := hv.1.2
    have hb : (A.e i).symm v ∈ T.U b := hv.2.2
    have h1 : T.g a b ((A.e i).symm v) * T.g b a ((A.e i).symm v) = 1 := by
      rw [T.g_mul a b a _ ⟨⟨ha, hb⟩, ha⟩, T.g_self a _ ha]
    exact Matrix.isUnit_det_of_right_inverse h1
  rw [extTrace_congr e, extTrace_chg hK hp hA hu hA0 ht]

end GlobalTheory.SecForm
end
end

open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extTrace_chart_indep : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} {A : HolAtlas M n} (T : HermSeq A 1 1) (a b : T.κ) (i : A.ι) {v : V n}, v ∈ chartSet T a i ∩ chartSet T b i → extTrace (midIn T a i) v = extTrace (midIn T b i) v := by
  atlas_forward_decl GlobalTheory.SecForm.extTrace_midIn_indep
end

section
set_option autoImplicit false

noncomputable section

open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.SecForm

theorem contDiffOn_extTrace : ∀ {n : ℕ} {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
    {U : Set (V n)} {H : V n → Matrix (m ⊕ l) (m ⊕ l) ℂ}, IsPosFrame U H →
    ∀ ξ η : V n, ContDiffOn ℝ ∞ (fun v => extTrace H v ξ η) U := by
  intro n m l _ _ _ _ U H hH ξ η
  have hM : ∀ v ∈ U, MContDiffAt ∞ H v := fun v hv a b =>
    (hH.smooth a b).contDiffAt (hH.isOpen.mem_nhds hv)
  have hP : ∀ v ∈ U, ∀ᶠ x in 𝓝 v, (H x).PosDef := fun v hv =>
    Filter.eventually_of_mem (hH.isOpen.mem_nhds hv) hH.posDef
  have key : ∀ v ∈ U,
      ContDiffAt ℝ ∞ (fun x => kappa * (secondForm H x ξ * secondFormAdj H x η).trace) v := by
    intro v hv
    have hu : IsUnit (H v).det := (hH.posDef v hv).det_pos.ne'.isUnit
    have hs : IsUnit (subGram (H v)).det := (posDef_subGram (hH.posDef v hv)).det_pos.ne'.isUnit
    have hc : ∀ ζ, MContDiffAt ∞ (fun x => secondForm H x ζ) v := fun ζ => by
      show MContDiffAt ∞ (fun x => quotMap m l * conn H x ζ * incl m l) v
      exact ((mContDiffAt_const _).mul ((hM v hv).conn hu (j := ∞) (by simp) ζ)).mul
        (mContDiffAt_const _)
    have ha : MContDiffAt ∞ (fun x => secondFormAdj H x η) v := by
      show MContDiffAt ∞ (fun x => (subGram (H x))ᵀ⁻¹ * (secondForm H x η)ᴴ * (quotGram (H x))ᵀ) v
      exact (((hM v hv).subGram.transpose.inv (by rwa [det_transpose])).mul
        (hc η).conjTranspose).mul ((hM v hv).quotGram hs).transpose
    have hp := (hc ξ).mul ha
    simp only [Matrix.trace, Matrix.diag_apply]
    exact contDiffAt_const.mul (ContDiffAt.sum fun i _ => hp i i)
  intro v hv
  refine ((key v hv).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hH.isOpen.mem_nhds hv] with x hx
  exact extTrace_eq ((hM x hx).of_le (by simp)) (hP x hx) ξ η

end GlobalTheory.SecForm
end
end

section
open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_extTrace_of_isPosFrame : ∀ {n : ℕ} {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set (V n)} {H : V n → Matrix (m ⊕ l) (m ⊕ l) ℂ}, IsPosFrame U H → ∀ ξ η : V n, ContDiffOn ℝ ∞ (fun v => extTrace H v ξ η) U := by
  first | exact @GlobalTheory.SecForm.contDiffOn_extTrace | exact GlobalTheory.SecForm.contDiffOn_extTrace | (intros; apply GlobalTheory.SecForm.contDiffOn_extTrace <;> assumption)
end

section
open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ddc_eq_of_local_eq : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) (α : A.Fld) (x : A.Pt) (f : V n → Alt n), A.loc α x.1.1 =ᶠ[𝓝 x.crd] f → A.ddc α x = kappa • delAt (dbarAt f) x.crd := by
  first | exact @GlobalTheory.SecForm.DdcGerm.ddc_eq_of_eventuallyEq | exact GlobalTheory.SecForm.DdcGerm.ddc_eq_of_eventuallyEq | (intros; apply GlobalTheory.SecForm.DdcGerm.ddc_eq_of_eventuallyEq <;> assumption)
end

section
open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecForm.DdcValues

variable {n : ℕ}

theorem coefwise_del_sum {ι : Type} [Fintype ι] {g : ι → V n → ℂ} (w : ι → Alt n) {β : V n → Alt n} {v : V n}
    (hg : ∀ i, DifferentiableAt ℝ (g i) v) (hβ : ∀ᶠ x in 𝓝 v, β x = ∑ i, g i x • w i) (ξ : V n) :
    coefwise (fun f => del f v ξ) β = ∑ i, del (g i) v ξ • w i := by
  have h (S) : del (fun x => (bas n).repr (β x) S) v ξ = ∑ i, del (g i) v ξ * (bas n).repr (w i) S := by
    have e : (fun x => (bas n).repr (β x) S) =ᶠ[𝓝 v] fun x => ∑ i, (bas n).repr (w i) S • g i x :=
      hβ.mono fun x hx => by simp [hx, Finsupp.finsetSum_apply, mul_comm]
    rw [del_congr e, del_sum (A := fun i x => (bas n).repr (w i) S • g i x) (fun i _ => (hg i).const_smul ((bas n).repr (w i) S)), ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [del_const_smul _ (hg i)]
    simp [mul_comm]
  simp only [coefwise, h, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_smul, ← Finset.smul_sum, Module.Basis.sum_repr]

theorem coefwise_dbar_sum {ι : Type} [Fintype ι] {g : ι → V n → ℂ} (w : ι → Alt n) {v : V n}
    (hg : ∀ i, DifferentiableAt ℝ (g i) v) (ξ : V n) :
    coefwise (fun f => dbar f v ξ) (fun x => ∑ i, g i x • w i) = ∑ i, dbar (g i) v ξ • w i := by
  have h (S) : dbar (fun x => (bas n).repr (∑ i, g i x • w i) S) v ξ =
      ∑ i, dbar (g i) v ξ * (bas n).repr (w i) S := by
    have e : (fun x => (bas n).repr (∑ i, g i x • w i) S) = fun x => ∑ i, (bas n).repr (w i) S • g i x :=
      funext fun x => by simp [Finsupp.finsetSum_apply, mul_comm]
    rw [e, dbar_sum (A := fun i x => (bas n).repr (w i) S • g i x) (fun i _ => (hg i).const_smul ((bas n).repr (w i) S)), ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dbar_const_smul _ (hg i)]
    simp [mul_comm]
  simp only [coefwise, h, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_smul, ← Finset.smul_sum, Module.Basis.sum_repr]

theorem sym_mul_sym_swap (a b c d : Fin n) : sym (a, b) * sym (c, d) = -(sym (a, d) * sym (c, b)) := by
  apply Subtype.ext
  change dz a * dzb b * (dz c * dzb d) = -(dz a * dzb d * (dz c * dzb b))
  have h₁ : dzb b * (dz c * dzb d) = dz c * dzb d * dzb b :=
    Subalgebra.mem_center_iff.1 (sym (c, d)).2 _
  have h₂ : dzb d * (dz c * dzb b) = dz c * dzb b * dzb d :=
    Subalgebra.mem_center_iff.1 (sym (c, b)).2 _
  have h₃ : dzb d * dzb b = -(dzb b * dzb d) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
  rw [mul_assoc, mul_assoc, h₁, h₂, mul_assoc, mul_assoc, h₃]
  simp only [mul_neg]

theorem sum_four (D : Fin n → Fin n → Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, (D a b c d + D c d a b - D a d c b - D c b a d) • (sym (a, b) * sym (c, d)) =
      (4 : ℂ) • ∑ a, ∑ b, ∑ c, ∑ d, D a b c d • (sym (a, b) * sym (c, d)) := by
  have P (F : Fin n → Fin n → Fin n → Fin n → Ev n) : ∑ a, ∑ b, ∑ c, ∑ d, F a b c d =
      ∑ p : Fin n × Fin n × Fin n × Fin n, F p.1 p.2.1 p.2.2.1 p.2.2.2 := by
    simp only [Fintype.sum_prod_type]
  rw [P, P]
  simp only [sub_smul, add_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  set T := ∑ p : Fin n × Fin n × Fin n × Fin n,
    D p.1 p.2.1 p.2.2.1 p.2.2.2 • (sym (p.1, p.2.1) * sym (p.2.2.1, p.2.2.2)) with hT
  have h₂ : ∑ p : Fin n × Fin n × Fin n × Fin n,
      D p.2.2.1 p.2.2.2 p.1 p.2.1 • (sym (p.1, p.2.1) * sym (p.2.2.1, p.2.2.2)) = T :=
    Fintype.sum_equiv ⟨fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1), fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun p => by simp [mul_comm]
  have h₃ : ∑ p : Fin n × Fin n × Fin n × Fin n,
      D p.1 p.2.2.2 p.2.2.1 p.2.1 • (sym (p.1, p.2.1) * sym (p.2.2.1, p.2.2.2)) = -T := by
    rw [hT, ← Finset.sum_neg_distrib]
    exact Fintype.sum_equiv ⟨fun p => (p.1, p.2.2.2, p.2.2.1, p.2.1), fun p => (p.1, p.2.2.2, p.2.2.1, p.2.1),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun p => by rw [sym_mul_sym_swap, smul_neg]; rfl
  have h₄ : ∑ p : Fin n × Fin n × Fin n × Fin n,
      D p.2.2.1 p.2.1 p.1 p.2.2.2 • (sym (p.1, p.2.1) * sym (p.2.2.1, p.2.2.2)) = -T := by
    rw [hT, ← Finset.sum_neg_distrib]
    exact Fintype.sum_equiv ⟨fun p => (p.2.2.1, p.2.1, p.1, p.2.2.2), fun p => (p.2.2.1, p.2.1, p.1, p.2.2.2),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun p => by rw [sym_mul_sym_swap, smul_neg, mul_comm]; rfl
  rw [h₂, h₃, h₄]
  module

end GlobalTheory.SecForm.DdcValues

namespace GlobalTheory.SecForm

open DdcValues

theorem ddc_ofValues {n : ℕ} (α : V n → V n → V n → ℂ) (v : V n)
    (h : ∀ a b, ContDiffAt ℝ 2 (fun x => α x (coordVec a) (coordVec b)) v) :
    kappa • delAt (dbarAt fun x => (ofValues (α x) : Alt n)) v = (ofValuesTwo (ddcForm α v) : Alt n) := by
  set f : Fin n × Fin n → V n → ℂ := fun p x => α x (coordVec p.1) (coordVec p.2) with hf
  have e₀ : (fun x => (ofValues (α x) : Alt n)) = fun x => ∑ p, f p x • (sym p : Alt n) := by
    funext x
    simp only [ofValues, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, Fintype.sum_prod_type, hf]
  have hev : ∀ᶠ x in 𝓝 v, ∀ p, DifferentiableAt ℝ (f p) x :=
    eventually_all.2 fun p => ((h p.1 p.2).eventually (by simp)).mono fun x hx => hx.differentiableAt (by simp)
  have e₁ : ∀ᶠ x in 𝓝 v, dbarAt (fun x => (ofValues (α x) : Alt n)) x =
      ∑ q : Fin n × Fin n × Fin n, dbar (f q.2) x (coordVec q.1) • (dzb q.1 * sym q.2) := by
    filter_upwards [hev] with x hx
    rw [e₀, dbarAt, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [coefwise_dbar_sum _ hx, Finset.mul_sum]
    simp only [mul_smul_comm]
  have hd (q : Fin n × Fin n × Fin n) : DifferentiableAt ℝ (fun x => dbar (f q.2) x (coordVec q.1)) v := by
    have h1 := (h q.2.1 q.2.2).fderiv_right (m := 1) (by norm_num)
    simp only [dbar_apply]
    exact (((h1.clm_apply contDiffAt_const).add
      ((h1.clm_apply contDiffAt_const).const_smul Complex.I)).const_smul (1 / 2 : ℂ)).differentiableAt one_ne_zero
  have e₂ : delAt (dbarAt fun x => (ofValues (α x) : Alt n)) v =
      ((∑ a, ∑ b, ∑ c, ∑ d, ddbar (f (c, d)) v (coordVec a) (coordVec b) • (sym (a, b) * sym (c, d)) : Ev n) :
        Alt n) := by
    simp only [delAt, coefwise_del_sum _ hd e₁, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul,
      Subalgebra.coe_mul, Fintype.sum_prod_type, Finset.mul_sum, mul_smul_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    rw [ddbar_eq_del_dbar (h c d), ← mul_assoc]
    rfl
  rw [e₂, ← Subalgebra.coe_smul]
  congr 1
  have := sum_four fun a b c d => ddbar (f (c, d)) v (coordVec a) (coordVec b)
  simp only [ofValuesTwo, ddcForm, mul_smul, ← Finset.smul_sum]
  erw [this]
  module

end GlobalTheory.SecForm
end
end

section
open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ddc_ofValues_eq : ∀ {n : ℕ} (α : V n → V n → V n → ℂ) (v : V n), (∀ a b, ContDiffAt ℝ 2 (fun x => α x (coordVec a) (coordVec b)) v) → kappa • delAt (dbarAt fun x => (ofValues (α x) : Alt n)) v = (ofValuesTwo (ddcForm α v) : Alt n) := by
  first | exact @GlobalTheory.SecForm.ddc_ofValues | exact GlobalTheory.SecForm.ddc_ofValues | (intros; apply GlobalTheory.SecForm.ddc_ofValues <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.SecForm.ChernTwo

variable {n : ℕ}

theorem sym_mul_swap (a b c d : Fin n) : sym (a, b) * sym (c, d) = -(sym (a, d) * sym (c, b)) := by
  apply Subtype.ext
  have h (u w : Fin n ⊕ Fin n → ℂ) : ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w =
      -(ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ u) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap u w)
  have h3 : dzb b * (dz c * dzb d) = -(dzb d * (dz c * dzb b)) := by
    have e1 : dzb b * dz c = -(dz c * dzb b) := h _ _
    have e2 : dzb b * dzb d = -(dzb d * dzb b) := h _ _
    have e3 : dz c * dzb d = -(dzb d * dz c) := h _ _
    rw [← mul_assoc, e1, neg_mul, mul_assoc, e2, mul_neg, ← mul_assoc, e3, neg_mul, neg_neg, mul_assoc]
  change dz a * dzb b * (dz c * dzb d) = -(dz a * dzb d * (dz c * dzb b))
  rw [mul_assoc, h3, mul_neg, mul_assoc]

def four (f : Fin n → Fin n → Fin n → Fin n → ℂ) : Ev n :=
  ∑ a, ∑ b, ∑ c, ∑ d, f a b c d • (sym (a, b) * sym (c, d))

theorem four_eq (f : Fin n → Fin n → Fin n → Fin n → ℂ) :
    four f = ∑ x : (Fin n × Fin n) × (Fin n × Fin n), f x.1.1 x.1.2 x.2.1 x.2.2 • (sym x.1 * sym x.2) := by
  simp only [four, Fintype.sum_prod_type]

theorem four_swap (f : Fin n → Fin n → Fin n → Fin n → ℂ) : four (fun a b c d => f c d a b) = four f := by
  rw [four_eq, four_eq]
  refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun x => ?_
  simp [mul_comm]

theorem four_swap' (f : Fin n → Fin n → Fin n → Fin n → ℂ) : four (fun a b c d => f a d c b) = -four f := by
  rw [four_eq, four_eq, ← Finset.sum_neg_distrib]
  refine Fintype.sum_equiv (⟨fun x => ((x.1.1, x.2.2), (x.2.1, x.1.2)), fun x => ((x.1.1, x.2.2), (x.2.1, x.1.2)),
    fun _ => rfl, fun _ => rfl⟩) _ _ ?_
  rintro ⟨⟨a, b⟩, c, d⟩
  simp only [Equiv.coe_fn_mk]
  rw [sym_mul_swap, smul_neg]

theorem four_add (f g : Fin n → Fin n → Fin n → Fin n → ℂ) :
    four (fun a b c d => f a b c d + g a b c d) = four f + four g := by
  simp only [four, add_smul, Finset.sum_add_distrib]

theorem four_sub (f g : Fin n → Fin n → Fin n → Fin n → ℂ) :
    four (fun a b c d => f a b c d - g a b c d) = four f - four g := by
  simp only [four, sub_smul, Finset.sum_sub_distrib]

theorem four_mul (t : ℂ) (f : Fin n → Fin n → Fin n → Fin n → ℂ) :
    four (fun a b c d => t * f a b c d) = t • four f := by
  simp only [four, mul_smul, Finset.smul_sum]

theorem four_wedge (α β : V n → V n → ℂ) :
    four (fun a b c d => wedge α β (coordVec a) (coordVec b) (coordVec c) (coordVec d)) =
      (4 : ℂ) • (ofValues α * ofValues β) := by
  set f : Fin n → Fin n → Fin n → Fin n → ℂ :=
    fun a b c d => α (coordVec a) (coordVec b) * β (coordVec c) (coordVec d) with hf
  have e0 : ofValues α * ofValues β = four f := by
    simp only [ofValues, four, Finset.sum_mul]
    simp only [Finset.mul_sum, smul_mul_smul_comm, hf]
  have e1 := four_swap f
  have e2 := four_swap' f
  have e3 := four_swap' fun a b c d => f c d a b
  have e : four (fun a b c d => wedge α β (coordVec a) (coordVec b) (coordVec c) (coordVec d)) =
      four f + four (fun a b c d => f c d a b) - four (fun a b c d => f a d c b) - four (fun a b c d => f c b a d) := by
    rw [← four_add, ← four_sub, ← four_sub]; rfl
  rw [e, e3, e1, e2, e0]
  module

theorem coeff_two {R : Type} [CommRing R] (F : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) :
    (Matrix.charpolyRev (-F)).coeff 2 =
      F (.inl 0) (.inl 0) * F (.inr 0) (.inr 0) - F (.inl 0) (.inr 0) * F (.inr 0) (.inl 0) := by
  rw [Matrix.charpolyRev, ← Matrix.det_submatrix_equiv_self (finSumFinEquiv (m := 1) (n := 1)).symm]
  have h0 : (finSumFinEquiv (m := 1) (n := 1)).symm (0 : Fin 2) = .inl 0 := rfl
  have h1 : (finSumFinEquiv (m := 1) (n := 1)).symm (1 : Fin 2) = .inr 0 := rfl
  rw [Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply, h0, h1]
  have : ∀ p q : Fin 1 ⊕ Fin 1, (1 - (Polynomial.X : Polynomial R) • (-F).map Polynomial.C) p q =
      (if p = q then 1 else 0) + Polynomial.C (F p q) * Polynomial.X := by
    intro p q
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply, map_neg, smul_eq_mul]
    ring
  simp only [this]
  have e : ∀ a b c d : R, ((1 + Polynomial.C a * Polynomial.X) * (1 + Polynomial.C d * Polynomial.X) -
      (0 + Polynomial.C b * Polynomial.X) * (0 + Polynomial.C c * Polynomial.X)) =
      1 + Polynomial.C (a + d) * Polynomial.X + Polynomial.C (a * d - b * c) * Polynomial.X ^ 2 := by
    intro a b c d
    simp only [map_add, map_sub, map_mul]; ring
  simp only [if_true, reduceCtorEq, if_false, e]
  simp [Polynomial.coeff_one, Polynomial.coeff_X, -map_add, -map_sub, -map_mul]

theorem aeval_curvPoly {r : Type} [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n) (p q : r) :
    MvPolynomial.aeval sym (GlobalTheory.GoodMetric.curvPoly G v p q) = ofValues (fun ξ η => curv G v ξ η p q) := by
  simp [GlobalTheory.GoodMetric.curvPoly, ofValues, Algebra.smul_def]

end GlobalTheory.SecForm.ChernTwo

namespace GlobalTheory.SecForm

open ChernTwo

theorem chernAt_two_eq {n : ℕ} (G : V n → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) (v : V n) :
    chernAt G v 2 = ofValuesTwo (chernTwo G v) := by
  have hc : ∀ a b c d, chernTwo G v a b c d = kappa ^ 2 * curvMinor G v (.inl 0) (.inr 0) a b c d := by
    intro a b c d
    simp only [chernTwo, Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton, curvMinor_self,
      Fin.default_eq_zero, curvMinor_comm G v (.inr 0) (.inl 0)]
    ring
  have e : ofValuesTwo (chernTwo G v) = (1 / 4 : ℂ) • four fun a b c d =>
      kappa ^ 2 * curvMinor G v (.inl 0) (.inr 0) (coordVec a) (coordVec b) (coordVec c) (coordVec d) := by
    simp only [ofValuesTwo, four, hc]
  rw [e, four_mul]
  simp only [curvMinor]
  rw [four_sub, four_wedge, four_wedge, chernAt, GlobalTheory.GoodMetric.chernPoly, coeff_two, map_sub, map_mul, map_mul]
  simp only [aeval_curvPoly]
  module

end GlobalTheory.SecForm
end
end

section
open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernAt_two_eq_ofValuesTwo_chernTwo : ∀ {n : ℕ} (G : V n → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) (v : V n), chernAt G v 2 = ofValuesTwo (chernTwo G v) := by
  first | exact @GlobalTheory.SecForm.chernAt_two_eq | exact GlobalTheory.SecForm.chernAt_two_eq | (intros; apply GlobalTheory.SecForm.chernAt_two_eq <;> assumption)
end

section
set_option autoImplicit false

open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.SecForm

private theorem ι_three_swap {W : Type} [AddCommGroup W] [Module ℂ W] (v w x : W) :
    ExteriorAlgebra.ι ℂ v * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ x) =
      -(ExteriorAlgebra.ι ℂ x * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ v)) := by
  have h : ∀ p q : W, ExteriorAlgebra.ι ℂ p * ExteriorAlgebra.ι ℂ q =
      -(ExteriorAlgebra.ι ℂ q * ExteriorAlgebra.ι ℂ p) :=
    fun p q => eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap p q)
  calc ExteriorAlgebra.ι ℂ v * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ x)
      = (ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ w) * ExteriorAlgebra.ι ℂ x := (mul_assoc _ _ _).symm
    _ = -(ExteriorAlgebra.ι ℂ w * (ExteriorAlgebra.ι ℂ v * ExteriorAlgebra.ι ℂ x)) := by
      rw [h v w, neg_mul, mul_assoc]
    _ = (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ x) * ExteriorAlgebra.ι ℂ v := by
      rw [h v x, mul_neg, neg_neg, mul_assoc]
    _ = _ := by rw [h w x, neg_mul, mul_assoc]

theorem sym_mul_sym_swap {n : ℕ} (a b c d : Fin n) :
    (sym (a, b) * sym (c, d) : Ev n) = -(sym (a, d) * sym (c, b)) := by
  apply Subtype.ext
  change dz a * dzb b * (dz c * dzb d) = -(dz a * dzb d * (dz c * dzb b))
  rw [mul_assoc, mul_assoc, ← mul_neg]
  congr 1
  exact ι_three_swap _ _ _

private theorem sum_four {ι R : Type} [Fintype ι] [AddCommMonoid R] (f : ι → ι → ι → ι → R) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ x : ι × ι × ι × ι, f x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  simp only [Fintype.sum_prod_type]

private theorem sum_four_swap_pairs {ι R : Type} [Fintype ι] [AddCommMonoid R] (f : ι → ι → ι → ι → R) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ b, ∑ c, ∑ d, f c d a b := by
  rw [sum_four f, sum_four fun a b c d => f c d a b]
  exact Fintype.sum_equiv ⟨fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1),
    fun _ => rfl, fun _ => rfl⟩ _ _ fun _ => rfl

private theorem sum_four_swap_second {ι R : Type} [Fintype ι] [AddCommMonoid R] (f : ι → ι → ι → ι → R) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ b, ∑ c, ∑ d, f a d c b := by
  rw [sum_four f, sum_four fun a b c d => f a d c b]
  exact Fintype.sum_equiv ⟨fun x => (x.1, x.2.2.2, x.2.2.1, x.2.1), fun x => (x.1, x.2.2.2, x.2.2.1, x.2.1),
    fun _ => rfl, fun _ => rfl⟩ _ _ fun _ => rfl

private theorem wedge_sum {ι R : Type} [Fintype ι] [CommRing R] [Algebra ℂ R] (s : ι → ι → R)
    (hs : ∀ a b c d, s a b * s c d = -(s a d * s c b)) (α β : ι → ι → ℂ) :
    (∑ a, ∑ b, α a b • s a b) * (∑ a, ∑ b, β a b • s a b) =
      (1 / 4 : ℂ) • ∑ a, ∑ b, ∑ c, ∑ d, wedge α β a b c d • (s a b * s c d) := by
  have h1 : (∑ a, ∑ b, α a b • s a b) * (∑ a, ∑ b, β a b • s a b) =
      ∑ a, ∑ b, ∑ c, ∑ d, (α a b * β c d) • (s a b * s c d) := by
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum, smul_mul_smul_comm]
  have h2 : ∑ a, ∑ b, ∑ c, ∑ d, (α c d * β a b) • (s a b * s c d) =
      ∑ a, ∑ b, ∑ c, ∑ d, (α a b * β c d) • (s a b * s c d) := by
    rw [sum_four_swap_pairs]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => by rw [mul_comm (s c d)]
  have h3 : ∀ γ : ι → ι → ι → ι → ℂ, ∑ a, ∑ b, ∑ c, ∑ d, γ a d c b • (s a b * s c d) =
      -∑ a, ∑ b, ∑ c, ∑ d, γ a b c d • (s a b * s c d) := by
    intro γ
    rw [sum_four_swap_second]
    simp only [← Finset.sum_neg_distrib, ← smul_neg, ← hs]
  have h4 := h3 fun a b c d => α a b * β c d
  have h5 := h3 fun a b c d => α c d * β a b
  rw [h1]
  simp only [wedge, add_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h4, h5, h2]
  module

theorem ofValues_mul_ofValues {n : ℕ} (α β : V n → V n → ℂ) :
    ofValues α * ofValues β = ofValuesTwo (wedge α β) :=
  wedge_sum (fun a b : Fin n => sym (a, b)) sym_mul_sym_swap
    (fun a b => α (coordVec a) (coordVec b)) (fun a b => β (coordVec a) (coordVec b))

end GlobalTheory.SecForm
end

section
open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ofValues_mul_ofValues' : ∀ {n : ℕ} (α β : V n → V n → ℂ), ofValues α * ofValues β = ofValuesTwo (wedge α β) := by
  first | exact @GlobalTheory.SecForm.ofValues_mul_ofValues | exact GlobalTheory.SecForm.ofValues_mul_ofValues | (intros; apply GlobalTheory.SecForm.ofValues_mul_ofValues <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open GlobalTheory.HermFrame GlobalTheory.SecForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped Classical ComplexOrder

namespace GlobalTheory.LineForm.DdcLine

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}

def hseq (hX : IsRegVar p D) (σ : k →+* ℂ) {E : X.Modules} (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2) :
    HermSeq (hX.atlas σ) 1 1 :=
  hX.seq (lineSC_shortExact fl) (h₁ := h.restrict (fl.isSubbundle 1) (fl.isVB 1)) (h₂ := h)
    (h₃ := VMetric.quot (S := lineSC fl) (r := 1) (s := 1) h (lineSC_shortExact fl) (fl.isVB 1) (fl.isVB_cokernel 1))
    (H.restrict _ _) H (VMetric.IsCInf.quot (S := lineSC fl) (r := 1) (s := 1) _ _ _ H) σ

variable (hX : IsRegVar p D) (σ : k →+* ℂ) {E : X.Modules} (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2)

theorem crd_mem (x : (hX.atlas σ).Pt) : x.crd ∈ chartSet (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1 := by
  refine ⟨x.ch.map_source x.2, ?_⟩
  show (x.ch.symm x.crd) ∈ ptsIn p σ (frameAt fl x.pt).U
  rw [x.ch.left_inv x.2]
  exact mem_frameAt fl x.pt

theorem loc_omF (x : (hX.atlas σ).Pt) :
    (hX.atlas σ).loc (fld _ (omF hX σ h fl)) x.1.1 =ᶠ[𝓝 x.crd]
      fun v => (ofValues (extTrace (midIn (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1) v) : Alt D) := by
  filter_upwards [(isOpen_chartSet (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1).mem_nhds (crd_mem hX σ h H fl x)] with v hv
  have hv1 : v ∈ ((hX.atlas σ).e x.1.1).target := hv.1
  rw [HolAtlas.loc, dif_pos hv1]
  set y : (hX.atlas σ).Pt := ⟨(x.1.1, ((hX.atlas σ).e x.1.1).symm v), ((hX.atlas σ).e x.1.1).map_target hv1⟩ with hy
  have hb : v ∈ chartSet (hseq hX σ h H fl) (frameAt fl y.pt) x.1.1 := ⟨hv1, mem_frameAt fl y.pt⟩
  have e1 : y.crd = v := ((hX.atlas σ).e x.1.1).right_inv hv1
  change (ofValues (extTrace (midIn (hseq hX σ h H fl) (frameAt fl y.pt) x.1.1) y.crd) : Alt D) = _
  rw [e1, GlobalTheory.T.extTrace_chart_indep (hseq hX σ h H fl) (frameAt fl y.pt) (frameAt fl x.pt) x.1.1 ⟨hb, hv⟩]

end GlobalTheory.LineForm.DdcLine

namespace GlobalTheory.LineForm.DdcLine

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
variable (hX : IsRegVar p D) (σ : k →+* ℂ)

theorem c1F_det_metric_eq_chernOne {F : X.Modules} {r : ℕ} {m : VMetric p F r} (Hm : m.IsCInf) (x : (hX.atlas σ).Pt) (c : Chart F r)
    (hc : x.pt ∈ ptsIn p σ c.U) :
    c1F hX σ (VMetric.det Hm) x = ofValues (chernOne (fun w => (m.met σ).G c (x.ch.symm w)) x.crd) := by
  obtain ⟨⟨a, y⟩, hy⟩ := x
  have hy' : y ∈ a.e.source := hy
  change y ∈ ptsIn p σ c.U at hc
  set b := pick ((VMetric.det Hm).φ σ).isLB y
  have hb : y ∈ ptsIn p σ ((VMetric.det Hm).B.U b) := mem_pick _ y
  have hc' : y ∈ ptsIn p σ ((VMetric.det Hm).B.U c) := hc
  have ho := ChartGlue.isOpen_over a.e (isOpen_ptsIn (p := p) (σ := σ) ((VMetric.det Hm).B.U c ⊓ (VMetric.det Hm).B.U b))
  have hm := ChartGlue.mem_over a.e hy' (mem_ptsIn_inf.2 ⟨hc', hb⟩)
  set u := c.isFrame.detUnit b.isFrame inf_le_left inf_le_right
  have hg := a.holo _ u.val
  have hf : ContDiffAt ℂ 2 (ev p σ _ u.val ∘ a.e.symm) (a.e y) :=
    (SCV.analyticAt_of_differentiableOn (hg.mono fun v hv => ⟨hv.1, hv.2⟩) (ho.mem_nhds hm)).contDiffAt
  have h0 : (ev p σ _ u.val ∘ a.e.symm) (a.e y) ≠ 0 := ev_ne_zero hm.2 u.isUnit
  have hC : ContDiffAt ℝ 2 (fun v => ((VMetric.det Hm).φ σ).φ c (a.e.symm v)) (a.e y) :=
    ((VMetric.det Hm).cInf σ).contDiffAt a hy' hc'
  have hlog : ContDiffAt ℝ 2 (fun v => Real.log (‖(ev p σ _ u.val ∘ a.e.symm) v‖ ^ 2)) (a.e y) :=
    ((hf.restrict_scalars ℝ).norm_sq ℂ).log (by simpa using h0)
  have key : leviForm (fun v => ((VMetric.det Hm).φ σ).φ b (a.e.symm v)) (a.e y) =
      leviForm (fun v => ((VMetric.det Hm).φ σ).φ c (a.e.symm v)) (a.e y) := by
    rw [leviForm_congr (u' := fun v => ((VMetric.det Hm).φ σ).φ c (a.e.symm v) +
        -Real.log (‖(ev p σ _ u.val ∘ a.e.symm) v‖ ^ 2)), leviForm_add hC hlog.neg,
      leviForm_neg, leviForm_log_normSq_eq_zero hf h0, neg_zero, add_zero]
    filter_upwards [ho.mem_nhds hm] with v hv
    rw [((VMetric.det Hm).φ σ).trans c b _ (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2, sub_eq_add_neg]
    rfl
  have eL : c1F hX σ (VMetric.det Hm) ⟨(a, y), hy⟩ =
      ofValues (HermFrame.ddc (fun v => ((VMetric.det Hm).φ σ).φ b (a.e.symm v)) (a.e y)) := rfl
  rw [eL]
  unfold HermFrame.ddc
  rw [key]
  have hM : MContDiffAt 2 (fun w => (m.met σ).G c (a.e.symm w)) (a.e y) :=
    (((Hm σ) c y hc).mContDiffAt a hy').of_le (WithTop.coe_le_coe.2 le_top)
  have hH : ∀ᶠ w in 𝓝 (a.e y), ((m.met σ).G c (a.e.symm w)).IsHermitian := by
    filter_upwards [ho.mem_nhds hm] with v hv
    exact ((m.met σ).posDef c _ (mem_ptsIn_inf.1 hv.2).1).1
  have hU : IsUnit ((m.met σ).G c (a.e.symm (a.e y))).det := by
    rw [a.e.left_inv hy']
    exact ((m.met σ).posDef c y hc).det_pos.ne'.isUnit
  have e2 : (fun v => ((VMetric.det Hm).φ σ).φ c (a.e.symm v)) =
      fun v => -Real.log ((m.met σ).G c (a.e.symm v)).det.re := rfl
  change _ = ofValues (chernOne (fun w => (m.met σ).G c (a.e.symm w)) (a.e y))
  congr 1
  funext ξ η
  rw [chernOne_eq_neg_ddc_log_det hM hH hU, e2, leviForm_neg, ddc]
  simp

end GlobalTheory.LineForm.DdcLine

namespace GlobalTheory.LineForm.DdcLine

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}
variable (hX : IsRegVar p D) (σ : k →+* ℂ) {E : X.Modules} (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2)

theorem restrict_G_sub (a : VBExt.AdaptedChart (lineSC fl) 1 1) (y : CxPts p σ) :
    ((h.restrict (fl.isSubbundle 1) (fl.isVB 1)).met σ).G a.sub y = subGram ((h.met σ).gram a.frame y) := by
  ext i j
  simp only [VMetric.restrict, Met.restrict, Met.gram, subGram, Matrix.toBlocks₁₁, Matrix.of_apply,
    VBExt.AdaptedChart.frame, VBExt.AdaptedChart.sub, Sum.elim_inl]

theorem quot_G_line (a : VBExt.AdaptedChart (lineSC fl) 1 1) {y : CxPts p σ} (hy : y ∈ ptsIn p σ a.U) :
    ((VMetric.quot (S := lineSC fl) (r := 1) (s := 1) h (lineSC_shortExact fl) (fl.isVB 1) (fl.isVB_cokernel 1)).met σ).G
      a.quot y = quotGram ((h.met σ).gram a.frame y) :=
  Met.quot_G (S := lineSC fl) (r := 1) (s := 1) (h.met σ) (lineSC_shortExact fl) (fl.isVB 1) (fl.isVB_cokernel 1) a hy

theorem isometric_quot_line :
    (VMetric.det (VMetric.IsCInf.quot (S := lineSC fl) (r := 1) (s := 1) (lineSC_shortExact fl) (fl.isVB 1)
      (fl.isVB_cokernel 1) H)).Isometric
      (VMetric.det (VMetric.IsCInf.quot (S := .mk _ _ (line_lineQuot fl)) (r := 1) (s := 1) (shortExact_lineQuot fl)
        (fl.isVB 1) (fl.isVB_gr 1) H)) :=
  (isometric_detQuot_and_bcInt_eq_of_iso k X p (lineSC fl) (.mk _ _ (line_lineQuot fl)) 1 1 h h H H
    (lineSC_shortExact fl) (shortExact_lineQuot fl) (fl.isVB 1) (fl.isVB_cokernel 1) (fl.isVB 1) (fl.isVB_gr 1)
    (Iso.refl _) (Iso.refl _) (by simp) (fun σ V s t y hy => by simp)).1

theorem c1F_grLB_zero_eq_chernOne_subGram (x : (hX.atlas σ).Pt) : c1F hX σ (VMetric.grLB fl 0 H) x =
    ofValues (chernOne (fun w => subGram ((h.met σ).gram (frameAt fl x.pt).frame (x.ch.symm w))) x.crd) := by
  have e₁ : c1F hX σ (VMetric.grLB fl 0 H) x =
      c1F hX σ (VMetric.det (H.restrict (fl.isSubbundle 1) (fl.isVB 1))) x := by
    rw [c1F_eq_of_isometric k X p D hX σ _ _ (isometric_grLB_zero H fl)]
  have e₂ : c1F hX σ (VMetric.det (H.restrict (fl.isSubbundle 1) (fl.isVB 1))) x =
      ofValues (chernOne (fun w => ((h.restrict (fl.isSubbundle 1) (fl.isVB 1)).met σ).G (frameAt fl x.pt).sub
        (x.ch.symm w)) x.crd) :=
    c1F_det_metric_eq_chernOne hX σ _ x (frameAt fl x.pt).sub (mem_frameAt fl x.pt)
  have e₃ : (fun w => ((h.restrict (fl.isSubbundle 1) (fl.isVB 1)).met σ).G (frameAt fl x.pt).sub (x.ch.symm w)) =
      fun w => subGram ((h.met σ).gram (frameAt fl x.pt).frame (x.ch.symm w)) :=
    funext fun w => restrict_G_sub σ h fl _ _
  rw [e₁, e₂, e₃]

theorem c1F_grLB_one_eq_chernOne_quotGram (x : (hX.atlas σ).Pt) : c1F hX σ (VMetric.grLB fl 1 H) x =
    ofValues (chernOne (fun w => quotGram ((h.met σ).gram (frameAt fl x.pt).frame (x.ch.symm w))) x.crd) := by
  have e₁ : c1F hX σ (VMetric.grLB fl 1 H) x = c1F hX σ (VMetric.det (VMetric.IsCInf.quot (S := lineSC fl) (r := 1)
      (s := 1) (lineSC_shortExact fl) (fl.isVB 1) (fl.isVB_cokernel 1) H)) x := by
    rw [c1F_eq_of_isometric k X p D hX σ _ _ (isometric_quot_line h H fl),
      c1F_eq_of_isometric k X p D hX σ _ _ (isometric_grLB_one H fl)]
  have e₂ : c1F hX σ (VMetric.det (VMetric.IsCInf.quot (S := lineSC fl) (r := 1) (s := 1) (lineSC_shortExact fl)
      (fl.isVB 1) (fl.isVB_cokernel 1) H)) x =
      ofValues (chernOne (fun w => ((VMetric.quot (S := lineSC fl) (r := 1) (s := 1) h (lineSC_shortExact fl) (fl.isVB 1)
        (fl.isVB_cokernel 1)).met σ).G (frameAt fl x.pt).quot (x.ch.symm w)) x.crd) :=
    c1F_det_metric_eq_chernOne hX σ (m := VMetric.quot (S := lineSC fl) (r := 1) (s := 1) h (lineSC_shortExact fl) (fl.isVB 1)
      (fl.isVB_cokernel 1)) (VMetric.IsCInf.quot (S := lineSC fl) (r := 1) (s := 1) (lineSC_shortExact fl) (fl.isVB 1)
      (fl.isVB_cokernel 1) H) x (frameAt fl x.pt).quot (mem_frameAt fl x.pt)
  have he : (fun w => ((VMetric.quot (S := lineSC fl) (r := 1) (s := 1) h (lineSC_shortExact fl) (fl.isVB 1)
      (fl.isVB_cokernel 1)).met σ).G (frameAt fl x.pt).quot (x.ch.symm w)) =ᶠ[𝓝 x.crd]
      (fun w => quotGram ((h.met σ).gram (frameAt fl x.pt).frame (x.ch.symm w))) := by
    filter_upwards [(isOpen_chartSet (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1).mem_nhds (crd_mem hX σ h H fl x)]
      with v hv
    have hv2 : x.ch.symm v ∈ ptsIn p σ (frameAt fl x.pt).U := hv.2
    exact quot_G_line σ h fl (frameAt fl x.pt) hv2
  have e₃ : chernOne (fun w => ((VMetric.quot (S := lineSC fl) (r := 1) (s := 1) h (lineSC_shortExact fl) (fl.isVB 1)
      (fl.isVB_cokernel 1)).met σ).G (frameAt fl x.pt).quot (x.ch.symm w)) x.crd =
      chernOne (fun w => quotGram ((h.met σ).gram (frameAt fl x.pt).frame (x.ch.symm w))) x.crd := by
    funext ξ η
    simp only [chernOne]
    rw [curv_congr he]
  rw [e₁, e₂, e₃]

theorem ofValuesTwo_sub {n : ℕ} (Ψ Φ : V n → V n → V n → V n → ℂ) :
    ofValuesTwo (fun a b c d => Ψ a b c d - Φ a b c d) = ofValuesTwo Ψ - ofValuesTwo Φ := by
  simp only [ofValuesTwo, sub_smul, Finset.sum_sub_distrib, smul_sub]

theorem ddc_omF : (hX.atlas σ).ddc (fld _ (omF hX σ h fl)) =
    fld _ (c2F hX σ h fl - c1F hX σ (VMetric.grLB fl 0 H) * c1F hX σ (VMetric.grLB fl 1 H)) := by
  funext x
  have hmem := crd_mem hX σ h H fl x
  have hpos := isPosFrame_midIn (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1
  rw [GlobalTheory.T.ddc_eq_of_local_eq _ _ x _ (loc_omF hX σ h H fl x), GlobalTheory.T.ddc_ofValues_eq _ _ (fun a b =>
    ((GlobalTheory.T.contDiffOn_extTrace_of_isPosFrame hpos _ _).contDiffAt (hpos.1.mem_nhds hmem)).of_le (WithTop.coe_le_coe.2 le_top))]
  have hc := (((GlobalTheory.SubQuotCurv.subQuotCurvature _ (Fin 1) (Fin 1) _ _).2 hpos).2.2.2 (by simp) (by simp) _ hmem).2.2.2
  have hd : ddcForm (extTrace (midIn (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1)) x.crd = fun ξ₁ η₁ ξ₂ η₂ =>
      chernTwo (midIn (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1) x.crd ξ₁ η₁ ξ₂ η₂ -
        wedge (chernOne (GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms.gramS (midIn (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1)) x.crd)
          (chernOne (GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms.gramQ (midIn (hseq hX σ h H fl) (frameAt fl x.pt) x.1.1)) x.crd) ξ₁ η₁ ξ₂ η₂ := by
    funext ξ₁ η₁ ξ₂ η₂; exact hc ξ₁ η₁ ξ₂ η₂
  rw [hd, ofValuesTwo_sub, ← GlobalTheory.T.chernAt_two_eq_ofValuesTwo_chernTwo, ← GlobalTheory.T.ofValues_mul_ofValues']
  simp only [fld, Pi.sub_apply, Pi.mul_apply, c1F_grLB_zero_eq_chernOne_subGram hX σ h H fl x, c1F_grLB_one_eq_chernOne_quotGram hX σ h H fl x]
  rfl

end GlobalTheory.LineForm.DdcLine

theorem GlobalTheory.LineForm.ddc_omF_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2), (hX.atlas σ).ddc (fld _ (omF hX σ h fl)) =
      fld _ (c2F hX σ h fl - c1F hX σ (VMetric.grLB fl 0 H) * c1F hX σ (VMetric.grLB fl 1 H)) :=
  fun _ _ _ _ _ _ hX σ _ h H fl => GlobalTheory.LineForm.DdcLine.ddc_omF hX σ h H fl
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ddc_omega_form_eq_c2_sub_c1_product : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2), (hX.atlas σ).ddc (fld _ (omF hX σ h fl)) = fld _ (c2F hX σ h fl - c1F hX σ (VMetric.grLB fl 0 H) * c1F hX σ (VMetric.grLB fl 1 H)) := by
  atlas_forward_decl GlobalTheory.LineForm.ddc_omF_eq
end
