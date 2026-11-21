import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralPullFourth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSubOfIsFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDelDbarZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarSumLeibniz
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityPullbackEqNormSqDetMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMeasUnivNeTopOfCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcEqOfLocalEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoFlagRationalSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernIsometricEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLinearLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineLimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralPullThird

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineForm

theorem mul_sub_mul_of_add_eq {R : Type} [CommRing R] {a b c e : R} (h : a + b = c + e) :
    c * e - a * b = (e - a) * (c - a) := by
  linear_combination (-a) * h

section Calc

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem ddc_sub_of_isForm (α β : A.Fld) (hα : A.IsForm α) (hβ : A.IsForm β) :
    A.IsForm (α - β) ∧ A.ddc (α - β) = A.ddc α - A.ddc β := by
  have C := (GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.1
  have e : α - β = α + (-1 : ℂ) • β := by rw [neg_one_smul, sub_eq_add_neg]
  have hβ' : A.IsForm ((-1 : ℂ) • β) := (C (-1) β β hβ hβ).2.2.1
  have hdα : A.IsForm (A.dbar α) := (C 0 α α hα hα).2.2.2.2.1
  have hdβ : A.IsForm (A.dbar β) := (C 0 β β hβ hβ).2.2.2.2.1
  have hdβ' : A.IsForm ((-1 : ℂ) • A.dbar β) := (C (-1) _ _ hdβ hdβ).2.2.1
  refine ⟨e ▸ (C 0 α _ hα hβ').1, ?_⟩
  rw [e, HolAtlas.ddc, HolAtlas.ddc, HolAtlas.ddc, (C 0 α _ hα hβ').2.2.2.2.2.2.1, (C (-1) β β hβ hβ).2.2.2.2.2.2.2.2,
    (C 0 _ _ hdα hdβ').2.2.2.2.2.1, (C (-1) _ _ hdβ hdβ).2.2.2.2.2.2.2.1, smul_add, smul_comm GlobalTheory.HermFrame.kappa (-1 : ℂ),
    neg_one_smul, sub_eq_add_neg]

theorem ddc_pullback {M' : Type} [TopologicalSpace M'] {n' : ℕ} (A' : HolAtlas M' n') (f : M' → M) (hf : A.IsHolo A' f)
    (α : A.Fld) (hα : A.IsForm α) : A'.ddc (A.pullback A' f α) = A.pullback A' f (A.ddc α) := by
  have C := (GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.1
  have P := ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.2.2.2 M' n' A' f hf).2
  have hdα : A.IsForm (A.dbar α) := (C 0 α α hα hα).2.2.2.2.1
  rw [HolAtlas.ddc, HolAtlas.ddc, ((P 0 α α).2.2.2 hα).2.2, ((P 0 (A.dbar α) (A.dbar α)).2.2.2 hdα).2.1,
    (P GlobalTheory.HermFrame.kappa (A.del (A.dbar α)) (A.del (A.dbar α))).2.2.1]

theorem fld_sub (f g : A.Pt → Ev n) : fld A (f - g) = fld A f - fld A g := by
  funext x; simp [fld]

theorem fld_mul (f g : A.Pt → Ev n) : fld A (f * g) = fld A f * fld A g := by
  funext x; simp [fld]

theorem pullback_sub {M' : Type} [TopologicalSpace M'] {n' : ℕ} (A' : HolAtlas M' n') (f : M' → M) (hf : A.IsHolo A' f)
    (α β : A.Fld) : A.pullback A' f (α - β) = A.pullback A' f α - A.pullback A' f β := by
  have P := ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.2.2.2 M' n' A' f hf).2
  rw [show α - β = α + (-1 : ℂ) • β by rw [neg_one_smul, sub_eq_add_neg], (P 0 α ((-1 : ℂ) • β)).1, (P (-1) β β).2.2.1,
    neg_one_smul, sub_eq_add_neg]

theorem pullback_mul {M' : Type} [TopologicalSpace M'] {n' : ℕ} (A' : HolAtlas M' n') (f : M' → M) (hf : A.IsHolo A' f)
    (α β : A.Fld) : A.pullback A' f (α * β) = A.pullback A' f α * A.pullback A' f β :=
  (((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.2.2.2 M' n' A' f hf).2 0 α β).2.1

end Calc

theorem ddc_omF_sub_pull : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    (hY.atlas σ).IsForm (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) - pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) ∧ (hY.atlas σ).ddc (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) - pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) = evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) ((X 4 - X 0) * (X 3 - X 0)) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl _ A σ
  have TY := GlobalTheory.T.firstChern_form_properties k Y p (d + 1) hY σ
  have TB := GlobalTheory.T.firstChern_form_properties k B q d hB σ
  obtain ⟨hHolo, hc1, hE⟩ := TB.2.2 Y p (d + 1) hY π w
  obtain ⟨hc2, hsum⟩ := hE E h H flB fl
  have cY := TY.2.1 _ (h.pull π w) (H.pull π w) fl fl
  have cB := TB.2.1 E h H flB flB
  have hpf : ∀ α, pullF hB hY σ π w α =
      (hB.atlas σ).pullback (hY.atlas σ) (GlobalTheory.Points.PtsOver.map π w _) α := fun _ => rfl
  have hωB : (hB.atlas σ).IsForm (fld (hB.atlas σ) (omF hB σ h flB)) := cB.1.1
  have hpω : (hY.atlas σ).IsForm (pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) := by
    rw [hpf]
    exact ((((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _ hHolo).2 0 (fld (hB.atlas σ) (omF hB σ h flB))
      (fld (hB.atlas σ) (omF hB σ h flB))).2.2.2 hωB).1
  obtain ⟨hF, hD⟩ := ddc_sub_of_isForm (hY.atlas σ) _ _ cY.1.1 hpω
  refine ⟨hF, ?_⟩
  rw [hD, hpf, ddc_pullback _ _ _ hHolo _ hωB, cY.2.2.2.2.2.2.2, cB.2.2.2.2.2.2.2, fld_sub (hB.atlas σ), fld_mul (hB.atlas σ),
    pullback_sub _ _ _ hHolo, pullback_mul _ _ _ hHolo, ← hpf, ← hpf, ← hpf, ← hc2, ← hc1, ← hc1]
  simp only [← fld_mul, ← fld_sub, evalF]
  congr 1
  funext x
  have hx := congrFun hsum x
  simp only [Pi.add_apply] at hx
  simp [fam5]
  exact mul_sub_mul_of_add_eq (R := Ev (d + 1)) hx

end GlobalTheory.LineForm

end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_hermitian_line_curvature : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    (hY.atlas σ).IsForm (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) - pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) ∧ (hY.atlas σ).ddc (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) - pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) = evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) ((X 4 - X 0) * (X 3 - X 0)) := by
  atlas_forward_decl GlobalTheory.LineForm.ddc_omF_sub_pull
end

section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_del_dbar_zero : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n),
    ∀ η : A.Fld, A.IsForm η → A.integral (A.del η) = 0 ∧ A.integral (A.dbar η) = 0 := by
  first | exact @GlobalTheory.CxFormStokesBoth.stokes | exact GlobalTheory.CxFormStokesBoth.stokes | (intros; apply GlobalTheory.CxFormStokesBoth.stokes <;> assumption)
end

section
set_option autoImplicit false

open MeasureTheory Filter
open GlobalTheory GlobalTheory.CxForm GlobalTheory.LineForm
open GlobalTheory.GoodMetric (coordVec)
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Topology

namespace GlobalTheory.CxForm.ByParts

section Point

variable {n : ℕ}

theorem delAt_fun (u : V n → ℂ) (x : V n) :
    delAt (fun y => algebraMap ℂ (Alt n) (u y)) x = ∑ a, del u x (coordVec a) • dz a := by
  simp only [delAt, Algebra.algebraMap_eq_smul_one, ← bas_empty]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [coefwise_smul (by simp), bas_empty, mul_smul_comm, mul_one]

theorem dbarAt_fun (u : V n → ℂ) (x : V n) :
    dbarAt (fun y => algebraMap ℂ (Alt n) (u y)) x = ∑ a, dbar u x (coordVec a) • dzb a := by
  simp only [dbarAt, Algebra.algebraMap_eq_smul_one, ← bas_empty]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [coefwise_smul (by simp), bas_empty, mul_smul_comm, mul_one]

theorem dzb_mul_dz (a b : Fin n) : dzb b * dz a = -(dz a * dzb b) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

theorem dbarAt_delAt_fun {u : V n → ℂ} {v : V n} (hu : ContDiffAt ℝ 2 u v) :
    dbarAt (delAt fun y => algebraMap ℂ (Alt n) (u y)) v = -delAt (dbarAt fun y => algebraMap ℂ (Alt n) (u y)) v := by
  have hconst := (delAt_dbarAt_linear_local n v).2.2.2.2
  have e₁ : (delAt fun y => algebraMap ℂ (Alt n) (u y)) = fun x => ∑ a, del u x (coordVec a) • dz a :=
    funext (delAt_fun u)
  have e₂ : (dbarAt fun y => algebraMap ℂ (Alt n) (u y)) = fun x => ∑ a, dbar u x (coordVec a) • dzb a :=
    funext (dbarAt_fun u)
  have hd (a : Fin n) : DifferentiableAt ℝ (fun x => del u x (coordVec a)) v := by
    have h1 : DifferentiableAt ℝ (del u) v :=
      (contDiffAt_del (m := 1) hu (by norm_num)).differentiableAt (by simp)
    exact ((ContinuousLinearMap.apply ℂ ℂ (coordVec a)).restrictScalars ℝ).differentiableAt.comp v h1
  rw [e₁, e₂, dbarAt_sum_smul (c := fun a x => del u x (coordVec a)) (F := fun a _ => dz a) hd
      (fun _ _ => differentiableAt_const _),
    DelForm.delAt_sum_smul (fun a x => dbar u x (coordVec a)) (fun a _ => dzb a)
      (fun a => differentiableAt_dbar_apply hu _) (fun _ _ => differentiableAt_const _)]
  simp only [(hconst _).1, (hconst _).2, smul_zero, add_zero, DelForm.dOne, Finset.sum_mul, smul_mul_assoc,
    ← ddbar_eq_dbar_del hu, ← ddbar_eq_del_dbar hu, dzb_mul_dz, smul_neg, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]

end Point

section Manifold

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem target_mem (x : A.Pt) : (A.e x.1.1).target ∈ 𝓝 x.crd :=
  (A.e x.1.1).open_target.mem_nhds (x.ch.map_source x.2)

theorem diff_coef {α : A.Fld} (h : A.IsForm α) (x : A.Pt) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun v => (bas n).repr (A.loc α x.1.1 v) S) x.crd :=
  ((h.smooth x.1.1 S).contDiffAt (target_mem A x)).differentiableAt (by simp)

theorem loc_mul (α β : A.Fld) (i : A.ι) : A.loc (α * β) i = fun v => A.loc α i v * A.loc β i v := by
  funext v
  unfold HolAtlas.loc
  split_ifs
  exacts [rfl, (mul_zero _).symm]

theorem loc_del_dbar (α : A.Fld) (i : A.ι) {v : V n} (hv : v ∈ (A.e i).target) :
    A.loc (A.del α) i v = delAt (A.loc α i) v ∧ A.loc (A.dbar α) i v = dbarAt (A.loc α i) v := by
  constructor <;> rw [HolAtlas.loc, dif_pos hv]
  · exact congrArg (delAt (A.loc α i)) ((A.e i).right_inv hv)
  · exact congrArg (dbarAt (A.loc α i)) ((A.e i).right_inv hv)

theorem loc_fn (g : M → ℝ) (i : A.ι) {v : V n} (hv : v ∈ (A.e i).target) :
    A.loc (A.fn g) i =ᶠ[𝓝 v] fun w => algebraMap ℂ (Alt n) (g ((A.e i).symm w) : ℂ) :=
  eventually_of_mem ((A.e i).open_target.mem_nhds hv) fun w hw => by
    rw [HolAtlas.loc, dif_pos hw]
    rfl

theorem dbar_del_fn {g : M → ℝ} (hg : A.SmoothOn Set.univ fun y => (g y : ℂ)) :
    A.dbar (A.del (A.fn g)) = -A.del (A.dbar (A.fn g)) := by
  funext x
  have hgerm := fun v => (delAt_dbarAt_linear_local n v).2.2.2.1
  have h₁ : A.loc (A.del (A.fn g)) x.1.1 =ᶠ[𝓝 x.crd]
      delAt fun w => algebraMap ℂ (Alt n) (g ((A.e x.1.1).symm w) : ℂ) :=
    eventually_of_mem (target_mem A x) fun v hv =>
      (loc_del_dbar A _ _ hv).1.trans (hgerm v _ _ (loc_fn A g _ hv)).1
  have h₂ : A.loc (A.dbar (A.fn g)) x.1.1 =ᶠ[𝓝 x.crd]
      dbarAt fun w => algebraMap ℂ (Alt n) (g ((A.e x.1.1).symm w) : ℂ) :=
    eventually_of_mem (target_mem A x) fun v hv =>
      (loc_del_dbar A _ _ hv).2.trans (hgerm v _ _ (loc_fn A g _ hv)).2
  have hu : ContDiffAt ℝ 2 (fun w => (g ((A.e x.1.1).symm w) : ℂ)) x.crd :=
    (((hg x.1.1).mono fun v hv => ⟨hv, trivial⟩).contDiffAt (target_mem A x)).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  rw [Pi.neg_apply, HolAtlas.dbar, HolAtlas.del, (hgerm _ _ _ h₁).2, (hgerm _ _ _ h₂).1]
  exact dbarAt_delAt_fun hu

theorem dbar_del_fn_mul {g : M → ℝ} {ψ : A.Fld} (hd : A.IsForm (A.del (A.fn g))) (hψ : A.IsForm ψ) :
    A.dbar (A.del (A.fn g) * ψ) = A.dbar (A.del (A.fn g)) * ψ - A.del (A.fn g) * A.dbar ψ := by
  funext x
  have key := (FormMul.leibniz_of_comm n (A.loc (A.del (A.fn g)) x.1.1) (A.loc ψ x.1.1) x.crd
    (-A.del (A.fn g) x) (diff_coef A hd x) (diff_coef A hψ x)).2 fun a => by
      rw [A.loc_crd, HolAtlas.del,
        ((delAt_dbarAt_linear_local n _).2.2.2.1 _ _ (loc_fn A g _ (x.ch.map_source x.2))).1, delAt_fun]
      simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, dzb_mul_dz, neg_mul, smul_neg,
        Finset.sum_neg_distrib]
  rw [A.loc_crd ψ x, neg_mul, ← sub_eq_add_neg] at key
  rw [HolAtlas.dbar, loc_mul]
  exact key

end Manifold

theorem integral_fn_mul_ddc : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (g : M → ℝ),
    A.SmoothOn Set.univ (fun y => (g y : ℂ)) → ∀ ψ : A.Fld, A.IsForm ψ →
      A.integral (A.fn g * A.ddc ψ) = A.integral (A.ddc (A.fn g) * ψ) := by
  intro M _ _ _ _ _ _ n A g hg ψ hψ
  obtain ⟨-, C, L, -⟩ := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A
  obtain ⟨hfin, hadd, -⟩ := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous M n A
  have S := GlobalTheory.T.integral_del_dbar_zero M n A
  have add : ∀ α β : A.Fld, A.IsForm α → A.IsForm β → A.integral (α + β) = A.integral α + A.integral β := by
    intro α β hα hβ
    simp only [← wInt_one]
    exact (hadd _ α β hα hβ (fun ε => have := hfin α hα ε; integrable_const _)
      (fun ε => have := hfin β hβ ε; integrable_const _)).2
  have fmul : ∀ {α β : A.Fld}, A.IsForm α → A.IsForm β → A.IsForm (α * β) := fun h h' => (C 0 _ _ h h').2.1
  have fsm : ∀ (c : ℂ) {α : A.Fld}, A.IsForm α → A.IsForm (c • α) := fun c _ h => (C c _ _ h h).2.2.1
  have fdel : ∀ {α : A.Fld}, A.IsForm α → A.IsForm (A.del α) := fun h => (C 0 _ _ h h).2.2.2.1
  have fdbar : ∀ {α : A.Fld}, A.IsForm α → A.IsForm (A.dbar α) := fun h => (C 0 _ _ h h).2.2.2.2.1
  have ha : A.IsForm (A.fn g) := A.isForm_fn hg
  have h₁ := fmul ha (fdbar hψ)
  have h₂ := fmul (fdel ha) hψ
  have e₁ : A.del (A.fn g * A.dbar ψ) = A.del (A.fn g) * A.dbar ψ + A.fn g * A.del (A.dbar ψ) :=
    (L (fun x => algebraMap ℂ (Ev n) (g x.pt)) (A.dbar ψ) ha (fdbar hψ)).1
  have e₂ := dbar_del_fn_mul A (fdel ha) hψ
  rw [dbar_del_fn A hg] at e₂
  have e : A.fn g * A.ddc ψ = A.ddc (A.fn g) * ψ + (A.del (HermFrame.kappa • (A.fn g * A.dbar ψ)) +
      A.dbar (HermFrame.kappa • (A.del (A.fn g) * ψ))) := by
    rw [(C _ _ _ h₁ h₁).2.2.2.2.2.2.2.1, (C _ _ _ h₂ h₂).2.2.2.2.2.2.2.2, e₁, e₂, HolAtlas.ddc, HolAtlas.ddc,
      mul_smul_comm, smul_mul_assoc, ← smul_add, ← smul_add, neg_mul]
    congr 1
    abel
  have k₁ := fsm HermFrame.kappa h₁
  have k₂ := fsm HermFrame.kappa h₂
  have k₀ : A.IsForm (A.ddc (A.fn g) * ψ) := fmul (fsm HermFrame.kappa (fdel (fdbar ha))) hψ
  rw [e, add _ _ k₀ (C 0 _ _ (fdel k₁) (fdbar k₂)).1, add _ _ (fdel k₁) (fdbar k₂),
    (S _ k₁).1, (S _ k₂).2, add_zero, add_zero]

end GlobalTheory.CxForm.ByParts
end

section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ddc_integration_by_parts : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (g : M → ℝ),
    A.SmoothOn Set.univ (fun y => (g y : ℂ)) → ∀ ψ : A.Fld, A.IsForm ψ → A.integral (A.fn g * A.ddc ψ) = A.integral (A.ddc (A.fn g) * ψ) := by
  first | exact @GlobalTheory.CxForm.ByParts.integral_fn_mul_ddc | exact GlobalTheory.CxForm.ByParts.integral_fn_mul_ddc | (intros; apply GlobalTheory.CxForm.ByParts.integral_fn_mul_ddc <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal
open GlobalTheory.CxForm GlobalTheory.ChartGlue

namespace GlobalTheory.LineForm.FnMul

section Chart

variable {M : Type} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] {n : ℕ}

theorem lintegral_chartMeas (e : OpenPartialHomeomorph M (V n)) {ρ f : M → ℝ≥0∞} (hf : Measurable f)
    (hρ : AEMeasurable (ρ ∘ e.symm) (volume.restrict e.target)) :
    ∫⁻ y, f y ∂chartMeas e ρ = ∫⁻ v in e.target, f (e.symm v) * ρ (e.symm v) := by
  have h0 : AEMeasurable e.symm (volume.restrict e.target) :=
    e.continuousOn_symm.aemeasurable e.open_target.measurableSet
  have h : AEMeasurable e.symm ((volume.restrict e.target).withDensity (ρ ∘ e.symm)) :=
    h0.mono_ac (withDensity_absolutelyContinuous _ _)
  rw [chartMeas, lintegral_map' hf.aemeasurable h,
    lintegral_withDensity_eq_lintegral_mul₀ hρ (g := fun v => f (e.symm v)) (hf.comp_aemeasurable h0)]
  exact lintegral_congr fun v => mul_comm _ _

theorem ofReal_mul_eq (a b : ℝ) : ENNReal.ofReal (a * b) =
    ENNReal.ofReal a * ENNReal.ofReal b + ENNReal.ofReal (-a) * ENNReal.ofReal (-b) := by
  rcases le_total 0 a with ha | ha
  · rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_of_nonpos (neg_nonpos.2 ha), zero_mul, add_zero]
  · rw [← neg_mul_neg, ENNReal.ofReal_mul (neg_nonneg.2 ha), ENNReal.ofReal_of_nonpos ha, zero_mul, zero_add]

variable [SecondCountableTopology M] (A : HolAtlas M n)

def glue (r : A.ι → V n → ℝ) : Measure M := glueMeas A.e fun i y => ENNReal.ofReal (r i (A.e i y))

theorem setLIntegral_glue {r : A.ι → V n → ℝ} (hr : ∀ i, ContinuousOn (r i) (A.e i).target)
    (hc : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      r i (A.e i y) = ‖transDet (A.e i) (A.e j) y‖ ^ 2 * r j (A.e j y))
    {f : M → ℝ≥0∞} (hf : Measurable f) (i : A.ι) {S : Set M} (hS : MeasurableSet S) (h : S ⊆ (A.e i).source) :
    ∫⁻ y in S, f y ∂glue A r =
      ∫⁻ v in (A.e i).target, S.indicator f ((A.e i).symm v) * ENNReal.ofReal (r i v) := by
  have h1 : (glue A r).restrict S = (chartMeas (A.e i) fun y => ENNReal.ofReal (r i (A.e i y))).restrict S :=
    (Measure.restrict_congr_meas hS).2 fun t ht htm =>
      glueMeas_apply A.e (fun i y => ENNReal.ofReal (r i (A.e i y))) A.holo (fun i j y hi hj => by
        rw [hc i j y hi hj, ENNReal.ofReal_mul (by positivity)]) i htm (ht.trans h)
  have h2 : ∀ᵐ v ∂volume.restrict (A.e i).target, ENNReal.ofReal (r i v) =
      ENNReal.ofReal (r i (A.e i ((A.e i).symm v))) :=
    (ae_restrict_iff' (A.e i).open_target.measurableSet).2 (.of_forall fun v hv => by rw [(A.e i).right_inv hv])
  rw [h1, ← lintegral_indicator hS, lintegral_chartMeas _ (ρ := fun y => ENNReal.ofReal (r i (A.e i y))) (hf.indicator hS)
    (((ENNReal.continuous_ofReal.comp_continuousOn (hr i)).aemeasurable
      (A.e i).open_target.measurableSet).congr h2)]
  refine lintegral_congr_ae ?_
  filter_upwards [h2] with v hv
  rw [hv]

theorem glue_mul {r : A.ι → V n → ℝ} (hr : ∀ i, ContinuousOn (r i) (A.e i).target)
    (hc : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      r i (A.e i y) = ‖transDet (A.e i) (A.e j) y‖ ^ 2 * r j (A.e j y))
    {g : M → ℝ} (hg : Continuous g) :
    glue A (fun i v => g ((A.e i).symm v) * r i v) =
      (glue A r).withDensity (fun y => ENNReal.ofReal (g y)) +
        (glue A fun i v => -r i v).withDensity fun y => ENNReal.ofReal (-g y) := by
  refine ext_of_cover (fun i => (A.e i).source) (fun i => (A.e i).open_source) A.cover fun i S hS h => ?_
  have m1 : Measurable fun y => ENNReal.ofReal (g y) := hg.measurable.ennreal_ofReal
  have m2 : Measurable fun y => ENNReal.ofReal (-g y) := hg.neg.measurable.ennreal_ofReal
  have h0 : AEMeasurable (A.e i).symm (volume.restrict (A.e i).target) :=
    (A.e i).continuousOn_symm.aemeasurable (A.e i).open_target.measurableSet
  have e0 := setLIntegral_glue A (r := fun i v => g ((A.e i).symm v) * r i v)
    (fun i => (hg.comp_continuousOn (A.e i).continuousOn_symm).mul (hr i))
    (fun i j y hi hj => by
      simp only [(A.e i).left_inv hi, (A.e j).left_inv hj, hc i j y hi hj]; ring)
    (f := fun _ => 1) measurable_const i hS h
  rw [setLIntegral_one] at e0
  rw [e0, Measure.add_apply, withDensity_apply _ hS, withDensity_apply _ hS,
    setLIntegral_glue A hr hc m1 i hS h,
    setLIntegral_glue A (r := fun i v => -r i v) (fun i => (hr i).neg)
      (fun i j y hi hj => by simp only [hc i j y hi hj]; ring) m2 i hS h,
    ← lintegral_add_left' (f := fun v => S.indicator (fun y => ENNReal.ofReal (g y)) ((A.e i).symm v) *
      ENNReal.ofReal (r i v)) (((m1.indicator hS).comp_aemeasurable h0).mul
      ((ENNReal.continuous_ofReal.comp_continuousOn (hr i)).aemeasurable (A.e i).open_target.measurableSet))]
  refine lintegral_congr fun v => ?_
  by_cases hv : (A.e i).symm v ∈ S
  · simp only [Function.comp_apply, indicator_of_mem hv, one_mul, ofReal_mul_eq]
  · simp only [Function.comp_apply, indicator_of_notMem hv, zero_mul, add_zero]

end Chart

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem dens_loc_fn_mul (g : M → ℝ) (ψ : A.Fld) (i : A.ι) (v : V n) :
    (dens (A.loc (A.fn g * ψ) i v)).re = g ((A.e i).symm v) * (dens (A.loc ψ i v)).re := by
  have key : ∀ x : A.Pt, (dens ((A.fn g * ψ) x)).re = g x.pt * (dens (ψ x)).re := fun x => by
    rw [Pi.mul_apply, HolAtlas.fn, ← Algebra.smul_def, ← Complex.re_ofReal_mul]
    simp only [dens, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_div_assoc]
  unfold HolAtlas.loc
  split_ifs with h
  · exact key _
  · simp [dens]

theorem dens_compat {ψ : A.Fld} (hψ : A.IsForm ψ) (i j : A.ι) (y : M) (hi : y ∈ (A.e i).source)
    (hj : y ∈ (A.e j).source) :
    (dens (A.loc ψ i (A.e i y))).re = ‖transDet (A.e i) (A.e j) y‖ ^ 2 * (dens (A.loc ψ j (A.e j y))).re := by
  have h1 := A.loc_crd ψ (⟨(i, y), hi⟩ : A.Pt)
  have h2 := A.loc_crd ψ (⟨(j, y), hj⟩ : A.Pt)
  have h3 := hψ.compat (⟨(i, y), hi⟩ : A.Pt) ⟨(j, y), hj⟩ rfl
  erw [h1, h2, h3, dens_pull]
  rw [Complex.re_ofReal_mul]
  rfl

end GlobalTheory.LineForm.FnMul

namespace GlobalTheory.LineForm

open GlobalTheory.LineForm.FnMul

theorem integral_fn_mul : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (g : M → ℝ),
    Continuous g → ∀ ψ : A.Fld, A.IsForm ψ → A.integral (A.fn g * ψ) = wInt A g ψ := by
  intro M _ _ _ _ _ _ n A g hg ψ hψ
  set r : A.ι → V n → ℝ := fun i v => (dens (A.loc ψ i v)).re with hr
  have rc : ∀ i, ContinuousOn (r i) (A.e i).target := fun i =>
    Complex.continuous_re.comp_continuousOn ((hψ.smooth i Finset.univ).continuousOn.div_const _)
  have rt := dens_compat A hψ
  have nc : ∀ i, ContinuousOn (fun v => -r i v) (A.e i).target := fun i => (rc i).neg
  have nt : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      -r i (A.e i y) = ‖transDet (A.e i) (A.e j) y‖ ^ 2 * -r j (A.e j y) := fun i j y hi hj => by
    simp only [hr, rt i j y hi hj]; ring
  have p1 : A.part ψ 1 = glue A r := by simp [HolAtlas.part, glue, hr]
  have p2 : A.part ψ (-1) = glue A fun i v => -r i v := by simp [HolAtlas.part, glue, hr]
  have q1 : A.part (A.fn g * ψ) 1 = glue A fun i v => g ((A.e i).symm v) * r i v := by
    simp [HolAtlas.part, glue, hr, dens_loc_fn_mul]
  have q2 : A.part (A.fn g * ψ) (-1) = glue A fun i v => g ((A.e i).symm v) * -r i v := by
    simp [HolAtlas.part, glue, hr, dens_loc_fn_mul]
  have f1 : IsFiniteMeasure (glue A r) :=
    ⟨lt_top_iff_ne_top.2 (glueMeas_univ_ne_top_of_compact A.e A.cover A.holo r rc rt)⟩
  have f2 : IsFiniteMeasure (glue A fun i v => -r i v) :=
    ⟨lt_top_iff_ne_top.2 (glueMeas_univ_ne_top_of_compact A.e A.cover A.holo (fun i v => -r i v) nc nt)⟩
  have i1 : Integrable g (glue A r) := hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  have i2 : Integrable g (glue A fun i v => -r i v) :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  rw [glue_mul A rc rt hg] at q1
  rw [glue_mul A (r := fun i v => -r i v) nc nt hg] at q2
  simp only [neg_neg] at q2
  rw [wInt, HolAtlas.integral, q1, q2, p1, p2, integral_eq_lintegral_pos_part_sub_lintegral_neg_part i1,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part i2]
  simp only [Measure.real, Measure.add_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have j1 : ∫⁻ y, ENNReal.ofReal (-g y) ∂glue A r ≠ ∞ := i1.neg.lintegral_lt_top.ne
  have j2 : ∫⁻ y, ENNReal.ofReal (-g y) ∂glue A (fun i v => -r i v) ≠ ∞ := i2.neg.lintegral_lt_top.ne
  rw [ENNReal.toReal_add i1.lintegral_lt_top.ne j2, ENNReal.toReal_add i2.lintegral_lt_top.ne j1]
  ring

end GlobalTheory.LineForm
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_integral_of_continuous : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (g : M → ℝ),
    Continuous g → ∀ ψ : A.Fld, A.IsForm ψ → A.integral (A.fn g * ψ) = wInt A g ψ := by
  atlas_forward_decl GlobalTheory.LineForm.integral_fn_mul
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped ContDiff
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.ChainLog

theorem loc_fn_eventuallyEq {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) (u : M → ℝ) (x : A.Pt) :
    A.loc (A.fn u) x.1.1 =ᶠ[𝓝 x.crd] fun v => algebraMap ℂ (Alt n) ((u ((A.e x.1.1).symm v) : ℝ) : ℂ) := by
  filter_upwards [(A.e x.1.1).open_target.mem_nhds ((A.e x.1.1).map_source x.2)] with v hv
  rw [HolAtlas.loc, dif_pos hv]
  rfl

theorem delAt_fun {n : ℕ} (g : V n → ℂ) (v : V n) :
    delAt (fun x => algebraMap ℂ (Alt n) (g x)) v = ∑ a, GlobalTheory.del g v (GlobalTheory.GoodMetric.coordVec a) • dz a := by
  simp only [delAt, Algebra.algebraMap_eq_smul_one, ← bas_empty]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coefwise_smul (by simp), bas_empty, mul_smul_comm, mul_one]

theorem dbarAt_fun {n : ℕ} (g : V n → ℂ) (v : V n) :
    dbarAt (fun x => algebraMap ℂ (Alt n) (g x)) v = ∑ b, GlobalTheory.dbar g v (GlobalTheory.GoodMetric.coordVec b) • dzb b := by
  simp only [dbarAt, Algebra.algebraMap_eq_smul_one, ← bas_empty]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coefwise_smul (by simp), bas_empty, mul_smul_comm, mul_one]

end GlobalTheory.ChainLog

namespace GlobalTheory.ChainLog

theorem ddc_fn_log_add : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (f : M → ℝ), A.SmoothOn Set.univ (fun y => (f y : ℂ)) → (∀ y, 0 ≤ f y) →
    ∀ t : ℝ, 0 < t → A.ddc (A.fn (fun y => Real.log (f y + t))) =
      A.fn (fun y => 1 / (f y + t)) * A.ddc (A.fn f) - A.fn (fun y => 1 / (f y + t) ^ 2) * (GlobalTheory.HermFrame.kappa • (A.del (A.fn f) * A.dbar (A.fn f))) := by
  intro M _ n A f hf hf0 t ht
  funext x
  set e := A.e x.1.1 with he
  set v0 := x.crd with hv0
  set w : V n → ℝ := fun v => f (e.symm v) with hwdef
  have hpt : e.symm v0 = x.pt := e.left_inv x.2
  have hw0 : w v0 = f x.pt := by simp only [hwdef, hpt]
  have hnhds : e.target ∈ 𝓝 v0 := e.open_target.mem_nhds (e.map_source x.2)
  have hwS : ContDiffAt ℝ ∞ w v0 := by
    have h1 := Complex.reCLM.contDiff.comp_contDiffOn (hf x.1.1)
    have h2 : ContDiffOn ℝ ∞ w e.target :=
      (h1.mono fun v hv => ⟨hv, trivial⟩).congr fun v _ => by simp [hwdef, he]
    exact h2.contDiffAt hnhds
  have hw : ContDiffAt ℝ 2 w v0 := hwS.of_le (WithTop.coe_le_coe.2 le_top)
  have hne : w v0 + t ≠ 0 := by rw [hw0]; linarith [hf0 x.pt]
  have hh : ContDiffAt ℝ 2 (fun s : ℝ => Real.log (s + t)) (w v0) :=
    (contDiffAt_id.add contDiffAt_const).log hne
  have hlw : ContDiffAt ℝ 2 (fun v => Real.log (w v + t)) v0 := hh.comp v0 hw
  have hL : ∀ p q, GlobalTheory.leviForm (fun v => Real.log (w v + t)) v0 p q =
      ((deriv (fun s : ℝ => Real.log (s + t)) (w v0) : ℝ) : ℂ) * GlobalTheory.leviForm w v0 p q
        + ((deriv (deriv (fun s : ℝ => Real.log (s + t))) (w v0) : ℝ) : ℂ) *
          (GlobalTheory.del (fun v => (w v : ℂ)) v0 p * GlobalTheory.dbar (fun v => (w v : ℂ)) v0 q) :=
    fun p q => GlobalTheory.leviForm_real_comp hh hw p q
  rw [GlobalTheory.deriv_deriv_log_add_const, GlobalTheory.deriv_log_add_const] at hL
  have hddc : ∀ u : M → ℝ, A.ddc (A.fn u) x = GlobalTheory.HermFrame.kappa • delAt (dbarAt fun v => algebraMap ℂ (Alt n) ((u (e.symm v) : ℝ) : ℂ)) v0 :=
    fun u => GlobalTheory.SecForm.DdcGerm.ddc_eq_of_eventuallyEq A _ x _ (loc_fn_eventuallyEq A u x)
  have hdel : A.del (A.fn f) x = ∑ a, GlobalTheory.del (fun v => (w v : ℂ)) v0 (GlobalTheory.GoodMetric.coordVec a) • dz a := by
    change delAt (A.loc (A.fn f) x.1.1) x.crd = _
    rw [GlobalTheory.SecForm.DdcGerm.delAt_germ (loc_fn_eventuallyEq A f x), delAt_fun]
  have hdbar : A.dbar (A.fn f) x = ∑ b, GlobalTheory.dbar (fun v => (w v : ℂ)) v0 (GlobalTheory.GoodMetric.coordVec b) • dzb b := by
    change dbarAt (A.loc (A.fn f) x.1.1) x.crd = _
    rw [GlobalTheory.SecForm.DdcGerm.dbarAt_germ (loc_fn_eventuallyEq A f x), dbarAt_fun]
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.smul_apply]
  rw [hddc, hddc, hdel, hdbar]
  rw [show (fun v => algebraMap ℂ (Alt n) (((fun y => Real.log (f y + t)) (e.symm v) : ℝ) : ℂ))
      = fun v => algebraMap ℂ (Alt n) ((Real.log (w v + t) : ℝ) : ℂ) from rfl,
    delAt_dbarAt_fun hlw, show (fun v => algebraMap ℂ (Alt n) ((f (e.symm v) : ℝ) : ℂ))
      = fun v => algebraMap ℂ (Alt n) ((w v : ℝ) : ℂ) from rfl, delAt_dbarAt_fun hw]
  simp only [HolAtlas.fn, ← hpt, ← Algebra.smul_def, ofValues, GlobalTheory.HermFrame.ddc, hL, AddSubmonoidClass.coe_finset_sum,
    Subalgebra.coe_smul, sym, Finset.sum_mul_sum, smul_mul_smul_comm, Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib,
    ← sub_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  simp only [hwdef]
  push_cast
  ring

end GlobalTheory.ChainLog
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ddc_log_plus_constant : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (f : M → ℝ), A.SmoothOn Set.univ (fun y => (f y : ℂ)) → (∀ y, 0 ≤ f y) →
    ∀ t : ℝ, 0 < t → A.ddc (A.fn (fun y => Real.log (f y + t))) =
      A.fn (fun y => 1 / (f y + t)) * A.ddc (A.fn f) - A.fn (fun y => 1 / (f y + t) ^ 2) * (GlobalTheory.HermFrame.kappa • (A.del (A.fn f) * A.dbar (A.fn f))) := by
  atlas_forward_decl GlobalTheory.ChainLog.ddc_fn_log_add
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.SmoothComp

theorem smooth_comp : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (f : M → ℝ) (s : Set ℝ) (G : ℝ → ℝ), Continuous f → A.SmoothOn Set.univ (fun y => (f y : ℂ)) →
    IsOpen s → (∀ y, f y ∈ s) → ContDiffOn ℝ (⊤ : ℕ∞) G s →
      Continuous (fun y => G (f y)) ∧ A.SmoothOn Set.univ (fun y => (G (f y) : ℂ)) ∧ A.IsForm (A.fn (fun y => G (f y))) := by
  intro M _ n A f s G hf hfs hs hfs' hG
  have hcont : Continuous (fun y => G (f y)) :=
    hG.continuousOn.comp_continuous hf hfs'
  have hsm : A.SmoothOn Set.univ (fun y => (G (f y) : ℂ)) := by
    intro i
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ (A.e i).symm) ((A.e i).target ∩ (A.e i).symm ⁻¹' Set.univ) := by
      have := (Complex.reCLM.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).comp_contDiffOn (hfs i)
      refine this.congr fun v _ => ?_
      simp
    have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G ∘ (f ∘ (A.e i).symm)) ((A.e i).target ∩ (A.e i).symm ⁻¹' Set.univ) :=
      hG.comp h1 fun v _ => hfs' _
    have h3 := (Complex.ofRealCLM.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).comp_contDiffOn h2
    refine h3.congr fun v _ => ?_
    simp
  exact ⟨hcont, hsm, A.isForm_fn hsm⟩

end GlobalTheory.SmoothComp
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_composition_form : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (f : M → ℝ) (s : Set ℝ) (G : ℝ → ℝ), Continuous f → A.SmoothOn Set.univ (fun y => (f y : ℂ)) →
    IsOpen s → (∀ y, f y ∈ s) → ContDiffOn ℝ (⊤ : ℕ∞) G s →
      Continuous (fun y => G (f y)) ∧ A.SmoothOn Set.univ (fun y => (G (f y) : ℂ)) ∧ A.IsForm (A.fn (fun y => G (f y))) := by
  atlas_forward_decl GlobalTheory.SmoothComp.smooth_comp
end

section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_hermitian_line_integral : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    (∀ y, 0 ≤ v y ∧ v y ≤ 1) ∧ Continuous v ∧ (hY.atlas σ).SmoothOn Set.univ (fun y => (v y : ℂ)) := by
  first | exact @GlobalTheory.CosSqSmooth.cosSq_smooth | exact GlobalTheory.CosSqSmooth.cosSq_smooth | (intros; apply GlobalTheory.CosSqSmooth.cosSq_smooth <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocalLelong

open Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.HermFrame (kappa)

section Point

variable {n : ℕ}

theorem del_mul_dbar {F φ₁ φ₀ : V n → ℝ} {g : V n → ℂ} {z : V n} (hg : ContDiffAt ℂ 2 g z)
    (h₁ : ContDiffAt ℝ 2 φ₁ z) (h₀ : ContDiffAt ℝ 2 φ₀ z)
    (e : F =ᶠ[𝓝 z] fun u => ‖g u‖ ^ 2 * Real.exp (-(φ₁ u - φ₀ u))) :
    ContDiffAt ℝ 2 F z ∧ ∀ ξ η : V n, del (fun u => (F u : ℂ)) z ξ * dbar (fun u => (F u : ℂ)) z η =
      F z * (leviForm F z ξ η + F z * (leviForm φ₁ z ξ η - leviForm φ₀ z ξ η)) := by
  have hn : ContDiffAt ℝ 2 (fun u => ‖g u‖ ^ 2) z := (hg.restrict_scalars ℝ).norm_sq ℂ
  have hF : ContDiffAt ℝ 2 F z := (hn.mul (h₁.sub h₀).neg.exp).congr_of_eventuallyEq e
  refine ⟨hF, fun ξ η => ?_⟩
  by_cases h : g z = 0
  · have hz : F z = 0 := by rw [e.self_of_nhds]; simp [h]
    have hm : IsLocalMin F z := e.mono fun u hu => by rw [hz, hu]; positivity
    have hd := hF.differentiableAt two_ne_zero
    rw [hz, del_apply, fderiv_ofReal_apply hd, fderiv_ofReal_apply hd, hm.fderiv_eq_zero]
    simp
  · have hz : F z ≠ 0 := by rw [e.self_of_nhds]; positivity
    have hl : ContDiffAt ℝ 2 (fun u => Real.log (‖g u‖ ^ 2)) z := hn.log (by simpa using h)
    have e₁ : (fun u => Real.log (F u)) =ᶠ[𝓝 z] fun u => Real.log (‖g u‖ ^ 2) - (φ₁ u - φ₀ u) := by
      filter_upwards [e, hg.continuousAt.eventually_ne h] with u hu hu'
      rw [hu, Real.log_mul (by positivity) (by positivity), Real.log_exp, sub_eq_add_neg _ (_ - _)]
    have e₂ := leviForm_real_comp (h := Real.log) (Real.contDiffAt_log.2 hz) hF ξ η
    rw [leviForm_congr e₁, leviForm_sub hl (h₁.sub h₀), leviForm_log_normSq_eq_zero hg h, leviForm_sub h₁ h₀,
      Real.deriv_log', deriv_inv] at e₂
    have hz' : (F z : ℂ) ≠ 0 := by exact_mod_cast hz
    simp only [zero_sub, ContinuousLinearMap.neg_apply, ContinuousLinearMap.sub_apply] at e₂
    push_cast at e₂
    field_simp at e₂
    linear_combination e₂

theorem delAt_fun (u : V n → ℂ) (v : V n) :
    delAt (fun x => algebraMap ℂ (Alt n) (u x)) v = ∑ a, del u v (coordVec a) • dz a := by
  simp only [delAt, Algebra.algebraMap_eq_smul_one, ← bas_empty]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coefwise_smul (by simp), bas_empty, mul_smul_comm, mul_one]

theorem dbarAt_fun (u : V n → ℂ) (v : V n) :
    dbarAt (fun x => algebraMap ℂ (Alt n) (u x)) v = ∑ a, dbar u v (coordVec a) • dzb a := by
  simp only [dbarAt, Algebra.algebraMap_eq_smul_one, ← bas_empty]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coefwise_smul (by simp), bas_empty, mul_smul_comm, mul_one]

theorem coe_ofValues (α : V n → V n → ℂ) :
    (ofValues α : Alt n) = ∑ a, ∑ b, α (coordVec a) (coordVec b) • (dz a * dzb b) := by
  simp only [ofValues, AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, sym]

theorem delAt_mul_dbarAt {F φ₁ φ₀ : V n → ℝ} {g : V n → ℂ} {z : V n} (hg : ContDiffAt ℂ 2 g z)
    (h₁ : ContDiffAt ℝ 2 φ₁ z) (h₀ : ContDiffAt ℝ 2 φ₀ z)
    (e : F =ᶠ[𝓝 z] fun u => ‖g u‖ ^ 2 * Real.exp (-(φ₁ u - φ₀ u))) :
    kappa • (delAt (fun x => algebraMap ℂ (Alt n) (F x)) z * dbarAt (fun x => algebraMap ℂ (Alt n) (F x)) z) =
      algebraMap ℂ (Alt n) (F z) * (kappa • delAt (dbarAt fun x => algebraMap ℂ (Alt n) (F x)) z +
        algebraMap ℂ (Alt n) (F z) * ((ofValues (HermFrame.ddc φ₁ z) : Alt n) - ofValues (HermFrame.ddc φ₀ z))) := by
  obtain ⟨hF, key⟩ := del_mul_dbar hg h₁ h₀ e
  rw [delAt_dbarAt_fun hF, delAt_fun, dbarAt_fun, ← Algebra.smul_def, ← Algebra.smul_def, Finset.sum_mul_sum]
  simp only [coe_ofValues, smul_mul_smul_comm, key, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    Finset.smul_sum, smul_smul, ← sub_smul, ← add_smul, HermFrame.ddc]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  ring

end Point

theorem del_mul_dbar_fn {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) (f : M → ℝ) (x : A.Pt)
    {φ₁ φ₀ : V n → ℝ} {g : V n → ℂ} (hg : ContDiffAt ℂ 2 g x.crd)
    (h₁ : ContDiffAt ℝ 2 φ₁ x.crd) (h₀ : ContDiffAt ℝ 2 φ₀ x.crd)
    (e : (fun u => f (x.ch.symm u)) =ᶠ[𝓝 x.crd] fun u => ‖g u‖ ^ 2 * Real.exp (-(φ₁ u - φ₀ u))) :
    kappa • (A.del (A.fn f) x * A.dbar (A.fn f) x) = A.fn f x * (A.ddc (A.fn f) x +
      A.fn f x * ((ofValues (HermFrame.ddc φ₁ x.crd) : Alt n) - ofValues (HermFrame.ddc φ₀ x.crd))) := by
  have hc : x.crd ∈ x.ch.target := x.ch.map_source x.2
  have l₁ (v) (hv : v ∈ x.ch.target) : A.loc (A.fn f) x.1.1 =ᶠ[𝓝 v]
      fun u => algebraMap ℂ (Alt n) (f (x.ch.symm u)) := by
    filter_upwards [x.ch.open_target.mem_nhds hv] with u hu
    rw [HolAtlas.loc, dif_pos hu]
    rfl
  have l₂ : A.loc (A.dbar (A.fn f)) x.1.1 =ᶠ[𝓝 x.crd] dbarAt fun u => algebraMap ℂ (Alt n) (f (x.ch.symm u)) := by
    filter_upwards [x.ch.open_target.mem_nhds hc] with u hu
    rw [HolAtlas.loc, dif_pos hu, ← ((delAt_dbarAt_linear_local n u).2.2.2.1 _ _ (l₁ u hu)).2]
    exact congrArg (dbarAt _) (x.ch.right_inv hu)
  have key := delAt_mul_dbarAt hg h₁ h₀ e
  rw [← ((delAt_dbarAt_linear_local n _).2.2.2.1 _ _ l₂).1, ← ((delAt_dbarAt_linear_local n _).2.2.2.1 _ _ (l₁ _ hc)).1,
    ← ((delAt_dbarAt_linear_local n _).2.2.2.1 _ _ (l₁ _ hc)).2, x.ch.left_inv x.2] at key
  exact key

section Lines

open GlobalTheory.VMetric GlobalTheory.CurveDens
open GlobalTheory.Twist (resM resM_resM)
open scoped ComplexOrder

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem isFrame_resM {F : X.Modules} (c : Chart F 1) {U : X.Opens} (h : U ≤ c.U) :
    IsFrame fun _ : Fin 1 => resM F h (c.e 0) := fun W hW => by
  convert c.isFrame W (hW.trans h) using 3
  funext i
  rw [resM_resM, Subsingleton.elim i 0]

theorem form_frame_eq_exp {F : X.Modules} (m : Met p σ F 1) (c : Chart F 1) {U : X.Opens} (h : U ≤ c.U) {y : CxPts p σ}
    (hy : y ∈ ptsIn p σ U) :
    (m.form (resM F h (c.e 0)) (resM F h (c.e 0)) y).re = Real.exp (-m.detWeight.φ c y) := by
  have hc := ptsIn_mono h hy
  have hp := (Complex.pos_iff.1 ((m.posDef c y hc).diag_pos (i := 0))).1
  rw [m.form_resM _ _ h hy, m.form_frame c hc]
  change _ = Real.exp (- -Real.log (m.G c y).det.re)
  rw [neg_neg, Matrix.det_fin_one, Real.exp_log hp]

theorem two_flags [IsIntegral X] {D : ℕ} (hX : IsRegVar p D) {W : X.Modules} {h : VMetric p W 2} (H : h.IsCInf)
    (fl fl' : Vert.Flag W 2) {v : CxPts p σ → ℝ} (hv : IsCosSq (h.met σ) (fl.ι 1) (fl'.ι 1) v) (x : (hX.atlas σ).Pt) :
    kappa • ((hX.atlas σ).del ((hX.atlas σ).fn fun y => 1 - v y) x * (hX.atlas σ).dbar ((hX.atlas σ).fn fun y => 1 - v y) x) =
      (hX.atlas σ).fn (fun y => 1 - v y) x * ((hX.atlas σ).ddc ((hX.atlas σ).fn fun y => 1 - v y) x +
        (hX.atlas σ).fn (fun y => 1 - v y) x *
          ((c1F hX σ (grLB fl' 1 H) x : Alt D) - c1F hX σ (grLB fl 0 H) x)) := by
  have hS := shortExact_lineQuot fl'
  have hL := fl'.isVB 1
  have hL' := fl.isVB 1
  have hQ := fl'.isVB_gr 1
  have hl := fl'.isSubbundle 1
  have hl' := fl.isSubbundle 1
  have HQ := IsCInf.quot (S := .mk _ _ (line_lineQuot fl')) (r := 1) (s := 1) hS hL hQ H
  rw [← c1F_eq_of_isometric k X p D hX σ _ _ (isometric_grLB_zero H fl),
    ← c1F_eq_of_isometric k X p D hX σ _ _ (isometric_grLB_one H fl')]
  obtain ⟨⟨c, y⟩, hy⟩ := x
  have hy' : y ∈ c.e.source := hy
  let a : Chart (fl'.F 1) 1 := hL.pick y
  let b : Chart (fl.F 1) 1 := hL'.pick y
  let e : Chart (fl'.gr 1) 1 := hQ.pick y
  let U : X.Opens := a.U ⊓ (b.U ⊓ e.U)
  have ha : U ≤ a.U := inf_le_left
  have hb : U ≤ b.U := inf_le_right.trans inf_le_left
  have he : U ≤ e.U := inf_le_right.trans inf_le_right
  have hU : y ∈ ptsIn p σ U := mem_ptsIn_inf.2 ⟨hL.mem_pick y, mem_ptsIn_inf.2 ⟨hL'.mem_pick y, hQ.mem_pick y⟩⟩
  obtain ⟨g, hg⟩ := exists_smul_frame e le_rfl he ((fl.ι 1 ≫ lineQuot fl').app U (resM _ hb (b.e 0)))
  rw [resM_resM] at hg
  have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) U)
  have hm := ChartGlue.mem_over c.e hy' hU
  have hf : ContDiffAt ℂ 2 (ev p σ _ g ∘ c.e.symm) (c.e y) :=
    (SCV.analyticAt_of_differentiableOn (c.holo _ g) (ho.mem_nhds hm)).contDiffAt
  refine del_mul_dbar_fn (hX.atlas σ) _ ⟨(c, y), hy⟩ hf
    (((VMetric.det HQ).cInf σ).contDiffAt c hy' (mem_pick _ y))
    (((VMetric.det (H.restrict hl' hL')).cInf σ).contDiffAt c hy' (mem_pick _ y)) ?_
  filter_upwards [ho.mem_nhds hm] with u hu
  have key := AdjFlag.div_eq_one_sub hS hL hQ hL' hl hl' (h.met σ) hv.symm (isFrame_resM a ha) (isFrame_resM b hb) hu.2
  rw [hg, form_smul_smul, Complex.mul_conj, Complex.re_ofReal_mul, form_frame_eq_exp _ _ _ hu.2,
    form_frame_eq_exp _ _ _ hu.2, Complex.normSq_eq_norm_sq, mul_div_assoc, ← Real.exp_sub] at key
  refine key.symm.trans (congrArg (_ * Real.exp ·) ?_)
  rw [neg_sub_neg, neg_sub]
  rfl

end Lines

theorem local_identity : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    GlobalTheory.HermFrame.kappa • ((hY.atlas σ).del ((hY.atlas σ).fn (fun y => 1 - v y)) * (hY.atlas σ).dbar ((hY.atlas σ).fn (fun y => 1 - v y))) = ((hY.atlas σ).fn (fun y => 1 - v y)) * ((hY.atlas σ).ddc ((hY.atlas σ).fn (fun y => 1 - v y)) + ((hY.atlas σ).fn (fun y => 1 - v y)) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 4 - X 0)) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl _ A σ v hv
  funext x
  have key := two_flags hY (H.pull π w) fl (flB.pull π) hv x
  rw [c1F_eq_of_isometric k Y p _ hY σ _ _ (VMetric.isometric_grLB_pull k B Y q p E 2 h H flB π w 1)] at key
  refine key.trans ?_
  simp only [Pi.mul_apply, Pi.add_apply, evalF, fld, map_sub, map_X, aeval_X, Subalgebra.coe_sub]
  rfl

end GlobalTheory.LocalLelong
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_hermitian_line_degree : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    GlobalTheory.HermFrame.kappa • ((hY.atlas σ).del ((hY.atlas σ).fn (fun y => 1 - v y)) * (hY.atlas σ).dbar ((hY.atlas σ).fn (fun y => 1 - v y))) = ((hY.atlas σ).fn (fun y => 1 - v y)) * ((hY.atlas σ).ddc ((hY.atlas σ).fn (fun y => 1 - v y)) + ((hY.atlas σ).fn (fun y => 1 - v y)) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 4 - X 0)) := by
  atlas_forward_decl GlobalTheory.LocalLelong.local_identity
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineNull

open GlobalTheory.CurveDens

theorem isCosSq_unique {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {V L L' : X.Modules} {r : ℕ}
    (h : Met p σ V r) {l : L ⟶ V} {l' : L' ⟶ V} (hL : IsVB L 1) (hL' : IsVB L' 1) (hl : IsSubbundle l)
    (hl' : IsSubbundle l') {v v' : CxPts p σ → ℝ} (hv : IsCosSq h l l' v) (hv' : IsCosSq h l l' v') : v = v' := by
  funext y
  obtain ⟨U, t, t', ht, ht', hU⟩ := AdjFlag.exists_frames hL hL' y
  have a := AdjFlag.form_frame_pos (h.restrict hl hL) ht hU
  have b := AdjFlag.form_frame_pos (h.restrict hl' hL') ht' hU
  rw [h.form_restrict hl hL t t hU] at a
  rw [h.form_restrict hl' hL' t' t' hU] at b
  have e := (hv U t t' y hU).symm.trans (hv' U t t' y hU)
  exact mul_right_cancel₀ a.ne' (mul_right_cancel₀ b.ne' e)

theorem part_cosSq_one : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ α : (hY.atlas σ).Fld, (hY.atlas σ).IsForm α → ∀ ε : ℤˣ, (hY.atlas σ).part α ε {y | v y = 1} = 0 := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv α _ ε
  obtain ⟨r, hr, -, h₂⟩ := exists_ratSec_fam5 k B Y q p d hB.toIsArithVar hY.toIsArithVar hB.regular π w E h H flB fl hfl A
  obtain ⟨v', hv', hlt⟩ := h₂ σ
  obtain rfl : v = v' := isCosSq_unique _ (fl.isVB 1) ((flB.pull π).isVB 1) (fl.isSubbundle 1)
    ((flB.pull π).isSubbundle 1) hv hv'
  generalize ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).div hr = D at hlt
  have hset : {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ (D.supp : Set Y)} = (offSupp p σ D)ᶜ := by
    ext y
    rw [Set.mem_compl_iff, offSupp, mem_ptsIn]
    exact not_not.symm
  have hA : MeasurableSet {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ (D.supp : Set Y)} := by
    rw [hset]
    exact (isOpen_ptsIn _).measurableSet.compl
  refine measure_mono_null (t := {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ (D.supp : Set Y)})
    (fun y hy => ?_) ?_
  · rw [hset]
    exact fun hm => (hlt y hm).1.ne hy
  · exact GlueCoverNull.glueMeas_null _ _ hA fun c =>
      ChernNull.chart_null hY.toIsArithVar D.supp.isClosed (CartierDiv.genericPoint_notMem_supp D) σ c

end GlobalTheory.LineNull
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_hermitian_line_height : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ α : (hY.atlas σ).Fld, (hY.atlas σ).IsForm α → ∀ ε : ℤˣ, (hY.atlas σ).part α ε {y | v y = 1} = 0 := by
  atlas_forward_decl GlobalTheory.LineNull.part_cosSq_one
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.LineForm.PLStep

section General

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem evalF_mul {ι : Type} (w : ι → A.Pt → Ev n) (P Q : MvPolynomial ι ℝ) :
    evalF A w (P * Q) = evalF A w P * evalF A w Q := by
  funext x
  simp only [evalF, fld, map_mul, Pi.mul_apply, Subalgebra.coe_mul]

theorem evalF_neg {ι : Type} (w : ι → A.Pt → Ev n) (P : MvPolynomial ι ℝ) :
    evalF A w (-P) = -evalF A w P := by
  funext x
  simp only [evalF, fld, map_neg, Pi.neg_apply, NegMemClass.coe_neg]

theorem evalF_comm {ι : Type} (w : ι → A.Pt → Ev n) (P : MvPolynomial ι ℝ) (ψ : A.Fld) :
    evalF A w P * ψ = ψ * evalF A w P := by
  funext x
  exact ((Subalgebra.mem_center_iff.1 (aeval (fun i => w i x) (P.map (algebraMap ℝ ℂ))).2) (ψ x)).symm

theorem wInt_div_two [MeasurableSpace M] (g : M → ℝ) (α : A.Fld) :
    wInt A (fun y => g y / 2) α = wInt A g α / 2 := by
  simp only [wInt, integral_div]; ring

theorem wInt_tendsto [MeasurableSpace M] (α : A.Fld) {G : ℝ → M → ℝ} {g b : M → ℝ} {l : Filter ℝ}
    [l.IsCountablyGenerated]
    (hm : ∀ᶠ t in l, ∀ ε : ℤˣ, AEStronglyMeasurable (G t) (A.part α ε))
    (hb : ∀ ε : ℤˣ, Integrable b (A.part α ε))
    (hbd : ∀ᶠ t in l, ∀ ε : ℤˣ, ∀ᵐ y ∂A.part α ε, ‖G t y‖ ≤ b y)
    (hl : ∀ ε : ℤˣ, ∀ᵐ y ∂A.part α ε, Tendsto (fun t => G t y) l (𝓝 (g y))) :
    Tendsto (fun t => wInt A (G t) α) l (𝓝 (wInt A g α)) := by
  have key : ∀ ε : ℤˣ, Tendsto (fun t => ∫ y, G t y ∂A.part α ε) l (𝓝 (∫ y, g y ∂A.part α ε)) := fun ε =>
    tendsto_integral_filter_of_dominated_convergence b (hm.mono fun t ht => ht ε)
      (hbd.mono fun t ht => ht ε) (hb ε) (hl ε)
  simp only [wInt]
  exact (key 1).sub (key (-1))

theorem alg_step (f : M → ℝ) (t : ℝ) (D α ψ : A.Fld) (hpos : ∀ y, 0 < f y + t) :
    (A.fn (fun y => 1 / (f y + t)) * D - A.fn (fun y => 1 / (f y + t) ^ 2) * (A.fn f * (D + A.fn f * α))) * ψ =
      A.fn (fun y => t / (f y + t) ^ 2) * (D + A.fn f * α) * ψ - A.fn (fun y => f y / (f y + t)) * (α * ψ) := by
  funext z
  have hz := (hpos z.pt).ne'
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, HolAtlas.fn, ← Algebra.smul_def]
  simp only [sub_mul, add_mul, smul_mul_assoc, smul_add, smul_sub, mul_add]
  match_scalars <;> push_cast <;> field_simp <;> ring

end General

theorem pl_step : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ K : MvPolynomial (Fin 5) ℝ,
      wInt (hY.atlas σ) (fun y => Real.log (1 - v y) / 2) (evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) ((X 0 - X 3) * ((X 4 - X 0) * K))) =
        1 / 2 * ((hY.atlas σ).integral (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) ((X 4 - X 0) * K)) - (hY.atlas σ).integral (pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB)) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) ((X 4 - X 0) * K))) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv K
  haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ hY.isProjOver
  haveI : T2Space (CxPts p σ) := CxPts.t2Space_cxPts_of_isProjOver σ hY.isProjOver
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  haveI : BorelSpace (Sp ℂ ⟶ Y) := ⟨rfl⟩
  have hcalc := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ (d + 1) (hY.atlas σ)
  have hbasic := GlobalTheory.T.firstChern_form_properties k Y p (d + 1) hY σ
  have hlin := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous (CxPts p σ) (d + 1) (hY.atlas σ)
  have hfib := (GlobalTheory.T.flag_bundle_chern_integral_pull_fourth k B Y q p d hB hY π w E h H flB fl hfl A σ v hv).1
  have hom := GlobalTheory.T.flag_bundle_hermitian_line_curvature k B Y q p d hB hY π w E h H flB fl hfl A σ
  obtain ⟨hv01, hvc, hvs⟩ := GlobalTheory.T.flag_bundle_hermitian_line_integral k B Y q p d hB hY π w E h H flB fl hfl A σ v hv
  have hloc := GlobalTheory.T.flag_bundle_hermitian_line_degree k B Y q p d hB hY π w E h H flB fl hfl A σ v hv
  have hnull := GlobalTheory.T.flag_bundle_hermitian_line_height k B Y q p d hB hY π w E h H flB fl hfl A σ v hv
  have hconc := GlobalTheory.T.flag_bundle_hermitian_line_limit k B Y q p d hB hY π w E h H flB fl hfl A σ v hv K
  set At := hY.atlas σ with hAt
  set x : Fin 5 → At.Pt → Ev (d + 1) := fun i => c1F hY σ (fam5 π w H flB fl A i) with hx
  set ω := (fld At (omF hY σ (h.pull π w) fl) - pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) with hω
  set Z := evalF At x K with hZ
  set α := evalF At x (X 4 - X 0) with hα
  set f : CxPts p σ → ℝ := fun y => 1 - v y with hf
  have hxF : ∀ i, At.IsForm (fld At (x i)) := fun i => (hbasic.1 _ (fam5 π w H flB fl A i)).1.1
  have hxd : ∀ i, At.del (fld At (x i)) = 0 := fun i => (hbasic.1 _ (fam5 π w H flB fl A i)).2.1
  have hxdb : ∀ i, At.dbar (fld At (x i)) = 0 := fun i => (hbasic.1 _ (fam5 π w H flB fl A i)).2.2.1
  have hev := fun P => hcalc.2.2.2.1 (Fin 5) x P hxF
  have hZF : At.IsForm Z := (hev K).1
  have hZd : At.del Z = 0 := (hev K).2.1 hxd
  have hZdb : At.dbar Z = 0 := (hev K).2.2 hxdb
  have hαF : At.IsForm α := (hev _).1
  have hωF : At.IsForm ω := hom.1
  have hops := fun (c : ℂ) (a b : At.Fld) (ha : At.IsForm a) (hb : At.IsForm b) => hcalc.2.1 c a b ha hb
  have hdbωF : At.IsForm (At.dbar ω) := (hops 0 ω ω hωF hωF).2.2.2.2.1
  have hψF : At.IsForm (Z * ω) := (hops 0 Z ω hZF hωF).2.1
  have hddcψ : At.ddc (Z * ω) = Z * At.ddc ω := by
    have l1 := (hcalc.2.2.1 (fun y => aeval (fun i => x i y) (K.map (algebraMap ℝ ℂ))) ω hZF hωF).2
    have l2 := (hcalc.2.2.1 (fun y => aeval (fun i => x i y) (K.map (algebraMap ℝ ℂ))) (At.dbar ω) hZF hdbωF).1
    change At.dbar (Z * ω) = At.dbar Z * ω + Z * At.dbar ω at l1
    change At.del (Z * At.dbar ω) = At.del Z * At.dbar ω + Z * At.del (At.dbar ω) at l2
    rw [hZdb, zero_mul, zero_add] at l1
    rw [hZd, zero_mul, zero_add] at l2
    show GlobalTheory.HermFrame.kappa • At.del (At.dbar (Z * ω)) = Z * (GlobalTheory.HermFrame.kappa • At.del (At.dbar ω))
    rw [l1, l2, mul_smul_comm]
  have hf01 : ∀ y, 0 ≤ f y ∧ f y ≤ 1 := fun y => ⟨by simp only [hf]; linarith [(hv01 y).2], by simp only [hf]; linarith [(hv01 y).1]⟩
  have hfc : Continuous f := continuous_const.sub hvc
  have hfs : At.SmoothOn Set.univ (fun y => (f y : ℂ)) := fun i =>
    ((contDiffOn_const (c := (1 : ℂ))).sub (hvs i)).congr fun z _ => by simp only [hf, Function.comp_apply]; push_cast; ring
  have hfF : At.IsForm (At.fn f) := At.isForm_fn hfs
  set D := At.ddc (At.fn f) with hD
  have hDF : At.IsForm D := by
    have db := (hops 0 _ _ hfF hfF).2.2.2.2.1
    have dd := (hops 0 _ _ db db).2.2.2.1
    exact (hops GlobalTheory.HermFrame.kappa _ _ dd dd).2.2.1
  have hρF : At.IsForm (D + At.fn f * α) := (hops 0 _ _ hDF (hops 0 _ _ hfF hαF).2.1).1
  have hddcF : At.IsForm (At.ddc (Z * ω)) := by
    have db := (hops 0 _ _ hψF hψF).2.2.2.2.1
    have dd := (hops 0 _ _ db db).2.2.2.1
    exact (hops GlobalTheory.HermFrame.kappa _ _ dd dd).2.2.1
  have hαψF : At.IsForm (α * (Z * ω)) := (hops 0 _ _ hαF hψF).2.1

  have F2 : ∀ t : ℝ, 0 < t → wInt At (fun y => Real.log (f y + t)) (At.ddc (Z * ω)) =
      At.integral (At.fn (fun y => t / (f y + t) ^ 2) * (D + At.fn f * α) * (Z * ω)) -
        wInt At (fun y => f y / (f y + t)) (α * (Z * ω)) := by
    intro t ht
    have hpos : ∀ y, 0 < f y + t := fun y => by linarith [(hf01 y).1]
    obtain ⟨c1, s1, -⟩ := GlobalTheory.T.smooth_composition_form _ _ At f (Set.Ioi (-t)) (fun s => Real.log (s + t)) hfc hfs isOpen_Ioi
      (fun y => by simp only [Set.mem_Ioi]; linarith [hpos y])
      (Real.contDiffOn_log.comp (contDiff_id.add contDiff_const).contDiffOn fun s hs => by
        simp only [Set.mem_Ioi] at hs; simp only [Set.mem_compl_iff, Set.mem_singleton_iff, id]; linarith)
    obtain ⟨-, -, g2F⟩ := GlobalTheory.T.smooth_composition_form _ _ At f (Set.Ioi (-t)) (fun s => t / (s + t) ^ 2) hfc hfs isOpen_Ioi
      (fun y => by simp only [Set.mem_Ioi]; linarith [hpos y])
      (contDiffOn_const.div ((contDiff_id.add contDiff_const).pow 2).contDiffOn fun s hs => by
        simp only [Set.mem_Ioi] at hs; show (s + t) ^ 2 ≠ 0; exact pow_ne_zero _ (by linarith : (0:ℝ) < s + t).ne')
    obtain ⟨c3, -, g3F⟩ := GlobalTheory.T.smooth_composition_form _ _ At f (Set.Ioi (-t)) (fun s => s / (s + t)) hfc hfs isOpen_Ioi
      (fun y => by simp only [Set.mem_Ioi]; linarith [hpos y])
      (contDiff_id.contDiffOn.div (contDiff_id.add contDiff_const).contDiffOn fun s hs => by
        simp only [Set.mem_Ioi] at hs; linarith)
    rw [← GlobalTheory.T.weighted_integral_of_continuous _ _ At _ c1 _ hddcF, GlobalTheory.T.ddc_integration_by_parts _ _ At _ s1 _ hψF,
      GlobalTheory.T.ddc_log_plus_constant _ _ At f hfs (fun y => (hf01 y).1) t ht, hloc, alg_step At f t D α (Z * ω) hpos,
      GlobalTheory.T.integral_sub_of_isForm' At _ _ ((hops 0 _ _ (hops 0 _ _ g2F hρF).2.1 hψF).2.1) ((hops 0 _ _ g3F hαψF).2.1),
      GlobalTheory.T.weighted_integral_of_continuous _ _ At _ c3 _ hαψF]
  have hnullae : ∀ β : At.Fld, At.IsForm β → ∀ ε : ℤˣ, ∀ᵐ y ∂At.part β ε, 0 < f y := by
    intro β hβ ε
    refine ae_iff.2 (measure_mono_null (fun y hy => ?_) (hnull β hβ ε))
    simp only [Set.mem_setOf_eq, hf, not_lt] at hy ⊢
    exact le_antisymm (hv01 y).2 (by linarith)
  have hfin := hlin.1
  have F3 : Tendsto (fun t => wInt At (fun y => Real.log (f y + t)) (At.ddc (Z * ω))) (𝓝[>] 0)
      (𝓝 (wInt At (fun y => Real.log (f y)) (At.ddc (Z * ω)))) := by
    refine wInt_tendsto At _ (b := fun y => 2 * |Real.log (f y) / 2| + 1) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht ε
      exact ((hfc.add continuous_const).log fun y =>
        (by linarith [(hf01 y).1, Set.mem_Ioi.1 ht] : 0 < f y + t).ne').aestronglyMeasurable
    · intro ε
      haveI := hfin _ hddcF ε
      exact (((hfib _ hddcF ε).abs.const_mul 2).add (integrable_const 1))
    · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht ε
      filter_upwards [hnullae _ hddcF ε] with y hy
      have h1 := (hf01 y).2
      have hlog1 : Real.log (f y + t) ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show 0 < f y + t by linarith [ht.1])
        linarith [ht.2]
      have hlog2 : Real.log (f y) ≤ Real.log (f y + t) := Real.log_le_log hy (by linarith [ht.1])
      have hlog3 : Real.log (f y) ≤ 0 := Real.log_nonpos hy.le h1
      have e : 2 * |Real.log (f y) / 2| = -Real.log (f y) := by
        rw [abs_div, abs_two, abs_of_nonpos hlog3]; ring
      rw [Real.norm_eq_abs, abs_le, e]
      constructor <;> linarith
    · intro ε
      filter_upwards [hnullae _ hddcF ε] with y hy
      have : Tendsto (fun t => f y + t) (𝓝[>] 0) (𝓝 (f y + 0)) :=
        ((continuous_const.add continuous_id).tendsto 0).mono_left nhdsWithin_le_nhds
      rw [add_zero] at this
      exact this.log hy.ne'
  have F4 : Tendsto (fun t => wInt At (fun y => f y / (f y + t)) (α * (Z * ω))) (𝓝[>] 0)
      (𝓝 (At.integral (α * (Z * ω)))) := by
    rw [← wInt_one]
    refine wInt_tendsto At _ (b := fun _ => 1) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht ε
      exact (hfc.div (hfc.add continuous_const) fun y =>
        (by linarith [(hf01 y).1, Set.mem_Ioi.1 ht] : 0 < f y + t).ne').aestronglyMeasurable
    · intro ε
      haveI := hfin _ hαψF ε
      exact integrable_const 1
    · filter_upwards [self_mem_nhdsWithin] with t ht ε
      refine Filter.Eventually.of_forall fun y => ?_
      have h0 := (hf01 y).1
      have ht' := Set.mem_Ioi.1 ht
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · have : 0 ≤ f y / (f y + t) := div_nonneg h0 (by linarith)
        linarith
      · exact (div_le_one (by linarith)).2 (by linarith)
    · intro ε
      filter_upwards [hnullae _ hαψF ε] with y hy
      have : Tendsto (fun t => f y + t) (𝓝[>] 0) (𝓝 (f y + 0)) :=
        ((continuous_const.add continuous_id).tendsto 0).mono_left nhdsWithin_le_nhds
      rw [add_zero] at this
      have h2 := (tendsto_const_nhds (x := f y)).div this hy.ne'
      rwa [div_self hy.ne'] at h2
  have F5 : Tendsto (fun t => wInt At (fun y => Real.log (f y + t)) (At.ddc (Z * ω))) (𝓝[>] 0)
      (𝓝 (0 - At.integral (α * (Z * ω)))) := by
    refine (hconc.sub F4).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (F2 t ht).symm
  have hcoreEq : wInt At (fun y => Real.log (1 - v y)) (At.ddc (Z * ω)) = -At.integral (α * (Z * ω)) :=
    (tendsto_nhds_unique F3 F5).trans (zero_sub _)
  have e1 : evalF At x ((X 0 - X 3) * ((X 4 - X 0) * K)) = ((-1 : ℝ) : ℂ) • At.ddc (Z * ω) := by
    rw [hddcψ, hom.2, hZ, ← evalF_mul]
    have : (X 0 - X 3) * ((X 4 - X 0) * K) = -(K * ((X 4 - X 0) * (X 3 - X 0))) := by ring
    rw [this, evalF_neg]
    simp
  have e2 := wInt_div_two At (fun y => Real.log (1 - v y)) (At.ddc (Z * ω))
  beta_reduce at e2
  have hcalcB := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ d (hB.atlas σ)
  have hbasicB := GlobalTheory.T.firstChern_form_properties k B q d hB σ
  have hoY : At.IsForm (fld At (omF hY σ (h.pull π w) fl)) := (hbasic.2.1 _ (h.pull π w) (H.pull π w) fl fl).1.1
  have hoB : (hB.atlas σ).IsForm (fld (hB.atlas σ) (omF hB σ h flB)) := (hbasicB.2.1 E h H flB flB).1.1
  have hpB : At.IsForm (pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) :=
    ((hcalcB.2.2.2.2 (CxPts p σ) (d + 1) At _ (hbasicB.2.2 Y p (d + 1) hY π w).1).2 0 (fld (hB.atlas σ) (omF hB σ h flB)) (fld (hB.atlas σ) (omF hB σ h flB)) |>.2.2.2 hoB).1
  have hPF : At.IsForm (evalF At x ((X 4 - X 0) * K)) := (hev _).1
  have eR : At.integral (fld At (omF hY σ (h.pull π w) fl) * evalF At x ((X 4 - X 0) * K)) -
      At.integral (pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB)) * evalF At x ((X 4 - X 0) * K)) =
      At.integral (α * (Z * ω)) := by
    rw [← GlobalTheory.T.integral_sub_of_isForm' At _ _ (hops 0 _ _ hoY hPF).2.1 (hops 0 _ _ hpB hPF).2.1, ← sub_mul, ← hω,
      ← evalF_comm, evalF_mul, ← hα, ← hZ, mul_assoc]
  rw [eR, e1, hlin.2.2.1 _ _ _ hddcF, e2, hcoreEq]
  ring

end GlobalTheory.LineForm.PLStep
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_chern_integral_pull_fifth : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ K : MvPolynomial (Fin 5) ℝ,
      wInt (hY.atlas σ) (fun y => Real.log (1 - v y) / 2) (evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) ((X 0 - X 3) * ((X 4 - X 0) * K))) =
        1 / 2 * ((hY.atlas σ).integral (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) ((X 4 - X 0) * K)) - (hY.atlas σ).integral (pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB)) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) ((X 4 - X 0) * K))) := by
  atlas_forward_decl GlobalTheory.LineForm.PLStep.pl_step
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.LogSinElim

section Alg

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {ι : Type} (w : ι → A.Pt → Ev n)

theorem evalF_add' (P Q : MvPolynomial ι ℝ) : evalF A w (P + Q) = evalF A w P + evalF A w Q := by
  funext x
  simp only [evalF, fld, map_add, Pi.add_apply, AddMemClass.coe_add]

theorem evalF_mul' (P Q : MvPolynomial ι ℝ) : evalF A w (P * Q) = evalF A w P * evalF A w Q := by
  funext x
  simp only [evalF, fld, map_mul, Pi.mul_apply, MulMemClass.coe_mul]

theorem evalF_sub' (P Q : MvPolynomial ι ℝ) : evalF A w (P - Q) = evalF A w P - evalF A w Q := by
  funext x
  simp only [evalF, fld, map_sub, Pi.sub_apply, AddSubgroupClass.coe_sub]

theorem evalF_X' (i : ι) : evalF A w (X i) = fld A (w i) := by
  funext x
  simp [evalF, fld]

theorem evalF_C' (r : ℝ) : evalF A w (C r) = (r : ℂ) • (1 : A.Fld) := by
  funext x
  simp [evalF, fld, Algebra.algebraMap_eq_smul_one]
  rfl

theorem evalF_aeval_self (s : ι → MvPolynomial ι ℝ) (hs : ∀ i, fld A (w i) = evalF A w (s i))
    (P : MvPolynomial ι ℝ) : evalF A w P = evalF A w (aeval s P) := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [evalF_C']
  | add P Q hP hQ => rw [map_add, evalF_add', evalF_add', hP, hQ]
  | mul_X P i hP => rw [map_mul, evalF_mul', evalF_mul', hP, aeval_X, evalF_X', hs]

end Alg

end GlobalTheory.LogSinElim

namespace GlobalTheory.LogSinElim

section Pull

variable {M M' : Type} [TopologicalSpace M] [TopologicalSpace M'] {n n' : ℕ} (A : HolAtlas M n) (A' : HolAtlas M' n')
  {ι κ : Type} (w : ι → A.Pt → Ev n) (w' : κ → A'.Pt → Ev n')

theorem pullback_evalF (f : M' → M) (hf : A.IsHolo A' f) (s : ι → MvPolynomial κ ℝ)
    (hs : ∀ i, A.pullback A' f (fld A (w i)) = evalF A' w' (s i)) (P : MvPolynomial ι ℝ) :
    A.pullback A' f (evalF A w P) = evalF A' w' (aeval s P) := by
  have hp := ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.2.2.2 M' n' A' f hf)
  induction P using MvPolynomial.induction_on with
  | C r => rw [evalF_C', aeval_C, algebraMap_eq, evalF_C', (hp.2 (r : ℂ) 1 1).2.2.1, hp.1]
  | add P Q hP hQ => rw [evalF_add', (hp.2 1 _ _).1, hP, hQ, map_add, evalF_add']
  | mul_X P i hP => rw [evalF_mul', (hp.2 1 _ _).2.1, hP, evalF_X', hs, map_mul, aeval_X, evalF_mul']

end Pull

def subQ : Fin 5 → MvPolynomial (Fin 5) ℝ := ![X 0, X 3 + X 4 - X 0, X 2, X 3, X 4]

def subB : Fin 5 → MvPolynomial (Fin 5) ℝ := ![X 4, X 3, X 2, X 3, X 4]

theorem dvd_aeval_sub (P : MvPolynomial (Fin 5) ℝ) : (X 4 - X 0 : MvPolynomial (Fin 5) ℝ) ∣ aeval subQ P - aeval subB P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ =>
    rw [map_add, map_add, add_sub_add_comm]
    exact dvd_add hP hQ
  | mul_X P i hP =>
    have hi : (X 4 - X 0 : MvPolynomial (Fin 5) ℝ) ∣ subQ i - subB i := by
      fin_cases i
      · exact ⟨-1, by simp [subQ, subB]⟩
      · exact ⟨1, by simp [subQ, subB]; ring⟩
      · exact ⟨0, by simp [subQ, subB]⟩
      · exact ⟨0, by simp [subQ, subB]⟩
      · exact ⟨0, by simp [subQ, subB]⟩
    rw [map_mul, map_mul, aeval_X, aeval_X,
      show aeval subQ P * subQ i - aeval subB P * subB i =
        (aeval subQ P - aeval subB P) * subQ i + aeval subB P * (subQ i - subB i) by ring]
    exact dvd_add (dvd_mul_of_dvd_left hP _) (dvd_mul_of_dvd_right hi _)

end GlobalTheory.LogSinElim

namespace GlobalTheory.LogSinElim

theorem evalF_one' {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {ι : Type} (w : ι → A.Pt → Ev n) :
    evalF A w 1 = 1 := by
  funext x
  simp [evalF, fld]

theorem logSin_elim : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ K : MvPolynomial (Fin 5) ℝ, K.IsHomogeneous d →
      wInt (hY.atlas σ) (fun y => Real.log (1 - v y) / 2) (evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) ((X 0 - X 3) * K)) =
        1 / 2 * ((hY.atlas σ).integral (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) K) - (hY.atlas σ).integral (pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB)) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) K)) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv K _hK
  haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ hY.isProjOver
  haveI : T2Space (CxPts p σ) := CxPts.t2Space_cxPts_of_isProjOver σ hY.isProjOver
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  obtain ⟨hLY, hEY, -⟩ := GlobalTheory.T.firstChern_form_properties k Y p (d + 1) hY σ
  obtain ⟨hLB, hEB, hPB⟩ := GlobalTheory.T.firstChern_form_properties k B q d hB σ
  obtain ⟨hol, hc1pull, hEpull⟩ := hPB Y p (d + 1) hY π w
  have hrel := (hEpull E h H flB fl).2
  have calcY := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ (d + 1) (hY.atlas σ)
  have calcB := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ d (hB.atlas σ)
  have lin := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous _ (d + 1) (hY.atlas σ)
  obtain ⟨hint, hfib⟩ := GlobalTheory.T.flag_bundle_chern_integral_pull_fourth k B Y q p d hB hY π w E h H flB fl hfl A σ v hv
  have hpl := GlobalTheory.T.flag_bundle_chern_integral_pull_fifth k B Y q p d hB hY π w E h H flB fl hfl A σ v hv
  have hglob := GlobalTheory.T.flag_bundle_chern_integral_pull_third k B Y q p d hB hY π w E h H flB fl hfl A σ
  have hpb := calcB.2.2.2.2 _ (d + 1) (hY.atlas σ) _ hol
  set w5 : Fin 5 → (hY.atlas σ).Pt → Ev (d + 1) := fun i => c1F hY σ (fam5 π w H flB fl A i) with hw5
  let wB : Fin 5 → (hB.atlas σ).Pt → Ev d := ![c1F hB σ (VMetric.grLB flB 1 H), c1F hB σ (VMetric.grLB flB 0 H),
    c1F hB σ A, c1F hB σ (VMetric.grLB flB 0 H), c1F hB σ (VMetric.grLB flB 1 H)]
  have f5 : ∀ i, (hY.atlas σ).IsForm (fld _ (w5 i)) := fun i => (hLY (fam5 π w H flB fl A i) (fam5 π w H flB fl A i)).1.1
  have fB : ∀ i, (hB.atlas σ).IsForm (fld _ (wB i)) := by
    intro i
    fin_cases i
    exacts [(hLB _ A).1.1, (hLB _ A).1.1, (hLB _ A).1.1, (hLB _ A).1.1, (hLB _ A).1.1]
  have ev5 : ∀ P, (hY.atlas σ).IsForm (evalF _ w5 P) := fun P => (calcY.2.2.2.1 (Fin 5) w5 P f5).1
  have evB : ∀ P, (hB.atlas σ).IsForm (evalF _ wB P) := fun P => (calcB.2.2.2.1 (Fin 5) wB P fB).1
  have hωY : (hY.atlas σ).IsForm (fld _ (omF hY σ (h.pull π w) fl)) := (hEY _ (h.pull π w) (H.pull π w) fl fl).1.1
  have hωB : (hB.atlas σ).IsForm (fld _ (omF hB σ h flB)) := (hEB E h H flB flB).1.1
  have hmulY : ∀ α β, (hY.atlas σ).IsForm α → (hY.atlas σ).IsForm β → (hY.atlas σ).IsForm (α * β) :=
    fun α β hα hβ => (calcY.2.1 1 α β hα hβ).2.1
  have hmulB : ∀ α β, (hB.atlas σ).IsForm α → (hB.atlas σ).IsForm β → (hB.atlas σ).IsForm (α * β) :=
    fun α β hα hβ => (calcB.2.1 1 α β hα hβ).2.1
  have hpω : (hY.atlas σ).IsForm (pullF hB hY σ π w (fld _ (omF hB σ h flB))) := ((hpb.2 1 _ 1).2.2.2 hωB).1
  have intAdd : ∀ α β, (hY.atlas σ).IsForm α → (hY.atlas σ).IsForm β →
      (hY.atlas σ).integral (α + β) = (hY.atlas σ).integral α + (hY.atlas σ).integral β := by
    intro α β hα hβ
    rw [← wInt_one, ← wInt_one, ← wInt_one]
    exact (lin.2.1 (fun _ => 1) α β hα hβ (fun ε => by haveI := lin.1 α hα ε; exact integrable_const _)
      (fun ε => by haveI := lin.1 β hβ ε; exact integrable_const _)).2

  have hrel' : ∀ x, w5 1 x = w5 3 x + w5 4 x - w5 0 x := fun x => by
    have e : w5 0 x + w5 1 x = w5 3 x + w5 4 x := congrFun hrel x
    exact eq_sub_of_add_eq' e
  have hsQ : ∀ i, fld _ (w5 i) = evalF (hY.atlas σ) w5 (subQ i) := by
    intro i
    fin_cases i
    · exact (evalF_X' _ w5 0).symm
    · show fld _ (w5 1) = evalF _ w5 (X 3 + X 4 - X 0)
      rw [evalF_sub', evalF_add', evalF_X', evalF_X', evalF_X']
      funext x
      simp only [fld, Pi.add_apply, Pi.sub_apply, hrel' x, AddSubgroupClass.coe_sub, AddMemClass.coe_add]
    · exact (evalF_X' _ w5 2).symm
    · exact (evalF_X' _ w5 3).symm
    · exact (evalF_X' _ w5 4).symm
  have hsB : ∀ i, pullF hB hY σ π w (fld _ (wB i)) = evalF (hY.atlas σ) w5 (subB i) := by
    intro i
    fin_cases i
    · exact (hc1pull (VMetric.grLB flB 1 H)).symm.trans (evalF_X' _ w5 4).symm
    · exact (hc1pull (VMetric.grLB flB 0 H)).symm.trans (evalF_X' _ w5 3).symm
    · exact (hc1pull A).symm.trans (evalF_X' _ w5 2).symm
    · exact (hc1pull (VMetric.grLB flB 0 H)).symm.trans (evalF_X' _ w5 3).symm
    · exact (hc1pull (VMetric.grLB flB 1 H)).symm.trans (evalF_X' _ w5 4).symm
  have hφ : pullF hB hY σ π w (evalF _ wB K) = evalF _ w5 (aeval subB K) :=
    pullback_evalF _ _ wB w5 _ hol subB hsB K

  obtain ⟨K1, hK1⟩ := dvd_aeval_sub K
  have hKs : evalF _ w5 K = evalF _ w5 ((X 4 - X 0) * K1) + evalF _ w5 (aeval subB K) := by
    rw [evalF_aeval_self _ w5 subQ hsQ K, ← evalF_add', ← hK1, sub_add_cancel]
  have hXK : evalF _ w5 ((X 0 - X 3) * K) =
      evalF _ w5 ((X 0 - X 3) * ((X 4 - X 0) * K1)) + evalF _ w5 (X 0 - X 3) * pullF hB hY σ π w (evalF _ wB K) := by
    rw [evalF_mul', hKs, mul_add, ← evalF_mul', hφ]

  have e1 := hfib _ (evB K)
  have e2 := (hglob _ (evB K) 0).2
  have e3 := (hglob _ (hmulB _ _ hωB (evB K)) 0).1
  have hs0 : hs 0 = 1 := by simp [hs]
  rw [hs0, map_one, evalF_one', pow_zero, mul_one, one_mul] at e2
  have hpm : ∀ α β, pullF hB hY σ π w (α * β) = pullF hB hY σ π w α * pullF hB hY σ π w β :=
    fun α β => (hpb.2 1 α β).2.1
  rw [pow_zero, one_mul, hpm] at e3
  norm_num at e2
  have hpF : (hY.atlas σ).IsForm (pullF hB hY σ π w (evalF _ wB K)) := ((hpb.2 1 _ 1).2.2.2 (evB K)).1
  have eA := (lin.2.1 (fun y => Real.log (1 - v y) / 2) _ _ (ev5 ((X 0 - X 3) * ((X 4 - X 0) * K1)))
    (hmulY _ _ (ev5 (X 0 - X 3)) hpF) (hint _ (ev5 _))
    (hint _ (hmulY _ _ (ev5 (X 0 - X 3)) hpF))).2
  have eK1 := hpl K1
  rw [hXK, eA, eK1, hKs, mul_add, mul_add, intAdd _ _ (hmulY _ _ hωY (ev5 _)) (hmulY _ _ hωY (ev5 _)),
    intAdd _ _ (hmulY _ _ hpω (ev5 _)) (hmulY _ _ hpω (ev5 _)), ← hφ, e1, e2, e3]
  ring

end GlobalTheory.LogSinElim
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_chern_integral_pull_first : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ K : MvPolynomial (Fin 5) ℝ, K.IsHomogeneous d →
      wInt (hY.atlas σ) (fun y => Real.log (1 - v y) / 2) (evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) ((X 0 - X 3) * K)) =
        1 / 2 * ((hY.atlas σ).integral (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) K) - (hY.atlas σ).integral (pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB)) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) K)) := by
  atlas_forward_decl GlobalTheory.LogSinElim.logSin_elim
end
