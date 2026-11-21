import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernRealClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernTensorAddStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernIsometricEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOmegaFormReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernRealClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormsFrameIndependentClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOmegaFormSqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoGradedDeterminantIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcOmegaFormEqC2SubC1Product
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointsMapHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernFormPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartCombinationPower

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineForm

theorem c1F_dual : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ L : HermLB p, c1F hX σ L.dual = -c1F hX σ L := by
  intro k _ X _ p D hX σ L
  funext x
  have e : (fun v => (L.dual.φ σ).φ (pick (L.dual.φ σ).isLB x.pt) (x.ch.symm v)) =
      fun v => -(L.φ σ).φ (pick (L.φ σ).isLB x.pt) (x.ch.symm v) := rfl
  have e₂ : ∀ (u : ReciprocityTheory.L2DbarEstimates.V D → ℝ) (z : ReciprocityTheory.L2DbarEstimates.V D),
      GlobalTheory.HermFrame.ddc (fun v => -u v) z = fun ξ η => -GlobalTheory.HermFrame.ddc u z ξ η := by
    intro u z
    funext ξ η
    simp only [GlobalTheory.HermFrame.ddc, GlobalTheory.leviForm_neg, neg_apply, mul_neg]
  simp only [c1F, Pi.neg_apply]
  rw [e, e₂, ofValues, ofValues]
  simp only [neg_smul, Finset.sum_neg_distrib]

end GlobalTheory.LineForm
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstChern_dual_neg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ L : HermLB p, c1F hX σ L.dual = -c1F hX σ L := by
  atlas_forward_decl GlobalTheory.LineForm.c1F_dual
end

section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_omega_form_real : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2), (hX.atlas σ).IsRealForm 1 (fld _ (omF hX σ h fl)) := by
  first | exact @GlobalTheory.LineForm.isRealForm_omF | exact GlobalTheory.LineForm.isRealForm_omF | (intros; apply GlobalTheory.LineForm.isRealForm_omF <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondChern_real_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2), (hX.atlas σ).IsRealForm 2 (fld _ (c2F hX σ h fl)) ∧ (hX.atlas σ).del (fld _ (c2F hX σ h fl)) = 0 ∧ (hX.atlas σ).dbar (fld _ (c2F hX σ h fl)) = 0 := by
  first | exact @GlobalTheory.ChernReal.c2F_isRealForm_closed | exact GlobalTheory.ChernReal.c2F_isRealForm_closed | (intros; apply GlobalTheory.ChernReal.c2F_isRealForm_closed <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineForm

open GlobalTheory.HermFrame Matrix
open scoped ComplexOrder

theorem c2F_flag_indep : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl fl' : Vert.Flag E 2), c2F hX σ h fl = c2F hX σ h fl' := by
  intro k _ X _ p D hX σ E h H fl fl'
  have gf : ∀ (f : Vert.Flag E 2) (y z : CxPts p σ), z ∈ ptsIn p σ (frameAt f y).U →
      (h.met σ).gram (frameAt f y).frame z =
        ((h.met σ).G ((frameAt f y).mid (lineSC_shortExact f)) z).submatrix finSumFinEquiv finSumFinEquiv :=
    fun f y z hz => Met.gram_frame (S := lineSC f) (r := 1) (s := 1) (h.met σ) (lineSC_shortExact f) (frameAt f y) hz
  have pf : ∀ (f : Vert.Flag E 2) (y z : CxPts p σ), z ∈ ptsIn p σ (frameAt f y).U →
      ((h.met σ).gram (frameAt f y).frame z).PosDef :=
    fun f y z hz => Met.posDef_gram_frame (S := lineSC f) (r := 1) (s := 1) (h.met σ) (lineSC_shortExact f) (frameAt f y) hz
  have sf : ∀ (f : Vert.Flag E 2) (y : CxPts p σ) (i j : Fin 1 ⊕ Fin 1),
      (hX.atlas σ).SmoothOn (ptsIn p σ (frameAt f y).U) fun z => (h.met σ).gram (frameAt f y).frame z i j :=
    fun f y i j => hX.smoothOn (fun _ hz => Met.IsCInf.gram (H σ) (frameAt f y).frame hz) i j
  let ch : Bool × CxPts p σ → Chart E (1 + 1) := fun a =>
    cond a.1 ((frameAt fl a.2).mid (lineSC_shortExact fl)) ((frameAt fl' a.2).mid (lineSC_shortExact fl'))
  let G : Bool × CxPts p σ → CxPts p σ → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ := fun a =>
    cond a.1 ((h.met σ).gram (frameAt fl a.2).frame) ((h.met σ).gram (frameAt fl' a.2).frame)
  let U : Bool × CxPts p σ → Set (CxPts p σ) := fun a => ptsIn p σ (ch a).U
  let g : Bool × CxPts p σ → Bool × CxPts p σ → CxPts p σ → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
    fun a b z => ((ch a).tr p σ (ch b) z).submatrix finSumFinEquiv finSumFinEquiv
  have hG : ∀ a, ∀ z ∈ U a, G a z = ((h.met σ).G (ch a) z).submatrix finSumFinEquiv finSumFinEquiv := by
    rintro ⟨b, y⟩ z hz
    cases b
    · exact gf fl' y z hz
    · exact gf fl y z hz
  have hUo : ∀ a, IsOpen (U a) := fun _ => isOpen_ptsIn _
  have hcov : ∀ y, ∃ a, y ∈ U a := fun y => ⟨(true, y), mem_frameAt fl y⟩
  have hholo : ∀ a b i j, (hX.atlas σ).HolOn (U a ∩ U b) fun z => g a b z i j := fun a b i j c =>
    (c.holo ((ch b).U ⊓ (ch a).U) (((ch a).isFrame.basis inf_le_right).repr
      (GlobalTheory.Twist.resM E inf_le_left ((ch b).e (finSumFinEquiv j))) (finSumFinEquiv i))).mono
      fun _ hv => ⟨hv.1, mem_ptsIn_inf.2 ⟨hv.2.2, hv.2.1⟩⟩
  have hsm : ∀ a i j, (hX.atlas σ).SmoothOn (U a) fun z => G a z i j := by
    rintro ⟨b, y⟩ i j
    cases b
    · exact sf fl' y i j
    · exact sf fl y i j
  have hpd : ∀ a, ∀ z ∈ U a, (G a z).PosDef := by
    rintro ⟨b, y⟩ z hz
    cases b
    · exact pf fl' y z hz
    · exact pf fl y z hz
  have htr : ∀ a b, ∀ z ∈ U a ∩ U b, G b z = chg (g a b z) (G a z) := by
    intro a b z hz
    rw [hG a z hz.1, hG b z hz.2, chg_submatrix, ← (h.met σ).trans _ _ z hz.1]
  have key := GlobalTheory.T.chernForms_frame_independent_closed (hX.atlas σ) U hUo hcov g hholo G hsm hpd htr 2
  funext x
  exact key.1 (true, x.pt) (false, x.pt) x (mem_frameAt fl x.pt) (mem_frameAt fl' x.pt)

end GlobalTheory.LineForm
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondChern_flag_independent : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl fl' : Vert.Flag E 2), c2F hX σ h fl = c2F hX σ h fl' := by
  atlas_forward_decl GlobalTheory.LineForm.c2F_flag_indep
end

section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_omega_form_sq_zero : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2), omF hX σ h fl * omF hX σ h fl = 0 := by
  first | exact @GlobalTheory.LineForm.omF_mul_self | exact GlobalTheory.LineForm.omF_mul_self | (intros; apply GlobalTheory.LineForm.omF_mul_self <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory

theorem c1F_grLB_add_grLB_flag_indep :
    ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl fl' : Vert.Flag E 2), c1F hX σ (VMetric.grLB fl 0 H) + c1F hX σ (VMetric.grLB fl 1 H) = c1F hX σ (VMetric.grLB fl' 0 H) + c1F hX σ (VMetric.grLB fl' 1 H) := by
  intro k _ X _ p D hX σ E h H fl fl'
  rw [← GlobalTheory.T.firstChern_tensor_add k X p D hX σ, ← GlobalTheory.T.firstChern_tensor_add k X p D hX σ,
    GlobalTheory.T.firstChern_isometric_eq k X p D hX σ _ _ (VMetric.isometric_grLB_tens_grLB_det k X p E h H fl),
    GlobalTheory.T.firstChern_isometric_eq k X p D hX σ _ _ (VMetric.isometric_grLB_tens_grLB_det k X p E h H fl')]

end GlobalTheory
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_first_chern_sum_indep : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl fl' : Vert.Flag E 2), c1F hX σ (VMetric.grLB fl 0 H) + c1F hX σ (VMetric.grLB fl 1 H) = c1F hX σ (VMetric.grLB fl' 0 H) + c1F hX σ (VMetric.grLB fl' 1 H) := by
  atlas_forward_decl GlobalTheory.c1F_grLB_add_grLB_flag_indep
end

section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.second_chern_form_pullback : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (Y : Scheme.{0}) (p' : Y ⟶ Sp k) (D' : ℕ) (hY : IsRegVar p' D') (π : Y ⟶ X) (w : π ≫ p = p'),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2) (fl' : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    fld _ (c2F hY σ (h.pull π w) fl') = pullF hX hY σ π w (fld _ (c2F hX σ h fl)) := by
  first | exact @GlobalTheory.SecondChernPull.c2F_pull_eq_pullF_c2F | exact GlobalTheory.SecondChernPull.c2F_pull_eq_pullF_c2F | (intros; apply GlobalTheory.SecondChernPull.c2F_pull_eq_pullF_c2F <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.LineForm

theorem c1F_grLB_sum_pullback_eq_pullback_sum : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (Y : Scheme.{0}) (p' : Y ⟶ Sp k) (D' : ℕ) (hY : IsRegVar p' D') (π : Y ⟶ X) (w : π ≫ p = p'),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2) (fl' : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    c1F hY σ (VMetric.grLB fl' 0 (H.pull π w)) + c1F hY σ (VMetric.grLB fl' 1 (H.pull π w)) = c1F hY σ ((VMetric.grLB fl 0 H).pull π w) + c1F hY σ ((VMetric.grLB fl 1 H).pull π w) := by
  intro k _ X _ p D _ σ Y p' D' hY π w E h H fl fl'
  have ht (L M : HermLB p') : c1F hY σ L + c1F hY σ M = c1F hY σ (L.tens M) := by
    funext ⟨⟨c, y⟩, hy⟩
    exact ((congrArg₂ (· + ·) (ChernTop.c1F_eq_matForm_hessL hY L hy) (ChernTop.c1F_eq_matForm_hessL hY M hy)).trans
      (map_add (ChernTop.matForm D') _ _).symm).trans
      ((congrArg (ChernTop.matForm D') (ChernTop.hessL_tens L M hy)).symm.trans (ChernTop.c1F_eq_matForm_hessL hY (L.tens M) hy).symm)
  have hi (L M : HermLB p') (e : L.Isometric M) : c1F hY σ L = c1F hY σ M := by
    funext ⟨⟨c, y⟩, hy⟩
    exact (ChernTop.c1F_eq_matForm_hessL hY L hy).trans ((congrArg (ChernTop.matForm D')
      (e.hess_eq c hy (mem_pick (M.φ σ).isLB y) (mem_pick (L.φ σ).isLB y)).symm).trans (ChernTop.c1F_eq_matForm_hessL hY M hy).symm)
  rw [ht, ht]
  refine hi _ _ ?_
  have e₁ := (GlobalTheory.VMetric.isometric_grLB_tens_grLB_det k Y p' _ _ (H.pull π w) fl').trans
    (VMetric.isometric_det_pull H π w)
  have e₂ := (GlobalTheory.VMetric.isometric_grLB_tens_grLB_det k X p E h H fl).pull π w
  have e₃ := HermLB.isometric_pull_tens (L := VMetric.grLB fl 0 H) (M := VMetric.grLB fl 1 H) π w
  exact (e₁.trans e₂.symm).trans e₃

end GlobalTheory.LineForm
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_first_chern_graded_pullback : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (Y : Scheme.{0}) (p' : Y ⟶ Sp k) (D' : ℕ) (hY : IsRegVar p' D') (π : Y ⟶ X) (w : π ≫ p = p'),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2) (fl' : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    c1F hY σ (VMetric.grLB fl' 0 (H.pull π w)) + c1F hY σ (VMetric.grLB fl' 1 (H.pull π w)) = c1F hY σ ((VMetric.grLB fl 0 H).pull π w) + c1F hY σ ((VMetric.grLB fl 1 H).pull π w) := by
  atlas_forward_decl GlobalTheory.LineForm.c1F_grLB_sum_pullback_eq_pullback_sum
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.LineForm

theorem basicForms : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    (∀ L M : HermLB p, (hX.atlas σ).IsRealForm 1 (fld _ (c1F hX σ L)) ∧ (hX.atlas σ).del (fld _ (c1F hX σ L)) = 0 ∧
      (hX.atlas σ).dbar (fld _ (c1F hX σ L)) = 0 ∧ c1F hX σ (L.tens M) = c1F hX σ L + c1F hX σ M ∧ c1F hX σ L.dual = -c1F hX σ L ∧
      (L.Isometric M → c1F hX σ L = c1F hX σ M)) ∧
    (∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl fl' : Vert.Flag E 2),
      (hX.atlas σ).IsRealForm 1 (fld _ (omF hX σ h fl)) ∧ (hX.atlas σ).IsRealForm 2 (fld _ (c2F hX σ h fl)) ∧
      (hX.atlas σ).del (fld _ (c2F hX σ h fl)) = 0 ∧ (hX.atlas σ).dbar (fld _ (c2F hX σ h fl)) = 0 ∧
      c2F hX σ h fl = c2F hX σ h fl' ∧ omF hX σ h fl * omF hX σ h fl = 0 ∧
      c1F hX σ (VMetric.grLB fl 0 H) + c1F hX σ (VMetric.grLB fl 1 H) = c1F hX σ (VMetric.grLB fl' 0 H) + c1F hX σ (VMetric.grLB fl' 1 H) ∧
      (hX.atlas σ).ddc (fld _ (omF hX σ h fl)) =
        fld _ (c2F hX σ h fl - c1F hX σ (VMetric.grLB fl 0 H) * c1F hX σ (VMetric.grLB fl 1 H))) ∧
    ∀ (Y : Scheme.{0}) (p' : Y ⟶ Sp k) (D' : ℕ) (hY : IsRegVar p' D') (π : Y ⟶ X) (w : π ≫ p = p'),
      (hX.atlas σ).IsHolo (hY.atlas σ) (GlobalTheory.Points.PtsOver.map π w _) ∧
      (∀ L : HermLB p, fld _ (c1F hY σ (L.pull π w)) = pullF hX hY σ π w (fld _ (c1F hX σ L))) ∧
      ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2) (fl' : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
        fld _ (c2F hY σ (h.pull π w) fl') = pullF hX hY σ π w (fld _ (c2F hX σ h fl)) ∧
        c1F hY σ (VMetric.grLB fl' 0 (H.pull π w)) + c1F hY σ (VMetric.grLB fl' 1 (H.pull π w)) =
          c1F hY σ ((VMetric.grLB fl 0 H).pull π w) + c1F hY σ ((VMetric.grLB fl 1 H).pull π w) := by
  intro k _ X _ p D hX σ
  refine ⟨fun L M => ⟨(GlobalTheory.T.firstChern_real_closed k X p D hX σ L).1, (GlobalTheory.T.firstChern_real_closed k X p D hX σ L).2.1, (GlobalTheory.T.firstChern_real_closed k X p D hX σ L).2.2,
    GlobalTheory.T.firstChern_tensor_add k X p D hX σ L M, GlobalTheory.T.firstChern_dual_neg k X p D hX σ L, GlobalTheory.T.firstChern_isometric_eq k X p D hX σ L M⟩,
    fun E h H fl fl' => ⟨GlobalTheory.T.flag_omega_form_real k X p D hX σ E h H fl, (GlobalTheory.T.secondChern_real_closed k X p D hX σ E h H fl).1, (GlobalTheory.T.secondChern_real_closed k X p D hX σ E h H fl).2.1,
      (GlobalTheory.T.secondChern_real_closed k X p D hX σ E h H fl).2.2, GlobalTheory.T.secondChern_flag_independent k X p D hX σ E h H fl fl', GlobalTheory.T.flag_omega_form_sq_zero k X p D hX σ E h H fl,
      GlobalTheory.T.graded_first_chern_sum_indep k X p D hX σ E h H fl fl', GlobalTheory.T.ddc_omega_form_eq_c2_sub_c1_product k X p D hX σ E h H fl⟩,
    fun Y p' D' hY π w => ⟨GlobalTheory.T.points_map_holomorphic k X p D hX σ Y p' D' hY π w, GlobalTheory.T.first_chern_form_pullback k X p D hX σ Y p' D' hY π w,
      fun E h H fl fl' => ⟨GlobalTheory.T.second_chern_form_pullback k X p D hX σ Y p' D' hY π w E h H fl fl', GlobalTheory.T.sum_first_chern_graded_pullback k X p D hX σ Y p' D' hY π w E h H fl fl'⟩⟩⟩

end GlobalTheory.LineForm
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstChern_form_properties : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    (∀ L M : HermLB p, (hX.atlas σ).IsRealForm 1 (fld _ (c1F hX σ L)) ∧ (hX.atlas σ).del (fld _ (c1F hX σ L)) = 0 ∧
      (hX.atlas σ).dbar (fld _ (c1F hX σ L)) = 0 ∧ c1F hX σ (L.tens M) = c1F hX σ L + c1F hX σ M ∧ c1F hX σ L.dual = -c1F hX σ L ∧
      (L.Isometric M → c1F hX σ L = c1F hX σ M)) ∧
    (∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl fl' : Vert.Flag E 2),
      (hX.atlas σ).IsRealForm 1 (fld _ (omF hX σ h fl)) ∧ (hX.atlas σ).IsRealForm 2 (fld _ (c2F hX σ h fl)) ∧
      (hX.atlas σ).del (fld _ (c2F hX σ h fl)) = 0 ∧ (hX.atlas σ).dbar (fld _ (c2F hX σ h fl)) = 0 ∧
      c2F hX σ h fl = c2F hX σ h fl' ∧ omF hX σ h fl * omF hX σ h fl = 0 ∧
      c1F hX σ (VMetric.grLB fl 0 H) + c1F hX σ (VMetric.grLB fl 1 H) = c1F hX σ (VMetric.grLB fl' 0 H) + c1F hX σ (VMetric.grLB fl' 1 H) ∧
      (hX.atlas σ).ddc (fld _ (omF hX σ h fl)) =
        fld _ (c2F hX σ h fl - c1F hX σ (VMetric.grLB fl 0 H) * c1F hX σ (VMetric.grLB fl 1 H))) ∧
    ∀ (Y : Scheme.{0}) (p' : Y ⟶ Sp k) (D' : ℕ) (hY : IsRegVar p' D') (π : Y ⟶ X) (w : π ≫ p = p'),
      (hX.atlas σ).IsHolo (hY.atlas σ) (GlobalTheory.Points.PtsOver.map π w _) ∧
      (∀ L : HermLB p, fld _ (c1F hY σ (L.pull π w)) = pullF hX hY σ π w (fld _ (c1F hX σ L))) ∧
      ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2) (fl' : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
        fld _ (c2F hY σ (h.pull π w) fl') = pullF hX hY σ π w (fld _ (c2F hX σ h fl)) ∧
        c1F hY σ (VMetric.grLB fl' 0 (H.pull π w)) + c1F hY σ (VMetric.grLB fl' 1 (H.pull π w)) =
          c1F hY σ ((VMetric.grLB fl 0 H).pull π w) + c1F hY σ ((VMetric.grLB fl 1 H).pull π w) := by
  atlas_forward_decl GlobalTheory.LineForm.basicForms
end
