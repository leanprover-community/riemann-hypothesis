import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormProductLatticeStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

open MeasureTheory

namespace GlobalTheory.HSApp.NormProd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (x : ℝ)
  {D : D7} (V : TH.HSp D) (dict : Formalism.L2.Theta.GA D V → (k : U.Comp) × FD.Frame (U.X k).Ψ r) (μ : Measure (AutQ V))

theorem ptN_rdU_le {la : ∀ k, FD.Wt (U.X k).Ψ r} {f : Rul Xo c} (hf : rdU U f ∈ holSub U.X la)
    (z : (k : U.Comp) × FD.Frame (U.X k).Ψ r) : AllWt.ptN la (rdU U f) z ≤ (supE U.X la (rdU U f)).toReal := by
  by_cases h : z.2 ∈ (U.X z.1).dom
  · have h1 : ENNReal.ofReal (AllWt.ptN la (rdU U f) z) ≤ supE U.X la (rdU U f) :=
      le_iSup (fun p : FPt U.X => ENNReal.ofReal ((U.X p.1).pnorm (la p.1) (rdU U f p.1) p.2)) ⟨z.1, ⟨z.2, h⟩⟩
    exact (ENNReal.ofReal_le_iff_le_toReal (supE_ne_top U.X la hf)).1 h1
  · have h0 : AllWt.ptN la (rdU U f) z = 0 := by
      simp [AllWt.ptN, FD.Data.pnorm, rdU, h]
    rw [h0]; exact ENNReal.toReal_nonneg

theorem petE_rdU_ne_top (hμ : μ Set.univ ≤ 1) {la : ∀ k, FD.Wt (U.X k).Ψ r} {f : Rul Xo c}
    (hf : rdU U f ∈ holSub U.X la) : AllWt.petE V dict μ la (rdU U f) ≠ ⊤ := by
  have hb : ∀ᵐ q ∂μ, ‖AllWt.ptN la (rdU U f) (dict (Quotient.out q))‖ ≤ (supE U.X la (rdU U f)).toReal :=
    Filter.Eventually.of_forall fun q => by
      rw [Real.norm_of_nonneg (AllWt.ptN_nonneg _ _ _)]; exact ptN_rdU_le U hf _
  refine ne_top_of_le_ne_top ?_ (eLpNorm_le_of_ae_bound hb)
  refine ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top
  exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (ne_top_of_le_ne_top ENNReal.one_ne_top hμ)

theorem eLpNorm_homN_ne_top (hμ : μ Set.univ ≤ 1) {G : WTZ E} {f : Rul Xo c}
    (hf : rdU U f ∈ holSub U.X (AllWt.modelWt U G)) :
    eLpNorm (fun q : AutQ V => AllWt.homN U x G f (dict (Quotient.out q))) 2 μ ≠ ⊤ := by
  have : (fun q : AutQ V => AllWt.homN U x G f (dict (Quotient.out q))) =
      AllWt.lieFacZ Dw x G • fun q : AutQ V => AllWt.ptN (AllWt.modelWt U G) (rdU U f) (dict (Quotient.out q)) := rfl
  rw [this, eLpNorm_const_smul]
  exact ENNReal.mul_ne_top enorm_ne_top (petE_rdU_ne_top U V dict μ hμ hf)

theorem homN_le_of_berg (hμ : μ Set.univ ≤ 1) (y : FPt U.X) {B : ℝ} (hB0 : 0 ≤ B) {G : WTZ E}
    (hB : AllWt.bergE V dict μ (AllWt.modelWt U G) y ≤ ENNReal.ofReal B) {f : Rul Xo c}
    (hf : rdU U f ∈ holSub U.X (AllWt.modelWt U G)) :
    AllWt.homN U x G f ⟨y.1, y.2.1⟩ ≤ Real.sqrt B * AllWt.petAt U x V dict μ G f := by
  have hfin := petE_rdU_ne_top U V dict μ hμ hf
  have h1 : ENNReal.ofReal (AllWt.ptN (AllWt.modelWt U G) (rdU U f) ⟨y.1, y.2.1⟩) ^ 2 /
      AllWt.petE V dict μ (AllWt.modelWt U G) (rdU U f) ^ 2 ≤ ENNReal.ofReal B :=
    (le_iSup₂ (f := fun P (_ : P ∈ holSub U.X (AllWt.modelWt U G)) =>
      ENNReal.ofReal (AllWt.ptN (AllWt.modelWt U G) P ⟨y.1, y.2.1⟩) ^ 2 /
        AllWt.petE V dict μ (AllWt.modelWt U G) P ^ 2) (rdU U f) hf).trans hB
  rw [ENNReal.div_le_iff_le_mul (Or.inr ENNReal.ofReal_ne_top) (Or.inl (ENNReal.pow_ne_top hfin))] at h1
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hfin)) h1
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (AllWt.ptN_nonneg _ _ _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hB0, ENNReal.toReal_pow] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (AllWt.lieFacZ Dw x G))
  have h4 : AllWt.homN U x G f ⟨y.1, y.2.1⟩ ^ 2 ≤ B * AllWt.petAt U x V dict μ G f ^ 2 := by
    unfold AllWt.homN AllWt.petAt
    nlinarith [h3]
  have h5 := Real.sqrt_le_sqrt h4
  rwa [Real.sqrt_sq (AllWt.homN_nonneg _ _ _ _ _), Real.sqrt_mul hB0, Real.sqrt_sq (AllWt.petAt_nonneg _ _ _ _ _ _ _)] at h5

end GlobalTheory.HSApp.NormProd

namespace GlobalTheory.HSApp

open MeasureTheory in

theorem petOn_mul_le : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (a b : AllWt.Weight (T.Q.Dw j)) (w : Cusp Z Y.U a) (f : Cusp Z Y.U b) (β : ℝ), 0 ≤ β → BergLe Z Y.U (fun _ => D.sp.W j) Y.dict a β → ∀ σ, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ (a + b) 0) σ (w.1 * f.1) ≤ Real.sqrt β * petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ a 0) σ w.1 * petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ b 0) σ f.1 := by
  intro D T j Y e o _ _ Z a b w f β hβ hB σ
  set σ' := goodOf Y.d.c₂ σ with hσ'
  have hg : GoodEmb Y.d.c₂ σ' := Formalism.L2.PjFree.goodEmb_goodOf Y.d.c₂ σ
  set μ := AllWt.muOn (Y.U σ') (D.sp.W j) (Y.dict σ') Z with hμdef
  have hμ : μ Set.univ ≤ 1 := AllWt.muPart_univ_le _ _ _
  have hwH := (AllWt.mem_cuspW.1 w.2.1).2 σ' hg
  have hfH := (AllWt.mem_cuspW.1 f.2.1).2 σ' hg
  have hab : AllWt.wtOf (T.Q.Dw j) (a + b) 0 = AllWt.wtOf (T.Q.Dw j) a 0 + AllWt.wtOf (T.Q.Dw j) b 0 :=
    AllWt.wtOf_add a b 0 0
  set Pa := AllWt.petAt (Y.U σ') (xiR D) (D.sp.W j) (Y.dict σ') μ (AllWt.wtOf (T.Q.Dw j) a 0) w.1 with hPa
  have hPa0 : 0 ≤ Pa := AllWt.petAt_nonneg _ _ _ _ _ _ _
  have hpt : ∀ z : (k : (Y.U σ').Comp) × FD.Frame ((Y.U σ').X k).Ψ D.R.r,
      AllWt.homN (Y.U σ') (xiR D) (AllWt.wtOf (T.Q.Dw j) (a + b) 0) (w.1 * f.1) z ≤
        (Real.sqrt β * Pa) * AllWt.homN (Y.U σ') (xiR D) (AllWt.wtOf (T.Q.Dw j) b 0) f.1 z := by
    intro z
    by_cases hz : z ∈ AllWt.framesOn (Y.U σ') Z
    · obtain ⟨h, -⟩ := id hz
      rw [hab, AllWt.homN_mul _ _ (AllWt.even_wtOf _ _) (AllWt.even_wtOf _ _) _ _ z h]
      refine mul_le_mul_of_nonneg_right ?_ (AllWt.homN_nonneg _ _ _ _ _)
      have hy := hB σ' hg ⟨z.1, ⟨z.2, h⟩⟩ hz
      exact NormProd.homN_le_of_berg (Y.U σ') (xiR D) (D.sp.W j) (Y.dict σ') μ hμ ⟨z.1, ⟨z.2, h⟩⟩ hβ hy hwH
    · have h0 : rdU (Y.U σ') w.1 z.1 z.2 = 0 := AllWt.rdU_eq_zero (Y.U σ') w.2.2 hz
      have h1 : AllWt.homN (Y.U σ') (xiR D) (AllWt.wtOf (T.Q.Dw j) (a + b) 0) (w.1 * f.1) z = 0 := by
        simp only [AllWt.homN, AllWt.ptN, FD.Data.pnorm, AllWt.rdU_mul, Pi.mul_apply, h0, zero_mul, norm_zero, mul_zero]
      rw [h1]
      exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hPa0) (AllWt.homN_nonneg _ _ _ _ _)
  have key : eLpNorm (fun q : AutQ (D.sp.W j) => AllWt.homN (Y.U σ') (xiR D) (AllWt.wtOf (T.Q.Dw j) (a + b) 0)
      (w.1 * f.1) (Y.dict σ' (Quotient.out q))) 2 μ ≤
      ENNReal.ofReal (Real.sqrt β * Pa) * eLpNorm (fun q : AutQ (D.sp.W j) => AllWt.homN (Y.U σ') (xiR D)
        (AllWt.wtOf (T.Q.Dw j) b 0) f.1 (Y.dict σ' (Quotient.out q))) 2 μ := by
    rw [← Real.enorm_eq_ofReal (mul_nonneg (Real.sqrt_nonneg _) hPa0), ← eLpNorm_const_smul]
    refine eLpNorm_mono_real fun q => ?_
    rw [Real.norm_of_nonneg (AllWt.homN_nonneg _ _ _ _ _)]
    exact hpt _
  have hfin := NormProd.eLpNorm_homN_ne_top (Y.U σ') (xiR D) (D.sp.W j) (Y.dict σ') μ hμ hfH
  have k2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) key
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) hPa0)] at k2
  show AllWt.petAt (Y.U σ') (xiR D) (D.sp.W j) (Y.dict σ') μ _ (w.1 * f.1) ≤
    Real.sqrt β * Pa * AllWt.petAt (Y.U σ') (xiR D) (D.sp.W j) (Y.dict σ') μ _ f.1
  rw [AllWt.petAt_eq, AllWt.petAt_eq (Y.U σ') (xiR D) (D.sp.W j) (Y.dict σ') μ (AllWt.wtOf (T.Q.Dw j) b 0)]
  exact k2

end GlobalTheory.HSApp
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.petersson_norm_mul_le_sqrt_bergman_mul_component : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (a b : AllWt.Weight (T.Q.Dw j)) (w : Cusp Z Y.U a) (f : Cusp Z Y.U b) (β : ℝ), 0 ≤ β → BergLe Z Y.U (fun _ => D.sp.W j) Y.dict a β → ∀ σ, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ (a + b) 0) σ (w.1 * f.1) ≤ Real.sqrt β * petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ a 0) σ w.1 * petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ b 0) σ f.1 := by
  atlas_forward_decl GlobalTheory.HSApp.petOn_mul_le
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp

theorem ready_data_mulStable_mulBound : GlobalTheory.CovTop.Hypotheses₂ → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (P : WtPar (T.Q.Dw j)) (R : Choice TF.X Z Y.U P) (ω : CanId R.toModif) (h : Ready R ω (xiR D) (fun _ => D.sp.W j) Y.dict) (f₁ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₁) (f₂ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₂) (th : R.L.Sec) (k : Consts), BergLe Z Y.U (fun _ => D.sp.W j) Y.dict P.u₁ k.beta → (h.data f₁ f₂ th k).MulStable ∧ (h.data f₁ f₂ th k).MulBound fun _ => k.beta := by
  intro hPr D T j Y e o hG hE Z TF P R ω h f₁ f₂ th k hB
  have tr : ∀ (a b : AllWt.Weight (T.Q.Dw j)) (_ : a = b) (g : Cusp Z Y.U a), ∃ g' : Cusp Z Y.U b, g'.1 = g.1 ∧
      (g ∈ latOn Y.U Z (wtOf _ a 0) → g' ∈ latOn Y.U Z (wtOf _ b 0)) := by
    rintro a b rfl g
    exact ⟨g, rfl, id⟩
  have key : ∀ (i : ℕ) (hi : i < P.T) (w' : Cusp Z Y.U P.u₁) (f' : Cusp Z Y.U (P.wt i)),
      ∃ g' : Cusp Z Y.U (P.wt (i + 1)), g'.1 = w'.1 * f'.1 ∧
        (w' ∈ latOn Y.U Z (wtOf _ P.u₁ 0) → f' ∈ latOn Y.U Z (wtOf _ (P.wt i) 0) →
          g' ∈ latOn Y.U Z (wtOf _ (P.wt (i + 1)) 0)) ∧
        ((h.equivV f₁ f₂ th k (Nat.succ_le_of_lt hi) g' : (h.data f₁ f₂ th k).V (i + 1)) :
            (h.data f₁ f₂ th k).Sec (i + 1)) =
          (h.data f₁ f₂ th k).mulW i (f₁.b.equivFun w') (h.equivV f₁ f₂ th k hi.le f') := by
    intro i hi w' f'
    have hx := GlobalTheory.T.cusp_form_product_lattice D T j Y e o hG hE Z P.u₁ (P.wt i) w' f' hPr
    obtain ⟨g, hg, hgl⟩ := hx
    have hy := tr _ _ (P.u₁_add_wt i) g
    obtain ⟨g', hg', hgl'⟩ := hy
    refine ⟨g', hg'.trans hg, fun a b => hgl' (hgl a b), ?_⟩
    exact (h.coe_equivV f₁ f₂ th k _ g').trans ((h.mulW_adjSec f₁ f₂ th k i w' f' g' (hg'.trans hg)).symm.trans
      (congrArg _ (h.coe_equivV f₁ f₂ th k hi.le f').symm))
  refine ⟨?_, ?_⟩
  · intro i hi w hw f hf
    have hk := key i hi (f₁.b.equivFun.symm w) ((h.equivV f₁ f₂ th k hi.le).symm f)
    obtain ⟨g', -, hl, he⟩ := hk
    have hw' : f₁.b.equivFun.symm w ∈ latOn Y.U Z (wtOf _ P.u₁ 0) :=
      (h.mem_lattice f₁ f₂ th k _).1
        (Eq.mpr (congrArg (· ∈ (h.data f₁ f₂ th k).lattice) (f₁.b.equivFun.apply_symm_apply w)) hw)
    have hf' : (h.equivV f₁ f₂ th k hi.le).symm f ∈ latOn Y.U Z (wtOf _ (P.wt i) 0) :=
      (h.equivV_mem f₁ f₂ th k hi.le _).1
        (Eq.mpr (congrArg (· ∈ (h.data f₁ f₂ th k).M i) (LinearEquiv.apply_symm_apply _ f)) hf)
    refine ⟨h.equivV f₁ f₂ th k (Nat.succ_le_of_lt hi) g', (h.equivV_mem f₁ f₂ th k _ g').2 (hl hw' hf'), ?_⟩
    exact he.trans (congrArg₂ (fun a b => (h.data f₁ f₂ th k).mulW i a b) (f₁.b.equivFun.apply_symm_apply w)
      (congrArg Subtype.val (LinearEquiv.apply_symm_apply _ f)))
  · intro i hi σ w hw f hf g hg
    have pe : ∀ (a b : AllWt.Weight (T.Q.Dw j)), a = b → ∀ σ x,
        petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ a 0) σ x =
          petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ b 0) σ x := by
      rintro a b rfl σ x
      rfl
    have hk := key i hi (f₁.b.equivFun.symm w) ((h.equivV f₁ f₂ th k hi.le).symm f)
    obtain ⟨g', hgp, -, he⟩ := hk
    have hgg : g = h.equivV f₁ f₂ th k (Nat.succ_le_of_lt hi) g' :=
      Subtype.ext (hg.trans ((congrArg₂ (fun a b => (h.data f₁ f₂ th k).mulW i a b) (f₁.b.equivFun.apply_symm_apply w)
        (congrArg Subtype.val (LinearEquiv.apply_symm_apply _ f))).symm.trans he.symm))
    have hb := GlobalTheory.T.petersson_norm_mul_le_sqrt_bergman_mul_component D T j Y e o hG hE Z P.u₁ (P.wt i) (f₁.b.equivFun.symm w)
      ((h.equivV f₁ f₂ th k hi.le).symm f) k.beta (zero_le_one.trans k.one_le_beta) hB σ
    have e0 : petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ (P.wt (i + 1)) 0) σ g'.1 =
        petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ (P.u₁ + P.wt i) 0) σ
          ((f₁.b.equivFun.symm w).1 * ((h.equivV f₁ f₂ th k hi.le).symm f).1) :=
      (congrArg (petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ (P.wt (i + 1)) 0) σ) hgp).trans
        (pe _ _ (P.u₁_add_wt i).symm σ _)
    have e1 := h.nrm_equivV f₁ f₂ th k (Nat.succ_le_of_lt hi) σ g'
    have e2 := h.normAt_eq f₁ f₂ th k σ (f₁.b.equivFun.symm w)
    have e3 := h.nrm_equivV f₁ f₂ th k hi.le σ ((h.equivV f₁ f₂ th k hi.le).symm f)
    have e2' := (congrArg ((h.data f₁ f₂ th k).normAt σ) (f₁.b.equivFun.apply_symm_apply w).symm).trans e2
    have e3' := (congrArg (((h.data f₁ f₂ th k).nm i).nrm σ) (LinearEquiv.apply_symm_apply _ f).symm).trans e3
    calc _ = _ := congrArg (((h.data f₁ f₂ th k).nm (i + 1)).nrm σ) hgg
      _ = _ := e1
      _ = _ := e0
      _ ≤ _ := hb
      _ = _ := congrArg₂ (fun a b => Real.sqrt k.beta * a * b) e2'.symm e3'.symm

end GlobalTheory.HSApp
end
