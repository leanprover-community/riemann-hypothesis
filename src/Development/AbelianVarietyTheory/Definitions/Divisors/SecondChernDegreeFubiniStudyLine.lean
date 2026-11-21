import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcMeasUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricIsometricOfIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBcFiniteOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsometryPullIdComp

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame

namespace GlobalTheory.ChTwoModel

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem quot_eq_map {S : ShortComplex X.Modules} (h : Met p σ S.X₂ (0 + 1)) (hS : S.ShortExact)
    (h₁ : IsVB S.X₁ 0) (h₃ : IsVB S.X₃ 1) [IsIso S.g] :
    h.quot hS h₁ h₃ = h.map (asIso S.g) := Met.ext_of_exists fun y => by
  obtain ⟨a, ha⟩ := Met.exists_adapted hS h₁ h₃ y
  refine ⟨a.quot, ha, ?_⟩
  rw [h.quot_G hS h₁ h₃ a ha]
  ext i j
  refine Eq.trans ?_ (((h.map (asIso S.g)).form_frame a.quot ha i j).symm.trans
    (h.form_map (asIso S.g) (a.t i) (a.t j) ha)).symm
  simp [quotGram, toBlocks₂₂, Met.gram, VBExt.AdaptedChart.frame]



theorem isometric_det_ofLB (L : HermLB p) : L.Isometric (VMetric.det (VMetric.isCInf_ofLB L)) :=
  HermLB.isometric_of_chart (M := VMetric.det (VMetric.isCInf_ofLB L)) (Chart.ofLB L.isLB)
    (fun _ => le_rfl) (fun x i j _ _ => congrArg (gm (𝟙 X) x _) (TautFlag.detUnit_chartSec_eq L.isLB i j).symm)
    fun σ _ _ hy => Met.detWeight_ofWeight (L.φ σ) hy



theorem eq_of_isFlagCh2 [IsIntegral X] (hX : IsRegSurf p) {E : X.Modules} {r : ℕ} {h : VMetric p E r}
    {H : h.IsCInf} {fl : Vert.Flag E r} {a b : ℝ} (ha : h.IsCh2Deg a)
    (hb : VMetric.IsFlagCh2 H fl b) : a = b := by
  let φ := (Scheme.Modules.pullbackId X).app E
  have e₁ := (VMetric.isIsometry_pull_id_comp k X p E r h).1
  have e₂ : h.IsIsometry (h.pull (𝟙 X) (Category.id_comp p)) φ.symm := fun σ V s t y hy => by
    have u (s : Γ(E, V)) : φ.hom.app V (φ.inv.app V s) = s := congr(($(φ.inv_hom_id)).app V s)
    exact (e₁ σ V _ _ y hy).symm.trans (congrArg₂ ((h.met σ).form · · y) (u s) (u t))
  have e₃ := (VMetric.isFlagCh2_ofIso k X p _ _ r h _ φ.symm H
    (H.pull (𝟙 X) (Category.id_comp p)) fl b e₂).1 hb
  have e₄ (q : X ⟶ Sp k) (e : 𝟙 X ≫ p = q) (fl') (H' : VMetric.IsFlagCh2 (H.pull (𝟙 X) e) fl' b) :
      VMetric.IsFlagCh2 (H.pull (𝟙 X) rfl) fl' b := by subst e; exact H'
  have e₅ := ha.eq_div (.self hX H fl) (e₄ _ _ _ e₃)
  rwa [show (VMetric.FlagModel.self hX H fl).deg = 1 from RegCover.deg_self hX, Nat.cast_one,
    div_one] at e₅


end GlobalTheory.ChTwoModel
