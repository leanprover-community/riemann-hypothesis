import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsTensorPowerStatement

section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CoverNorm

theorem isRatSec_pull_tens {X Z : Scheme.{0}} [IsIntegral Z] (A B : LB X) (j : Z ⟶ X)
    {r : (A.pull j).ι → Z.functionFieldˣ} {s : (B.pull j).ι → Z.functionFieldˣ}
    (hr : IsRatSec (A.pull j) r) (hs : IsRatSec (B.pull j) s) :
    IsRatSec ((CechPic.tens A B).pull j)
      fun i => r (fun _ => (i PUnit.unit).1) * s fun _ => (i PUnit.unit).2 := by
  have cA {i : ((CechPic.tens A B).pull j).ι} :
      ((CechPic.tens A B).pull j).U i ≤ (A.pull j).U fun _ => (i PUnit.unit).1 :=
    fun _ hx => Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hx PUnit.unit).1
  have cB {i : ((CechPic.tens A B).pull j).ι} :
      ((CechPic.tens A B).pull j).U i ≤ (B.pull j).U fun _ => (i PUnit.unit).2 :=
    fun _ hx => Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hx PUnit.unit).2
  intro i i' h
  have lA := inf_le_inf (cA (i := i)) (cA (i := i'))
  have lB := inf_le_inf (cB (i := i)) (cB (i := i'))
  rw [Units.val_mul, Units.val_mul, hr _ _ (lA h), hs _ _ (lB h), mul_mul_mul_comm,
    ← fnOf_resG lA h, ← fnOf_resG lB h, ← map_mul,
    InducedPull.val_pull_g _ j i i' (InducedPull.inf_le _ j i i')]
  congr 2
  refine Eq.trans ?_ (map_mul _ _ _).symm
  refine congrArg₂ (· * ·) ?_ ?_
  · refine (congrArg _ (InducedPull.val_pull_g A j _ _ (InducedPull.inf_le A j _ _))).trans ?_
    have e := (Scheme.Hom.appLE_map j (InducedPull.inf_le A j (fun _ => (i PUnit.unit).1)
      fun _ => (i' PUnit.unit).1) (homOfLE lA).op).trans
      (Scheme.Hom.map_appLE j (InducedPull.inf_le _ j i i') (homOfLE (le_inf (inf_le_left.trans inf_le_left)
        (inf_le_right.trans inf_le_left))).op).symm
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom e) (A.g (i PUnit.unit).1 (i' PUnit.unit).1).val
  · refine (congrArg _ (InducedPull.val_pull_g B j _ _ (InducedPull.inf_le B j _ _))).trans ?_
    have e := (Scheme.Hom.appLE_map j (InducedPull.inf_le B j (fun _ => (i PUnit.unit).2)
      fun _ => (i' PUnit.unit).2) (homOfLE lB).op).trans
      (Scheme.Hom.map_appLE j (InducedPull.inf_le _ j i i') (homOfLE (le_inf (inf_le_left.trans inf_le_right)
        (inf_le_right.trans inf_le_right))).op).symm
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom e) (B.g (i PUnit.unit).2 (i' PUnit.unit).2).val

theorem norms_tens : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L₁ L₂ : HermLB V.p) (f₁ : Y.X → Y.Fn) (a₁ : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l₁ : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) (f₂ : Y.X → Y.Fn) (a₂ : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l₂ : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ), Norms V L₁ f₁ a₁ l₁ → Norms V L₂ f₂ a₂ l₂ → Norms V (L₁.tens L₂) (fun x => f₁ x * f₂ x) (fun σ y => a₁ σ y + a₂ σ y) (fun v e y => l₁ v e y + l₂ v e y) := by
  intro F _ _ Y V L₁ L₂ f₁ a₁ l₁ f₂ a₂ l₂ h₁ h₂
  obtain ⟨r₁, hr₁, hu₁, hc₁, hv₁⟩ := h₁
  obtain ⟨r₂, hr₂, hu₂, hc₂, hv₂⟩ := h₂
  have cA {i : ((L₁.tens L₂).B.pull V.j).ι} {x : V.G} (hx : x ∈ ((L₁.tens L₂).B.pull V.j).U i) :
      x ∈ (L₁.B.pull V.j).U fun _ => (i PUnit.unit).1 :=
    Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hx PUnit.unit).1
  have cB {i : ((L₁.tens L₂).B.pull V.j).ι} {x : V.G} (hx : x ∈ ((L₁.tens L₂).B.pull V.j).U i) :
      x ∈ (L₂.B.pull V.j).U fun _ => (i PUnit.unit).2 :=
    Set.mem_iInter.2 fun _ => (Set.mem_iInter.1 hx PUnit.unit).2
  have split : ∀ (i : ((L₁.tens L₂).B.pull V.j).ι) (g₁ g₂ : Y.Fn),
      V.φ (g₁ * g₂) * (((r₁ (fun _ => (i PUnit.unit).1) * r₂ (fun _ => (i PUnit.unit).2) : V.G.functionFieldˣ)) :
        V.G.functionField) =
      (V.φ g₁ * (r₁ (fun _ => (i PUnit.unit).1) : V.G.functionField)) *
        (V.φ g₂ * (r₂ (fun _ => (i PUnit.unit).2) : V.G.functionField)) := by
    intro i g₁ g₂
    rw [map_mul, Units.val_mul]
    ring
  refine ⟨fun i => r₁ (fun _ => (i PUnit.unit).1) * r₂ (fun _ => (i PUnit.unit).2),
    isRatSec_pull_tens L₁.B L₂.B V.j hr₁ hr₂, fun i x hx => ?_, fun σ z y y' i e₁ e₂ hi => ?_,
    fun v e y z yt i e₁ e₂ hi => ?_⟩
  · rw [split]
    exact (hu₁ _ x (cA hx)).mul (hu₂ _ x (cB hx))
  · have hπ : V.π (under z) = under y := by
      show _ = y.1 _
      rw [e₁]
      rfl
    have H₁ := hc₁ σ z y y' _ e₁ e₂ (cA hi)
    have H₂ := hc₂ σ z y y' _ e₁ e₂ (cB hi)
    have U₁ := hu₁ _ _ (cA hi)
    have U₂ := hu₂ _ _ (cB hi)
    rw [hπ] at U₁ U₂
    have n₁ := norm_ne_zero_iff.2 (ratVal_ne_zero (y := z) U₁)
    have n₂ := norm_ne_zero_iff.2 (ratVal_ne_zero (y := z) U₂)
    beta_reduce
    rw [split, ratVal_mul U₁.regAt U₂.regAt, norm_mul, Real.log_mul n₁ n₂, H₁, H₂]
    change _ = _ - ((L₁.φ _).φ (i PUnit.unit).1 y' + (L₂.φ _).φ (i PUnit.unit).2 y') / 2
    ring
  · have H₁ := hv₁ v e y z yt (fun _ => (i PUnit.unit).1) e₁ e₂ (fun x hx => (hi hx).1)
    have H₂ := hv₂ v e y z yt (fun _ => (i PUnit.unit).2) e₁ e₂ (fun x hx => (hi hx).2)
    have hmem : below z ∈ ((L₁.tens L₂).B.pull V.j).U i := by
      have h1 : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ (L₁.tens L₂).B.U (i PUnit.unit) := by
        rw [← e₂]
        exact hi (Set.mem_univ _)
      exact Set.mem_iInter.2 fun _ => h1
    have hπ : V.π (below z) = below y.1 := by
      rw [← e₁]
      rfl
    have U₁ := hu₁ _ _ (cA hmem)
    have U₂ := hu₂ _ _ (cB hmem)
    rw [hπ] at U₁ U₂
    rw [split, SmallSec.valAt_mul U₁.regAt U₂.regAt, map_mul,
      Real.log_mul (e.w.pos (SmallSec.valAt_ne_zero U₁)).ne' (e.w.pos (SmallSec.valAt_ne_zero U₂)).ne', ← H₁, ← H₂]

end GlobalTheory.CoverNorm
end
end

section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norms_tensor_product : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L₁ L₂ : HermLB V.p) (f₁ : Y.X → Y.Fn) (a₁ : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l₁ : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) (f₂ : Y.X → Y.Fn) (a₂ : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l₂ : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ), Norms V L₁ f₁ a₁ l₁ → Norms V L₂ f₂ a₂ l₂ → Norms V (L₁.tens L₂) (fun x => f₁ x * f₂ x) (fun σ y => a₁ σ y + a₂ σ y) (fun v e y => l₁ v e y + l₂ v e y) := by
  first | exact @GlobalTheory.CoverNorm.norms_tens | exact GlobalTheory.CoverNorm.norms_tens | (intros; apply GlobalTheory.CoverNorm.norms_tens <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

namespace GlobalTheory.CoverNorm

theorem Norms.dual : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L : HermLB V.p) (f : Y.X → Y.Fn)
    (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ),
    Norms V L f a l → Norms V L.dual (fun x => (f x)⁻¹) (fun σ y => -a σ y) (fun v e y => -l v e y) := by
  intro F _ _ Y V L f a l h
  obtain ⟨r, hr, hun, hcx, hfin⟩ := h
  have key : ∀ (i : (L.B.pull V.j).ι) (g : Y.Fn),
      V.φ g⁻¹ * (((r i)⁻¹ : V.G.functionFieldˣ) : V.G.functionField) = (V.φ g * r i)⁻¹ := by
    intro i g
    rw [map_inv₀, Units.val_inv_eq_inv_val, mul_inv]
  refine ⟨fun i => (r i)⁻¹, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have e := hr i j hij
    have e' : fnOf _ hij (((CechPic.dual L.B).pull V.j).g i j).val = (fnOf _ hij ((L.B.pull V.j).g i j).val)⁻¹ :=
      (congrArg (fun u : Γ(V.G, (L.B.pull V.j).U i ⊓ (L.B.pull V.j).U j)ˣ => fnOf _ hij u.val)
        (GlobalTheory.LineNorm.Neg.pull_dual_g L.B V.j i j)).trans (map_units_inv _ _)
    refine Eq.trans ?_ (congrArg (· * _) e').symm
    rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, e, mul_inv]
    rfl
  · intro i x hx
    show UnitAt x (V.φ (f (V.π x))⁻¹ * (((r i)⁻¹ : V.G.functionFieldˣ) : V.G.functionField))
    rw [key i (f (V.π x))]
    exact (hun i x hx).inv
  · intro σ z y y' i e1 e2 hi
    have H := hcx σ z y y' i e1 e2 hi
    rw [show (L.dual.φ _).φ (i PUnit.unit) y' = -((L.φ _).φ (i PUnit.unit) y') from rfl]
    have hπ : V.π (under z) = under y := by
      show _ = y.1 _
      rw [e1]
      rfl
    have hx : under z ∈ (L.B.pull V.j).U i := hi
    have hU := hun i _ hx
    rw [hπ] at hU
    have one : ratVal (1 : V.G.functionField) z = 1 := by
      have e := ratVal_fnOf (y := z) CxPts.mem_ptsIn_top trivial 1
      rw [map_one] at e
      rw [e]
      exact CxPts.ev_one CxPts.mem_ptsIn_top
    have k3 : ratVal (V.φ (f (under y)) * (r i : V.G.functionField))⁻¹ z *
        ratVal (V.φ (f (under y)) * (r i : V.G.functionField)) z = 1 := by
      rw [← ratVal_mul hU.inv.regAt hU.regAt, inv_mul_cancel₀ hU.ne_zero, one]
    have h0 : ratVal (V.φ (f (under y)) * (r i : V.G.functionField)) z ≠ 0 := right_ne_zero_of_mul_eq_one k3
    have h0' : ratVal (V.φ (f (under y)) * (r i : V.G.functionField))⁻¹ z ≠ 0 := left_ne_zero_of_mul_eq_one k3
    have k4 := congrArg (fun t : ℂ => Real.log ‖t‖) k3
    simp only [norm_mul, norm_one, Real.log_one] at k4
    rw [Real.log_mul (norm_ne_zero_iff.2 h0') (norm_ne_zero_iff.2 h0)] at k4
    show -a σ y = Real.log ‖ratVal (V.φ (f (under y))⁻¹ * (((r i)⁻¹ : V.G.functionFieldˣ) : V.G.functionField)) z‖ - _
    rw [key i (f (under y))]
    linarith
  · intro v e y z yt i e1 e2 hi
    have H := hfin v e y z yt i e1 e2 hi
    have hmem : below z ∈ (L.B.pull V.j).U i := by
      have h1 : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ L.B.U (i PUnit.unit) := by
        rw [← e2]
        exact hi (Set.mem_univ _)
      exact Set.mem_iInter.2 fun _ => h1
    have hπ : V.π (below z) = below y.1 := by
      rw [← e1]
      rfl
    have hU := hun i _ hmem
    rw [hπ] at hU
    show -l v e y = Real.log (e.w (valAt z (V.φ (f (below y.1))⁻¹ * (((r i)⁻¹ : V.G.functionFieldˣ) : V.G.functionField))))
    rw [key i (f (below y.1)), GlobalTheory.LineNorm.Neg.valAt_inv hU, map_inv₀, Real.log_inv, H]

end GlobalTheory.CoverNorm
end
end

section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norms_dual_bundle : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L : HermLB V.p) (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ), Norms V L f a l → Norms V L.dual (fun x => (f x)⁻¹) (fun σ y => -a σ y) (fun v e y => -l v e y) := by
  first | exact @GlobalTheory.CoverNorm.Norms.dual | exact GlobalTheory.CoverNorm.Norms.dual | (intros; apply GlobalTheory.CoverNorm.Norms.dual <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CoverNorm

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem isRatSec_one_pull_triv (V : Cover Y) :
    IsRatSec ((LB.triv V.X).pull V.j) (fun _ => 1) := fun a b h => by
  have hL := LB.isLB_pull (LB.isLB_triv V.X) V.j
  obtain rfl : a = b := Subsingleton.elim (α := PUnit → PUnit) _ _
  have := congrArg (fun u : Γ(V.G, _)ˣ => fnOf _ h.1 u.val) (hL.g_self a)
  rw [Units.val_one, map_one] at this
  exact (this.symm.trans (fnOf_resG _ h.1 _)).trans (mul_one _).symm

theorem norms_triv_fnB : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y), Norms V (HermLB.triv V.p) (fun _ => 1) (fun _ _ => 0) (fun _ _ _ => 0) ∧ ∀ (u : ∀ σ : 𝓞 F →+* ℂ, CxPts V.p σ → ℝ) (hu : ∀ σ y, CxPts.CInfAt (u σ) y) (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ), (∀ (σ : F →+* ℂ) (z : CxPts (V.π ≫ Y.str) σ) (y : Pts Y σ) (y' : CxPts V.p (σ.comp (algebraMap (𝓞 F) F))), y.1 = z.1 ≫ V.π → y'.1 = z.1 ≫ V.j → a σ y = -(u _ y' / 2)) → Norms V (ArInt.fnB u hu hc) (fun _ => 1) a (fun _ _ _ => 0) := by
  intro F _ _ Y V
  have hcx {σ : F →+* ℂ} (z : CxPts (V.π ≫ Y.str) σ) :
      Real.log ‖ratVal (V.φ 1 * ((1 : V.G.functionFieldˣ) : V.G.functionField)) z‖ = 0 := by
    rw [map_one, Units.val_one, mul_one]
    have e := ratVal_fnOf (y := z) CxPts.mem_ptsIn_top trivial 1
    rw [map_one, CxPts.ev_one CxPts.mem_ptsIn_top] at e
    rw [e, norm_one, Real.log_one]
  have hfin {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) :
      0 = Real.log (e.w (valAt z (V.φ 1 * ((1 : V.G.functionFieldˣ) : V.G.functionField)))) := by
    rw [map_one, Units.val_one, mul_one, GlobalTheory.TrueGeo.Res.valAt_one, map_one, Real.log_one]
  refine ⟨⟨fun _ => 1, isRatSec_one_pull_triv V, fun i x _ => ?_, fun σ z y y' i _ _ _ => ?_,
    fun v e y z yt i _ _ _ => hfin e z⟩, fun u hu hc a ha => ⟨fun _ => 1, isRatSec_one_pull_triv V,
    fun i x _ => ?_, fun σ z y y' i e₁ e₂ _ => ?_, fun v e y z yt i _ _ _ => hfin e z⟩⟩
  · rw [map_one, Units.val_one, mul_one]; exact unitAt_one x
  · rw [hcx]
    show (0 : ℝ) = 0 - 0 / 2
    ring
  · rw [map_one, Units.val_one, mul_one]; exact unitAt_one x
  · rw [hcx, ha σ z y y' e₁ e₂]
    show -(u _ y' / 2) = 0 - u _ y' / 2
    ring

end GlobalTheory.CoverNorm
end
end

section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_weight_smooth_normalization : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y), Norms V (HermLB.triv V.p) (fun _ => 1) (fun _ _ => 0) (fun _ _ _ => 0) ∧ ∀ (u : ∀ σ : 𝓞 F →+* ℂ, CxPts V.p σ → ℝ) (hu : ∀ σ y, CxPts.CInfAt (u σ) y) (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ), (∀ (σ : F →+* ℂ) (z : CxPts (V.π ≫ Y.str) σ) (y : Pts Y σ) (y' : CxPts V.p (σ.comp (algebraMap (𝓞 F) F))), y.1 = z.1 ≫ V.π → y'.1 = z.1 ≫ V.j → a σ y = -(u _ y' / 2)) → Norms V (ArInt.fnB u hu hc) (fun _ => 1) a (fun _ _ _ => 0) := by
  first | exact @GlobalTheory.CoverNorm.norms_triv_fnB | exact GlobalTheory.CoverNorm.norms_triv_fnB | (intros; apply GlobalTheory.CoverNorm.norms_triv_fnB <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O

namespace GlobalTheory.CoverNorm

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {V : Cover Y}

theorem norms_zp {L : HermLB V.p} {f : Y.X → Y.Fn} {a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} (h : Norms V L f a l) (m : ℤ) :
    Norms V (ArInt.zp L m) (fun x => f x ^ m) (fun σ y => m * a σ y) (fun v e y => m * l v e y) := by
  have h₁ := GlobalTheory.T.norms_tensor_power F Y V L f a l m.toNat h
  have h₂ := GlobalTheory.T.norms_dual_bundle F Y V _ _ _ _ (GlobalTheory.T.norms_tensor_power F Y V L f a l (-m).toNat h)
  refine (GlobalTheory.T.norms_tensor_product F Y V _ _ _ _ _ _ _ _ h₁ h₂).congr (fun x => ?_) (fun σ y => ?_) (fun v e y => ?_)
  · rcases m with n | n
    · simp
    · rw [zpow_negSucc]
      have : (Int.negSucc n).toNat = 0 := rfl
      have h' : (-Int.negSucc n).toNat = n + 1 := rfl
      rw [this, h', pow_zero, one_mul]
  · have := Int.toNat_sub_toNat_neg m
    have hE : ((m.toNat : ℕ) : ℝ) - (((-m).toNat : ℕ) : ℝ) = m := by exact_mod_cast this
    linear_combination a σ y * hE
  · have := Int.toNat_sub_toNat_neg m
    have hE : ((m.toNat : ℕ) : ℝ) - (((-m).toNat : ℕ) : ℝ) = m := by exact_mod_cast this
    linear_combination l v e y * hE

theorem norms_comb {ι : Type} [Fintype ι] {L : ι → HermLB V.p} {f : ι → Y.X → Y.Fn} {a : ι → ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l : ι → ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} (h : ∀ i, Norms V (L i) (f i) (a i) (l i)) (n : ι → ℤ) :
    Norms V (ArInt.comb L n) (fun x => ∏ i, f i x ^ n i) (fun σ y => ∑ i, (n i : ℝ) * a i σ y)
      (fun v e y => ∑ i, (n i : ℝ) * l i v e y) := by
  have key : ∀ s : List ι, Norms V (s.foldr (fun i M => (ArInt.zp (L i) (n i)).tens M) (HermLB.triv V.p))
      (fun x => (s.map fun i => f i x ^ n i).prod) (fun σ y => (s.map fun i => (n i : ℝ) * a i σ y).sum)
      (fun v e y => (s.map fun i => (n i : ℝ) * l i v e y).sum) := by
    intro s
    induction s with
    | nil => exact (GlobalTheory.T.conjugate_weight_smooth_normalization F Y V).1
    | cons i s ih =>
      simp only [List.foldr_cons, List.map_cons, List.prod_cons, List.sum_cons]
      exact GlobalTheory.T.norms_tensor_product F Y V _ _ _ _ _ _ _ _ (norms_zp (h i) (n i)) ih
  refine (key Finset.univ.toList).congr (fun x => ?_) (fun σ y => ?_) (fun v e y => ?_)
  · exact Finset.prod_map_toList _ _
  · exact Finset.sum_map_toList _ _
  · exact Finset.sum_map_toList _ _

end GlobalTheory.CoverNorm
end
end
