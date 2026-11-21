import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MSmoothOfWeightIffIsCInf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PnPosOfGeneratesAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MongeAmpereIntegralInvariantHomeomorphTransport

section
namespace MetricWeightSmoothness
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.MetWeightSmooth

theorem cInfAt_log_normSq_ratVal {F : Type} [Field F] {σ : F →+* ℂ} {Y : Var F} {g : Y.Fn} {y : Pts Y σ}
    (h : UnitAt (under y) g) : CInfAt (fun z : Pts Y σ => Real.log (‖ratVal g z‖ ^ 2)) y := by
  obtain ⟨U, hy, a, e⟩ := h.regAt.exists_fnOf
  have hW : y ∈ ptsIn Y.str σ U := mem_ptsIn.2 hy
  refine ⟨U, Unit, inferInstance, fun _ => a, fun v => Real.log (‖v ()‖ ^ 2), {v | v () ≠ 0},
    hW, isOpen_ne_fun (continuous_apply _) continuous_const, ?_, ?_, ?_⟩
  · show ev Y.str σ U a y ≠ 0
    have := ratVal_ne_zero h
    rwa [← e, ratVal_fnOf hW] at this
  · refine ContDiffOn.log ?_ fun v hv => pow_ne_zero 2 (norm_ne_zero_iff.2 hv)
    exact ((contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ ())).contDiffOn
  · filter_upwards [(isOpen_ptsIn U).mem_nhds hW] with z hz
    rw [← e, ratVal_fnOf hz]

theorem cInfAt_of_smoothOn_tAtlas {F : Type} [Field F] {σ : F →+* ℂ} {Y : Var F} {e : ℕ} {X : Type} [TopologicalSpace X]
    {A : FinHolAtlas e X} {h : X ≃ₜ Pts Y σ} (hA : IsAlgAtlas (tAtlas A h)) {U : Set X} (hU : IsOpen U) {φ : X → ℝ}
    (hφ : A.SmoothOn U φ) {y : Pts Y σ} (hy : h.symm y ∈ U) : CInfAt (fun z => φ (h.symm z)) y := by
  have hS : IsOpen (h.symm ⁻¹' U) := hU.preimage h.symm.continuous
  have hs : (tAtlas A h).SmoothOn (h.symm ⁻¹' U) (fun z => φ (h.symm z)) := fun j => by
    have e₁ : (fun z => φ (h.symm z)) ∘ ((tAtlas A h).chart j).symm = φ ∘ (A.chart j).symm :=
      funext fun v => by simp [tAtlas_symm]
    have e₂ : ((tAtlas A h).chart j).target ∩ ((tAtlas A h).chart j).symm ⁻¹' (h.symm ⁻¹' U) =
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' U := by
      ext v
      simp [tAtlas_symm, tAtlas_target]
    rw [e₁, e₂]
    exact hφ j
  exact (cInfAt_iff_smoothOn hA.anRead hS).2 ((hA.smoothOn_iff hA.anRead hS).1 hs) y hy

theorem metWeight_isCInf : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y) (Δ : Y.Dv) (m : ∀ σ, C.Met Y σ Δ) (hm : ∀ σ y, PosAt (m σ) y) (Q : ∀ a, LocPot (M.X a)), (∀ a, IsPot (I.pt a) (m (I.ε a)) (Q a) ∧ IsPotential (M.A a) (Q a)) → ∀ σ, (metWeight Δ (m σ) (hm σ)).IsCInf := by
  intro F _ _ C Y e M I Δ m hm Q hQ σ
  obtain ⟨a, rfl⟩ := I.ε.surjective σ
  intro c y hy
  obtain ⟨x, rfl⟩ := (I.pt a).surjective y
  have hxU : (I.pt a).symm (I.pt a x) ∈ (Q a).U x := by simpa using (Q a).mem_U x
  obtain ⟨f, hf⟩ := (hQ a).1 x
  have key : ∀ z : Pts Y (I.ε a), (I.pt a).symm z ∈ (Q a).U x → z ∈ ptsIn Y.str (I.ε a) ((toLB Δ).U c) →
      UnitAt (under z) (f * (c.1.2 : Y.Fn)) ∧ (metWeight Δ (m _) (hm _)).φ c z =
        2 * (Q a).φ x ((I.pt a).symm z) + Real.log (‖ratVal (f * (c.1.2 : Y.Fn)) z‖ ^ 2) := by
    intro z hz hzc
    have hzc' : under z ∈ c.1.1 := mem_ptsIn.1 hzc
    obtain ⟨h₁, h₂, h₃⟩ := hf _ hz
    rw [Homeomorph.apply_symm_apply] at h₁ h₂ h₃
    have he : Δ.IsEqn (under z) c.1.2 := c.2.2 _ hzc'
    have hu := he.generatesAt_iff.1 h₁
    have hgen := CartierDiv.isEqn_iff_generatesAt_inv.1 he
    have hp := pn_pos_of_generatesAt (C := C) hgen (hm _ z)
    have hr : 0 < ‖ratVal (f * (c.1.2 : Y.Fn)) z‖ ^ 2 := pow_pos (norm_pos_iff.2 (ratVal_ne_zero hu)) 2
    have e₁ : (f * (c.1.2 : Y.Fn)) * (c.1.2 : Y.Fn)⁻¹ = f := by
      rw [mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), mul_one]
    have e₂ := C.pn_mul Y _ Δ (m _) _ _ z hu.regAt hgen.regularAt
    rw [e₁] at e₂
    refine ⟨hu, ?_⟩
    rw [metWeight_φ, h₃, lnN, e₂, Real.log_mul hr.ne' hp.ne']
    ring
  have hS : IsOpen ((I.pt a).symm ⁻¹' (Q a).U x) := ((Q a).isOpen_U x).preimage (I.pt a).symm.continuous
  refine (((cInfAt_of_smoothOn_tAtlas (isAlgAtlas_tAtlas I a) ((Q a).isOpen_U x) ((hQ a).2.1 x) hxU).const_mul 2).add
    (cInfAt_log_normSq_ratVal (key _ hxU hy).1)).congr ?_
  filter_upwards [hS.mem_nhds hxU, (isOpen_ptsIn _).mem_nhds hy] with z hz hzc
  exact (key z hz hzc).2

end GlobalTheory.CompanionTheory.MetWeightSmooth

end
end

end MetricWeightSmoothness
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm
theorem _root_.GlobalTheory.Adopt.metWeight_isCInf_of_potential : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y) (Δ : Y.Dv) (m : ∀ σ, C.Met Y σ Δ) (hm : ∀ σ y, PosAt (m σ) y) (Q : ∀ a, LocPot (M.X a)), (∀ a, IsPot (I.pt a) (m (I.ε a)) (Q a) ∧ IsPotential (M.A a) (Q a)) → ∀ σ, (metWeight Δ (m σ) (hm σ)).IsCInf := by
  first | exact @MetricWeightSmoothness.GlobalTheory.CompanionTheory.MetWeightSmooth.metWeight_isCInf | exact MetricWeightSmoothness.GlobalTheory.CompanionTheory.MetWeightSmooth.metWeight_isCInf | (intros; apply MetricWeightSmoothness.GlobalTheory.CompanionTheory.MetWeightSmooth.metWeight_isCInf <;> assumption)

end
end

section
namespace HalfMetricWeight
section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Dblock.HalfWeight

theorem half_metWeight_eq : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (σ : F →+* ℂ) (D : ℕ) (A : FinHolAtlas D (Pts Y σ)), IsAlgAtlas A → ∀ (Δ : Y.Dv) (m : C.Met Y σ Δ) (hm : ∀ y, PosAt m y) (Q : LocPot (Pts Y σ)), IsPot id m Q → ∀ (x : Pts Y σ) (c : (toLB Δ).ι), x ∈ ptsIn Y.str σ ((toLB Δ).U c) → ∃ W : Set (Pts Y σ), IsOpen W ∧ x ∈ W ∧ ∃ G : Pts Y σ → ℂ, A.HoloOn W G ∧ ∀ z ∈ W, (metWeight Δ m hm).φ c z / 2 = Q.φ x z + (G z).re := by
  intro F _ _ C Y σ D A hA Δ m hm Q hQ x c hx
  obtain ⟨f, hf⟩ := hQ x
  have hxc : under x ∈ c.1.1 := mem_ptsIn.1 hx
  have hu : UnitAt (under x) (f * (c.1.2 : Y.Fn)) :=
    (c.2.2 _ hxc).generatesAt_iff.1 (hf x (Q.mem_U x)).1
  obtain ⟨U, hU, a, ea⟩ := hu.regAt.exists_fnOf
  have hxU : x ∈ ptsIn Y.str σ U := mem_ptsIn.2 hU
  have hv : ∀ z ∈ ptsIn Y.str σ U, ev Y.str σ U a z = ratVal (f * (c.1.2 : Y.Fn)) z := fun z hz => by
    rw [← ea, ratVal_fnOf hz]
  have hS : IsOpen (ptsIn Y.str σ U ∩ (Q.U x ∩ ptsIn Y.str σ ((toLB Δ).U c))) :=
    (isOpen_ptsIn _).inter ((Q.isOpen_U x).inter (isOpen_ptsIn _))
  have hH : hA.anRead.HoloOn (ptsIn Y.str σ U ∩ (Q.U x ∩ ptsIn Y.str σ ((toLB Δ).U c))) (ev Y.str σ U a) :=
    fun j => (hA.anRead.holoOn_ev U a j).mono fun v hv => ⟨hv.1, hv.2.1⟩
  obtain ⟨W, hW, hxW, hs, G, hG, e⟩ := AnRead.HoloOn.exists_log hH hS ⟨hxU, Q.mem_U x, hx⟩
    (by rw [hv x hxU]; exact ratVal_ne_zero hu)
  refine ⟨W, hW, hxW, G, (hA.holoOn_iff hA.anRead hW).2 hG, fun z hz => ?_⟩
  obtain ⟨hzU, hzQ, hzc⟩ := hs hz
  have hzc' : under z ∈ c.1.1 := mem_ptsIn.1 hzc
  have he := c.2.2 _ hzc'
  obtain ⟨hgen, -, hφ⟩ := hf z hzQ
  have hgen' : Δ.GeneratesAt (under z) f := hgen
  have huz : UnitAt (under z) (f * (c.1.2 : Y.Fn)) := he.generatesAt_iff.1 hgen'
  have hgi := CartierDiv.isEqn_iff_generatesAt_inv.1 he
  have hp := pn_pos_of_generatesAt (C := C) hgi (hm z)
  have hr : 0 < ‖ratVal (f * (c.1.2 : Y.Fn)) z‖ := norm_pos_iff.2 (ratVal_ne_zero huz)
  have e1 : f = (f * (c.1.2 : Y.Fn)) * ((c.1.2 : Y.Fn))⁻¹ := by
    rw [mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), mul_one]
  have e2 : C.pn Y σ Δ m (C.cx Y σ f) z =
      ‖ratVal (f * (c.1.2 : Y.Fn)) z‖ ^ 2 * C.pn Y σ Δ m (C.cx Y σ ((c.1.2 : Y.Fn))⁻¹) z := by
    rw [← C.pn_mul Y σ Δ m _ _ z huz.regAt hgi.regularAt, ← e1]
  have e3 : Q.φ x z = -(Real.log (C.pn Y σ Δ m (C.cx Y σ f) z) / 2) := hφ
  have e4 : (G z).re = Real.log ‖ratVal (f * (c.1.2 : Y.Fn)) z‖ := by rw [e z hz, hv z hzU]
  rw [metWeight_φ, e4, e3, e2, Real.log_mul (pow_pos hr 2).ne' hp.ne', Real.log_pow]
  push_cast
  ring

end GlobalTheory.CompanionTheory.Dblock.HalfWeight

end
end

end HalfMetricWeight
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm
theorem _root_.GlobalTheory.Adopt.half_metWeight_eq_potential_holo : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (σ : F →+* ℂ) (D : ℕ) (A : FinHolAtlas D (Pts Y σ)), IsAlgAtlas A → ∀ (Δ : Y.Dv) (m : C.Met Y σ Δ) (hm : ∀ y, PosAt m y) (Q : LocPot (Pts Y σ)), IsPot id m Q → ∀ (x : Pts Y σ) (c : (toLB Δ).ι), x ∈ ptsIn Y.str σ ((toLB Δ).U c) → ∃ W : Set (Pts Y σ), IsOpen W ∧ x ∈ W ∧ ∃ G : Pts Y σ → ℂ, A.HoloOn W G ∧ ∀ z ∈ W, (metWeight Δ m hm).φ c z / 2 = Q.φ x z + (G z).re := by
  first | exact @HalfMetricWeight.GlobalTheory.CompanionTheory.Dblock.HalfWeight.half_metWeight_eq | exact HalfMetricWeight.GlobalTheory.CompanionTheory.Dblock.HalfWeight.half_metWeight_eq | (intros; apply HalfMetricWeight.GlobalTheory.CompanionTheory.Dblock.HalfWeight.half_metWeight_eq <;> assumption)

end
end

section
namespace PotentialityTransport
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.CarriedPot

theorem isPotential_tAtlas_pullback : ∀ (e : ℕ) (X X' : Type) [TopologicalSpace X] [TopologicalSpace X']
    (A : FinHolAtlas e X) (h : X ≃ₜ X') (P : LocPot X), IsPotential A P →
      IsPotential (tAtlas A h) (P.pullback h.symm h.symm.continuous) := by
  intro e X X' _ _ A h P hP
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · have hs := hP.1 (h.symm x) j
    have e₁ : (P.pullback h.symm h.symm.continuous).φ x ∘ ((tAtlas A h).chart j).symm =
        P.φ (h.symm x) ∘ (A.chart j).symm := funext fun w => by
      simp only [Function.comp_apply, tAtlas_symm, LocPot.pullback, Homeomorph.symm_apply_apply]
    have e₂ : ((tAtlas A h).chart j).target ∩ ((tAtlas A h).chart j).symm ⁻¹'
          (P.pullback h.symm h.symm.continuous).U x =
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U (h.symm x) := by
      ext w
      simp only [Set.mem_inter_iff, Set.mem_preimage, tAtlas_target, tAtlas_symm, LocPot.pullback,
        Homeomorph.symm_apply_apply]
    rw [e₁, e₂]
    exact hs
  · obtain ⟨W, hW, hyW, G, hG, hd⟩ := hP.2 (h.symm x) (h.symm x') (h.symm y) hy
    refine ⟨h.symm ⁻¹' W, hW.preimage h.symm.continuous, hyW, G ∘ h.symm, fun j => ?_, fun z hz => ?_⟩
    · have hs := hG j
      have e₁ : (G ∘ h.symm) ∘ ((tAtlas A h).chart j).symm = G ∘ (A.chart j).symm := funext fun w => by
        simp only [Function.comp_apply, tAtlas_symm, Homeomorph.symm_apply_apply]
      have e₂ : ((tAtlas A h).chart j).target ∩ ((tAtlas A h).chart j).symm ⁻¹' (h.symm ⁻¹' W) =
          (A.chart j).target ∩ (A.chart j).symm ⁻¹' W := by
        ext w
        simp only [Set.mem_inter_iff, Set.mem_preimage, tAtlas_target, tAtlas_symm,
          Homeomorph.symm_apply_apply]
      rw [e₁, e₂]
      exact hs
    · exact hd (h.symm z) hz

end GlobalTheory.CompanionTheory.CarriedPot

end

end PotentialityTransport
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm
theorem _root_.GlobalTheory.Adopt.isPotential_transport_homeomorph : ∀ (e : ℕ) (X X' : Type) [TopologicalSpace X] [TopologicalSpace X'] (A : FinHolAtlas e X) (h : X ≃ₜ X') (P : LocPot X), IsPotential A P → IsPotential (tAtlas A h) (P.pullback h.symm h.symm.continuous) := by
  first | exact @PotentialityTransport.GlobalTheory.CompanionTheory.CarriedPot.isPotential_tAtlas_pullback | exact PotentialityTransport.GlobalTheory.CompanionTheory.CarriedPot.isPotential_tAtlas_pullback | (intros; apply PotentialityTransport.GlobalTheory.CompanionTheory.CarriedPot.isPotential_tAtlas_pullback <;> assumption)

end
end

section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CombChern

section Bundle

variable {X : Scheme.{0}} [IsIntegral X]

theorem presents_zpow {D : CartierDiv X} {L : LB X} {r : L.ι → X.functionFieldˣ} (h : Presents D L r) (n : ℤ) :
    Presents (n • D) (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n) fun j => r (j PUnit.unit) ^ n := by
  have mem : ∀ (j : PUnit → L.ι) {x : X}, x ∈ (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).U j →
      x ∈ L.U (j PUnit.unit) := fun j x hx => by simpa using Set.mem_iInter.1 hx PUnit.unit
  refine ⟨LB.isLB_linComb h.isLB _ _, fun j j' hjj => ?_, fun j x hx => (h.isEqn _ x (mem j hx)).zsmul n⟩
  have l : (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).U j ⊓
      (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).U j' ≤ L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit) :=
    fun x hx => ⟨mem j hx.1, mem j' hx.2⟩
  have hg : (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).g j j' = res l (L.g (j PUnit.unit) (j' PUnit.unit)) ^ n := by
    change ∏ _k : PUnit, _ = _
    exact Fintype.prod_unique _
  have key : ∀ {U : X.Opens} (hU : genericPoint X ∈ U) (u : Γ(X, U)ˣ) (m : ℤ),
      fnOf U hU ((u ^ m : Γ(X, U)ˣ) : Γ(X, U)) = fnOf U hU (u : Γ(X, U)) ^ m := fun hU u m => by
    have e := congrArg Units.val (map_zpow (Units.map (fnOf _ hU).toMonoidHom) u m)
    rw [Units.val_zpow_eq_zpow_val, Units.coe_map, Units.coe_map] at e
    exact e
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, h.isRatSec _ _ (l hjj), mul_zpow, hg, key]
  congr 2
  exact (fnOf_resG l hjj _).symm

end Bundle

section Comb

variable {X : Scheme.{0}} [IsIntegral X] {ι : Type} (T : ι → LB X) (b : ι → ℤ)

noncomputable def cBun : List ι → LB X
  | [] => LB.triv X
  | i :: l => CechPic.tens (LB.LinComb (T i) (K := PUnit) (fun _ => 𝟙 X) fun _ => b i) (cBun l)

noncomputable def cEq (r : ∀ i, (T i).ι → X.functionFieldˣ) : ∀ l, (cBun T b l).ι → X.functionFieldˣ
  | [] => fun _ => 1
  | i :: l => fun q => r i (q.1 PUnit.unit) ^ b i * cEq r l q.2

theorem presents_cBun {D : ι → CartierDiv X} {r : ∀ i, (T i).ι → X.functionFieldˣ}
    (hr : ∀ i, Presents (D i) (T i) (r i)) :
    ∀ l, Presents ((l.map fun i => b i • D i).sum) (cBun T b l) (cEq T b r l)
  | [] => presents_zero
  | i :: l => by
    rw [List.map_cons, List.sum_cons]
    exact (presents_zpow (hr i) (b i)).tens (presents_cBun hr l)

variable {k : Type} [CommRing k] {p : X ⟶ Sp k} {σ : k →+* ℂ}

noncomputable def cWt (ψ : ∀ i, Weight p σ (T i)) : ∀ l, Weight p σ (cBun T b l)
  | [] => Weight.ofFun 0
  | i :: l => ((ψ i).zpow (b i)).tens (cWt ψ l)

theorem isCInf_cWt {ψ : ∀ i, Weight p σ (T i)} (h : ∀ i, (ψ i).IsCInf) : ∀ l, (cWt T b ψ l).IsCInf
  | [] => Weight.isCInf_ofFun fun y => cInfAt_const 0 y
  | i :: l => ((h i).zpow (b i)).tens (isCInf_cWt h l)

noncomputable def cIdx (ψ : ∀ i, Weight p σ (T i)) (x : CxPts p σ) : ∀ l, (cBun T b l).ι
  | [] => PUnit.unit
  | i :: l => (fun _ => pick (ψ i).isLB x, cIdx ψ x l)

theorem mem_cIdx (ψ : ∀ i, Weight p σ (T i)) (x : CxPts p σ) :
    ∀ l, x ∈ ptsIn p σ ((cBun T b l).U (cIdx T b ψ x l))
  | [] => mem_ptsIn_top
  | i :: l => mem_ptsIn_inf.2 ⟨mem_pow_iff.2 (mem_pick (ψ i).isLB x), mem_cIdx ψ x l⟩

theorem cWt_φ (ψ : ∀ i, Weight p σ (T i)) (x z : CxPts p σ) :
    ∀ l, (cWt T b ψ l).φ (cIdx T b ψ x l) z = (l.map fun i => (b i : ℝ) * (ψ i).φ (pick (ψ i).isLB x) z).sum
  | [] => rfl
  | i :: l => by
    rw [List.map_cons, List.sum_cons, ← cWt_φ ψ x z l]
    exact congrArg (· + _) ((ψ i).zpow_φ (b i) _ z)

end Comb

section Met

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

theorem metWeight_isCInf_at {e : ℕ} {M : Man e} (I : ManIs M Y) (a : Fin (M.n + 1)) {Δ : Y.Dv}
    {m : C.Met Y (I.ε a) Δ} (hm : ∀ y, PosAt m y) {Q : LocPot (M.X a)}
    (hQ : IsPot (I.pt a) m Q ∧ IsPotential (M.A a) Q) : (metWeight Δ m hm).IsCInf := by
  intro c y hy
  obtain ⟨x, rfl⟩ := (I.pt a).surjective y
  have hxU : (I.pt a).symm (I.pt a x) ∈ Q.U x := by simpa using Q.mem_U x
  obtain ⟨f, hf⟩ := hQ.1 x
  have key : ∀ z : Pts Y (I.ε a), (I.pt a).symm z ∈ Q.U x → z ∈ ptsIn Y.str (I.ε a) ((toLB Δ).U c) →
      UnitAt (under z) (f * (c.1.2 : Y.Fn)) ∧ (metWeight Δ m hm).φ c z =
        2 * Q.φ x ((I.pt a).symm z) + Real.log (‖ratVal (f * (c.1.2 : Y.Fn)) z‖ ^ 2) := by
    intro z hz hzc
    have hzc' : under z ∈ c.1.1 := mem_ptsIn.1 hzc
    obtain ⟨h₁, h₂, h₃⟩ := hf _ hz
    rw [Homeomorph.apply_symm_apply] at h₁ h₂ h₃
    have he : Δ.IsEqn (under z) c.1.2 := c.2.2 _ hzc'
    have hu := he.generatesAt_iff.1 h₁
    have hgen := CartierDiv.isEqn_iff_generatesAt_inv.1 he
    have hp := pn_pos_of_generatesAt (C := C) hgen (hm z)
    have hr : 0 < ‖ratVal (f * (c.1.2 : Y.Fn)) z‖ ^ 2 := pow_pos (norm_pos_iff.2 (ratVal_ne_zero hu)) 2
    have e₁ : (f * (c.1.2 : Y.Fn)) * (c.1.2 : Y.Fn)⁻¹ = f := by
      rw [mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), mul_one]
    have e₂ := C.pn_mul Y _ Δ m _ _ z hu.regAt hgen.regularAt
    rw [e₁] at e₂
    refine ⟨hu, ?_⟩
    rw [metWeight_φ, h₃, lnN, e₂, Real.log_mul hr.ne' hp.ne']
    ring
  have hS : IsOpen ((I.pt a).symm ⁻¹' Q.U x) := (Q.isOpen_U x).preimage (I.pt a).symm.continuous
  refine (((MetricWeightSmoothness.GlobalTheory.CompanionTheory.MetWeightSmooth.cInfAt_of_smoothOn_tAtlas (isAlgAtlas_tAtlas I a) (Q.isOpen_U x)
    (hQ.2.1 x) hxU).const_mul 2).add
    (MetricWeightSmoothness.GlobalTheory.CompanionTheory.MetWeightSmooth.cInfAt_log_normSq_ratVal (key _ hxU hy).1)).congr ?_
  filter_upwards [hS.mem_nhds hxU, (isOpen_ptsIn _).mem_nhds hy] with z hz hzc
  exact (key z hz hzc).2

end Met

theorem mInt_combPot_eq_inter : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] [NumberField F] (Y : GlobalTheory.ProjVar.Var F)
    (e : ℕ) (M : Man e) (I : ManIs M Y) (a : Fin (M.n + 1)) (ι : Type) [Fintype ι] (Δ : ι → Y.Dv)
    (m : ∀ i (σ : F →+* ℂ), (cxSt F).Met Y σ (Δ i)) (b : ι → ℤ) (Q : ι → LocPot (M.X a)), Y.dim = e →
    (∀ i σ, (cxSt F).mSmooth Y σ (Δ i) (m i σ)) →
    (∀ i, IsPot (I.pt a) (m i (I.ε a)) (Q i) ∧ IsPotential (M.A a) (Q i)) →
    mInt (M.A a) (fun _ => InhabCalc.combPot Q (fun i => (b i : ℝ)) (fun _ => 0)) (fun _ => 1) =
      (Y.inter (fun _ => ∑ i, b i • Δ i) : ℝ) := by
  intro hCD F _ _ Y e M I a ι _ Δ m b Q hdim _ hQ
  subst hdim
  have hm : ∀ i y, PosAt (m i (I.ε a)) y := by
    intro i y
    obtain ⟨x, rfl⟩ := (I.pt a).surjective y
    obtain ⟨f, hf⟩ := (hQ i).1 x
    exact (hf x ((Q i).mem_U x)).2.1
  let ψ : ∀ i, Weight Y.str (I.ε a) (toLB (Δ i)) := fun i => metWeight (Δ i) (m i (I.ε a)) (hm i)
  have hψ : ∀ i, (ψ i).IsCInf := fun i => metWeight_isCInf_at I a (hm i) (hQ i)
  let l := (Finset.univ : Finset ι).toList
  have hp := presents_cBun (fun i => toLB (Δ i)) b (fun i => presents_toLB (Δ i)) l
  have hD : (l.map fun i => b i • Δ i).sum = ∑ i, b i • Δ i := Finset.sum_map_toList _ _
  rw [hD] at hp
  let φ := cWt (fun i => toLB (Δ i)) b ψ l
  have hφ : φ.IsCInf := isCInf_cWt _ b hψ l
  obtain ⟨-, hc⟩ := hCD F Y (I.ε a) _ _ _ hp φ hφ
  have := CxPts.secondCountableTopology_of_isProjOver (I.ε a) Y.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver (I.ε a) Y.isProjOver
  have hA := isAlgAtlas_tAtlas I a
  rw [← hc, ChernMA.chernInt_eq_mInt hφ hA continuous_const]
  let TM : LocPot (M.X a) := InhabCalc.combPot Q (fun i => (b i : ℝ)) (fun _ => 0)
  have hTM : IsPotential (M.A a) TM :=
    InhabCalc.isPotential_combPot _ _ (fun i => (hQ i).2) _ _ (fun _ => contDiffOn_const)
  let T : LocPot (Pts Y (I.ε a)) := TM.pullback (I.pt a).symm (I.pt a).symm.continuous
  have hT : IsPotential (tAtlas (M.A a) (I.pt a)) T :=
    PotentialityTransport.GlobalTheory.CompanionTheory.CarriedPot.isPotential_tAtlas_pullback _ _ _ _ _ _ hTM
  have hsf : SameForm (tAtlas (M.A a) (I.pt a)) φ.locPot T := by
    refine Weight.sameForm_of_re (R := hA.anRead) _ hA hT fun x => ?_
    have h6 := fun i => HalfMetricWeight.GlobalTheory.CompanionTheory.Dblock.HalfWeight.half_metWeight_eq F (cxSt F) Y (I.ε a) _ _ hA (Δ i)
      (m i (I.ε a)) (hm i) _ (IsPot.pullback_symm (hQ i).1) x (pick (ψ i).isLB x) (mem_pick _ x)
    choose W hW hxW G hG hGe using h6
    refine ⟨cIdx _ b ψ x l, mem_cIdx _ b ψ x l, ⋂ i, W i, isOpen_iInter_of_finite hW, Set.mem_iInter.2 hxW,
      fun z => ∑ i, (b i : ℂ) * G i z, (hA.holoOn_iff hA.anRead (isOpen_iInter_of_finite hW)).1 ?_, fun z hz => ?_⟩
    · intro j t ht
      exact Finset.analyticAt_fun_sum _ fun i _ =>
        analyticAt_const.mul (hG i j t ⟨ht.1, Set.mem_iInter.1 ht.2 i⟩)
    · have e1 : ∀ i, (ψ i).φ (pick (ψ i).isLB x) z =
          2 * ((Q i).φ ((I.pt a).symm x) ((I.pt a).symm z) + (G i z).re) := fun i => by
        have := hGe i z (Set.mem_iInter.1 hz i)
        simp only [LocPot.pullback] at this
        linarith
      have e3 : T.φ x z = ∑ i, (b i : ℝ) * (Q i).φ ((I.pt a).symm x) ((I.pt a).symm z) + 0 := rfl
      have e4 : ∀ i, ((b i : ℂ) * G i z).re = (b i : ℝ) * (G i z).re := fun i => by simp
      rw [cWt_φ, Finset.sum_map_toList, e3, Complex.re_sum]
      simp only [e1, e4]
      rw [Finset.sum_div, add_zero, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
  rw [SameForm.mInt_eq (fun _ => hsf), MongeAmpereTransport.GlobalTheory.CompanionTheory.MaTransport.mInt_tAtlas _ _ _ _ _ _ _ (fun _ => hT)
    continuous_const]
  refine InhabCalc.mInt_congr_φ (M.A a) (fun _ => ?_) _
  funext x z
  simp [T, TM, LocPot.pullback]

end GlobalTheory.CombChern
end
end
