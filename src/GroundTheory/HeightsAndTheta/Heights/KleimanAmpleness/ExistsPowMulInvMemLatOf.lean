import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestMore
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockEqChartRing
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AevalEqZeroOfMemSatIdealModel
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver cechZc quotPart cechMap)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomogIdeal)

def QuotSecsBase.Statement : Prop :=
  ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1)) (J : Ideal (MRingOver S ι))
    (hJ : mIdealOver S y ≤ J),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ → IsMultiHomogIdeal J → ∀ β : K → ℤ,
    ∃ (Q : Kleiman.LineBundle S (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (J' : Ideal (Kleiman.Poly S N)),
      (∀ p ∈ J', ∀ d : ℕ, homogeneousComponent d p ∈ J') ∧
      ∀ (c : ℕ), ∀ z'' ∈ cechZc ι (quotPart S J) (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) 0,
        ∃ s : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) → Ω,
          (∀ I, s I ∈ (Q.twist (Kleiman.twistSys S _ (c : ℤ))).sub I) ∧
          (∀ (I₁ I₂ : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)), I₁.1 ⊆ I₂.1 →
            s I₁ - s I₂ ∈ ((Q.twist (Kleiman.twistSys S _ (c : ℤ))).twist (Kleiman.idealSys _ J')).sub I₂) ∧
          ∀ t ∈ (Q.twist (Kleiman.twistSys S _ (c : ℤ))).secs,
            (∀ I, t - s I ∈ ((Q.twist (Kleiman.twistSys S _ (c : ℤ))).twist (Kleiman.idealSys _ J')).sub I) →
            ∃ z ∈ cechZc ι (quotPart S (mIdealOver S y)) (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) 0,
              cechMap S ι (Submodule.factor hJ) 0 z = z''

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver cechZc quotPart cechMap CechC)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomogIdeal)

def QuotCocycleValues.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (J : Ideal (MRingOver S ι))
    (hJ : mIdealOver S y ≤ J) (γ : K → ℤ),
    ∀ z'' ∈ cechZc ι (quotPart S J) γ 0,
      ∃ w : (∀ k, ι k) → Ω,
        (∀ d : ∀ k, ι k, (∀ k, y ⟨k, d k⟩ ≠ 0) → w d * genInv y γ d ∈ chartRingOver S y d) ∧
        (∀ d d' : ∀ k, ι k, (∀ k, y ⟨k, d k⟩ ≠ 0) → (∀ k, y ⟨k, d' k⟩ ≠ 0) →
          (w d - w d') * genInv y γ d ∈
            Submodule.span ↥(chartRingOver S y d ⊔ chartRingOver S y d') (dehom S y J d)) ∧
        ∀ t ∈ secOver S y γ,
          (∀ d : ∀ k, ι k, (∀ k, y ⟨k, d k⟩ ≠ 0) →
            (t - w d) * genInv y γ d ∈ Submodule.span ↥(chartRingOver S y d) (dehom S y J d)) →
          ∃ z ∈ cechZc ι (quotPart S (mIdealOver S y)) γ 0, cechMap S ι (Submodule.factor hJ) 0 z = z''

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)

def QuotChartLift.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (J : Ideal (MRingOver S ι)) (γ : K → ℤ) (w : (∀ k, ι k) → Ω),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ →
    (∀ d : ∀ k, ι k, (∀ k, y ⟨k, d k⟩ ≠ 0) → w d * genInv y γ d ∈ chartRingOver S y d) →
    (∀ d d' : ∀ k, ι k, (∀ k, y ⟨k, d k⟩ ≠ 0) → (∀ k, y ⟨k, d' k⟩ ≠ 0) →
      (w d - w d') * genInv y γ d ∈
        Submodule.span ↥(chartRingOver S y d ⊔ chartRingOver S y d') (dehom S y J d)) →
    ∀ i, baseVec y k₀ e i ≠ 0 → ∃ s : Ω, ∀ d : ∀ k, ι k, (∀ k, y ⟨k, d k⟩ ≠ 0) →
      s * genInv y γ d ∈ overRing (S := S) y k₀ e d i ∧
        (s - w d) * genInv y γ d ∈ Submodule.span ↥(overRing (S := S) y k₀ e d i) (dehom S y J d)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)

def QuotIdealSub.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (J : Ideal (MRingOver S ι)) (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀) (β : K → ℤ) (c : ℤ)
    (I : Kleiman.Chart (baseVec y k₀ e)) (u : Ω),
    (∀ d : ∀ k, ι k, (∀ k, y ⟨k, d k⟩ ≠ 0) →
      u * genInv y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) d ∈
        Submodule.span ↥(chartRingOver S y d ⊔ Kleiman.chartRing S (baseVec y k₀ e) I) (dehom S y J d)) →
    u ∈ (((TranslateEq.ofSecond (bundleOfDeg (e := e) hy β)).twist (Kleiman.twistSys S (baseVec y k₀ e) c)).twist
      (Kleiman.idealSys (baseVec y k₀ e) (satIdeal S y k₀ e J))).sub I

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver cechZc quotPart cechMap)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomogIdeal)

noncomputable section

section Charts

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [Algebra S Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {N : ℕ} {e : ι k₀ ≃ Fin (N + 1)}

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem mem_span_of_le {A B : Subalgebra S Ω} (h : A ≤ B) {s : Set Ω} {v : Ω}
    (hv : v ∈ Submodule.span A s) : v ∈ Submodule.span B s := by
  induction hv using Submodule.span_induction with
  | mem z hz => exact Submodule.subset_span hz
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul a z _ hz =>
    have := Submodule.smul_mem _ (⟨a, h a.2⟩ : B) hz
    rw [Subalgebra.smul_def] at this ⊢
    exact this

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem mul_mem_span {A : Subalgebra S Ω} {s : Set Ω} {a v : Ω} (ha : a ∈ A)
    (hv : v ∈ Submodule.span A s) : a * v ∈ Submodule.span A s := by
  have := Submodule.smul_mem _ (⟨a, ha⟩ : A) hv
  rwa [Subalgebra.smul_def] at this

theorem zpow_ratio_mem_overRing (d : ∀ k, ι k) (i : Fin (N + 1)) (n : ℤ) :
    (y ⟨k₀, d k₀⟩ / baseVec y k₀ e i) ^ n ∈ overRing (S := S) y k₀ e d i := by
  refine zpow_mem_of_inv_mem _ ?_ ?_ n
  · have : y ⟨k₀, d k₀⟩ / baseVec y k₀ e i = baseVec y k₀ e (e (d k₀)) / baseVec y k₀ e i := by
      simp [IndefiniteRowSideFullHecke.Kleiman2.blockVec]
    rw [this]
    exact chartRing_le_overRing d i (ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing _ i _)
  · rw [inv_div]
    exact chartRingOver_le_overRing d i (div_mem_chartRingOver d k₀ (e.symm i))

theorem mem_twist_single (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀) (β : K → ℤ) (c : ℤ) {i : Fin (N + 1)}
    (hi : baseVec y k₀ e i ≠ 0) (t : Ω) :
    t ∈ ((TranslateEq.ofSecond (bundleOfDeg (e := e) hy β)).twist (Kleiman.twistSys S (baseVec y k₀ e) c)).sub
        (Kleiman.singleChart hi) ↔
      ∀ d : ∀ k, ι k, (∀ k, y ⟨k, d k⟩ ≠ 0) →
        t * genInv y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) d ∈ overRing (S := S) y k₀ e d i := by
  rw [TranslateEq.mem_twist_twistSys_iff (TranslateEq.ofSecond (bundleOfDeg (e := e) hy β)).toSubSystem c
    (Kleiman.singleChart hi) (Finset.mem_singleton_self i)]
  constructor
  · rintro ⟨u, hu, rfl⟩ d hd
    have hu' : u ∈ latOf (S := S) y k₀ e β i := (ofSecond_sub_single (bundleOfDeg (e := e) hy β) hi u).1 hu
    have h1 := (mem_latOf β i u).1 hu' d hd
    rw [genInv_add_baseDeg β c hd]
    have heq : baseVec y k₀ e i ^ c • u * (genInv y β d * y ⟨k₀, d k₀⟩ ^ (-c)) =
        (y ⟨k₀, d k₀⟩ / baseVec y k₀ e i) ^ (-c) * (u * genInv y β d) := by
      have ha : baseVec y k₀ e i ^ c ≠ 0 := zpow_ne_zero c hi
      have hb : y ⟨k₀, d k₀⟩ ^ c ≠ 0 := zpow_ne_zero c (hd k₀)
      rw [smul_eq_mul, div_zpow]
      simp only [zpow_neg]
      field_simp
    rw [heq]
    exact mul_mem (zpow_ratio_mem_overRing d i (-c)) h1
  · intro h
    refine ⟨baseVec y k₀ e i ^ (-c) * t, ?_, ?_⟩
    · refine (ofSecond_sub_single (bundleOfDeg (e := e) hy β) hi _).2 ((mem_latOf β i _).2 fun d hd => ?_)
      have h1 := h d hd
      rw [genInv_add_baseDeg β c hd] at h1
      have heq : baseVec y k₀ e i ^ (-c) * t * genInv y β d =
          (y ⟨k₀, d k₀⟩ / baseVec y k₀ e i) ^ c * (t * (genInv y β d * y ⟨k₀, d k₀⟩ ^ (-c))) := by
        have ha : baseVec y k₀ e i ^ c ≠ 0 := zpow_ne_zero c hi
        have hb : y ⟨k₀, d k₀⟩ ^ c ≠ 0 := zpow_ne_zero c (hd k₀)
        rw [div_zpow, zpow_neg, zpow_neg]
        field_simp
      rw [heq]
      exact mul_mem (zpow_ratio_mem_overRing d i c) h1
    · rw [smul_eq_mul, ← mul_assoc, ← zpow_add₀ hi, add_neg_cancel, zpow_zero, one_mul]

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem aeval_ratio_monos {i : Fin (N + 1)} (hi : baseVec y k₀ e i ≠ 0) {s : Kleiman.Poly S N}
    (hs : s ∈ Kleiman.monos ({i} : Finset (Fin (N + 1)))) :
    aeval (fun j => baseVec y k₀ e j / baseVec y k₀ e i) s = 1 := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨j, hj, rfl⟩ := ha
    have hj' : j = i := by simpa using hj
    rw [hj', aeval_X, div_self hi]
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul, ha, hb, mul_one]

theorem mem_span_of_mem_idealMod {J : Ideal (MRingOver S ι)} {i : Fin (N + 1)} (hi : baseVec y k₀ e i ≠ 0)
    {q : Ω} (hq : q ∈ Kleiman.idealMod (x := baseVec y k₀ e) (satIdeal S y k₀ e J) (Kleiman.singleChart hi))
    {d : ∀ k, ι k} (hd : ∀ k, y ⟨k, d k⟩ ≠ 0) :
    q ∈ Submodule.span (overRing (S := S) y k₀ e d i) (dehom S y J d) := by
  induction hq using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨f, s, n, hf, hs, hfn, hsn, rfl⟩ := hz
    have h1 := Kleiman.aeval_div_of_isHomogeneous (x := baseVec y k₀ e) hfn i
    have h2 := Kleiman.aeval_div_of_isHomogeneous (x := baseVec y k₀ e) hsn i
    rw [aeval_ratio_monos hi hs] at h2
    have hxn : baseVec y k₀ e i ^ n ≠ 0 := pow_ne_zero n hi
    have hf' : aeval (baseVec y k₀ e) f = baseVec y k₀ e i ^ n *
        aeval (fun j => baseVec y k₀ e j / baseVec y k₀ e i) f := by
      rw [h1]; field_simp
    have hs' : aeval (baseVec y k₀ e) s = baseVec y k₀ e i ^ n := by
      field_simp at h2; exact h2.symm
    rw [hf', hs', mul_div_cancel_left₀ _ hxn]
    exact aeval_mem_of_mem_satIdeal hf hi hd
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul a z _ hz =>
    rw [Kleiman.chartRing_smul_def]
    have ha : (a : Ω) ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y k₀ e) i := by
      rw [TranslateEq.chartRing.equiv (S := S) (baseVec y k₀ e) hi]; exact a.2
    exact mul_mem_span (chartRing_le_overRing d i ha) hz

theorem mem_ideal_single (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀) (β : K → ℤ) (c : ℤ)
    {J : Ideal (MRingOver S ι)} {i : Fin (N + 1)} (hi : baseVec y k₀ e i ≠ 0) {u : Ω}
    (hu : u ∈ (((TranslateEq.ofSecond (bundleOfDeg (e := e) hy β)).twist (Kleiman.twistSys S (baseVec y k₀ e) c)).twist
      (Kleiman.idealSys (baseVec y k₀ e) (satIdeal S y k₀ e J))).sub (Kleiman.singleChart hi))
    {d : ∀ k, ι k} (hd : ∀ k, y ⟨k, d k⟩ ≠ 0) :
    u * genInv y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) d ∈
      Submodule.span (overRing (S := S) y k₀ e d i) (dehom S y J d) := by
  induction hu using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨q, hq, a, ha, rfl⟩ := hz
    have ha' := (mem_twist_single hy β c hi a).1 ha d hd
    rw [smul_eq_mul, mul_assoc, mul_comm]
    exact mul_mem_span ha' (mem_span_of_mem_idealMod hi hq hd)
  | zero => rw [zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | smul a z _ hz =>
    rw [Kleiman.chartRing_smul_def, mul_assoc]
    have ha : (a : Ω) ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y k₀ e) i := by
      rw [TranslateEq.chartRing.equiv (S := S) (baseVec y k₀ e) hi]; exact a.2
    exact mul_mem_span (chartRing_le_overRing d i ha) hz

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem overRing_le_chart (d : ∀ k, ι k) (I : Kleiman.Chart (baseVec y k₀ e)) {i : Fin (N + 1)} (hi : i ∈ I.1) :
    overRing (S := S) y k₀ e d i ≤ chartRingOver S y d ⊔ Kleiman.chartRing S (baseVec y k₀ e) I := by
  refine sup_le le_sup_left (le_trans ?_ le_sup_right)
  refine Algebra.adjoin_le ?_
  rintro _ ⟨j, rfl⟩
  exact TranslateEq.div_mem_chartRing_of_mem I hi j

end Charts

theorem QuotSecsBase.proof (hV : QuotCocycleValues.Statement) (hL : QuotChartLift.Statement)
    (hI : QuotIdealSub.Statement) : QuotSecsBase.Statement := by
  intro S _ _ K _ _ ι _ _ Ω _ _ y k₀ N e J hJ hy _ β
  set x := baseVec y k₀ e with hx
  refine ⟨TranslateEq.ofSecond (bundleOfDeg (e := e) hy β), satIdeal S y k₀ e J,
    fun p hp n => homogeneousComponent_mem_satIdeal hp n, fun c z'' hz'' => ?_⟩
  have hγ : β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ = β + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ := by
    rw [natCast_zsmul]
  rw [hγ] at hz'' ⊢
  set γ := β + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ with hγdef
  obtain ⟨w, hwa, hwb, hwc⟩ := hV S K ι Ω y J hJ γ z'' hz''
  have hlift := hL S K ι Ω y k₀ N e J γ w hy hwa hwb
  choose sf hsf using hlift
  have hpick : ∀ I : Kleiman.Chart x, ∃ i, i ∈ I.1 := fun I => I.2.1
  choose pick hpick using hpick
  have hxp : ∀ I : Kleiman.Chart x, x (pick I) ≠ 0 := fun I => (Kleiman.mem_support x).1 (I.2.2 (hpick I))
  have hsingle : ∀ {i} (hi : x i ≠ 0), pick (Kleiman.singleChart hi) = i := fun {i} hi => by
    simpa [Kleiman.singleChart] using hpick (Kleiman.singleChart hi)
  refine ⟨fun I => sf (pick I) (hxp I), fun I => ?_, fun I₁ I₂ h12 => ?_, fun t ht htI => ?_⟩
  ·
    have h1 := (mem_twist_single (S := S) hy β (c : ℤ) (hxp I) _).2 fun d hd => (hsf _ (hxp I) d hd).1
    refine SubSystem.mono _ (Kleiman.singleChart (hxp I)) I ?_ _ h1
    exact Finset.singleton_subset_iff.2 (hpick I)
  ·
    refine hI S K ι Ω y k₀ N e J hy β (c : ℤ) I₂ _ fun d hd => ?_
    have h1 := (hsf _ (hxp I₁) d hd).2
    have h2 := (hsf _ (hxp I₂) d hd).2
    have h1' := mem_span_of_le (overRing_le_chart d I₂ (h12 (hpick I₁))) h1
    have h2' := mem_span_of_le (overRing_le_chart d I₂ (hpick I₂)) h2
    have := sub_mem h1' h2'
    rw [← sub_mul, sub_sub_sub_cancel_right] at this
    exact this
  ·
    refine hwc t ?_ fun d hd => ?_
    ·
      simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
        Subalgebra.mem_toSubmodule]
      intro d hd
      have hi : x (e (d k₀)) ≠ 0 := by simpa [hx, IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hd k₀
      have h1 := (mem_twist_single (S := S) hy β (c : ℤ) hi t).1
        ((Submodule.mem_iInf _).1 ht (Kleiman.singleChart hi)) d hd
      rw [overRing_self] at h1
      exact h1
    · have hi : x (e (d k₀)) ≠ 0 := by simpa [hx, IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hd k₀
      have h1 := mem_ideal_single hy β (c : ℤ) hi (htI (Kleiman.singleChart hi)) hd
      have key : ∀ j (hj : x j ≠ 0), j = e (d k₀) → (sf j hj - w d) * genInv y γ d ∈
          Submodule.span (overRing (S := S) y k₀ e d (e (d k₀))) (dehom S y J d) := by
        intro j hj hj'
        subst hj'
        exact (hsf _ hj d hd).2
      have h2 := key _ (hxp (Kleiman.singleChart hi)) (hsingle hi)
      have h3 := add_mem h1 h2
      rw [← add_mul, sub_add_sub_cancel, overRing_self] at h3
      exact h3

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

namespace PullSecsModel

section Loc

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

theorem self_mem_fracSub (A : Subalgebra S Ω) (P : Ideal A) [hP : P.IsPrime] {r : Ω} (hr : r ∈ A) :
    r ∈ fracSub A P :=
  ⟨⟨r, hr⟩, 1, one_not_mem_of_prime hP, by simp⟩

theorem mem_of_forall_fracSub (A : Subalgebra S Ω) (a : Ω)
    (h : ∀ (P : Ideal A) [P.IsPrime], a ∈ fracSub A P) : a ∈ A := by
  by_contra ha
  have hJ : mulMemIdeal A a ≠ ⊤ := by
    intro hJ
    apply ha
    have h1 : (1 : A) ∈ mulMemIdeal A a := hJ ▸ Submodule.mem_top
    change ((1 : A) : Ω) * a ∈ A at h1
    rwa [OneMemClass.coe_one, one_mul] at h1
  obtain ⟨P, hP, hJP⟩ := Ideal.exists_le_maximal _ hJ
  have := hP.isPrime
  obtain ⟨u, v, hv, huv⟩ : ∃ u v : A, v ∉ P ∧ a = (u : Ω) / v := h P
  apply hv (hJP _)
  change (v : Ω) * a ∈ A
  rw [huv, mul_div_cancel₀ _ (coe_ne_zero_of_not_mem hv)]
  exact u.2

theorem locIn_comap_le_fracSub {A B : Subalgebra S Ω} (hAB : A ≤ B) (P : Ideal B) [P.IsPrime] (u : Ω)
    (hu : u ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A (P.comap (Subalgebra.inclusion hAB))) : u ∈ fracSub B P := by
  obtain ⟨a, b, hb, rfl⟩ := mem_locIn.mp hu
  exact ⟨Subalgebra.inclusion hAB a, Subalgebra.inclusion hAB b, hb, rfl⟩

end Loc

section Join

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]
  {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)]
  {K₀ : Type} [Fintype K₀] [DecidableEq K₀] {ι₀ : K₀ → Type} [∀ k, Fintype (ι₀ k)]
  {y₁ : (Σ k, ι₁ k) → Ω} {y₀ : (Σ k, ι₀ k) → Ω} {k₀ : K₀} {N N' : ℕ} {e : ι₀ k₀ ≃ Fin (N + 1)}
  {x' : Fin (N' + 1) → Ω}

variable (S y₁ y₀) in

abbrev joinRing (c₁ : ∀ k, ι₁ k) (c₀ : ∀ k, ι₀ k) : Subalgebra S Ω :=
  chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.joinVec y₁ y₀) (IndefiniteRowSideFullHecke.Kleiman2.joinChart c₁ c₀)

omit [Fintype K₁] [∀ k, Fintype (ι₁ k)] [Fintype K₀] [DecidableEq K₀] [∀ k, Fintype (ι₀ k)] in
theorem chartRingOver_le_join₁ (c₁ : ∀ k, ι₁ k) (c₀ : ∀ k, ι₀ k) :
    chartRingOver S y₁ c₁ ≤ joinRing S y₁ y₀ c₁ c₀ :=
  Algebra.adjoin_le (by rintro _ ⟨⟨k, a⟩, rfl⟩; exact Algebra.subset_adjoin ⟨⟨Sum.inl k, a⟩, rfl⟩)

omit [Fintype K₁] [∀ k, Fintype (ι₁ k)] [Fintype K₀] [DecidableEq K₀] [∀ k, Fintype (ι₀ k)] in
theorem chartRingOver_le_join₀ (c₁ : ∀ k, ι₁ k) (c₀ : ∀ k, ι₀ k) :
    chartRingOver S y₀ c₀ ≤ joinRing S y₁ y₀ c₁ c₀ :=
  Algebra.adjoin_le (by rintro _ ⟨⟨k, a⟩, rfl⟩; exact Algebra.subset_adjoin ⟨⟨Sum.inr k, a⟩, rfl⟩)

omit [Fintype K₁] [∀ k, Fintype (ι₁ k)] [Fintype K₀] [DecidableEq K₀] [∀ k, Fintype (ι₀ k)] in

theorem joinRing_le (c₁ : ∀ k, ι₁ k) (c₀ : ∀ k, ι₀ k) (T : Subalgebra S Ω) (h₁ : chartRingOver S y₁ c₁ ≤ T)
    (h₀ : chartRingOver S y₀ c₀ ≤ T) : joinRing S y₁ y₀ c₁ c₀ ≤ T := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨⟨k | k, a⟩, rfl⟩
  · exact h₁ (Algebra.subset_adjoin ⟨⟨k, a⟩, rfl⟩)
  · exact h₀ (Algebra.subset_adjoin ⟨⟨k, a⟩, rfl⟩)

omit [∀ k, Fintype (ι₁ k)] [DecidableEq K₀] [∀ k, Fintype (ι₀ k)] in

theorem prod_pullDeg (c₁ : ∀ k, ι₁ k) (c₀ : ∀ k, ι₀ k) (β : K₀ → ℤ) :
    ∏ k, IndefiniteRowSideFullHecke.Kleiman2.joinVec y₁ y₀ ⟨k, IndefiniteRowSideFullHecke.Kleiman2.joinChart c₁ c₀ k⟩ ^ (-IndefiniteRowSideFullHecke.Kleiman2.pullDeg β k) =
      genInv y₀ β c₀ := by
  rw [Fintype.prod_sum_type]
  simp [IndefiniteRowSideFullHecke.Kleiman2.pullDeg, genInv, IndefiniteRowSideFullHecke.Kleiman2.joinVec, IndefiniteRowSideFullHecke.Kleiman2.joinChart]

omit [∀ k, Fintype (ι₁ k)] [DecidableEq K₀] [∀ k, Fintype (ι₀ k)] in

theorem mem_secOver_join_iff (β : K₀ → ℤ) (t : Ω) :
    t ∈ secOver S (IndefiniteRowSideFullHecke.Kleiman2.joinVec y₁ y₀) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β) ↔
      ∀ (c₁ : ∀ k, ι₁ k) (c₀ : ∀ k, ι₀ k), (∀ k, y₁ ⟨k, c₁ k⟩ ≠ 0) → (∀ k, y₀ ⟨k, c₀ k⟩ ≠ 0) →
        t * genInv y₀ β c₀ ∈ joinRing S y₁ y₀ c₁ c₀ := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  constructor
  · intro h c₁ c₀ h₁ h₀
    have := h (IndefiniteRowSideFullHecke.Kleiman2.joinChart c₁ c₀) (by rintro (k | k); exacts [h₁ k, h₀ k])
    rwa [prod_pullDeg] at this
  · intro h c hc
    obtain ⟨c₁, c₀, rfl⟩ : ∃ (c₁ : ∀ k, ι₁ k) (c₀ : ∀ k, ι₀ k), c = IndefiniteRowSideFullHecke.Kleiman2.joinChart c₁ c₀ :=
      ⟨fun k => c (Sum.inl k), fun k => c (Sum.inr k), by funext k; rcases k with k | k <;> rfl⟩
    rw [prod_pullDeg]
    exact h c₁ c₀ (fun k => hc (Sum.inl k)) (fun k => hc (Sum.inr k))

omit [Fintype K₁] [∀ k, Fintype (ι₁ k)] in
theorem baseVec_e (c₀ : ∀ k, ι₀ k) : baseVec y₀ k₀ e (e (c₀ k₀)) = y₀ ⟨k₀, c₀ k₀⟩ := by
  rw [baseVec_apply, Equiv.symm_apply_apply]

omit [Fintype K₁] [∀ k, Fintype (ι₁ k)] in

theorem domRing_le_join (hsame : IndefiniteRowSideFullHecke.Kleiman2.SameModel S y₁ (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x'))
    (c₁ : ∀ k, ι₁ k) (c₀ : ∀ k, ι₀ k) (h₁ : ∀ k, y₁ ⟨k, c₁ k⟩ ≠ 0) (h₀ : ∀ k, y₀ ⟨k, c₀ k⟩ ≠ 0) {b : Ω}
    (hb : b ∈ Kleiman.domRing S (baseVec y₀ k₀ e) x' (e (c₀ k₀))) : b ∈ joinRing S y₁ y₀ c₁ c₀ := by
  refine mem_of_forall_fracSub _ b fun P _ => ?_
  have hle₁ := chartRingOver_le_join₁ (S := S) (y₁ := y₁) (y₀ := y₀) c₁ c₀
  have hz : IndefiniteRowSideFullHecke.Kleiman2.locIn _ (P.comap (Subalgebra.inclusion hle₁)) ∈
      IndefiniteRowSideFullHecke.Kleiman2.modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') := by
    rw [← hsame]
    exact ⟨c₁, h₁, _, inferInstance, rfl⟩
  obtain ⟨c', hc', p', hp', hz'⟩ := hz
  have hT : ∀ u ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') c') p',
      u ∈ fracSub (joinRing S y₁ y₀ c₁ c₀) P := by
    intro u hu
    rw [← hz'] at hu
    exact locIn_comap_le_fracSub hle₁ P u hu
  have hi' : x' (c' ()) ≠ 0 := hc' ()
  have hi : baseVec y₀ k₀ e (e (c₀ k₀)) ≠ 0 := by rw [baseVec_e]; exact h₀ k₀
  have hpair : pairRing S x' (baseVec y₀ k₀ e) (c' ()) (e (c₀ k₀)) ≤ fracSub (joinRing S y₁ y₀ c₁ c₀) P := by
    refine Algebra.adjoin_le ?_
    rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · have := hp'
      exact hT _ (subset_locIn _ p' (Algebra.subset_adjoin ⟨⟨(), a⟩, rfl⟩))
    · refine self_mem_fracSub _ P ?_
      have : baseVec y₀ k₀ e a / baseVec y₀ k₀ e (e (c₀ k₀)) = y₀ ⟨k₀, e.symm a⟩ / y₀ ⟨k₀, c₀ k₀⟩ := by
        rw [baseVec_e, baseVec_apply]
      show baseVec y₀ k₀ e a / baseVec y₀ k₀ e (e (c₀ k₀)) ∈ _
      rw [this]
      exact chartRingOver_le_join₀ c₁ c₀ (div_mem_chartRingOver c₀ k₀ _)
  exact hpair (mem_pairRing_of_mem_domRing hi' hi hb)

omit [Fintype K₁] [∀ k, Fintype (ι₁ k)] in

theorem exists_pow_mul_inv_mem_latOf (β : K₀ → ℤ) (i : Fin (N + 1))
    (f : ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y₀ k₀ e) i) {d : ∀ k, ι₀ k}
    (hdle : chartRingOver S y₀ d ≤ powMulMem _ (f : Ω) f.2) :
    ∃ n : ℕ, (f : Ω) ^ n * (genInv y₀ β d)⁻¹ ∈ latOf (S := S) y₀ k₀ e β i := by
  have hM : ∀ d' : ∀ k, ι₀ k, ∃ M : ℕ, (∀ k, y₀ ⟨k, d' k⟩ ≠ 0) →
      (f : Ω) ^ M * ((genInv y₀ β d)⁻¹ * genInv y₀ β d') ∈ overRing (S := S) y₀ k₀ e d' i := by
    intro d'
    by_cases hd' : ∀ k, y₀ ⟨k, d' k⟩ ≠ 0
    · have hfB : (f : Ω) ∈ overRing (S := S) y₀ k₀ e d' i := chartRing_le_overRing d' i f.2
      have hdP : chartRingOver S y₀ d ≤ powMulMem _ (f : Ω) hfB :=
        hdle.trans (powMulMem_mono (chartRing_le_overRing d' i) f.2)
      have hd'P : chartRingOver S y₀ d' ≤ powMulMem _ (f : Ω) hfB :=
        (chartRingOver_le_overRing d' i).trans (le_powMulMem _ hfB)
      have hratio : (genInv y₀ β d)⁻¹ * genInv y₀ β d' = ∏ k, (y₀ ⟨k, d k⟩ / y₀ ⟨k, d' k⟩) ^ β k := by
        rw [inv_mul_eq_div]
        simp only [genInv]
        rw [← Finset.prod_div_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [zpow_neg, zpow_neg, inv_div_inv, div_zpow]
      have hrP : (genInv y₀ β d)⁻¹ * genInv y₀ β d' ∈ powMulMem _ (f : Ω) hfB := by
        rw [hratio]
        refine Subalgebra.prod_mem _ fun k _ => zpow_mem_of_inv_mem _ ?_ ?_ _
        · exact hd'P (div_mem_chartRingOver d' k _)
        · rw [inv_div]; exact hdP (div_mem_chartRingOver d k _)
      obtain ⟨M, hM⟩ := hrP
      exact ⟨M, fun _ => hM⟩
    · exact ⟨0, fun h => absurd h hd'⟩
  choose M hM using hM
  refine ⟨∑ d', M d', fun d' hd' => ?_⟩
  rw [mul_assoc]
  exact pow_mul_mem_of_le _ (chartRing_le_overRing d' i f.2)
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ d')) (hM d' hd')

omit [Fintype K₁] [∀ k, Fintype (ι₁ k)] in

theorem secs_bundleOfDeg (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y₀ k₀) (β : K₀ → ℤ) (c : ℤ) :
    ((TranslateEq.ofSecond (bundleOfDeg (e := e) hy β)).twist (Kleiman.twistSys S (baseVec y₀ k₀ e) c)).secs =
      secOver S y₀ (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := by
  ext t
  rw [mem_secs_iff]
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  constructor
  · intro h d hd
    have hi : baseVec y₀ k₀ e (e (d k₀)) ≠ 0 := by rw [baseVec_e]; exact hd k₀
    have h1 := (mem_twist_single hy β c hi t).mp (h _ hi) d hd
    rw [overRing_self] at h1
    exact h1
  · intro h i hi
    exact (mem_twist_single hy β c hi t).mpr fun d hd => chartRingOver_le_overRing d i (h d hd)

omit [Fintype K₁] [∀ k, Fintype (ι₁ k)] in

theorem mem_sub_iff_latOf [IsNoetherianRing S] (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y₀ k₀) (β : K₀ → ℤ)
    (Q : Kleiman.LineBundle S (baseVec y₀ k₀ e))
    (hQ : ∀ c : ℤ, (Q.twist (Kleiman.twistSys S (baseVec y₀ k₀ e) c)).secs =
      secOver S y₀ (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀))
    {i : Fin (N + 1)} (hi : baseVec y₀ k₀ e i ≠ 0) (l : Ω) :
    l ∈ Q.sub (Kleiman.singleChart hi) ↔ l ∈ latOf (S := S) y₀ k₀ e β i := by
  obtain ⟨c₁, h₁⟩ := Kleiman.Generated.full S Ω N (baseVec y₀ k₀ e) Q
  obtain ⟨c₂, h₂⟩ := Kleiman.Generated.full S Ω N (baseVec y₀ k₀ e) (TranslateEq.ofSecond (bundleOfDeg (e := e) hy β))
  have heq : (Q.twist (Kleiman.twistSys S (baseVec y₀ k₀ e) (max c₁ c₂))).sub (Kleiman.singleChart hi) =
      ((TranslateEq.ofSecond (bundleOfDeg (e := e) hy β)).twist
        (Kleiman.twistSys S (baseVec y₀ k₀ e) (max c₁ c₂))).sub (Kleiman.singleChart hi) := by
    rw [← h₁ _ (le_max_left _ _), ← h₂ _ (le_max_right _ _), hQ, secs_bundleOfDeg]
  have hiI : i ∈ (Kleiman.singleChart hi).1 := Finset.mem_singleton_self i
  have hxc : baseVec y₀ k₀ e i ^ (max c₁ c₂) ≠ 0 := zpow_ne_zero _ hi
  change l ∈ Q.sub (Kleiman.singleChart hi) ↔ l ∈ (bundleOfDeg (e := e) hy β).lat i
  rw [← ofSecond_sub_single (bundleOfDeg (e := e) hy β) hi l]
  constructor
  · intro hl
    have h1 := (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem (max c₁ c₂) _ hiI _).mpr ⟨l, hl, rfl⟩
    rw [heq] at h1
    obtain ⟨u, hu, hul⟩ := (TranslateEq.mem_twist_twistSys_iff _ (max c₁ c₂) _ hiI _).mp h1
    rw [smul_eq_mul, smul_eq_mul, mul_right_inj' hxc] at hul
    rwa [hul]
  · intro hl
    have h1 := (TranslateEq.mem_twist_twistSys_iff (TranslateEq.ofSecond (bundleOfDeg (e := e) hy β)).toSubSystem
      (max c₁ c₂) _ hiI _).mpr ⟨l, hl, rfl⟩
    rw [← heq] at h1
    obtain ⟨u, hu, hul⟩ := (TranslateEq.mem_twist_twistSys_iff _ (max c₁ c₂) _ hiI _).mp h1
    rw [smul_eq_mul, smul_eq_mul, mul_right_inj' hxc] at hul
    rwa [hul]

omit [Fintype K₁] [∀ k, Fintype (ι₁ k)] [Fintype K₀] [DecidableEq K₀] [∀ k, Fintype (ι₀ k)] in

theorem exists_chart₁ (hsame : IndefiniteRowSideFullHecke.Kleiman2.SameModel S y₁ (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x')) {i' : Fin (N' + 1)}
    (hi' : x' i' ≠ 0) (i : Fin (N + 1)) (P : Ideal (pairRing S x' (baseVec y₀ k₀ e) i' i)) [P.IsPrime] :
    ∃ c₁ : ∀ k, ι₁ k, (∀ k, y₁ ⟨k, c₁ k⟩ ≠ 0) ∧
      chartRingOver S y₁ c₁ ≤ fracSub (pairRing S x' (baseVec y₀ k₀ e) i' i) P := by
  have hC' : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (fun _ => i') ≤ pairRing S x' (baseVec y₀ k₀ e) i' i :=
    Algebra.adjoin_le (by rintro _ ⟨⟨⟨⟩, a⟩, rfl⟩; exact Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩))
  have hz : IndefiniteRowSideFullHecke.Kleiman2.locIn _ (P.comap (Subalgebra.inclusion hC')) ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts S y₁ := by
    rw [hsame]
    exact ⟨fun _ => i', fun _ => hi', _, inferInstance, rfl⟩
  obtain ⟨c₁, hc₁, p₁, hp₁, hz₁⟩ := hz
  refine ⟨c₁, hc₁, fun r hr => ?_⟩
  have := hp₁
  have hr' := subset_locIn _ p₁ hr
  rw [← hz₁] at hr'
  exact locIn_comap_le_fracSub hC' P r hr'

omit [Fintype K₁] [∀ k, Fintype (ι₁ k)] in

theorem exists_chart₀ (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y₀ k₀) (i' : Fin (N' + 1)) {i : Fin (N + 1)}
    (hi : baseVec y₀ k₀ e i ≠ 0) (P : Ideal (pairRing S x' (baseVec y₀ k₀ e) i' i)) [P.IsPrime] :
    ∃ f : ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y₀ k₀ e) i, (f : Ω) ≠ 0 ∧ ∃ d : ∀ k, ι₀ k, (∀ k, y₀ ⟨k, d k⟩ ≠ 0) ∧
      chartRingOver S y₀ d ≤ powMulMem _ (f : Ω) f.2 ∧
      chartRingOver S y₀ d ≤ fracSub (pairRing S x' (baseVec y₀ k₀ e) i' i) P ∧
      ∀ n : ℕ, ((f : Ω) ^ n)⁻¹ ∈ fracSub (pairRing S x' (baseVec y₀ k₀ e) i' i) P := by
  have hGD : ReciprocityTheory.ChartRestriction.G.Geo.chartRing S (baseVec y₀ k₀ e) i ≤ pairRing S x' (baseVec y₀ k₀ e) i' i :=
    (TranslateEq.chartRing.equiv S _ hi).le.trans (chartRing_le_pairRing i' hi)
  obtain ⟨f, hf, d, hd, hdle⟩ := exists_basic hy hi (P.comap (Subalgebra.inclusion hGD))
  have hf0 : (f : Ω) ≠ 0 := coe_ne_zero_of_not_mem hf
  have hfP : ∀ M : ℕ, Subalgebra.inclusion hGD (f ^ M) ∉ P := by
    intro M hM
    rw [map_pow] at hM
    exact hf (Ideal.mem_comap.mpr (Ideal.IsPrime.mem_of_pow_mem inferInstance M hM))
  refine ⟨f, hf0, d, hd, hdle, fun r hr => ?_, fun n => ?_⟩
  · obtain ⟨M, hM⟩ := hdle hr
    refine ⟨Subalgebra.inclusion hGD ⟨_, hM⟩, Subalgebra.inclusion hGD (f ^ M), hfP M, ?_⟩
    rw [Subalgebra.coe_inclusion, Subalgebra.coe_inclusion, SubmonoidClass.coe_pow]
    exact (mul_div_cancel_left₀ r (pow_ne_zero M hf0)).symm
  · refine ⟨1, Subalgebra.inclusion hGD (f ^ n), hfP n, ?_⟩
    rw [OneMemClass.coe_one, Subalgebra.coe_inclusion, SubmonoidClass.coe_pow, one_div]

theorem mem_secOver_of_mem_pullSecs [IsNoetherianRing S] (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y₀ k₀)
    (hsame : IndefiniteRowSideFullHecke.Kleiman2.SameModel S y₁ (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x')) (β : K₀ → ℤ)
    (Q : Kleiman.LineBundle S (baseVec y₀ k₀ e))
    (hQ : ∀ c : ℤ, (Q.twist (Kleiman.twistSys S (baseVec y₀ k₀ e) c)).secs =
      secOver S y₀ (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀))
    (t : Ω) (ht : t ∈ Kleiman.pullSecs x' Q.toSubSystem) :
    t ∈ secOver S (IndefiniteRowSideFullHecke.Kleiman2.joinVec y₁ y₀) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β) := by
  rw [mem_secOver_join_iff]
  intro c₁ c₀ h₁ h₀
  have hi : baseVec y₀ k₀ e (e (c₀ k₀)) ≠ 0 := by rw [baseVec_e]; exact h₀ k₀
  simp only [Kleiman.pullSecs, Submodule.mem_iInf] at ht
  have ht' := ht _ hi
  clear ht
  induction ht' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, hb, l, hl, rfl⟩ := hz
    have hl' := (mem_latOf β _ l).mp ((mem_sub_iff_latOf hy β Q hQ hi l).mp hl) c₀ h₀
    rw [overRing_self] at hl'
    rw [mul_assoc]
    exact Subalgebra.mul_mem _ (domRing_le_join hsame c₁ c₀ h₁ h₀ hb) (chartRingOver_le_join₀ c₁ c₀ hl')
  | zero => rw [zero_mul]; exact Subalgebra.zero_mem _
  | add u v _ _ hu hv => rw [add_mul]; exact Subalgebra.add_mem _ hu hv
  | smul r u _ hu =>
    rw [Algebra.smul_def, mul_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ r) hu

theorem mem_pullSecs_of_mem_secOver [IsNoetherianRing S] (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y₀ k₀)
    (hsame : IndefiniteRowSideFullHecke.Kleiman2.SameModel S y₁ (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x')) (β : K₀ → ℤ)
    (Q : Kleiman.LineBundle S (baseVec y₀ k₀ e))
    (hQ : ∀ c : ℤ, (Q.twist (Kleiman.twistSys S (baseVec y₀ k₀ e) c)).secs =
      secOver S y₀ (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀))
    (t : Ω) (ht : t ∈ secOver S (IndefiniteRowSideFullHecke.Kleiman2.joinVec y₁ y₀) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg β)) :
    t ∈ Kleiman.pullSecs x' Q.toSubSystem := by
  rw [mem_secOver_join_iff] at ht
  simp only [Kleiman.pullSecs, Submodule.mem_iInf]
  intro i hi
  obtain ⟨m, g, hgQ⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (Q.fg (Kleiman.singleChart hi))
  obtain ⟨Q', hQ'⟩ := Q.invertible (Kleiman.singleChart hi)
  have hlw : ∀ l ∈ Q.sub (Kleiman.singleChart hi), ∀ w ∈ Q',
      l * w ∈ Kleiman.chartRing S (baseVec y₀ k₀ e) (Kleiman.singleChart hi) := by
    intro l hl w hw
    have h := Submodule.mul_mem_mul hl hw
    rw [hQ', Submodule.mem_one] at h
    obtain ⟨r, hr⟩ := h
    rw [← hr]
    exact r.2
  have hg : ∀ b, g b ∈ Q.sub (Kleiman.singleChart hi) := fun b => by
    rw [← hgQ]; exact Submodule.subset_span ⟨b, rfl⟩
  rw [← hgQ] at hQ'
  obtain ⟨w, hwQ, -, hsum⟩ := exists_sum_eq_one g Q' hQ'
  have htw : ∀ b, t * w b ∈ Kleiman.domRing S (baseVec y₀ k₀ e) x' i := by
    intro b
    refine mem_domRing_of_forall fun i' hi' => ?_
    refine mem_of_forall_fracSub _ _ fun P _ => ?_
    obtain ⟨c₁, hc₁, h1⟩ := exists_chart₁ (y₀ := y₀) (e := e) hsame hi' i P
    obtain ⟨f, hf0, d, hd, hdle, h0, hinv⟩ := exists_chart₀ (x' := x') hy i' hi P
    obtain ⟨n, hn⟩ := exists_pow_mul_inv_mem_latOf (S := S) (y₀ := y₀) β i f hdle
    have hlwb := chartRing_le_pairRing (x' := x') i' hi
      (hlw _ ((mem_sub_iff_latOf hy β Q hQ hi _).mpr hn) (w b) (hwQ b))
    have htd := joinRing_le c₁ d _ h1 h0 (ht c₁ d hc₁ hd)
    have hG := genInv_ne_zero β hd
    have e1 : t * w b =
        t * genInv y₀ β d * ((f : Ω) ^ n * (genInv y₀ β d)⁻¹ * w b) * ((f : Ω) ^ n)⁻¹ := by
      field_simp
    rw [e1]
    exact mul_mem (mul_mem htd (self_mem_fracSub _ P hlwb)) (hinv n)
  have e : t = ∑ b, t * w b * g b := by
    calc t = t * ∑ b, g b * w b := by rw [hsum, mul_one]
      _ = ∑ b, t * w b * g b := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
  rw [e]
  exact Submodule.sum_mem _ fun b _ => Submodule.subset_span ⟨t * w b, htw b, g b, hg b, rfl⟩

end Join

end PullSecsModel

theorem PullSecsModel.full : PullSecsModel.Statement := by
  intro S _ K₁ _ ι₁ _ K₀ _ _ ι₀ _ Ω _ _ y₁ y₀ k₀ N N' e x x' hx hS _ hy _ hsame Q β hQ
  subst hx
  ext t
  exact ⟨PullSecsModel.mem_secOver_of_mem_pullSecs hy hsame β Q hQ t,
    PullSecsModel.mem_pullSecs_of_mem_secOver hy hsame β Q hQ t⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
