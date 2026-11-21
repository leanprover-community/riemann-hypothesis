import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ContinuousCoB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.HenselRoot

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.InjectiveDecompositionAction NumberField IsDedekindDomain
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.Fin.U1

section Sq

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem norm_sub_eq_max {x y : v.adicCompletion F} (h : ‖x‖ ≠ ‖y‖) : ‖x - y‖ = max ‖x‖ ‖y‖ := by
  have h' : ‖x‖ ≠ ‖-y‖ := by rwa [norm_neg]
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h', norm_neg]

theorem sq_of_nonint (Δ a b : v.adicCompletion F) (h2 : ‖(2 : v.adicCompletion F)‖ = 1) (hΔ : ‖Δ‖ = 1)
    (hab : a * a - Δ * (b * b) = 1) (hni : 1 < ‖a‖ ∨ 1 < ‖b‖) : ∃ s, s * s = Δ := by
  have hn : ‖a * a - Δ * (b * b)‖ = 1 := by rw [hab, norm_one]
  have heq : ‖a‖ = ‖b‖ := by
    by_contra hne
    have hne2 : ‖a * a‖ ≠ ‖Δ * (b * b)‖ := by
      rw [norm_mul, norm_mul, norm_mul, hΔ, one_mul]
      intro h
      apply hne
      have ha := norm_nonneg a; have hb := norm_nonneg b
      nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ + ‖b‖)]
    rw [norm_sub_eq_max v hne2, norm_mul, norm_mul, norm_mul, hΔ, one_mul] at hn
    rcases hni with h | h
    · have : ‖a‖ * ‖a‖ ≤ 1 := hn ▸ le_max_left _ _
      nlinarith
    · have : ‖b‖ * ‖b‖ ≤ 1 := hn ▸ le_max_right _ _
      nlinarith
  have hb1 : 1 < ‖b‖ := by rcases hni with h | h <;> linarith
  have hb0 : b ≠ 0 := by intro h; rw [h, norm_zero] at hb1; linarith
  set t := a / b with ht
  have htn : ‖t‖ = 1 := by rw [ht, norm_div, heq, div_self (by linarith)]
  have ht0 : t ≠ 0 := by intro h; rw [h, norm_zero] at htn; linarith
  have htt : t * t - Δ = 1 / (b * b) := by
    rw [ht]; field_simp; linear_combination hab
  set u := Δ / (t * t) with hu
  have hu1 : ‖u - 1‖ < 1 := by
    have : u - 1 = -(1 / (b * b)) / (t * t) := by
      rw [hu, ← htt]; field_simp; ring
    rw [this, norm_div, norm_neg, norm_div, norm_one, norm_mul, norm_mul, htn, mul_one, div_one]
    have : 1 < ‖b‖ * ‖b‖ := by nlinarith
    rw [div_lt_one (by linarith)]; exact this
  have hv2 : Valued.v (((2 : ℕ) : v.adicCompletion F)) = 1 := by
    have h2' : ‖((2 : ℕ) : v.adicCompletion F)‖ = 1 := by exact_mod_cast h2
    apply le_antisymm
    · exact Valued.toNormedField.norm_le_one_iff.mp h2'.le
    · by_contra hlt
      push Not at hlt
      have := Valued.toNormedField.norm_lt_one_iff.mpr hlt
      linarith
  obtain ⟨z, hz⟩ := PI.LocalEndW.henselRoot F v 2 u hv2 (Valued.toNormedField.norm_lt_one_iff.mp hu1)
  refine ⟨t * z, ?_⟩
  have : z * z = u := by rw [← hz]; ring
  calc t * z * (t * z) = (t * t) * (z * z) := by ring
    _ = Δ := by rw [this, hu]; field_simp

end Sq

section Single

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] [NumberField F]

def single (v : HeightOneSpectrum (𝓞 F)) (t : v.adicCompletion F) : FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.mk (Pi.single v t) (by
    filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with w hw
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw
    rw [Pi.single_eq_of_ne hw]
    exact zero_mem _)

theorem single_self (v : HeightOneSpectrum (𝓞 F)) (t : v.adicCompletion F) : single v t v = t := by
  show Pi.single v t v = t
  exact Pi.single_eq_same v t

theorem single_ne {v w : HeightOneSpectrum (𝓞 F)} (t : v.adicCompletion F) (h : w ≠ v) : single v t w = 0 := by
  show Pi.single v t w = 0
  exact Pi.single_eq_of_ne h t

theorem pairA_mul (x y : Ainf F) (α β : Af F) : pairA F x α * pairA F y β = pairA F (x * y) (α * β) := rfl
theorem pairA_add (x y : Ainf F) (α β : Af F) : pairA F x α + pairA F y β = pairA F (x + y) (α + β) := rfl
theorem pairA_neg (x : Ainf F) (α : Af F) : -pairA F x α = pairA F (-x) (-α) := rfl
theorem algebraMap_AF (c : F) :
    algebraMap F (AF F) c = pairA F (algebraMap F (Ainf F) c) (algebraMap F (Af F) c) := rfl
theorem pairA_eq_iff (x y : Ainf F) (α β : Af F) : pairA F x α = pairA F y β ↔ x = y ∧ α = β := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨rfl, rfl⟩
    rfl
theorem fa_ext {x y : Af F} (h : ∀ w, x w = y w) : x = y := by
  first
    | exact RestrictedProduct.ext h
    | exact Subtype.ext (funext h)
theorem fa_mul (x y : Af F) (w : HeightOneSpectrum (𝓞 F)) : (x * y) w = x w * y w := rfl
theorem fa_add (x y : Af F) (w : HeightOneSpectrum (𝓞 F)) : (x + y) w = x w + y w := rfl
theorem fa_zero (w : HeightOneSpectrum (𝓞 F)) : (0 : Af F) w = 0 := rfl
theorem fa_neg (x : Af F) (w : HeightOneSpectrum (𝓞 F)) : (-x) w = -x w := rfl
theorem af_apply (c : F) (v : HeightOneSpectrum (𝓞 F)) :
    (algebraMap F (Af F) c) v = algebraMap F (v.adicCompletion F) c := rfl

end Single

section Split

variable {D : D7} (δ : D.host.E) (hδ : D.sp.cm.sig δ = -δ) (hδ0 : δ ≠ 0) (Δ : D.host.F)
  (hΔ : algebraMap D.host.F D.host.E Δ = δ * δ)

include hΔ hδ0 in

theorem exists_splitIdem (v : HeightOneSpectrum (𝓞 D.host.F)) (s : v.adicCompletion D.host.F)
    (hs : s * s = algebraMap D.host.F (v.adicCompletion D.host.F) Δ) (hcA : ∀ a b, cA D (pt δ a b) = pt δ a (-b)) :
    ∃ e, IsSplitIdem D e := by
  have hΔ0 : Δ ≠ 0 := by
    intro h; rw [h, map_zero] at hΔ; exact hδ0 (mul_self_eq_zero.mp hΔ.symm)
  have hs0 : s ≠ 0 := by
    intro h; rw [h, mul_zero] at hs
    exact hΔ0 ((map_eq_zero_iff _ (algebraMap D.host.F (v.adicCompletion D.host.F)).injective).mp hs.symm)
  set a : AF D.host.F := pairA D.host.F 0 (single v (1 / 2)) with ha
  set b : AF D.host.F := pairA D.host.F 0 (single v (1 / (2 * s))) with hb
  have e1 : a * a + DA Δ * (b * b) = a := by
    rw [ha, hb, DA, algebraMap_AF, pairA_mul, pairA_mul, pairA_mul, pairA_add, pairA_eq_iff]
    refine ⟨by ring, fa_ext fun w => ?_⟩
    simp only [fa_mul, fa_add, af_apply]
    by_cases hw : w = v
    · subst hw
      have h2 : (2 : w.adicCompletion D.host.F) ≠ 0 := by
        have := (algebraMap D.host.F (w.adicCompletion D.host.F)).injective.ne (two_ne_zero (α := D.host.F))
        rwa [map_ofNat, map_zero] at this
      rw [single_self, single_self, ← hs]; field_simp; ring
    · rw [single_ne _ hw, single_ne _ hw]; ring
  have h2 : (2 : v.adicCompletion D.host.F) ≠ 0 := by
    have := (algebraMap D.host.F (v.adicCompletion D.host.F)).injective.ne (two_ne_zero (α := D.host.F))
    rwa [map_ofNat, map_zero] at this
  have e2 : a * b + b * a = b := by
    rw [ha, hb, pairA_mul, pairA_mul, pairA_add, pairA_eq_iff]
    refine ⟨by ring, fa_ext fun w => ?_⟩
    simp only [fa_mul, fa_add]
    by_cases hw : w = v
    · subst hw; rw [single_self, single_self]; field_simp; ring
    · rw [single_ne _ hw, single_ne _ hw]; ring
  have e3 : a * a + DA Δ * (b * -b) = 0 := by
    rw [ha, hb, DA, algebraMap_AF, pairA_neg, pairA_mul, pairA_mul, pairA_mul, pairA_add]
    show pairA D.host.F _ _ = pairA D.host.F 0 0
    rw [pairA_eq_iff]
    refine ⟨by ring, fa_ext fun w => ?_⟩
    simp only [fa_mul, fa_add, fa_neg, af_apply, fa_zero]
    by_cases hw : w = v
    · subst hw; rw [single_self, single_self, ← hs]; field_simp; ring
    · rw [single_ne _ hw, single_ne _ hw]; ring
  have e4 : a * -b + b * a = 0 := by ring
  have e5 : a + a = pairA D.host.F 0 (single v 1) := by
    rw [ha, pairA_add, pairA_eq_iff]
    refine ⟨by ring, fa_ext fun w => ?_⟩
    simp only [fa_add]
    by_cases hw : w = v
    · subst hw; rw [single_self, single_self]; field_simp; norm_num
    · rw [single_ne _ hw, single_ne _ hw, add_zero]
  refine ⟨pt δ a b, ?_, ?_, v, pairA D.host.F 0 (single v 1), ?_, ?_⟩
  · rw [pt_mul δ Δ hΔ, e1, e2]
  · rw [hcA, pt_mul δ Δ hΔ, e3, e4]; exact mkE_zero δ (AF D.host.F)
  · refine ⟨single v 1, rfl, ?_, fun v' hv' => ?_⟩
    · exact single_self v 1
    · exact single_ne 1 hv'
  · rw [hcA, pt, pt, mkE_add, add_neg_cancel, e5, algebraMap_eq_mkE]

end Split

end Formalism.IndefR.Fin.U1

end
end

section
noncomputable section

open Filter Topology

namespace Formalism.IndefR.Fin.U1


section Defs

variable {K : Type*} [Field K]

def nrm (Δ p r : K) : K := p * p - Δ * (r * r)

def cAq (Δ a b p r : K) : K := (a * (p * p + Δ * (r * r)) - Δ * b * (2 * p * r)) / nrm Δ p r

def cBq (Δ a b p r : K) : K := (b * (p * p + Δ * (r * r)) - a * (2 * p * r)) / nrm Δ p r

end Defs

section Loc

variable {K : Type*} [NormedField K]

theorem loc_of (Δ a b p0 r0 : K) (hN : nrm Δ p0 r0 ≠ 0) (hA : cAq Δ a b p0 r0 = 1) (hB : cBq Δ a b p0 r0 = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ η > 0, ∀ p r : K, ‖p - p0‖ < η → ‖r - r0‖ < η →
      nrm Δ p r ≠ 0 ∧ ‖cAq Δ a b p r - 1‖ < ε ∧ ‖cBq Δ a b p r‖ < ε := by
  have hcN : Continuous fun y : K × K => nrm Δ y.1 y.2 := by unfold nrm; fun_prop
  have hn1 : Continuous fun y : K × K => a * (y.1 * y.1 + Δ * (y.2 * y.2)) - Δ * b * (2 * y.1 * y.2) := by
    fun_prop
  have hn2 : Continuous fun y : K × K => b * (y.1 * y.1 + Δ * (y.2 * y.2)) - a * (2 * y.1 * y.2) := by
    fun_prop
  have hA' : ContinuousAt (fun y : K × K => cAq Δ a b y.1 y.2) (p0, r0) := by
    unfold cAq; exact hn1.continuousAt.div hcN.continuousAt hN
  have hB' : ContinuousAt (fun y : K × K => cBq Δ a b y.1 y.2) (p0, r0) := by
    unfold cBq; exact hn2.continuousAt.div hcN.continuousAt hN
  have e1 : ∀ᶠ y in 𝓝 ((p0, r0) : K × K), nrm Δ y.1 y.2 ≠ 0 := hcN.continuousAt.eventually_ne hN
  have e2 : ∀ᶠ y in 𝓝 ((p0, r0) : K × K), ‖cAq Δ a b y.1 y.2 - 1‖ < ε := by
    have t := hA'.tendsto
    simp only [hA] at t
    exact (Metric.tendsto_nhds.1 t ε hε).mono fun y hy => by rwa [dist_eq_norm] at hy
  have e3 : ∀ᶠ y in 𝓝 ((p0, r0) : K × K), ‖cBq Δ a b y.1 y.2‖ < ε := by
    have t := hB'.tendsto
    simp only [hB] at t
    exact (Metric.tendsto_nhds.1 t ε hε).mono fun y hy => by rwa [dist_zero_right] at hy
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1 (e1.and (e2.and e3))
  refine ⟨η, hη, fun p r hp hr => ?_⟩
  have hd : dist ((p, r) : K × K) (p0, r0) < η := by
    rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]; exact ⟨hp, hr⟩
  obtain ⟨h1, h2, h3⟩ := hball hd
  exact ⟨h1, h2, h3⟩

theorem loc_near (Δ a b : K) (h2 : (2 : K) ≠ 0) (hΔ : Δ ≠ 0) (hab : a * a - Δ * (b * b) = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p0 r0 : K, ∃ η > 0, ∀ p r : K, ‖p - p0‖ < η → ‖r - r0‖ < η →
      nrm Δ p r ≠ 0 ∧ ‖cAq Δ a b p r - 1‖ < ε ∧ ‖cBq Δ a b p r‖ < ε := by
  by_cases ha : 1 + a = 0
  · have hb : b = 0 := by
      have hbb : Δ * (b * b) = 0 := by
        have : a = -1 := by linear_combination ha
        subst this; linear_combination -hab
      exact mul_self_eq_zero.mp ((mul_eq_zero.mp hbb).resolve_left hΔ)
    have hN : nrm Δ 0 1 = -Δ := by unfold nrm; ring
    have hN0 : nrm Δ 0 1 ≠ 0 := by rw [hN]; exact neg_ne_zero.mpr hΔ
    refine ⟨0, 1, loc_of Δ a b 0 1 hN0 ?_ ?_ ε hε⟩
    · unfold cAq; rw [div_eq_one_iff_eq hN0, hN, hb]; linear_combination Δ * ha
    · unfold cBq; rw [hb]; simp
  · have hN : nrm Δ (1 + a) b = 2 * (1 + a) := by unfold nrm; linear_combination hab
    have hN0 : nrm Δ (1 + a) b ≠ 0 := by rw [hN]; exact mul_ne_zero h2 ha
    refine ⟨1 + a, b, loc_of Δ a b (1 + a) b hN0 ?_ ?_ ε hε⟩
    · unfold cAq; rw [div_eq_one_iff_eq hN0, hN]; linear_combination (a + 2) * hab
    · unfold cBq; rw [div_eq_zero_iff]; left; linear_combination (-b) * hab

end Loc

end Formalism.IndefR.Fin.U1

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.InjectiveDecompositionAction NumberField IsDedekindDomain
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.Fin.U1

section Comp

variable {F : Type} [Field F] [NumberField F]

theorem finite_adele_fst_mul (x y : AF F) : (x * y).1 = x.1 * y.1 := rfl
theorem finite_adele_fst_add (x y : AF F) : (x + y).1 = x.1 + y.1 := rfl
theorem finite_adele_fst_sub (x y : AF F) : (x - y).1 = x.1 - y.1 := rfl
theorem finite_adele_fst_one : (1 : AF F).1 = 1 := rfl
theorem finite_adele_snd_mul (x y : AF F) (v : HeightOneSpectrum (𝓞 F)) : (x * y).2 v = x.2 v * y.2 v := rfl
theorem finite_adele_snd_add (x y : AF F) (v : HeightOneSpectrum (𝓞 F)) : (x + y).2 v = x.2 v + y.2 v := rfl
theorem finite_adele_snd_sub (x y : AF F) (v : HeightOneSpectrum (𝓞 F)) : (x - y).2 v = x.2 v - y.2 v := rfl
theorem finite_adele_snd_one (v : HeightOneSpectrum (𝓞 F)) : (1 : AF F).2 v = 1 := rfl
theorem finite_adele_snd_algebraMap (c : F) (v : HeightOneSpectrum (𝓞 F)) :
    (algebraMap F (AF F) c).2 v = algebraMap F (v.adicCompletion F) c := rfl

abbrev epv (v : HeightOneSpectrum (𝓞 F)) : AF F := pairA F 0 (single v 1)

theorem epv_fst (v : HeightOneSpectrum (𝓞 F)) : (epv v).1 = 0 := rfl
theorem epv_self (v : HeightOneSpectrum (𝓞 F)) : (epv v).2 v = 1 := by
  classical
  first
  | exact Pi.single_eq_same v (1 : v.adicCompletion F)
  | (simp [epv, pairA, single]; done)
  | (simp [epv, pairA, single]; convert Pi.single_eq_same v (1 : v.adicCompletion F); done)
  | (simp [epv, pairA, single]; rfl)
theorem epv_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : (epv v).2 w = 0 := by
  classical
  first
  | exact Pi.single_eq_of_ne h (1 : v.adicCompletion F)
  | (simp [epv, pairA, single, h]; done)
  | (simp [epv, pairA, single]; convert Pi.single_eq_of_ne h (1 : v.adicCompletion F); done)
  | (simp [epv, pairA, single]; rfl)

theorem epv_sq (v : HeightOneSpectrum (𝓞 F)) : epv v * epv v = epv v := by
  refine Prod.ext ?_ ?_
  · rw [finite_adele_fst_mul, epv_fst, mul_zero]
  · apply RestrictedProduct.ext
    intro w
    refine (finite_adele_snd_mul (epv v) (epv v) w).trans ?_
    by_cases h : w = v
    · subst h
      rw [epv_self, mul_one]
      exact (epv_self w).symm
    · rw [epv_ne h, mul_zero]
      exact (epv_ne h).symm

end Comp

section Split

variable {D : D7} (δ : D.host.E) (hδ : D.sp.cm.sig δ = -δ) (hδ0 : δ ≠ 0) (Δ : D.host.F)
  (hΔ : algebraMap D.host.F D.host.E Δ = δ * δ)

include hΔ hδ0 hδ in

theorem exists_splitIdem' (v : HeightOneSpectrum (𝓞 D.host.F)) (s : v.adicCompletion D.host.F)
    (hs : s * s = algebraMap D.host.F (v.adicCompletion D.host.F) Δ) :
    ∃ e, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) (epv v) := by
  classical
  have hc : ∀ (a : AF D.host.F) (x : D.host.E), cA D (a ⊗ₜ[D.host.F] x) = a ⊗ₜ[D.host.F] D.sp.cm.sig x := by
    intro a x
    first
    | rfl
    | simp [cA]
  have h2F : (2 : v.adicCompletion D.host.F) ≠ 0 := by
    have h := (algebraMap D.host.F (v.adicCompletion D.host.F)).injective.ne (two_ne_zero (α := D.host.F))
    rw [map_ofNat, map_zero] at h
    exact h
  have hΔ0 : Δ ≠ 0 := by
    rintro rfl
    apply hδ0
    have h0 : δ * δ = 0 := by rw [← hΔ, map_zero]
    exact mul_self_eq_zero.mp h0
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hΔ0
    have h0 : algebraMap D.host.F (v.adicCompletion D.host.F) Δ = 0 := by rw [← hs, mul_zero]
    exact (map_eq_zero_iff _ (algebraMap D.host.F (v.adicCompletion D.host.F)).injective).mp h0
  have hsv : ∀ t : v.adicCompletion D.host.F, (single v t) v = t := by
    intro t
    first
    | exact Pi.single_eq_same v t
    | (simp [single]; done)
    | (simp [single]; convert Pi.single_eq_same v t; done)
    | (simp [single]; rfl)
  have hsw : ∀ (t : v.adicCompletion D.host.F) (w : HeightOneSpectrum (𝓞 D.host.F)), w ≠ v →
      (single v t) w = 0 := by
    intro t w hw
    first
    | exact Pi.single_eq_of_ne hw t
    | (simp [single, hw]; done)
    | (simp [single]; convert Pi.single_eq_of_ne hw t; done)
    | (simp [single]; rfl)
  have hAF : ∀ x y : AF D.host.F, x.1 = y.1 → (∀ w, x.2 w = y.2 w) → x = y :=
by
    intro x y h1 h2
    refine Prod.ext h1 ?_
    apply RestrictedProduct.ext
    exact h2
  obtain ⟨a, ha⟩ : ∃ a : AF D.host.F, a = pairA D.host.F 0 (single v (2 : v.adicCompletion D.host.F)⁻¹) :=
    ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : AF D.host.F, b = pairA D.host.F 0 (single v (2 * s)⁻¹) := ⟨_, rfl⟩
  have ha1 : a.1 = 0 := by rw [ha]; rfl
  have hb1 : b.1 = 0 := by rw [hb]; rfl
  have ha2v : a.2 v = (2 : v.adicCompletion D.host.F)⁻¹ := by rw [ha]; exact hsv _
  have hb2v : b.2 v = (2 * s)⁻¹ := by rw [hb]; exact hsv _
  have ha2w : ∀ w, w ≠ v → a.2 w = 0 := by intro w hw; rw [ha]; exact hsw _ w hw
  have hb2w : ∀ w, w ≠ v → b.2 w = 0 := by intro w hw; rw [hb]; exact hsw _ w hw
  have hDAv : (DA Δ).2 v = s * s := by rw [hs]; exact finite_adele_snd_algebraMap Δ v
  have A1 : a * a + DA Δ * (b * b) = a := by
    apply hAF
    · simp only [finite_adele_fst_add, finite_adele_fst_mul, ha1, hb1]
      ring
    · intro w
      simp only [finite_adele_snd_add, finite_adele_snd_mul]
      by_cases hw : w = v
      · subst hw
        rw [ha2v, hb2v, hDAv]
        field_simp
        ring
      · rw [ha2w w hw, hb2w w hw]
        ring
  have A2 : a * b + a * b = b := by
    apply hAF
    · simp only [finite_adele_fst_add, finite_adele_fst_mul, ha1, hb1]
      ring
    · intro w
      simp only [finite_adele_snd_add, finite_adele_snd_mul]
      by_cases hw : w = v
      · subst hw
        rw [ha2v, hb2v]
        field_simp
        ring
      · rw [ha2w w hw, hb2w w hw]
        ring
  have A3 : a * a - DA Δ * (b * b) = 0 := by
    apply hAF
    · simp only [finite_adele_fst_sub, finite_adele_fst_mul, ha1, hb1]
      rw [show (0 : AF D.host.F).1 = 0 from rfl]
      ring
    · intro w
      simp only [finite_adele_snd_sub, finite_adele_snd_mul]
      rw [show (0 : AF D.host.F).2 w = 0 from rfl]
      by_cases hw : w = v
      · subst hw
        rw [ha2v, hb2v, hDAv]
        field_simp
        ring
      · rw [ha2w w hw, hb2w w hw]
        ring
  have A4 : a + a = epv v := by
    apply hAF
    · simp only [finite_adele_fst_add, ha1, epv_fst]
      ring
    · intro w
      simp only [finite_adele_snd_add]
      by_cases hw : w = v
      · subst hw
        rw [ha2v, epv_self, ← two_mul, mul_inv_cancel₀ h2F]
      · rw [ha2w w hw, epv_ne hw]
        ring
  obtain ⟨ι, hι⟩ : ∃ f : AF D.host.F →+* AE D, f = algebraMap (AF D.host.F) (AE D) := ⟨_, rfl⟩
  have hιt : ∀ x : AF D.host.F, ι x = x ⊗ₜ[D.host.F] (1 : D.host.E) := by intro x; rw [hι]; rfl
  obtain ⟨d, hd⟩ : ∃ d : AE D, d = (1 : AF D.host.F) ⊗ₜ[D.host.F] δ := ⟨_, rfl⟩
  have kd : d * d = ι (DA Δ) := by
    rw [hd, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← hΔ, hιt,
      show algebraMap D.host.F D.host.E Δ = Δ • (1 : D.host.E) from Algebra.algebraMap_eq_smul_one Δ,
      ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  have k1 : ι a * ι a + ι (DA Δ) * (ι b * ι b) = ι a := by
    simpa only [map_add, map_mul] using congrArg ι A1
  have k2 : ι a * ι b + ι a * ι b = ι b := by
    simpa only [map_add, map_mul] using congrArg ι A2
  have k3 : ι a * ι a - ι (DA Δ) * (ι b * ι b) = 0 := by
    simpa only [map_sub, map_mul, map_zero] using congrArg ι A3
  have k4 : ι a + ι a = ι (epv v) := by
    simpa only [map_add] using congrArg ι A4
  have hcι : ∀ x, cA D (ι x) = ι x := by
    intro x
    rw [hιt, hc, map_one]
  have hcd : cA D (ι b * d) = -(ι b * d) := by
    rw [hιt, hd, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, hc, hδ, TensorProduct.tmul_neg]
  have hce : cA D (ι a + ι b * d) = ι a - ι b * d := by
    rw [map_add, hcι, hcd, sub_eq_add_neg]
  have hsum : ι a + ι b * d + cA D (ι a + ι b * d) = algebraMap (AF D.host.F) (AE D) (epv v) := by
    rw [hce, ← hι, ← k4]
    ring
  refine ⟨ι a + ι b * d, ⟨?_, ?_, v, epv v, ?_, hsum⟩, hsum⟩
  · linear_combination k1 + d * k2 + ι b * ι b * kd
  · rw [hce]
    linear_combination k3 - ι b * ι b * kd
  · exact ⟨single v 1, rfl, epv_self v, fun v' hv' => epv_ne hv'⟩

include hδ hδ0 hΔ in

theorem removal (lam : FirstPropositionFrame D →* Circle)
    (hsplit : ∀ e, IsSplitIdem D e → ∀ x : FirstPropositionFrame D, SuppAtU D e (x : (AE D)ˣ) → lam x = 1)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (hS : ∀ v ∉ S, ‖(2 : v.adicCompletion D.host.F)‖ = 1 ∧
      ‖algebraMap D.host.F (v.adicCompletion D.host.F) Δ‖ = 1) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 D.host.F))) (a b : AF D.host.F) (h : a * a - DA Δ * (b * b) = 1),
      (∀ v, v ∉ S → ¬ (‖a.2 v‖ ≤ 1 ∧ ‖b.2 v‖ ≤ 1) → v ∈ T) →
      ∃ (a' b' : AF D.host.F) (h' : a' * a' - DA Δ * (b' * b') = 1),
        lam (mkU δ hδ Δ hΔ h') = lam (mkU δ hδ Δ hΔ h) ∧ a'.1 = a.1 ∧ b'.1 = b.1 ∧
        (∀ v ∈ S, a'.2 v = a.2 v ∧ b'.2 v = b.2 v) ∧ ∀ v ∉ S, ‖a'.2 v‖ ≤ 1 ∧ ‖b'.2 v‖ ≤ 1 := by
  classical
  have hAF : ∀ x y : AF D.host.F, x.1 = y.1 → (∀ w, x.2 w = y.2 w) → x = y := by
    intro x y h1 h2
    refine Prod.ext h1 ?_
    apply RestrictedProduct.ext
    exact h2
  obtain ⟨ι, hι⟩ : ∃ f : AF D.host.F →+* AE D, f = algebraMap (AF D.host.F) (AE D) := ⟨_, rfl⟩
  have hιt : ∀ z : AF D.host.F, ι z = z ⊗ₜ[D.host.F] (1 : D.host.E) := by intro z; rw [hι]; rfl
  obtain ⟨dd, hdd⟩ : ∃ d : AE D, d = (1 : AF D.host.F) ⊗ₜ[D.host.F] δ := ⟨_, rfl⟩
  have hpt : ∀ p q : AF D.host.F, pt δ p q = ι p + ι q * dd := by
    intro p q
    rw [hιt, hιt, hdd, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
  intro T
  refine Finset.induction_on T ?_ ?_
  · intro a b h hT
    refine ⟨a, b, h, rfl, rfl, rfl, fun v _ => ⟨rfl, rfl⟩, fun v hv => ?_⟩
    by_contra hn
    exact absurd (hT v hv hn) (Finset.notMem_empty v)
  · intro v T0 _ ih a b h hT
    by_cases hgood : v ∈ S ∨ (‖a.2 v‖ ≤ 1 ∧ ‖b.2 v‖ ≤ 1)
    · apply ih a b h
      intro w hw hn
      rcases Finset.mem_insert.mp (hT w hw hn) with h0 | h0
      · subst h0
        rcases hgood with h1 | h1
        · exact absurd h1 hw
        · exact absurd h1 hn
      · exact h0
    have hvS : v ∉ S := fun h0 => hgood (Or.inl h0)
    have hni : 1 < ‖a.2 v‖ ∨ 1 < ‖b.2 v‖ := by
      by_contra hc
      push_neg at hc
      exact hgood (Or.inr hc)
    obtain ⟨h2v, hΔv⟩ := hS v hvS
    have hav : a.2 v * a.2 v - algebraMap D.host.F (v.adicCompletion D.host.F) Δ * (b.2 v * b.2 v) = 1 := by
      have h0 := congrArg (fun z : AF D.host.F => z.2 v) h
      simp only [finite_adele_snd_sub, finite_adele_snd_mul, finite_adele_snd_one] at h0
      rw [← finite_adele_snd_algebraMap Δ v]
      exact h0
    obtain ⟨s, hs⟩ := sq_of_nonint (F := D.host.F) (v := v)
      (Δ := algebraMap D.host.F (v.adicCompletion D.host.F) Δ) (a := a.2 v) (b := b.2 v) h2v hΔv hav hni
    obtain ⟨e, he, hee⟩ := exists_splitIdem' δ hδ hδ0 Δ hΔ v s hs
    obtain ⟨a', ha'⟩ : ∃ a' : AF D.host.F, a' = a - epv v * a + epv v := ⟨_, rfl⟩
    obtain ⟨b', hb'⟩ : ∃ b' : AF D.host.F, b' = b - epv v * b := ⟨_, rfl⟩
    have ha'1 : a'.1 = a.1 := by rw [ha', finite_adele_fst_add, finite_adele_fst_sub, finite_adele_fst_mul, epv_fst]; ring
    have hb'1 : b'.1 = b.1 := by rw [hb', finite_adele_fst_sub, finite_adele_fst_mul, epv_fst]; ring
    have ha'v : a'.2 v = 1 := by rw [ha', finite_adele_snd_add, finite_adele_snd_sub, finite_adele_snd_mul, epv_self]; ring
    have hb'v : b'.2 v = 0 := by rw [hb', finite_adele_snd_sub, finite_adele_snd_mul, epv_self]; ring
    have ha'w : ∀ w, w ≠ v → a'.2 w = a.2 w := by
      intro w hw
      rw [ha', finite_adele_snd_add, finite_adele_snd_sub, finite_adele_snd_mul, epv_ne hw]
      ring
    have hb'w : ∀ w, w ≠ v → b'.2 w = b.2 w := by
      intro w hw
      rw [hb', finite_adele_snd_sub, finite_adele_snd_mul, epv_ne hw]
      ring
    have h' : a' * a' - DA Δ * (b' * b') = 1 := by
      apply hAF
      · have h0 := congrArg (fun z : AF D.host.F => z.1) h
        simp only [finite_adele_fst_sub, finite_adele_fst_mul, finite_adele_fst_one] at h0 ⊢
        rw [ha'1, hb'1]
        exact h0
      · intro w
        have h0 := congrArg (fun z : AF D.host.F => z.2 w) h
        simp only [finite_adele_snd_sub, finite_adele_snd_mul, finite_adele_snd_one] at h0 ⊢
        by_cases hw : w = v
        · subst hw
          rw [ha'v, hb'v]
          ring
        · rw [ha'w w hw, hb'w w hw]
          exact h0
    have hX : (((mkU δ hδ Δ hΔ h : FirstPropositionFrame D) : (AE D)ˣ) : AE D) = pt δ a b := rfl
    have hX' : (((mkU δ hδ Δ hΔ h' : FirstPropositionFrame D) : (AE D)ˣ) : AE D) = pt δ a' b' := rfl
    have hsupp : SuppAtU D e ((mkU δ hδ Δ hΔ h' * (mkU δ hδ Δ hΔ h)⁻¹ : FirstPropositionFrame D) : (AE D)ˣ) := by
      unfold SuppAtU
      rw [hee]
      obtain ⟨u, hu⟩ : ∃ u : AE D, u = ((((mkU δ hδ Δ hΔ h)⁻¹ : FirstPropositionFrame D) : (AE D)ˣ) : AE D) := ⟨_, rfl⟩
      have hXu : pt δ a b * u = 1 := by
        rw [← hX, hu]
        simp
      have hval : ((((mkU δ hδ Δ hΔ h' * (mkU δ hδ Δ hΔ h)⁻¹ : FirstPropositionFrame D)) : (AE D)ˣ) : AE D) =
          pt δ a' b' * u := by
        rw [hu, ← hX']
        simp
      rw [hval, ← hι]
      have hk : ι (epv v) * ι (epv v) = ι (epv v) := by rw [← map_mul, epv_sq]
      have hda : a' = a + epv v * (1 - a) := by rw [ha']; ring
      have hdb : b' = b + epv v * (-b) := by rw [hb']; ring
      rw [hpt] at hXu
      rw [hpt, hda, hdb, map_add, map_add, map_mul, map_mul, map_sub, map_one, map_neg]
      linear_combination (2 * ι (epv v) - 1 - ι (epv v) * ι (epv v)) * hXu + (u - 1) * hk
    have hlam : lam (mkU δ hδ Δ hΔ h') = lam (mkU δ hδ Δ hΔ h) := by
      have h1 := hsplit e he _ hsupp
      rw [map_mul, map_inv] at h1
      exact mul_inv_eq_one.mp h1
    obtain ⟨a'', b'', h'', hl, h1a, h1b, hSab, hint⟩ := ih a' b' h' (by
      intro w hw hn
      have hwv : w ≠ v := by
        rintro rfl
        apply hn
        rw [ha'v, hb'v]
        simp
      rw [ha'w w hwv, hb'w w hwv] at hn
      rcases Finset.mem_insert.mp (hT w hw hn) with h0 | h0
      · exact absurd h0 hwv
      · exact h0)
    refine ⟨a'', b'', h'', hl.trans hlam, h1a.trans ha'1, h1b.trans hb'1, fun w hw => ?_, hint⟩
    have hwv : w ≠ v := fun h0 => hvS (h0 ▸ hw)
    obtain ⟨h1, h2⟩ := hSab w hw
    exact ⟨h1.trans (ha'w w hwv), h2.trans (hb'w w hwv)⟩

end Split

end Formalism.IndefR.Fin.U1

end
end
