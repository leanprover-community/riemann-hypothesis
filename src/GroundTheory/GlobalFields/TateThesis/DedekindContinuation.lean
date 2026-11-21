import Mathlib
import GroundTheory.GlobalFields.TateThesis.TateMain
import GroundTheory.GlobalFields.TateThesis.EulerFactors
import GroundTheory.GlobalFields.TateThesis.EulerFactorsFourierInfinite
import GroundTheory.GlobalFields.TateThesis.EulerFactorsFourierFinite

section
open NumberField Topology Filter Complex Set
open scoped NumberField.AdeleRing

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

theorem eqOn_of_differentiableOn_of_eq_globalZeta {F : 𝔸[K] → ℂ} {χ : HeckeCharacter K}
    {S : Set ℂ} (hS : S.Finite) (hSre : ∀ z ∈ S, z.re ≤ 1) {G H : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G Sᶜ) (hH : DifferentiableOn ℂ H Sᶜ)
    (hGZ : ∀ s : ℂ, 1 < s.re → G s = globalZeta F χ s)
    (hHZ : ∀ s : ℂ, 1 < s.re → H s = globalZeta F χ s) : EqOn G H Sᶜ := by
  have hopen : IsOpen Sᶜ := hS.isClosed.isOpen_compl
  have hU : IsPreconnected Sᶜ :=
    (hS.countable.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected
  have h2 : (2 : ℂ) ∈ Sᶜ := fun h ↦ by
    have := hSre 2 h
    norm_num at this
  have heq : G =ᶠ[𝓝 (2 : ℂ)] H :=
    Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)) fun s hs ↦ (hGZ s hs).trans (hHZ s hs).symm
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hopen)
    (hH.analyticOnNhd hopen) hU h2 heq

theorem eq_tateZeta_of_differentiable {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K)
    {χ : HeckeCharacter K} (hχ : ∃ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) ≠ 1)
    {G : ℂ → ℂ} (hG : Differentiable ℂ G) (hGZ : ∀ s : ℂ, 1 < s.re → G s = globalZeta F χ s) :
    G = tateZeta F χ := by
  have h := eqOn_of_differentiableOn_of_eq_globalZeta (S := ∅) finite_empty (by simp)
    hG.differentiableOn (differentiable_tateZeta hF hχ).differentiableOn hGZ
    fun s hs ↦ tateZeta_eq_globalZeta hF χ hs
  funext s
  exact h (by simp)

theorem eqOn_tateZeta_of_differentiableOn {χ : HeckeCharacter K} {τ : ℝ}
    (hτ : ∀ x : IdeleGroup K, (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I))
    {F : 𝔸[K] → ℂ} (hF : F ∈ schwartzBruhat K) {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G {-((τ : ℂ) * I), 1 - (τ : ℂ) * I}ᶜ)
    (hGZ : ∀ s : ℂ, 1 < s.re → G s = globalZeta F χ s) :
    EqOn G (tateZeta F χ) {-((τ : ℂ) * I), 1 - (τ : ℂ) * I}ᶜ := by
  refine eqOn_of_differentiableOn_of_eq_globalZeta (toFinite _) ?_ hG ?_ hGZ
    fun s hs ↦ tateZeta_eq_globalZeta hF χ hs
  · intro z hz
    rcases hz with rfl | rfl <;> simp
  · intro s hs
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hs
    exact (differentiableAt_tateZeta hτ hF hs.1 hs.2).differentiableWithinAt

end

end GroundTheory.Global
end

section
open NumberField InfinitePlace IsDedekindDomain MeasureTheory Complex WithZero
open scoped NumberField.AdeleRing nonZeroDivisors

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

theorem differentIdeal_ne_bot : differentIdeal ℤ (𝓞 K) ≠ ⊥ :=
  FractionalIdeal.coeIdeal_ne_zero.1 coe_differentIdeal_ne_zero

def differentUnit : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  idealUnit (differentIdeal ℤ (𝓞 K)) differentIdeal_ne_bot

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

theorem exists_ofFinite_toFractionalIdeal_eq :
    ∃ δ : (FiniteAdeleRing (𝓞 K) K)ˣ, toFractionalIdeal (ofFinite δ) =
      idealUnit χ.conductor χ.conductor_ne_bot * differentUnit := by
  obtain ⟨x, hx⟩ := toFractionalIdeal_surjective (K := K)
    (idealUnit χ.conductor χ.conductor_ne_bot * differentUnit)
  refine ⟨toFinite K x, ?_⟩
  rw [← hx, toFractionalIdeal_eq_iff]
  intro v
  rw [count_toFractionalIdeal]
  rfl

theorem valued_of_toFractionalIdeal_eq {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit)
    (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((δ : FiniteAdeleRing (𝓞 K) K) v) = WithZero.exp (-(χ.condExp v + differentExp v)) := by
  rw [valued_eq_exp_ord, ← count_toFractionalIdeal, hδ, Units.val_mul,
    FractionalIdeal.count_mul K v (idealUnit χ.conductor χ.conductor_ne_bot).ne_zero
      (differentUnit (K := K)).ne_zero]
  rfl

def fourierConst (δ : (FiniteAdeleRing (𝓞 K) K)ˣ) : ℂ :=
  (∏ w, (-I) ^ (χ.infiniteWeight w).natAbs) *
    finiteFourier K χ.finiteTestFun ((δ⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K)

theorem fourierConst_ne_zero {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit) :
    χ.fourierConst δ ≠ 0 :=
  mul_ne_zero (Finset.prod_ne_zero_iff.2 fun _ _ ↦ pow_ne_zero _ (neg_ne_zero.2 I_ne_zero))
    (χ.finiteFourier_finiteTestFun_ne_zero δ (χ.valued_of_toFractionalIdeal_eq hδ))

theorem adelicFourier_testFunction {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit)
    (y : 𝔸[K]) :
    adelicFourier K χ.testFunction y = χ.fourierConst δ * (χ⁻¹).testFunction (ofFinite δ • y) := by
  have hy1 : (ofFinite δ • y).1 = y.1 := by
    change (1 : InfiniteAdeleRing K) * y.1 = y.1
    exact one_mul _
  have hy2 : (ofFinite δ • y).2 = (δ : FiniteAdeleRing (𝓞 K) K) * y.2 := rfl
  rw [testFunction, adelicFourier_schwartzBruhatTensor, schwartzBruhatTensor,
    mixedFourierSchwartz_apply, χ.mixedFourier_infiniteSchwartz,
    χ.finiteFourier_finiteTestFun δ (χ.valued_of_toFractionalIdeal_eq hδ) y.2, testFunction,
    schwartzBruhatTensor, hy1, hy2, fourierConst]
  ring

end HeckeCharacter

end

end GroundTheory.Global
end

section
open NumberField InfinitePlace IsDedekindDomain MeasureTheory Complex Topology Filter Set
open scoped NumberField.AdeleRing nonZeroDivisors

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

theorem ofReal_inv_cpow_of_pos {r : ℝ} (hr : 0 < r) (s : ℂ) :
    ((r⁻¹ : ℝ) : ℂ) ^ s = (r : ℂ) ^ (-s) := by
  rw [ofReal_inv, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hr.le]; exact Real.pi_pos.ne), cpow_neg]

theorem globalZeta_comp_smul (F : 𝔸[K] → ℂ) (χ : HeckeCharacter K) (a : IdeleGroup K) (s : ℂ) :
    globalZeta (fun y ↦ F (a • y)) χ s =
      (χ.toIdele a : ℂ)⁻¹ * ((ideleModule K a : ℝ) : ℂ) ^ (-s) * globalZeta F χ s := by
  unfold globalZeta
  have h := integral_mul_left_eq_self (μ := ideleMeasure K)
    (fun x : IdeleGroup K ↦ F (a • (x : 𝔸[K])) * (χ.toIdele x : ℂ) *
      ((ideleModule K x : ℝ) : ℂ) ^ s) a⁻¹
  rw [← h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  have h1 : a • ((a⁻¹ * x : IdeleGroup K) : 𝔸[K]) = (x : 𝔸[K]) := by
    rw [Units.smul_def, smul_eq_mul, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
  have h2 : ((ideleModule K (a⁻¹ * x) : ℝ) : ℂ) ^ s =
      ((ideleModule K a : ℝ) : ℂ) ^ (-s) * ((ideleModule K x : ℝ) : ℂ) ^ s := by
    rw [map_mul, map_inv, Positive.val_mul, Positive.coe_inv, ofReal_mul,
      mul_cpow_ofReal_nonneg (inv_nonneg.2 (ideleModule K a).2.le) (ideleModule K x).2.le,
      ofReal_inv_cpow_of_pos (ideleModule K a).2]
  beta_reduce
  rw [h1, h2]
  simp only [map_mul, map_inv, Circle.coe_mul, Circle.coe_inv]
  ring

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

def discrNormConductor : ℝ := |(discr K : ℝ)| * (Ideal.absNorm χ.conductor : ℝ)

theorem discrNormConductor_pos : 0 < χ.discrNormConductor := by
  refine mul_pos (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))) (Nat.cast_pos.2 ?_)
  exact Nat.pos_of_ne_zero fun h ↦ χ.conductor_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem discrNormConductor_inv : χ⁻¹.discrNormConductor = χ.discrNormConductor := by
  rw [discrNormConductor, discrNormConductor, conductor_inv]

theorem ideleModule_ofFinite_of_toFractionalIdeal_eq {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit) :
    (ideleModule K (ofFinite δ) : ℝ) = χ.discrNormConductor⁻¹ := by
  have hI : χ.conductor * differentIdeal ℤ (𝓞 K) ≠ ⊥ :=
    mul_ne_zero χ.conductor_ne_bot differentIdeal_ne_bot
  have hunit : idealUnit χ.conductor χ.conductor_ne_bot * differentUnit = idealUnit _ hI := by
    ext
    simp [idealUnit, differentUnit, FractionalIdeal.coeIdeal_mul]
  have hpos : ∀ v, 0 ≤ ord v (ofFinite δ) := fun v ↦ by
    rw [← count_toFractionalIdeal, hδ, hunit]
    change 0 ≤ FractionalIdeal.count K v
      (((χ.conductor * differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K))) : FractionalIdeal (𝓞 K)⁰ K)
    rw [count_coeIdeal_eq_multiplicity v hI]
    positivity
  have hideal : idealOfExponents (ordFinsupp K (ofFinite δ)) =
      χ.conductor * differentIdeal ℤ (𝓞 K) := by
    have h1 : toFractionalIdeal (ofFinite δ) =
        idealUnit _ (idealOfExponents_ne_bot (K := K) (n := ordFinsupp K (ofFinite δ)) hpos) := by
      rw [toFractionalIdeal_eq_iff]
      intro v
      exact (count_idealOfExponents (n := ordFinsupp K (ofFinite δ)) hpos v).symm
    rw [hδ, hunit] at h1
    exact FractionalIdeal.coeIdeal_injective (K := K) (congrArg Units.val h1).symm
  have hinf : infiniteModule (ofFinite δ) = 1 := by
    have e : ((ofFinite δ : IdeleGroup K) : 𝔸[K]).1 = 1 := by
      change ((toInfinite K (ofFinite δ) : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = 1
      rw [toInfinite_ofFinite, Units.val_one]
    simp only [infiniteModule, e]
    exact Finset.prod_eq_one fun w _ ↦ by
      rw [show (1 : InfiniteAdeleRing K) w = 1 from rfl, norm_one, one_pow]
  rw [ideleModule_apply, hinf, one_mul, finiteModule_ofFinite_eq hpos, hideal, map_mul,
    absNorm_differentIdeal K (𝓞 K), discrNormConductor, Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs,
    mul_comm]

theorem globalZeta_adelicFourier_testFunction {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit)
    (s : ℂ) :
    globalZeta (adelicFourier K χ.testFunction) χ⁻¹ s =
      χ.fourierConst δ * (χ.toIdele (ofFinite δ) : ℂ) * (χ.discrNormConductor : ℂ) ^ s *
        globalZeta (χ⁻¹).testFunction χ⁻¹ s := by
  have hf : adelicFourier K χ.testFunction =
      fun y ↦ χ.fourierConst δ * (χ⁻¹).testFunction (ofFinite δ • y) :=
    funext (χ.adelicFourier_testFunction hδ)
  have h1 : globalZeta (fun y ↦ χ.fourierConst δ * (χ⁻¹).testFunction (ofFinite δ • y)) χ⁻¹ s =
      χ.fourierConst δ * globalZeta (fun y ↦ (χ⁻¹).testFunction (ofFinite δ • y)) χ⁻¹ s := by
    unfold globalZeta
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hf, h1, globalZeta_comp_smul, χ.ideleModule_ofFinite_of_toFractionalIdeal_eq hδ,
    ofReal_inv_cpow_of_pos χ.discrNormConductor_pos, neg_neg, χ.inv_toIdele, Circle.coe_inv, inv_inv]
  ring

theorem exists_inv_ne_one (hχ : ∃ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) ≠ 1) :
    ∃ v : normOneSubgroup K, χ⁻¹.toIdele (v : IdeleGroup K) ≠ 1 := by
  obtain ⟨v, hv⟩ := hχ
  exact ⟨v, by rw [χ.inv_toIdele, ne_eq, inv_eq_one]; exact hv⟩

theorem inv_eq_cpow_of_forall {τ : ℝ}
    (hτ : ∀ x : IdeleGroup K, (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I)) :
    ∀ x : IdeleGroup K,
      ((χ⁻¹).toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ (((-τ : ℝ) : ℂ) * I) := fun x ↦ by
  rw [χ.inv_toIdele, Circle.coe_inv, hτ, ← cpow_neg]
  push_cast
  ring_nf

theorem differentiable_const_cpow_mul {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) {r : ℝ}
    (hr : 0 < r) : Differentiable ℂ fun s ↦ c * (r : ℂ) ^ s * f s :=
  ((differentiable_const c).mul
    (differentiable_id.const_cpow (Or.inl (ofReal_ne_zero.2 hr.ne')))).mul hf

theorem tateZeta_adelicFourier_testFunction {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit)
    (hχ : ∃ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) ≠ 1) (s : ℂ) :
    tateZeta (adelicFourier K χ.testFunction) χ⁻¹ s =
      χ.fourierConst δ * (χ.toIdele (ofFinite δ) : ℂ) * (χ.discrNormConductor : ℂ) ^ s *
        tateZeta (χ⁻¹).testFunction χ⁻¹ s := by
  have hχ' := χ.exists_inv_ne_one hχ
  have h := eq_tateZeta_of_differentiable (adelicFourier_mem_schwartzBruhat χ.testFunction_mem) hχ'
    (G := fun s ↦ χ.fourierConst δ * (χ.toIdele (ofFinite δ) : ℂ) * (χ.discrNormConductor : ℂ) ^ s *
      tateZeta (χ⁻¹).testFunction χ⁻¹ s)
    (differentiable_const_cpow_mul (differentiable_tateZeta (χ⁻¹).testFunction_mem hχ') _
      χ.discrNormConductor_pos)
    fun s hs ↦ by
      rw [tateZeta_eq_globalZeta (χ⁻¹).testFunction_mem _ hs,
        χ.globalZeta_adelicFourier_testFunction hδ]
  exact (congrFun h s).symm

theorem tateZeta_adelicFourier_testFunction_of_forall {δ : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hδ : toFractionalIdeal (ofFinite δ) = idealUnit χ.conductor χ.conductor_ne_bot * differentUnit)
    {τ : ℝ}
    (hτ : ∀ x : IdeleGroup K, (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I))
    {s : ℂ} (hs₀ : s ≠ (τ : ℂ) * I) (hs₁ : s ≠ 1 + (τ : ℂ) * I) :
    tateZeta (adelicFourier K χ.testFunction) χ⁻¹ s =
      χ.fourierConst δ * (χ.toIdele (ofFinite δ) : ℂ) * (χ.discrNormConductor : ℂ) ^ s *
        tateZeta (χ⁻¹).testFunction χ⁻¹ s := by
  have hτ' := χ.inv_eq_cpow_of_forall hτ
  have hpole : ∀ z : ℂ, z ≠ (τ : ℂ) * I → z ≠ 1 + (τ : ℂ) * I →
      z ≠ -(((-τ : ℝ) : ℂ) * I) ∧ z ≠ 1 - ((-τ : ℝ) : ℂ) * I := fun z h0 h1 ↦ by
    push_cast
    constructor
    · rw [neg_mul, neg_neg]; exact h0
    · rw [neg_mul, sub_neg_eq_add]; exact h1
  have hmem : s ∈ ({-(((-τ : ℝ) : ℂ) * I), 1 - ((-τ : ℝ) : ℂ) * I} : Set ℂ)ᶜ := by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact hpole s hs₀ hs₁
  have h := eqOn_tateZeta_of_differentiableOn hτ'
    (adelicFourier_mem_schwartzBruhat χ.testFunction_mem)
    (G := fun s ↦ χ.fourierConst δ * (χ.toIdele (ofFinite δ) : ℂ) * (χ.discrNormConductor : ℂ) ^ s *
      tateZeta (χ⁻¹).testFunction χ⁻¹ s)
    (fun z hz ↦ by
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
      refine DifferentiableAt.differentiableWithinAt ?_
      exact ((differentiableAt_const _).mul ((differentiableAt_id).const_cpow
        (Or.inl (ofReal_ne_zero.2 χ.discrNormConductor_pos.ne')))).mul
        (differentiableAt_tateZeta hτ' (χ⁻¹).testFunction_mem hz.1 hz.2))
    fun s hs ↦ by
      rw [tateZeta_eq_globalZeta (χ⁻¹).testFunction_mem _ hs,
        χ.globalZeta_adelicFourier_testFunction hδ]
  exact (h hmem).symm

end HeckeCharacter

end

end GroundTheory.Global
end

section
open NumberField InfinitePlace IsDedekindDomain MeasureTheory Complex Topology Filter Set
open scoped NumberField.AdeleRing ComplexConjugate Real

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

theorem ofReal_cpow_conj {r : ℝ} (hr : 0 < r) (s : ℂ) : (r : ℂ) ^ conj s = conj ((r : ℂ) ^ s) := by
  rw [cpow_conj _ _ (by rw [arg_ofReal_of_nonneg hr.le]; exact Real.pi_pos.ne), conj_ofReal]

theorem Gammaℝ_conj (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
  rw [Gammaℝ_def, Gammaℝ_def, map_mul, ← ofReal_cpow_conj Real.pi_pos, ← Gamma_conj]
  congr 2 <;> simp [map_div₀, map_neg, map_ofNat]

theorem Gammaℂ_conj (s : ℂ) : Gammaℂ (conj s) = conj (Gammaℂ s) := by
  have h2π : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; rfl
  rw [Gammaℂ_def, Gammaℂ_def, map_mul, map_mul, h2π, ← ofReal_cpow_conj (by positivity),
    ← Gamma_conj, map_ofNat, map_neg]

theorem Gammaℂ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Gammaℂ s ≠ 0 := by
  rw [Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero_of_re_pos hs)
  rw [Ne, cpow_eq_zero_iff, not_and_or]
  exact Or.inl (mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero))

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

theorem infiniteGamma_ne_zero (w : InfinitePlace K) {s : ℂ} (hs : 0 < s.re) :
    χ.infiniteGamma w s ≠ 0 := by
  unfold infiniteGamma
  split_ifs with hw
  · refine Gammaℝ_ne_zero_of_re_pos ?_
    have := (χ.infiniteWeight_of_isReal hw).1
    simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, intCast_re]
    have h0 : (0 : ℝ) ≤ (χ.infiniteWeight w : ℝ) := by exact_mod_cast this
    linarith
  · refine Gammaℂ_ne_zero_of_re_pos ?_
    simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, div_ofNat_re, natCast_re]
    positivity

theorem gammaFactor_ne_zero {s : ℂ} (hs : 0 < s.re) : χ.gammaFactor s ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun w _ ↦ χ.infiniteGamma_ne_zero w hs

theorem differentiable_gammaFactor_inv : Differentiable ℂ fun s ↦ (χ.gammaFactor s)⁻¹ := by
  have h : (fun s ↦ (χ.gammaFactor s)⁻¹) = fun s ↦ ∏ w, (χ.infiniteGamma w s)⁻¹ := by
    funext s
    rw [gammaFactor, Finset.prod_inv_distrib]
  rw [h]
  refine Differentiable.fun_finsetProd fun w _ ↦ ?_
  unfold infiniteGamma
  split_ifs
  · exact differentiable_Gammaℝ_inv.comp ((differentiable_id.add_const _).add_const _)
  · exact differentiable_Gammaℂ_inv.comp ((differentiable_id.add_const _).add_const _)

end HeckeCharacter

end

end GroundTheory.Global
end

section
open NumberField InfinitePlace IsDedekindDomain MeasureTheory Complex
open scoped NumberField.AdeleRing

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

variable (K) in

theorem normOneClassMeasure_univ_ne_zero : normOneClassMeasure K Set.univ ≠ 0 := by
  rw [normOneClassMeasure_univ]
  exact (isFundamentalDomain_normOneFundamentalDomain K (normOneMeasure K)).measure_ne_zero
    (NeZero.ne _)

variable (K) in

theorem normOneClassMeasure_univ_toReal_ne_zero : (normOneClassMeasure K Set.univ).toReal ≠ 0 :=
  ENNReal.toReal_ne_zero.2 ⟨normOneClassMeasure_univ_ne_zero K, measure_ne_top _ _⟩

namespace HeckeCharacter

variable {χ : HeckeCharacter K} {τ : ℝ}
  (hτ : ∀ x : IdeleGroup K, (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I))
include hτ

theorem conductor_eq_top_of_forall : χ.conductor = ⊤ := by
  have h : ∀ v, IdeleGroup.conductorExponentAt (χ.toIdele.comp IdeleGroup.ofFinite) v = 0 := fun v ↦
    (IdeleGroup.conductorExponentAt_eq_zero_iff Circle.noSmallSubgroups _
      (χ.continuous_toIdele.comp IdeleGroup.continuous_ofFinite) v).2 fun x hx ↦ by
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply,
          ofFinite_finiteUnitsSingle]
        refine Circle.ext ?_
        rw [hτ, ideleModule_finiteEmbedding, norm_eq_one_of_mul_eq_one x.mul_inv
          ((Submonoid.mem_units_iff _ _).1 hx).1 ((Submonoid.mem_units_iff _ _).1 hx).2]
        simp
  rw [conductor, IdeleGroup.conductor]
  simp only [h, pow_zero]
  rw [finprod_one, Ideal.one_eq_top]

theorem infiniteParams_of_forall (w : InfinitePlace K) : χ.infiniteParams w = (0, τ) := by
  refine (χ.infiniteParams_unique w (p := (0, τ)) (fun _ ↦ ⟨le_rfl, by norm_num⟩) fun a ↦ ?_).symm
  dsimp only
  rw [infiniteComponent_apply, hτ, ideleModule_infiniteEmbedding, zpow_zero, one_mul]

theorem infiniteWeight_of_forall (w : InfinitePlace K) : χ.infiniteWeight w = 0 := by
  rw [infiniteWeight, infiniteParams_of_forall hτ]

theorem infiniteTau_of_forall (w : InfinitePlace K) : χ.infiniteTau w = τ := by
  rw [infiniteTau, infiniteParams_of_forall hτ]

theorem infiniteSchwartz_zero_of_forall : χ.infiniteSchwartz 0 = 1 := by
  rw [infiniteSchwartz_apply]
  simp [infinitePoly, infiniteWeight_of_forall hτ]

theorem finiteTestFun_zero_of_forall : χ.finiteTestFun 0 = 1 := by
  have hv : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ χ.conductor := fun v h ↦ by
    rw [conductor_eq_top_of_forall hτ, Ideal.dvd_iff_le, top_le_iff] at h
    exact v.isPrime.ne_top h
  unfold finiteTestFun
  exact (finprod_congr fun v ↦ χ.finiteTest_eq_one (hv v) (by
    rw [show (0 : FiniteAdeleRing (𝓞 K) K) v = 0 from rfl, map_zero]; exact zero_le)).trans finprod_one

theorem testFunction_zero_of_forall : χ.testFunction 0 = 1 := by
  show χ.infiniteSchwartz (homeomorphMixedSpace K 0) * χ.finiteTestFun 0 = 1
  rw [homeomorphMixedSpace_apply, map_zero, infiniteSchwartz_zero_of_forall hτ,
    finiteTestFun_zero_of_forall hτ, one_mul]

end HeckeCharacter

end

end GroundTheory.Global
end

section
open NumberField InfinitePlace IsDedekindDomain MeasureTheory Complex Topology Filter Set
open scoped NumberField.AdeleRing ComplexConjugate Real

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

def completedLFunction (s : ℂ) : ℂ :=
  ((π : ℂ) ^ nrComplexPlaces K)⁻¹ * (χ.discrNormConductor : ℂ) ^ (s / 2) *
    tateZeta χ.testFunction χ s

theorem discrNormConductor_cpow_ne_zero (s : ℂ) : (χ.discrNormConductor : ℂ) ^ s ≠ 0 := by
  rw [Ne, cpow_eq_zero_iff, not_and_or]
  exact Or.inl (ofReal_ne_zero.2 χ.discrNormConductor_pos.ne')

theorem completedLFunction_eq {s : ℂ} (hs : 1 < s.re) :
    χ.completedLFunction s =
      (χ.discrNormConductor : ℂ) ^ (s / 2) * χ.gammaFactor s * χ.LFunction s := by
  rw [completedLFunction, tateZeta_eq_globalZeta χ.testFunction_mem χ hs,
    χ.globalZeta_testFunction hs]
  have hπ := pi_pow_nrComplexPlaces_ne_zero (K := K)
  field_simp

theorem differentiable_const_mul_cpow_half {f : ℂ → ℂ} {s : ℂ} (hf : DifferentiableAt ℂ f s) :
    DifferentiableAt ℂ (fun s ↦ ((π : ℂ) ^ nrComplexPlaces K)⁻¹ *
      (χ.discrNormConductor : ℂ) ^ (s / 2) * f s) s :=
  ((differentiableAt_const _).mul ((differentiableAt_id.div_const 2).const_cpow
    (Or.inl (ofReal_ne_zero.2 χ.discrNormConductor_pos.ne')))).mul hf

def conductorDifferentIdele : (FiniteAdeleRing (𝓞 K) K)ˣ :=
  χ.exists_ofFinite_toFractionalIdeal_eq.choose

theorem toFractionalIdeal_conductorDifferentIdele :
    toFractionalIdeal (ofFinite χ.conductorDifferentIdele) =
      idealUnit χ.conductor χ.conductor_ne_bot * differentUnit :=
  χ.exists_ofFinite_toFractionalIdeal_eq.choose_spec

def rootNumber : ℂ :=
  χ.fourierConst χ.conductorDifferentIdele * (χ.toIdele (ofFinite χ.conductorDifferentIdele) : ℂ) *
    (χ.discrNormConductor : ℂ) ^ (1 / 2 : ℂ)

theorem completedLFunction_eq_rootNumber_mul_of_eq {s : ℂ}
    (h : tateZeta (adelicFourier K χ.testFunction) χ⁻¹ (1 - s) =
      χ.fourierConst χ.conductorDifferentIdele *
        (χ.toIdele (ofFinite χ.conductorDifferentIdele) : ℂ) *
        (χ.discrNormConductor : ℂ) ^ (1 - s) * tateZeta (χ⁻¹).testFunction χ⁻¹ (1 - s)) :
    χ.completedLFunction s = χ.rootNumber * χ⁻¹.completedLFunction (1 - s) := by
  have hA : (χ.discrNormConductor : ℂ) ≠ 0 := ofReal_ne_zero.2 χ.discrNormConductor_pos.ne'
  rw [completedLFunction, tateZeta_eq_tateZeta_one_sub χ.testFunction_mem, h, rootNumber,
    completedLFunction, discrNormConductor_inv]
  have hc : (χ.discrNormConductor : ℂ) ^ (s / 2) * (χ.discrNormConductor : ℂ) ^ (1 - s) =
      (χ.discrNormConductor : ℂ) ^ (1 / 2 : ℂ) * (χ.discrNormConductor : ℂ) ^ ((1 - s) / 2) := by
    rw [← cpow_add _ _ hA, ← cpow_add _ _ hA]
    congr 1
    ring
  linear_combination (((π : ℂ) ^ nrComplexPlaces K)⁻¹ * χ.fourierConst χ.conductorDifferentIdele *
    (χ.toIdele (ofFinite χ.conductorDifferentIdele) : ℂ) * tateZeta (χ⁻¹).testFunction χ⁻¹ (1 - s)) * hc

theorem completedLFunction_eq_rootNumber_mul {s : ℂ}
    (hs : ∀ τ : ℝ, (∀ x : IdeleGroup K,
      (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I)) →
        s ≠ -((τ : ℂ) * I) ∧ s ≠ 1 - (τ : ℂ) * I) :
    χ.completedLFunction s = χ.rootNumber * χ⁻¹.completedLFunction (1 - s) := by
  refine χ.completedLFunction_eq_rootNumber_mul_of_eq ?_
  by_cases hχ : ∃ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) ≠ 1
  · exact χ.tateZeta_adelicFourier_testFunction χ.toFractionalIdeal_conductorDifferentIdele hχ _
  · push Not at hχ
    obtain ⟨τ, hτ⟩ := (forall_normOne_eq_one_iff χ).1 hχ
    obtain ⟨h0, h1⟩ := hs τ hτ
    refine χ.tateZeta_adelicFourier_testFunction_of_forall
      χ.toFractionalIdeal_conductorDifferentIdele hτ (fun h ↦ h1 ?_) (fun h ↦ h0 ?_)
    · linear_combination -h
    · linear_combination -h

theorem completedLFunction_eq_rootNumber_mul_of_not
    (hχ : ¬ ∃ τ : ℝ, ∀ x : IdeleGroup K,
      (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I)) (s : ℂ) :
    χ.completedLFunction s = χ.rootNumber * χ⁻¹.completedLFunction (1 - s) :=
  χ.completedLFunction_eq_rootNumber_mul fun τ hτ ↦ absurd ⟨τ, hτ⟩ hχ

theorem two_ne_pole (τ : ℝ) : (2 : ℂ) ≠ -((τ : ℂ) * I) ∧ (2 : ℂ) ≠ 1 - (τ : ℂ) * I := by
  constructor <;> intro h <;> have := congrArg re h <;> simp at this

theorem neg_one_ne_pole (τ : ℝ) :
    (-1 : ℂ) ≠ -((τ : ℂ) * I) ∧ (-1 : ℂ) ≠ 1 - (τ : ℂ) * I := by
  constructor <;> intro h <;> have := congrArg re h <;> simp at this <;> norm_num at this

theorem completedLFunction_two_ne_zero : χ.completedLFunction 2 ≠ 0 := by
  rw [χ.completedLFunction_eq (by norm_num)]
  exact mul_ne_zero (mul_ne_zero (χ.discrNormConductor_cpow_ne_zero _)
    (χ.gammaFactor_ne_zero (by norm_num))) (χ.LFunction_ne_zero (by norm_num))

theorem rootNumber_mul_rootNumber_inv : χ.rootNumber * χ⁻¹.rootNumber = 1 := by
  have h1 := χ.completedLFunction_eq_rootNumber_mul (s := 2) fun τ _ ↦ two_ne_pole τ
  have h2 := χ⁻¹.completedLFunction_eq_rootNumber_mul (s := -1) fun τ _ ↦ neg_one_ne_pole τ
  rw [inv_inv, show (1 : ℂ) - -1 = 2 by norm_num] at h2
  rw [show (1 : ℂ) - 2 = -1 by norm_num, h2, ← mul_assoc] at h1
  exact mul_right_cancel₀ χ.completedLFunction_two_ne_zero (h1.symm.trans (one_mul _).symm)

end HeckeCharacter

end

end GroundTheory.Global
end

section
open NumberField InfinitePlace IsDedekindDomain MeasureTheory Complex Topology Filter Set
open scoped NumberField.AdeleRing ComplexConjugate Real

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

theorem exists_normOne_ne_one_of_not
    (hχ : ¬ ∃ τ : ℝ, ∀ x : IdeleGroup K,
      (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I)) :
    ∃ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) ≠ 1 := by
  by_contra h
  push Not at h
  exact hχ ((forall_normOne_eq_one_iff χ).1 h)

theorem differentiable_completedLFunction
    (hχ : ¬ ∃ τ : ℝ, ∀ x : IdeleGroup K,
      (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I)) :
    Differentiable ℂ χ.completedLFunction := fun s ↦
  χ.differentiable_const_mul_cpow_half
    (differentiable_tateZeta χ.testFunction_mem (χ.exists_normOne_ne_one_of_not hχ) s)

theorem LFunction_eq_mul_completedLFunction {s : ℂ} (hs : 1 < s.re) :
    χ.LFunction s = (χ.discrNormConductor : ℂ) ^ (-(s / 2)) * (χ.gammaFactor s)⁻¹ *
      χ.completedLFunction s := by
  have h1 := χ.discrNormConductor_cpow_ne_zero (s / 2)
  have h2 := χ.gammaFactor_ne_zero (by linarith : 0 < s.re)
  rw [χ.completedLFunction_eq hs, cpow_neg]
  field_simp

theorem differentiable_cpow_mul_gammaFactor_inv :
    Differentiable ℂ fun s ↦ (χ.discrNormConductor : ℂ) ^ (-(s / 2)) * (χ.gammaFactor s)⁻¹ :=
  ((differentiable_id.div_const 2).neg.const_cpow
    (Or.inl (ofReal_ne_zero.2 χ.discrNormConductor_pos.ne'))).mul χ.differentiable_gammaFactor_inv

theorem exists_LFunction_continuation
    (hχ : ¬ ∃ τ : ℝ, ∀ x : IdeleGroup K,
      (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I)) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ s : ℂ, 1 < s.re → g s = χ.LFunction s :=
  ⟨fun s ↦ (χ.discrNormConductor : ℂ) ^ (-(s / 2)) * (χ.gammaFactor s)⁻¹ * χ.completedLFunction s,
    χ.differentiable_cpow_mul_gammaFactor_inv.mul (χ.differentiable_completedLFunction hχ),
    fun _ hs ↦ (χ.LFunction_eq_mul_completedLFunction hs).symm⟩

theorem tendsto_const_mul_cpow_half (c : ℂ) :
    Tendsto (fun s : ℂ ↦ ((π : ℂ) ^ nrComplexPlaces K)⁻¹ * (χ.discrNormConductor : ℂ) ^ (s / 2))
      (𝓝[≠] c) (𝓝 (((π : ℂ) ^ nrComplexPlaces K)⁻¹ * (χ.discrNormConductor : ℂ) ^ (c / 2))) :=
  ((((differentiable_const _).mul ((differentiable_id.div_const 2).const_cpow
    (Or.inl (ofReal_ne_zero.2 χ.discrNormConductor_pos.ne')))).continuous.tendsto c).mono_left
      nhdsWithin_le_nhds)

section Trivial

variable {χ} {τ : ℝ}
  (hτ : ∀ x : IdeleGroup K, (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I))
include hτ

theorem differentiableAt_completedLFunction_of_forall {s : ℂ} (hs₀ : s ≠ -((τ : ℂ) * I))
    (hs₁ : s ≠ 1 - (τ : ℂ) * I) : DifferentiableAt ℂ χ.completedLFunction s :=
  χ.differentiable_const_mul_cpow_half (differentiableAt_tateZeta hτ χ.testFunction_mem hs₀ hs₁)

theorem tendsto_mul_completedLFunction_neg_of_forall :
    Tendsto (fun s ↦ (s + (τ : ℂ) * I) * χ.completedLFunction s) (𝓝[≠] (-((τ : ℂ) * I)))
      (𝓝 (-(((normOneClassMeasure K univ).toReal : ℂ) * ((π : ℂ) ^ nrComplexPlaces K)⁻¹ *
        (χ.discrNormConductor : ℂ) ^ (-((τ : ℂ) * I) / 2)))) := by
  have h := (χ.tendsto_const_mul_cpow_half (-((τ : ℂ) * I))).mul
    (tendsto_mul_tateZeta_neg hτ χ.testFunction_mem)
  rw [testFunction_zero_of_forall hτ] at h
  refine (h.congr fun s ↦ ?_).trans (le_of_eq (congrArg 𝓝 (by ring)))
  rw [completedLFunction]
  ring

theorem adelicFourier_testFunction_zero_of_forall :
    adelicFourier K χ.testFunction 0 = χ.fourierConst χ.conductorDifferentIdele := by
  rw [χ.adelicFourier_testFunction χ.toFractionalIdeal_conductorDifferentIdele, smul_zero,
    testFunction_zero_of_forall (χ.inv_eq_cpow_of_forall hτ), mul_one]

theorem tendsto_mul_completedLFunction_one_sub_of_forall :
    Tendsto (fun s ↦ (s - (1 - (τ : ℂ) * I)) * χ.completedLFunction s) (𝓝[≠] (1 - (τ : ℂ) * I))
      (𝓝 (((normOneClassMeasure K univ).toReal : ℂ) * ((π : ℂ) ^ nrComplexPlaces K)⁻¹ *
        (χ.discrNormConductor : ℂ) ^ ((1 - (τ : ℂ) * I) / 2) *
          χ.fourierConst χ.conductorDifferentIdele)) := by
  have h := (χ.tendsto_const_mul_cpow_half (1 - (τ : ℂ) * I)).mul
    (tendsto_mul_tateZeta_one_sub hτ χ.testFunction_mem)
  rw [adelicFourier_testFunction_zero_of_forall hτ] at h
  refine (h.congr fun s ↦ ?_).trans (le_of_eq (congrArg 𝓝 (by ring)))
  rw [completedLFunction]
  ring

omit hτ in

theorem residue_one_sub_ne_zero :
    ((normOneClassMeasure K univ).toReal : ℂ) * ((π : ℂ) ^ nrComplexPlaces K)⁻¹ *
      (χ.discrNormConductor : ℂ) ^ ((1 - (τ : ℂ) * I) / 2) *
        χ.fourierConst χ.conductorDifferentIdele ≠ 0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero
    (ofReal_ne_zero.2 (normOneClassMeasure_univ_toReal_ne_zero K))
    (inv_ne_zero pi_pow_nrComplexPlaces_ne_zero)) (χ.discrNormConductor_cpow_ne_zero _))
    (χ.fourierConst_ne_zero χ.toFractionalIdeal_conductorDifferentIdele)

theorem completedLFunction_eq_rootNumber_mul_of_forall {s : ℂ} (hs₀ : s ≠ -((τ : ℂ) * I))
    (hs₁ : s ≠ 1 - (τ : ℂ) * I) :
    χ.completedLFunction s = χ.rootNumber * χ⁻¹.completedLFunction (1 - s) := by
  refine χ.completedLFunction_eq_rootNumber_mul fun τ' hτ' ↦ ?_
  have h : τ' = τ := by
    rw [← archExponent_eq_of_forall hτ' (Classical.arbitrary _),
      archExponent_eq_of_forall hτ (Classical.arbitrary _)]
  subst h
  exact ⟨hs₀, hs₁⟩

theorem gammaFactor_neg_of_forall : χ.gammaFactor (-((τ : ℂ) * I)) = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary (InfinitePlace K))) ?_
  unfold infiniteGamma
  rw [infiniteTau_of_forall hτ, infiniteWeight_of_forall hτ]
  split_ifs
  · rw [show -((τ : ℂ) * I) + (τ : ℂ) * I + ((0 : ℤ) : ℂ) = 0 by push_cast; ring]
    exact Gammaℝ_eq_zero_iff.2 ⟨0, by simp⟩
  · rw [show -((τ : ℂ) * I) + (τ : ℂ) * I + (((0 : ℤ).natAbs : ℕ) : ℂ) / 2 = 0 by push_cast; ring,
      Gammaℂ_def, Complex.Gamma_zero, mul_zero]

theorem exists_LFunction_continuation_of_forall :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g {1 - (τ : ℂ) * I}ᶜ ∧
      (∀ s : ℂ, 1 < s.re → g s = χ.LFunction s) ∧
      ∃ r : ℂ, r ≠ 0 ∧ Tendsto (fun s ↦ (s - (1 - (τ : ℂ) * I)) * g s)
        (𝓝[≠] (1 - (τ : ℂ) * I)) (𝓝 r) := by
  set c : ℂ := -((τ : ℂ) * I) with hc
  set d : ℂ := 1 - (τ : ℂ) * I with hd
  set h : ℂ → ℂ := fun s ↦ (χ.discrNormConductor : ℂ) ^ (-(s / 2)) * (χ.gammaFactor s)⁻¹ with hh
  have hdiff : Differentiable ℂ h := χ.differentiable_cpow_mul_gammaFactor_inv
  have hcd : c ≠ d := fun h0 ↦ by
    have := congrArg re h0
    simp [hc, hd] at this
  have hhc : h c = 0 := by
    simp only [hh, hc, gammaFactor_neg_of_forall hτ, inv_zero, mul_zero]
  set g₀ : ℂ → ℂ := fun s ↦ h s * χ.completedLFunction s with hg₀
  set rc : ℂ := -(((normOneClassMeasure K univ).toReal : ℂ) * ((π : ℂ) ^ nrComplexPlaces K)⁻¹ *
    (χ.discrNormConductor : ℂ) ^ (-((τ : ℂ) * I) / 2)) with hrc

  have hres : Tendsto (fun s ↦ (s - c) * χ.completedLFunction s) (𝓝[≠] c) (𝓝 rc) := by
    refine (tendsto_mul_completedLFunction_neg_of_forall hτ).congr fun s ↦ ?_
    rw [hc, sub_neg_eq_add]
  have hslope : Tendsto (fun s ↦ (s - c)⁻¹ * h s) (𝓝[≠] c) (𝓝 (deriv h c)) := by
    refine (hasDerivAt_iff_tendsto_slope.1 (hdiff c).hasDerivAt).congr fun s ↦ ?_
    rw [slope_fun_def_field, hhc]
    beta_reduce
    rw [sub_zero, div_eq_inv_mul]
  have hlim : Tendsto g₀ (𝓝[≠] c) (𝓝 (deriv h c * rc)) := by
    refine (hslope.mul hres).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : s - c ≠ 0 := sub_ne_zero.2 hs
    simp only [hg₀]
    field_simp
  set G : ℂ → ℂ := Function.update g₀ c (deriv h c * rc) with hG
  have hGeq : ∀ s, s ≠ c → G s = g₀ s := fun s hs ↦ Function.update_of_ne hs _ _
  refine ⟨G, ?_, fun s hs ↦ ?_, ?_⟩
  · have hnhds : ({d}ᶜ : Set ℂ) ∈ 𝓝 c := isOpen_compl_singleton.mem_nhds hcd
    refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff hnhds).1 ⟨?_, ?_⟩
    · refine DifferentiableOn.congr (fun z hz ↦ ?_) fun z hz ↦ hGeq z hz.2
      simp only [Set.mem_sdiff, mem_compl_iff, mem_singleton_iff] at hz
      exact ((hdiff z).mul (differentiableAt_completedLFunction_of_forall hτ hz.2 hz.1)).differentiableWithinAt
    · rw [hG, continuousAt_update_same]
      exact hlim
  · have hsc : s ≠ c := fun h0 ↦ by
      have := congrArg re h0
      simp [hc] at this
      linarith
    rw [hGeq s hsc, χ.LFunction_eq_mul_completedLFunction hs]
  · refine ⟨h d * (((normOneClassMeasure K univ).toReal : ℂ) * ((π : ℂ) ^ nrComplexPlaces K)⁻¹ *
      (χ.discrNormConductor : ℂ) ^ ((1 - (τ : ℂ) * I) / 2) *
        χ.fourierConst χ.conductorDifferentIdele), mul_ne_zero ?_ residue_one_sub_ne_zero, ?_⟩
    · exact mul_ne_zero (χ.discrNormConductor_cpow_ne_zero _) (inv_ne_zero (χ.gammaFactor_ne_zero
        (by simp [hd])))
    · have hh' : Tendsto h (𝓝[≠] d) (𝓝 (h d)) :=
        ((hdiff d).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
      refine (hh'.mul (tendsto_mul_completedLFunction_one_sub_of_forall hτ)).congr' ?_
      have hne : ∀ᶠ s in 𝓝[≠] d, s ≠ c :=
        eventually_nhdsWithin_of_eventually_nhds (isOpen_compl_singleton.mem_nhds hcd.symm)
      filter_upwards [hne] with s hs
      rw [hGeq s hs]
      simp only [hg₀]
      ring

end Trivial

end HeckeCharacter

end

end GroundTheory.Global
end

section
open NumberField InfinitePlace IsDedekindDomain MeasureTheory Complex Topology Filter Set
open scoped NumberField.AdeleRing Real

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

namespace HeckeCharacter

theorem one_toIdele_eq_cpow (x : IdeleGroup K) :
    ((1 : HeckeCharacter K).toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ (((0 : ℝ) : ℂ) * I) := by
  simp [toIdele_apply]

theorem discrNormConductor_one : (1 : HeckeCharacter K).discrNormConductor = |(discr K : ℝ)| := by
  rw [discrNormConductor, conductor_eq_top_of_forall one_toIdele_eq_cpow, Ideal.absNorm_top]
  simp

open Classical in

theorem gammaFactor_one (s : ℂ) :
    (1 : HeckeCharacter K).gammaFactor s =
      Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K := by
  have h : ∀ w, (1 : HeckeCharacter K).infiniteGamma w s =
      if w.IsReal then Gammaℝ s else Gammaℂ s := fun w ↦ by
    rw [infiniteGamma, infiniteTau_of_forall one_toIdele_eq_cpow,
      infiniteWeight_of_forall one_toIdele_eq_cpow]
    simp
  rw [gammaFactor, Finset.prod_congr rfl fun w _ ↦ h w, prod_eq_prod_mul_prod]
  have h1 : ∀ w : {w : InfinitePlace K // IsReal w},
      (if w.1.IsReal then Gammaℝ s else Gammaℂ s) = Gammaℝ s := fun w ↦ if_pos w.2
  have h2 : ∀ w : {w : InfinitePlace K // IsComplex w},
      (if w.1.IsReal then Gammaℝ s else Gammaℂ s) = Gammaℂ s := fun w ↦
    if_neg (not_isReal_iff_isComplex.2 w.2)
  simp only [h1, h2, Finset.prod_const, Finset.card_univ]

end HeckeCharacter

open HeckeCharacter

variable (K)

def completedDedekindZeta (s : ℂ) : ℂ := (1 : HeckeCharacter K).completedLFunction s

theorem differentiableAt_completedDedekindZeta {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    DifferentiableAt ℂ (completedDedekindZeta K) s :=
  differentiableAt_completedLFunction_of_forall (one_toIdele_eq_cpow (K := K)) (by simpa using hs₀)
    (by simpa using hs₁)

theorem tendsto_mul_completedDedekindZeta_zero_volume :
    Tendsto (fun s ↦ s * completedDedekindZeta K s) (𝓝[≠] 0)
      (𝓝 (-(((normOneClassMeasure K univ).toReal : ℂ) * ((π : ℂ) ^ nrComplexPlaces K)⁻¹))) := by
  have h := tendsto_mul_completedLFunction_neg_of_forall (one_toIdele_eq_cpow (K := K))
  simp only [ofReal_zero, zero_mul, neg_zero, add_zero, zero_div, cpow_zero, mul_one] at h
  exact h

theorem completedDedekindZeta_eq_rootNumber_mul {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    completedDedekindZeta K s =
      (1 : HeckeCharacter K).rootNumber * completedDedekindZeta K (1 - s) := by
  have h := completedLFunction_eq_rootNumber_mul_of_forall (one_toIdele_eq_cpow (K := K)) (s := s)
    (by simpa using hs₀) (by simpa using hs₁)
  rwa [inv_one] at h

theorem tendsto_one_sub_nhdsNE_one : Tendsto (fun s : ℂ ↦ 1 - s) (𝓝[≠] 1) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun s hs ↦ ?_⟩
  · exact ((continuous_const.sub continuous_id).tendsto' 1 0 (by simp)).mono_left nhdsWithin_le_nhds
  · exact sub_ne_zero.2 (Ne.symm hs)

theorem tendsto_sub_one_mul_completedDedekindZeta_rootNumber :
    Tendsto (fun s ↦ (s - 1) * completedDedekindZeta K s) (𝓝[≠] 1)
      (𝓝 ((1 : HeckeCharacter K).rootNumber *
        (((normOneClassMeasure K univ).toReal : ℂ) * ((π : ℂ) ^ nrComplexPlaces K)⁻¹))) := by
  have h := ((tendsto_mul_completedDedekindZeta_zero_volume K).comp
    tendsto_one_sub_nhdsNE_one).const_mul (-(1 : HeckeCharacter K).rootNumber)
  rw [show -(1 : HeckeCharacter K).rootNumber * -(((normOneClassMeasure K univ).toReal : ℂ) *
    ((π : ℂ) ^ nrComplexPlaces K)⁻¹) = (1 : HeckeCharacter K).rootNumber *
      (((normOneClassMeasure K univ).toReal : ℂ) * ((π : ℂ) ^ nrComplexPlaces K)⁻¹) by ring] at h
  refine h.congr' ?_
  have h0 : ∀ᶠ s in 𝓝[≠] (1 : ℂ), s ≠ 0 :=
    eventually_nhdsWithin_of_eventually_nhds (isOpen_compl_singleton.mem_nhds one_ne_zero)
  filter_upwards [h0, self_mem_nhdsWithin] with s hs₀ hs₁
  rw [Function.comp_apply, completedDedekindZeta_eq_rootNumber_mul K hs₀ hs₁]
  ring

theorem differentiable_discr_cpow_mul_gamma_inv :
    Differentiable ℂ fun s : ℂ ↦ ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(s / 2)) *
      (Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K)⁻¹ := by
  have h := (1 : HeckeCharacter K).differentiable_cpow_mul_gammaFactor_inv
  simp only [discrNormConductor_one, gammaFactor_one] at h
  exact h

def normalizedDedekindZeta (s : ℂ) : ℂ :=
  ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(s / 2)) *
    (Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K)⁻¹ * completedDedekindZeta K s

theorem normalizedDedekindZeta_eq {s : ℂ} (hs : 1 < s.re) : normalizedDedekindZeta K s = dedekindZeta K s := by
  have h := (1 : HeckeCharacter K).LFunction_eq_mul_completedLFunction hs
  rw [LFunction_one, discrNormConductor_one, gammaFactor_one] at h
  exact h.symm

theorem residue_normalizedDedekindZeta_at_one :
    Tendsto (fun s ↦ (s - 1) * normalizedDedekindZeta K s) (𝓝[≠] 1)
      (𝓝 (((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-((1 : ℂ) / 2)) *
        (Gammaℝ 1 ^ nrRealPlaces K * Gammaℂ 1 ^ nrComplexPlaces K)⁻¹ *
        ((1 : HeckeCharacter K).rootNumber *
        (((normOneClassMeasure K univ).toReal : ℂ) * ((π : ℂ) ^ nrComplexPlaces K)⁻¹)))) := by
  have hH := ((differentiable_discr_cpow_mul_gamma_inv K).continuous.tendsto 1).mono_left
    (nhdsWithin_le_nhds (s := {1}ᶜ))
  refine (hH.mul (tendsto_sub_one_mul_completedDedekindZeta_rootNumber K)).congr fun s ↦ ?_
  simp only [normalizedDedekindZeta]
  ring

theorem tendsto_ofReal_nhdsGT_one : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
  refine tendsto_nhdsWithin_iff.2 ⟨(continuous_ofReal.tendsto' 1 1 (by simp)).mono_left
    nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun s (hs : 1 < s) ↦ ?_⟩
  simp only [mem_compl_iff, mem_singleton_iff]
  exact_mod_cast hs.ne'

theorem rootNumber_mul_volume :
    (1 : HeckeCharacter K).rootNumber *
      ((|(discr K : ℝ)| ^ (-(1 / 2 : ℝ)) * (normOneClassMeasure K univ).toReal : ℝ) : ℂ) =
      (dedekindZeta_residue K : ℂ) := by
  have hres : _ = (dedekindZeta_residue K : ℂ) := tendsto_nhds_unique
    ((residue_normalizedDedekindZeta_at_one K).comp tendsto_ofReal_nhdsGT_one)
    ((tendsto_sub_one_mul_dedekindZeta_nhdsGT K).congr' (by
      filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
      rw [Function.comp_apply, normalizedDedekindZeta_eq K (by simpa using hs)]))
  rw [Gammaℝ_one, Gammaℂ_one, one_pow, one_mul] at hres
  have ha : 0 ≤ |(discr K : ℝ)| := abs_nonneg _
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [← hres, ofReal_mul, ofReal_cpow ha]
  push_cast
  simp only [one_div, inv_pow, inv_inv]
  field_simp

theorem HeckeCharacter.rootNumber_one : (1 : HeckeCharacter K).rootNumber = 1 := by
  have h2 := (1 : HeckeCharacter K).rootNumber_mul_rootNumber_inv
  rw [inv_one] at h2
  have h := rootNumber_mul_volume K
  have ha : 0 < |(discr K : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))
  have hv : 0 < (normOneClassMeasure K univ).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (normOneClassMeasure_univ_toReal_ne_zero K).symm
  have hb : 0 < |(discr K : ℝ)| ^ (-(1 / 2 : ℝ)) * (normOneClassMeasure K univ).toReal :=
    mul_pos (Real.rpow_pos_of_pos ha _) hv
  have hW : (1 : HeckeCharacter K).rootNumber = ((dedekindZeta_residue K /
      (|(discr K : ℝ)| ^ (-(1 / 2 : ℝ)) * (normOneClassMeasure K univ).toReal) : ℝ) : ℂ) := by
    rw [ofReal_div, ← h, mul_div_cancel_right₀ _ (ofReal_ne_zero.2 hb.ne')]
  have ht : 0 < dedekindZeta_residue K /
      (|(discr K : ℝ)| ^ (-(1 / 2 : ℝ)) * (normOneClassMeasure K univ).toReal) :=
    div_pos (dedekindZeta_residue_pos K) hb
  rw [hW, ← ofReal_mul, ofReal_eq_one] at h2
  rw [hW, show dedekindZeta_residue K /
      (|(discr K : ℝ)| ^ (-(1 / 2 : ℝ)) * (normOneClassMeasure K univ).toReal) = 1 by nlinarith,
    ofReal_one]

theorem normOneClassMeasure_univ_toReal_eq :
    (normOneClassMeasure K univ).toReal = Real.sqrt |(discr K : ℝ)| * dedekindZeta_residue K := by
  have h := rootNumber_mul_volume K
  rw [rootNumber_one, one_mul, ofReal_inj] at h
  have ha : 0 < |(discr K : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K))
  rw [← h, Real.sqrt_eq_rpow, ← mul_assoc, ← Real.rpow_add ha]
  norm_num

open NumberField.Units in

theorem normOneClassMeasure_univ_toReal_eq_classNumber :
    (normOneClassMeasure K univ).toReal = 2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K *
      regulator K * classNumber K / torsionOrder K := by
  rw [normOneClassMeasure_univ_toReal_eq, dedekindZeta_residue_def]
  have h1 : 0 < Real.sqrt |(discr K : ℝ)| :=
    Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K)))
  have h2 : (0 : ℝ) < torsionOrder K := Nat.cast_pos.2 (torsionOrder_pos K)
  field_simp

theorem completedDedekindZeta_one_sub {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    completedDedekindZeta K (1 - s) = completedDedekindZeta K s := by
  rw [completedDedekindZeta_eq_rootNumber_mul K hs₀ hs₁, rootNumber_one, one_mul]

theorem tendsto_mul_completedDedekindZeta_zero :
    Tendsto (fun s ↦ s * completedDedekindZeta K s) (𝓝[≠] 0)
      (𝓝 (-(((Real.sqrt |(discr K : ℝ)| * dedekindZeta_residue K : ℝ) : ℂ) *
        ((π : ℂ) ^ nrComplexPlaces K)⁻¹))) := by
  have h := tendsto_mul_completedDedekindZeta_zero_volume K
  rwa [normOneClassMeasure_univ_toReal_eq] at h

end

end GroundTheory.Global
end
