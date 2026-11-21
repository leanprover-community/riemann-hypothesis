import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TraceHermNondegenerate
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SupLeL2PrincipalTorus
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointwiseNormSqPullbackTensorEqProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IntegrableOnFundamentalDomainOfContinuous
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBasisSpanEqOfCommensurable
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTorusOfSelfD
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ThetaFunctionTorusL2Norm
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ProjAEqSumReps
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockHxDifferentiable
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRowHighestHarmonicPolyDerivUnitaryAction
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariant

section
namespace GlobalTheory

open Complex ReciprocityTheory.ChartRestriction.G.I2

namespace FockTranslation

variable {ι : Type} [Fintype ι]

theorem herm_add_left (u v w : EuclideanSpace ℂ ι) : Hf (u + v) w = Hf u w + Hf v w := by
  simp [Hf, add_mul, Finset.sum_add_distrib]

theorem herm_add_right (u v w : EuclideanSpace ℂ ι) : Hf u (v + w) = Hf u v + Hf u w := by
  simp [Hf, mul_add, Finset.sum_add_distrib]

theorem herm_sub_left (u v w : EuclideanSpace ℂ ι) : Hf (u - v) w = Hf u w - Hf v w := by
  simp [Hf, sub_mul, Finset.sum_sub_distrib]

theorem herm_sub_right (u v w : EuclideanSpace ℂ ι) : Hf u (v - w) = Hf u v - Hf u w := by
  simp [Hf, mul_sub, Finset.sum_sub_distrib]

theorem herm_neg_left (u w : EuclideanSpace ℂ ι) : Hf (-u) w = -Hf u w := by
  simp [Hf]

theorem herm_neg_right (u w : EuclideanSpace ℂ ι) : Hf u (-w) = -Hf u w := by
  simp [Hf]

theorem herm_zero_right (u : EuclideanSpace ℂ ι) : Hf u 0 = 0 := by
  simp [Hf]

theorem herm_smul_right (c : ℂ) (u w : EuclideanSpace ℂ ι) :
    Hf u (c • w) = (starRingEnd ℂ) c * Hf u w := by
  simp only [Hf, PiLp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem herm_conj (u w : EuclideanSpace ℂ ι) : (starRingEnd ℂ) (Hf u w) = Hf w u := by
  simp only [Hf, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem herm_sub_swap (u w : EuclideanSpace ℂ ι) :
    Hf w u = Hf u w - 2 * I * ((Hf u w).im : ℂ) := by
  have h := Complex.sub_conj (Hf u w)
  rw [herm_conj] at h
  push_cast at h
  linear_combination -h

theorem herm_self (x : EuclideanSpace ℂ ι) : Hf x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Hf, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem herm_self_re (x : EuclideanSpace ℂ ι) : (Hf x x).re = ‖x‖ ^ 2 := by
  rw [herm_self, Complex.ofReal_re]

theorem herm_self_im (x : EuclideanSpace ℂ ι) : (Hf x x).im = 0 := by
  rw [herm_self, Complex.ofReal_im]

theorem herm_re_swap (u w : EuclideanSpace ℂ ι) : (Hf w u).re = (Hf u w).re := by
  rw [← herm_conj u w, Complex.conj_re]

theorem herm_im_swap (u w : EuclideanSpace ℂ ι) : (Hf w u).im = -(Hf u w).im := by
  rw [← herm_conj u w, Complex.conj_im]

theorem herm_differentiable (a : EuclideanSpace ℂ ι) :
    Differentiable ℂ fun v : EuclideanSpace ℂ ι => Hf v a := by
  unfold Hf
  fun_prop

end FockTranslation

open FockTranslation in

theorem fock_translation_laws {ι : Type} [Fintype ι] (U : ℕ → EuclideanSpace ℂ ι → (EuclideanSpace ℂ ι → ℂ) → EuclideanSpace ℂ ι → ℂ)
    (hU : ∀ (q : ℕ) a F v, U q a F v = cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a)) (q : ℕ) :
    (∀ a b F, U q a (U q b F) = cexp (-(q * Real.pi * I * (Hf a b).im)) • U q (a + b) F) ∧ (∀ F, U q 0 F = F) ∧
    (∀ a F, (fun v => U q a F (-v)) = U q (-a) (fun v => F (-v))) ∧
    (∀ a F (M : ℕ), (U q a)^[M] F = U q ((M : ℂ) • a) F) ∧
    (∀ a F v, ‖U q a F v‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) = ‖F (v - a)‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v - a‖ ^ 2)) ∧
    (∀ (Y : GT ι) F, F ∈ Y.Sec q ↔ Differentiable ℂ F ∧ ∀ γ ∈ lat Y.b, Y.ka γ • U q γ F = F) ∧
    (∀ (Y : GT ι) a, (∀ γ ∈ lat Y.b, ∃ k : ℤ, q * (Hf a γ).im = k) → ∀ F ∈ Y.Sec q, U q a F ∈ Y.Sec q) ∧
    (∀ (φ : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (N : ℕ), (∀ v w, Hf (φ v) (φ w) = N * Hf v w) →
      ∀ a F, U (q * N) a (F ∘ φ) = U q (φ a) F ∘ φ) := by
  have h1 : ∀ a b F, U q a (U q b F) =
      cexp (-(q * Real.pi * I * (Hf a b).im)) • U q (a + b) F := by
    intro a b F
    funext v
    simp only [hU, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add, sub_sub]
    congr 2
    simp only [herm_add_left, herm_add_right, herm_sub_left]
    rw [herm_sub_swap a b]
    ring
  have h2 : ∀ F, U q 0 F = F := by
    intro F
    funext v
    simp [hU, herm_zero_right]
  have h6 : ∀ (Y : GT ι) F, F ∈ Y.Sec q ↔
      Differentiable ℂ F ∧ ∀ γ ∈ lat Y.b, Y.ka γ • U q γ F = F := by
    intro Y F
    have key : ∀ γ v, (Y.ka γ • U q γ F) (v + γ) =
        Y.ka γ * cexp (q * Real.pi * Hf v γ + q * Real.pi * Hf γ γ / 2) * F v := by
      intro γ v
      simp only [hU, Pi.smul_apply, smul_eq_mul, add_sub_cancel_right, herm_add_left]
      rw [← mul_assoc]
      congr 3
      ring
    refine and_congr_right fun _ => forall₂_congr fun γ _ => ⟨fun h => ?_, fun h v => ?_⟩
    · funext w
      have := key γ (w - γ)
      rw [← h, sub_add_cancel] at this
      exact this
    · rw [← key, h]
  refine ⟨h1, h2, ?_, ?_, ?_, h6, ?_, ?_⟩
  · intro a F
    funext v
    simp only [hU, herm_neg_left, herm_neg_right, neg_neg]
    congr 2
    abel
  · intro a F M
    induction M with
    | zero => simp [h2]
    | succ M ih =>
      rw [Function.iterate_succ_apply', ih, h1]
      have : (Hf a ((M : ℂ) • a)).im = 0 := by
        rw [herm_smul_right]
        simp [herm_self_im]
      rw [this]
      have e : a + (M : ℂ) • a = ((M + 1 : ℕ) : ℂ) • a := by
        push_cast
        rw [add_smul, one_smul, add_comm]
      simp [e]
  · intro a F v
    rw [hU, norm_mul, mul_pow, Complex.norm_exp, mul_comm (_ ^ 2) (‖F (v - a)‖ ^ 2), mul_assoc,
      ← Real.exp_nat_mul, ← Real.exp_add]
    congr 2
    rw [← herm_self_re v, ← herm_self_re (v - a)]
    have e : (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2 : ℂ) =
        ((q * Real.pi : ℝ) : ℂ) * Hf v a - ((q * Real.pi / 2 : ℝ) : ℂ) * Hf a a := by
      push_cast
      ring
    rw [e]
    simp only [herm_sub_left, herm_sub_right, Complex.sub_re, Complex.re_ofReal_mul,
      herm_re_swap v a]
    push_cast
    ring
  · intro Y a ha F hF
    rw [h6] at hF ⊢
    obtain ⟨hd, hF⟩ := hF
    refine ⟨?_, fun γ hγ => ?_⟩
    · have e : U q a F = fun v =>
          cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a) :=
        funext fun v => hU q a F v
      rw [e]
      have := herm_differentiable a
      fun_prop
    · obtain ⟨k, hk⟩ := ha γ hγ
      have hk' : (q : ℂ) * ((Hf a γ).im : ℂ) = k := by exact_mod_cast hk
      have hc : U q γ (U q a F) = U q a (U q γ F) := by
        rw [h1, h1, add_comm γ a]
        congr 1
        rw [Complex.exp_eq_exp_iff_exists_int]
        refine ⟨k, ?_⟩
        rw [herm_im_swap a γ, ← hk']
        push_cast
        ring
      rw [hc]
      conv_rhs => rw [← hF γ hγ]
      funext v
      simp only [Pi.smul_apply, smul_eq_mul, hU q a]
      ring
  · intro φ N hφ a F
    funext v
    simp only [hU, Function.comp_apply, hφ, map_sub]
    congr 2
    push_cast
    ring

end GlobalTheory
end

section
namespace GlobalTheory

open Complex ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory

namespace IsogenySum

open FockTranslation

variable {ι : Type} [Fintype ι]

theorem eq_zero_of_im_lattice (Y : GT ι) {a : EuclideanSpace ℂ ι}
    (h : ∀ y ∈ lat Y.b, (Hf y a).im = 0) : a = 0 := by
  have hspan : ∀ v, (Hf v a).im = 0 := by
    intro v
    have hv : v ∈ Submodule.span ℝ (Set.range Y.b) := by
      rw [Y.b.span_eq]; exact Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx => exact h x (Submodule.subset_span hx)
    | zero => simp [Hf]
    | add x y _ _ hx hy => rw [herm_add_left, Complex.add_im, hx, hy, add_zero]
    | smul c x _ hx =>
      have e : Hf (c • x) a = (c : ℂ) * Hf x a := by
        simp only [Hf, PiLp.smul_apply, Complex.real_smul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e, Complex.im_ofReal_mul, hx, mul_zero]
  have h1 := hspan (I • a)
  have e : Hf (I • a) a = I * Hf a a := by
    simp only [Hf, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, Complex.I_mul_im, herm_self_re] at h1
  simpa using h1

theorem mem_lattice_of_int (Y : GT ι) {a : EuclideanSpace ℂ ι}
    (h : ∀ y ∈ lat Y.b, ∃ k : ℤ, (Hf y a).im = k) : a ∈ lat Y.b := by
  have hfl : ∀ y ∈ lat Y.b, ((⌊(Hf y a).im⌋ : ℤ) : ℝ) = (Hf y a).im := by
    intro y hy
    obtain ⟨k, hk⟩ := h y hy
    rw [hk, Int.floor_intCast]
  let φ : lat Y.b →+ ℤ :=
    { toFun := fun y => ⌊(Hf (y : EuclideanSpace ℂ ι) a).im⌋
      map_zero' := by simp [Hf]
      map_add' := by
        intro y y'
        apply Int.cast_injective (α := ℝ)
        push_cast
        rw [hfl _ ((lat Y.b).add_mem y.2 y'.2), hfl _ y.2, hfl _ y'.2, herm_add_left,
          Complex.add_im] }
  obtain ⟨x0, hx0, hφ⟩ := Y.perfect φ
  have h0 : a + x0 = 0 := by
    apply eq_zero_of_im_lattice Y
    intro y hy
    have := hφ ⟨y, hy⟩
    simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
    rw [hfl y hy] at this
    rw [herm_add_right, Complex.add_im, this, herm_im_swap x0 y]
    ring
  have : a = -x0 := eq_neg_of_add_eq_zero_left h0
  rw [this]
  exact (lat Y.b).neg_mem hx0

theorem exists_common_sublattice (Y Y' : GT ι) (R : Finset (EuclideanSpace ℂ ι))
    (hR' : ∀ y ∈ lat Y'.b, ∃ r ∈ R, y - r ∈ lat Y.b) :
    ∃ b : Module.Basis (Fin (2 * Fintype.card ι)) ℝ (EuclideanSpace ℂ ι),
      lat b ≤ lat Y.b ∧ lat b ≤ lat Y'.b := by
  have hN : ∀ i, ∃ N : ℤ, N ≠ 0 ∧ N • Y'.b i ∈ lat Y.b := by
    intro i
    have hi : Y'.b i ∈ lat Y'.b := Submodule.subset_span ⟨i, rfl⟩
    choose r hr hr' using fun n : ℤ => hR' (n • Y'.b i) ((lat Y'.b).smul_mem n hi)
    obtain ⟨n, m, hnm, e⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℤ => (⟨r n, hr n⟩ : R))
    have e' : r n = r m := congrArg Subtype.val e
    refine ⟨n - m, sub_ne_zero.2 hnm, ?_⟩
    have := (lat Y.b).sub_mem (hr' n) (hr' m)
    rw [e', sub_sub_sub_cancel_right] at this
    rwa [sub_smul]
  choose N hN0 hN using hN
  have hu : ∀ i, IsUnit (N i : ℝ) := fun i => (Int.cast_ne_zero.2 (hN0 i)).isUnit
  refine ⟨Y'.b.isUnitSMul hu, ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul]
    exact hN i
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul]
    exact (lat Y'.b).smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)

section

variable (U : ℕ → EuclideanSpace ℂ ι → (EuclideanSpace ℂ ι → ℂ) → EuclideanSpace ℂ ι → ℂ)
  (hU : ∀ (q : ℕ) a F v, U q a F v =
    cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a))
include hU

theorem pairing_density_add (Y : GT ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ Y.Sec 1)
    (y y' : EuclideanSpace ℂ ι) {x : EuclideanSpace ℂ ι} (hx : x ∈ lat Y.b)
    (v : EuclideanSpace ℂ ι) :
    U 1 y F (v + x) * (starRingEnd ℂ) (U 1 y' F (v + x)) * cexp (-(Real.pi * Hf (v + x) (v + x))) =
      cexp (2 * Real.pi * I * (Hf x (y - y')).im) *
        (U 1 y F v * (starRingEnd ℂ) (U 1 y' F v) * cexp (-(Real.pi * Hf v v))) := by
  have hk : Y.ka x * (starRingEnd ℂ) (Y.ka x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Y.ka_abs x hx]; simp
  have e : ∀ z, v + x - z = (v - z) + x := fun z => by abel
  simp only [hU, e, hF.2 x hx, map_mul, ← Complex.exp_conj, map_add, map_sub, map_div₀,
    herm_conj, Complex.conj_ofReal, Nat.cast_one, one_mul, map_ofNat]
  have key : cexp (Real.pi * Hf (v + x) y - Real.pi * Hf y y / 2) *
      cexp (Real.pi * Hf (v - y) x + Real.pi * Hf x x / 2) *
      cexp (Real.pi * Hf y' (v + x) - Real.pi * Hf y' y' / 2) *
      cexp (Real.pi * Hf x (v - y') + Real.pi * Hf x x / 2) *
      cexp (-(Real.pi * Hf (v + x) (v + x))) =
      cexp (2 * Real.pi * I * (Hf x (y - y')).im) *
      cexp (Real.pi * Hf v y - Real.pi * Hf y y / 2) *
      cexp (Real.pi * Hf y' v - Real.pi * Hf y' y' / 2) * cexp (-(Real.pi * Hf v v)) := by
    simp only [← Complex.exp_add]
    congr 1
    simp only [herm_add_left, herm_add_right, herm_sub_left, herm_sub_right, Complex.sub_im]
    rw [herm_sub_swap x y, herm_sub_swap x y']
    push_cast
    ring
  linear_combination (F (v - y) * (starRingEnd ℂ) (F (v - y'))) * key +
    (F (v - y) * (starRingEnd ℂ) (F (v - y')) *
      cexp (Real.pi * Hf (v + x) y - Real.pi * Hf y y / 2) *
      cexp (Real.pi * Hf (v - y) x + Real.pi * Hf x x / 2) *
      cexp (Real.pi * Hf y' (v + x) - Real.pi * Hf y' y' / 2) *
      cexp (Real.pi * Hf x (v - y') + Real.pi * Hf x x / 2) *
      cexp (-(Real.pi * Hf (v + x) (v + x)))) * hk

theorem translate_differentiable {F : EuclideanSpace ℂ ι → ℂ} (hF : Differentiable ℂ F)
    (a : EuclideanSpace ℂ ι) : Differentiable ℂ (U 1 a F) := by
  have e : U 1 a F = fun v =>
      cexp ((1 : ℕ) * Real.pi * Hf v a - (1 : ℕ) * Real.pi * Hf a a / 2) * F (v - a) :=
    funext fun v => hU 1 a F v
  rw [e]
  have := herm_differentiable a
  fun_prop

theorem pairing_density_continuous {F : EuclideanSpace ℂ ι → ℂ} (hF : Differentiable ℂ F)
    (y y' : EuclideanSpace ℂ ι) : Continuous fun v =>
      U 1 y F v * (starRingEnd ℂ) (U 1 y' F v) * cexp (-(Real.pi * Hf v v)) := by
  have h1 := (translate_differentiable U hU hF y).continuous
  have h2 := (translate_differentiable U hU hF y').continuous
  simp only [herm_self]
  fun_prop

theorem integral_pairing_density_eq_zero (Y : GT ι) {F : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ Y.Sec 1) {κ : Type} [Fintype κ] (b : Module.Basis κ ℝ (EuclideanSpace ℂ ι))
    (hb : lat b ≤ lat Y.b) (y y' : EuclideanSpace ℂ ι)
    (hint : ∀ x ∈ lat b, ∃ k : ℤ, (Hf x (y - y')).im = k) (hne : y - y' ∉ lat Y.b) :
    ∫ v in ZSpan.fundamentalDomain b,
      U 1 y F v * (starRingEnd ℂ) (U 1 y' F v) * cexp (-(Real.pi * Hf v v)) = 0 := by
  obtain ⟨x, hx, hx'⟩ : ∃ x ∈ lat Y.b, cexp (2 * Real.pi * I * (Hf x (y - y')).im) ≠ 1 := by
    by_contra hcon
    push Not at hcon
    refine hne (mem_lattice_of_int Y fun x hx => ?_)
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 (hcon x hx)
    refine ⟨k, ?_⟩
    rw [mul_comm (k : ℂ)] at hk
    have := mul_left_cancel₀ Complex.two_pi_I_ne_zero hk
    exact_mod_cast this
  have h := setIntegral_fundamentalDomain_add_right volume b
    (fun v => U 1 y F v * (starRingEnd ℂ) (U 1 y' F v) * cexp (-(Real.pi * Hf v v)))
    (fun γ hγ v => by
      obtain ⟨k, hk⟩ := hint γ hγ
      simp only [pairing_density_add U hU Y hF y y' (hb hγ), hk]
      rw [mul_comm _ ((k : ℝ) : ℂ), Complex.ofReal_intCast, Complex.exp_int_mul_two_pi_mul_I,
        one_mul]) x
  simp only [pairing_density_add U hU Y hF y y' hx] at h
  rw [integral_const_mul] at h
  have h2 := sub_eq_zero.2 h
  rw [← sub_one_mul] at h2
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hx')

theorem translate_translate (Y : GT ι)
    (hY : ∀ x ∈ lat Y.b, ∀ y ∈ lat Y.b,
      Y.ka (x + y) = Y.ka x * Y.ka y * cexp (Real.pi * I * (Hf x y).im))
    {x y : EuclideanSpace ℂ ι} (hx : x ∈ lat Y.b) (hy : y ∈ lat Y.b)
    (F : EuclideanSpace ℂ ι → ℂ) :
    Y.ka x • U 1 x (Y.ka y • U 1 y F) = Y.ka (x + y) • U 1 (x + y) F := by
  have h1 := (fock_translation_laws U hU 1).1 x y F
  have e : U 1 x (Y.ka y • U 1 y F) = Y.ka y • U 1 x (U 1 y F) := by
    funext v
    simp only [Pi.smul_apply, smul_eq_mul, hU 1 x]
    ring
  rw [e, h1, hY x hx y hy, smul_smul, smul_smul]
  congr 2
  obtain ⟨k, hk⟩ := Y.integral x y hx hy
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-k, ?_⟩
  rw [hk]
  push_cast
  ring

theorem thetaSectionPointwiseNormSq_periodic (Y : GT ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ Y.Sec 1)
    {γ : EuclideanSpace ℂ ι} (hγ : γ ∈ lat Y.b) (v : EuclideanSpace ℂ ι) :
    Y.ptN2 1 F (v + γ) = Y.ptN2 1 F v := by
  obtain ⟨-, -, -, -, h5, h6, -⟩ := fock_translation_laws U hU 1
  have h := h5 γ F (v + γ)
  rw [add_sub_cancel_right] at h
  unfold GT.ptN2
  rw [← h]
  conv_lhs => rw [← ((h6 Y F).1 hF).2 γ hγ]
  rw [Pi.smul_apply, norm_smul, Y.ka_abs γ hγ, one_mul]

end

theorem continuous_thetaSectionPointwiseNormSq (Y : GT ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : Continuous F) :
    Continuous (Y.ptN2 1 F) := by
  unfold GT.ptN2
  fun_prop

theorem thetaSectionPointwiseNormSq_eq (Y : GT ι) (F : EuclideanSpace ℂ ι → ℂ) (v : EuclideanSpace ℂ ι) :
    ((Y.ptN2 1 F v : ℝ) : ℂ) = F v * (starRingEnd ℂ) (F v) * cexp (-(Real.pi * Hf v v)) := by
  rw [GT.ptN2, Complex.mul_conj, Complex.normSq_eq_norm_sq, herm_self]
  push_cast
  congr 2
  ring

end IsogenySum

open IsogenySum FockTranslation in

theorem isogeny_sum_mem_and_norm {ι : Type} [Fintype ι] (U : ℕ → EuclideanSpace ℂ ι → (EuclideanSpace ℂ ι → ℂ) → EuclideanSpace ℂ ι → ℂ)
    (hU : ∀ (q : ℕ) a F v, U q a F v = cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a))
    (Y Y' : GT ι) (hY : (∀ x ∈ lat Y.b, ∀ y ∈ lat Y.b, Y.ka (x + y) = Y.ka x * Y.ka y * cexp (Real.pi * I * (Hf x y).im))) (hY' : (∀ x ∈ lat Y'.b, ∀ y ∈ lat Y'.b, Y'.ka (x + y) = Y'.ka x * Y'.ka y * cexp (Real.pi * I * (Hf x y).im)))
    (hag : ∀ x ∈ lat Y.b, x ∈ lat Y'.b → Y.ka x = Y'.ka x)
    (R : Finset (EuclideanSpace ℂ ι)) (hR : ∀ y ∈ R, y ∈ lat Y'.b) (hR' : ∀ y ∈ lat Y'.b, ∃! r ∈ R, y - r ∈ lat Y.b)
    (F : EuclideanSpace ℂ ι → ℂ) (hF : F ∈ Y.Sec 1) :
    (∑ y ∈ R, Y'.ka y • U 1 y F) ∈ Y'.Sec 1 ∧ Y'.l2 1 (∑ y ∈ R, Y'.ka y • U 1 y F) = R.card * Y.l2 1 F := by
  classical
  obtain ⟨-, -, -, -, h5, h6, -⟩ := fock_translation_laws U hU 1
  have hinj : ∀ y ∈ R, ∀ y' ∈ R, y - y' ∈ lat Y.b → y = y' := fun y hy y' hy' h =>
    (hR' y (hR y hy)).unique ⟨hy, by simp⟩ ⟨hy', h⟩
  have hdiff : Differentiable ℂ (∑ y ∈ R, Y'.ka y • U 1 y F) :=
    Differentiable.sum fun y _ => (translate_differentiable U hU hF.1 y).const_smul _
  have hmem : (∑ y ∈ R, Y'.ka y • U 1 y F) ∈ Y'.Sec 1 := by
    refine (h6 Y' _).2 ⟨hdiff, fun γ hγ => ?_⟩
    have e : Y'.ka γ • U 1 γ (∑ y ∈ R, Y'.ka y • U 1 y F) =
        ∑ y ∈ R, Y'.ka γ • U 1 γ (Y'.ka y • U 1 y F) := by
      funext v
      simp only [Pi.smul_apply, smul_eq_mul, hU 1 γ, Finset.sum_apply, Finset.mul_sum]
    rw [e]
    choose σ hσ hσ' using fun (y) (hy : y ∈ R) =>
      (hR' (γ + y) ((lat Y'.b).add_mem hγ (hR y hy))).exists
    have hσinj : ∀ y (hy : y ∈ R) y' (hy' : y' ∈ R), σ y hy = σ y' hy' → y = y' := by
      intro y hy y' hy' h
      refine hinj y hy y' hy' ?_
      have := (lat Y.b).sub_mem (hσ' y hy) (hσ' y' hy')
      rwa [h, sub_sub_sub_cancel_right, add_sub_add_left_eq_sub] at this
    refine Finset.sum_bij σ hσ hσinj ?_ ?_
    · intro z hz
      obtain ⟨a, ha, h⟩ := Finset.surj_on_of_inj_on_of_card_le σ hσ
        (fun a₁ a₂ h₁ h₂ h => hσinj a₁ h₁ a₂ h₂ h) le_rfl z hz
      exact ⟨a, ha, h.symm⟩
    · intro y hy
      have hd' : γ + y - σ y hy ∈ lat Y'.b :=
        (lat Y'.b).sub_mem ((lat Y'.b).add_mem hγ (hR y hy)) (hR _ (hσ y hy))
      have hfix : Y'.ka (γ + y - σ y hy) • U 1 (γ + y - σ y hy) F = F := by
        rw [← hag _ (hσ' y hy) hd']
        exact ((h6 Y F).1 hF).2 _ (hσ' y hy)
      rw [translate_translate U hU Y' hY' hγ (hR y hy)]
      conv_rhs => rw [← hfix]
      rw [translate_translate U hU Y' hY' (hR _ (hσ y hy)) hd', add_sub_cancel]
  refine ⟨hmem, ?_⟩
  obtain ⟨b, hb, hb'⟩ := exists_common_sublattice Y Y' R fun y hy => (hR' y hy).exists
  have e1 := average_fundamentalDomain_eq_real volume Y'.b b _
    (continuous_thetaSectionPointwiseNormSq Y' hdiff.continuous) (fun γ hγ v => thetaSectionPointwiseNormSq_periodic U hU Y' hmem hγ v) hb' 0
  have e2 := fun a => average_fundamentalDomain_eq_real volume Y.b b _
    (continuous_thetaSectionPointwiseNormSq Y hF.1.continuous) (fun γ hγ v => thetaSectionPointwiseNormSq_periodic U hU Y hF hγ v) hb a
  simp only [add_zero] at e1
  have e3 : ∫ v in ZSpan.fundamentalDomain b, Y'.ptN2 1 (∑ y ∈ R, Y'.ka y • U 1 y F) v =
      ∑ y ∈ R, ∫ v in ZSpan.fundamentalDomain b, Y.ptN2 1 F (v + -y) := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal]
    have hpt : ∀ v, ((Y'.ptN2 1 (∑ y ∈ R, Y'.ka y • U 1 y F) v : ℝ) : ℂ) =
        ∑ y ∈ R, ∑ y' ∈ R, (Y'.ka y * (starRingEnd ℂ) (Y'.ka y')) *
          (U 1 y F v * (starRingEnd ℂ) (U 1 y' F v) * cexp (-(Real.pi * Hf v v))) := by
      intro v
      rw [thetaSectionPointwiseNormSq_eq]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
      rw [Finset.sum_mul_sum]
      simp only [Finset.sum_mul]
      exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => by ring
    have hint : ∀ y y', IntegrableOn (fun v => (Y'.ka y * (starRingEnd ℂ) (Y'.ka y')) *
          (U 1 y F v * (starRingEnd ℂ) (U 1 y' F v) * cexp (-(Real.pi * Hf v v))))
          (ZSpan.fundamentalDomain b) volume := fun y y' =>
      integrableOn_fundamentalDomain_of_continuous volume b _
        (continuous_const.mul (pairing_density_continuous U hU hF.1 y y'))
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [integral_finset_sum _ fun y _ => integrable_finset_sum _ fun y' _ => hint y y',
      Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [integral_finset_sum _ fun y' _ => hint y y', Finset.sum_eq_single_of_mem y hy]
    · have hk : Y'.ka y * (starRingEnd ℂ) (Y'.ka y) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Y'.ka_abs y (hR y hy)]; simp
      rw [hk, ← integral_complex_ofReal]
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      simp only [one_mul]
      rw [← thetaSectionPointwiseNormSq_eq Y, ← sub_eq_add_neg]
      exact congrArg _ (h5 y F v)
    · intro y' hy' hne
      rw [integral_const_mul, integral_pairing_density_eq_zero U hU Y hF b hb y y'
        (fun x hx => Y'.integral _ _ (hb' hx) ((lat Y'.b).sub_mem (hR y hy) (hR y' hy')))
        (fun h => hne (hinj y hy y' hy' h).symm), mul_zero]
  unfold GT.l2
  rw [← e1, setAverage_eq, e3, Finset.smul_sum]
  simp only [← setAverage_eq, e2]
  simp

end GlobalTheory
end

section
namespace GlobalTheory.TensorLat

open NumberField ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}

theorem norm_sq_contr_apply_le (γ : Fin n → Vsp dim) (w : Fin n → E) (i : Idx dim) :
    ‖contr γ w i‖ ^ 2 ≤ (∑ k, ‖i.1 (w k)‖ ^ 2) * ∑ k, ‖γ k i‖ ^ 2 := by
  refine le_trans ?_ (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖i.1 (w k)‖)
    fun k => ‖γ k i‖)
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  rw [contr_apply]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp

theorem norm_sq_contr_le (γ : Fin n → Vsp dim) (w : Fin n → E) {R : ℝ}
    (hw : ∀ τ : E →+* ℂ, ∑ k, ‖τ (w k)‖ ^ 2 ≤ R) :
    ‖contr γ w‖ ^ 2 ≤ R * ‖flat γ‖ ^ 2 := by
  rw [norm_sq_flat, EuclideanSpace.norm_sq_eq]
  simp only [EuclideanSpace.norm_sq_eq (γ _)]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => (norm_sq_contr_apply_le γ w i).trans ?_
  exact mul_le_mul_of_nonneg_right (hw i.1) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem norm_contr_le (γ : Fin n → Vsp dim) (w : Fin n → E) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hw : ∀ τ : E →+* ℂ, ∑ k, ‖τ (w k)‖ ^ 2 ≤ ρ ^ 2) :
    ‖contr γ w‖ ≤ ρ * ‖flat γ‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow]
  exact norm_sq_contr_le γ w hw

theorem exists_contr_ne_zero {ι : Type*} (v : ι → Fin n → E)
    (hspan : Submodule.span E (Set.range v) = ⊤) {γ : Fin n → Vsp dim} (hγ : γ ≠ 0) :
    ∃ i, contr γ (v i) ≠ 0 := by
  by_contra h
  push Not at h
  exact hγ (eq_zero_of_contr_span hspan (by rintro _ ⟨i, rfl⟩; exact h i))

theorem le_mul_norm_flat (X : PT E) (Λ' : Submodule (𝓞 E) (Fin n → E)) {ι : Type*}
    (v : ι → Fin n → E) (hv : ∀ i, v i ∈ Λ') (hspan : Submodule.span E (Set.range v) = ⊤)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hlen : ∀ i (τ : E →+* ℂ), ∑ k, ‖τ (v i k)‖ ^ 2 ≤ ρ ^ 2)
    {lam : ℝ} (hlam : ∀ x ∈ X.L, x ≠ 0 → lam ≤ ‖x‖)
    {γ : Fin n → Vsp X.dim} (hγ : γ ∈ tensorLat X Λ') (h0 : γ ≠ 0) :
    lam ≤ ρ * ‖flat γ‖ := by
  obtain ⟨i, hi⟩ := exists_contr_ne_zero v hspan h0
  exact (hlam _ (hγ _ (hv i)) hi).trans (norm_contr_le γ (v i) hρ (hlen i))

omit [IsCMField E] in

theorem span_eq_top_of_rat {S : Set (Fin n → E)} (h : Submodule.span ℚ S = ⊤) :
    Submodule.span E S = ⊤ :=
  eq_top_iff.2 fun x _ => Submodule.span_le_restrictScalars ℚ E S (h ▸ Submodule.mem_top (x := x))

theorem le_mul_norm_flat_of_selfDual (X : PT E) (Λ' : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    {lam : ℝ} (hlam : ∀ x ∈ X.L, x ≠ 0 → lam ≤ ‖x‖)
    {γ : Fin n → Vsp X.dim} (hγ : γ ∈ tensorLat X Λ') (h0 : γ ≠ 0) :
    lam ≤ 2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E * ‖flat γ‖ := by
  obtain ⟨v, hv, -, hspan, hlen⟩ := exists_short_vectors Λ' hfg hint hdual
  have hr : 0 ≤ rdE E := Real.rpow_nonneg (abs_nonneg _) _
  exact le_mul_norm_flat X Λ' v hv (span_eq_top_of_rat hspan) (by positivity) hlen hlam hγ h0

example (X : PT E) (x : Vsp X.dim) (hx : x ∈ X.L) (k : Fin n) :
    Pi.single k x ∈ tensorLat X (ReciprocityTheory.GeometryOfNumbersTheory.stdLat E n) ∧
      ‖flat (Pi.single k x : Fin n → Vsp X.dim)‖ ^ 2 = ‖x‖ ^ 2 := by
  constructor
  · refine mem_tensorLat_stdLat.2 fun j => ?_
    by_cases h : j = k
    · subst h; simpa using hx
    · simp [h]
  · rw [norm_sq_flat, Finset.sum_eq_single k]
    · simp
    · intro j _ h; simp [h]
    · simp

end GlobalTheory.TensorLat
end

section
namespace GlobalTheory.TensorLat

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem isogeny_sum_tensorLat (T : PT E) (w₀ : 𝓞 E) (hw : (w₀ : E) + cc (w₀ : E) = 1)
    (heps : ∀ x ∈ T.L, (T.eps x : ℝ) = Real.cos (Real.pi * (Hf x (act w₀ x)).im))
    (Λ' : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    (R : Finset (Fin n → Vsp T.dim)) (hR : ∀ y ∈ R, y ∈ tensorLat T Λ')
    (hR' : ∀ y ∈ tensorLat T Λ', ∃! r, r ∈ R ∧ ∀ k, y k - r k ∈ T.L)
    (F : (Fin n → Vsp T.dim) → ℂ) (hF : F ∈ T.Sec 1 n)
    (Y' : GT (Fin n × Idx T.dim)) (hY' : ∀ γ, flat γ ∈ lat Y'.b ↔ γ ∈ tensorLat T Λ')
    (hka' : ∀ γ, Y'.ka (flat γ) = tensorEps w₀ γ) :
    (∑ y ∈ R, tensorEps w₀ y • T.U 1 y F) ∘ flat.symm ∈ Y'.Sec 1 ∧
      Y'.l2 1 ((∑ y ∈ R, tensorEps w₀ y • T.U 1 y F) ∘ flat.symm) = R.card * T.l2 1 F := by
  classical
  obtain ⟨⟨Y, hY, hka⟩, h2, h3, h4⟩ := principal_torus_of_selfDual T (stdLat E n) stdLat_fg
    (fun _ hx => mem_stdLat_iff_herm.1 hx) (fun _ hx => mem_stdLat_iff_herm.2 hx) w₀ hw
  obtain ⟨-, h2', -, -⟩ := principal_torus_of_selfDual T Λ' hfg hint hdual w₀ hw
  obtain ⟨hFm, hFl⟩ := (h3 heps Y hY hka).2 F hF
  set U : ℕ → EuclideanSpace ℂ (Fin n × Idx T.dim) → (EuclideanSpace ℂ (Fin n × Idx T.dim) → ℂ) →
      EuclideanSpace ℂ (Fin n × Idx T.dim) → ℂ := fun q a G v =>
    cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * G (v - a) with hUdef
  have hU : ∀ (q : ℕ) a G v,
      U q a G v = cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * G (v - a) :=
    fun _ _ _ _ => rfl
  let e : (Fin n → Vsp T.dim) ↪ EuclideanSpace ℂ (Fin n × Idx T.dim) :=
    ⟨flat, (flat (n := n) (ι := Idx T.dim)).injective⟩
  have he : ∀ y, e y = flat y := fun _ => rfl
  have key := isogeny_sum_mem_and_norm U hU Y Y' (h2 Y hY hka).2 (h2' Y' hY' hka').2
    (fun x _ _ => by
      obtain ⟨γ, rfl⟩ := (flat (n := n) (ι := Idx T.dim)).surjective x
      rw [hka, hka'])
    (R.map e)
    (fun y hy => by
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_map.1 hy
      exact (hY' γ).2 (hR γ hγ))
    (fun y hy => by
      obtain ⟨γ, rfl⟩ := (flat (n := n) (ι := Idx T.dim)).surjective y
      obtain ⟨r, ⟨hr, hr'⟩, hu⟩ := hR' γ ((hY' γ).1 hy)
      refine ⟨flat r, ⟨Finset.mem_map.2 ⟨r, hr, rfl⟩, ?_⟩, ?_⟩
      · rw [← map_sub, hY, mem_tensorLat_stdLat]
        exact hr'
      · rintro z ⟨hz, hz'⟩
        obtain ⟨r', hr2, rfl⟩ := Finset.mem_map.1 hz
        rw [he, ← map_sub, hY, mem_tensorLat_stdLat] at hz'
        rw [he, hu r' ⟨hr2, hz'⟩])
    (F ∘ flat.symm) hFm
  have e1 : (∑ y ∈ R.map e, Y'.ka y • U 1 y (F ∘ flat.symm)) =
      (∑ y ∈ R, tensorEps w₀ y • T.U 1 y F) ∘ flat.symm := by
    rw [Finset.sum_map]
    funext v
    simp only [he, hka', h4 U hU, Finset.sum_apply, Function.comp_apply, Pi.smul_apply]
  rw [e1, Finset.card_map, hFl] at key
  exact key

theorem exists_min_period (T : PT E) (Λ' : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    {lam : ℝ} (hlam : 0 < lam) (hmin : ∀ x ∈ T.L, x ≠ 0 → lam ≤ ‖x‖) :
    ∃ lam' : ℝ, 0 < lam' ∧ (∀ γ ∈ tensorLat T Λ', γ ≠ 0 → lam' ≤ ‖flat γ‖) ∧
      (1 + 4 * Real.sqrt (2 * Fintype.card (Fin n × Idx T.dim)) / (Real.sqrt Real.pi * lam')) ^
          Fintype.card (Fin n × Idx T.dim) =
        (1 + 4 * Real.sqrt (2 * Fintype.card (Idx T.dim) * n) *
          (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^
          (Fintype.card (Idx T.dim) * n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, one_pos, fun γ _ h => absurd (Subsingleton.elim γ 0) h, by simp⟩
  have hf : (0 : ℝ) < fdeg E := by
    have h1 := ShortVectors.finrank_eq (E := E)
    have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
    exact_mod_cast (by omega : 0 < fdeg E)
  have hr : 0 < rdE E := Real.rpow_pos_of_pos
    (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero E)) _
  have hρ : 0 < 2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E := by positivity
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  set ρ := 2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E with hρdef
  refine ⟨lam / ρ, by positivity, fun γ hγ h0 => ?_, ?_⟩
  · rw [div_le_iff₀' hρ]
    exact le_mul_norm_flat_of_selfDual T Λ' hfg hint hdual hmin hγ h0
  · rw [Fintype.card_prod, Fintype.card_fin, mul_comm n, Nat.cast_mul, ← mul_assoc]
    congr 2
    field_simp

open Classical in

theorem norm_sum_jet_isogeny_sum_le (T : PT E) (w₀ : 𝓞 E) (hw : (w₀ : E) + cc (w₀ : E) = 1)
    (heps : ∀ x ∈ T.L, (T.eps x : ℝ) = Real.cos (Real.pi * (Hf x (act w₀ x)).im))
    (Λ' : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    (R : Finset (Fin n → Vsp T.dim)) (hR : ∀ y ∈ R, y ∈ tensorLat T Λ')
    (hR' : ∀ y ∈ tensorLat T Λ', ∃! r, r ∈ R ∧ ∀ k, y k - r k ∈ T.L)
    (F : (Fin n → Vsp T.dim) → ℂ) (hF : F ∈ T.Sec 1 n)
    (lam : ℝ) (hlam : 0 < lam) (hmin : ∀ γ ∈ T.L, γ ≠ 0 → lam ≤ ‖γ‖)
    {κ : Type} (J : Finset κ) (c : κ → ℂ) (hc : ∀ j ∈ J, ‖c j‖ ≤ 1) (y : κ → Fin n → Vsp T.dim)
    (P : MvPolynomial (Letter n T.dim) ℂ) (a : ℕ) (hP : P.IsHomogeneous a) :
    ‖∑ j ∈ J, c j * polyDeriv P dir (T.U 1 (y j) (∑ r ∈ R, tensorEps w₀ r • T.U 1 r F)) 0‖ ≤
      J.card * (∑ m ∈ P.support, ‖P.coeff m‖) * (Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) *
        Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card (Idx T.dim) * n) *
          (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^
          (Fintype.card (Idx T.dim) * n) * Real.sqrt (R.card * T.l2 1 F) := by
  obtain ⟨Y', hY', hka'⟩ := exists_tensorTorus (X := T) hfg hint hdual w₀
  obtain ⟨hm, hl⟩ := isogeny_sum_tensorLat T w₀ hw heps Λ' hfg hint hdual R hR hR' F hF Y' hY' hka'
  obtain ⟨lam', hlam', hmin', hC⟩ := exists_min_period T Λ' hfg hint hdual hlam hmin
  set U : ℕ → EuclideanSpace ℂ (Fin n × Idx T.dim) → (EuclideanSpace ℂ (Fin n × Idx T.dim) → ℂ) →
      EuclideanSpace ℂ (Fin n × Idx T.dim) → ℂ := fun q a G v =>
    cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * G (v - a) with hUdef
  have hU : ∀ (q : ℕ) a G v,
      U q a G v = cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * G (v - a) :=
    fun _ _ _ _ => rfl
  have key := theta_value_bound sup_le_l2_principal_torus U hU Y' _ hm lam' hlam'
    (fun x hx h0 => by
      obtain ⟨γ, rfl⟩ := (flat (n := n) (ι := Idx T.dim)).surjective x
      exact hmin' γ ((hY' γ).1 hx) fun h => h0 (by rw [h, map_zero]))
    J c hc (fun j => flat (y j)) P a hP
  rw [hl, hC] at key
  refine le_of_eq_of_le ?_ (key.trans_eq (by ring))
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [translate_comp_flat_symm T U hU, ← polyDeriv_comp_flat_symm, map_zero]
  congr!

end GlobalTheory.TensorLat

namespace GlobalTheory

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD TensorLat

open Classical in

theorem normalised_theta_value_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (T : PT E) (w₀ : 𝓞 E) (hw : (w₀ : E) + cc (w₀ : E) = 1)
    (heps : ∀ x ∈ T.L, (T.eps x : ℝ) = Real.cos (Real.pi * (Hf x (act w₀ x)).im))
    (s : (Fin 1 → Vsp T.dim) → ℂ) (hs : s ∈ T.Sec 1 1) (hs0 : s ≠ 0)
    (Λ' : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    (R : Finset (Fin n → Vsp T.dim)) (hR : ∀ y ∈ R, y ∈ tensorLat T Λ')
    (hR' : ∀ y ∈ tensorLat T Λ', ∃! r, r ∈ R ∧ ∀ k, y k - r k ∈ T.L)
    (β : ℂ) (hβ : ‖β‖ ^ 2 = R.card)
    (lam : ℝ) (hlam : 0 < lam) (hmin : ∀ γ ∈ T.L, γ ≠ 0 → lam ≤ ‖γ‖)
    {κ : Type} (J : Finset κ) (c : κ → ℂ) (hc : ∀ j ∈ J, ‖c j‖ ≤ 1) (y : κ → Fin n → Vsp T.dim)
    (P : MvPolynomial (Letter n T.dim) ℂ) (a : ℕ) (hP : P.IsHomogeneous a) :
    β ≠ 0 ∧ 0 < T.l2 1 s ∧
    ‖β⁻¹ * ∑ j ∈ J, c j * polyDeriv P dir (T.U 1 (y j)
        (∑ r ∈ R, tensorEps w₀ r • T.U 1 r (ReciprocityTheory.ChartRestriction.G.I2.tens T fun _ => s))) 0‖ /
        Real.sqrt (T.l2 1 s) ^ n ≤
      J.card * (∑ m ∈ P.support, ‖P.coeff m‖) * (Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) *
        Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card (Idx T.dim) * n) *
          (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^
          (Fintype.card (Idx T.dim) * n) := by
  have hl : 0 < T.l2 1 s := ThetaBound.l2_pos_of_mem_sec_of_ne_zero T le_rfl hs hs0
  have hRpos : 0 < R.card := by
    obtain ⟨r, ⟨hr, -⟩, -⟩ := hR' 0 (Submodule.zero_mem _)
    exact Finset.card_pos.2 ⟨r, hr⟩
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [norm_zero, zero_pow two_ne_zero] at hβ
    exact hRpos.ne (by exact_mod_cast hβ)
  refine ⟨hβ0, hl, ?_⟩
  have key := norm_sum_jet_isogeny_sum_le T w₀ hw heps Λ' hfg hint hdual R hR hR'
    (ReciprocityTheory.ChartRestriction.G.I2.tens T fun _ => s) (tens_mem T fun _ => hs) lam hlam hmin J c hc y P a hP
  have hsq : Real.sqrt (R.card * T.l2 1 (ReciprocityTheory.ChartRestriction.G.I2.tens T fun _ : Fin n => s)) =
      ‖β‖ * Real.sqrt (T.l2 1 s) ^ n := by
    rw [l2_tens_eq_prod, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← hβ,
      Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), mul_mul_mul_comm, ← mul_pow,
      Real.mul_self_sqrt hl.le, sq]
  have hb : 0 < ‖β‖ := norm_pos_iff.2 hβ0
  have hs' : 0 < Real.sqrt (T.l2 1 s) ^ n := pow_pos (Real.sqrt_pos.2 hl) n
  rw [hsq] at key
  rw [norm_mul, norm_inv, div_le_iff₀ hs', inv_mul_le_iff₀ hb]
  exact key.trans_eq (by ring)

example {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (T : PT E) :
    (∀ y ∈ ({0} : Finset (Fin n → Vsp T.dim)), y ∈ tensorLat T (ReciprocityTheory.GeometryOfNumbersTheory.stdLat E n)) ∧
      ∀ y ∈ tensorLat T (ReciprocityTheory.GeometryOfNumbersTheory.stdLat E n),
        ∃! r, r ∈ ({0} : Finset (Fin n → Vsp T.dim)) ∧ ∀ k, y k - r k ∈ T.L := by
  refine ⟨fun y hy => by rw [Finset.mem_singleton.1 hy]; exact Submodule.zero_mem _,
    fun y hy => ⟨0, ⟨Finset.mem_singleton_self _, fun k => ?_⟩,
      fun r hr => Finset.mem_singleton.1 hr.1⟩⟩
  simpa using mem_tensorLat_stdLat.1 hy k

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ThetaPT

open MeasureTheory

theorem Hf_add_smul_left {κ : Type} [Fintype κ] (c : ℂ) (v w u : EuclideanSpace ℂ κ) :
    I2.Hf (v + c • w) u = I2.Hf v u + c * I2.Hf w u := by
  unfold I2.Hf
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem Hf_neg_right {κ : Type} [Fintype κ] (v w : EuclideanSpace ℂ κ) :
    I2.Hf v (-w) = -I2.Hf v w := by
  unfold I2.Hf
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

theorem Hf_neg_left {κ : Type} [Fintype κ] (v w : EuclideanSpace ℂ κ) :
    I2.Hf (-v) w = -I2.Hf v w := by
  unfold I2.Hf
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

theorem cexp_pi_int (k : ℤ) : cexp (Real.pi * I * (k : ℂ)) = ((Real.cos (Real.pi * k) : ℝ) : ℂ) := by
  have h : (Real.pi : ℂ) * I * (k : ℂ) = ((Real.pi * k : ℝ) : ℂ) * I := by push_cast; ring
  have hs : Real.sin (Real.pi * k) = 0 := by rw [mul_comm]; exact Real.sin_int_mul_pi k
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hs]
  simp

theorem l2_one_eq_integral_fundamentalDomain_div_volume {E : Type} [Field E] [NumberField E] {g : ℕ} (T : I2.PT E)
    (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim) (θ : (Fin g → ℂ) → ℂ)
    (hs : (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) ∈ T.Sec 1 1)
    (A : AddSubgroup (Fin g → ℂ)) (hL : ∀ z, z ∈ A ↔ ψ z ∈ T.L) (Fd : Set (Fin g → ℂ))
    (hFd : IsAddFundamentalDomain A Fd volume) :
    T.l2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) =
      (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (I2.Hf (ψ z) (ψ z)).re)) / (volume Fd).toReal := by
  classical

  have hper : ∀ (a : A) (z : Fin g → ℂ),
      ‖θ (a +ᵥ z)‖ ^ 2 * Real.exp (-Real.pi * (I2.Hf (ψ (a +ᵥ z)) (ψ (a +ᵥ z))).re) =
        ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (I2.Hf (ψ z) (ψ z)).re) := by
    intro a z
    have ha : ψ a ∈ T.L := (hL a).1 a.2
    obtain ⟨-, hq⟩ := hs
    have h := hq (fun _ => ψ a) (fun _ => ha) (fun _ => ψ z)
    simp only [Pi.add_apply, I2.HC, Fin.sum_univ_one, Fin.prod_univ_one, pow_one, Nat.cast_one,
      _root_.one_mul, map_add, LinearEquiv.symm_apply_apply] at h
    have hε : ‖((T.eps (ψ a) : ℤ) : ℂ)‖ = 1 := by
      rcases T.eps_pm _ ha with h1 | h1 <;> simp [h1]
    have hv : (a +ᵥ z : Fin g → ℂ) = z + a := by
      change (a : Fin g → ℂ) + z = z + a
      exact add_comm _ _
    have hre : ((Real.pi : ℂ) * I2.Hf (ψ z) (ψ a) + (Real.pi : ℂ) * I2.Hf (ψ a) (ψ a) / 2).re =
        Real.pi * (I2.Hf (ψ z) (ψ a)).re + Real.pi * (I2.Hf (ψ a) (ψ a)).re / 2 := by
      simp [Complex.add_re, Complex.div_ofNat_re]
    rw [hv, h, map_add, GlobalTheory.EtaAn.ThetaTorus.Hf_add_re, norm_mul, norm_mul, hε, _root_.one_mul,
      Complex.norm_exp, hre, mul_pow, sq (Real.exp _), ← Real.exp_add,
      mul_comm (Real.exp _) (‖θ z‖ ^ 2), _root_.mul_assoc, ← Real.exp_add]
    congr 2
    ring

  let ψR : (Fin g → ℂ) ≃L[ℝ] I2.Vsp T.dim := (ψ.restrictScalars ℝ).toContinuousLinearEquiv
  have hψR : ∀ z, ψR z = ψ z := fun z => rfl
  let eR : (Fin g → ℂ) ≃L[ℝ] (Fin 1 → I2.Vsp T.dim) :=
    ψR.trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ (I2.Vsp T.dim)).symm
  have heR : ∀ z, eR z = fun _ => ψ z := fun z => rfl

  have hl2 : T.l2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) =
      ⨍ z in ψ ⁻¹' ZSpan.fundamentalDomain T.b,
        ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (I2.Hf (ψ z) (ψ z)).re) := by
    have hset : eR ⁻¹' T.fd 1 = ψ ⁻¹' ZSpan.fundamentalDomain T.b := by
      ext z
      simp [I2.PT.fd, heR]
    unfold I2.PT.l2
    rw [GlobalTheory.EtaAn.ThetaTorus.setAverage_equiv volume volume eR, hset]
    congr 1
    funext z
    simp [I2.PT.ptN2, I2.HC, heR]

  have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving ψR volume volume :=
    ⟨ψR.continuous.measurable, MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure _ _⟩

  have hfd0 : IsAddFundamentalDomain A (ψ ⁻¹' ZSpan.fundamentalDomain T.b) volume := by
    have h0 := ZSpan.isAddFundamentalDomain T.b (volume : Measure (I2.Vsp T.dim))
    refine h0.preimage_of_equiv hqmp
      (e := fun y => (⟨ψ.symm y, (hL _).2 (by simp only [LinearEquiv.apply_symm_apply]; exact y.2)⟩ : A)) ⟨?_, ?_⟩ ?_
    · intro y y' hyy
      have := congrArg Subtype.val hyy
      exact Subtype.ext (ψ.symm.injective this)
    · intro a
      refine ⟨⟨ψ a, (hL a).1 a.2⟩, ?_⟩
      ext1
      simp
    · intro y z
      change ψ (ψ.symm (y : I2.Vsp T.dim) + z) = (y : I2.Vsp T.dim) + ψ z
      simp
  have hcA : Countable A := by
    have : Countable (Submodule.span ℤ (Set.range T.b)) := inferInstance
    refine Function.Injective.countable
      (f := fun a : A => (⟨ψ a, (hL a).1 a.2⟩ : Submodule.span ℤ (Set.range T.b))) ?_
    intro a a' h
    exact Subtype.ext (ψ.injective (congrArg Subtype.val h))
  rw [hl2, MeasureTheory.setAverage_eq, MeasureTheory.measureReal_def, hfd0.measure_eq hFd,
    hfd0.setIntegral_eq hFd hper, smul_eq_mul, div_eq_inv_mul]

theorem theta_on_torus :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (w : 𝓞 E) (L : Lt E r) (x : Frame X.Ψ r) (t : ℝ) (T : I2.PT E) (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim) (e : Fin g ≃ I2.Idx T.dim), IsSympl X bas → x ∈ X.dom → (w : E) + cc (w : E) = 1 → (T.r = r ∧ (∀ z z', I2.Hf (ψ z) (ψ z') = hx X bas idx x z z') ∧ (∀ ga, ga ∈ T.L ↔ ∃ u ∈ L, ga = ψ (pv X idx x u)) ∧ (∀ (a : 𝓞 E) u, ψ (pv X idx x ((a : E) • u)) = I2.act a (ψ (pv X idx x u))) ∧ (∀ ga ∈ T.L, (T.eps ga : ℝ) = Real.cos (Real.pi * (I2.Hf ga (I2.act w ga)).im)) ∧ (∀ j, (e j).1 = rowType X (idx j) ∧ ψ (Pi.single j 1) = ((Real.sqrt t : ℝ) : ℂ) • EuclideanSpace.single (e j) (1 : ℂ))) → (∀ θ : (Fin g → ℂ) → ℂ, IsTheta1 X bas idx (w : E) x L θ → (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) ∈ T.Sec 1 1 ∧ (MeanOne X bas idx x L θ → T.l2 1 (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) = 1)) ∧ (∀ (n k : ℕ) (th : Fin n → (Fin g → ℂ) → ℂ) (a z : Fin n → Fin g → ℂ), ∏ b, fock X bas idx x k (a b) (th b) (z b) = T.U k (fun b => -ψ (a b)) (fun v => ∏ b, th b (ψ.symm (v b))) (fun b => ψ (z b))) ∧ ∀ u ∈ L, eps1 X (w : E) u = (T.eps (ψ (pv X idx x u)) : ℂ) := by
  intro E _ _ _ r X g bas idx w L x t T ψ e hsy hxd hw hT
  obtain ⟨-, hH, hL, hact, heps, -⟩ := hT
  have hlaws := hx_laws E r X g bas idx 0 hsy ⟨0, rfl⟩ x hxd
  have hpvL : ∀ u ∈ L, ψ (pv X idx x u) ∈ T.L := fun u hu => (hL _).2 ⟨u, hu, rfl⟩

  have hsign : ∀ u ∈ L, eps1 X (w : E) u = (T.eps (ψ (pv X idx x u)) : ℂ) := by
    intro u hu
    have hmem := hpvL u hu
    obtain ⟨k, hk⟩ := T.integral _ _ hmem (T.stable w _ hmem)
    have him : (I2.Hf (ψ (pv X idx x u)) (I2.act w (ψ (pv X idx x u)))).im =
        (EF X u ((w : E) • u) : ℝ) := by
      rw [← hact, hH]
      exact hlaws.2.2.1 u _
    have hq : ((EF X u ((w : E) • u) : ℚ) : ℂ) = (k : ℂ) := by
      have h1 : ((EF X u ((w : E) • u) : ℚ) : ℝ) = (k : ℝ) := by rw [← him, hk]
      have h2 := congrArg (fun s : ℝ => (s : ℂ)) h1
      push_cast at h2
      exact h2
    have hs1 : ((T.eps (ψ (pv X idx x u)) : ℤ) : ℂ) = ((Real.cos (Real.pi * k) : ℝ) : ℂ) := by
      have h1 := heps _ hmem
      rw [hk] at h1
      rw [← h1]
      norm_cast
    unfold eps1
    rw [hq, cexp_pi_int, hs1]

  have hHadd : ∀ z a : Fin g → ℂ, hx X bas idx x (z + (1 / 2 : ℂ) • a) a =
      I2.Hf (ψ z) (ψ a) + I2.Hf (ψ a) (ψ a) / 2 := by
    intro z a
    rw [← hH, map_add, map_smul, Hf_add_smul_left]
    ring
  have hHadd' : ∀ z a : Fin g → ℂ, hx X bas idx x (z + (1 / 2 : ℂ) • a) a =
      hx X bas idx x z a + hx X bas idx x a a / 2 := by
    intro z a
    rw [hHadd, hH, hH]

  have hthper : ∀ θ, IsTheta1 X bas idx (w : E) x L θ → ∀ u ∈ L, ∀ z,
      θ (z + pv X idx x u) = (T.eps (ψ (pv X idx x u)) : ℂ) *
        cexp (Real.pi * I2.Hf (ψ z) (ψ (pv X idx x u)) +
          Real.pi * I2.Hf (ψ (pv X idx x u)) (ψ (pv X idx x u)) / 2) * θ z := by
    intro θ hθ u hu z
    obtain ⟨-, hθp⟩ := hθ
    have h := congrFun (hθp u hu) z
    simp only [Pi.smul_apply, smul_eq_mul, fock, hHadd, hsign u hu, Nat.cast_one, _root_.one_mul] at h
    set ε : ℂ := ((T.eps (ψ (pv X idx x u)) : ℤ) : ℂ) with hεdef
    set P := I2.Hf (ψ z) (ψ (pv X idx x u))
    set Q := I2.Hf (ψ (pv X idx x u)) (ψ (pv X idx x u))
    have hε : ε * ε = 1 := by
      rcases T.eps_pm _ (hpvL u hu) with h1 | h1 <;> simp [hεdef, h1]
    have hc : cexp (Real.pi * P + Real.pi * Q / 2) * cexp (-(Real.pi * (P + Q / 2))) = 1 := by
      rw [← Complex.exp_add, show (Real.pi : ℂ) * P + Real.pi * Q / 2 + -(Real.pi * (P + Q / 2)) = 0 by ring,
        Complex.exp_zero]
    rw [← h]
    linear_combination (-(cexp (Real.pi * P + Real.pi * Q / 2) * cexp (-(Real.pi * (P + Q / 2)))) *
      θ (z + pv X idx x u)) * hε - θ (z + pv X idx x u) * hc

  have hsec : ∀ θ, IsTheta1 X bas idx (w : E) x L θ →
      (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) ∈ T.Sec 1 1 := by
    intro θ hθ
    show Differentiable ℂ (fun v : Fin 1 → I2.Vsp T.dim => θ (ψ.symm (v 0))) ∧ _
    refine ⟨?_, ?_⟩
    · have hd : Differentiable ℂ (fun y : I2.Vsp T.dim => ψ.symm y) := by
        simpa using (LinearMap.toContinuousLinearMap
          (ψ.symm : I2.Vsp T.dim →ₗ[ℂ] (Fin g → ℂ))).differentiable
      obtain ⟨hθd, -⟩ := hθ
      exact hθd.comp (hd.comp (differentiable_apply 0))
    · intro gam hgam v
      obtain ⟨u, hu, hgu⟩ := (hL (gam 0)).1 (hgam 0)
      have h := hthper θ hθ u hu (ψ.symm (v 0))
      simp only [Pi.add_apply, I2.HC, Fin.sum_univ_one, Fin.prod_univ_one, pow_one, Nat.cast_one,
        _root_.one_mul, map_add]
      rw [hgu, LinearEquiv.symm_apply_apply, h, LinearEquiv.apply_symm_apply]
  refine ⟨fun θ hθ => ⟨hsec θ hθ, fun hM => ?_⟩, ?_, hsign⟩
  · obtain ⟨A, Fd, hA, hFd, hmean⟩ := hM
    have hAL : ∀ z, z ∈ A ↔ ψ z ∈ T.L := by
      intro z
      rw [hA z, hL]
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v, hv, rfl⟩
      · rintro ⟨v, hv, h⟩
        exact ⟨v, hv, ψ.injective h⟩
    rw [l2_one_eq_integral_fundamentalDomain_div_volume T ψ θ (hsec θ hθ) A hAL Fd hFd]
    simpa only [hH] using hmean
  · intro n k th a z
    simp only [fock, I2.PT.U, Pi.sub_apply, sub_neg_eq_add, map_add, LinearEquiv.symm_apply_apply]
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 1
    congr 1
    simp only [I2.HC, Hf_neg_right, Hf_neg_left, neg_neg, hH, hHadd']
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

end GlobalTheory.Dict.ThetaPT
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.VacJet

theorem polyDeriv_rename {σ κ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {F : W → ℂ}
    (hF : ContDiff ℂ (⊤ : ℕ∞) F) (ρ : σ → κ) (u : κ → W) (P : MvPolynomial σ ℂ) (x : W) :
    I2.polyDeriv (MvPolynomial.rename ρ P) u F x = I2.polyDeriv P (fun l => u (ρ l)) F x := by
  induction P using MvPolynomial.induction_on generalizing x with
  | C a =>
    have h (τ : Type) : (MvPolynomial.C a : MvPolynomial τ ℂ) = a • MvPolynomial.monomial 0 1 := by
      simp [MvPolynomial.smul_eq_C_mul]
    rw [MvPolynomial.rename_C, h, h]
    simp [I2.polyDeriv_smul, I2.polyDeriv_monomial_one, I2.pdTerm_eq_itD,
      -MvPolynomial.smul_monomial, -MvPolynomial.monomial_zero']
  | add P Q hP hQ => simp only [map_add, I2.polyDeriv_add, hP, hQ]
  | mul_X P l hP =>
    rw [map_mul, MvPolynomial.rename_X, polyDeriv_mul_X hF, polyDeriv_mul_X hF, funext hP]

theorem sum_norm_coeff_rename {σ κ : Type} {ρ : σ → κ} (hρ : Function.Injective ρ) (P : MvPolynomial σ ℂ) :
    ∑ m ∈ (MvPolynomial.rename ρ P).support, ‖(MvPolynomial.rename ρ P).coeff m‖ =
      ∑ m ∈ P.support, ‖P.coeff m‖ := by
  rw [MvPolynomial.support_rename_of_injective hρ,
    Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hρ h)]
  exact Finset.sum_congr rfl fun m _ => by rw [MvPolynomial.coeff_rename_mapDomain ρ hρ]

theorem polyDeriv_smul_dir {σ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {P : MvPolynomial σ ℂ} {d : ℕ}
    (hP : P.IsHomogeneous d) (c : ℂ) (u : σ → W) (F : W → ℂ) (x : W) :
    I2.polyDeriv P (fun l => c • u l) F x = c ^ d * I2.polyDeriv P u F x := by
  refine polyDeriv_smul_letter P (fun _ => c) _ (fun m hm => ?_) u F x
  have := hP (MvPolynomial.mem_support_iff.1 hm)
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← this]
  congr 1
  simp [Finsupp.weight_apply, Finsupp.sum]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem thA_heisG_sum (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (y : Matrix (Fin n) (Fin r) E) {J : Type} (s : Finset J) (a : ℂ) (c : J → ℂ)
    (f : J → TF n g) (hf : ∀ i, IsSB (f i)) (z : Fin n → Fin g → ℂ) :
    thA X bas idx (heisG X bas y (a • ∑ i ∈ s, c i • f i)) x z =
      a * ∑ i ∈ s, c i * thA X bas idx (heisG X bas y (f i)) x z := by
  have h1 : heisG X bas y (a • ∑ i ∈ s, c i • f i) = a • ∑ i ∈ s, c i • heisG X bas y (f i) := by
    funext t
    simp [heisG, heisS, Finset.sum_mul, _root_.mul_assoc]
  have hsb (i) : IsSB (c i • heisG X bas y (f i)) :=
    TensVac.sb_smul _ ((heisG_laws E r X g bas idx n hs hn).2.2.2 y _ (hf i)).1
  rw [h1, UnAct.thA_smul, Pi.smul_apply, smul_eq_mul]
  congr 1
  induction s using Finset.induction_on with
  | empty => simpa using congrFun (UnAct.thA_smul (X := X) (bas := bas) idx x 0 (0 : TF n g)) z
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, UnAct.thA_add idx hs hx (hsb b) (RecSum.isSB_sum s _ hsb),
      Pi.add_apply, UnAct.thA_smul, Pi.smul_apply, smul_eq_mul, ih]
    funext t
    simp [heisG, heisS, Finset.sum_mul, _root_.mul_assoc]

section Torus

variable (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r) {dim : (E →+* ℂ) → ℕ}
  (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp dim)

noncomputable def rowPt : Matrix (Fin n) (Fin r) E →+ (Fin n → I2.Vsp dim) :=
  AddMonoidHom.mk' (fun y b => ψ (pv X idx x (y b))) fun y y' => by
    funext b
    rw [Pi.add_apply, ← map_add]
    congr 1
    exact congrArg (· ∘ idx) (per_add X x (y b) (y' b))

theorem rowPt_apply (y : Matrix (Fin n) (Fin r) E) (b : Fin n) :
    rowPt idx x ψ y b = ψ (pv X idx x (y b)) := rfl

variable {ψ}

theorem map_pv_smul (e : Fin g ≃ I2.Idx dim) (c : ℂ)
    (he : ∀ j, (e j).1 = rowType X (idx j) ∧ ψ (Pi.single j 1) = c • EuclideanSpace.single (e j) (1 : ℂ))
    (a : E) (u : Fin r → E) : ψ (pv X idx x (a • u)) = I2.actE a (ψ (pv X idx x u)) := by
  have h (z : Fin g → ℂ) (j) : ψ z (e j) = c * z j := by
    conv_lhs => rw [← Finset.univ_sum_single z]
    have h2 (i) : (Pi.single i (z i) : Fin g → ℂ) = z i • (Pi.single i 1 : Fin g → ℂ) := by
      rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one]
    simp only [h2, map_sum, map_smul, (he _).2]
    simp [Pi.single_apply, _root_.mul_comm]
  ext i
  obtain ⟨j, rfl⟩ := e.surjective i
  simp only [I2.actE, h, pv_smul, (he j).1]
  ring

end Torus

theorem mem_tensorLat_iff (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r) (T : I2.PT E)
    (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp T.dim) {L : Lt E r} (hL : ∀ ga, ga ∈ T.L ↔ ∃ u ∈ L, ga = ψ (pv X idx x u))
    (hψ : ∀ (a : E) u, ψ (pv X idx x (a • u)) = I2.actE a (ψ (pv X idx x u))) {Λ : Lt E n}
    (hΛ : Λ ∈ Vset E n 1) (ga : Fin n → I2.Vsp T.dim) :
    ga ∈ TensorLat.tensorLat T Λ ↔ ∃ y ∈ tens Λ L, ga = rowPt idx x ψ y := by
  have hp (v : Fin n → E) (u : Fin r → E) :
      rowPt idx x ψ (vecMulVec v u) = TensorLat.tens (ψ (pv X idx x u)) v := by
    funext b
    rw [rowPt_apply, TensorLat.tens_apply, ← hψ]
    rfl
  have hsp := (TensorLat.tensorLat_span_integral_perfect T Λ hΛ.1 (fun a ha => (hΛ.2.1 a).1 ha)
    (fun a ha => (hΛ.2.1 a).2 ha)).2.2.1
  rw [hsp]
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨p, hp', v, hv, rfl⟩ := ha
      obtain ⟨u, hu, rfl⟩ := (hL p).1 hp'
      exact ⟨_, AddSubgroup.subset_closure ⟨v, hv, u, hu, rfl⟩, (hp v u).symm⟩
    | zero => exact ⟨0, zero_mem _, (map_zero _).symm⟩
    | add a b _ _ ha hb =>
      obtain ⟨y, hy, rfl⟩ := ha
      obtain ⟨y', hy', rfl⟩ := hb
      exact ⟨y + y', add_mem hy hy', (map_add _ _ _).symm⟩
    | smul m a _ ha =>
      obtain ⟨y, hy, rfl⟩ := ha
      exact ⟨m • y, AddSubgroup.zsmul_mem _ hy m, (map_zsmul _ _ _).symm⟩
  · rintro ⟨y, hy, rfl⟩
    induction hy using AddSubgroup.closure_induction with
    | mem a ha =>
      obtain ⟨v, hv, u, hu, rfl⟩ := ha
      exact Submodule.subset_span ⟨_, (hL _).2 ⟨u, hu, rfl⟩, v, hv, hp v u⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | neg a _ ha => rw [map_neg]; exact neg_mem ha

theorem jet_projA_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : 𝓞 E, (w : E) + cc (w : E) = 1 → ∀ L : Lt E r, SelfD X L → ∀ Λ ∈ Vset E n 1, ∀ v : TF n g, IsVac X bas (w : E) (tens (stdL E n) L) v → ∀ x ∈ X.dom, X.IsOrtho x → ∀ t : ℝ, 0 < t → (∀ τ, X.c τ = t) → ∀ (θ : (Fin g → ℂ) → ℂ) (κ : ℂ), IsTheta1 X bas idx (w : E) x L θ → MeanOne X bas idx x L θ → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ lam : ℝ, 0 < lam → (∀ u ∈ L, u ≠ 0 → lam ^ 2 ≤ (hx X bas idx x (pv X idx x u) (pv X idx x u)).re) → ∀ (y : Matrix (Fin n) (Fin r) E) (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (d : ℕ), P.IsHomogeneous d → ‖κ * thP X hr bas idx (heisG X bas y (projA X bas (w : E) (tens Λ L) v)) P x‖ * Real.sqrt ((((stdL E n).toAddSubgroup.relIndex Λ.toAddSubgroup) : ℝ) ^ r) ≤ (∑ m ∈ P.support, ‖P.coeff m‖) * (Real.pi * Real.exp 1 * t * d) ^ ((d : ℝ) / 2) * Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * g * n) * (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^ (g * n) := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn w hw L hL Λ hΛ v hv x hx hox t ht hc θ κ hθ hm hκ lam hlam hmin
    y P d hP
  by_cases hκ0 : κ = 0
  · rw [hκ0, zero_mul, norm_zero, zero_mul]
    have : 0 ≤ rdE E := Real.rpow_nonneg (abs_nonneg _) _
    positivity
  obtain ⟨T, ψ, e, hT⟩ := exists_torus_of_selfD E r X g bas idx hs w hw L hL x hx hox t ht hc
  obtain ⟨hsec, hU, -⟩ := ThetaPT.theta_on_torus E r X g bas idx w L x t T ψ e hs hx hw hT
  obtain ⟨-, hH, hTL, hact, heps, he⟩ := hT
  obtain ⟨hs1, hl2⟩ := hsec θ hθ
  replace hl2 := hl2 hm
  obtain ⟨R, hR, hR', hcard, hpos, hproj⟩ :=
    VacMean.vac_proj_mean E r X g q0 hr bas idx n hs hn w hw L hL Λ hΛ v hv
  obtain ⟨-, -, him, -, -, hinj, -⟩ := hx_laws E r X g bas idx n hs hn x hx
  have hψ := map_pv_smul idx x e _ he
  have hlat := mem_tensorLat_iff idx x T ψ hTL hψ hΛ
  set Φ : Matrix (Fin n) (Fin r) E →+ (Fin n → I2.Vsp T.dim) := rowPt idx x ψ with hΦ
  have hΦinj : Function.Injective fun y => -Φ y := fun a b h => by
    funext k
    exact hinj (ψ.injective (congrFun (neg_injective h) k))
  have hΦL (a : Matrix (Fin n) (Fin r) E) (k) : Φ a k ∈ T.L ↔ a k ∈ L := by
    rw [hTL]
    exact ⟨fun ⟨u, hu, h⟩ => hinj (ψ.injective h) ▸ hu, fun h => ⟨_, h, rfl⟩⟩
  have hΦe (a : Matrix (Fin n) (Fin r) E) : TensorLat.tensorEps w (-Φ a) = epsW X (w : E) a := by
    rw [TensorLat.tensorEps_neg, TensorLat.tensorEps, epsW, I2.HC, Complex.im_sum]
    simp only [hΦ, rowPt_apply, ← hact, hH, him]
    push_cast
    rfl
  set s : (Fin 1 → I2.Vsp T.dim) → ℂ := fun v => θ (ψ.symm (v 0)) with hsdef
  have hs0 : s ≠ 0 := fun h => by
    rw [h] at hl2
    simp [I2.PT.l2, I2.PT.ptN2] at hl2
  let ρ : Harm.Var X.Ψ q0 X.p0 (Fin n) → I2.Letter n T.dim :=
    fun l => (l.2.2, e (idx.symm (rowOf X hr (l.1, l.2.1))))
  have hρ : Function.Injective ρ := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h
    obtain ⟨h3, h4⟩ := Prod.ext_iff.1 ((rowOf X hr).injective (idx.symm.injective (e.injective h2)))
    exact Prod.ext h3 (Prod.ext h4 h1)
  have hcR : (R.image fun y => -Φ y).card = R.card := Finset.card_image_of_injective _ hΦinj
  obtain ⟨-, -, key⟩ := normalised_theta_value_bound T w hw heps s hs1 hs0 Λ hΛ.1
    (fun a ha => (hΛ.2.1 a).1 ha) (fun a ha => (hΛ.2.1 a).2 ha) (R.image fun y => -Φ y)
    (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha
      exact neg_mem ((hlat _).2 ⟨b, hR b hb, rfl⟩))
    (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := (hlat _).1 ha
      have h1 (c) (k) : Φ b k - (-Φ c) k ∈ T.L ↔ (-b) k - c k ∈ L := by
        rw [← neg_mem_iff, show (-b) k - c k = (-b - c) k from rfl, ← hΦL, map_sub, map_neg]
        simp only [Pi.sub_apply, Pi.neg_apply]
        congr! 1
        abel
      obtain ⟨c, ⟨hc1, hc2⟩, hc3⟩ := hR' (-b) (neg_mem hb)
      refine ⟨-Φ c, ⟨Finset.mem_image_of_mem _ hc1, fun k => (h1 c k).2 (hc2 k)⟩, ?_⟩
      rintro _ ⟨h2, h3⟩
      obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 h2
      rw [hc3 c' ⟨hc', fun k => (h1 c' k).1 (h3 k)⟩])
    ((Real.sqrt R.card : ℝ) : ℂ)
    (by rw [hcR, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Nat.cast_nonneg _)])
    lam hlam
    (fun a ha h0 => by
      obtain ⟨u, hu, rfl⟩ := (hTL a).1 ha
      have h1 := hmin u hu (by
        rintro rfl
        exact h0 (by rw [show pv X idx x 0 = 0 from congrArg (· ∘ idx) (per_zero X x), map_zero]))
      rw [← hH, I2.jof_Hf_self_re] at h1
      exact le_of_sq_le_sq h1 (norm_nonneg _))
    ({()} : Finset Unit) (fun _ => 1) (by simp) (fun _ => -Φ y) (MvPolynomial.rename ρ P) d
    hP.rename_isHomogeneous
  rw [Finset.sum_singleton, hl2, Real.sqrt_one, one_pow, div_one, _root_.one_mul, sum_norm_coeff_rename hρ,
    Finset.card_singleton, Nat.cast_one, _root_.one_mul, ← Fintype.card_congr e, Fintype.card_fin,
    Finset.sum_image fun a _ b _ h => hΦinj h] at key
  simp only [hΦe] at key
  set G := T.U 1 (-Φ y) (∑ a ∈ R, epsW X (w : E) a • T.U 1 (-Φ a) (I2.tens T fun _ => s)) with hG
  let A : (Fin n → Fin g → ℂ) ≃L[ℂ] (Fin n → I2.Vsp T.dim) :=
    ContinuousLinearEquiv.piCongrRight fun _ => ψ.toContinuousLinearEquiv
  obtain ⟨-, -, -, hdiff, hlast⟩ := fock_laws E r X g bas idx n hs hn x hx 1 θ
  have hGA (z : Fin n → Fin g → ℂ) : G (A z) = ∑ a ∈ R, epsW X (w : E) a *
      ∏ b, fock X bas idx x 1 (pv X idx x (y b)) (fock X bas idx x 1 (pv X idx x (a b)) θ) (z b) := by
    have h1 (a : Matrix (Fin n) (Fin r) E) : T.U 1 (-Φ a) (I2.tens T fun _ => s) =
        fun v => ∏ b, fock X bas idx x 1 (pv X idx x (a b)) θ (ψ.symm (v b)) := by
      funext v
      rw [hU n 1 (fun _ => θ) (fun b => pv X idx x (a b)) (fun b => ψ.symm (v b))]
      simp only [LinearEquiv.apply_symm_apply]
      rfl
    have h2 (a : Matrix (Fin n) (Fin r) E) :=
      hU n 1 (fun b => fock X bas idx x 1 (pv X idx x (a b)) θ) (fun b => pv X idx x (y b)) z
    simp only [h2, ← h1]
    simp only [hG, I2.PT.U, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => mul_left_comm _ _ _
  have hGd : ContDiff ℂ (⊤ : ℕ∞) G := by
    have h1 : G = (fun z => G (A z)) ∘ A.symm := by
      funext v
      simp
    rw [h1, funext hGA]
    refine I2.contDiff_of_diff (Differentiable.comp ?_ A.symm.differentiable)
    refine Differentiable.fun_sum fun a _ => Differentiable.const_mul ?_ _
    refine (contDiff_prod fun b _ => (I2.contDiff_of_diff ((fock_laws E r X g bas idx n hs hn x hx 1 _).2.2.2.1
      (hdiff hθ.1 _) _)).comp (contDiff_apply ℂ (Fin g → ℂ) b)).differentiable (by simp)
  have hsb (a) : IsSB (heisG X bas a v) := ((heisG_laws E r X g bas idx n hs hn).2.2.2 a v hv.1).1
  have hth : thA X bas idx (heisG X bas y (projA X bas (w : E) (tens Λ L) v)) x =
      (κ⁻¹ * (R.card : ℂ)⁻¹) • fun z => G ((A : (Fin n → Fin g → ℂ) →L[ℂ] (Fin n → I2.Vsp T.dim)) z) := by
    funext z
    rw [hproj, thA_heisG_sum idx hs hn hx y R _ _ _ hsb, Pi.smul_apply, ContinuousLinearEquiv.coe_coe, hGA]
    have h2 (a : Matrix (Fin n) (Fin r) E) :=
      hlast (fun b => fock X bas idx x 1 (pv X idx x (a b)) θ) κ _ (hsb a) (hlast _ κ v hv.1 hκ a) y z
    simp only [h2, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    field_simp
  have hdir : (fun l => (A : (Fin n → Fin g → ℂ) →L[ℂ] (Fin n → I2.Vsp T.dim)) (letterDir X hr idx l)) =
      fun l => ((Real.sqrt t : ℝ) : ℂ) • I2.dir (ρ l) := by
    funext l b
    change ψ (letterDir X hr idx l b) = _
    by_cases h : b = l.2.2
    · subst h
      simp only [letterDir, I2.dir, ρ, Pi.smul_apply, Pi.single_eq_same, (he _).2]
    · simp [letterDir, I2.dir, ρ, h]
  rw [thP, hth, I2.polyDeriv_smul_fun _ _ (hGd.fun_comp (ContinuousLinearMap.contDiff _)),
    ColPoly.polyDeriv_comp_linear hGd, hdir, polyDeriv_smul_dir hP, ← polyDeriv_rename hGd, map_zero]
  have hc0 : (0 : ℝ) < R.card := by exact_mod_cast hpos
  have hsq : 0 < Real.sqrt R.card := Real.sqrt_pos.2 hc0
  have hpw : (Real.pi * Real.exp 1 * t * d) ^ ((d : ℝ) / 2) =
      Real.sqrt t ^ d * (Real.pi * Real.exp 1 * d) ^ ((d : ℝ) / 2) := by
    rw [mul_right_comm _ t, Real.mul_rpow (by positivity) ht.le, _root_.mul_comm, Real.sqrt_eq_rpow,
      ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 2
    ring
  rw [← Nat.cast_pow, ← hcard, hpw]
  have hk : ‖κ‖ ≠ 0 := norm_ne_zero_iff.2 hκ0
  refine le_of_eq_of_le ?_ ((mul_le_mul_of_nonneg_left key (pow_nonneg (Real.sqrt_nonneg t) d)).trans_eq (by ring))
  simp only [norm_mul, norm_inv, norm_pow, Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have h3 := Real.mul_self_sqrt hc0.le
  set q := Real.sqrt R.card
  rw [← h3]
  field_simp

end GlobalTheory.Dict.VacJet
end
