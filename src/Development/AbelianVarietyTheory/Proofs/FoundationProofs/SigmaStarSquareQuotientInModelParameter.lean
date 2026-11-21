import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsWeierstrassPSeries

section
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

open Filter Topology

noncomputable section

namespace GlobalTheory.WpSeries

abbrev tay (f : ℂ → ℂ) : PowerSeries ℂ := PowerSeries.mk (coef1 f)

variable {f g : ℂ → ℂ}

lemma tay_congr (h : f =ᶠ[𝓝 0] g) : tay f = tay g := by
  ext n
  simp only [PowerSeries.coeff_mk, coef1, h.iteratedDeriv_eq n]

lemma tay_congr' (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (h : f =ᶠ[𝓝[≠] 0] g) :
    tay f = tay g :=
  tay_congr ((hf.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hg.continuousAt).1 h)

lemma tay_add (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    tay (fun z => f z + g z) = tay f + tay g := by
  ext n
  simp only [map_add, PowerSeries.coeff_mk, coef1, ← add_div]
  congr 1
  exact iteratedDeriv_add hf.contDiffAt hg.contDiffAt

lemma tay_sub (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    tay (fun z => f z - g z) = tay f - tay g := by
  ext n
  simp only [map_sub, PowerSeries.coeff_mk, coef1, ← sub_div]
  congr 1
  exact iteratedDeriv_sub hf.contDiffAt hg.contDiffAt

lemma tay_mul (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    tay (fun z => f z * g z) = tay f * tay g := by
  ext n
  have h : iteratedDeriv n (fun z => f z * g z) 0 = _ :=
    iteratedDeriv_mul (n := n) hf.contDiffAt hg.contDiffAt
  simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, coef1, h]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have e : ((n.choose i : ℂ) * (i.factorial : ℂ) * ((n - i).factorial : ℂ)) = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi'
  have h1 : (i.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 i.factorial_ne_zero
  have h2 : ((n - i).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (n - i).factorial_ne_zero
  have h3 : (n.choose i : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos hi').ne'
  rw [← e]
  field_simp

lemma constantCoeff_tay (f : ℂ → ℂ) : PowerSeries.constantCoeff (tay f) = f 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  simp [coef1]

lemma tay_const (c : ℂ) : tay (fun _ => c) = PowerSeries.C c := by
  ext n
  rcases n with _ | n
  · simp [coef1]
  · simp [coef1, iteratedDeriv_const]

lemma tay_deriv (f : ℂ → ℂ) : tay (deriv f) = PowerSeries.derivativeFun (tay f) := by
  ext n
  refine Eq.trans ?_ (PowerSeries.coeff_derivativeFun (tay f) n).symm
  simp only [PowerSeries.coeff_mk, coef1, iteratedDeriv_succ', Nat.factorial_succ]
  have h1 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  have h2 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

lemma tay_id : tay (fun z => z) = PowerSeries.X := by
  ext n
  rcases n with _ | _ | n
  · simp [coef1]
  · simp [coef1]
  · simp [coef1, iteratedDeriv_succ', iteratedDeriv_const, PowerSeries.coeff_X]

lemma tay_pow (hf : AnalyticAt ℂ f 0) (n : ℕ) : tay (fun z => f z ^ n) = tay f ^ n := by
  induction n with
  | zero => simp [tay_const]
  | succ n ih =>
    simp only [pow_succ]
    rw [tay_mul (hf.fun_pow n) hf, ih]

def sqWp (L : PeriodPair) (z : ℂ) : ℂ := 1 + z ^ 2 * L.weierstrassPExcept 0 z

lemma analyticAt_sqWp (L : PeriodPair) : AnalyticAt ℂ (sqWp L) 0 := by
  have := L.analyticAt_weierstrassPExcept 0
  unfold sqWp
  fun_prop

lemma sqWp_eq (L : PeriodPair) {z : ℂ} (hz : z ≠ 0) : sqWp L z = z ^ 2 * L.weierstrassP z := by
  rw [← L.weierstrassPExcept_add 0, sqWp]
  simp
  field_simp
  ring

lemma eventually_notMem (L : PeriodPair) : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ L.lattice := by
  have h := L.compl_lattice_diff_singleton_mem_nhds 0
  filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with z h1 h2 h3
  exact h1 ⟨h3, h2⟩

lemma deriv_sqWp (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    deriv (sqWp L) z = 2 * z * L.weierstrassP z + z ^ 2 * L.derivWeierstrassP z := by
  have h0 : z ≠ 0 := by rintro rfl; exact hz (zero_mem _)
  have h1 : sqWp L =ᶠ[𝓝 z] fun w => w ^ 2 * L.weierstrassP w := by
    filter_upwards [isOpen_ne.mem_nhds h0] with w hw using sqWp_eq L hw
  have h2 : DifferentiableAt ℂ L.weierstrassP z :=
    L.differentiableOn_weierstrassP.differentiableAt (L.isClosed_lattice.isOpen_compl.mem_nhds hz)
  rw [h1.deriv_eq, deriv_fun_mul (by fun_prop) h2, L.deriv_weierstrassP]
  simp

lemma isWpSer_sqWp (L : PeriodPair) : IsWpSer L.g₂ L.g₃ (tay (sqWp L)) := by
  have hp := analyticAt_sqWp L
  have hd := hp.deriv
  have hi : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
  refine ⟨by rw [constantCoeff_tay]; simp [sqWp], ?_⟩
  have key := tay_congr' (f := fun z => (z * deriv (sqWp L) z - 2 * sqWp L z) ^ 2)
    (g := fun z => 4 * sqWp L z ^ 3 - L.g₂ * z ^ 4 * sqWp L z - L.g₃ * z ^ 6)
    (by fun_prop) (by fun_prop) (by
      filter_upwards [eventually_notMem L, self_mem_nhdsWithin] with z h1 h2
      rw [deriv_sqWp L h1, sqWp_eq L h2]
      linear_combination z ^ 6 * L.derivWeierstrassP_sq z h1)
  rw [tay_pow (by fun_prop), tay_sub (by fun_prop) (by fun_prop),
    tay_sub (by fun_prop) (by fun_prop), tay_sub (by fun_prop) (by fun_prop),
    tay_mul hi hd, tay_mul analyticAt_const hp, tay_mul analyticAt_const (hp.fun_pow 3),
    tay_mul (by fun_prop) hp, tay_mul analyticAt_const (hi.fun_pow 4),
    tay_mul analyticAt_const (hi.fun_pow 6), tay_pow hp, tay_pow hi, tay_pow hi, tay_id,
    tay_deriv, tay_const, tay_const, tay_const, tay_const, map_ofNat, map_ofNat] at key
  exact key

theorem exists_wpSer : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∃ P : PowerSeries ℂ, IsWpSer (g2 Λ) (g3 Λ) P ∧ ∀ v, v ∉ Λ → PowerSeries.X ^ 2 * PowerSeries.mk (coef1 (sqTh Λ v)) = PowerSeries.mk (coef1 (sgStar Λ)) ^ 2 * lineSer P (wpF Λ v) := by
  intro Λ h
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  refine ⟨tay (sqWp L), ?_, fun v hv => ?_⟩
  · rw [GlobalTheory.LatticeInvariants.g2_eq hL, GlobalTheory.LatticeInvariants.lattice_invariant_g3_eq hL]
    exact isWpSer_sqWp L
  have hp := analyticAt_sqWp L
  have hi : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
  have hs : AnalyticAt ℂ (sgStar Λ) 0 := h.differentiable.analyticAt 0
  have ht : AnalyticAt ℂ (sqTh Λ v) 0 := (h.differentiable_sqTh v).analyticAt 0
  have key := tay_congr' (f := fun z => z ^ 2 * sqTh Λ v z)
    (g := fun z => sgStar Λ z ^ 2 * (sqWp L z - wpF Λ v * z ^ 2))
    (by fun_prop) (by fun_prop) (by
      filter_upwards [eventually_notMem L, self_mem_nhdsWithin] with z h1 h2
      rw [h.sqTh_eq hv ((hL z).not.2 h1), sqWp_eq L h2, GlobalTheory.LatticeInvariants.wpF_eq hL z]
      ring)
  rw [tay_mul (hi.fun_pow 2) ht, tay_mul (hs.fun_pow 2) (by fun_prop), tay_sub hp (by fun_prop),
    tay_mul analyticAt_const (hi.fun_pow 2), tay_pow hi, tay_pow hs, tay_id, tay_const] at key
  exact key

end GlobalTheory.WpSeries
end
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weierstrassPSeries_and_sigmaStarQuotientSeries : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∃ P : PowerSeries ℂ, IsWpSer (g2 Λ) (g3 Λ) P ∧ ∀ v, v ∉ Λ → PowerSeries.X ^ 2 * PowerSeries.mk (coef1 (sqTh Λ v)) = PowerSeries.mk (coef1 (sgStar Λ)) ^ 2 * lineSer P (wpF Λ v) := by
  atlas_forward_decl GlobalTheory.WpSeries.exists_wpSer
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.WpForm

open PowerSeries

theorem exists_subst_inverse {R : Type*} [CommRing R] (l : PowerSeries R)
    (h0 : constantCoeff l = 0) (h1 : coeff 1 l = 1) :
    ∃ ex : PowerSeries R, constantCoeff ex = 0 ∧
      subst ex l = (X : PowerSeries R) ∧ subst l ex = (X : PowerSeries R) := by
  have hA : GlobalTheory.FormalInv.linearPart (fun _ : Unit => (l : MvPowerSeries Unit R)) = 1 := by
    ext i j
    exact h1
  obtain ⟨v, hv, h, h'⟩ := (GlobalTheory.FormalInv.exists_substInv_iff
    (u := fun _ : Unit => (l : MvPowerSeries Unit R)) (fun _ => h0)).2 (hA ▸ isUnit_one)
  exact ⟨v (), hv (), h (), h' ()⟩

theorem subst_eq_of_equation {K : Type} [Field K] [CharZero K] {a b : K}
    {P m q M : PowerSeries K} (hP : IsWpSer a b P) (hm : constantCoeff m = 1)
    (hq : constantCoeff q = 1)
    (hd : X * derivative K q - 2 * q = derivative K (X * m) * M)
    (hM : M ^ 2 = 4 * q ^ 3 - C a * X ^ 4 * q - C b * X ^ 6) :
    (subst (X * m : PowerSeries K) P : PowerSeries K) = m ^ 2 * q := by
  set l : PowerSeries K := X * m with hl
  have h0 : constantCoeff l = 0 := by simp [hl]
  have h1 : coeff 1 l = 1 := by
    rw [hl, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul]; simpa using hm
  obtain ⟨ex, he0, he1, he2⟩ := exists_subst_inverse l h0 h1
  have sl : HasSubst l := HasSubst.of_constantCoeff_zero' h0
  have se : HasSubst ex := HasSubst.of_constantCoeff_zero' he0
  have hle : ∀ f : PowerSeries K, (subst l (subst ex f : PowerSeries K) : PowerSeries K) = f := by
    intro f
    rw [subst_comp_subst_apply se sl, he2]
    exact congrFun MvPowerSeries.subst_self f
  have hel : ∀ f : PowerSeries K, (subst ex (subst l f : PowerSeries K) : PowerSeries K) = f := by
    intro f
    rw [subst_comp_subst_apply sl se, he1]
    exact congrFun MvPowerSeries.subst_self f
  set Q : PowerSeries K := subst ex (m ^ 2 * q) with hQ
  have hQl : (subst l Q : PowerSeries K) = m ^ 2 * q := hle _
  have hw : derivative K l = m + X * derivative K m := by
    rw [hl, Derivation.leibniz]; simp [add_comm]
  have hw0 : derivative K l ≠ 0 := by
    intro h
    have := congrArg constantCoeff (hw.symm.trans h)
    simp [hm] at this
  have hch := derivative_subst (f := Q) sl
  rw [hQl, Derivation.leibniz, Derivation.leibniz_pow] at hch
  simp only [smul_eq_mul, nsmul_eq_mul] at hch
  have key : l * (subst l (derivative K Q) : PowerSeries K) - 2 * (m ^ 2 * q) = m ^ 3 * M := by
    apply mul_right_cancel₀ hw0
    have hch' : m ^ 2 * derivative K q + q * (2 * (m * derivative K m)) =
        (subst l (derivative K Q) : PowerSeries K) * derivative K l := by simpa using hch
    linear_combination -l * hch' + m ^ 3 * hd - 2 * m ^ 2 * q * hw +
      (m ^ 2 * derivative K q + q * (2 * (m * derivative K m))) * hl
  have hQW : IsWpSer a b Q := by
    constructor
    · have h2 : ∀ f : PowerSeries K, constantCoeff (subst ex f : PowerSeries K) = constantCoeff f := by
        intro f
        have hf := eq_X_mul_shift_add_const f
        conv_lhs => rw [hf]
        rw [← coe_substAlgHom se, map_add, map_mul, substAlgHom_X, map_add, map_mul, he0,
          C_eq_algebraMap, AlgHom.commutes]
        simp
      rw [hQ, h2]; simp [hm, hq]
    · rw [← hel (_ ^ 2), ← hel (_ - C b * X ^ 6)]
      congr 1
      have hD : derivativeFun Q = derivative K Q := rfl
      rw [hD, ← coe_substAlgHom sl]
      simp only [map_pow, map_sub, map_mul, map_ofNat, substAlgHom_X, C_eq_algebraMap,
        AlgHom.commutes]
      rw [coe_substAlgHom sl, hQl]
      simp only [C_eq_algebraMap] at hM
      change (l * _ - _) ^ 2 = _ - algebraMap K (PowerSeries K) a * l ^ 4 * _ -
        algebraMap K (PowerSeries K) b * l ^ 6
      rw [key, hl]
      linear_combination m ^ 6 * hM
  rw [(GlobalTheory.WpSeries.existsUnique_isWpSer K a b).unique hP hQW, hQl]

theorem dX_eq_derivative {K : Type*} [CommRing K] (f : PowerSeries K) : dX f = derivative K f := by
  ext n
  simp [dX, coeff_derivative, mul_comm]

theorem derivative_flog {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p])
    (wq : PowerSeries ℂ_[p]) : derivative ℂ_[p] (flog W wq) = omegaW W wq := by
  ext n
  have : ((n : ℂ_[p]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp [flog, coeff_derivative, this]

theorem wp_flog : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq P : PowerSeries ℂ_[p]), IsWq W wq → IsWpSer (W.c₄ / 12) (W.c₆ / 216) P → PowerSeries.X ^ 2 * (PowerSeries.subst (flog W wq) P : PowerSeries ℂ_[p]) = flog W wq ^ 2 * lineSer wq⁻¹ (-(W.b₂ / 12)) := by
  intro p _ W wq P hwq hP
  have hw1 := GlobalTheory.GenusOneDatum.constantCoeff_of_isWq hwq
  obtain ⟨m, hm⟩ := X_dvd_iff.2 (GlobalTheory.GenusOneDatum.constantCoeff_flog W wq)
  have hm1 : constantCoeff m = 1 := by
    have := GlobalTheory.GenusOneDatum.coeff_one_flog hwq
    rw [hm, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul] at this
    simpa using this
  have he : wq * wq⁻¹ = 1 := PowerSeries.mul_inv_cancel wq (by rw [hw1]; exact one_ne_zero)
  have he1 : constantCoeff wq⁻¹ = 1 := by simp [PowerSeries.constantCoeff_inv, hw1]
  set e := wq⁻¹ with hedef
  set N : PowerSeries ℂ_[p] := C W.a₁ * X + C W.a₃ * X ^ 3 * wq - 2 with hN
  have h2 : constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := map_ofNat _ 2
  have hω : omegaW W wq * (wq * N) = -2 * wq - X * derivative ℂ_[p] wq := by
    have hu : (wq * N)⁻¹ * (wq * N) = 1 :=
      PowerSeries.inv_mul_cancel _ (by simp [hN, hw1, h2])
    have : omegaW W wq = (-2 * wq - X * derivative ℂ_[p] wq) * (wq * N)⁻¹ := by
      rw [← dX_eq_derivative]; rfl
    rw [this, mul_assoc, hu, mul_one]
  have hde : wq * derivative ℂ_[p] e + e * derivative ℂ_[p] wq = 0 := by
    have := congrArg (derivative ℂ_[p]) he
    rw [Derivation.leibniz] at this
    simpa using this
  set r := W.b₂ / 12 with hr
  have hq : lineSer e (-r) = e + C r * X ^ 2 := by simp [lineSer]
  have hdq : derivative ℂ_[p] (e + C r * X ^ 2) = derivative ℂ_[p] e + C r * (2 * X) := by
    rw [map_add, Derivation.leibniz, Derivation.leibniz_pow]; simp
  have hW : wq = 1 + C W.a₁ * X * wq + C W.a₂ * X ^ 2 * wq + C W.a₃ * X ^ 3 * wq ^ 2 +
    C W.a₄ * X ^ 4 * wq ^ 2 + C W.a₆ * X ^ 6 * wq ^ 3 := hwq
  have hW' : e ^ 2 = e ^ 3 + C W.a₁ * X * e ^ 2 + C W.a₂ * X ^ 2 * e ^ 2 + C W.a₃ * X ^ 3 * e +
      C W.a₄ * X ^ 4 * e + C W.a₆ * X ^ 6 := by
    linear_combination e ^ 3 * hW + (-e ^ 2 + C W.a₁ * X * e ^ 2 + C W.a₂ * X ^ 2 * e ^ 2 +
      (C W.a₃ * X ^ 3 + C W.a₄ * X ^ 4) * e * (wq * e + 1) +
      C W.a₆ * X ^ 6 * ((wq * e) ^ 2 + wq * e + 1)) * he
  have hNe : N * e = C W.a₁ * X * e + C W.a₃ * X ^ 3 - 2 * e := by
    rw [hN]; linear_combination C W.a₃ * X ^ 3 * he
  have c2 : (12 : PowerSeries ℂ_[p]) * C r = C W.a₁ ^ 2 + 4 * C W.a₂ := by
    have : 12 * r = W.a₁ ^ 2 + 4 * W.a₂ := by rw [hr, WeierstrassCurve.b₂]; ring
    simpa only [map_mul, map_add, map_pow, map_ofNat] using congrArg (C (R := ℂ_[p])) this
  have c4 : (C (W.c₄ / 12) : PowerSeries ℂ_[p]) =
      12 * C r ^ 2 - 2 * (2 * C W.a₄ + C W.a₁ * C W.a₃) := by
    have : W.c₄ / 12 = 12 * r ^ 2 - 2 * (2 * W.a₄ + W.a₁ * W.a₃) := by
      rw [hr, WeierstrassCurve.c₄, WeierstrassCurve.b₄]; ring
    rw [this]; simp only [map_mul, map_add, map_sub, map_pow, map_ofNat]
  have c6 : (C (W.c₆ / 216) : PowerSeries ℂ_[p]) =
      2 * C r * (2 * C W.a₄ + C W.a₁ * C W.a₃) - 8 * C r ^ 3 - (C W.a₃ ^ 2 + 4 * C W.a₆) := by
    have : W.c₆ / 216 = 2 * r * (2 * W.a₄ + W.a₁ * W.a₃) - 8 * r ^ 3 - (W.a₃ ^ 2 + 4 * W.a₆) := by
      rw [hr, WeierstrassCurve.c₆, WeierstrassCurve.b₄, WeierstrassCurve.b₆]; ring
    rw [this]; simp only [map_mul, map_add, map_sub, map_pow, map_ofNat]
  have main := subst_eq_of_equation (m := m) (q := e + C r * X ^ 2) (M := N * e) hP hm1
    (by simp [he1])
    (by
      rw [← hm, derivative_flog, hdq]
      linear_combination -e ^ 2 * hω + X * e * hde +
        (omegaW W wq * N * e + 2 * e - X * derivative ℂ_[p] e) * he)
    (by
      rw [hNe, c4, c6]
      linear_combination 4 * hW' - X ^ 2 * e ^ 2 * c2)
  rw [hq, hm, main]
  ring

end GlobalTheory.WpForm
end
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassP_formalGroupLog_uniformises : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq P : PowerSeries ℂ_[p]), IsWq W wq → IsWpSer (W.c₄ / 12) (W.c₆ / 216) P → PowerSeries.X ^ 2 * (PowerSeries.subst (flog W wq) P : PowerSeries ℂ_[p]) = flog W wq ^ 2 * lineSer wq⁻¹ (-(W.b₂ / 12)) := by
  first | exact @GlobalTheory.WpForm.wp_flog | exact GlobalTheory.WpForm.wp_flog | (intros; apply GlobalTheory.WpForm.wp_flog <;> assumption)
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_isWeierstrassPSeries : ∀ (K : Type) [Field K] [CharZero K] (a b : K), ∃! P : PowerSeries K, IsWpSer a b P := by
  first | exact @GlobalTheory.WpSeries.existsUnique_isWpSer | exact GlobalTheory.WpSeries.existsUnique_isWpSer | (intros; apply GlobalTheory.WpSeries.existsUnique_isWpSer <;> assumption)
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta.Param

open PowerSeries

theorem isWpSer_map {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) {a b : K} {P : PowerSeries K}
    (h : IsWpSer a b P) : IsWpSer (f a) (f b) (PowerSeries.map f P) := by
  have hd : derivativeFun (PowerSeries.map f P) = PowerSeries.map f (derivativeFun P) := by
    ext n
    simp [derivativeFun, coeff_derivative]
  refine ⟨?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h.1, map_one]
  · have := congrArg (PowerSeries.map f) h.2
    simp only [map_pow, map_sub, map_mul, map_C, map_X, map_ofNat] at this
    rw [hd]
    exact this

theorem isWpSer_rescale {K : Type*} [CommRing K] (e : K) {a b : K} {P : PowerSeries K}
    (h : IsWpSer a b P) : IsWpSer (e ^ 4 * a) (e ^ 6 * b) (rescale e P) := by
  have hd : X * derivativeFun (rescale e P) = rescale e (X * derivativeFun P) := by
    ext n
    cases n with
    | zero => simp [coeff_rescale]
    | succ n => simp [coeff_rescale, coeff_succ_X_mul, derivativeFun, coeff_derivative, mul_assoc, pow_succ']
  have hC : ∀ c : K, rescale e (C c) = C c := by
    intro c
    ext n
    cases n <;> simp [coeff_rescale, coeff_C]
  refine ⟨?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_zero_eq_constantCoeff_apply, h.1]
    simp
  · have := congrArg (rescale e) h.2
    rw [hd]
    rw [map_pow, map_sub] at this
    simp only [map_pow (rescale e), map_sub (rescale e), map_mul (rescale e) _ P, map_mul (rescale e) (C _),
      map_mul (rescale e) 4, hC, rescale_X, map_ofNat] at this
    rw [this]
    simp only [map_mul, map_pow]
    ring

variable {p : ℕ} [Fact p.Prime]

theorem lamC_coe' (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := by
  simp [lamC]

theorem theta_series_map_coefficients (lam : Qbar →+* ℂ_[p]) (F : ℂ → ℂ) (T : PowerSeries Qbar)
    (h : PowerSeries.mk (coef1 F) = PowerSeries.map (algebraMap Qbar ℂ) T) :
    GL3Theta.ser1 lam F = PowerSeries.map lam T := by
  ext n
  have := congrArg (coeff n) h
  rw [coeff_mk, coeff_map] at this
  rw [GL3Theta.ser1, coeff_mk, coeff_map, ← lamC_coe']
  exact congrArg (lamC lam) this

theorem invariants (g : GL3Theta.G1 p) (a b : Qbar) (ha : g2 g.abelian₂ = a) (hb : g3 g.abelian₂ = b) :
    g.W.c₄ / 12 = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 4 * g.lam a ∧
    g.W.c₆ / 216 = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 6 * g.lam b ∧
    g.W.b₂ / 12 = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * g.C.r := by
  have e : ∀ x : Qbar, lamC g.lam (-(x : ℂ) / 4) = -g.lam x / 4 := by
    intro x
    have : -(x : ℂ) / 4 = ((-x / 4 : Qbar) : ℂ) := by
      push_cast; rfl
    rw [this, lamC_coe', map_div₀, map_neg, map_ofNat]
  unfold GL3Theta.G1.W
  rw [WeierstrassCurve.variableChange_c₄, WeierstrassCurve.variableChange_c₆,
    WeierstrassCurve.variableChange_b₂]
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, wModel, ha, hb, e]
  refine ⟨by ring, by ring, by ring⟩

theorem exists_algebraic_series (Λ : AddSubgroup ℂ) (hL : IsLat Λ) (a b w : Qbar) (ha : g2 Λ = a) (hb : g3 Λ = b)
    (hσ : AlgEnt (sgStar Λ)) (v : ℂ) (hv : v ∉ Λ) (hw : wpF Λ v = w) :
    ∃ P₀ S : PowerSeries Qbar, IsWpSer a b P₀ ∧
      PowerSeries.mk (coef1 (sgStar Λ)) = PowerSeries.map (algebraMap Qbar ℂ) (X * S) ∧
      PowerSeries.mk (coef1 (sqTh Λ v)) = PowerSeries.map (algebraMap Qbar ℂ) (S ^ 2 * lineSer P₀ w) := by
  obtain ⟨P, hP, hPv⟩ := GlobalTheory.T.exists_weierstrassPSeries_and_sigmaStarQuotientSeries Λ hL
  obtain ⟨P₀, hP₀, -⟩ := GlobalTheory.T.existsUnique_isWeierstrassPSeries Qbar a b
  rw [ha, hb] at hP
  have hPP : P = PowerSeries.map (algebraMap Qbar ℂ) P₀ :=
    (GlobalTheory.T.existsUnique_isWeierstrassPSeries ℂ a b).unique hP (isWpSer_map (algebraMap Qbar ℂ) hP₀)
  have h0 : coef1 (sgStar Λ) 0 = 0 := by
    simp [coef1, (hL.sg_eq_zero 0).2 (zero_mem _)]
  obtain ⟨S, hS⟩ : ∃ S : PowerSeries Qbar,
      PowerSeries.mk (coef1 (sgStar Λ)) = PowerSeries.map (algebraMap Qbar ℂ) (X * S) := by
    refine ⟨PowerSeries.mk fun n => ⟨coef1 (sgStar Λ) (n + 1), hσ.2 _⟩, ?_⟩
    ext n
    cases n with
    | zero => simp [h0]
    | succ n => rw [coeff_map, coeff_succ_X_mul, coeff_mk, coeff_mk]; rfl
  refine ⟨P₀, S, hP₀, hS, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 (X_ne_zero (R := ℂ)))
  rw [hPv v hv, hS, hPP, hw]
  simp only [lineSer, map_mul, map_pow, map_sub, map_X, map_C]
  have : algebraMap Qbar ℂ w = (w : ℂ) := rfl
  rw [this]
  ring

theorem subst_lineSer {K : Type*} [Field K] (l E q S P : PowerSeries K) (ε r w : K) (hl0 : constantCoeff l = 0)
    (hE : X * E = l * subst (C ε * l) S)
    (hform : X ^ 2 * (subst l (rescale ε P) : PowerSeries K) = l ^ 2 * lineSer q (-(ε ^ 2 * r))) :
    (subst (C ε * l) (S ^ 2 * lineSer P w) : PowerSeries K) = E ^ 2 * lineSer q (ε ^ 2 * (w - r)) := by
  have hl : HasSubst l := HasSubst.of_constantCoeff_zero' hl0
  have hel : HasSubst (C ε * l) := HasSubst.of_constantCoeff_zero' (by simp [hl0])
  have hres : subst l (rescale ε P) = (subst (C ε * l) P : PowerSeries K) := by
    rw [rescale_eq_subst, subst_comp_subst_apply (HasSubst.smul_X' ε) hl, subst_smul hl, subst_X hl, smul_eq_C_mul]
  rw [hres] at hform
  have hCs : subst (C ε * l) (C w : PowerSeries K) = (C w : PowerSeries K) := by
    rw [← coe_substAlgHom hel]
    exact (substAlgHom hel).commutes w
  apply mul_left_cancel₀ (pow_ne_zero 2 (X_ne_zero (R := K)))
  rw [← mul_assoc, ← mul_pow, hE]
  simp only [lineSer, map_mul, map_pow, map_sub, map_neg] at hform ⊢
  rw [subst_mul hel, subst_pow hel, subst_sub hel, subst_mul hel, subst_pow hel, subst_X hel, hCs]
  linear_combination (subst (C ε * l) S : PowerSeries K) ^ 2 * hform

theorem constantCoeff_l (g : GL3Theta.G1 p) : constantCoeff g.l = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, GL3Theta.G1.l, flog, coeff_mk]; simp

theorem X_mul_ePhi1 (g : GL3Theta.G1 p) (S : PowerSeries ℂ_[p]) (hS : GL3Theta.ser1 g.lam (sgStar g.abelian₂) = X * S) :
    X * ePhi1 g.lam g.abelian₂ g.C g.wq = g.l * subst (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.l) S := by
  have hl0 := constantCoeff_l g
  have hel : HasSubst (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.l) :=
    HasSubst.of_constantCoeff_zero' (by rw [map_mul, hl0, mul_zero])
  have hS' : sgSer g.lam g.abelian₂ = X * S := hS
  ext n
  cases n with
  | zero => rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, map_mul, map_mul, hl0,
      constantCoeff_X, zero_mul, zero_mul]
  | succ n =>
    rw [coeff_succ_X_mul, ePhi1, coeff_mk, hS', ← C_eq_algebraMap, ← GL3Theta.G1.W, ← GL3Theta.G1.l,
      subst_mul hel, subst_X hel, mul_assoc, coeff_C_mul, inv_mul_cancel_left₀ (Units.ne_zero _)]

theorem sqTh_atU : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsWq g.W g.wq → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → AlgEnt (sqTh g.abelian₂ v) ∧ g.atU (sqTh g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2 * lineSer g.wq⁻¹ (xAt g v) := by
  intro p _ g hq hL h2 h3 hσ v hv hw
  obtain ⟨a, ha⟩ : ∃ a : Qbar, g2 g.abelian₂ = a := ⟨⟨_, h2⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Qbar, g3 g.abelian₂ = b := ⟨⟨_, h3⟩, rfl⟩
  obtain ⟨w, hw'⟩ : ∃ w : Qbar, wpF g.abelian₂ v = w := ⟨⟨_, hw⟩, rfl⟩
  obtain ⟨P₀, S, hP₀, hS, hT⟩ := exists_algebraic_series g.abelian₂ hL a b w ha hb hσ v hv hw'
  refine ⟨⟨hL.differentiable_sqTh v, fun n => ?_⟩, ?_⟩
  · have := congrArg (coeff n) hT
    rw [coeff_mk, coeff_map] at this
    rw [this]
    exact SetLike.coe_mem _
  obtain ⟨i4, i6, i2⟩ := invariants g a b ha hb
  have hform := GlobalTheory.T.weierstrassP_formalGroupLog_uniformises p g.W g.wq
    (rescale ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) (PowerSeries.map g.lam P₀)) hq
    (by rw [i4, i6]; exact isWpSer_rescale _ (isWpSer_map g.lam hP₀))
  rw [i2, ← GL3Theta.G1.l] at hform
  have hE := X_mul_ePhi1 g (PowerSeries.map g.lam S) (by rw [theta_series_map_coefficients g.lam _ _ hS, map_mul, map_X])
  have hm : PowerSeries.map g.lam (S ^ 2 * lineSer P₀ w) =
      PowerSeries.map g.lam S ^ 2 * lineSer (PowerSeries.map g.lam P₀) (g.lam w) := by
    simp only [lineSer, map_mul, map_pow, map_sub, map_X, map_C]
  rw [GL3Theta.G1.atU, ← C_eq_algebraMap, theta_series_map_coefficients g.lam _ _ hT, hm, xAt, hw', lamC_coe']
  exact subst_lineSer _ _ _ _ _ _ _ _ (constantCoeff_l g) hE hform

end GlobalTheory.EvenTheta.Param
end
