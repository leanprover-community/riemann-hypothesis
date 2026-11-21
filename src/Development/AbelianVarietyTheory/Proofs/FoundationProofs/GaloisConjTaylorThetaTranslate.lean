import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsMulEqPolynomialWeierstrassP
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero

section
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Topology
open Filter

noncomputable section

namespace GlobalTheory.SigmaConj

section Formal

open PowerSeries

variable {R S : Type} [CommRing R] [CommRing S]

def wSer (s : R) (A : R⟦X⟧) : R⟦X⟧ :=
  d⁄dX R A ^ 2 - A * d⁄dX R (d⁄dX R A) - C s * A ^ 2

def OdeSer (s a b : R) (A : R⟦X⟧) : Prop :=
  (d⁄dX R (wSer s A) * A - 2 * wSer s A * d⁄dX R A) ^ 2 =
    4 * wSer s A ^ 3 - C a * wSer s A * A ^ 4 - C b * A ^ 6

def homSer (m : ℕ) (q : ℕ → R) (s : R) (A : R⟦X⟧) : R⟦X⟧ :=
  ∑ k ∈ Finset.range (m + 1), C (q k) * (wSer s A ^ k * A ^ (2 * (m - k)))

def EndSer (α : R) (N m : ℕ) (q : ℕ → R) (s : R) (A : R⟦X⟧) : Prop :=
  rescale α A ^ 2 * A ^ (2 * m) = A ^ (2 * N) * homSer m q s A

lemma map_deriv (φ : R →+* S) (A : R⟦X⟧) : map φ (d⁄dX R A) = d⁄dX S (map φ A) := by
  ext n; simp [coeff_derivative]

lemma map_rescale (φ : R →+* S) (α : R) (A : R⟦X⟧) :
    map φ (rescale α A) = rescale (φ α) (map φ A) := by
  ext n; simp [coeff_rescale]

lemma map_wSer (φ : R →+* S) (s : R) (A : R⟦X⟧) : map φ (wSer s A) = wSer (φ s) (map φ A) := by
  simp [wSer, map_deriv]

lemma OdeSer.map (φ : R →+* S) {s a b : R} {A : R⟦X⟧} (h : OdeSer s a b A) :
    OdeSer (φ s) (φ a) (φ b) (map φ A) := by
  have := congrArg (PowerSeries.map φ) h
  simpa [OdeSer, map_deriv, map_wSer, map_ofNat] using this

lemma OdeSer.of_map (φ : R →+* S) (hφ : Function.Injective φ) {s a b : R} {A : R⟦X⟧}
    (h : OdeSer (φ s) (φ a) (φ b) (PowerSeries.map φ A)) : OdeSer s a b A := by
  apply PowerSeries.map_injective φ hφ
  simpa [OdeSer, map_deriv, map_wSer, map_ofNat] using h

lemma EndSer.map (φ : R →+* S) {α s : R} {N m : ℕ} {q : ℕ → R} {A : R⟦X⟧}
    (h : EndSer α N m q s A) : EndSer (φ α) N m (fun k => φ (q k)) (φ s) (map φ A) := by
  have := congrArg (PowerSeries.map φ) h
  simpa [EndSer, homSer, map_rescale, map_wSer] using this

lemma EndSer.descend {M : Type} [Field M] [Algebra M ℂ] {α s : M} {N m : ℕ} {q : ℕ → ℂ}
    {A : M⟦X⟧} (h : EndSer (algebraMap M ℂ α) N m q (algebraMap M ℂ s)
      (PowerSeries.map (algebraMap M ℂ) A)) : ∃ q' : ℕ → M, EndSer α N m q' s A := by
  obtain ⟨r, hr⟩ := (Algebra.linearMap M ℂ).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (algebraMap M ℂ).injective)
  have hr' : ∀ x : M, r (algebraMap M ℂ x) = x := fun x => LinearMap.congr_fun hr x
  refine ⟨fun k => r (q k), ?_⟩
  ext n
  have h1 := congrArg (fun B => r (coeff n B)) h
  have c1 : ∀ (x y : ℂ⟦X⟧) (c : ℂ), x * (C c * y) = C c * (x * y) := fun x y c => by ring
  have c2 : ∀ (x y : M⟦X⟧) (c : M), x * (C c * y) = C c * (x * y) := fun x y c => by ring
  simp only [homSer, Finset.mul_sum, c1, ← map_rescale, ← map_wSer,
    ← map_pow (PowerSeries.map (algebraMap M ℂ)), ← map_mul (PowerSeries.map (algebraMap M ℂ)),
    map_sum, coeff_C_mul, coeff_map, hr'] at h1
  simp only [homSer, Finset.mul_sum, c2, map_sum, coeff_C_mul]
  rw [h1]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm (q k), ← Algebra.smul_def, r.map_smul, smul_eq_mul, mul_comm (r (q k))]

lemma ode_unique {a b : ℂ} {P Q : ℂ⟦X⟧} (hP0 : constantCoeff P = 1) (hQ0 : constantCoeff Q = 1)
    (hP : (X * d⁄dX ℂ P - 2 * P) ^ 2 = 4 * P ^ 3 - C a * X ^ 4 * P - C b * X ^ 6)
    (hQ : (X * d⁄dX ℂ Q - 2 * Q) ^ 2 = 4 * Q ^ 3 - C a * X ^ 4 * Q - C b * X ^ 6) : P = Q := by
  by_contra hne
  have hD : P - Q ≠ 0 := sub_ne_zero.2 hne
  obtain ⟨n, E, hE, hE0⟩ : ∃ (n : ℕ) (E : ℂ⟦X⟧), P = Q + X ^ n * E ∧ constantCoeff E ≠ 0 :=
    ⟨(P - Q).order.toNat, divXPowOrder (P - Q), by rw [X_pow_order_mul_divXPowOrder]; ring,
      by simpa [constantCoeff_divXPowOrder_eq_zero_iff] using hD⟩
  have hx : (X : ℂ⟦X⟧) * d⁄dX ℂ (X ^ n : ℂ⟦X⟧) = (n : ℂ⟦X⟧) * X ^ n := by
    cases n with
    | zero => simp
    | succ n => simp [Derivation.leibniz_pow]; ring
  have hd : X * d⁄dX ℂ P = X * d⁄dX ℂ Q + X ^ n * ((n : ℂ⟦X⟧) * E + X * d⁄dX ℂ E) := by
    rw [hE, map_add, Derivation.leibniz]
    simp only [smul_eq_mul]
    linear_combination E * hx
  have key : X ^ n * ((((n : ℂ⟦X⟧) * E + X * d⁄dX ℂ E) - 2 * E) *
      (X * d⁄dX ℂ P - 2 * P + (X * d⁄dX ℂ Q - 2 * Q))) =
      X ^ n * (E * (4 * (P ^ 2 + P * Q + Q ^ 2) - C a * X ^ 4)) := by
    have e : X ^ n * E = P - Q := by rw [hE]; ring
    linear_combination hP - hQ - (X * d⁄dX ℂ P - 2 * P + (X * d⁄dX ℂ Q - 2 * Q)) * hd
      - (2 * (X * d⁄dX ℂ P - 2 * P + (X * d⁄dX ℂ Q - 2 * Q))
        + (4 * (P ^ 2 + P * Q + Q ^ 2) - C a * X ^ 4)) * e
  have k2 := congrArg constantCoeff (mul_left_cancel₀ (pow_ne_zero n (X_ne_zero (R := ℂ))) key)
  simp [hP0, hQ0, map_ofNat] at k2
  have : ((n : ℂ) + 1) * constantCoeff E = 0 := by linear_combination (-1 / 4 : ℂ) * k2
  exact (mul_ne_zero (Nat.cast_add_one_ne_zero n) hE0) this

lemma ode_reduce {s a b : ℂ} {U V : ℂ⟦X⟧} (hUV : U * V = 1) (h : OdeSer s a b (X * U)) :
    (X * d⁄dX ℂ (wSer s (X * U) * V ^ 2) - 2 * (wSer s (X * U) * V ^ 2)) ^ 2 =
      4 * (wSer s (X * U) * V ^ 2) ^ 3 - C a * X ^ 4 * (wSer s (X * U) * V ^ 2) - C b * X ^ 6 := by
  unfold OdeSer at h
  set P := wSer s (X * U) * V ^ 2 with hP
  have hW : wSer s (X * U) = P * U ^ 2 := by
    rw [hP, mul_assoc, ← mul_pow, mul_comm V, hUV]; simp
  have hU : U ≠ 0 := left_ne_zero_of_mul_eq_one hUV
  rw [hW] at h
  simp only [Derivation.leibniz, Derivation.leibniz_pow, derivative_X, smul_eq_mul,
    nsmul_eq_mul] at h
  apply mul_left_cancel₀ (pow_ne_zero 6 hU)
  push_cast at h
  linear_combination h

lemma theta_unique {s a b : ℂ} {A B : ℂ⟦X⟧} (hA0 : coeff 0 A = 0) (hA1 : coeff 1 A = 1)
    (hA2 : coeff 2 A = 0) (hB0 : coeff 0 B = 0) (hB1 : coeff 1 B = 1) (hB2 : coeff 2 B = 0)
    (hA : OdeSer s a b A) (hB : OdeSer s a b B) : A = B := by
  obtain ⟨U, rfl⟩ : X ∣ A := X_dvd_iff.2 (by simpa using hA0)
  obtain ⟨T, rfl⟩ : X ∣ B := X_dvd_iff.2 (by simpa using hB0)
  rw [coeff_succ_X_mul] at hA1 hA2 hB1 hB2
  simp only [coeff_zero_eq_constantCoeff] at hA1 hB1
  have hUV : U * U⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by simp [hA1])
  have hTV : T * T⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by simp [hB1])
  have hV0 : constantCoeff U⁻¹ = 1 := by simp [hA1]
  have hV1 : constantCoeff T⁻¹ = 1 := by simp [hB1]
  generalize U⁻¹ = V at hUV hV0
  generalize T⁻¹ = Y at hTV hV1
  have hPQ := ode_unique (by simp [wSer, Derivation.leibniz, hA1, hV0])
    (by simp [wSer, Derivation.leibniz, hB1, hV1]) (ode_reduce hUV hA) (ode_reduce hTV hB)
  have dV : d⁄dX ℂ V = -V ^ 2 * d⁄dX ℂ U := by
    have := congrArg (d⁄dX ℂ) hUV
    simp only [Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero] at this
    linear_combination V * this - d⁄dX ℂ V * hUV
  have dY : d⁄dX ℂ Y = -Y ^ 2 * d⁄dX ℂ T := by
    have := congrArg (d⁄dX ℂ) hTV
    simp only [Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero] at this
    linear_combination Y * this - d⁄dX ℂ Y * hTV
  have h1 : d⁄dX ℂ U * V = d⁄dX ℂ T * Y := by
    refine derivative.ext ?_ ?_
    · apply mul_left_cancel₀ (pow_ne_zero 2 (X_ne_zero (R := ℂ)))
      simp only [wSer, Derivation.leibniz, smul_eq_mul, derivative_X, map_add, mul_one] at hPQ ⊢
      rw [dV, dY]
      linear_combination -hPQ + ((U * V + 1) * (1 - C s * X ^ 2) - X ^ 2 * V * d⁄dX ℂ (d⁄dX ℂ U)) * hUV
        - ((T * Y + 1) * (1 - C s * X ^ 2) - X ^ 2 * Y * d⁄dX ℂ (d⁄dX ℂ T)) * hTV
    · have e : ∀ F : ℂ⟦X⟧, constantCoeff (d⁄dX ℂ F) = coeff 1 F := fun F => by
        rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative]; simp
      rw [map_mul, map_mul, e, e, hA2, hB2, zero_mul, zero_mul]
  have h2 : U * Y = 1 := by
    refine derivative.ext ?_ (by simp [hA1, hV1])
    simp only [Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero]
    rw [dY]
    linear_combination U * Y * h1 - Y * d⁄dX ℂ U * hUV
  have : U = T := by linear_combination T * h2 - U * hTV
  rw [this]

lemma coeff_two_mul' (f g : R⟦X⟧) : coeff 2 (f * g) =
    coeff 0 f * coeff 2 g + coeff 1 f * coeff 1 g + coeff 2 f * coeff 0 g := by
  simp [coeff_mul, Finset.Nat.antidiagonal_succ]; ring

lemma coeff_one_mul' (f g : R⟦X⟧) : coeff 1 (f * g) =
    coeff 0 f * coeff 1 g + coeff 1 f * coeff 0 g := by
  simp [coeff_mul, Finset.Nat.antidiagonal_succ]

lemma coeff_zero_mul' (f g : R⟦X⟧) : coeff 0 (f * g) = coeff 0 f * coeff 0 g := by
  simp

lemma OdeSer.const_eq {s a b : ℂ} {A : ℂ⟦X⟧} (hA0 : coeff 0 A = 0) (hA1 : coeff 1 A = 1)
    (hA2 : coeff 2 A = 0) (hA : OdeSer s a b A) : s = -2 * coeff 3 A := by
  have w0 : coeff 0 (wSer s A) = 1 := by
    simp only [wSer, sq, map_sub, coeff_zero_mul', coeff_derivative, coeff_C_mul]
    simp [hA0, hA1]
  have w1 : coeff 1 (wSer s A) = 0 := by
    simp only [wSer, sq, map_sub, coeff_one_mul', coeff_derivative, coeff_C_mul]
    simp [hA0, hA1, hA2]
  have w2 : coeff 2 (wSer s A) = -s := by
    simp only [wSer, sq, map_sub, coeff_two_mul', coeff_derivative, coeff_C_mul]
    simp [hA0, hA1, hA2]; ring
  have h := congrArg (coeff 2) hA
  generalize wSer s A = W at h w0 w1 w2
  have e2 : (2 : ℂ⟦X⟧) = C 2 := rfl
  have e4 : (4 : ℂ⟦X⟧) = C 4 := rfl
  simp only [pow_succ, pow_zero, one_mul, e2, e4, mul_assoc, map_sub, coeff_C_mul, coeff_two_mul',
    coeff_one_mul', coeff_zero_mul', coeff_derivative, Nat.reduceAdd, hA0, hA1, hA2, w0, w1, w2] at h
  push_cast at h
  linear_combination (1 / 12 : ℂ) * h

end Formal

section Taylor

open PowerSeries

def Ent : Subring (ℂ → ℂ) where
  carrier := {f | Differentiable ℂ f}
  mul_mem' := fun hf hg => hf.mul hg
  one_mem' := differentiable_const 1
  add_mem' := fun hf hg => hf.add hg
  zero_mem' := differentiable_const 0
  neg_mem' := fun hf => hf.neg

lemma Ent.diff (f : Ent) : Differentiable ℂ f.1 := f.2

lemma Ent.contDiff (f : Ent) (n : ℕ) : ContDiff ℂ n f.1 := (Ent.diff f).contDiff

def dE (f : Ent) : Ent :=
  ⟨deriv f.1, differentiableOn_univ.1 ((Ent.diff f).differentiableOn.deriv isOpen_univ)⟩

def cE (c : ℂ) : Ent := ⟨fun _ => c, differentiable_const c⟩

def sE (α : ℂ) (f : Ent) : Ent :=
  ⟨fun z => f.1 (α * z), (Ent.diff f).comp (differentiable_id.const_mul α)⟩

def tay : Ent →+* ℂ⟦X⟧ where
  toFun f := PowerSeries.mk (coef1 f.1)
  map_zero' := by ext n; simp [coef1]
  map_one' := by
    ext n
    cases n with
    | zero => simp [coef1]
    | succ n =>
      have : ((1 : Ent) : ℂ → ℂ) = fun _ => 1 := rfl
      rw [coeff_mk, coef1, this, iteratedDeriv_const]
      simp [coeff_one]
  map_add' f g := by
    ext n
    simp only [coeff_mk, map_add, coef1, Subring.coe_add]
    rw [iteratedDeriv_add (Ent.contDiff f n).contDiffAt (Ent.contDiff g n).contDiffAt, add_div]
  map_mul' f g := by
    ext n
    simp only [coeff_mk, coeff_mul, coef1, Subring.coe_mul]
    rw [iteratedDeriv_mul (Ent.contDiff f n).contDiffAt (Ent.contDiff g n).contDiffAt,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_div]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have h1 : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have h2 : ((n - k).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - k).factorial_ne_zero
    have h3 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    rw [Nat.cast_choose ℂ hk']
    field_simp

lemma coeff_tay (f : Ent) (n : ℕ) : coeff n (tay f) = coef1 f.1 n := coeff_mk n (coef1 f.1)

lemma tay_dE (f : Ent) : tay (dE f) = d⁄dX ℂ (tay f) := by
  ext n
  have h3 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h4 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  simp only [coeff_derivative, coeff_tay, coef1, dE, iteratedDeriv_succ', Nat.factorial_succ]
  push_cast
  field_simp

lemma tay_cE (c : ℂ) : tay (cE c) = C c := by
  ext n
  cases n with
  | zero => simp [coeff_tay, coef1, cE]
  | succ n => simp [coeff_tay, coef1, cE, iteratedDeriv_const, coeff_C]

lemma tay_sE (α : ℂ) (f : Ent) : tay (sE α f) = rescale α (tay f) := by
  ext n
  simp only [coeff_rescale, coeff_tay, coef1, sE]
  rw [iteratedDeriv_comp_const_mul (Ent.contDiff f n)]
  simp [mul_div_assoc]

lemma tay_injective : Function.Injective tay := by
  intro f g h
  ext z
  rw [← Complex.taylorSeries_eq_of_entire' 0 z (Ent.diff f),
    ← Complex.taylorSeries_eq_of_entire' 0 z (Ent.diff g)]
  refine tsum_congr fun n => ?_
  have := congrArg (coeff n) h
  simp only [coeff_tay, coef1, div_eq_inv_mul] at this
  rw [this]

def wE (s : ℂ) (f : Ent) : Ent := dE f ^ 2 - f * dE (dE f) - cE s * f ^ 2

lemma tay_wE (s : ℂ) (f : Ent) : tay (wE s f) = wSer s (tay f) := by
  simp [wE, wSer, tay_dE, tay_cE]

lemma wE_apply (s : ℂ) (f : Ent) (z : ℂ) :
    (wE s f).1 z = deriv f.1 z ^ 2 - f.1 z * deriv (deriv f.1) z - s * f.1 z ^ 2 := by
  simp [wE, dE, cE]

lemma eq_of_eq_off (L : PeriodPair) {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ z ∉ L.lattice, f z = g z) (z : ℂ) : f z = g z :=
  tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] z)
    (hf.continuousAt.mono_left nhdsWithin_le_nhds) (hg.continuousAt.mono_left nhdsWithin_le_nhds)
    ((eventually_ne_notMem_periodLattice L z).mono h)

lemma Ent.ext_off (L : PeriodPair) {f g : Ent} (h : ∀ z ∉ L.lattice, f.1 z = g.1 z) : f = g :=
  Subtype.ext (funext (eq_of_eq_off L (Ent.diff f).continuous (Ent.diff g).continuous h))

lemma odeSer_tay (L : PeriodPair) {s : ℂ} {f : Ent}
    (h : ∀ z ∉ L.lattice, (wE s f).1 z = L.weierstrassP z * f.1 z ^ 2) :
    OdeSer s L.g₂ L.g₃ (tay f) := by
  have key : (dE (wE s f) * f - 2 * wE s f * dE f) ^ 2 =
      4 * wE s f ^ 3 - cE L.g₂ * wE s f * f ^ 4 - cE L.g₃ * f ^ 6 := by
    refine Ent.ext_off L fun z hz => ?_
    have h1 : HasDerivAt (wE s f).1
        (L.derivWeierstrassP z * f.1 z ^ 2 + L.weierstrassP z * (2 * f.1 z * deriv f.1 z)) z := by
      have := (hasDerivAt_weierstrassP L hz).mul ((Ent.diff f z).hasDerivAt.pow 2)
      refine HasDerivAt.congr_of_eventuallyEq (by simpa using this) ?_
      filter_upwards [eventually_notMem_periodLattice L hz] with w hw using h w hw
    have h2 := L.derivWeierstrassP_sq z hz
    have e2 : ((2 : Ent) : ℂ → ℂ) z = 2 := rfl
    have e4 : ((4 : Ent) : ℂ → ℂ) z = 4 := rfl
    simp only [dE, cE, Subring.coe_pow, AddSubgroupClass.coe_sub, Subring.coe_mul, Pi.pow_apply,
      Pi.sub_apply, Pi.mul_apply, e2, e4, h1.deriv, h z hz]
    linear_combination f.1 z ^ 6 * h2
  have := congrArg tay key
  simpa [OdeSer, tay_dE, tay_cE, tay_wE, map_ofNat] using this

lemma endSer_tay_iff (L : PeriodPair) {s α : ℂ} {f : Ent} {N m : ℕ} {q : ℕ → ℂ}
    (h : ∀ z ∉ L.lattice, (wE s f).1 z = L.weierstrassP z * f.1 z ^ 2)
    (h0 : ∀ z ∉ L.lattice, f.1 z ≠ 0) :
    EndSer α N m q s (tay f) ↔ ∀ z ∉ L.lattice, f.1 (α * z) ^ 2 =
      f.1 z ^ (2 * N) * ∑ k ∈ Finset.range (m + 1), q k * L.weierstrassP z ^ k := by
  have e : EndSer α N m q s (tay f) ↔ sE α f ^ 2 * f ^ (2 * m) = f ^ (2 * N) *
      ∑ k ∈ Finset.range (m + 1), cE (q k) * (wE s f ^ k * f ^ (2 * (m - k))) := by
    rw [← tay_injective.eq_iff]
    simp [EndSer, homSer, tay_sE, tay_cE, tay_wE]
  have e2 : ∀ z ∉ L.lattice,
      (∑ k ∈ Finset.range (m + 1), cE (q k) * (wE s f ^ k * f ^ (2 * (m - k))) : Ent).1 z =
      (∑ k ∈ Finset.range (m + 1), q k * L.weierstrassP z ^ k) * f.1 z ^ (2 * m) := by
    intro z hz
    rw [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
    simp only [cE, Subring.coe_pow, Subring.coe_mul, Pi.pow_apply, Pi.mul_apply, h z hz,
      Nat.add_sub_cancel_left]
    ring
  rw [e]
  constructor
  · intro H z hz
    have := congrArg (fun g : Ent => g.1 z) H
    simp only [Subring.coe_pow, Subring.coe_mul, Pi.pow_apply, Pi.mul_apply, e2 z hz, sE] at this
    exact mul_right_cancel₀ (pow_ne_zero (2 * m) (h0 z hz)) (by rw [this]; ring)
  · intro H
    refine Ent.ext_off L fun z hz => ?_
    simp only [Subring.coe_pow, Subring.coe_mul, Pi.pow_apply, Pi.mul_apply, e2 z hz, sE, H z hz]
    ring

def twist (c : ℂ) (f : Ent) : Ent :=
  ⟨fun z => f.1 z * Complex.exp (c * z ^ 2), by
    have := Ent.diff f
    change Differentiable ℂ _
    fun_prop⟩

lemma deriv_twist (c : ℂ) (f : Ent) : deriv (twist c f).1 =
    fun z => (deriv f.1 z + 2 * c * z * f.1 z) * Complex.exp (c * z ^ 2) := by
  funext z
  have := (Ent.diff f z).hasDerivAt.mul (((hasDerivAt_pow 2 z).const_mul c).cexp)
  refine (HasDerivAt.deriv this).trans ?_
  simp; ring

lemma wE_twist (s c : ℂ) (f : Ent) (z : ℂ) :
    (wE (s - 2 * c) (twist c f)).1 z = (wE s f).1 z * Complex.exp (c * z ^ 2) ^ 2 := by
  have := ((Ent.diff (dE f) z).hasDerivAt.add
    (((hasDerivAt_id z).const_mul (2 * c)).mul (Ent.diff f z).hasDerivAt)).mul
      (((hasDerivAt_pow 2 z).const_mul c).cexp)
  have h2 : deriv (fun z => (deriv f.1 z + 2 * c * z * f.1 z) * Complex.exp (c * z ^ 2)) z = _ :=
    HasDerivAt.deriv this
  rw [wE_apply, wE_apply, deriv_twist, h2]
  simp [twist, dE]; ring

lemma coeff_tay_of_odd {f : Ent} (h1 : deriv f.1 0 = 1) (ho : ∀ z, f.1 (-z) = -f.1 z) :
    coeff 0 (tay f) = 0 ∧ coeff 1 (tay f) = 1 ∧ coeff 2 (tay f) = 0 := by
  have e : sE (-1) f = -f := by ext z; simp [sE, ho]
  have := congrArg tay e
  rw [tay_sE, map_neg] at this
  have e0 := congrArg (coeff 0) this
  have e2 := congrArg (coeff 2) this
  simp only [coeff_rescale, map_neg] at e0 e2
  exact ⟨by linear_combination e0 / 2, by simp [coeff_tay, coef1, h1], by linear_combination e2 / 2⟩

end Taylor

section Lattice

variable (L : PeriodPair)

lemma exists_wE {f : Ent} (h00 : f.1 0 = 0) (h1 : deriv f.1 0 = 1) (h0 : ∀ z ∉ L.lattice, f.1 z ≠ 0)
    (hadd : ∀ u ∉ L.lattice, ∀ v ∉ L.lattice, (L.weierstrassP u - L.weierstrassP v) *
      (f.1 u ^ 2 * f.1 v ^ 2) = -(f.1 (u + v) * f.1 (u - v))) :
    ∃ s, ∀ z ∉ L.lattice, (wE s f).1 z = L.weierstrassP z * f.1 z ^ 2 := by
  have hf := Ent.diff f
  have hfc := hf.continuous
  have hf' : Differentiable ℂ (deriv f.1) := Ent.diff (dE f)
  let φ : ℂ → ℂ → ℂ := fun u v =>
    f.1 (u + v) * f.1 (u - v) + L.weierstrassP u * f.1 u ^ 2 * f.1 v ^ 2
  let φ' : ℂ → ℂ → ℂ := fun u v => deriv f.1 (u + v) * f.1 (u - v) - f.1 (u + v) * deriv f.1 (u - v)
    + L.weierstrassP u * f.1 u ^ 2 * (2 * f.1 v * deriv f.1 v)
  have p : ∀ {g : ℂ → ℂ}, Differentiable ℂ g → ∀ u v,
      HasDerivAt (fun v => g (u + v)) (deriv g (u + v)) v := fun hg u v =>
    (hg _).hasDerivAt.comp_const_add u v
  have q : ∀ {g : ℂ → ℂ}, Differentiable ℂ g → ∀ u v,
      HasDerivAt (fun v => g (u - v)) (-deriv g (u - v)) v := fun hg u v =>
    (hg _).hasDerivAt.comp_const_sub u v
  have d1 : ∀ u v, HasDerivAt (φ u) (φ' u v) v := fun u v => by
    have := ((p hf u v).mul (q hf u v)).add
      (((hf v).hasDerivAt.pow 2).const_mul (L.weierstrassP u * f.1 u ^ 2))
    refine HasDerivAt.congr_deriv this ?_
    simp [φ']; ring
  have d2 : ∀ u, HasDerivAt (φ' u) (2 * (f.1 u * deriv (deriv f.1) u - deriv f.1 u ^ 2 +
      L.weierstrassP u * f.1 u ^ 2)) 0 := fun u => by
    have := (((p hf' u 0).mul (q hf u 0)).sub ((p hf u 0).mul (q hf' u 0))).add
      ((((hf 0).hasDerivAt.const_mul 2).mul (hf' 0).hasDerivAt).const_mul
        (L.weierstrassP u * f.1 u ^ 2))
    refine HasDerivAt.congr_deriv this ?_
    simp [h00, h1]; ring
  obtain ⟨u₀, hu₀⟩ := (eventually_ne_notMem_periodLattice L 0).exists
  refine ⟨-(f.1 u₀ * deriv (deriv f.1) u₀ - deriv f.1 u₀ ^ 2 + L.weierstrassP u₀ * f.1 u₀ ^ 2) /
    f.1 u₀ ^ 2, fun u hu => ?_⟩
  have e0 : (fun v => f.1 u₀ ^ 2 * φ u v) = fun v => f.1 u ^ 2 * φ u₀ v :=
    funext (eq_of_eq_off L (by simp only [φ]; fun_prop) (by simp only [φ]; fun_prop) fun v hv => by
      simp only [φ]
      linear_combination f.1 u₀ ^ 2 * hadd u hu v hv - f.1 u ^ 2 * hadd u₀ hu₀ v hv)
  have e1 : (fun v => f.1 u₀ ^ 2 * φ' u v) = fun v => f.1 u ^ 2 * φ' u₀ v :=
    funext fun v => ((d1 u v).const_mul _).unique (e0 ▸ (d1 u₀ v).const_mul _)
  have e2 := ((d2 u).const_mul (f.1 u₀ ^ 2)).unique (e1 ▸ (d2 u₀).const_mul _)
  have := h0 u₀ hu₀
  rw [wE_apply]
  field_simp
  linear_combination (-1 / 2 : ℂ) * e2

variable {L} {f : ℂ → ℂ} {k α : ℂ} {N : ℕ}

lemma exp_scale (hα : α * (starRingEnd ℂ) α = N) (z ω : ℂ) :
    Complex.exp (k * (2 * (α * z) + α * ω) * (starRingEnd ℂ) (α * ω)) =
      Complex.exp (k * (2 * z + ω) * (starRingEnd ℂ) ω) ^ N := by
  rw [← Complex.exp_nat_mul, ← hα, map_mul]
  congr 1; ring

lemma exists_poly (hf : Differentiable ℂ f) (h0 : ∀ z, f z = 0 ↔ z ∈ L.lattice)
    (ho : ∀ z, f (-z) = -f z)
    (hp : ∀ ω ∈ L.lattice, ∀ z, f (z + ω) ^ 2 =
      f z ^ 2 * Complex.exp (k * (2 * z + ω) * (starRingEnd ℂ) ω))
    (hα : α * (starRingEnd ℂ) α = N) (hL : ∀ ω ∈ L.lattice, α * ω ∈ L.lattice) :
    ∃ (m : ℕ) (q : ℕ → ℂ), ∀ z ∉ L.lattice, f (α * z) ^ 2 =
      f z ^ (2 * N) * ∑ j ∈ Finset.range (m + 1), q j * L.weierstrassP z ^ j := by
  obtain ⟨A, hA⟩ := exists_eq_polynomial_weierstrassP L
    (g := fun z => f (α * z) ^ 2 / f z ^ (2 * N))
    (by
      have h1 : AnalyticAt ℂ (fun z => f (α * z) ^ 2) 0 :=
        (show Differentiable ℂ (fun z => f (α * z) ^ 2) by fun_prop).analyticAt 0
      have h2 : AnalyticAt ℂ (fun z => f z ^ (2 * N)) 0 :=
        (show Differentiable ℂ (fun z => f z ^ (2 * N)) by fun_prop).analyticAt 0
      exact h1.meromorphicAt.div h2.meromorphicAt)
    (fun z hz => DifferentiableAt.div (by fun_prop) (by fun_prop)
      (pow_ne_zero _ fun h => hz ((h0 z).1 h)))
    (fun z ω hω => by
      simp only [pow_mul]
      rw [mul_add, hp _ (hL ω hω), hp ω hω, exp_scale hα, mul_pow,
        mul_div_mul_right _ _ (pow_ne_zero _ (Complex.exp_ne_zero _))])
    (fun z => by simp [ho, pow_mul])
  refine ⟨A.natDegree, A.coeff, fun z hz => ?_⟩
  rw [← Polynomial.eval_eq_sum_range, ← hA z hz,
    mul_div_cancel₀ _ (pow_ne_zero _ fun h => hz ((h0 z).1 h))]

lemma twist_eq_zero (hf : Differentiable ℂ f) (h0 : ∀ z, f z = 0 ↔ z ∈ L.lattice)
    (hp : ∀ ω ∈ L.lattice, ∀ z, f (z + ω) ^ 2 =
      f z ^ 2 * Complex.exp (k * (2 * z + ω) * (starRingEnd ℂ) ω))
    (hα : α * (starRingEnd ℂ) α = N) (hα0 : α ≠ 0) (hαN : α ^ 2 ≠ N) {c : ℂ} {R : ℂ → ℂ}
    (h : ∀ z ∉ L.lattice, (f (α * z) * Complex.exp (c * (α * z) ^ 2)) ^ 2 =
      (f z * Complex.exp (c * z ^ 2)) ^ (2 * N) * R (L.weierstrassP z)) : c = 0 := by
  have hfc := hf.continuous
  set κ : ℂ := 2 * c * (α ^ 2 - N) with hκ
  have h1 : ∀ z ∉ L.lattice, f (α * z) ^ 2 * Complex.exp (κ * z ^ 2) =
      (f z ^ 2) ^ N * R (L.weierstrassP z) := fun z hz => by
    apply mul_right_cancel₀ (pow_ne_zero (2 * N) (Complex.exp_ne_zero (c * z ^ 2)))
    have e : Complex.exp (κ * z ^ 2) * Complex.exp (c * z ^ 2) ^ (2 * N) =
        Complex.exp (c * (α * z) ^ 2) ^ 2 := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1; rw [hκ]; push_cast; ring
    have := h z hz
    rw [mul_pow, ← e, mul_pow (f z)] at this
    rw [← pow_mul]
    linear_combination this
  have h2 : ∀ ω ∈ L.lattice, ∀ z, f (α * (z + ω)) ^ 2 * Complex.exp (κ * (z + ω) ^ 2) =
      f (α * z) ^ 2 * Complex.exp (κ * z ^ 2) *
        Complex.exp (k * (2 * z + ω) * (starRingEnd ℂ) ω) ^ N := fun ω hω =>
    eq_of_eq_off L (by fun_prop) (by fun_prop) fun z hz => by
      rw [h1 z hz, h1 _ (fun h => hz (by simpa using sub_mem h hω)), hp ω hω,
        L.weierstrassP_add_coe z ⟨ω, hω⟩]
      ring
  have hω := L.ω₁_mem_lattice
  have hω0 : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  generalize L.ω₁ = ω at hω hω0
  have h3 : α * ω ∈ L.lattice := by
    have := h2 ω hω 0
    simpa [(h0 0).2 (zero_mem _), h0] using this
  have h4 : ∀ w, Complex.exp (κ * (w / α + ω) ^ 2) = Complex.exp (κ * (w / α) ^ 2) :=
    eq_of_eq_off L (by fun_prop) (by fun_prop) fun w hw => by
      have e := h2 ω hω (w / α)
      rw [mul_add, hp _ h3, exp_scale hα, mul_div_cancel₀ _ hα0] at e
      apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 fun h => hw ((h0 w).1 h))
        (pow_ne_zero N (Complex.exp_ne_zero (k * (2 * (w / α) + ω) * (starRingEnd ℂ) ω))))
      linear_combination e
  by_contra hc
  have hκ0 : κ ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hc) (sub_ne_zero.2 hαN)
  have h5 := h4 (α * ((Real.pi * Complex.I / (κ * ω) - ω) / 2))
  rw [mul_div_cancel_left₀ _ hα0] at h5
  have e : κ * ((Real.pi * Complex.I / (κ * ω) - ω) / 2 + ω) ^ 2 =
      κ * ((Real.pi * Complex.I / (κ * ω) - ω) / 2) ^ 2 + Real.pi * Complex.I := by
    field_simp; ring
  rw [e, Complex.exp_add_pi_mul_I] at h5
  exact Complex.exp_ne_zero _ (CharZero.neg_eq_self_iff.1 h5)

lemma sgStar_facts (L : PeriodPair) (Λ : AddSubgroup ℂ) (hL : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) :
    ∃ (f : Ent) (s k : ℂ), f.1 = sgStar Λ ∧ deriv f.1 0 = 1 ∧ (∀ z, f.1 (-z) = -f.1 z) ∧
      (∀ z, f.1 z = 0 ↔ z ∈ L.lattice) ∧
      (∀ ω ∈ L.lattice, ∀ z, f.1 (z + ω) ^ 2 =
        f.1 z ^ 2 * Complex.exp (k * (2 * z + ω) * (starRingEnd ℂ) ω)) ∧
      ∀ z ∉ L.lattice, (wE s f).1 z = L.weierstrassP z * f.1 z ^ 2 := by
  obtain ⟨⟨hd, hd1, hodd, hU⟩, hzero, -, hwp, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ
    ⟨L.ω₁, L.ω₂, L.indep, by
      ext z
      rw [hL, PeriodPair.mem_lattice, AddSubgroup.mem_closure_pair]
      simp⟩
  obtain ⟨-, -, -, -, hw, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ hL
  obtain ⟨s, hs⟩ := exists_wE L (f := ⟨sgStar Λ, hd⟩) ((hzero 0).2 Λ.zero_mem) hd1
    (fun z hz h => hz ((hL z).1 ((hzero z).1 h))) (fun u hu v hv => by
      have hu' : u ∉ Λ := fun h => hu ((hL u).1 h)
      have hv' : v ∉ Λ := fun h => hv ((hL v).1 h)
      rw [← (hw u hu').1, ← (hw v hv').1]
      exact hwp u v hu' hv')
  refine ⟨⟨sgStar Λ, hd⟩, s, Real.pi / area Λ, rfl, hd1, hodd, fun z => (hzero z).trans (hL z),
    fun ω hω z => ?_, hs⟩
  have e := congrArg (· ^ 2) (hU ω ((hL ω).2 hω) z)
  have e1 : ((if ω / 2 ∈ Λ then 1 else -1 : ℂ)) ^ 2 = 1 := by split_ifs <;> norm_num
  simp only [U1, mul_pow, e1, one_mul] at e
  change sgStar Λ (z + ω) ^ 2 = sgStar Λ z ^ 2 * _
  rw [← e, mul_assoc, ← Complex.exp_nat_mul, ← Complex.exp_add]
  have : ((2 : ℕ) : ℂ) * (-(Real.pi : ℂ) * z * (starRingEnd ℂ) ω / (area Λ : ℂ) -
      (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * (area Λ : ℂ))) +
      Real.pi / area Λ * (2 * z + ω) * (starRingEnd ℂ) ω = 0 := by
    push_cast; ring
  rw [this, Complex.exp_zero, mul_one]

end Lattice

lemma liftM_coe (M : IntermediateField ℚ ℂ) (x : M) : liftM M (x : ℂ) = x := by
  simp [TaylorLogMetric.liftM]

lemma coe_liftM {M : IntermediateField ℚ ℂ} {x : ℂ} (hx : x ∈ M) : (liftM M x : ℂ) = x := by
  simp [TaylorLogMetric.liftM, hx]

theorem conj_sgStar (L : PeriodPair) (Λ : AddSubgroup ℂ) (hL : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) {α : ℂ} {N : ℕ} (hαM : α ∈ M)
    (hρ : cj M ρ α = α) (hα : α * (starRingEnd ℂ) α = N) (hα0 : α ≠ 0) (hαN : α ^ 2 ≠ N)
    (hαL : ∀ ω ∈ Λ, α * ω ∈ Λ) (h2 : g2 Λ ∈ M) (h3 : g3 Λ ∈ M)
    (hc : ∀ n, coef1 (sgStar Λ) n ∈ M) (n : ℕ) :
    cj M ρ (coef1 (sgStar Λ) n) = coef1 (sgStar (lamConj M ρ Λ)) n := by
  obtain ⟨e2, e3, hΔ, -, -, -, hex⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ hL
  obtain ⟨L', a2, a3⟩ := hex (ρ (liftM M (g2 Λ))) (ρ (liftM M (g3 Λ))) (by
    have : (liftM M (g2 Λ)) ^ 3 - 27 * (liftM M (g3 Λ)) ^ 2 ≠ 0 := fun h => hΔ (by
      have := congrArg (algebraMap M ℂ) h
      simp only [map_sub, map_mul, map_pow, map_ofNat, map_zero] at this
      simpa [coe_liftM h2, coe_liftM h3, TaylorLogMetric.discr] using this)
    have := (map_ne_zero ρ).2 this
    simpa [map_ofNat] using this)
  obtain ⟨b2, b3, -, -, -, huniq, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L'
    L'.lattice.toAddSubgroup (fun _ => Iff.rfl)
  have hspec : g2 (lamConj M ρ Λ) = ρ (liftM M (g2 Λ)) ∧ g3 (lamConj M ρ Λ) = ρ (liftM M (g3 Λ)) :=
    Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ =>
      g2 Λ' = ρ (liftM M (g2 Λ)) ∧ g3 Λ' = ρ (liftM M (g3 Λ)))
      ⟨L'.lattice.toAddSubgroup, b2.trans a2, b3.trans a3⟩
  have hL' : ∀ z, z ∈ lamConj M ρ Λ ↔ z ∈ L'.lattice := fun z => by
    rw [huniq _ (hspec.1.trans (b2.trans a2).symm) (hspec.2.trans (b3.trans a3).symm)]
    rfl
  obtain ⟨f, s, k, hf, f1, fo, f0, fp, fw⟩ := sgStar_facts L Λ hL
  obtain ⟨g, s', k', hg, g1, go, g0, gp, gw⟩ := sgStar_facts L' _ hL'
  rw [← hf] at hc ⊢
  rw [← hg]
  let A : PowerSeries M := PowerSeries.mk fun n => liftM M (coef1 f.1 n)
  have hA : PowerSeries.map (algebraMap M ℂ) A = tay f := by
    ext n; simp [A, coeff_tay, coe_liftM (hc n)]
  obtain ⟨c0, c1, c2⟩ := coeff_tay_of_odd f1 fo
  have ode := odeSer_tay L fw
  have hs : s ∈ M := by
    rw [ode.const_eq c0 c1 c2, coeff_tay]
    exact mul_mem (neg_mem (ofNat_mem M 2)) (hc 3)
  obtain ⟨m, q, hq⟩ := exists_poly (Ent.diff f) f0 fo fp hα
    (fun ω hω => (hL _).1 (hαL ω ((hL _).2 hω)))
  have en := (endSer_tay_iff L fw (fun z hz h => hz ((f0 z).1 h))).2 hq
  have ι : ∀ {x : ℂ}, x ∈ M → algebraMap M ℂ (liftM M x) = x := fun hx => coe_liftM hx
  rw [← hA, ← ι hs, ← e2, ← e3, ← ι h2, ← ι h3] at ode
  rw [← hA, ← ι hs, ← ι hαM] at en
  obtain ⟨q', en'⟩ := en.descend
  have ode' := (ode.of_map _ (algebraMap M ℂ).injective).map (ρ : M →+* ℂ)
  have en'' := en'.map (ρ : M →+* ℂ)
  simp only [RingHom.coe_coe] at ode' en''
  rw [← a2, ← a3] at ode'
  rw [show ρ (liftM M α) = α from hρ] at en''
  obtain ⟨c, hcs⟩ : ∃ c, ρ (liftM M s) = s' - 2 * c := ⟨(s' - ρ (liftM M s)) / 2, by ring⟩
  rw [hcs] at ode' en''
  have tw : ∀ z ∉ L'.lattice, (wE (s' - 2 * c) (twist c g)).1 z =
      L'.weierstrassP z * (twist c g).1 z ^ 2 := fun z hz => by
    rw [wE_twist, gw z hz]; simp only [twist]; ring
  obtain ⟨t0, t1, t2⟩ := coeff_tay_of_odd (f := twist c g)
    (by simp [deriv_twist, g1]) (fun z => by simp [twist, go])
  have cA : ∀ n, PowerSeries.coeff n (PowerSeries.map (ρ : M →+* ℂ) A) = cj M ρ (coef1 f.1 n) :=
    fun n => by simp [A, cj]
  have l0 : liftM M 0 = 0 := liftM_coe M 0
  have l1 : liftM M 1 = 1 := liftM_coe M 1
  have eq := theta_unique (by rw [cA, ← coeff_tay, c0, cj, l0, map_zero])
    (by rw [cA, ← coeff_tay, c1, cj, l1, map_one]) (by rw [cA, ← coeff_tay, c2, cj, l0, map_zero])
    t0 t1 t2 ode' (odeSer_tay L' tw)
  rw [eq, endSer_tay_iff L' tw (fun z hz =>
    mul_ne_zero (fun h => hz ((g0 z).1 h)) (Complex.exp_ne_zero _))] at en''
  have hc0 : c = 0 := twist_eq_zero (Ent.diff g) g0 gp hα hα0 hαN
    (R := fun x => ∑ j ∈ Finset.range (m + 1), ρ (q' j) * x ^ j) en''
  rw [← cA, eq, coeff_tay, hc0]
  simp [twist]

theorem galSg_all : ∀ D : D7, galSg D := by
  intro D cc δ h M ρ hK h2 h3 hc n
  obtain ⟨⟨w₁, w₂, hw, he⟩, -, -, -, hcm⟩ :=
    GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ h
  let L : PeriodPair := ⟨w₁, w₂, hw⟩
  have hL : ∀ z, z ∈ lamOf D cc δ ↔ z ∈ L.lattice := fun z => by
    rw [he, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
    simp [L]
  obtain ⟨b, hb⟩ : ∃ b : D.host.K, b ^ 2 = -(D.host.d : D.host.K) :=
    ⟨_, Formalism.FrobeniusOrbits.SplitK.bK_sq (D.host.sqd_sq)⟩
  have hbi : IsIntegral ℤ b := IsIntegral.of_pow two_pos (by
    rw [hb]; exact (isIntegral_natCast _).neg)
  have hd : (D.host.d : ℝ) ≠ 0 := by exact_mod_cast D.host.hyp.2.1.pos.ne'
  have hsq : D.host.φ₀ (b : D.host.E) ^ 2 = -(D.host.d : ℂ) := by
    have := congrArg (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) hb
    rw [map_pow, map_neg, map_natCast] at this
    exact this
  have hcm' := hcm ⟨b, hbi⟩
  have hK' := hK b
  change ∀ w ∈ _, D.host.φ₀ (b : D.host.E) * w ∈ _ at hcm'
  generalize D.host.φ₀ (b : D.host.E) = α at hsq hcm' hK'
  have hdc : (D.host.d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hn : α * (starRingEnd ℂ) α = D.host.d := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← norm_pow, hsq]
    simp
  exact conj_sgStar L _ hL M ρ hK'.1 hK'.2 hn (fun h0 => hdc (by simpa [h0] using hsq))
    (fun h0 => hdc (by linear_combination (hsq - h0) / 2)) hcm' h2 h3 hc n

end GlobalTheory.SigmaConj
end
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_taylorSeries_canonicalOddTheta_all : ∀ D : D7, galSg D := by
  atlas_forward_decl GlobalTheory.SigmaConj.galSg_all
end

section
open Filter Topology

namespace GlobalTheory.JetConj

def JetRel (S : Subring (ℂ × ℂ)) (f g : ℂ → ℂ) : Prop :=
  AnalyticAt ℂ f 0 ∧ AnalyticAt ℂ g 0 ∧ ∀ n, (iteratedDeriv n f 0, iteratedDeriv n g 0) ∈ S

def IsFieldGraph (S : Subring (ℂ × ℂ)) : Prop :=
  (∀ a b, (a, b) ∈ S → (a = 0 ↔ b = 0)) ∧ ∀ a b, (a, b) ∈ S → (a⁻¹, b⁻¹) ∈ S

noncomputable def graph (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) : Subring (ℂ × ℂ) :=
  (RingHom.prod (M.val : M →+* ℂ) (ρ : M →+* ℂ)).range

lemma mem_graph {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ} {a b : ℂ} :
    (a, b) ∈ graph M ρ ↔ ∃ h : a ∈ M, ρ ⟨a, h⟩ = b := by
  simp only [graph, RingHom.mem_range, RingHom.prod_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨x, hx, hy⟩
    subst hx
    exact ⟨x.2, hy⟩
  · rintro ⟨h, hb⟩
    exact ⟨⟨a, h⟩, rfl, hb⟩

lemma isFieldGraph_graph (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) : IsFieldGraph (graph M ρ) := by
  refine ⟨fun a b hab => ?_, fun a b hab => ?_⟩
  · obtain ⟨h, rfl⟩ := mem_graph.1 hab
    rw [map_eq_zero]
    exact ⟨fun ha => Subtype.ext ha, fun h0 => congrArg Subtype.val h0⟩
  · obtain ⟨h, rfl⟩ := mem_graph.1 hab
    refine mem_graph.2 ⟨inv_mem h, ?_⟩
    rw [← map_inv₀]
    rfl

variable {S : Subring (ℂ × ℂ)} {f f' g g' h h' : ℂ → ℂ}

lemma pair_natCast (S : Subring (ℂ × ℂ)) (n : ℕ) : ((n : ℂ), (n : ℂ)) ∈ S := by
  convert natCast_mem S n using 1
  ext <;> simp

lemma pair_mul {a b c d : ℂ} (h1 : (a, b) ∈ S) (h2 : (c, d) ∈ S) : (a * c, b * d) ∈ S := S.mul_mem h1 h2

lemma pair_add {a b c d : ℂ} (h1 : (a, b) ∈ S) (h2 : (c, d) ∈ S) : (a + c, b + d) ∈ S := S.add_mem h1 h2

lemma pair_sub {a b c d : ℂ} (h1 : (a, b) ∈ S) (h2 : (c, d) ∈ S) : (a - c, b - d) ∈ S := S.sub_mem h1 h2

lemma pair_sum {ι : Type*} (s : Finset ι) {a b : ι → ℂ} (h : ∀ i ∈ s, (a i, b i) ∈ S) :
    (∑ i ∈ s, a i, ∑ i ∈ s, b i) ∈ S := by
  have hs : (∑ i ∈ s, ((a i, b i) : ℂ × ℂ)) ∈ S := sum_mem h
  convert hs using 1
  ext <;> simp [Prod.fst_sum, Prod.snd_sum]

lemma JetRel.congr (H : JetRel S f f') (h1 : f =ᶠ[𝓝 0] g) (h2 : f' =ᶠ[𝓝 0] g') : JetRel S g g' := by
  obtain ⟨hf, hf', hd⟩ := H
  refine ⟨hf.congr h1, hf'.congr h2, fun n => ?_⟩
  rw [← h1.iteratedDeriv_eq n, ← h2.iteratedDeriv_eq n]
  exact hd n

lemma JetRel.zero (H : JetRel S f f') : (f 0, f' 0) ∈ S := by simpa using H.2.2 0

lemma JetRel.const {a b : ℂ} (h : (a, b) ∈ S) : JetRel S (fun _ => a) (fun _ => b) := by
  refine ⟨analyticAt_const, analyticAt_const, fun n => ?_⟩
  rw [iteratedDeriv_const, iteratedDeriv_const]
  split_ifs
  · exact h
  · exact S.zero_mem

lemma JetRel.sub (H : JetRel S f f') (K : JetRel S g g') :
    JetRel S (fun z => f z - g z) (fun z => f' z - g' z) := by
  obtain ⟨hf, hf', hdf⟩ := H
  obtain ⟨hg, hg', hdg⟩ := K
  refine ⟨by fun_prop, by fun_prop, fun n => ?_⟩
  rw [iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt, iteratedDeriv_fun_sub hf'.contDiffAt hg'.contDiffAt]
  exact pair_sub (hdf n) (hdg n)

private lemma iteratedDeriv_mul_mem_of_iteratedDeriv_mem (hf : AnalyticAt ℂ f 0) (hf' : AnalyticAt ℂ f' 0) (hg : AnalyticAt ℂ g 0)
    (hg' : AnalyticAt ℂ g' 0) (n : ℕ) (H : ∀ i ≤ n, (iteratedDeriv i f 0, iteratedDeriv i f' 0) ∈ S)
    (K : ∀ i ≤ n, (iteratedDeriv i g 0, iteratedDeriv i g' 0) ∈ S) :
    (iteratedDeriv n (fun z => f z * g z) 0, iteratedDeriv n (fun z => f' z * g' z) 0) ∈ S := by
  rw [iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt, iteratedDeriv_fun_mul hf'.contDiffAt hg'.contDiffAt]
  exact pair_sum _ fun i hi => pair_mul (pair_mul (pair_natCast S _)
    (H i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))) (K (n - i) (Nat.sub_le n i))

lemma JetRel.mul (H : JetRel S f f') (K : JetRel S g g') :
    JetRel S (fun z => f z * g z) (fun z => f' z * g' z) := by
  obtain ⟨hf, hf', hdf⟩ := H
  obtain ⟨hg, hg', hdg⟩ := K
  exact ⟨by fun_prop, by fun_prop, fun n => iteratedDeriv_mul_mem_of_iteratedDeriv_mem hf hf' hg hg' n (fun i _ => hdf i) (fun i _ => hdg i)⟩

lemma JetRel.pow (H : JetRel S f f') (k : ℕ) : JetRel S (fun z => f z ^ k) (fun z => f' z ^ k) := by
  induction k with
  | zero => simpa using JetRel.const (S := S) (a := 1) (b := 1) S.one_mem
  | succ k ih => simpa [pow_succ] using ih.mul H

lemma JetRel.deriv (H : JetRel S f f') : JetRel S (deriv f) (deriv f') := by
  obtain ⟨hf, hf', hd⟩ := H
  refine ⟨hf.deriv, hf'.deriv, fun n => ?_⟩
  rw [← iteratedDeriv_succ', ← iteratedDeriv_succ']
  exact hd (n + 1)

lemma JetRel.comp_mul (hf : Differentiable ℂ f) (hf' : Differentiable ℂ f') {c : ℂ} (hc : (c, c) ∈ S)
    (H : JetRel S f f') : JetRel S (fun z => f (c * z)) (fun z => f' (c * z)) := by
  obtain ⟨-, -, hd⟩ := H
  have d1 : Differentiable ℂ (fun z => f (c * z)) := by fun_prop
  have d2 : Differentiable ℂ (fun z => f' (c * z)) := by fun_prop
  refine ⟨d1.analyticAt 0, d2.analyticAt 0, fun n => ?_⟩
  simp only [iteratedDeriv_comp_const_mul hf.contDiff c, iteratedDeriv_comp_const_mul hf'.contDiff c, mul_zero]
  exact pair_mul (by simpa using S.pow_mem hc n) (hd n)

lemma JetRel.of_comp_mul (hS : IsFieldGraph S) (hf : Differentiable ℂ f) (hf' : Differentiable ℂ f')
    {c : ℂ} (hc0 : c ≠ 0) (hc : (c, c) ∈ S)
    (H : JetRel S (fun z => f (c * z)) (fun z => f' (c * z))) : JetRel S f f' := by
  have hc' : (c⁻¹, c⁻¹) ∈ S := hS.2 c c hc
  have d1 : Differentiable ℂ (fun z => f (c * z)) := by fun_prop
  have d2 : Differentiable ℂ (fun z => f' (c * z)) := by fun_prop
  simpa [mul_inv_cancel_left₀ hc0] using JetRel.comp_mul d1 d2 hc' H

lemma exists_iteratedDeriv_ne_zero (hg : AnalyticAt ℂ g 0) (h0 : ¬ g =ᶠ[𝓝 0] 0) :
    ∃ k, iteratedDeriv k g 0 ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply h0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hg.eventually_analyticAt
  have hd : DifferentiableOn ℂ g (Metric.ball 0 ε) := fun y hy =>
    (hball y hy).differentiableAt.differentiableWithinAt
  filter_upwards [Metric.ball_mem_nhds 0 hε] with z hz
  have hs := Complex.hasSum_taylorSeries_on_ball hd hz
  simp only [hcon, smul_zero] at hs
  exact (hasSum_zero.unique hs).symm

private lemma eq_div_of_binomial_convolution (a b c : ℕ → ℂ) (m n : ℕ) (hb : ∀ j < m, b j = 0) (hbm : b m ≠ 0)
    (hc : c (n + m) = ∑ j ∈ Finset.range (n + m + 1), ((n + m).choose j : ℂ) * a j * b (n + m - j)) :
    a n = (c (n + m) - ∑ j ∈ Finset.range n, ((n + m).choose j : ℂ) * a j * b (n + m - j)) *
      (((n + m).choose n : ℂ) * b m)⁻¹ := by
  have hC : ((n + m).choose n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_right n m)).ne'
  have htail : ∑ j ∈ Finset.Ico (n + 1) (n + m + 1), ((n + m).choose j : ℂ) * a j * b (n + m - j) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_Ico] at hj
    rw [hb (n + m - j) (by omega), mul_zero]
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : n + 1 ≤ n + m + 1), htail, add_zero,
    Finset.sum_range_succ, Nat.add_sub_cancel_left] at hc
  rw [hc, add_sub_cancel_left]
  field_simp

lemma JetRel.of_mul (hS : IsFieldGraph S) (hf : AnalyticAt ℂ f 0) (hf' : AnalyticAt ℂ f' 0)
    (G : JetRel S g g') (h0 : ¬ g =ᶠ[𝓝 0] 0)
    (H : JetRel S (fun z => f z * g z) (fun z => f' z * g' z)) : JetRel S f f' := by
  obtain ⟨hg, hg', hdg⟩ := G
  obtain ⟨-, -, hdH⟩ := H
  classical
  have hex : ∃ k, iteratedDeriv k g 0 ≠ 0 := exists_iteratedDeriv_ne_zero hg h0
  set m := Nat.find hex with hmdef
  have hm : iteratedDeriv m g 0 ≠ 0 := Nat.find_spec hex
  have hlt : ∀ j < m, iteratedDeriv j g 0 = 0 := fun j hj => not_not.1 (Nat.find_min hex hj)
  have hm' : iteratedDeriv m g' 0 ≠ 0 := fun h => hm ((hS.1 _ _ (hdg m)).2 h)
  have hlt' : ∀ j < m, iteratedDeriv j g' 0 = 0 := fun j hj => (hS.1 _ _ (hdg j)).1 (hlt j hj)
  refine ⟨hf, hf', fun n => ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hc : iteratedDeriv (n + m) (fun z => f z * g z) 0 = _ := iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt
    have hc' : iteratedDeriv (n + m) (fun z => f' z * g' z) 0 = _ :=
      iteratedDeriv_fun_mul hf'.contDiffAt hg'.contDiffAt
    have e1 := eq_div_of_binomial_convolution (fun j => iteratedDeriv j f 0) (fun j => iteratedDeriv j g 0)
      (fun j => iteratedDeriv j (fun z => f z * g z) 0) m n hlt hm hc
    have e2 := eq_div_of_binomial_convolution (fun j => iteratedDeriv j f' 0) (fun j => iteratedDeriv j g' 0)
      (fun j => iteratedDeriv j (fun z => f' z * g' z) 0) m n hlt' hm' hc'
    beta_reduce at e1 e2
    rw [e1, e2]
    refine pair_mul (pair_sub (hdH (n + m)) (pair_sum _ fun j hj =>
      pair_mul (pair_mul (pair_natCast S _) (ih j (Finset.mem_range.1 hj))) (hdg _)))
      (hS.2 _ _ (pair_mul (pair_natCast S _) (hdg m)))

lemma JetRel.of_deriv_eq (hf : AnalyticAt ℂ f 0) (hf' : AnalyticAt ℂ f' 0) (G : JetRel S g g')
    (e : _root_.deriv f =ᶠ[𝓝 0] fun z => f z * g z) (e' : _root_.deriv f' =ᶠ[𝓝 0] fun z => f' z * g' z)
    (h0 : (f 0, f' 0) ∈ S) : JetRel S f f' := by
  obtain ⟨hg, hg', hdg⟩ := G
  refine ⟨hf, hf', fun n => ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simpa using h0
    | succ n =>
      rw [iteratedDeriv_succ', iteratedDeriv_succ', e.iteratedDeriv_eq n, e'.iteratedDeriv_eq n]
      exact iteratedDeriv_mul_mem_of_iteratedDeriv_mem hf hf' hg hg' n (fun i hi => ih i (Nat.lt_succ_of_le hi)) (fun i _ => hdg i)

private lemma deriv_eventuallyEq_logDeriv_pow_succ {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hne : f 0 ≠ 0) (j : ℕ) :
    AnalyticAt ℂ (fun z => _root_.deriv (fun w => f w ^ (j + 1)) z / (((j + 1 : ℕ) : ℂ) * f z ^ (j + 1))) 0 ∧
    (_root_.deriv (fun w => f w ^ (j + 1)) =ᶠ[𝓝 0] fun z =>
      _root_.deriv (fun w => f w ^ (j + 1)) z / (((j + 1 : ℕ) : ℂ) * f z ^ (j + 1)) *
        (((j + 1 : ℕ) : ℂ) * f z ^ (j + 1))) ∧
    (_root_.deriv f =ᶠ[𝓝 0] fun z =>
      f z * (_root_.deriv (fun w => f w ^ (j + 1)) z / (((j + 1 : ℕ) : ℂ) * f z ^ (j + 1)))) := by
  have hk : ((j + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero j)
  have hu : AnalyticAt ℂ (fun w => f w ^ (j + 1)) 0 := by fun_prop
  have hne' : ∀ᶠ z in 𝓝 (0 : ℂ), f z ≠ 0 := hf.continuousAt.eventually_ne hne
  refine ⟨hu.deriv.fun_div (by fun_prop) (mul_ne_zero hk (pow_ne_zero _ hne)), ?_, ?_⟩
  · filter_upwards [hne'] with z hz
    rw [div_mul_cancel₀ _ (mul_ne_zero hk (pow_ne_zero _ hz))]
  · filter_upwards [hne', hf.eventually_analyticAt] with z hz hza
    have hz' : f z ^ j ≠ 0 := pow_ne_zero j hz
    rw [deriv_fun_pow hza.differentiableAt, Nat.add_sub_cancel]
    field_simp
    ring

lemma JetRel.of_pow (hS : IsFieldGraph S) (hf : AnalyticAt ℂ f 0) (hf' : AnalyticAt ℂ f' 0) {k : ℕ}
    (hk : k ≠ 0) (H : JetRel S (fun z => f z ^ k) (fun z => f' z ^ k)) (h0 : (f 0, f' 0) ∈ S)
    (hne : f 0 ≠ 0) : JetRel S f f' := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hne' : f' 0 ≠ 0 := fun h => hne ((hS.1 _ _ h0).2 h)
  obtain ⟨hv, e1, e2⟩ := deriv_eventuallyEq_logDeriv_pow_succ hf hne j
  obtain ⟨hv', e1', e2'⟩ := deriv_eventuallyEq_logDeriv_pow_succ hf' hne' j
  have G : JetRel S (fun z => ((j + 1 : ℕ) : ℂ) * f z ^ (j + 1)) (fun z => ((j + 1 : ℕ) : ℂ) * f' z ^ (j + 1)) :=
    (JetRel.const (pair_natCast S (j + 1))).mul H
  have hnz : ¬ (fun z => ((j + 1 : ℕ) : ℂ) * f z ^ (j + 1)) =ᶠ[𝓝 0] 0 := fun hev =>
    mul_ne_zero (Nat.cast_ne_zero.2 (Nat.succ_ne_zero j)) (pow_ne_zero _ hne) hev.eq_of_nhds
  have V := JetRel.of_mul hS hv hv' G hnz (H.deriv.congr e1 e1')
  exact JetRel.of_deriv_eq hf hf' V e2 e2' h0

lemma jetRel_of_weierstrass_system {p q p' q' : ℂ → ℂ} {c c' : ℂ} (hc : (c, c') ∈ S)
    (hp : AnalyticAt ℂ p 0) (hp' : AnalyticAt ℂ p' 0) (hq : AnalyticAt ℂ q 0) (hq' : AnalyticAt ℂ q' 0)
    (e1 : deriv p =ᶠ[𝓝 0] q) (e1' : deriv p' =ᶠ[𝓝 0] q')
    (e2 : deriv q =ᶠ[𝓝 0] fun z => (6 * p z) * p z - c)
    (e2' : deriv q' =ᶠ[𝓝 0] fun z => (6 * p' z) * p' z - c')
    (h0 : (p 0, p' 0) ∈ S) (h1 : (q 0, q' 0) ∈ S) : JetRel S q q' := by
  have hA : AnalyticAt ℂ (fun z => 6 * p z * p z) 0 := by fun_prop
  have hA' : AnalyticAt ℂ (fun z => 6 * p' z * p' z) 0 := by fun_prop
  have hp6 : AnalyticAt ℂ (fun z => 6 * p z) 0 := by fun_prop
  have hp6' : AnalyticAt ℂ (fun z => 6 * p' z) 0 := by fun_prop
  have h6 : ((6 : ℂ), (6 : ℂ)) ∈ S := by simpa using pair_natCast S 6
  have key : ∀ n, (iteratedDeriv n p 0, iteratedDeriv n p' 0) ∈ S ∧
      (iteratedDeriv n q 0, iteratedDeriv n q' 0) ∈ S := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      cases n with
      | zero => exact ⟨by simpa using h0, by simpa using h1⟩
      | succ n =>
        refine ⟨?_, ?_⟩
        · rw [iteratedDeriv_succ', iteratedDeriv_succ', e1.iteratedDeriv_eq n, e1'.iteratedDeriv_eq n]
          exact (ih n (Nat.lt_succ_self n)).2
        · rw [iteratedDeriv_succ', iteratedDeriv_succ', e2.iteratedDeriv_eq n, e2'.iteratedDeriv_eq n,
            iteratedDeriv_fun_sub hA.contDiffAt contDiffAt_const,
            iteratedDeriv_fun_sub hA'.contDiffAt contDiffAt_const, iteratedDeriv_const, iteratedDeriv_const]
          refine pair_sub (iteratedDeriv_mul_mem_of_iteratedDeriv_mem hp6 hp6' hp hp' n (fun i hi => ?_)
            (fun i hi => (ih i (Nat.lt_succ_of_le hi)).1)) ?_
          · rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
            exact pair_mul h6 (ih i (Nat.lt_succ_of_le hi)).1
          · split_ifs
            · exact hc
            · exact S.zero_mem
  exact ⟨hq, hq', fun n => (key n).2⟩

end GlobalTheory.JetConj
end

section
open Filter Topology PeriodPair

namespace GlobalTheory.JetConj

noncomputable def wr (f : ℂ → ℂ) (z : ℂ) : ℂ := f z * deriv (deriv f) z - deriv f z ^ 2

lemma wr_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) : wr f z = wr g z := by
  unfold wr
  rw [h.eq_of_nhds, h.deriv.eq_of_nhds, h.deriv.deriv.eq_of_nhds]

lemma wr_mul {f g : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) :
    wr (fun w => f w * g w) z = wr f z * g z ^ 2 + f z ^ 2 * wr g z := by
  have e : deriv (fun w => f w * g w) =ᶠ[𝓝 z] fun w => deriv f w * g w + f w * deriv g w := by
    filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with w a b
    exact (a.differentiableAt.hasDerivAt.fun_mul b.differentiableAt.hasDerivAt).deriv
  have a := hf.differentiableAt.hasDerivAt
  have b := hg.differentiableAt.hasDerivAt
  have a' := hf.deriv.differentiableAt.hasDerivAt
  have b' := hg.deriv.differentiableAt.hasDerivAt
  unfold wr
  rw [e.deriv.eq_of_nhds, e.eq_of_nhds, ((a'.fun_mul b).fun_add (a.fun_mul b')).deriv]
  ring

lemma wr_pow {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (k : ℕ) :
    wr (fun w => f w ^ k) z * f z ^ 2 = k * (f z ^ k) ^ 2 * wr f z := by
  induction k with
  | zero => simp [wr]
  | succ k ih =>
    simp only [pow_succ (n := k)]
    rw [wr_mul (hf.fun_pow k) hf]
    push_cast
    linear_combination f z ^ 2 * ih

lemma wr_affine {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c d z : ℂ) :
    wr (fun w => f (c * w + d)) z = c ^ 2 * wr f (c * z + d) := by
  have key : ∀ {g : ℂ → ℂ}, Differentiable ℂ g →
      deriv (fun w => g (c * w + d)) = fun w => c * deriv g (c * w + d) := by
    intro g hg
    funext w
    have := (hg (c * w + d)).hasDerivAt.comp w (((hasDerivAt_id w).const_mul c).add_const d)
    rw [show (fun w => g (c * w + d)) = g ∘ fun w => c * id w + d from rfl, this.deriv]
    ring
  unfold wr
  rw [key hf, deriv_const_mul_field', key hf.deriv]
  ring

structure IsSigmaLike (L : PeriodPair) (σ : ℂ → ℂ) : Prop where
  diff : Differentiable ℂ σ
  deriv_zero : deriv σ 0 = 1
  zero_iff : ∀ z, σ z = 0 ↔ z ∈ L.lattice
  add : ∀ u v, u ∉ L.lattice → v ∉ L.lattice →
    (℘[L] u - ℘[L] v) * (σ u ^ 2 * σ v ^ 2) = -(σ (u + v) * σ (u - v))

variable {L : PeriodPair} {σ : ℂ → ℂ}

lemma eq_of_eqOn_compl_lattice (L : PeriodPair) {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ z ∉ L.lattice, f z = g z) : f = g :=
  Continuous.ext_on ((countable_periodLattice L).dense_compl ℂ) hf hg h

lemma second_deriv_sigma_product_at_zero (hσ : Differentiable ℂ σ) (a k l : ℂ) :
    deriv (deriv fun v => σ (a + v) * σ (a - v) * k + l * σ v ^ 2) 0 =
      2 * wr σ a * k + l * (2 * (deriv σ 0 ^ 2 + σ 0 * deriv (deriv σ) 0)) := by
  have p : ∀ {g : ℂ → ℂ}, Differentiable ℂ g → ∀ v, HasDerivAt (fun v => g (a + v)) (deriv g (a + v)) v :=
    fun hg v => (hg _).hasDerivAt.comp_const_add a v
  have m : ∀ {g : ℂ → ℂ}, Differentiable ℂ g → ∀ v, HasDerivAt (fun v => g (a - v)) (-deriv g (a - v)) v :=
    fun hg v => (hg _).hasDerivAt.comp_const_sub a v
  have e : (deriv fun v => σ (a + v) * σ (a - v) * k + l * σ v ^ 2) = fun v =>
      (deriv σ (a + v) * σ (a - v) - σ (a + v) * deriv σ (a - v)) * k + l * (2 * (σ v * deriv σ v)) := by
    funext v
    rw [((((p hσ v).fun_mul (m hσ v)).mul_const k).fun_add
      (((hσ v).hasDerivAt.fun_pow 2).const_mul l)).deriv]
    simp
    ring
  rw [e, (((((p hσ.deriv 0).fun_mul (m hσ 0)).fun_sub ((p hσ 0).fun_mul (m hσ.deriv 0))).mul_const k).fun_add
    ((((hσ 0).hasDerivAt.fun_mul (hσ.deriv 0).hasDerivAt).const_mul 2).const_mul l)).deriv]
  simp only [wr, add_zero, sub_zero]
  ring

lemma IsSigmaLike.add_wr (H : IsSigmaLike L σ) (a : ℂ) {b : ℂ} (hb : b ∉ L.lattice) :
    σ (a + b) * σ (a - b) = wr σ a * σ b ^ 2 - wr σ b * σ a ^ 2 := by
  have hσ := H.diff
  have hc := hσ.continuous
  have h1 := hσ.deriv.continuous
  have h2 := hσ.deriv.deriv.continuous
  refine congrFun (eq_of_eqOn_compl_lattice L (f := fun a => σ (a + b) * σ (a - b))
    (g := fun a => wr σ a * σ b ^ 2 - wr σ b * σ a ^ 2) (by fun_prop) (by unfold wr; fun_prop) ?_) a
  intro a ha
  have e : (fun v => σ (a + v) * σ (a - v) * σ b ^ 2 + (℘[L] a * (σ a ^ 2 * σ b ^ 2)) * σ v ^ 2) =
      fun v => σ (b + v) * σ (b - v) * σ a ^ 2 + (℘[L] b * (σ a ^ 2 * σ b ^ 2)) * σ v ^ 2 := by
    refine eq_of_eqOn_compl_lattice L (by fun_prop) (by fun_prop) fun v hv => ?_
    linear_combination σ b ^ 2 * H.add a v ha hv - σ a ^ 2 * H.add b v hb hv
  have e2 := congrArg (fun f => deriv (deriv f) 0) e
  simp only [second_deriv_sigma_product_at_zero hσ, H.deriv_zero, (H.zero_iff 0).2 (zero_mem _)] at e2
  linear_combination H.add a b ha hb - e2 / 2

lemma IsSigmaLike.double (H : IsSigmaLike L σ) {u : ℂ} (hu : u ∉ L.lattice) :
    σ (u + u) = -℘'[L] u * σ u ^ 4 := by
  have hσ := H.diff
  have e : (fun v => (℘[L] u - ℘[L] v) * (σ u ^ 2 * σ v ^ 2)) =ᶠ[𝓝 u] fun v => -(σ (u + v) * σ (u - v)) := by
    filter_upwards [eventually_notMem_periodLattice L hu] with v hv using H.add u v hu hv
  have d1 := ((hasDerivAt_weierstrassP L hu).const_sub (℘[L] u)).fun_mul
    (((hσ u).hasDerivAt.fun_pow 2).const_mul (σ u ^ 2))
  have d2 := (((hσ _).hasDerivAt.comp_const_add u u).fun_mul
    ((hσ _).hasDerivAt.comp_const_sub u u)).fun_neg
  have := d1.unique (d2.congr_of_eventuallyEq e)
  simp only [sub_self, H.deriv_zero, (H.zero_iff 0).2 (zero_mem _)] at this
  linear_combination -this

noncomputable def divQuot (σ : ℂ → ℂ) (u : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  σ (n * z + n * u) / σ (z + u) ^ (n ^ 2)

lemma IsSigmaLike.analyticAt_divQuot (H : IsSigmaLike L σ) {u z : ℂ} (hz : z + u ∉ L.lattice) (n : ℕ) :
    AnalyticAt ℂ (divQuot σ u n) z := by
  have hσ := H.diff
  have a : Differentiable ℂ fun z => σ (n * z + n * u) := by fun_prop
  have b : Differentiable ℂ fun z => σ (z + u) ^ (n ^ 2) := by fun_prop
  exact (a.analyticAt z).fun_div (b.analyticAt z) (pow_ne_zero _ (mt (H.zero_iff _).1 hz))

lemma eventually_add_notMem (L : PeriodPair) {u z : ℂ} (hz : z + u ∉ L.lattice) :
    ∀ᶠ w in 𝓝 z, w + u ∉ L.lattice :=
  (continuous_add_const u).continuousAt.eventually (eventually_notMem_periodLattice L hz)

lemma IsSigmaLike.divQuot_rec (H : IsSigmaLike L σ) {u z : ℂ} (hz : z + u ∉ L.lattice) (n : ℕ) :
    divQuot σ u (n + 2) z * (((n + 1 : ℕ) : ℂ) ^ 2 * divQuot σ u n z) = wr (divQuot σ u (n + 1)) z := by
  have hσ := H.diff
  have h0 : σ (z + u) ≠ 0 := mt (H.zero_iff _).1 hz
  have b : Differentiable ℂ fun z => σ (z + u) := by fun_prop
  have e : (fun w => σ ((n + 1 : ℕ) * w + (n + 1 : ℕ) * u)) =ᶠ[𝓝 z]
      fun w => divQuot σ u (n + 1) w * σ (w + u) ^ ((n + 1) ^ 2) := by
    filter_upwards [eventually_add_notMem L hz] with w hw
    rw [divQuot, div_mul_cancel₀ _ (pow_ne_zero _ (mt (H.zero_iff _).1 hw))]
  have e1 := wr_congr e
  rw [wr_affine hσ, wr_mul (H.analyticAt_divQuot hz _) ((b.analyticAt z).fun_pow _)] at e1
  have e2 := wr_pow (b.analyticAt z) ((n + 1) ^ 2)
  have e3 := wr_affine hσ 1 u z
  simp only [one_mul, one_pow] at e3
  rw [e3] at e2
  have e4 := H.add_wr ((n + 1 : ℕ) * z + (n + 1 : ℕ) * u) hz
  have e5 := e.eq_of_nhds
  rw [show ((n + 1 : ℕ) : ℂ) * z + (n + 1 : ℕ) * u + (z + u) = (n + 2 : ℕ) * z + (n + 2 : ℕ) * u by
    push_cast; ring, show ((n + 1 : ℕ) : ℂ) * z + (n + 1 : ℕ) * u - (z + u) = n * z + n * u by
    push_cast; ring, e5] at e4
  have e6 : σ (z + u) ^ ((n + 2) ^ 2) * σ (z + u) ^ (n ^ 2) =
      (σ (z + u) ^ ((n + 1) ^ 2)) ^ 2 * σ (z + u) ^ 2 := by ring
  have h7 : σ (z + u) ^ ((n + 1) ^ 2) ≠ 0 := pow_ne_zero _ h0
  rw [divQuot, divQuot, div_mul_eq_mul_div, ← mul_div_assoc, ← mul_div_assoc, div_div, mul_comm (σ (z + u) ^ (n ^ 2)), e6,
    div_eq_iff (mul_ne_zero (pow_ne_zero _ h7) (pow_ne_zero _ h0))]
  push_cast at *
  linear_combination ((n : ℂ) + 1) ^ 2 * e4 + σ (z + u) ^ 2 * e1 + divQuot σ u (n + 1) z ^ 2 * e2

lemma IsSigmaLike.divQuot_ne (H : IsSigmaLike L σ) {u : ℂ} (hu : u ∉ L.lattice) {n : ℕ} (hn : n ≠ 0) :
    ¬ divQuot σ u n =ᶠ[𝓝 0] 0 := by
  intro h
  have hσ := H.diff
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have a : Differentiable ℂ fun z => σ (n * z + n * u) := by fun_prop
  have e : (fun z => σ (n * z + n * u)) =ᶠ[𝓝 0] 0 := by
    filter_upwards [h, eventually_add_notMem L (z := 0) (by simpa using hu)] with w hw hw'
    simpa [divQuot, mt (H.zero_iff _).1 hw'] using hw
  have e2 := (a.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ 0) e (Set.mem_univ (u / n - u))
  simp only [Pi.zero_apply] at e2
  rw [show (n : ℂ) * (u / n - u) + n * u = u by field_simp; ring] at e2
  exact hu ((H.zero_iff _).1 e2)

lemma JetRel.wr {S : Subring (ℂ × ℂ)} {f f' : ℂ → ℂ} (H : JetRel S f f') : JetRel S (wr f) (wr f') :=
  (H.mul H.deriv.deriv).sub (H.deriv.pow 2)

theorem jetRel_divQuot {S : Subring (ℂ × ℂ)} (hS : IsFieldGraph S) {L L' : PeriodPair} {σ σ' : ℂ → ℂ}
    (H : IsSigmaLike L σ) (H' : IsSigmaLike L' σ') {u u' : ℂ} (hu : u ∉ L.lattice) (hu' : u' ∉ L'.lattice)
    (hg : (L.g₂, L'.g₂) ∈ S) (hp : (℘[L] u, ℘[L'] u') ∈ S) (hq : (℘'[L] u, ℘'[L'] u') ∈ S) (n : ℕ) :
    JetRel S (divQuot σ u n) (divQuot σ' u' n) := by
  have z0 : ∀ {L : PeriodPair} {u : ℂ}, u ∉ L.lattice → 0 + u ∉ L.lattice := fun h => by simpa using h
  have c0 : ∀ {L : PeriodPair} {σ : ℂ → ℂ} {u : ℂ}, IsSigmaLike L σ →
      (fun _ => (0 : ℂ)) =ᶠ[𝓝 0] divQuot σ u 0 := fun H =>
    .of_forall fun z => by simp [divQuot, (H.zero_iff 0).2 (zero_mem _)]
  have c1 : ∀ {L : PeriodPair} {σ : ℂ → ℂ} {u : ℂ}, IsSigmaLike L σ → u ∉ L.lattice →
      (fun _ => (1 : ℂ)) =ᶠ[𝓝 0] divQuot σ u 1 := fun H hu => by
    filter_upwards [eventually_add_notMem _ (z0 hu)] with w hw
    simp [divQuot, mt (H.zero_iff _).1 hw]
  have c2 : ∀ {L : PeriodPair} {σ : ℂ → ℂ} {u : ℂ}, IsSigmaLike L σ → u ∉ L.lattice →
      (fun z => 0 - ℘'[L] (z + u)) =ᶠ[𝓝 0] divQuot σ u 2 := @fun L σ u H hu => by
    filter_upwards [eventually_add_notMem _ (z0 hu)] with w hw
    rw [divQuot, show ((2 : ℕ) : ℂ) * w + (2 : ℕ) * u = (w + u) + (w + u) by push_cast; ring, H.double hw]
    have := mt (H.zero_iff _).1 hw
    field_simp
    ring
  have c3 : ∀ {L : PeriodPair} {u : ℂ}, u ∉ L.lattice →
      AnalyticAt ℂ (fun z => ℘'[L] (z + u)) 0 ∧
      (deriv (fun z => ℘[L] (z + u)) =ᶠ[𝓝 0] fun z => ℘'[L] (z + u)) ∧
      (deriv (fun z => ℘'[L] (z + u)) =ᶠ[𝓝 0] fun z => 6 * ℘[L] (z + u) * ℘[L] (z + u) - L.g₂ * (2 : ℂ)⁻¹) :=
    @fun L u hu => by
    refine ⟨(L.analyticOnNhd_derivWeierstrassP _ (z0 hu)).comp (f := (· + u)) (by fun_prop), ?_, ?_⟩
    · filter_upwards [weierstrass_system_add_const L u (z0 hu)] with w hw using hw.1.deriv
    · filter_upwards [weierstrass_system_add_const L u (z0 hu)] with w hw
      rw [hw.2.deriv]; ring
  have hq2 : JetRel S (fun z => ℘'[L] (z + u)) (fun z => ℘'[L'] (z + u')) :=
    jetRel_of_weierstrass_system (pair_mul hg (hS.2 _ _ (pair_natCast S 2)))
      (analyticAt_weierstrassP_add L u (z0 hu)) (analyticAt_weierstrassP_add L' u' (z0 hu'))
      (c3 hu).1 (c3 hu').1 (c3 hu).2.1 (c3 hu').2.1 (c3 hu).2.2 (c3 hu').2.2
      (by simpa using hp) (by simpa using hq)
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  match n with
  | 0 => exact (JetRel.const S.zero_mem).congr (c0 H) (c0 H')
  | 1 => exact (JetRel.const S.one_mem).congr (c1 H hu) (c1 H' hu')
  | 2 => exact ((JetRel.const S.zero_mem).sub hq2).congr (c2 H hu) (c2 H' hu')
  | n + 3 =>
    have c4 : ∀ {L : PeriodPair} {σ : ℂ → ℂ} {u : ℂ}, IsSigmaLike L σ → u ∉ L.lattice →
        wr (divQuot σ u (n + 2)) =ᶠ[𝓝 0] fun z =>
          divQuot σ u (n + 3) z * (((n + 2 : ℕ) : ℂ) ^ 2 * divQuot σ u (n + 1) z) := fun H hu => by
      filter_upwards [eventually_add_notMem _ (z0 hu)] with w hw using (H.divQuot_rec hw (n + 1)).symm
    refine JetRel.of_mul hS (H.analyticAt_divQuot (z0 hu) _) (H'.analyticAt_divQuot (z0 hu') _)
      (((JetRel.const (pair_natCast S (n + 2))).pow 2).mul (ih (n + 1) (by omega))) ?_
      ((ih (n + 2) (by omega)).wr.congr (c4 H hu) (c4 H' hu'))
    intro e
    apply H.divQuot_ne hu (n := n + 1) (by omega)
    have hn : ((n + 2 : ℕ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : n + 2 ≠ 0))
    filter_upwards [e] with w hw using (mul_eq_zero.1 hw).resolve_left hn

end GlobalTheory.JetConj
end

section
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Filter Topology PeriodPair

namespace GlobalTheory.JetConj

lemma exists_periodPair {Λ : AddSubgroup ℂ}
    (h : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) :
    ∃ L : PeriodPair, ∀ z, z ∈ Λ ↔ z ∈ L.lattice := by
  obtain ⟨w₁, w₂, h, rfl⟩ := h
  refine ⟨⟨w₁, w₂, h⟩, fun z => ?_⟩
  simp [AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]

lemma exists_basis_of_periodPair {Λ : AddSubgroup ℂ} {L : PeriodPair} (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) :
    ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂} := by
  refine ⟨L.ω₁, L.ω₂, L.indep, ?_⟩
  ext z
  simp [h, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]

variable {Λ : AddSubgroup ℂ} {L : PeriodPair}

lemma isSigmaLike_sgStar (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) : IsSigmaLike L (sgStar Λ) := by
  obtain ⟨⟨a, b, -, -⟩, c, -, d, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ (exists_basis_of_periodPair h)
  obtain ⟨-, -, -, -, e, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ h
  refine ⟨a, b, fun z => (c z).trans (h z), fun u v hu hv => ?_⟩
  rw [← h] at hu hv
  rw [← (e u hu).1, ← (e v hv).1]
  exact d u v hu hv

lemma differentiable_U1 {G : ℂ → ℂ} (hG : Differentiable ℂ G) (x : ℂ) : Differentiable ℂ (U1 Λ x G) := by
  unfold U1
  fun_prop

lemma thetaTranslate_canonicalOddTheta_of_half_mem (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) {x : ℂ} (hx : x / 2 ∈ Λ) :
    U1 Λ x (sgStar Λ) = sgStar Λ := by
  obtain ⟨⟨-, -, -, a⟩, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ (exists_basis_of_periodPair h)
  funext z
  have : x ∈ Λ := by
    have := Λ.add_mem hx hx
    rwa [add_halves] at this
  rw [a x this, if_pos hx, one_mul]

lemma thetaTranslate_natCast_mul {G : ℂ → ℂ} {u z : ℂ} (hz : G (z + u) ≠ 0) (n : ℕ) :
    U1 Λ (n * u) G (n * z) = U1 Λ u G z ^ (n ^ 2) * divQuot G u n z := by
  unfold U1 divQuot
  rw [mul_pow, ← Complex.exp_nat_mul]
  have : -(Real.pi : ℂ) * (n * z) * (starRingEnd ℂ) (n * u) / (area Λ : ℂ) -
      (Real.pi : ℂ) * (n * u) * (starRingEnd ℂ) (n * u) / (2 * (area Λ : ℂ)) =
      ((n ^ 2 : ℕ) : ℂ) * (-(Real.pi : ℂ) * z * (starRingEnd ℂ) u / (area Λ : ℂ) -
      (Real.pi : ℂ) * u * (starRingEnd ℂ) u / (2 * (area Λ : ℂ))) := by
    simp only [map_mul, map_natCast]
    push_cast
    ring
  rw [this]
  field_simp

lemma thetaTranslate_zero_at_shifted_point (G : ℂ → ℂ) (u : ℂ) (N s : ℝ) (hs : s ^ 2 = 1) :
    U1 Λ ((N + s : ℝ) * u) G 0 = U1 Λ (N * u) G (s * u) *
      Complex.exp (-((Real.pi : ℂ) * u * (starRingEnd ℂ) u / (2 * (area Λ : ℂ)))) := by
  have hs' : (s : ℂ) ^ 2 = 1 := by exact_mod_cast hs
  unfold U1
  rw [mul_assoc (G _), ← Complex.exp_add]
  congr 2
  · push_cast; ring
  · simp only [map_mul, Complex.conj_ofReal]
    push_cast
    linear_combination (-((Real.pi : ℂ) * u * (starRingEnd ℂ) u / (2 * (area Λ : ℂ)))) * hs'

lemma translate_facts (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) {u : ℂ} (hu : u ∉ Λ) {m k : ℕ}
    (hk : m ^ 2 = k + 1) (hN : ((m ^ 2 : ℕ) : ℂ) * u ∈ Λ) :
    ∃ K : ℂ → ℂ, AnalyticAt ℂ K 0 ∧ K 0 ≠ 0 ∧
      ((fun z => U1 Λ ((2 * m : ℕ) * u) (sgStar Λ) ((2 * m : ℕ) * z)) =ᶠ[𝓝 0]
        fun z => K z * divQuot (sgStar Λ) u (2 * m) z) ∧
      ((fun z => sgStar Λ ((2 * m ^ 2 : ℕ) * z)) =ᶠ[𝓝 0]
        fun z => K z ^ (m ^ 2) * divQuot (sgStar Λ) u (2 * m ^ 2) z) ∧
      K 0 = (0 - divQuot (sgStar Λ) u k 0) * (divQuot (sgStar Λ) u (k + 2) 0)⁻¹ := by
  have H := isSigmaLike_sgStar h
  obtain ⟨⟨-, -, hodd, hq⟩, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ (exists_basis_of_periodPair h)
  have hu' : 0 + u ∉ L.lattice := by simpa [← h] using hu
  have hev : ∀ᶠ z in 𝓝 0, sgStar Λ (z + u) ≠ 0 :=
    (eventually_add_notMem L hu').mono fun z hz => mt (H.zero_iff _).1 hz
  have h0 : sgStar Λ (0 + u) ≠ 0 := hev.self_of_nhds
  have hc : U1 Λ u (sgStar Λ) 0 ≠ 0 := mul_ne_zero h0 (Complex.exp_ne_zero _)
  refine ⟨fun z => U1 Λ u (sgStar Λ) z ^ ((2 * m) ^ 2),
    ((differentiable_U1 H.diff u).analyticAt 0).fun_pow _, pow_ne_zero _ hc, ?_, ?_, ?_⟩
  · filter_upwards [hev] with z hz using thetaTranslate_natCast_mul hz _
  · filter_upwards [hev] with z hz
    rw [← pow_mul, show (2 * m) ^ 2 * m ^ 2 = (2 * m ^ 2) ^ 2 by ring, ← thetaTranslate_natCast_mul hz,
      thetaTranslate_canonicalOddTheta_of_half_mem h]
    convert hN using 1
    push_cast
    ring
  · have e1 := thetaTranslate_natCast_mul (Λ := Λ) h0 (k + 2)
    have e2 := thetaTranslate_natCast_mul (Λ := Λ) h0 k
    have f1 := thetaTranslate_zero_at_shifted_point (Λ := Λ) (sgStar Λ) u (k + 1) 1 (by norm_num)
    have f2 := thetaTranslate_zero_at_shifted_point (Λ := Λ) (sgStar Λ) u (k + 1) (-1) (by norm_num)
    have hN' : ((k + 1 : ℝ) : ℂ) * u ∈ Λ := by
      rw [hk] at hN
      exact_mod_cast hN
    rw [hq _ hN'] at f1 f2
    rw [show ((k + 1 + 1 : ℝ) : ℂ) = ((k + 2 : ℕ) : ℂ) by push_cast; ring] at f1
    rw [show ((k + 1 + -1 : ℝ) : ℂ) = ((k : ℕ) : ℂ) by push_cast; ring] at f2
    rw [mul_zero] at e1 e2
    rw [e1, Complex.ofReal_one, one_mul u] at f1
    rw [e2, Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul u, hodd] at f2
    have hψ : divQuot (sgStar Λ) u (k + 2) 0 ≠ 0 := by
      intro e
      rw [e, mul_zero] at f1
      rw [zero_add] at h0
      refine mul_ne_zero (mul_ne_zero ?_ h0) (Complex.exp_ne_zero _) f1.symm
      split_ifs <;> norm_num
    rw [eq_mul_inv_iff_mul_eq₀ hψ]
    apply mul_left_cancel₀ (pow_ne_zero (k ^ 2) hc)
    rw [show (k + 2) ^ 2 = k ^ 2 + (2 * m) ^ 2 by nlinarith, pow_add] at f1
    linear_combination f1 + f2

lemma taylorCoeff_mem_iff_iteratedDeriv_mem {M : IntermediateField ℚ ℂ} {f : ℂ → ℂ} {n : ℕ} :
    coef1 f n ∈ M ↔ iteratedDeriv n f 0 ∈ M := by
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  constructor
  · intro h
    have := M.mul_mem h (natCast_mem M n.factorial)
    rwa [coef1, div_mul_cancel₀ _ hn] at this
  · exact fun h => M.div_mem h (natCast_mem M _)

lemma mem_graph_iff_cj {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ} {a b : ℂ} :
    (a, b) ∈ graph M ρ ↔ a ∈ M ∧ cj M ρ a = b := by
  rw [mem_graph]
  constructor
  · rintro ⟨h, e⟩
    exact ⟨h, by rw [cj, TaylorLogMetric.liftM, dif_pos h, e]⟩
  · rintro ⟨h, e⟩
    exact ⟨h, by rwa [cj, TaylorLogMetric.liftM, dif_pos h] at e⟩

lemma pair_iteratedDeriv_iff {S : Subring (ℂ × ℂ)} (hS : IsFieldGraph S) {f g : ℂ → ℂ} {n : ℕ} :
    (iteratedDeriv n f 0, iteratedDeriv n g 0) ∈ S ↔ (coef1 f n, coef1 g n) ∈ S := by
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  constructor
  · intro h
    simpa [coef1, div_eq_mul_inv] using pair_mul h (hS.2 _ _ (pair_natCast S n.factorial))
  · intro h
    simpa [coef1, hn] using pair_mul h (pair_natCast S n.factorial)

lemma mem_graph_val {M : IntermediateField ℚ ℂ} {a : ℂ} : (a, a) ∈ graph M M.val ↔ a ∈ M := by
  exact ⟨fun h => (mem_graph.1 h).1, fun h => mem_graph.2 ⟨h, rfl⟩⟩

lemma exists_periodPair_lamConj (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) {M : IntermediateField ℚ ℂ}
    (ρ : M →ₐ[ℚ] ℂ) (h2 : g2 Λ ∈ M) (h3 : g3 Λ ∈ M) :
    ∃ L' : PeriodPair, (∀ z, z ∈ lamConj M ρ Λ ↔ z ∈ L'.lattice) ∧ (L.g₂, L'.g₂) ∈ graph M ρ := by
  obtain ⟨a2, a3, hd, -, -, -, hex⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ h
  have m2 : (g2 Λ, cj M ρ (g2 Λ)) ∈ graph M ρ := mem_graph_iff_cj.2 ⟨h2, rfl⟩
  have m3 : (g3 Λ, cj M ρ (g3 Λ)) ∈ graph M ρ := mem_graph_iff_cj.2 ⟨h3, rfl⟩
  have md := pair_sub (pair_mul m2 (pair_mul m2 m2))
    (pair_mul (pair_natCast _ 27) (pair_mul m3 m3))
  obtain ⟨L', b2, b3⟩ := hex (cj M ρ (g2 Λ)) (cj M ρ (g3 Λ)) (by
    intro e
    apply hd
    have := ((isFieldGraph_graph M ρ).1 _ _ md).2 (by push_cast; linear_combination e)
    unfold TaylorLogMetric.discr
    push_cast at this
    linear_combination this)
  obtain ⟨c2, c3, -, -, -, huniq, -⟩ :=
    GlobalTheory.LatticeInvariants.invariants_dictionary L' L'.lattice.toAddSubgroup (fun _ => Iff.rfl)
  have hs := Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ =>
    g2 Λ' = ρ (TaylorLogMetric.liftM M (g2 Λ)) ∧ g3 Λ' = ρ (TaylorLogMetric.liftM M (g3 Λ)))
    ⟨L'.lattice.toAddSubgroup, c2.trans b2, c3.trans b3⟩
  have e : lamConj M ρ Λ = L'.lattice.toAddSubgroup :=
    huniq _ (hs.1.trans (c2.trans b2).symm) (hs.2.trans (c3.trans b3).symm)
  refine ⟨L', fun z => by rw [e]; rfl, ?_⟩
  rw [← a2, b2]
  exact m2

theorem galois_translate_sgStar : ∀ D : D7, gal1 D := by
  intro D cc δ hc M ρ hK h2 h3 x x' m hm hmx hA hM n
  have hlat := (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ hc).1
  have hsg := GlobalTheory.T.galois_taylorSeries_canonicalOddTheta_all D cc δ hc M ρ hK h2 h3
  have hst := (GlobalTheory.ConjPoint.galStar_holds D cc δ hc M ρ hK h2 h3).2.2.2.2.2.1
  generalize lamOf D cc δ = Λ at *
  obtain ⟨L, hL⟩ := exists_periodPair hlat
  obtain ⟨L', hL', hg⟩ := exists_periodPair_lamConj hL ρ h2 h3
  have hm2 : ((2 * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2 * m ≠ 0)
  have hm3 : ((2 * m ^ 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : 2 * m ^ 2 ≠ 0)
  unfold Adp1 at hA
  obtain ⟨u, rfl⟩ : ∃ u, x = (2 * m : ℕ) * u := ⟨x / (2 * m : ℕ), by field_simp⟩
  obtain ⟨u', rfl⟩ : ∃ u, x' = (2 * m : ℕ) * u := ⟨x' / (2 * m : ℕ), by field_simp⟩
  rw [mul_div_cancel_left₀ _ hm2, mul_div_cancel_left₀ _ hm2] at hA
  have hN : ((m ^ 2 : ℕ) : ℂ) * u ∈ Λ := by
    convert hmx using 1
    push_cast
    ring
  have hN' := (hst (m ^ 2) u u' hA).1 hN
  have half : ∀ {Λ : AddSubgroup ℂ} {u : ℂ}, u ∈ Λ → ((2 * m : ℕ) : ℂ) * u / 2 ∈ Λ := by
    intro Λ u hu
    have := Λ.nsmul_mem hu m
    convert this using 1
    rw [nsmul_eq_mul]
    push_cast
    ring
  rcases hA with ⟨hu, hu'⟩ | ⟨hu, hu', p1, p2, p3, p4⟩
  · rw [thetaTranslate_canonicalOddTheta_of_half_mem hL (half hu)] at hM ⊢
    rw [thetaTranslate_canonicalOddTheta_of_half_mem hL' (half hu')]
    exact hsg hM n
  have H := isSigmaLike_sgStar hL
  have H' := isSigmaLike_sgStar hL'
  obtain ⟨-, -, -, -, e, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ hL
  obtain ⟨-, -, -, -, e', -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L' _ hL'
  rw [(e u hu).1] at p1 p3
  rw [(e u hu).2] at p2 p4
  rw [(e' u' hu').1] at p3
  rw [(e' u' hu').2] at p4
  have hS := isFieldGraph_graph M ρ
  have hS0 := isFieldGraph_graph M M.val
  have huL : u ∉ L.lattice := mt (hL u).2 hu
  have ψ := jetRel_divQuot hS H H' huL (mt (hL' u').2 hu') hg
    (mem_graph_iff_cj.2 ⟨p1, p3.symm⟩) (mem_graph_iff_cj.2 ⟨p2, p4.symm⟩)
  have ψ0 := jetRel_divQuot hS0 H H huL huL (mem_graph_val.2 (mem_graph_iff_cj.1 hg).1)
    (mem_graph_val.2 p1) (mem_graph_val.2 p2)
  obtain ⟨k, hk⟩ : ∃ k, m ^ 2 = k + 1 := Nat.exists_eq_succ_of_ne_zero (by positivity)
  obtain ⟨K, a1, a2, a3, a4, a5⟩ := translate_facts hL hu hk hN
  obtain ⟨K', b1, -, b3, b4, b5⟩ := translate_facts hL' hu' hk hN'
  have dG := differentiable_U1 (Λ := Λ) H.diff ((2 * m : ℕ) * u)
  have dG' := differentiable_U1 (Λ := lamConj M ρ Λ) H'.diff ((2 * m : ℕ) * u')

  have G0 : JetRel (graph M M.val) (U1 Λ ((2 * m : ℕ) * u) (sgStar Λ)) (U1 Λ ((2 * m : ℕ) * u) (sgStar Λ)) :=
    ⟨dG.analyticAt 0, dG.analyticAt 0, fun n => mem_graph_val.2 (taylorCoeff_mem_iff_iteratedDeriv_mem.1 (hM n))⟩
  have K0 : JetRel (graph M M.val) K K :=
    JetRel.of_mul hS0 a1 a1 (ψ0 (2 * m)) (H.divQuot_ne huL (by omega))
      ((G0.comp_mul dG dG (pair_natCast _ _)).congr a3 a3)
  have s0 : JetRel (graph M M.val) (sgStar Λ) (sgStar Λ) :=
    JetRel.of_comp_mul hS0 H.diff H.diff hm3 (pair_natCast _ _)
      (((K0.pow _).mul (ψ0 _)).congr a4.symm a4.symm)
  have sM : ∀ n, coef1 (sgStar Λ) n ∈ M := fun n => taylorCoeff_mem_iff_iteratedDeriv_mem.2 (mem_graph_val.1 (s0.2.2 n))
  have s1 : JetRel (graph M ρ) (sgStar Λ) (sgStar (lamConj M ρ Λ)) :=
    ⟨H.diff.analyticAt 0, H'.diff.analyticAt 0, fun n =>
      (pair_iteratedDeriv_iff hS).2 (mem_graph_iff_cj.2 ⟨sM n, hsg sM n⟩)⟩
  have K2 : JetRel (graph M ρ) (fun z => K z ^ (m ^ 2)) (fun z => K' z ^ (m ^ 2)) :=
    JetRel.of_mul hS (a1.fun_pow _) (b1.fun_pow _) (ψ (2 * m ^ 2)) (H.divQuot_ne huL (by positivity))
      ((s1.comp_mul H.diff H'.diff (pair_natCast _ _)).congr a4 b4)
  have K1 : JetRel (graph M ρ) K K' :=
    JetRel.of_pow hS a1 b1 (by positivity) K2 (by
      rw [a5, b5]
      exact pair_mul (pair_sub (Subring.zero_mem _) (ψ k).zero) (hS.2 _ _ (ψ (k + 2)).zero)) a2
  have G1 := JetRel.of_comp_mul hS dG dG' hm2 (pair_natCast _ _) ((K1.mul (ψ _)).congr a3.symm b3.symm)
  exact (mem_graph_iff_cj.1 ((pair_iteratedDeriv_iff hS).1 (G1.2.2 n))).2

end GlobalTheory.JetConj
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_conj_taylor_thetaTranslate : ∀ D : D7, gal1 D := by
  atlas_forward_decl GlobalTheory.JetConj.galois_translate_sgStar
end
