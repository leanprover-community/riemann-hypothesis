import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedHalf
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ExistsFinitePartOneIdeleSplitCongruenceQuotient
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedDefs
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion

section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem velu_pair (L : PeriodPair) (z P : ℂ) (hz : z ∉ L.lattice) (hP : P ∉ L.lattice)
    (hp : z + P ∉ L.lattice) (hm : z - P ∉ L.lattice) :
    (L.weierstrassP (z + P) - L.weierstrassP P) + (L.weierstrassP (z + -P) - L.weierstrassP (-P))
      = fW L.g₂ L.g₃ (L.weierstrassP P) / (L.weierstrassP z - L.weierstrassP P) ^ 2
        + fW' L.g₂ (L.weierstrassP P) / (2 * (L.weierstrassP z - L.weierstrassP P)) := by
  have hne := Formalism.L2.Th1.E.AddThm.P_sub_ne L z P hz hP hp hm
  have hP' : -P ∉ L.lattice := fun h => hP (by simpa using L.lattice.neg_mem h)
  have h1 := Formalism.L2.Th1.E.AddThm.P_add L z P hz hP hp hm
  have h2 := Formalism.L2.Th1.E.AddThm.P_add L z (-P) hz hP' (by simpa [sub_eq_add_neg] using hm)
    (by simpa using hp)
  rw [L.weierstrassP_neg, L.derivWeierstrassP_neg] at h2
  have hY := L.derivWeierstrassP_sq z hz
  have hy := L.derivWeierstrassP_sq P hP
  rw [L.weierstrassP_neg, h1, h2]
  unfold fW fW'
  generalize L.weierstrassP z = X at *
  generalize L.weierstrassP P = x at *
  generalize L.derivWeierstrassP z = Y at *
  generalize L.derivWeierstrassP P = y at *
  field_simp
  linear_combination 4 * hY + 4 * hy

theorem velu_fun (L : PeriodPair) (α : ℂ) (T : Finset ℂ) (hα : α ≠ 0) (hs : MulStable L α)
    (hT : IsHalfReps L α T) (z : ℂ) (hz : α * z ∉ L.lattice) :
    α ^ 2 * L.weierstrassP (α * z) = veluFun L.g₂ L.g₃ (xsOf L T) (L.weierstrassP z) := by
  obtain ⟨hK, hdisj⟩ := hT.kerReps
  have hzL : z ∉ L.lattice := fun h => hz (hs z h)
  rw [isogenyP L α _ hα hs hK z hz, Finset.sum_union hdisj,
    Finset.sum_image (by intro a _ b _ h; exact neg_injective h)]
  simp only [veluFun, xsOf]
  rw [Finset.sum_image (by intro a ha b hb h; exact hT.injOn ha hb h)]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun P hP => ?_
  obtain ⟨hαP, h2P⟩ := hT.1 P hP

  have hPL : P ∉ L.lattice := fun h => h2P (by rw [two_mul]; exact L.lattice.add_mem h h)

  have hp : z + P ∉ L.lattice := fun h => hz (by
    have := L.lattice.sub_mem (hs _ h) hαP
    rwa [mul_add, add_sub_cancel_right] at this)
  have hm : z - P ∉ L.lattice := fun h => hz (by
    have := L.lattice.add_mem (hs _ h) hαP
    rwa [mul_sub, sub_add_cancel] at this)
  exact velu_pair L z P hzL hPL hp hm

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

variable {K : Type} [Field K] [CharZero K] [DecidableEq K] (g2 g3 : K) (xs : Finset K)

theorem rootPoly_monic : (rootPoly xs).Monic := by
  unfold rootPoly
  exact monic_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)

theorem rootPoly_natDegree : (rootPoly xs).natDegree = xs.card := by
  unfold rootPoly
  rw [natDegree_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)]
  simp

theorem rootPoly_eval (t : K) : (rootPoly xs).eval t = ∏ x ∈ xs, (t - x) := by
  unfold rootPoly
  rw [eval_prod]
  simp

theorem rootPoly_eval_ne {t : K} (ht : t ∉ xs) : (rootPoly xs).eval t ≠ 0 := by
  rw [rootPoly_eval, Finset.prod_ne_zero_iff]
  intro x hx h
  rw [sub_eq_zero] at h
  exact ht (h ▸ hx)

theorem rootPoly_eval_mem {t : K} (ht : t ∈ xs) : (rootPoly xs).eval t = 0 := by
  rw [rootPoly_eval]
  exact Finset.prod_eq_zero ht (sub_self t)

theorem rootPoly_erase {x : K} (hx : x ∈ xs) :
    rootPoly xs = (X - C x) * rootPoly (xs.erase x) := by
  unfold rootPoly
  exact (Finset.mul_prod_erase xs (fun y => (X - C y : K[X])) hx).symm

theorem veluNum_eval' (t : K) :
    (veluNum g2 g3 xs).eval t = t * (rootPoly xs).eval t ^ 2
      + ∑ x ∈ xs, (fW g2 g3 x + fW' g2 x / 2 * (t - x)) * (rootPoly (xs.erase x)).eval t ^ 2 := by
  unfold veluNum
  simp [eval_finsetSum]

theorem veluNum_eval {t : K} (ht : t ∉ xs) :
    (veluNum g2 g3 xs).eval t = veluFun g2 g3 xs t * (rootPoly xs).eval t ^ 2 := by
  rw [veluNum_eval']
  unfold veluFun
  rw [add_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl (fun x hx => ?_)
  have hne : t - x ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    exact ht (h ▸ hx)
  rw [rootPoly_erase xs hx]
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  field_simp

theorem veluNum_natDegree_le : (veluNum g2 g3 xs).natDegree ≤ 2 * xs.card + 1 := by
  unfold veluNum
  refine natDegree_add_le_of_degree_le ?_ ?_
  · refine natDegree_mul_le.trans ?_
    have h1 := natDegree_pow_le (p := rootPoly xs) (n := 2)
    rw [rootPoly_natDegree] at h1
    rw [natDegree_X]
    omega
  · refine natDegree_sum_le_of_forall_le _ _ (fun x hx => ?_)
    refine natDegree_mul_le.trans ?_
    have h1 := natDegree_pow_le (p := rootPoly (xs.erase x)) (n := 2)
    rw [rootPoly_natDegree] at h1
    have h2 : (xs.erase x).card ≤ xs.card := Finset.card_erase_le
    have h3 : (C (fW g2 g3 x) + C (fW' g2 x / 2) * (X - C x) : K[X]).natDegree ≤ 1 := by
      refine natDegree_add_le_of_degree_le (by simp) ?_
      refine natDegree_mul_le.trans ?_
      simp
    omega

theorem veluNum_eval_mem {x : K} (hx : x ∈ xs) :
    (veluNum g2 g3 xs).eval x = fW g2 g3 x * (rootPoly (xs.erase x)).eval x ^ 2 := by
  rw [veluNum_eval', rootPoly_eval_mem xs hx, Finset.sum_eq_single_of_mem x hx]
  · simp
  · intro y _ hy
    rw [rootPoly_eval_mem (xs.erase y) (Finset.mem_erase.2 ⟨hy.symm, hx⟩)]
    simp

theorem veluNum_coprime (h : ∀ x ∈ xs, fW g2 g3 x ≠ 0) :
    IsCoprime (veluNum g2 g3 xs) (rootPoly xs ^ 2) := by
  refine IsCoprime.pow_right ?_
  unfold rootPoly
  refine IsCoprime.prod_right (fun x hx => ?_)
  refine IsCoprime.symm ?_
  rw [(irreducible_X_sub_C x).coprime_iff_not_dvd, dvd_iff_isRoot, IsRoot.def,
    veluNum_eval_mem g2 g3 xs hx]
  exact mul_ne_zero (h x hx) (pow_ne_zero 2 (rootPoly_eval_ne _ (Finset.notMem_erase x xs)))

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

def HasT (f : ℂ → ℂ) (s : PowerSeries ℂ) : Prop := AnalyticAt ℂ f 0 ∧ taylor0 f = s

theorem HasT.add {f g : ℂ → ℂ} {s t : PowerSeries ℂ} (hf : HasT f s) (hg : HasT g t) :
    HasT (fun z => f z + g z) (s + t) :=
  ⟨hf.1.add hg.1, by rw [(taylorRing.1 f g hf.1 hg.1).1, hf.2, hg.2]⟩

theorem HasT.mul {f g : ℂ → ℂ} {s t : PowerSeries ℂ} (hf : HasT f s) (hg : HasT g t) :
    HasT (fun z => f z * g z) (s * t) :=
  ⟨hf.1.mul hg.1, by rw [(taylorRing.1 f g hf.1 hg.1).2, hf.2, hg.2]⟩

theorem hasT_const (c : ℂ) : HasT (fun _ => c) (PowerSeries.C c) :=
  ⟨analyticAt_const, taylorRing.2.1 c⟩

theorem hasT_id : HasT (fun z => z) PowerSeries.X := ⟨analyticAt_id, taylorRing.2.2.1⟩

theorem HasT.pow {f : ℂ → ℂ} {s : PowerSeries ℂ} (hf : HasT f s) (n : ℕ) :
    HasT (fun z => f z ^ n) (s ^ n) := by
  induction n with
  | zero => simpa using hasT_const 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem hasT_sum {ι : Type} (S : Finset ι) (f : ι → ℂ → ℂ) (s : ι → PowerSeries ℂ)
    (h : ∀ i ∈ S, HasT (f i) (s i)) : HasT (fun z => ∑ i ∈ S, f i z) (∑ i ∈ S, s i) := by
  induction S using Finset.induction_on with
  | empty => simpa using hasT_const 0
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a S)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem HasT.rescale {f : ℂ → ℂ} {s : PowerSeries ℂ} (hf : HasT f s) (a : ℂ) :
    HasT (fun z => f (a * z)) (PowerSeries.rescale a s) := by
  refine ⟨?_, by rw [taylorDeriv.2.1 f a hf.1, hf.2]⟩
  refine AnalyticAt.fun_comp (f := fun z : ℂ => a * z) (g := f) ?_ (analyticAt_const.mul analyticAt_id)
  simpa using hf.1

def uFun (L : PeriodPair) (z : ℂ) : ℂ := 1 + z ^ 2 * L.weierstrassPExcept 0 z

theorem hasT_uFun (L : PeriodPair) : HasT (uFun L) (wpNum L.g₂ L.g₃) := by
  have h : HasT (L.weierstrassPExcept 0) (pOf L.g₂ L.g₃) :=
    ⟨L.analyticAt_weierstrassPExcept 0, pOfLattice L⟩
  rw [(wpNumDen ℂ L.g₂ L.g₃).1]
  have h3 := (hasT_const 1).add ((hasT_id.pow 2).mul h)
  rw [map_one] at h3
  exact h3

theorem uFun_eq (L : PeriodPair) {z : ℂ} (hz : z ≠ 0) : uFun L z = z ^ 2 * L.weierstrassP z := by
  have h := L.weierstrassPExcept_add 0 z
  simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, div_zero] at h
  rw [← h, uFun]
  field_simp
  ring

def homF (u : ℂ → ℂ) (m : ℕ) (Q : ℂ[X]) (z : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (m + 1), Q.coeff i * u z ^ i * z ^ (2 * (m - i))

theorem hasT_homF {u : ℂ → ℂ} {U : PowerSeries ℂ} (hu : HasT u U) (m : ℕ) (Q : ℂ[X]) :
    HasT (homF u m Q) (homS U m Q) :=
  hasT_sum _ _ _ fun i _ => ((hasT_const (Q.coeff i)).mul (hu.pow i)).mul (hasT_id.pow _)

theorem homF_eq {u : ℂ → ℂ} {m : ℕ} {Q : ℂ[X]} (hQ : Q.natDegree ≤ m) {z t : ℂ}
    (h : u z = z ^ 2 * t) : homF u m Q z = z ^ (2 * m) * Q.eval t := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hQ), Finset.mul_sum, homF]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  rw [h, Nat.add_sub_cancel_left]
  ring

theorem eventually_notMem (L : PeriodPair) {α : ℂ} (hα : α ≠ 0) :
    ∀ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ, z ≠ 0 ∧ α * z ∉ L.lattice := by
  have h1 : Filter.Tendsto (fun z : ℂ => α * z) (nhds 0) (nhds 0) := by
    have : ContinuousAt (fun z : ℂ => α * z) 0 := by fun_prop
    simpa [ContinuousAt] using this
  have h2 := h1 (L.compl_lattice_sdiff_singleton_mem_nhds 0)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [h2] with z hz hz0
  refine ⟨hz0, fun hm => hz ⟨hm, ?_⟩⟩
  simpa [hα] using hz0

theorem xs_notMem (L : PeriodPair) {α : ℂ} {T : Finset ℂ} (hs : MulStable L α)
    (hT : IsHalfReps L α T) {z : ℂ} (hz : α * z ∉ L.lattice) : L.weierstrassP z ∉ xsOf L T := by
  intro hm
  obtain ⟨P, hP, hPz⟩ := Finset.mem_image.1 hm
  have hz' : z ∉ L.lattice := fun h => hz (hs z h)
  have hP' : P ∉ L.lattice := fun h => (hT.1 P hP).2 (by
    rw [two_mul]; exact L.lattice.add_mem h h)
  have hαP := (hT.1 P hP).1
  rcases (pInjective L z P hz' hP').1 hPz.symm with h | h
  · apply hz
    have : α * z = α * (z - P) + α * P := by ring
    rw [this]; exact L.lattice.add_mem (hs _ h) hαP
  · apply hz
    have : α * z = α * (z + P) - α * P := by ring
    rw [this]; exact L.lattice.sub_mem (hs _ h) hαP

theorem velu_series (L : PeriodPair) (α : ℂ) (T : Finset ℂ) (hα : α ≠ 0) (hs : MulStable L α)
    (hT : IsHalfReps L α T) :
    PowerSeries.rescale α (wpNum L.g₂ L.g₃)
        * homS (wpNum L.g₂ L.g₃) (2 * (xsOf L T).card) (rootPoly (xsOf L T) ^ 2)
      = homS (wpNum L.g₂ L.g₃) (2 * (xsOf L T).card + 1) (veluNum L.g₂ L.g₃ (xsOf L T)) := by
  have hu := hasT_uFun L
  have h1 := (hu.rescale α).mul (hasT_homF hu (2 * (xsOf L T).card) (rootPoly (xsOf L T) ^ 2))
  have h2 := hasT_homF hu (2 * (xsOf L T).card + 1) (veluNum L.g₂ L.g₃ (xsOf L T))
  rw [← h1.2, ← h2.2]
  refine taylorRing.2.2.2 _ _ ((h1.1.frequently_eq_iff_eventually_eq h2.1).1 ?_)
  refine Filter.Eventually.frequently ?_
  filter_upwards [eventually_notMem L hα] with z hz
  obtain ⟨hz0, hzα⟩ := hz
  have hx := xs_notMem L hs hT hzα
  have hd : (rootPoly (xsOf L T) ^ 2).natDegree ≤ 2 * (xsOf L T).card := by
    rw [(rootPoly_monic (xsOf L T)).natDegree_pow, rootPoly_natDegree]
  rw [homF_eq hd (uFun_eq L hz0), homF_eq (veluNum_natDegree_le _ _ _) (uFun_eq L hz0),
    uFun_eq L (mul_ne_zero hα hz0), veluNum_eval _ _ _ hx, ← velu_fun L α T hα hs hT z hzα,
    Polynomial.eval_pow]
  ring

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

variable {K : Type} [Field K] (U : PowerSeries K)

theorem homS_add (m : ℕ) (P Q : K[X]) : homS U m (P + Q) = homS U m P + homS U m Q := by
  simp only [homS, coeff_add, map_add, add_mul, Finset.sum_add_distrib]

theorem homS_sub (m : ℕ) (P Q : K[X]) : homS U m (P - Q) = homS U m P - homS U m Q := by
  simp only [homS, coeff_sub, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem homS_zero (m : ℕ) : homS U m (0 : K[X]) = 0 := by
  simp [homS]

theorem homS_sum {ι : Type} (s : Finset ι) (m : ℕ) (f : ι → K[X]) :
    homS U m (∑ i ∈ s, f i) = ∑ i ∈ s, homS U m (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [homS_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, homS_add, ih]

theorem homS_monomial (m i : ℕ) (hi : i ≤ m) (a : K) :
    homS U m (monomial i a) = PowerSeries.C a * U ^ i * PowerSeries.X ^ (2 * (m - i)) := by
  unfold homS
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [coeff_monomial, if_neg (Ne.symm hb)]
    simp
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hi)) h

theorem homS_mul (m n : ℕ) (P Q : K[X]) (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n) :
    homS U (m + n) (P * Q) = homS U m P * homS U n Q := by
  have eP : P = ∑ i ∈ Finset.range (m + 1), monomial i (P.coeff i) :=
    P.as_sum_range' (m + 1) (Nat.lt_succ_of_le hP)
  have eQ : Q = ∑ j ∈ Finset.range (n + 1), monomial j (Q.coeff j) :=
    Q.as_sum_range' (n + 1) (Nat.lt_succ_of_le hQ)
  have e : P * Q = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      monomial (i + j) (P.coeff i * Q.coeff j) := by
    conv_lhs => rw [eP, eQ]
    rw [Finset.sum_mul_sum]
    simp only [monomial_mul_monomial]
  rw [e, homS_sum]
  simp only [homS_sum]
  unfold homS
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hj' : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have := homS_monomial U (m + n) (i + j) (by omega) (P.coeff i * Q.coeff j)
  unfold homS at this
  rw [this]
  have h2 : 2 * (m + n - (i + j)) = 2 * (m - i) + 2 * (n - j) := by omega
  rw [h2, pow_add, pow_add, map_mul]
  ring

theorem homS_eq_zero (hU : PowerSeries.constantCoeff U = 1) (m : ℕ) (P : K[X]) (hP : P.natDegree ≤ m)
    (h : homS U m P = 0) : P = 0 := by
  have h1 : PowerSeries.coeff (2 * (m - P.natDegree)) (homS U m P) = P.leadingCoeff := by
    unfold homS
    rw [map_sum, Finset.sum_eq_single P.natDegree]
    · rw [PowerSeries.coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        map_mul, map_pow, hU]
      simp
    · intro b hb hne
      have hb' : b ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [PowerSeries.coeff_mul_X_pow', if_neg (by omega)]
      · rw [coeff_eq_zero_of_natDegree_lt hgt]
        simp
    · intro hh
      exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hP)) hh
  rw [h, map_zero] at h1
  exact leadingCoeff_eq_zero.1 h1.symm

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

section Proj

variable {E : Type} [Field E]

def serMap (ψ : E →+ E) (S : PowerSeries E) : PowerSeries E :=
  PowerSeries.mk fun n => ψ (PowerSeries.coeff n S)

def polMap (ψ : E →+ E) (m : ℕ) (Q : E[X]) : E[X] :=
  ∑ i ∈ Finset.range (m + 1), monomial i (ψ (Q.coeff i))

theorem coeff_serMap (ψ : E →+ E) (S : PowerSeries E) (n : ℕ) :
    PowerSeries.coeff n (serMap ψ S) = ψ (PowerSeries.coeff n S) := by
  simp [serMap]

theorem serMap_sum (ψ : E →+ E) {ι : Type} (s : Finset ι) (f : ι → PowerSeries E) :
    serMap ψ (∑ i ∈ s, f i) = ∑ i ∈ s, serMap ψ (f i) := by
  ext n
  simp [coeff_serMap, map_sum]

theorem coeff_polMap (ψ : E →+ E) (m : ℕ) (Q : E[X]) (i : ℕ) :
    (polMap ψ m Q).coeff i = if i ≤ m then ψ (Q.coeff i) else 0 := by
  simp only [polMap, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range (m + 1)) i]
  simp

theorem natDegree_polMap_le (ψ : E →+ E) (m : ℕ) (Q : E[X]) : (polMap ψ m Q).natDegree ≤ m := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  rw [coeff_polMap, if_neg (by omega)]

variable (k : Subfield E)

theorem coeff_mem_mul {S T : PowerSeries E} (hS : ∀ n, PowerSeries.coeff n S ∈ k)
    (hT : ∀ n, PowerSeries.coeff n T ∈ k) : ∀ n, PowerSeries.coeff n (S * T) ∈ k := by
  intro n
  rw [PowerSeries.coeff_mul]
  exact sum_mem fun p _ => mul_mem (hS _) (hT _)

theorem coeff_mem_one : ∀ n, PowerSeries.coeff n (1 : PowerSeries E) ∈ k := by
  intro n
  rw [PowerSeries.coeff_one]
  split_ifs
  · exact one_mem k
  · exact zero_mem k

theorem coeff_mem_pow {S : PowerSeries E} (hS : ∀ n, PowerSeries.coeff n S ∈ k) (i : ℕ) :
    ∀ n, PowerSeries.coeff n (S ^ i) ∈ k := by
  induction i with
  | zero => simpa using coeff_mem_one k
  | succ i ih => rw [pow_succ]; exact coeff_mem_mul k ih hS

theorem coeff_mem_X : ∀ n, PowerSeries.coeff n (PowerSeries.X : PowerSeries E) ∈ k := by
  intro n
  rw [PowerSeries.coeff_X]
  split_ifs
  · exact one_mem k
  · exact zero_mem k

variable {k}

theorem serMap_mul (ψ : E →+ E) (hψ : ∀ c ∈ k, ∀ x, ψ (c * x) = c * ψ x) {W : PowerSeries E}
    (hW : ∀ n, PowerSeries.coeff n W ∈ k) (S : PowerSeries E) :
    serMap ψ (W * S) = W * serMap ψ S := by
  ext n
  rw [coeff_serMap, PowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hψ _ (hW _), coeff_serMap]

theorem serMap_C (ψ : E →+ E) (q : E) : serMap ψ (PowerSeries.C q) = PowerSeries.C (ψ q) := by
  ext n
  rw [coeff_serMap, PowerSeries.coeff_C, PowerSeries.coeff_C]
  split_ifs
  · rfl
  · exact map_zero ψ

theorem serMap_homS (ψ : E →+ E) (hψ : ∀ c ∈ k, ∀ x, ψ (c * x) = c * ψ x) {U : PowerSeries E}
    (hU : ∀ n, PowerSeries.coeff n U ∈ k) (m : ℕ) (Q : E[X]) :
    serMap ψ (homS U m Q) = homS U m (polMap ψ m Q) := by
  unfold homS
  rw [serMap_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hW : ∀ n, PowerSeries.coeff n (U ^ i * PowerSeries.X ^ (2 * (m - i))) ∈ k :=
    coeff_mem_mul k (coeff_mem_pow k hU i) (coeff_mem_pow k (coeff_mem_X k) _)
  rw [coeff_polMap, if_pos hi', mul_assoc, mul_assoc, mul_comm (PowerSeries.C (Q.coeff i)),
    serMap_mul ψ hψ hW, serMap_C, mul_comm]

theorem exists_proj (k : Subfield E) : ∃ ψ : E →+ E, (∀ c ∈ k, ∀ x, ψ (c * x) = c * ψ x) ∧
    (∀ x, ψ x ∈ k) ∧ ψ 1 = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k E)
    (LinearMap.ker_eq_bot.mpr (algebraMap k E).injective)
  refine ⟨(k.subtype : k →+ E).comp g.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro c hc x
    have := g.map_smul (⟨c, hc⟩ : k) x
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe]
    have h2 : (⟨c, hc⟩ : k) • x = c * x := rfl
    rw [← h2, this]
    rfl
  · intro x
    exact (g x).2
  · have := LinearMap.congr_fun hg 1
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply, map_one, LinearMap.id_apply] at this
    simp [this]

end Proj

theorem proj_trick {E : Type} [Field E] (k : Subfield E) (U V : PowerSeries E)
    (hU : ∀ n, PowerSeries.coeff n U ∈ k) (hV : ∀ n, PowerSeries.coeff n V ∈ k)
    (hU0 : PowerSeries.constantCoeff U = 1) (A B : E[X]) (N : ℕ) (hA : A.natDegree ≤ N + 1)
    (hB : B.Monic) (hBd : B.natDegree = N) (hc : IsCoprime A B)
    (h : V * homS U N B = homS U (N + 1) A) : ∀ i, B.coeff i ∈ k := by
  obtain ⟨ψ, hψ, hψk, hψ1⟩ := exists_proj k
  set A' := polMap ψ (N + 1) A with hA'
  set B' := polMap ψ N B with hB'
  have hA'd : A'.natDegree ≤ N + 1 := natDegree_polMap_le ψ _ A
  have hB'd : B'.natDegree ≤ N := natDegree_polMap_le ψ _ B
  have h' : V * homS U N B' = homS U (N + 1) A' := by
    rw [hA', hB', ← serMap_homS ψ hψ hU, ← serMap_homS ψ hψ hU, ← serMap_mul ψ hψ hV, h]
  have hBN : B'.coeff N = 1 := by
    rw [hB', coeff_polMap, if_pos le_rfl, ← hBd, hB.coeff_natDegree, hψ1]
  have hB'deg : B'.natDegree = N := by
    refine le_antisymm hB'd (le_natDegree_of_ne_zero ?_)
    rw [hBN]; exact one_ne_zero
  have hB'm : B'.Monic := by
    rw [Monic, leadingCoeff, hB'deg, hBN]
  have hcross : A * B' = A' * B := by
    have h0 : homS U (N + 1 + N) (A * B' - A' * B) = 0 := by
      rw [homS_sub, homS_mul U _ _ _ _ hA hB'd, homS_mul U _ _ _ _ hA'd hBd.le, ← h, ← h']
      ring
    have hdeg : (A * B' - A' * B).natDegree ≤ N + 1 + N := by
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact natDegree_mul_le.trans (add_le_add hA hB'd)
      · exact natDegree_mul_le.trans (add_le_add hA'd hBd.le)
    exact sub_eq_zero.mp (homS_eq_zero U hU0 _ _ hdeg h0)
  have hdvd : B ∣ B' := by
    refine hc.symm.dvd_of_dvd_mul_left ?_
    rw [hcross]
    exact dvd_mul_left _ _
  have heq : B = B' :=
    (eq_of_monic_of_dvd_of_natDegree_le hB hB'm hdvd (by rw [hB'deg, hBd])).symm
  intro i
  rw [heq, hB', coeff_polMap]
  split_ifs
  · exact hψk _
  · exact zero_mem k

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

theorem sqrt_poly {E : Type} [Field E] [CharZero E] (k : Subfield E) (h : E[X]) (hm : h.Monic)
    (hk : ∀ i, (h ^ 2).coeff i ∈ k) : ∀ i, h.coeff i ∈ k := by
  have key : ∀ m i : ℕ, h.natDegree ≤ i + m → h.coeff i ∈ k := by
    intro m
    induction m with
    | zero =>
      intro i hi
      rcases Nat.eq_or_lt_of_le (by simpa using hi : h.natDegree ≤ i) with h1 | h1
      · rw [← h1, hm.coeff_natDegree]; exact k.one_mem
      · rw [coeff_eq_zero_of_natDegree_lt h1]; exact k.zero_mem
    | succ m ih =>
      intro i hi
      by_cases h0 : h.natDegree ≤ i + m
      · exact ih i h0
      have hin : i < h.natDegree := by omega
      set n := h.natDegree with hn
      have hmem : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal (i + n),
          h.coeff x.1 * h.coeff x.2 - (if x = (i, n) then h.coeff i else 0)
            - (if x = (n, i) then h.coeff i else 0) ∈ k := by
        rintro ⟨a, b⟩ hx
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        simp only at hx
        by_cases ha : a = i
        · have hb : b = n := by omega
          subst ha; subst hb
          have hne : ¬ ((a, h.natDegree) = (h.natDegree, a)) := by
            intro he
            have := (Prod.mk.injEq _ _ _ _ ▸ he : a = h.natDegree ∧ h.natDegree = a).1
            omega
          rw [if_pos rfl, if_neg hne, hm.coeff_natDegree]
          simp [k.zero_mem]
        by_cases ha' : a = n
        · have hb : b = i := by omega
          subst hb
          rw [ha']
          have hne : ¬ ((n, b) = (b, n)) := by
            intro he
            have := (Prod.mk.injEq _ _ _ _ ▸ he : n = b ∧ b = n).1
            omega
          rw [if_neg hne, if_pos rfl, hn, hm.coeff_natDegree]
          simp [k.zero_mem]
        have hne1 : ¬ ((a, b) = (i, n)) := fun he => ha (congrArg Prod.fst he)
        have hne2 : ¬ ((a, b) = (n, i)) := fun he => ha' (congrArg Prod.fst he)
        rw [if_neg hne1, if_neg hne2, sub_zero, sub_zero]
        rcases lt_or_gt_of_ne ha with h1 | h1
        · have : n < b := by omega
          show h.coeff a * h.coeff b ∈ k
          rw [coeff_eq_zero_of_natDegree_lt this, mul_zero]; exact k.zero_mem
        · rcases lt_or_gt_of_ne ha' with h2 | h2
          · exact k.mul_mem (ih a (by omega)) (ih b (by omega))
          · show h.coeff a * h.coeff b ∈ k
            rw [coeff_eq_zero_of_natDegree_lt h2, zero_mul]; exact k.zero_mem
      have hsum := k.sum_mem hmem
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← coeff_mul, ← pow_two,
        Finset.sum_ite_eq', Finset.sum_ite_eq',
        if_pos (by simp),
        if_pos (by simp [add_comm])] at hsum
      have h2 : (2 : E) * h.coeff i ∈ k := by
        have := k.sub_mem (hk (i + n)) hsum
        have e : (h ^ 2).coeff (i + n) - ((h ^ 2).coeff (i + n) - h.coeff i - h.coeff i)
            = 2 * h.coeff i := by ring
        rwa [e] at this
      have h2k : (2 : E) ∈ k := by
        have := k.add_mem k.one_mem k.one_mem
        rwa [one_add_one_eq_two] at this
      have := k.mul_mem (k.inv_mem h2k) h2
      rwa [← mul_assoc, inv_mul_cancel₀ (two_ne_zero), one_mul] at this
  intro i
  exact key h.natDegree i (by omega)

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

theorem wpNum_coeff_mem (k : Subfield ℂ) {g2 g3 : ℂ} (h2 : g2 ∈ k) (h3 : g3 ∈ k) (n : ℕ) :
    PowerSeries.coeff n (wpNum g2 g3) ∈ k := by
  have h := (seriesMap k ℂ k.subtype ⟨g2, h2⟩ ⟨g3, h3⟩ 0 0).1
  have h' : wpNum g2 g3 = PowerSeries.map k.subtype (wpNum (⟨g2, h2⟩ : k) ⟨g3, h3⟩) := h.symm
  rw [h', PowerSeries.coeff_map]
  exact (PowerSeries.coeff n (wpNum (⟨g2, h2⟩ : k) ⟨g3, h3⟩)).2

theorem kerPoly_mem (L : PeriodPair) (α : ℂ) (T : Finset ℂ) (hα : α ≠ 0) (hs : MulStable L α)
    (hT : IsHalfReps L α T) (k : Subfield ℂ) (h2 : L.g₂ ∈ k) (h3 : L.g₃ ∈ k) (hk : α ∈ k) :
    ∀ i, (rootPoly (xsOf L T)).coeff i ∈ k := by
  apply sqrt_poly k _ (rootPoly_monic _)
  refine proj_trick k (wpNum L.g₂ L.g₃) (PowerSeries.rescale α (wpNum L.g₂ L.g₃))
    (wpNum_coeff_mem k h2 h3) ?_ ?_ (veluNum L.g₂ L.g₃ (xsOf L T)) (rootPoly (xsOf L T) ^ 2)
    (2 * (xsOf L T).card) (veluNum_natDegree_le _ _ _) ((rootPoly_monic _).pow 2) ?_
    (veluNum_coprime _ _ _ fun x hx => hT.fW_ne hx) (velu_series L α T hα hs hT)
  · intro n
    rw [PowerSeries.coeff_rescale]
    exact k.mul_mem (k.pow_mem hk n) (wpNum_coeff_mem k h2 h3 n)
  · simp [wpNum]
  · rw [(rootPoly_monic _).natDegree_pow, rootPoly_natDegree]

theorem prod_mem_of_rootPoly {E : Type} [Field E] (k : Subfield E) (xs : Finset E)
    (h : ∀ i, (rootPoly xs).coeff i ∈ k) : ∏ x ∈ xs, x ∈ k := by
  have h0 : (rootPoly xs).coeff 0 = (-1) ^ xs.card * ∏ x ∈ xs, x := by
    rw [Polynomial.coeff_zero_eq_eval_zero, rootPoly, Polynomial.eval_prod]
    simp only [eval_sub, eval_X, eval_C, zero_sub]
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun x _ => (neg_one_mul x).symm
  have h1 : ∏ x ∈ xs, x = (-1) ^ xs.card * (rootPoly xs).coeff 0 := by
    rw [h0, ← mul_assoc, ← mul_pow]
    simp
  rw [h1]
  exact k.mul_mem (k.pow_mem (k.neg_mem k.one_mem) _) (h 0)

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem sqD_eq (d r : ℕ) :
    (r : ℂ) + redSqD d = (((r : ℤ) - 1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * omegaK d := by
  unfold redSqD
  push_cast
  ring

theorem sqD_normSq (d r : ℕ) : Complex.normSq ((r : ℂ) + redSqD d) = ((r ^ 2 + d : ℕ) : ℝ) := by
  unfold redSqD omegaK
  have h : (r : ℂ) + (2 * ((1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2) - 1)
      = ⟨(r : ℝ), Real.sqrt d⟩ := by
    apply Complex.ext <;> simp <;> ring
  rw [h, Complex.normSq_mk, Real.mul_self_sqrt (Nat.cast_nonneg d)]
  push_cast
  ring

theorem sqD_mulStable (d : ℕ) (L : PeriodPair) (hCM : HasCMBy d L) (r : ℕ) : MulStable L ((r : ℂ) + redSqD d) := by
  rw [sqD_eq]
  exact (hasCMByStable d L hCM _ _).1

theorem kerProdAt_of_norm (d : ℕ) (L : PeriodPair) (hCM : HasCMBy d L) (l e r : ℕ) (hodd : Odd (r ^ 2 + d))
    (hl : ¬ l ∣ r ^ 2 + d) (he : ¬ e ∣ r ^ 2 + d) (he' : ¬ e ∣ (r ^ 2 + d - 1) / 2) :
    KerProdAt d L l e := by
  have hN := sqD_normSq d r
  have hs := sqD_mulStable d L hCM r
  have hα : (r : ℂ) + redSqD d ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hN
    have h1 : r ^ 2 + d = 0 := by exact_mod_cast hN.symm
    rw [h1] at hodd
    exact absurd hodd (by decide)
  obtain ⟨T, hT⟩ := halfReps_exist L _ hα hs _ hN hodd
  have hcard : 2 * T.card + 1 = r ^ 2 + d := by
    have h1 := hT.card hα hs
    rw [hN] at h1
    exact_mod_cast h1
  have hcard' : T.card = (r ^ 2 + d - 1) / 2 := by omega
  refine ⟨r ^ 2 + d, T, hl, he, by rw [hcard']; exact he', ?_, ?_⟩
  · intro z hz
    exact ⟨hT.notMem hz, ker_norm hs hN (hT.1 z hz).1⟩
  · intro k h2 h3 hk
    have hαk : (r : ℂ) + redSqD d ∈ k := by
      unfold redSqD
      exact k.add_mem (natCast_mem k r)
        (k.sub_mem (k.mul_mem (by exact_mod_cast natCast_mem k 2) hk) k.one_mem)
    have h4 := prod_mem_of_rootPoly k (xsOf L T) (kerPoly_mem L _ T hα hs hT k h2 h3 hαk)
    unfold xsOf at h4
    rwa [Finset.prod_image (fun a ha b hb hab => hT.injOn ha hb hab)] at h4

theorem kerProd_prin (d : ℕ) (L : PeriodPair) (hd4 : d % 4 = 3) (hCM : HasCMBy d L) (l : ℕ) (hl : l.Prime)
    (h5 : 5 ≤ l) (hld : ¬ l ∣ d) (e : ℕ) (he : e = 2 ∨ e = 3 ∧ ¬ 3 ∣ d) : KerProdAt d L l e := by
  rcases he with rfl | ⟨rfl, h3⟩
  · refine kerProdAt_of_norm d L hCM l 2 0 ?_ ?_ ?_ ?_
    · rw [Nat.odd_iff]; omega
    · simpa using hld
    · omega
    · omega
  · have hmod : d % 3 = 1 ∨ d % 3 = 2 := by omega
    rcases hmod with h1 | h2
    · by_cases hl2 : l ∣ 2 ^ 2 + d
      · have hl4 : ¬ l ∣ 4 ^ 2 + d := by
          intro h
          have h12 : l ∣ 12 := by
            have := Nat.dvd_sub h hl2
            have e12 : 4 ^ 2 + d - (2 ^ 2 + d) = 12 := by omega
            rwa [e12] at this
          have hle : l ≤ 12 := Nat.le_of_dvd (by norm_num) h12
          interval_cases l <;> omega
        refine kerProdAt_of_norm d L hCM l 3 4 ?_ hl4 ?_ ?_
        · rw [Nat.odd_iff]; omega
        · omega
        · omega
      · refine kerProdAt_of_norm d L hCM l 3 2 ?_ hl2 ?_ ?_
        · rw [Nat.odd_iff]; omega
        · omega
        · omega
    · refine kerProdAt_of_norm d L hCM l 3 0 ?_ ?_ ?_ ?_
      · rw [Nat.odd_iff]; omega
      · simpa using hld
      · omega
      · omega

end ReciprocityTheory.ChartRestriction.L1
end
end

section
namespace ReciprocityTheory.ChartRestriction.L1

open scoped NumberTheorySymbols

theorem prime_choice_class (d : ℕ) (hsq : Squarefree d) (hd4 : d % 4 = 3) (h3 : 3 ∣ d) (hd3 : d ≠ 3) :
    ∃ a : ℕ, a % 3 = 2 ∧ J((a : ℤ) | d) = 1 := by
  obtain ⟨d', rfl⟩ := h3
  have hd'4 : d' % 4 = 1 := by omega
  have hd'1 : d' ≠ 1 := by
    rintro rfl
    exact hd3 rfl
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hd'1
  have hq2 : q ≠ 2 := by
    rintro rfl
    obtain ⟨t, ht⟩ := hqd
    omega
  haveI := Fact.mk hq
  obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare (F := ZMod q) (by rw [ZMod.ringChar_zmod_n]; exact hq2)
  obtain ⟨d'', rfl⟩ := hqd
  have hd''0 : d'' ≠ 0 := by
    rintro rfl
    simp at hd4
  haveI : NeZero d'' := ⟨hd''0⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hcop1 : Nat.Coprime q d'' := by
    refine (Nat.Prime.coprime_iff_not_dvd hq).mpr ?_
    rintro ⟨e, rfl⟩
    exact absurd (Nat.isUnit_iff.mp (hsq q ⟨3 * e, by ring⟩)) hq.one_lt.ne'
  have hcop2 : Nat.Coprime 3 (q * d'') := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_
    rintro ⟨e, he⟩
    exact absurd (Nat.isUnit_iff.mp (hsq 3 ⟨e, by rw [he]; ring⟩)) (by norm_num)

  obtain ⟨b, hb1, hb2⟩ := Nat.chineseRemainder hcop1 c.val 1
  obtain ⟨a, ha1, ha2⟩ := Nat.chineseRemainder hcop2 2 b
  refine ⟨a, ?_, ?_⟩
  · unfold Nat.ModEq at ha1
    omega
  have hmq : a % q = c.val % q := (ha2.of_mul_right d'').trans hb1
  have hmd : a % d'' = 1 % d'' := (ha2.of_mul_left q).trans hb2
  have hm3 : a % 3 = 2 := by
    unfold Nat.ModEq at ha1
    omega
  have hJ3 : J((a : ℤ) | 3) = -1 := by
    rw [jacobiSym.mod_left]
    have : (a : ℤ) % ((3 : ℕ) : ℤ) = 2 := by omega
    rw [this]
    norm_num
  have hJq : J((a : ℤ) | q) = -1 := by
    have : (a : ℤ) % (q : ℤ) = (c.val : ℤ) % (q : ℤ) := by exact_mod_cast hmq
    rw [jacobiSym.mod_left, this, ← jacobiSym.mod_left, ← jacobiSym.legendreSym.to_jacobiSym,
      legendreSym.eq_neg_one_iff]
    simpa using hc
  have hJd : J((a : ℤ) | d'') = 1 := by
    have : (a : ℤ) % (d'' : ℤ) = ((1 : ℕ) : ℤ) % (d'' : ℤ) := by exact_mod_cast hmd
    rw [jacobiSym.mod_left, this, ← jacobiSym.mod_left, Nat.cast_one, jacobiSym.one_left]
  rw [jacobiSym.mul_right, jacobiSym.mul_right, hJ3, hJq, hJd]
  norm_num

theorem prime_choice_recip (d p : ℕ) (hd4 : d % 4 = 3) (hp : Odd p) :
    J(-(d : ℤ) | p) = J((p : ℤ) | d) := by
  have hd : Odd d := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.neg _ hp]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hp) with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h hd]
  · rw [ZMod.χ₄_nat_three_mod_four h, jacobiSym.quadratic_reciprocity_three_mod_four hd4 h]
    ring

theorem prime_choice_lift (d p s : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hd0 : 0 < d) (hdp : d < p)
    (hs : p ∣ s ^ 2 + d) : ∃ r : ℕ, Even r ∧ p ∣ r ^ 2 + d ∧ ¬ p ^ 2 ∣ r ^ 2 + d := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨r0, hr0e, hr0⟩ : ∃ r0 : ℕ, Even r0 ∧ p ∣ r0 ^ 2 + d := by
    rcases Nat.even_or_odd s with he | ho
    · exact ⟨s, he, hs⟩
    · refine ⟨s + p, ho.add_odd hpodd, ?_⟩
      have e : (s + p) ^ 2 + d = (s ^ 2 + d) + p * (2 * s + p) := by ring
      rw [e]
      exact dvd_add hs (dvd_mul_right _ _)
  have hndvd : ¬ p ∣ r0 := by
    intro h
    have h2 : p ∣ r0 ^ 2 := dvd_pow h two_ne_zero
    have hpd : p ∣ d := (Nat.dvd_add_right h2).mp hr0
    have := Nat.le_of_dvd hd0 hpd
    omega
  by_cases hsq : p ^ 2 ∣ r0 ^ 2 + d
  ·
    refine ⟨r0 + 2 * p, hr0e.add (even_two_mul p), ?_, ?_⟩
    · have e : (r0 + 2 * p) ^ 2 + d = (r0 ^ 2 + d) + p * (4 * r0 + 4 * p) := by ring
      rw [e]
      exact dvd_add hr0 (dvd_mul_right _ _)
    · intro h
      have e : (r0 + 2 * p) ^ 2 + d = (r0 ^ 2 + d) + p ^ 2 * 4 + p * (4 * r0) := by ring
      rw [e] at h
      have h1 : p ^ 2 ∣ p * (4 * r0) := (Nat.dvd_add_right (dvd_add hsq (dvd_mul_right _ _))).mp h
      rw [pow_two] at h1
      have h2 : p ∣ 4 * r0 := Nat.dvd_of_mul_dvd_mul_left hp.pos h1
      rcases (Nat.Prime.dvd_mul hp).mp h2 with h4 | h4
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h4)))
      · exact hndvd h4
  · exact ⟨r0, hr0e, hr0, hsq⟩

theorem prime_choice (d b : ℕ) (hsq : Squarefree d) (hd4 : d % 4 = 3) (h3 : 3 ∣ d) (hd3 : d ≠ 3) :
    ∃ p r : ℕ, p.Prime ∧ b < p ∧ d < p ∧ p % 3 = 2 ∧ Even r ∧ p ∣ r ^ 2 + d ∧ ¬ p ^ 2 ∣ r ^ 2 + d := by
  obtain ⟨a, ha3, ha⟩ := prime_choice_class d hsq hd4 h3 hd3
  have hd0 : d ≠ 0 := by omega
  haveI : NeZero d := ⟨hd0⟩
  have hunit : IsUnit (a : ZMod d) := by
    rw [ZMod.isUnit_iff_coprime]
    by_contra hnc
    have h0 : J((a : ℤ) | d) = 0 := jacobiSym.eq_zero_iff.mpr ⟨hd0, by simpa [Int.gcd_natCast_natCast] using hnc⟩
    rw [ha] at h0
    exact one_ne_zero h0
  obtain ⟨p, hpgt, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit (b + d)
  have hpd : p % d = a % d := (ZMod.natCast_eq_natCast_iff' p a d).mp hpa
  have hp3 : p % 3 = 2 := by
    rw [← Nat.mod_mod_of_dvd p h3, hpd, Nat.mod_mod_of_dvd a h3, ha3]
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hmod : (p : ℤ) % (d : ℤ) = (a : ℤ) % (d : ℤ) := by exact_mod_cast hpd
  have hJ : J(-(d : ℤ) | p) = 1 := by
    rw [prime_choice_recip d p hd4 hpodd, jacobiSym.mod_left, hmod, ← jacobiSym.mod_left, ha]
  haveI := Fact.mk hp
  have hne : (((-(d : ℤ)) : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    have h1 : (d : ZMod p) = 0 := by
      push_cast at h0
      simpa using h0
    have := Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff d p).mp h1)
    omega
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff p hne] at hJ
  obtain ⟨x, hx⟩ := hJ
  have hs : p ∣ x.val ^ 2 + d := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast at hx ⊢
    rw [ZMod.natCast_zmod_val]
    linear_combination -hx
  obtain ⟨r, hr1, hr2, hr3⟩ := prime_choice_lift d p x.val hp (by omega) (by omega) (by omega) hs
  exact ⟨p, r, hp, by omega, by omega, hp3, hr1, hr2, hr3⟩

end ReciprocityTheory.ChartRestriction.L1
end

section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

namespace CardG

theorem card_line {F : Type} [Field F] [Fintype F] (u v : F) (h : u ≠ 0 ∨ v ≠ 0) :
    (Finset.univ.filter (fun w : F × F => u * w.1 + v * w.2 = 0)).card = Fintype.card F := by
  rcases h with h | h
  · have : Finset.univ.filter (fun w : F × F => u * w.1 + v * w.2 = 0)
        = Finset.univ.image (fun t : F => (-(v * t) / u, t)) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
      constructor
      · intro e
        refine ⟨y, ?_, rfl⟩
        field_simp
        linear_combination -e
      · rintro ⟨t, e, rfl⟩
        rw [← e]; field_simp; ring
    rw [this, Finset.card_image_of_injective _ (fun s t e => (Prod.mk.inj e).2), Finset.card_univ]
  · have : Finset.univ.filter (fun w : F × F => u * w.1 + v * w.2 = 0)
        = Finset.univ.image (fun t : F => (t, -(u * t) / v)) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
      constructor
      · intro e
        refine ⟨x, rfl, ?_⟩
        field_simp
        linear_combination -e
      · rintro ⟨t, rfl, e⟩
        rw [← e]; field_simp; ring
    rw [this, Finset.card_image_of_injective _ (fun s t e => (Prod.mk.inj e).1), Finset.card_univ]

theorem card_ker {F : Type} [Field F] [Fintype F] (a b c d : F) (hdet : a * d - b * c = 0)
    (hne : ¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0)) :
    (Finset.univ.filter (fun w : F × F => a * w.1 + b * w.2 = 0 ∧ c * w.1 + d * w.2 = 0)).card
      = Fintype.card F := by
  by_cases hab : a ≠ 0 ∨ b ≠ 0
  · rw [← card_line a b hab]
    congr 1
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun e => e.1, fun e => ⟨e, ?_⟩⟩
    rcases hab with h | h
    · apply mul_left_cancel₀ h
      linear_combination c * e + y * hdet
    · apply mul_left_cancel₀ h
      linear_combination d * e - x * hdet
  · push Not at hab
    obtain ⟨ha, hb⟩ := hab
    have hcd : c ≠ 0 ∨ d ≠ 0 := by
      by_contra hcd
      push Not at hcd
      exact hne ⟨ha, hb, hcd.1, hcd.2⟩
    rw [← card_line c d hcd]
    congr 1
    ext ⟨x, y⟩
    simp [ha, hb]

theorem coord_unique (L : PeriodPair) {m n m' n' : ℤ}
    (h : (m : ℂ) * L.ω₁ + n * L.ω₂ = m' * L.ω₁ + n' * L.ω₂) : m = m' ∧ n = n' := by
  have hi := LinearIndependent.pair_iff.mp L.indep ((m - m' : ℤ) : ℝ) ((n - n' : ℤ) : ℝ) (by
    simp only [Complex.real_smul]; push_cast; linear_combination h)
  constructor
  · have := hi.1
    have h2 : m - m' = 0 := by exact_mod_cast this
    omega
  · have := hi.2
    have h2 : n - n' = 0 := by exact_mod_cast this
    omega

theorem mem_iff (L : PeriodPair) (p : ℕ) (hp : p ≠ 0) {z : ℂ} {m n : ℤ}
    (h : (m : ℂ) * L.ω₁ + n * L.ω₂ = p * z) :
    z ∈ L.lattice ↔ (m : ZMod p) = 0 ∧ (n : ZMod p) = 0 := by
  have hpc : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro hz
    obtain ⟨m', n', e⟩ := PeriodPair.mem_lattice.mp hz
    have := coord_unique L (m := m) (n := n) (m' := p * m') (n' := p * n') (by
      rw [h, ← e]; push_cast; ring)
    exact ⟨⟨m', this.1⟩, ⟨n', this.2⟩⟩
  · rintro ⟨⟨m', rfl⟩, ⟨n', rfl⟩⟩
    refine PeriodPair.mem_lattice.mpr ⟨m', n', ?_⟩
    apply mul_left_cancel₀ hpc
    rw [← h]; push_cast; ring

def co (L : PeriodPair) (z : ℂ) : ℤ × ℤ :=
  if h : z ∈ L.lattice then
    ((PeriodPair.mem_lattice.mp h).choose, (PeriodPair.mem_lattice.mp h).choose_spec.choose)
  else 0

theorem co_spec (L : PeriodPair) {z : ℂ} (h : z ∈ L.lattice) :
    ((co L z).1 : ℂ) * L.ω₁ + ((co L z).2 : ℂ) * L.ω₂ = z := by
  rw [co, dif_pos h]
  exact (PeriodPair.mem_lattice.mp h).choose_spec.choose_spec

end CardG

open CardG

theorem card_G (L : PeriodPair) (β : ℂ) (hβ : MulStable L β) (p M : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : Complex.normSq β = ((p * M : ℕ) : ℝ)) (hM : ¬ p ∣ M) (T : Finset ℂ)
    (hT : IsHalfReps L (p : ℂ) T) :
    2 * (T.filter (fun P => β * P ∈ L.lattice)).card + 1 = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨hS1, hS2, hS3⟩, hdisj⟩ := hT.kerReps
  obtain ⟨a, b, c, d, h1, h2, -, hn⟩ := Ker.matrix_data L β hβ
  have hpc : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hdetZ : a * d - b * c = (p : ℤ) * M := by
    have : ((a * d - b * c : ℤ) : ℝ) = (((p : ℤ) * M : ℤ) : ℝ) := by
      rw [← hn, hN]; push_cast; ring
    exact_mod_cast this
  have hdet : (a : ZMod p) * d - b * c = 0 := by
    have := congrArg (fun k : ℤ => (k : ZMod p)) hdetZ
    simpa using this
  have hne : ¬ ((a : ZMod p) = 0 ∧ (b : ZMod p) = 0 ∧ (c : ZMod p) = 0 ∧ (d : ZMod p) = 0) := by
    simp only [ZMod.intCast_zmod_eq_zero_iff_dvd]
    rintro ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩, ⟨d', rfl⟩⟩
    apply hM
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have : (M : ℤ) = p * (a' * d' - b' * c') := by
      apply mul_left_cancel₀ hp0
      rw [← hdetZ]; ring
    exact Int.natCast_dvd_natCast.mp ⟨_, this⟩

  have hmul : ∀ {z : ℂ} {m n : ℤ}, (m : ℂ) * L.ω₁ + n * L.ω₂ = p * z →
      (β * z ∈ L.lattice ↔ (a : ZMod p) * m + b * n = 0 ∧ (c : ZMod p) * m + d * n = 0) := by
    intro z m n e
    have := mem_iff L p hp.ne_zero (z := β * z) (m := a * m + b * n) (n := c * m + d * n) (by
      push_cast
      linear_combination β * e - (m : ℂ) * h1 - (n : ℂ) * h2)
    rw [this]; push_cast; rfl
  set S := T ∪ T.image (fun P => -P) with hSdef
  set K := Finset.univ.filter (fun w : ZMod p × ZMod p =>
    (a : ZMod p) * w.1 + b * w.2 = 0 ∧ (c : ZMod p) * w.1 + d * w.2 = 0) with hK
  have hKcard : K.card = p := by
    have := card_ker (a : ZMod p) b c d hdet hne
    rw [ZMod.card] at this
    rw [hK]
    convert this
  have h0K : (0 : ZMod p × ZMod p) ∈ K := by simp [hK]
  have hcardS : (S.filter (fun P => β * P ∈ L.lattice)).card
      = 2 * (T.filter (fun P => β * P ∈ L.lattice)).card := by
    have himg : (T.image (fun P => -P)).filter (fun P => β * P ∈ L.lattice)
        = (T.filter (fun P => β * P ∈ L.lattice)).image (fun P => -P) := by
      ext Q
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨P, hP, rfl⟩, hQ⟩
        refine ⟨P, ⟨hP, ?_⟩, rfl⟩
        have := neg_mem hQ
        simpa using this
      · rintro ⟨P, ⟨hP, hQ⟩, rfl⟩
        refine ⟨⟨P, hP, rfl⟩, ?_⟩
        have := neg_mem hQ
        simpa using this
    rw [hSdef, Finset.filter_union, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hdisj), himg,
      Finset.card_image_of_injective _ neg_injective]
    ring
  have hbij : (S.filter (fun P => β * P ∈ L.lattice)).card = (K.erase 0).card := by
    apply Finset.card_nbij
      (fun z => (((co L (p * z)).1 : ZMod p), ((co L (p * z)).2 : ZMod p)))
    · intro P hP
      obtain ⟨hPS, hPβ⟩ := Finset.mem_filter.mp hP
      have e := co_spec L (hS1 P hPS).1
      rw [Finset.mem_coe, Finset.mem_erase]
      constructor
      · intro h0
        apply (hS1 P hPS).2
        rw [mem_iff L p hp.ne_zero e]
        exact Prod.mk.inj h0
      · rw [hK, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, (hmul e).mp hPβ⟩
    · intro P hP Q hQ hPQ
      have hPS := (Finset.mem_filter.mp (Finset.mem_coe.mp hP)).1
      have hQS := (Finset.mem_filter.mp (Finset.mem_coe.mp hQ)).1
      have eP := co_spec L (hS1 P hPS).1
      have eQ := co_spec L (hS1 Q hQS).1
      apply hS2 P hPS Q hQS
      rw [mem_iff L p hp.ne_zero (m := (co L (p * P)).1 - (co L (p * Q)).1)
        (n := (co L (p * P)).2 - (co L (p * Q)).2) (by push_cast; linear_combination eP - eQ)]
      obtain ⟨e1, e2⟩ := Prod.mk.inj hPQ
      push_cast
      exact ⟨sub_eq_zero.mpr e1, sub_eq_zero.mpr e2⟩
    · rintro ⟨x, y⟩ hxy
      obtain ⟨hxy0, hxyK⟩ := Finset.mem_erase.mp (Finset.mem_coe.mp hxy)
      obtain ⟨m, rfl⟩ := ZMod.intCast_surjective x
      obtain ⟨n, rfl⟩ := ZMod.intCast_surjective y
      set z : ℂ := ((m : ℂ) * L.ω₁ + n * L.ω₂) / p with hz
      have ez : (m : ℂ) * L.ω₁ + n * L.ω₂ = p * z := by rw [hz]; field_simp
      have hzp : (p : ℂ) * z ∈ L.lattice := PeriodPair.mem_lattice.mpr ⟨m, n, ez⟩
      have hzL : z ∉ L.lattice := by
        rw [mem_iff L p hp.ne_zero ez]
        rintro ⟨e1, e2⟩
        exact hxy0 (by rw [e1, e2]; rfl)
      have hzβ : β * z ∈ L.lattice := (hmul ez).mpr (Finset.mem_filter.mp hxyK).2
      obtain ⟨P, hPS, hzP⟩ := hS3 z hzp hzL
      have eP := co_spec L (hS1 P hPS).1
      refine ⟨P, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hPS, ?_⟩), ?_⟩
      · have : β * P = β * z - β * (z - P) := by ring
        rw [this]
        exact sub_mem hzβ (hβ _ hzP)
      · have := (mem_iff L p hp.ne_zero (m := m - (co L (p * P)).1)
          (n := n - (co L (p * P)).2) (by push_cast; linear_combination ez - eP)).mp hzP
        push_cast at this
        exact Prod.ext (sub_eq_zero.mp this.1).symm (sub_eq_zero.mp this.2).symm
  rw [← hcardS, hbij, Finset.card_erase_of_mem h0K, hKcard]
  have := hp.pos
  omega

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

theorem rootPoly_monic' {E : Type} [Field E] (xs : Finset E) : (rootPoly xs).Monic :=
  monic_prod_of_monic _ _ fun x _ => monic_X_sub_C x

theorem rootPoly_inter_mul_sdiff {E : Type} [Field E] (xs ys : Finset E) :
    rootPoly (xs ∩ ys) * rootPoly (xs \ ys) = rootPoly xs := by
  unfold rootPoly
  rw [← Finset.prod_union (Finset.disjoint_sdiff_inter xs ys).symm, Finset.union_comm,
    Finset.sdiff_union_inter]

theorem rootPoly_isCoprime_of_disjoint {E : Type} [Field E] (xs ys : Finset E) (h : Disjoint xs ys) :
    IsCoprime (rootPoly xs) (rootPoly ys) := by
  unfold rootPoly
  refine IsCoprime.prod_left fun x hx => IsCoprime.prod_right fun y hy => ?_
  refine isCoprime_X_sub_C_of_isUnit_sub ?_
  have hne : x ≠ y := fun e => Finset.disjoint_left.1 h hx (e ▸ hy)
  exact (sub_ne_zero.2 hne).isUnit

theorem exists_poly_map_subfield {E : Type} [Field E] [DecidableEq E] (k : Subfield E) (P : E[X])
    (h : ∀ i, P.coeff i ∈ k) : ∃ p : (k)[X], p.map k.subtype = P := by
  have : P ∈ Polynomial.lifts k.subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, h n⟩, rfl⟩
  exact this

theorem rootPoly_inter_mem {E : Type} [Field E] (k : Subfield E) (xs ys : Finset E)
    (hx : ∀ i, (rootPoly xs).coeff i ∈ k) (hy : ∀ i, (rootPoly ys).coeff i ∈ k) :
    ∀ i, (rootPoly (xs ∩ ys)).coeff i ∈ k := by
  obtain ⟨p, hp⟩ := exists_poly_map_subfield k _ hx
  obtain ⟨q, hq⟩ := exists_poly_map_subfield k _ hy
  set R := rootPoly (xs ∩ ys) with hR
  set g0 := EuclideanDomain.gcd p q with hg0
  set g := g0.map k.subtype with hg
  have hgP : g ∣ rootPoly xs := by
    rw [← hp]; exact Polynomial.map_dvd _ (EuclideanDomain.gcd_dvd_left p q)
  have hgQ : g ∣ rootPoly ys := by
    rw [← hq]; exact Polynomial.map_dvd _ (EuclideanDomain.gcd_dvd_right p q)
  have hA := rootPoly_inter_mul_sdiff xs ys
  have hB := rootPoly_inter_mul_sdiff ys xs
  rw [Finset.inter_comm ys xs] at hB
  have hdisj : Disjoint (xs \ ys) (ys \ xs) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.1 hb).2 (Finset.mem_sdiff.1 ha).1
  obtain ⟨u, v, huv⟩ := rootPoly_isCoprime_of_disjoint _ _ hdisj
  have hgR : g ∣ R := by
    have : R = u * rootPoly xs + v * rootPoly ys := by
      rw [← hA, ← hB]
      linear_combination (-R) * huv
    rw [this]
    exact dvd_add (hgP.mul_left _) (hgQ.mul_left _)
  have hRg : R ∣ g := by
    have e : g = EuclideanDomain.gcd (rootPoly xs) (rootPoly ys) := by
      rw [← hp, ← hq, Polynomial.gcd_map]
    rw [e]
    exact EuclideanDomain.dvd_gcd ⟨_, hA.symm⟩ ⟨_, hB.symm⟩
  have hRm : R.Monic := rootPoly_monic' _
  have hg0' : g ≠ 0 := fun e => hRm.ne_zero (by simpa [e] using hgR)
  have hg00 : g0 ≠ 0 := fun e => hg0' (by rw [hg, e, Polynomial.map_zero])
  have hmon : (g0 * C g0.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hg00
  have hmon' : ((g0 * C g0.leadingCoeff⁻¹).map k.subtype).Monic := hmon.map _
  have hassoc : Associated ((g0 * C g0.leadingCoeff⁻¹).map k.subtype) R := by
    have h1 : Associated g R := associated_of_dvd_dvd hgR hRg
    refine Associated.trans ?_ h1
    rw [Polynomial.map_mul, Polynomial.map_C]
    refine (associated_mul_unit_left g _ ?_).symm.symm
    refine Polynomial.isUnit_C.2 (IsUnit.mk0 _ ?_)
    simpa using hg00
  have heq := eq_of_monic_of_associated hmon' hRm hassoc
  intro i
  rw [← heq, Polynomial.coeff_map]
  exact (((g0 * C g0.leadingCoeff⁻¹).coeff i)).2

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem xsOf_filter (L : PeriodPair) (α β : ℂ) (hα : MulStable L α) (hβ : MulStable L β) (T T' : Finset ℂ)
    (hT : IsHalfReps L α T) (hT' : IsHalfReps L β T') :
    xsOf L (T.filter (fun P => β * P ∈ L.lattice)) = xsOf L T ∩ xsOf L T' := by
  ext x
  simp only [xsOf, Finset.mem_image, Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨P, ⟨hP, hβP⟩, rfl⟩
    refine ⟨⟨P, hP, rfl⟩, ?_⟩
    have := (hT'.mem_xsOf hβ (hT.notMem hP)).2 hβP
    simpa only [xsOf, Finset.mem_image] using this
  · rintro ⟨⟨P, hP, rfl⟩, h2⟩
    refine ⟨P, ⟨hP, ?_⟩, rfl⟩
    refine (hT'.mem_xsOf hβ (hT.notMem hP)).1 ?_
    simpa only [xsOf, Finset.mem_image] using h2

theorem natCast_mulStable (L : PeriodPair) (n : ℕ) : MulStable L (n : ℂ) := by
  intro ω hω
  have := L.lattice.nsmul_mem hω n
  simpa [nsmul_eq_mul] using this

theorem kerProd_ideal (d : ℕ) (L : PeriodPair) (hsq : Squarefree d) (hd4 : d % 4 = 3) (hCM : HasCMBy d L)
    (l : ℕ) (hl : l.Prime) (h3 : 3 ∣ d) (hd3 : d ≠ 3) : KerProdAt d L l 3 := by
  obtain ⟨p, r, hp, hb, -, hp3, hr, hdiv, hndiv⟩ := prime_choice d (l + 3) hsq hd4 h3 hd3
  obtain ⟨M, hM⟩ := hdiv
  have hpM : ¬ p ∣ M := by
    rintro ⟨c, rfl⟩
    exact hndiv ⟨c, by rw [hM]; ring⟩
  have hp2 : p ≠ 2 := by omega
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set β : ℂ := (r : ℂ) + redSqD d with hβdef
  have hβs : MulStable L β := sqD_mulStable d L hCM r
  have hβN : Complex.normSq β = ((p * M : ℕ) : ℝ) := by rw [← hM]; exact sqD_normSq d r
  have hβN' : Complex.normSq β = ((r ^ 2 + d : ℕ) : ℝ) := sqD_normSq d r
  have hps : MulStable L (p : ℂ) := natCast_mulStable L p
  have hpN : Complex.normSq (p : ℂ) = ((p * p : ℕ) : ℝ) := by
    rw [Complex.normSq_natCast]; push_cast; ring
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hdodd : Odd d := by rw [Nat.odd_iff]; omega
  have hNodd : Odd (r ^ 2 + d) := (hr.pow_of_ne_zero two_ne_zero).add_odd hdodd
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hβN'
    have : (r ^ 2 + d : ℕ) = 0 := by exact_mod_cast hβN'.symm
    omega
  obtain ⟨T, hT⟩ := halfReps_exist L (p : ℂ) hp0 hps (p * p) hpN (hpodd.mul hpodd)
  obtain ⟨T', hT'⟩ := halfReps_exist L β hβ0 hβs (r ^ 2 + d) hβN' hNodd
  have hcard := card_G L β hβs p M hp hp2 hβN hpM T hT
  refine ⟨p, T.filter (fun P => β * P ∈ L.lattice), ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rcases (Nat.dvd_prime hp).1 h with h1 | h1
    · exact hl.one_lt.ne' h1
    · omega
  · omega
  · omega
  · intro z hz
    have hz' := (Finset.mem_filter.1 hz).1
    exact ⟨hT.notMem hz', (hT.1 z hz').1⟩
  · intro k h2 h3' hω
    have hpk : (p : ℂ) ∈ k := natCast_mem k p
    have hβk : β ∈ k := by
      rw [hβdef, redSqD]
      exact k.add_mem (natCast_mem k r)
        (k.sub_mem (k.mul_mem (by simp) hω) k.one_mem)
    have h1 := kerPoly_mem L (p : ℂ) T hp0 hps hT k h2 h3' hpk
    have h1' := kerPoly_mem L β T' hβ0 hβs hT' k h2 h3' hβk
    have h4 := prod_mem_of_rootPoly k _ (rootPoly_inter_mem k _ _ h1 h1')
    rw [← xsOf_filter L (p : ℂ) β hps hβs T T' hT hT', xsOf, Finset.prod_image] at h4
    · exact h4
    · intro a ha b hb hab
      exact hT.injOn (Finset.mem_coe.2 (Finset.mem_filter.1 ha).1)
        (Finset.mem_coe.2 (Finset.mem_filter.1 hb).1) hab

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem kerProd (d : ℕ) (L : PeriodPair) (hsq : Squarefree d) (hd4 : d % 4 = 3) (hCM : HasCMBy d L) (l : ℕ)
    (hl : l.Prime) (h5 : 5 ≤ l) (hld : ¬ l ∣ d) (e : ℕ) (he : e = 2 ∨ e = 3 ∧ d ≠ 3) :
    KerProdAt d L l e := by
  rcases he with he | ⟨he, hd3⟩
  · exact kerProd_prin d L hd4 hCM l hl h5 hld e (Or.inl he)
  · by_cases h3 : 3 ∣ d
    · subst he
      exact kerProd_ideal d L hsq hd4 hCM l hl h3 hd3
    · exact kerProd_prin d L hd4 hCM l hl h5 hld e (Or.inr ⟨he, h3⟩)

end ReciprocityTheory.ChartRestriction.L1
end
end
