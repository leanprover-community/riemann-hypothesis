import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrKIsometricAndOneSubSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedAndEventuallySubMemLatStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFontaineThetaOnAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemDeRhamFiltrationOfForallAinfLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsilonRootPowSubZetaExpMemFiltration
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLiftsOfNormLeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicNormZpowSubOnePadicValInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUnitPowSubOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicTowerLevelGeneratorProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntAddFilClosedInDeRhamPeriodRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamElementOfCocycleRecursion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicActionOnRootTower

section
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage.Conv

section General

variable {A : Type*} [CommRing A]

theorem step_mem (I : Ideal A) (φ : A →+* A) (hφ : I.map φ ≤ I) {c : A} (hc : c ∈ I) (n : ℕ)
    {y : A} (hy : y ∈ I ^ n) : c * φ y ∈ I ^ (n + 1) := by
  rw [pow_succ']
  refine Ideal.mul_mem_mul hc ?_
  have h : φ y ∈ (I ^ n).map φ := Ideal.mem_map_of_mem φ hy
  rw [Ideal.map_pow] at h
  exact Ideal.pow_right_mono hφ n h

theorem solve (I : Ideal A) [hI : IsAdicComplete I A] (φ : A →+* A) (hφ : I.map φ ≤ I) {c : A}
    (hc : c ∈ I) (q : A) : ∃ y, y - c * φ y = q := by
  let f : ℕ → A := fun n => (fun z => q + c * φ z)^[n] 0
  have hf : ∀ n, f (n + 1) = q + c * φ (f n) := fun n => Function.iterate_succ_apply' _ _ _
  have h1 : ∀ n, f n - f (n + 1) ∈ I ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := step_mem I φ hφ hc n ih
      rw [hf (n + 1)]
      nth_rewrite 1 [hf n]
      convert this using 1
      rw [map_sub]; ring
  have h2 : ∀ m n, m ≤ n → f m - f n ∈ I ^ m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := add_mem ih (Ideal.pow_le_pow_right hmn (h1 n))
      rwa [sub_add_sub_cancel] at this
  obtain ⟨L, hL⟩ := hI.toIsPrecomplete.prec' f (by
    intro m n hmn
    simp only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    exact h2 m n hmn)
  simp only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem] at hL
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero]
  refine hI.toIsHausdorff.haus' _ fun n => ?_
  simp only [smul_eq_mul, Ideal.mul_top, SModEq.zero]
  refine Ideal.pow_le_pow_right (Nat.le_succ n) ?_
  have := sub_mem (step_mem I φ hφ hc n (hL n)) (hL (n + 1))
  convert this using 1
  rw [hf, map_sub]; ring

theorem geom_mem (p : ℕ) (e : A) :
    ∑ i ∈ Finset.range p, e ^ i ∈ Ideal.span {(p : A), e - 1} := by
  have h : ∑ i ∈ Finset.range p, e ^ i = (p : A) + ∑ i ∈ Finset.range p, (e ^ i - 1) := by
    rw [Finset.sum_sub_distrib]; simp
  rw [h]
  refine add_mem (Ideal.subset_span (by simp)) (Ideal.sum_mem _ fun i _ => ?_)
  obtain ⟨d, hd⟩ : e - 1 ∣ e ^ i - 1 := by simpa using sub_dvd_pow_sub_pow e 1 i
  rw [hd]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

theorem map_le (p : ℕ) (φ : A →+* A) {m c : A} (h : φ m = c * m) :
    (Ideal.span {(p : A), m}).map φ ≤ Ideal.span {(p : A), m} := by
  rw [Ideal.map_span, Ideal.span_le]
  rintro _ ⟨x, rfl | rfl, rfl⟩
  · rw [map_natCast]; exact Ideal.subset_span (by simp)
  · rw [h]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

theorem iterate_mem (I : Ideal A) (φ : A →+* A) (hφ : I.map φ ≤ I) {m c : A} (hc : c ∈ I)
    (h : φ m = c * m) (k : ℕ) : ∃ d ∈ I ^ k, φ^[k] m = d * m := by
  induction k with
  | zero => exact ⟨1, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨d, hd, e⟩ := ih
    refine ⟨c * φ d, step_mem I φ hφ hc k hd, ?_⟩
    rw [Function.iterate_succ_apply', e, map_mul, h]; ring

end General

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem frob_mu : WittVector.frobenius AI.μ =
    (∑ i ∈ Finset.range l, WittVector.teichmuller l AI.ε ^ i) * AI.μ := by
  have h : WittVector.frobenius (WittVector.teichmuller l AI.ε) =
      WittVector.teichmuller l AI.ε ^ l := by
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  rw [LocAinf.μ, map_sub, map_one, h, geom_sum_mul]

theorem mu_not_isUnit : ¬ IsUnit AI.μ := by
  intro h
  obtain ⟨θ, hθ⟩ := exists_isTheta l P AI
  have h0 : θ AI.μ = 0 := (hθ.2.2.2.1 _).2 ⟨AI.π₁, by rw [AI.μ_eq, mul_comm]⟩
  have := h.map θ
  rw [h0] at this
  exact not_isUnit_zero this

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), (∀ q : Ainf l, ∃ y : Ainf l, AI.μ * y - WittVector.frobenius (AI.μ * y) = AI.μ * q) ∧ ∀ M n : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, (WittVector.frobenius : Ainf l →+* Ainf l)^[k] AI.μ ∈ Ideal.span {((l : ℕ) : Ainf l) ^ n, AI.ξ ^ M} := by
  intro l _ P AI
  have hc : ∑ i ∈ Finset.range l, WittVector.teichmuller l AI.ε ^ i ∈
      Ideal.span {((l : ℕ) : Ainf l), AI.μ} := geom_mem l _
  have hφ := map_le l _ (frob_mu AI)
  refine ⟨fun q => ?_, fun M n => ⟨n + M, fun k hk => ?_⟩⟩
  · haveI := (GlobalTheory.Per.AinfComplete.main l AI.μ (mu_not_isUnit AI)).1
    obtain ⟨y, hy⟩ := solve _ _ hφ hc q
    refine ⟨y, ?_⟩
    rw [map_mul, frob_mu, ← hy]; ring
  · obtain ⟨d, hd, e⟩ := iterate_mem _ _ hφ hc (frob_mu AI) k
    rw [e]
    refine Ideal.mul_mem_right _ _ ?_
    have h1 : Ideal.span {((l : ℕ) : Ainf l), AI.μ} ≤ Ideal.span {((l : ℕ) : Ainf l), AI.ξ} := by
      rw [Ideal.span_le]
      rintro x (rfl | rfl)
      · exact Ideal.subset_span (by simp)
      · rw [AI.μ_eq]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    have h2 := Ideal.pow_le_pow_right hk (Ideal.pow_right_mono h1 k hd)
    rw [Ideal.span_insert] at h2
    rw [Ideal.span_insert, ← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
    exact Ideal.sup_pow_add_le_pow_sup_pow h2

end GlobalTheory.ExpImage.Conv
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_mu_frobenius_equation_solvable_and_tendsto : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), (∀ q : Ainf l, ∃ y : Ainf l, AI.μ * y - WittVector.frobenius (AI.μ * y) = AI.μ * q) ∧ ∀ M n : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, (WittVector.frobenius : Ainf l →+* Ainf l)^[k] AI.μ ∈ Ideal.span {((l : ℕ) : Ainf l) ^ n, AI.ξ ^ M} := by
  atlas_forward_decl GlobalTheory.ExpImage.Conv.main
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lifts_of_norm_le_one_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (c : ↥(K0 K)), ‖(c : Om l)‖ ≤ 1 → ∃ w : Ainf l, Lifts AI K w c := by
  first | exact @GlobalTheory.ExpImage.exists_lifts_of_norm_le_one | exact GlobalTheory.ExpImage.exists_lifts_of_norm_le_one | (intros; apply GlobalTheory.ExpImage.exists_lifts_of_norm_le_one <;> assumption)
end

section
section
noncomputable section

namespace GlobalTheory.ExpImage.Tail

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l}

abbrev Fr (l : ℕ) [Fact l.Prime] (n : ℕ) : Ainf l →+* Ainf l :=
  (WittVector.frobenius : Ainf l →+* Ainf l) ^ n

theorem Fr_succ (n : ℕ) (a : Ainf l) : Fr l (n + 1) a = WittVector.frobenius (Fr l n a) := by
  rw [Fr, pow_succ']; rfl

theorem Fr_succ' (n : ℕ) (a : Ainf l) : Fr l (n + 1) a = Fr l n (WittVector.frobenius a) := by
  rw [Fr, pow_succ]; rfl

theorem frob_teich (x : OCb l) :
    WittVector.frobenius (WittVector.teichmuller l x) = WittVector.teichmuller l x ^ l := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]

theorem Fr_teich (n : ℕ) (x : OCb l) :
    Fr l n (WittVector.teichmuller l x) = WittVector.teichmuller l x ^ l ^ n := by
  induction n with
  | zero => simp [Fr]
  | succ n ih => rw [Fr_succ, ih, map_pow, frob_teich, ← pow_mul, pow_succ']

theorem lifts_Fr {w : Ainf l} {c : ↥(K0 K)} (h : Lifts AI K w c) (n : ℕ) :
    Lifts AI K (Fr l n w) ((frK P K ^ n) c) := by
  induction n with
  | zero => simpa [Fr] using h
  | succ n ih =>
    rw [Fr_succ, pow_succ']
    exact ih.frob

theorem lifts_sum {ι : Type} (T : Finset ι) (w : ι → Ainf l) (c : ι → ↥(K0 K))
    (h : ∀ i ∈ T, Lifts AI K (w i) (c i)) : Lifts AI K (∑ i ∈ T, w i) (∑ i ∈ T, c i) := by
  unfold Lifts at h ⊢
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl h

def oK (P : LocPrime l) (K : FinExt l) : ↥(K0 K) →+* P.R.BdR :=
  (oB P).comp (algebraMap ↥(K0 K) (Om l))

theorem oK_apply (c : ↥(K0 K)) : oK P K c = oB P (c : Om l) := rfl

def u (P : LocPrime l) (j : ℕ) : P.R.BdR := qB P ((j.factorial : ℚ_[l])⁻¹) * tD P ^ j

theorem u_mem (j : ℕ) : u P j ∈ FilB P 0 := by
  refine qB_mul_mem _ (FilB_anti ?_ (FilB_pow tD_mem j))
  simp

theorem taylor0 (hT : LocTied l P AI) (m M : ℕ) :
    io AI (WittVector.teichmuller l AI.ε ^ m) - ∑ j ∈ Finset.range M, (m : P.R.BdR) ^ j * u P j ∈
      FilB P (M : ℤ) := by
  have h := GlobalTheory.T.teichmullerEpsilonRoot_pow_sub_zeta_exp_mem_filtration l P AI hT 0 m M
  rw [P.ζQ_zero, one_pow, map_one, one_mul] at h
  convert h using 3 with j hj
  · rfl
  · rw [pow_zero, div_one, div_eq_mul_inv, map_mul, map_pow, map_natCast, u, mul_assoc]

theorem span_mem_Lat {M n : ℕ} {a : Ainf l}
    (ha : a ∈ Ideal.span {((l : ℕ) : Ainf l) ^ n, AI.ξ ^ M}) : io AI a ∈ Lat AI M n := by
  obtain ⟨x, y, rfl⟩ := Ideal.mem_span_pair.mp ha
  refine ⟨x, ?_⟩
  have h := FilB_zero_mul (io_mem AI y) (FilB_pow (io_ξ_mem AI) M)
  rw [mul_one] at h
  convert h using 1
  simp only [map_add, map_mul, map_pow]
  ring

theorem tail (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (K : FinExt l) (ι : Type) (T : Finset ι) (w : ι → Ainf l) (c : ι → ↥(K0 K)) (m : ι → ℕ) (M : ℕ)
    (d : ℕ → ↥(K0 K)) (hM : 1 ≤ M) (hw : ∀ i ∈ T, Lifts AI K (w i) (c i))
    (hd : ∀ j < M, ‖(d j : Om l)‖ ≤ 1 ∧
      d j - (l : ↥(K0 K)) ^ j * frK P K (d j) = ∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j) :
    ∃ y : Ainf l, y - WittVector.frobenius y =
        ∑ i ∈ T, w i * WittVector.teichmuller l AI.ε ^ m i ∧
      io AI y - ∑ j ∈ Finset.range M,
        qB P ((j.factorial : ℚ_[l])⁻¹) * oB P (d j : Om l) * tD P ^ j ∈ FilB P (M : ℤ) := by
  have hD : ∀ j, ∃ D : Ainf l, j < M → Lifts AI K D (d j) := by
    intro j
    by_cases hj : j < M
    · obtain ⟨D, hD⟩ := GlobalTheory.T.exists_lifts_of_norm_le_one_alt l P AI hT K (d j) (hd j hj).1
      exact ⟨D, fun _ => hD⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose D hD using hD
  have h0 : D 0 - WittVector.frobenius (D 0) = ∑ i ∈ T, w i := by
    have h1 := (hD 0 hM).sub (hD 0 hM).frob
    have h2 := (hd 0 hM).2
    simp only [pow_zero, one_mul, mul_one] at h2
    rw [h2] at h1
    exact h1.unique (lifts_sum T w c hw)
  obtain ⟨q, hq⟩ : AI.μ ∣ ∑ i ∈ T, w i * (WittVector.teichmuller l AI.ε ^ m i - 1) := by
    refine Finset.dvd_sum fun i _ => Dvd.dvd.mul_left ?_ _
    have := sub_dvd_pow_sub_pow (WittVector.teichmuller l AI.ε) 1 (m i)
    rwa [one_pow] at this
  obtain ⟨hc1, hc2⟩ := GlobalTheory.T.ainf_mu_frobenius_equation_solvable_and_tendsto l P AI
  obtain ⟨y', hy'⟩ := hc1 q
  have hy : (D 0 + AI.μ * y') - WittVector.frobenius (D 0 + AI.μ * y') =
      ∑ i ∈ T, w i * WittVector.teichmuller l AI.ε ^ m i := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib] at hq
    rw [map_add]
    linear_combination h0 + hy' - hq
  refine ⟨D 0 + AI.μ * y', hy, ?_⟩
  set y := D 0 + AI.μ * y' with hydef
  let E : ℕ → P.R.BdR := fun n => io AI (Fr l n y) -
    ∑ j ∈ Finset.range M, (l : P.R.BdR) ^ (j * n) * oK P K ((frK P K ^ n) (d j)) * u P j
  have hstep : ∀ n, E n - E (n + 1) ∈ FilB P (M : ℤ) := by
    intro n
    have h1 : io AI (Fr l n y) - io AI (Fr l (n + 1) y) =
        ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) *
          io AI (WittVector.teichmuller l AI.ε ^ (m i * l ^ n)) := by
      rw [Fr_succ', ← map_sub, ← map_sub, hy, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_mul, map_mul, (lifts_Fr (hw i hi) n).io_eq, map_pow (Fr l n), Fr_teich, ← pow_mul,
        mul_comm (l ^ n), oK_apply]
    have h2 : ∀ j ∈ Finset.range M,
        (l : P.R.BdR) ^ (j * n) * oK P K ((frK P K ^ n) (d j)) * u P j -
          (l : P.R.BdR) ^ (j * (n + 1)) * oK P K ((frK P K ^ (n + 1)) (d j)) * u P j =
        ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) * (((m i * l ^ n : ℕ) : P.R.BdR) ^ j * u P j) := by
      intro j hj
      have h3 := congrArg (fun x => oK P K ((frK P K ^ n) x)) (hd j (Finset.mem_range.mp hj)).2
      simp only [map_sub, map_mul, map_pow, map_natCast, map_sum] at h3
      have h4 : (frK P K ^ (n + 1)) (d j) = (frK P K ^ n) (frK P K (d j)) := by
        rw [pow_succ]; rfl
      have h5 : ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) * (((m i * l ^ n : ℕ) : P.R.BdR) ^ j * u P j)
          = (l : P.R.BdR) ^ (j * n) * u P j *
            ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) * (m i : P.R.BdR) ^ j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast
        ring
      rw [h4, h5, ← h3]
      ring
    have h6 : E n - E (n + 1) = ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) *
        (io AI (WittVector.teichmuller l AI.ε ^ (m i * l ^ n)) -
          ∑ j ∈ Finset.range M, ((m i * l ^ n : ℕ) : P.R.BdR) ^ j * u P j) := by
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      rw [← h1, Finset.sum_comm, ← Finset.sum_congr rfl h2, Finset.sum_sub_distrib]
      simp only [E]
      ring
    rw [h6]
    refine Submodule.sum_mem _ fun i hi => FilB_zero_mul ?_ (taylor0 hT _ _)
    rw [oK_apply, ← (lifts_Fr (hw i hi) n).io_eq]
    exact io_mem AI _
  have htel : ∀ n, E 0 - E n ∈ FilB P (M : ℤ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := add_mem ih (hstep n)
      rwa [sub_add_sub_cancel] at this
  have hE0 : E 0 ∈ FilB P (M : ℤ) := by
    refine GlobalTheory.T.mem_deRhamFiltration_of_forall_ainfLattice l P AI hT M _ fun r => ?_
    obtain ⟨k₀, hk₀⟩ := hc2 M r
    have hk : ∀ j, ∃ k : ℕ, (l : P.R.BdR) ^ k * u P j ∈ Lat AI M r := fun j =>
      (GlobalTheory.T.bounded_and_eventually_sub_mem_Lat_alt l P AI hT _ (u_mem j) M r).1
    choose k hk using hk
    set n := k₀ + ∑ j ∈ Finset.range M, k j with hn
    have hEn : E n ∈ Lat AI M r := by
      obtain ⟨M', rfl⟩ := Nat.exists_eq_add_of_le' hM
      have e0 : oK P K ((frK P K ^ n) (d 0)) = io AI (Fr l n (D 0)) := by
        rw [oK_apply, (lifts_Fr (hD 0 hM) n).io_eq]
      have e1 : E n = io AI (Fr l n y') * io AI (Fr l n AI.μ) - ∑ j ∈ Finset.range M',
          (l : P.R.BdR) ^ ((j + 1) * n) * oK P K ((frK P K ^ n) (d (j + 1))) * u P (j + 1) := by
        simp only [E, hydef]
        rw [Finset.sum_range_succ', e0]
        simp only [map_add, map_mul, u, zero_mul, pow_zero, Nat.factorial_zero, Nat.cast_one,
          inv_one, map_one]
        ring
      rw [e1]
      refine sub_mem (io_mul_mem_Lat AI _ (span_mem_Lat ?_)) (sum_mem fun j hj => ?_)
      · have := hk₀ n (Nat.le_add_right _ _)
        rwa [← RingHom.coe_pow] at this
      · have hj' : j + 1 < M' + 1 := Nat.succ_lt_succ (Finset.mem_range.mp hj)
        have hle : k (j + 1) ≤ (j + 1) * n := by
          have a1 : k (j + 1) ≤ ∑ j ∈ Finset.range (M' + 1), k j :=
            Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj')
          have a2 : n ≤ (j + 1) * n := Nat.le_mul_of_pos_left _ (Nat.succ_pos j)
          omega
        obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
        have := io_mul_mem_Lat AI (((l : ℕ) : Ainf l) ^ e * Fr l n (D (j + 1))) (hk (j + 1))
        convert this using 1
        rw [he, oK_apply, ← (lifts_Fr (hD _ hj') n).io_eq, map_mul, map_pow, map_natCast]
        ring
    have := add_mem (FilB_le_Lat AI (n := r) (htel n)) hEn
    rwa [sub_add_cancel] at this
  convert hE0 using 1
  simp only [E, Fr, pow_zero, mul_zero, one_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [u, oK_apply, AlgHom.one_apply]
  ring

end GlobalTheory.ExpImage.Tail
end
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_equation_lift_Ainf : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (ι : Type) (T : Finset ι) (w : ι → Ainf l) (c : ι → ↥(K0 K)) (m : ι → ℕ) (M : ℕ) (d : ℕ → ↥(K0 K)), 1 ≤ M → (∀ i ∈ T, Lifts AI K (w i) (c i)) → (∀ j < M, ‖(d j : Om l)‖ ≤ 1 ∧ d j - (l : ↥(K0 K)) ^ j * frK P K (d j) = ∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j) → ∃ y : Ainf l, y - WittVector.frobenius y = ∑ i ∈ T, w i * WittVector.teichmuller l AI.ε ^ m i ∧ io AI y - ∑ j ∈ Finset.range M, qB P ((j.factorial : ℚ_[l])⁻¹) * oB P (d j : Om l) * tD P ^ j ∈ FilB P (M : ℤ) := by
  atlas_forward_decl GlobalTheory.ExpImage.Tail.tail
end

section
section
noncomputable section

namespace GlobalTheory.ExpImage.Expand

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem frob_teich (x : OCb l) :
    WittVector.frobenius (WittVector.teichmuller l x) = WittVector.teichmuller l x ^ l := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]

theorem root_pow (AI : LocAinf l P) (m : ℕ) : AI.εroot m ^ (l ^ m) = AI.ε := by
  induction m with
  | zero => simp [LocAinf.εroot]
  | succ m ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    exact ih

theorem epsT_pow (AI : LocAinf l P) (s : ℕ) :
    epsT AI s ^ (l ^ s) = WittVector.teichmuller l AI.ε := by
  rw [epsT, ← map_pow, root_pow]

theorem lifts_iter {AI : LocAinf l P} {K : FinExt l} {w : Ainf l} {c : ↥(K0 K)}
    (h : Lifts AI K w c) (k : ℕ) :
    Lifts AI K ((WittVector.frobenius : Ainf l → Ainf l)^[k] w) ((frK P K ^ k) c) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ', AlgHom.mul_apply]
    exact ih.frob

theorem qB_eq (z : ℚ_[l]) : qB P z = oB P (algebraMap ℚ_[l] (Om l) z) :=
  IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR z

theorem coeff_eq (K : FinExt l) (s j : ℕ) {ι : Type} (T : Finset ι) (c : ι → ↥(K0 K))
    (m : ι → ℕ) (d : ↥(K0 K)) :
    algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ *
        levSum P K s j T c m d =
      ∑ k ∈ Finset.range s, ∑ i ∈ T, (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) *
          (P.ζQ s ^ (m i * l ^ k) * algebraMap ℚ_[l] (Om l)
            ((((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j / (j.factorial : ℚ_[l]))) +
        algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l])⁻¹) * (d : Om l) := by
  have hl : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hj : (j.factorial : ℚ_[l]) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  rw [levSum, mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j / (j.factorial : ℚ_[l]) =
        ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * ((l : ℚ_[l]) ^ (j * k) * (m i : ℚ_[l]) ^ j) := by
      push_cast
      rw [div_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm k j]
      field_simp
    rw [e, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]
    ring
  · have e : (j.factorial : ℚ_[l])⁻¹ =
        ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * (l : ℚ_[l]) ^ (s * j) := by
      field_simp
    rw [e, map_mul, map_pow, map_natCast, mul_assoc]

theorem expand : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (ι : Type) (T : Finset ι) (w : ι → Ainf l) (c : ι → ↥(K0 K)) (m : ι → ℕ) (M : ℕ) (d : ℕ → ↥(K0 K)), 1 ≤ M → (∀ i ∈ T, Lifts AI K (w i) (c i)) → (∀ j < M, ‖(d j : Om l)‖ ≤ 1 ∧ d j - (l : ↥(K0 K)) ^ j * frK P K (d j) = (frK P K ^ s) (∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j)) → ∃ y : Ainf l, y - WittVector.frobenius y = ∑ i ∈ T, w i * epsT AI s ^ m i ∧ io AI y - ∑ j ∈ Finset.range M, oB P (algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * levSum P K s j T c m (d j)) * tD P ^ j ∈ FilB P (M : ℤ) := by
  intro l _ P AI TT K s ι T w c m M d hM hw hd
  obtain ⟨y₁, h1, h2⟩ := GlobalTheory.T.frobenius_equation_lift_Ainf l P AI TT K ι T
    (fun i => (WittVector.frobenius : Ainf l → Ainf l)^[s] (w i)) (fun i => (frK P K ^ s) (c i)) m M d hM
    (fun i hi => lifts_iter (hw i hi) s) (fun j hj => ⟨(hd j hj).1, by
      rw [(hd j hj).2, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_pow, map_natCast]⟩)
  set H : ℕ → Ainf l := fun k =>
    ∑ i ∈ T, (WittVector.frobenius : Ainf l → Ainf l)^[k] (w i) * epsT AI s ^ (m i * l ^ k) with hH
  have hφ : ∀ k, WittVector.frobenius (H k) = H (k + 1) := by
    intro k
    simp only [hH]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, Function.iterate_succ_apply', epsT, frob_teich, ← pow_mul]
    congr 2
    ring
  have hs : H s = ∑ i ∈ T, (WittVector.frobenius : Ainf l → Ainf l)^[s] (w i) *
      WittVector.teichmuller l AI.ε ^ m i := by
    simp only [hH]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (m i), pow_mul, epsT_pow]
  have h0 : H 0 = ∑ i ∈ T, w i * epsT AI s ^ m i := by simp [hH]
  refine ⟨∑ k ∈ Finset.range s, H k + y₁, ?_, ?_⟩
  · have ht := Finset.sum_range_sub' H s
    rw [Finset.sum_sub_distrib] at ht
    rw [map_add, map_sum, Finset.sum_congr rfl (fun k _ => hφ k), ← h0]
    rw [← hs] at h1
    linear_combination ht + h1
  · have hk : ∑ k ∈ Finset.range s, ∑ i ∈ T, oB P (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) *
        (io AI (epsT AI s ^ (m i * l ^ k)) - oB P (P.ζQ s ^ (m i * l ^ k)) *
          ∑ j ∈ Finset.range M, qB P ((((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j /
            (j.factorial : ℚ_[l])) * tD P ^ j) ∈ FilB P (M : ℤ) := by
      refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun i hi => ?_
      refine FilB_zero_mul ?_ (GlobalTheory.T.teichmullerEpsilonRoot_pow_sub_zeta_exp_mem_filtration l P AI TT s (m i * l ^ k) M)
      rw [← (lifts_iter (hw i hi) k).io_eq]
      exact io_mem AI _
    have e1 : io AI (∑ k ∈ Finset.range s, H k) = ∑ k ∈ Finset.range s, ∑ i ∈ T,
        oB P (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) * io AI (epsT AI s ^ (m i * l ^ k)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hH]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_mul, (lifts_iter (hw i hi) k).io_eq]
    have e2 : ∑ j ∈ Finset.range M, oB P (algebraMap ℚ_[l] (Om l)
          ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * levSum P K s j T c m (d j)) * tD P ^ j =
        ∑ k ∈ Finset.range s, ∑ i ∈ T, oB P (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) *
          (oB P (P.ζQ s ^ (m i * l ^ k)) *
            ∑ j ∈ Finset.range M, qB P ((((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j /
              (j.factorial : ℚ_[l])) * tD P ^ j) +
        ∑ j ∈ Finset.range M, qB P ((j.factorial : ℚ_[l])⁻¹) * oB P (d j : Om l) * tD P ^ j := by
      simp only [coeff_eq, map_add, map_sum, map_mul, ← qB_eq, add_mul, Finset.sum_add_distrib,
        Finset.sum_mul, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have := add_mem hk h2
    rw [map_add, e1, e2]
    convert this using 1
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring

end GlobalTheory.ExpImage.Expand
end
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusSolution_expansion_mod_filtration : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (ι : Type) (T : Finset ι) (w : ι → Ainf l) (c : ι → ↥(K0 K)) (m : ι → ℕ) (M : ℕ) (d : ℕ → ↥(K0 K)), 1 ≤ M → (∀ i ∈ T, Lifts AI K (w i) (c i)) → (∀ j < M, ‖(d j : Om l)‖ ≤ 1 ∧ d j - (l : ↥(K0 K)) ^ j * frK P K (d j) = (frK P K ^ s) (∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j)) → ∃ y : Ainf l, y - WittVector.frobenius y = ∑ i ∈ T, w i * epsT AI s ^ m i ∧ io AI y - ∑ j ∈ Finset.range M, oB P (algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * levSum P K s j T c m (d j)) * tD P ^ j ∈ FilB P (M : ℤ) := by
  atlas_forward_decl GlobalTheory.ExpImage.Expand.expand
end

section
section
noncomputable section

namespace GlobalTheory.ExpImage.IntCoc

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage Filter Topology
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

theorem oB_mem {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (α : Om l) :
    oB P α ∈ FilB P 0 := by
  have hα : IsIntegral ℚ_[l] α := Algebra.IsIntegral.isIntegral α
  obtain ⟨K, hK⟩ : ∃ K : FinExt l, α ∈ K.1 :=
    ⟨⟨IntermediateField.adjoin ℚ_[l] {α}, IntermediateField.adjoin.finiteDimensional hα⟩,
      IntermediateField.mem_adjoin_simple_self _ α⟩
  have h := ((P.PD K).Fil 0).smul_mem (⟨α, hK⟩ : ↥K.1) (P.PD K).one_mem
  rw [Algebra.smul_def, mul_one, IsScalarTower.algebraMap_apply ↥K.1 (Om l) P.R.BdR] at h
  exact (T.fil _ _ _).2 ((T.fil K _ _).1 h)

theorem act_qB (P : LocPrime l) (g : GQ l) (c : ℚ_[l]) : P.actQdR g (qB P c) = qB P c :=
  AlgEquiv.commutes _ c

def tw (LT : LocTheory) (e : ℕ) (σ : GQ l) : ℚ_[l] :=
  (((LT l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l])

def coc (LT : LocTheory) (e : ℕ) (x b : (LT l).R.BdR) (σ : GQ l) : (LT l).R.BdR :=
  qB (LT l) ((logChi LT σ : ℤ_[l]) : ℚ_[l]) * x +
    (qB (LT l) (tw LT e σ) * (LT l).actQdR σ b - b)

variable (LT : LocTheory)

theorem norm_chi (σ : GQ l) : ‖((LT l).χQ σ : ℚ_[l])‖ = 1 :=
  (cyc_basic l _ (LT l).χQ_cyc).1 σ

theorem logChi_coe (σ : GQ l) :
    ((logChi LT σ : ℤ_[l]) : ℚ_[l]) = logZl l ((LT l).χQ σ : ℚ_[l]) := by
  exact congrArg Subtype.val (dif_pos ((GlobalTheory.PadicLogUnits.logZl_hom l).2.2.1 _ (norm_chi LT σ)))

theorem logChi_mul (σ τ : GQ l) : ((logChi LT (σ * τ) : ℤ_[l]) : ℚ_[l]) =
    ((logChi LT σ : ℤ_[l]) : ℚ_[l]) + ((logChi LT τ : ℤ_[l]) : ℚ_[l]) := by
  rw [logChi_coe, logChi_coe, logChi_coe, map_mul, Units.val_mul,
    (GlobalTheory.PadicLogUnits.logZl_hom l).1 _ _ (norm_chi LT σ) (norm_chi LT τ)]

theorem logZl_one : logZl l 1 = 0 := by
  have h := (GlobalTheory.PadicLogUnits.logZl_hom l).1 1 1 norm_one norm_one
  rw [mul_one] at h
  exact left_eq_add.1 h

theorem continuous_logChi : Continuous fun σ : GQ l => ((logChi LT σ : ℤ_[l]) : ℚ_[l]) := by
  simp only [logChi_coe]
  exact (GlobalTheory.PadicLogUnits.logZl_hom l).2.1.comp_continuous (cyc_basic l _ (LT l).χQ_cyc).2.1
    (norm_chi LT)

theorem tw_eq (e : ℕ) (σ : GQ l) : tw LT e σ = (((LT l).χQ σ : ℚ_[l]) ^ e)⁻¹ := by
  simp [tw]

theorem norm_tw (e : ℕ) (σ : GQ l) : ‖tw LT e σ‖ = 1 := by
  simp [tw_eq, norm_chi]

theorem tw_mul (e : ℕ) (σ τ : GQ l) : tw LT e (σ * τ) = tw LT e σ * tw LT e τ := by
  rw [tw, tw, tw, map_mul, mul_zpow, Units.val_mul]

theorem continuous_tw (e : ℕ) : Continuous (tw (l := l) LT e) := by
  have : tw (l := l) LT e = fun σ => (((LT l).χQ σ : ℚ_[l]) ^ e)⁻¹ := funext (tw_eq LT e)
  rw [this]
  exact ((cyc_basic l _ (LT l).χQ_cyc).2.1.pow e).inv₀ fun σ => pow_ne_zero _ (Units.ne_zero _)

theorem tw_act (e : ℕ) (σ : GQ l) (α : Om l) (h : σ α = α) :
    qB (LT l) (tw LT e σ) * (LT l).actQdR σ (oB (LT l) α * tD (LT l) ^ e) =
      oB (LT l) α * tD (LT l) ^ e := by
  have h1 : qB (LT l) (tw LT e σ) * qB (LT l) ((LT l).χQ σ : ℚ_[l]) ^ e = 1 := by
    rw [← map_pow, ← map_mul, tw_eq, inv_mul_cancel₀ (pow_ne_zero _ (Units.ne_zero _)), map_one]
  rw [map_mul, map_pow, act_tD, (LT l).actQdR_Om, h, mul_pow]
  linear_combination (oB (LT l) α * tD (LT l) ^ e) * h1

theorem coc_mul (e : ℕ) (x b : (LT l).R.BdR) (σ τ : GQ l)
    (h : qB (LT l) (tw LT e σ) * (LT l).actQdR σ x = x) :
    coc LT e x b (σ * τ) =
      coc LT e x b σ + qB (LT l) (tw LT e σ) * (LT l).actQdR σ (coc LT e x b τ) := by
  simp only [coc, logChi_mul, tw_mul, map_add, map_mul, map_sub, act_qB, AlgEquiv.mul_apply]
  linear_combination (-qB (LT l) ((logChi LT τ : ℤ_[l]) : ℚ_[l])) * h

theorem small_mul {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {M n k : ℕ} {c : ℚ_[l]}
    {x : P.R.BdR} (hc : ‖c‖ ≤ (l : ℝ) ^ (-(k : ℤ))) (hx : (l : P.R.BdR) ^ k * x ∈ Lat AI M n) :
    qB P c * x ∈ Lat AI M n := by
  have h0 : ((l : ℚ_[l]) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have h1 : ‖c / (l : ℚ_[l]) ^ k‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.2 h0), Padic.norm_p_pow]
    exact hc
  have := qB_mul_mem_Lat AI T ⟨_, h1⟩ hx
  rwa [← mul_assoc, ← map_natCast (qB P), ← map_pow, ← map_mul, div_mul_cancel₀ _ h0] at this

theorem ev_small {f : GQ l → ℚ_[l]} (hf : Continuous f) (h1 : f 1 = 0) (k : ℕ) :
    ∀ᶠ τ in 𝓝 (1 : GQ l), ‖f τ‖ ≤ (l : ℝ) ^ (-(k : ℤ)) := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  refine hf.norm.continuousAt.eventually_le_const ?_
  show ‖f 1‖ < _
  rw [h1, norm_zero]
  exact zpow_pos hl _

theorem coc_small {AI : LocAinf l (LT l)} (T : LocTied l (LT l) AI) (e M n : ℕ)
    {x b : (LT l).R.BdR} (hx : x ∈ FilB (LT l) 0) (hb : b ∈ FilB (LT l) 0) :
    ∀ᶠ τ in 𝓝 (1 : GQ l), coc LT e x b τ ∈ Lat AI M n := by
  obtain ⟨⟨k, hk⟩, -⟩ := GlobalTheory.T.bounded_and_eventually_sub_mem_Lat_alt l _ AI T x hx M n
  obtain ⟨⟨k', hk'⟩, h3⟩ := GlobalTheory.T.bounded_and_eventually_sub_mem_Lat_alt l _ AI T b hb M n
  have h1 := ev_small (continuous_logChi (l := l) LT)
    (by rw [logChi_coe, map_one, Units.val_one, logZl_one]) k
  have h2 := ev_small (f := fun τ : GQ l => tw LT e τ - 1) ((continuous_tw LT e).sub continuous_const)
    (by simp [tw]) k'
  filter_upwards [h1, h2, h3] with τ a1 a2 a3
  have := add_mem (small_mul T a1 hk) (add_mem (small_mul T a2 hk')
    (qB_mul_mem_Lat AI T ⟨_, (norm_tw LT e τ).le⟩ a3))
  convert this using 1
  simp only [coc, map_sub, map_one]
  ring

theorem coc_near {AI : LocAinf l (LT l)} (T : LocTied l (LT l) AI) (e M n : ℕ)
    {x b : (LT l).R.BdR} (hx : x ∈ FilB (LT l) 0) (hb : b ∈ FilB (LT l) 0) (σ : GQ l)
    (h : qB (LT l) (tw LT e σ) * (LT l).actQdR σ x = x) :
    ∀ᶠ τ in 𝓝 σ, coc LT e x b τ - coc LT e x b σ ∈ Lat AI M n := by
  have ht : Tendsto (fun τ : GQ l => σ⁻¹ * τ) (𝓝 σ) (𝓝 1) := by
    have := (continuous_mul_left σ⁻¹).tendsto σ
    rwa [inv_mul_cancel] at this
  filter_upwards [ht.eventually (coc_small LT T e M n hx hb)] with τ hτ
  have h1 := coc_mul LT e x b σ (σ⁻¹ * τ) h
  rw [mul_inv_cancel_left] at h1
  rw [h1, add_sub_cancel_left]
  exact qB_mul_mem_Lat AI T ⟨_, (norm_tw LT e σ).le⟩ (act_mem_Lat AI σ hτ)

theorem fil_mul (e : ℕ) {M : ℤ} {x b : (LT l).R.BdR} {σ τ : GQ l}
    (h : qB (LT l) (tw LT e σ) * (LT l).actQdR σ x = x) {y z : ℚ_[l]}
    (hy : qB (LT l) y - coc LT e x b σ ∈ FilB (LT l) M)
    (hz : qB (LT l) z - coc LT e x b τ ∈ FilB (LT l) M) :
    qB (LT l) (y + tw LT e σ * z) - coc LT e x b (σ * τ) ∈ FilB (LT l) M := by
  have := add_mem hy (qB_mul_mem (tw LT e σ) (act_mem σ hz))
  convert this using 1
  rw [coc_mul LT e x b σ τ h, map_add, map_mul, map_sub, act_qB]
  ring

theorem nearZ_mul (e M : ℕ) {x b : (LT l).R.BdR} {σ τ : GQ l}
    (h : qB (LT l) (tw LT e σ) * (LT l).actQdR σ x = x)
    (hy : NearZ (LT l) M (coc LT e x b σ)) (hz : NearZ (LT l) M (coc LT e x b τ)) :
    NearZ (LT l) M (coc LT e x b (σ * τ)) := by
  obtain ⟨y, hy⟩ := hy
  obtain ⟨z, hz⟩ := hz
  let u : ℤ_[l] := ⟨tw LT e σ, (norm_tw LT e σ).le⟩
  refine ⟨y + u * z, ?_⟩
  rw [PadicInt.coe_add, PadicInt.coe_mul]
  exact fil_mul LT e h hy hz

theorem exists_pow_lt {ε : ℝ} (hε : 0 < ε) : ∃ n : ℕ, (l : ℝ) ^ (-(n : ℤ)) < ε := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl)
  exact ⟨n, by rwa [zpow_neg, zpow_natCast, ← inv_pow]⟩

theorem eq_zero_of_fil {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {M : ℕ}
    (hM : 1 ≤ M) {c : ℚ_[l]} (hc : qB P c ∈ FilB P (M : ℤ)) : c = 0 := by
  by_contra h
  obtain ⟨n, hn⟩ := exists_pow_lt (l := l) (norm_pos_iff.2 h)
  exact absurd (GlobalTheory.T.norm_le_of_qB_mem_Lat_alt l P AI T M n hM c (FilB_le_Lat AI hc)) (not_le.2 hn)

end GlobalTheory.ExpImage.IntCoc

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage Filter Topology IntCoc

theorem integral_cocycle_of_gen : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (g : GQ l), IsGen (LT l).χQ K s g → ∀ α ∈ Ks K s, ∀ b ∈ FilB (LT l) 0, (∀ h ∈ Hinf K, NearZ (LT l) (e + 1) ((LT l).actQdR h b - b)) → NearZ (LT l) (e + 1) (qB (LT l) ((logChi LT g : ℤ_[l]) : ℚ_[l]) * (oB (LT l) α * tD (LT l) ^ e) + (qB (LT l) (((LT l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (LT l).actQdR g b - b)) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (α) := by
  intro LT l _ AI T K s hs e g hg α hα b hb hH hgz
  set x := oB (LT l) α * tD (LT l) ^ e with hxdef
  have hM : 1 ≤ e + 1 := Nat.le_add_left 1 e
  have hx : x ∈ FilB (LT l) 0 :=
    FilB_zero_mul (oB_mem T α) (FilB_anti (by positivity) (FilB_pow tD_mem e))
  have hfix : ∀ σ ∈ Gj K s, qB (LT l) (tw LT e σ) * (LT l).actQdR σ x = x :=
    fun σ hσ => tw_act LT e σ α (hσ ⟨α, hα⟩)
  have hχ : IsCyc (LT l).χQ := (LT l).χQ_cyc
  have hact : IsActC AI.actC := ⟨AI.actC_ext, AI.actC_norm⟩
  have hH1 : ∀ h ∈ Hinf K, (LT l).χQ h = 1 := fun h hh =>
    ((cyc_basic l _ hχ).2.2 K h (Hinf_le_fix hh)).2.1 hh
  have hHG : ∀ h ∈ Hinf K, h ∈ Gj K s := fun h hh =>
    (((cyc_basic l _ hχ).2.2 K h (Hinf_le_fix hh)).1 s).2 (by
      rw [hH1 h hh, Units.val_one, sub_self, norm_zero]; positivity)
  have hHz : ∀ h ∈ Hinf K, NearZ (LT l) (e + 1) (coc LT e x b h) := fun h hh => by
    have := hH h hh
    convert this using 1
    simp [coc, tw, logChi_coe, hH1 h hh, logZl_one]
  have hpow : ∀ a : ℕ, NearZ (LT l) (e + 1) (coc LT e x b (g ^ a)) := fun a => by
    induction a with
    | zero => rw [pow_zero]; exact hHz 1 (one_mem _)
    | succ a ih => rw [pow_succ']; exact nearZ_mul LT e _ (hfix g hg.1) hgz ih
  have hall : ∀ σ ∈ Gj K s, NearZ (LT l) (e + 1) (coc LT e x b σ) := fun σ hσ => by
    refine GlobalTheory.T.padicInt_add_fil_closed_in_deRhamPeriodRing l _ AI T _ hM _ fun n => ?_
    have hcl := ((gen_dense l _ _ hact hχ K s hs).2 g hg).2.2 hσ
    obtain ⟨τ, ⟨h, hh, a, rfl⟩, hτ⟩ := ((mem_closure_iff_frequently.1 hcl).and_eventually
      (coc_near LT T e (e + 1) n hx hb σ (hfix σ hσ))).exists
    obtain ⟨z, hz⟩ := nearZ_mul LT e _ (hfix h (hHG h hh)) (hHz h hh) (hpow a)
    refine ⟨z, ?_⟩
    have := add_mem (FilB_le_Lat AI (n := n) hz) hτ
    rwa [sub_add_sub_cancel] at this
  choose! z hz using hall
  refine ⟨fun σ => (z σ : ℚ_[l]), fun σ _ => (z σ).2, ⟨?_, fun _ _ => Set.mem_univ _, ?_⟩, b, hb, ?_⟩
  · intro σ hσ
    rw [ContinuousWithinAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt (l := l) hε
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
      (coc_near LT T e (e + 1) n hx hb σ (hfix σ hσ))] with τ hτ h1
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (GlobalTheory.T.norm_le_of_qB_mem_Lat_alt l _ AI T _ n hM _ ?_) hn
    have := sub_mem (add_mem (FilB_le_Lat AI (n := n) (hz τ hτ)) h1) (FilB_le_Lat AI (hz σ hσ))
    convert this using 1
    rw [map_sub]
    ring
  · intro σ hσ τ hτ
    rw [← sub_eq_zero]
    refine eq_zero_of_fil T hM ?_
    have := sub_mem (hz _ (mul_mem hσ hτ)) (fil_mul LT e (hfix σ hσ) (hz σ hσ) (hz τ hτ))
    rwa [sub_sub_sub_cancel_right, ← map_sub] at this
  · intro σ hσ
    have := hz σ hσ
    rw [coc, ← sub_sub, Nat.cast_add_one] at this
    exact this

end GlobalTheory.ExpImage
end
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_cocycle_of_generator_and_fixing : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (g : GQ l), IsGen (LT l).χQ K s g → ∀ α ∈ Ks K s, ∀ b ∈ FilB (LT l) 0, (∀ h ∈ Hinf K, NearZ (LT l) (e + 1) ((LT l).actQdR h b - b)) → NearZ (LT l) (e + 1) (qB (LT l) ((logChi LT g : ℤ_[l]) : ℚ_[l]) * (oB (LT l) α * tD (LT l) ^ e) + (qB (LT l) (((LT l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (LT l).actQdR g b - b)) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (α) := by
  atlas_forward_decl GlobalTheory.ExpImage.integral_cocycle_of_gen
end

section
section
noncomputable section

namespace GlobalTheory.ExpImage.LowTerms

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem oB_mem_zero {AI : LocAinf l P} (T : LocTied l P AI) (x : Om l) : oB P x ∈ FilB P 0 := by
  obtain ⟨y, h1, -⟩ := T.om x
  exact (GlobalTheory.ThetaTie.fil_zero T _).2 ⟨y, h1.symm⟩

theorem tD_pow_mem_zero (j : ℕ) : tD P ^ j ∈ FilB P 0 :=
  FilB_anti (by simp) (FilB_pow (tD_mem (P := P)) j)

theorem act_term (g : GQ l) (c : ℚ_[l]) {x : Om l} (hx : g x = x) (j : ℕ) :
    P.actQdR g (qB P c * (oB P x * tD P ^ j)) =
      qB P (c * (P.χQ g : ℚ_[l]) ^ j) * (oB P x * tD P ^ j) := by
  rw [map_mul, map_mul, map_pow, act_tD, P.actQdR_Om, hx, AlgEquiv.commutes, map_mul, map_pow,
    mul_pow]
  ring

theorem Ks_le_Kinf (K : FinExt l) (s : ℕ) : Ks K s ≤ Kinf K :=
  sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ fun _ hx => Exists.intro s hx) _

theorem expStar_of_sum : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (g : GQ l), IsGen (LT l).χQ K s g → ∀ w : ℕ → Om l, (∀ j, w j ∈ Ks K s) → ∀ b ∈ FilB (LT l) 0, (∀ h ∈ Hinf K, NearZ (LT l) (e + 1) ((LT l).actQdR h b - b)) → NearZ (LT l) (e + 1) (∑ j ∈ Finset.range (e + 1), oB (LT l) (w j) * tD (LT l) ^ j + (qB (LT l) (((LT l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (LT l).actQdR g b - b)) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) (logZl l ((LT l).χQ g : ℚ_[l]))⁻¹ * w e) := by
  intro LT l _ AI T K s hs e g hg w hw b hb hH hN
  have hχ : IsCyc (LT l).χQ := (LT l).χQ_cyc
  obtain ⟨hn, -, hker⟩ := GlobalTheory.Cyc.cyc_basic l _ hχ
  obtain ⟨-, -, hint, hlog⟩ := GlobalTheory.PadicLogUnits.logZl_hom l
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  set u : ℚ_[l] := ((LT l).χQ g : ℚ_[l]) with hu
  have hu0 : u ≠ 0 := Units.ne_zero _
  have hL : logZl l u ≠ 0 := by
    rw [← norm_pos_iff, hlog s hs.1 hs.2 u hg.2.le, hg.2]
    exact zpow_pos hl _
  have hLc : ((logChi LT g : ℤ_[l]) : ℚ_[l]) = logZl l u :=
    congrArg Subtype.val (dif_pos (hint _ (hn g)))
  have hne : ∀ j ∈ Finset.range e, u ^ ((j : ℤ) - e) - 1 ≠ 0 := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    rw [← norm_pos_iff, GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one l s hs u hg.2 _ (by omega)]
    exact zpow_pos hl _
  set c : ℕ → ℚ_[l] := fun j => (u ^ ((j : ℤ) - e) - 1)⁻¹ with hc
  set S : (LT l).R.BdR :=
    ∑ j ∈ Finset.range e, qB (LT l) (c j) * (oB (LT l) (w j) * tD (LT l) ^ j) with hS
  have hS0 : S ∈ FilB (LT l) 0 :=
    Submodule.sum_mem _ fun j _ =>
      qB_mul_mem _ (FilB_zero_mul (oB_mem_zero T _) (tD_pow_mem_zero j))
  have hSH : ∀ h ∈ Hinf K, (LT l).actQdR h S = S := by
    intro h hh
    have h1 : (LT l).χQ h = 1 := (hker K h (Hinf_le_fix hh)).2.1 hh
    rw [hS, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [act_term h _ (hh ⟨w j, Ks_le_Kinf K s (hw j)⟩), h1]
    simp
  have hSg : qB (LT l) (((LT l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (LT l).actQdR g S - S =
      ∑ j ∈ Finset.range e, oB (LT l) (w j) * tD (LT l) ^ j := by
    rw [hS, map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [act_term g _ (hg.1 ⟨w j, hw j⟩), ← mul_assoc, ← map_mul, ← sub_mul, ← map_sub]
    have : (((LT l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (c j * u ^ j) - c j = 1 := by
      have h2 : u ^ ((j : ℤ) - e) = u ^ (-(e : ℤ)) * u ^ j := by
        rw [sub_eq_neg_add, zpow_add₀ hu0, zpow_natCast]
      have h3 : (u ^ ((j : ℤ) - e) - 1) * c j = 1 := mul_inv_cancel₀ (hne j hj)
      rw [Units.val_zpow_eq_zpow_val, ← hu]
      rw [h2] at h3
      linear_combination h3
    rw [this, map_one, one_mul]
  refine GlobalTheory.T.integral_cocycle_of_generator_and_fixing LT l AI T K s hs e g hg _
    (mul_mem (IntermediateField.algebraMap_mem _ _) (hw e)) (b + S) (add_mem hb hS0)
    (fun h hh => ?_) ?_
  · have := hH h hh
    rwa [map_add, hSH h hh, add_sub_add_right_eq_sub]
  · have h4 : qB (LT l) (logZl l u) * oB (LT l) (algebraMap ℚ_[l] (Om l) (logZl l u)⁻¹) = 1 := by
      rw [← IsScalarTower.algebraMap_apply, ← map_mul, mul_inv_cancel₀ hL, map_one]
    convert hN using 1
    rw [hLc, Finset.sum_range_succ, ← hSg, map_add, map_mul]
    linear_combination (oB (LT l) (w e) * tD (LT l) ^ e) * h4

end GlobalTheory.ExpImage.LowTerms
end
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expStar_of_low_terms_removed : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (g : GQ l), IsGen (LT l).χQ K s g → ∀ w : ℕ → Om l, (∀ j, w j ∈ Ks K s) → ∀ b ∈ FilB (LT l) 0, (∀ h ∈ Hinf K, NearZ (LT l) (e + 1) ((LT l).actQdR h b - b)) → NearZ (LT l) (e + 1) (∑ j ∈ Finset.range (e + 1), oB (LT l) (w j) * tD (LT l) ^ j + (qB (LT l) (((LT l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (LT l).actQdR g b - b)) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) (logZl l ((LT l).χQ g : ℚ_[l]))⁻¹ * w e) := by
  atlas_forward_decl GlobalTheory.ExpImage.LowTerms.expStar_of_sum
end

section
namespace GlobalTheory.PowerSeriesAdicEval

open PowerSeries

theorem exists_algHom_apply_X {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal A) [h : IsAdicComplete I A] {y : A} (hy : y ∈ I) :
    ∃ ev : PowerSeries R →ₐ[R] A, ev PowerSeries.X = y := by
  let _ : WithIdeal A := ⟨I⟩
  let _ : UniformSpace R := ⊥
  have _ : DiscreteUniformity R := ⟨rfl⟩
  have hI : IsAdic I := rfl
  obtain ⟨h1, h2⟩ := hI.isAdicComplete_iff.mp h
  have ha : PowerSeries.HasEval y := WithIdeal.isTopologicallyNilpotent_of_mem hy
  have _ : ContinuousSMul R A := DiscreteTopology.instContinuousSMul R A
  refine ⟨PowerSeries.aeval ha, ?_⟩
  rw [← Polynomial.coe_X, PowerSeries.aeval_coe, Polynomial.aeval_X]

theorem algHom_coe {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (f : PowerSeries R →ₐ[R] A) (p : Polynomial R) :
    f (p : PowerSeries R) = Polynomial.aeval (f PowerSeries.X) p := by
  have : f.comp (Polynomial.coeToPowerSeries.algHom R) = Polynomial.aeval (f PowerSeries.X) := by
    apply Polynomial.algHom_ext
    simp
  have h := DFunLike.congr_fun this p
  simpa using h

theorem algHom_ext_of_isHausdorff {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal A) [h : IsHausdorff I A] (f f' : PowerSeries R →ₐ[R] A)
    (hX : f PowerSeries.X = f' PowerSeries.X) (hy : f PowerSeries.X ∈ I) : f = f' := by
  apply AlgHom.ext
  intro F
  rw [← sub_eq_zero]
  refine IsHausdorff.haus h _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  have e := F.eq_X_pow_mul_shift_add_trunc n
  set G : PowerSeries R := PowerSeries.mk fun i => PowerSeries.coeff (i + n) F
  have : f F - f' F = f PowerSeries.X ^ n * (f G - f' G) := by
    conv_lhs => rw [e]
    rw [map_add, map_add, map_mul, map_mul, map_pow, map_pow, algHom_coe, algHom_coe, ← hX]
    ring
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hy n)

theorem exists_eval_and_unique :
    ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (y : A),
      IsAdicComplete (Ideal.span {y}) A →
        (∃ ev : PowerSeries R →ₐ[R] A, ev PowerSeries.X = y) ∧
          ∀ f f' : PowerSeries R →ₐ[R] A, f PowerSeries.X = f' PowerSeries.X →
            y ∣ f PowerSeries.X → f = f' := by
  intro R A _ _ _ y h
  exact ⟨exists_algHom_apply_X (Ideal.span {y}) (Ideal.mem_span_singleton_self y),
    fun f f' h1 h2 => algHom_ext_of_isHausdorff (Ideal.span {y}) f f' h1
      (Ideal.mem_span_singleton.2 h2)⟩

end GlobalTheory.PowerSeriesAdicEval
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

open PowerSeries

namespace GlobalTheory.ExpImage

noncomputable def triSol {R : Type*} [CommRing R] (M : ℕ → ℕ → R) (g : ℕ → R) (n : ℕ) : R :=
  Ring.inverse (M n n) * (g n - ∑ i : Fin n, M n i * triSol M g i)
decreasing_by exact i.2

open PowerSeries in
private lemma constantCoeff_coeff_one_one_add_X_pow {R : Type*} [CommRing R] (N : ℕ) :
    constantCoeff ((1 + X : R⟦X⟧) ^ N) = 1 ∧ coeff 1 ((1 + X : R⟦X⟧) ^ N) = N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e : (1 + X : R⟦X⟧) ^ (N + 1) = (1 + X) ^ N + X * (1 + X) ^ N := by ring
    have h1 : coeff 1 (X * (1 + X : R⟦X⟧) ^ N) = constantCoeff ((1 + X : R⟦X⟧) ^ N) := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
    refine ⟨?_, ?_⟩
    · rw [e, map_add, ih.1, map_mul, constantCoeff_X, zero_mul, add_zero]
    · rw [e, map_add, ih.2, h1, ih.1]
      push_cast
      ring

open PowerSeries in
private lemma isUnit_padicInt_of_not_dvd' {l : ℕ} [Fact l.Prime] (z : ℤ_[l]) (hz : ¬ (l : ℤ_[l]) ∣ z) :
    IsUnit z :=
  PadicInt.isUnit_iff.2 (le_antisymm (PadicInt.norm_le_one z)
    (not_lt.1 fun h => hz ((PadicInt.norm_lt_one_iff_dvd z).1 h)))

open PowerSeries in
private lemma toZMod_eq_zero_iff_dvd {l : ℕ} [Fact l.Prime] (z : ℤ_[l]) :
    PadicInt.toZMod z = 0 ↔ (l : ℤ_[l]) ∣ z := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

open PowerSeries in
private lemma three_le_prime_pow {l s : ℕ} (hl : l.Prime) (hs : 1 ≤ s) (h2 : l = 2 → 2 ≤ s) :
    3 ≤ l ^ s := by
  rcases hl.eq_two_or_odd' with rfl | hodd
  · calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (h2 rfl)
  · have h3 : 3 ≤ l := by
      have := hl.two_le
      rcases hodd with ⟨r, hr⟩
      omega
    calc 3 ≤ l := h3
      _ = l ^ 1 := (pow_one l).symm
      _ ≤ l ^ s := Nat.pow_le_pow_right hl.pos hs

open PowerSeries in
private lemma coeff_one_mul_one_add_X_sq_mul_pow {R : Type*} [CommRing R] (f w : R⟦X⟧) (n : ℕ) :
    coeff 1 (f * (1 + X ^ 2 * w) ^ n) = coeff 1 f := by
  obtain ⟨q, hq⟩ : X ^ 2 ∣ (1 + X ^ 2 * w) ^ n - 1 ^ n := by
    have := sub_dvd_pow_sub_pow (1 + X ^ 2 * w) 1 n
    rw [add_sub_cancel_left] at this
    exact (dvd_mul_right _ _).trans this
  have e : f * (1 + X ^ 2 * w) ^ n = f + X ^ 2 * (f * q) := by
    rw [one_pow] at hq
    linear_combination f * hq
  rw [e, map_add, X_pow_dvd_iff.1 (dvd_mul_right _ _) 1 (by norm_num), add_zero]

open PowerSeries in
private lemma sum_mul_triSol_eq {R : Type*} [CommRing R] (M : ℕ → ℕ → R)
    (g : ℕ → R) (n : ℕ) (hn : IsUnit (M n n)) :
    ∑ i ∈ Finset.range (n + 1), M n i * _root_.GlobalTheory.ExpImage.triSol M g i = g n := by
  rw [Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range (fun i => M n i *
    _root_.GlobalTheory.ExpImage.triSol M g i) n]
  conv_lhs => rw [_root_.GlobalTheory.ExpImage.triSol]
  rw [← mul_assoc, Ring.mul_inverse_cancel _ hn, one_mul]
  ring

open PowerSeries in

theorem _root_.GlobalTheory.ExpImage.solve_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (s : ℕ), _root_.GlobalTheory.Cyc.Lev l s →
    ∀ (m : ℕ), ¬ l ∣ m → ∀ U : ℤ_[l], (l : ℤ_[l]) ^ s ∣ U - 1 →
    ∀ (γ : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] PowerSeries ℤ_[l]) (v : PowerSeries ℤ_[l]),
    PowerSeries.X * v = (1 + PowerSeries.X) ^ (1 + l ^ s) - 1 →
    γ PowerSeries.X = PowerSeries.X * v → ∀ (k : ℕ) (F : PowerSeries ℤ_[l]),
    ∃ p F' : PowerSeries ℤ_[l], PowerSeries.C U * (1 + PowerSeries.X) ^ m * γ p - v ^ k * p =
      v ^ k * (PowerSeries.X * F - (l : PowerSeries ℤ_[l]) ^ s * F') := by
  intro l _ s hs m hm U hU γ v hv hγ k F
  obtain ⟨hs1, hs2⟩ : 1 ≤ s ∧ (l = 2 → 2 ≤ s) := by
    unfold _root_.GlobalTheory.Cyc.Lev at hs
    exact hs
  have hlp : l.Prime := Fact.out

  let T : PowerSeries ℤ_[l] →ₗ[ℤ_[l]] PowerSeries ℤ_[l] :=
    LinearMap.mulLeft ℤ_[l] (C U * (1 + X) ^ m) ∘ₗ γ.toLinearMap -
      LinearMap.mulLeft ℤ_[l] (v ^ k)
  have hT : ∀ f, T f = C U * (1 + X) ^ m * γ f - v ^ k * f := fun f => rfl
  have hTX : ∀ i : ℕ, T (X ^ i) = (C U * (1 + X) ^ m * v ^ i - v ^ k) * X ^ i := by
    intro i
    rw [hT, map_pow, hγ]
    ring

  have hloc : ∀ f g : PowerSeries ℤ_[l], ∀ j : ℕ, (∀ i < j + 1, coeff i f = coeff i g) →
      coeff j (T f) = coeff j (T g) := by
    intro f g j h
    obtain ⟨q, hq⟩ : X ^ (j + 1) ∣ f - g :=
      X_pow_dvd_iff.2 fun i hi => by rw [map_sub, h i hi, sub_self]
    have e : T f - T g = X ^ (j + 1) * (C U * (1 + X) ^ m * v ^ (j + 1) * γ q - v ^ k * q) := by
      rw [← map_sub, hq, hT, map_mul, map_pow, hγ]
      ring
    have h2 : coeff j (T f - T g) = 0 := by
      rw [e]
      exact X_pow_dvd_iff.1 (dvd_mul_right _ _) j (Nat.lt_succ_self j)
    rwa [map_sub, sub_eq_zero] at h2
  have hsum : ∀ (c : ℕ → ℤ_[l]) (j : ℕ),
      coeff j (T (mk c)) = ∑ i ∈ Finset.range (j + 1), c i * coeff j (T (X ^ i)) := by
    intro c j
    rw [hloc (mk c) (∑ i ∈ Finset.range (j + 1), c i • X ^ i) j]
    · simp [map_sum, map_smul]
    · intro i hi
      simp [coeff_mk, map_sum, coeff_X_pow, Finset.mem_range.2 hi]

  have hv0 : constantCoeff v = 1 + (l : ℤ_[l]) ^ s := by
    have h := congrArg (coeff 1) hv
    rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply,
      map_sub, (constantCoeff_coeff_one_one_add_X_pow (R := ℤ_[l]) (1 + l ^ s)).2] at h
    rw [h]
    simp
  have hunitv : IsUnit v := by
    rw [isUnit_iff_constantCoeff, hv0]
    refine isUnit_padicInt_of_not_dvd' _ fun hd => ?_
    have h1 : (l : ℤ_[l]) ∣ 1 :=
      (dvd_add_left (dvd_pow_self (l : ℤ_[l]) (by omega : s ≠ 0))).1 hd
    have hn := PadicInt.isUnit_iff.1 (isUnit_of_dvd_one h1)
    have h2 := (PadicInt.norm_lt_one_iff_dvd (l : ℤ_[l])).2 dvd_rfl
    linarith

  have hdiag : ∀ i : ℕ, (l : ℤ_[l]) ^ s ∣ coeff i (T (X ^ i)) := by
    intro i
    have e := coeff_mul_X_pow (C U * (1 + X) ^ m * v ^ i - v ^ k) i 0
    rw [zero_add] at e
    rw [hTX, e, coeff_zero_eq_constantCoeff_apply]
    simp only [map_sub, map_mul, map_pow, constantCoeff_C, hv0,
      (constantCoeff_coeff_one_one_add_X_pow (R := ℤ_[l]) m).1, mul_one]
    have ha : ∀ n : ℕ, (l : ℤ_[l]) ^ s ∣ (1 + (l : ℤ_[l]) ^ s) ^ n - 1 := fun n => by
      simpa using sub_dvd_pow_sub_pow (1 + (l : ℤ_[l]) ^ s) 1 n
    have e2 : U * (1 + (l : ℤ_[l]) ^ s) ^ i - (1 + (l : ℤ_[l]) ^ s) ^ k =
        (U - 1) * (1 + (l : ℤ_[l]) ^ s) ^ i + ((1 + (l : ℤ_[l]) ^ s) ^ i - 1) -
          ((1 + (l : ℤ_[l]) ^ s) ^ k - 1) := by ring
    rw [e2]
    exact dvd_sub (dvd_add (dvd_mul_of_dvd_left hU _) (ha i)) (ha k)

  have hsub : ∀ n : ℕ, IsUnit (coeff (n + 1) (T (X ^ n))) := by
    intro n
    refine isUnit_padicInt_of_not_dvd' _ fun hd => hm ?_
    rw [← toZMod_eq_zero_iff_dvd] at hd
    haveI : CharP (PowerSeries (ZMod l)) l :=
      charP_of_injective_ringHom (PowerSeries.C_injective (R := ZMod l)) l
    obtain ⟨t, ht⟩ : ∃ t, l ^ s = t + 3 := ⟨l ^ s - 3, by have := three_le_prime_pow hlp hs1 hs2; omega⟩
    have hvb : PowerSeries.map PadicInt.toZMod v = 1 + X ^ 2 * (X ^ t * (1 + X)) := by
      apply X_mul_cancel
      have h := congrArg (PowerSeries.map (PadicInt.toZMod (p := l))) hv
      simp only [map_mul, map_sub, map_pow, map_add, map_one, PowerSeries.map_X] at h
      rw [h, pow_add, pow_one, add_pow_char_pow (1 : PowerSeries (ZMod l)) X l s, one_pow, ht]
      ring
    have hU1 : PadicInt.toZMod U = 1 := by
      have : PadicInt.toZMod (U - 1) = 0 := (toZMod_eq_zero_iff_dvd _).2
        ((dvd_pow_self (l : ℤ_[l]) (by omega : s ≠ 0)).trans hU)
      rwa [map_sub, map_one, sub_eq_zero] at this
    have hcomp : PadicInt.toZMod (coeff (n + 1) (T (X ^ n))) = (m : ZMod l) := by
      rw [← coeff_map, hTX, add_comm n 1]
      simp only [map_mul, map_sub, map_pow, map_add, map_one, PowerSeries.map_X,
        PowerSeries.map_C, hU1, one_mul]
      rw [coeff_mul_X_pow, hvb, map_sub, coeff_one_mul_one_add_X_sq_mul_pow,
        show ((1 : PowerSeries (ZMod l)) + X ^ 2 * (X ^ t * (1 + X))) ^ k =
          1 * (1 + X ^ 2 * (X ^ t * (1 + X))) ^ k by rw [one_mul],
        coeff_one_mul_one_add_X_sq_mul_pow, (constantCoeff_coeff_one_one_add_X_pow m).2]
      simp
    rw [hcomp] at hd
    exact (ZMod.natCast_eq_zero_iff m l).1 hd
  let g : ℕ → ℤ_[l] := fun j => coeff j (v ^ k * (X * F))
  let c : ℕ → ℤ_[l] := _root_.GlobalTheory.ExpImage.triSol (fun n i => coeff (n + 1) (T (X ^ i)))
    (fun n => g (n + 1))
  have hcoef : ∀ j : ℕ, (l : ℤ_[l]) ^ s ∣ coeff j (T (mk c) - v ^ k * (X * F)) := by
    intro j
    rw [map_sub, hsum]
    cases j with
    | zero =>
      have h0 : coeff 0 (v ^ k * (X * F)) = 0 := by
        simp [coeff_zero_eq_constantCoeff_apply]
      rw [h0, sub_zero, Finset.sum_range_one]
      exact dvd_mul_of_dvd_right (hdiag 0) _
    | succ n =>
      have hs' := sum_mul_triSol_eq (fun n i => coeff (n + 1) (T (X ^ i)))
        (fun n => g (n + 1)) n (hsub n)
      rw [Finset.sum_range_succ]
      convert dvd_mul_of_dvd_right (hdiag (n + 1)) (c (n + 1)) using 1
      simp only [g, c] at hs' ⊢
      rw [← hs', Finset.sum_congr rfl fun i _ => mul_comm _ _]
      ring
  let E : PowerSeries ℤ_[l] := mk fun j => (hcoef j).choose
  have hE : T (mk c) - v ^ k * (X * F) = C ((l : ℤ_[l]) ^ s) * E := by
    ext j
    rw [coeff_C_mul, coeff_mk]
    exact (hcoef j).choose_spec
  obtain ⟨u, hu⟩ := hunitv.pow k
  refine ⟨mk c, -(↑u⁻¹ * E), ?_⟩
  have hE' : T (mk c) = v ^ k * (X * F) + C ((l : ℤ_[l]) ^ s) * E := by
    rw [← hE]; ring
  rw [← hT, hE']
  have hl : (l : PowerSeries ℤ_[l]) ^ s = C ((l : ℤ_[l]) ^ s) := by simp
  rw [hl, ← hu]
  have : (u : PowerSeries ℤ_[l]) * ↑u⁻¹ = 1 := Units.mul_inv u
  linear_combination (-(C ((l : ℤ_[l]) ^ s) * E)) * this

end GlobalTheory.ExpImage
end

section
section
noncomputable section

namespace GlobalTheory.ExpImage.EpsSolve

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem εroot_pow_eq (m : ℕ) : AI.εroot m ^ (l ^ m) = AI.ε := by
  induction m with
  | zero => simp [LocAinf.εroot]
  | succ m ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply',
      frobeniusEquiv_symm_pow_p]
    exact ih

theorem epsT_pow (s : ℕ) : epsT AI s ^ (l ^ s) = 1 + AI.μ := by
  rw [epsT, ← map_pow, εroot_pow_eq, LocAinf.μ]
  ring

theorem epsT_zero : epsT AI 0 = 1 + AI.μ := by simpa using epsT_pow AI 0

theorem μ_not_unit : ¬ IsUnit AI.μ := by
  obtain ⟨θ, -, -, -, h, -⟩ := GlobalTheory.Cyc.exists_isTheta l P AI
  intro hu
  have h0 : θ AI.μ = 0 := (h _).mpr ⟨AI.π₁, by rw [AI.μ_eq, mul_comm]⟩
  have := hu.map θ
  rw [h0] at this
  exact not_isUnit_zero this

theorem actW_epsT (g : GQ l) (u : ℕ) (hu : (P.χQ g : ℚ_[l]) = (u : ℚ_[l])) (j : ℕ) :
    AI.actW g (epsT AI j) = epsT AI j ^ u := by
  rw [epsT, LocAinf.actW, WittVector.map_teichmuller, ← map_pow,
    ← GlobalTheory.ExpImage.actT_εroot_eq_pow l P AI g u hu j]
  rfl

theorem actW_μ (g : GQ l) (u : ℕ) (hu : (P.χQ g : ℚ_[l]) = (u : ℚ_[l])) :
    AI.actW g AI.μ = (1 + AI.μ) ^ u - 1 := by
  have h := actW_epsT AI g u hu 0
  rw [epsT_zero, map_add, map_one] at h
  linear_combination h

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ),
    Lev l s → ∀ g : GQ l, (P.χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ U : ℤ_[l],
    (l : ℤ_[l]) ^ s ∣ U - 1 → ∀ m : ℕ, ¬ l ∣ m → Solv AI K s g U (epsT AI s ^ m) := by
  intro l _ P AI K s hs g hg U hU m hm
  have hc := (GlobalTheory.Per.AinfComplete.main l AI.μ (μ_not_unit AI)).2
  obtain ⟨⟨ev, hev⟩, huniq⟩ := GlobalTheory.PowerSeriesAdicEval.exists_eval_and_unique ℤ_[l] (Ainf l) AI.μ hc
  obtain ⟨v, hv⟩ : (PowerSeries.X : PowerSeries ℤ_[l]) ∣ (1 + PowerSeries.X) ^ (1 + l ^ s) - 1 := by
    have := sub_dvd_pow_sub_pow (1 + PowerSeries.X : PowerSeries ℤ_[l]) 1 (1 + l ^ s)
    simpa using this
  have hsub : PowerSeries.HasSubst (PowerSeries.X * v : PowerSeries ℤ_[l]) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  let γ : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] PowerSeries ℤ_[l] := PowerSeries.substAlgHom hsub
  have hγ : γ PowerSeries.X = PowerSeries.X * v := PowerSeries.substAlgHom_X hsub
  have hgμ : AI.actW g AI.μ = AI.μ * ev v := by
    have := congrArg ev hv
    simp only [map_sub, map_pow, map_add, map_one, map_mul, hev] at this
    rw [actW_μ AI g _ hg, this]
  have hgev : ∀ f, AI.actW g (ev f) = ev (γ f) := by
    have := huniq (((AI.actWHom g : Ainf l ≃ₐ[ℤ_[l]] Ainf l) : Ainf l →ₐ[ℤ_[l]] Ainf l).comp ev)
      (ev.comp γ) (by
        change AI.actW g (ev PowerSeries.X) = ev (γ PowerSeries.X)
        rw [hγ, map_mul, hev, hgμ]) (by
        change AI.μ ∣ AI.actW g (ev PowerSeries.X)
        rw [hev, hgμ]
        exact dvd_mul_right _ _)
    intro f
    exact DFunLike.congr_fun this f
  have hχ : ∀ h ∈ Hinf K, (P.χQ h : ℚ_[l]) = ((1 : ℕ) : ℚ_[l]) := by
    intro h hh
    have := ((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.2 K h (Hinf_le_fix hh)).2.mp hh
    rw [this]
    simp
  have hhev : ∀ h ∈ Hinf K, ∀ f, AI.actW h (ev f) = ev f := by
    intro h hh
    have hμ : AI.actW h AI.μ = AI.μ := by
      rw [actW_μ AI h 1 (hχ h hh)]
      ring
    have := huniq (((AI.actWHom h : Ainf l ≃ₐ[ℤ_[l]] Ainf l) : Ainf l →ₐ[ℤ_[l]] Ainf l).comp ev)
      ev (by
        change AI.actW h (ev PowerSeries.X) = ev PowerSeries.X
        rw [hev, hμ]) (by
        change AI.μ ∣ AI.actW h (ev PowerSeries.X)
        rw [hev, hμ])
    intro f
    exact DFunLike.congr_fun this f
  have hgE : AI.actW g (epsT AI s) = epsT AI s * (1 + AI.μ) := by
    rw [actW_epsT AI g _ hg, pow_add, pow_one, epsT_pow]
  choose pp FF hpF using GlobalTheory.ExpImage.solve_mod_pow l s hs m hm U hU γ v hv.symm hγ
  let F : ℕ → PowerSeries ℤ_[l] := fun k => Nat.rec 1 (fun k f => FF (k + 1) f) k
  have hF : ∀ k, F (k + 1) = FF (k + 1) (F k) := fun _ => rfl
  refine ⟨fun k => epsT AI s ^ m * ev (pp (k + 1) (F k)), fun k => epsT AI s ^ m * ev (F k), ?_,
    fun k h hh => ?_, fun k => ?_⟩
  · change epsT AI s ^ m * ev 1 = _
    rw [map_one, mul_one]
  · rw [map_mul, map_pow, actW_epsT AI h 1 (hχ h hh), pow_one, hhev h hh]
  · have h1 := congrArg ev (hpF (k + 1) (F k))
    have hC : ev (PowerSeries.C U) = algebraMap ℤ_[l] (Ainf l) U := ev.commutes U
    simp only [map_sub, map_pow, map_add, map_one, map_mul, hev, hC, map_natCast] at h1
    unfold Step
    beta_reduce
    rw [hF, map_mul, map_pow, hgE, hgev, hgμ, mul_pow, mul_pow]
    linear_combination (epsT AI s ^ m * AI.μ ^ (k + 1)) * h1

end GlobalTheory.ExpImage.EpsSolve
end
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainfCocycleSolution_teichmullerEpsilonRoot_pow : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ), Lev l s → ∀ g : GQ l, (P.χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ U : ℤ_[l], (l : ℤ_[l]) ^ s ∣ U - 1 → ∀ m : ℕ, ¬ l ∣ m → Solv AI K s g U (epsT AI s ^ m) := by
  atlas_forward_decl GlobalTheory.ExpImage.EpsSolve.main
end

section
section
noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem exists_inv_pow_one_add {l : ℕ} [Fact l.Prime] {s : ℕ} (hs : 1 ≤ s) (e : ℕ) (u : ℚ_[l]ˣ)
    (hu : (u : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l])) :
    ∃ U : ℤ_[l], (U : ℚ_[l]) = ((u ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) ∧ (l : ℤ_[l]) ^ s ∣ U - 1 := by
  have hn : (-(l : ℤ_[l]) ^ s) ∈ nonunits ℤ_[l] := by
    rw [PadicInt.mem_nonunits, norm_neg, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (by rw [PadicInt.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)) (by omega)
  have hunit := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hn
  obtain ⟨V, hV⟩ := hunit.exists_left_inv
  refine ⟨V ^ e, ?_, ?_⟩
  · have h1 : (V : ℚ_[l]) * (u : ℚ_[l]) = 1 := by
      have := congrArg (fun z : ℤ_[l] => (z : ℚ_[l])) hV
      rw [hu]
      push_cast at this ⊢
      linear_combination this
    have h2 : (V : ℚ_[l]) = (u : ℚ_[l])⁻¹ := eq_inv_of_mul_eq_one_left h1
    simp [h2]
  · have h1 : (l : ℤ_[l]) ^ s ∣ V - 1 := ⟨-V, by linear_combination hV⟩
    have h2 := sub_dvd_pow_sub_pow V 1 e
    rw [one_pow] at h2
    exact h1.trans h2

theorem zetaQ_pow_level {l : ℕ} [Fact l.Prime] (P : LocPrime l) (s : ℕ) : P.ζQ s ^ (l ^ s) = 1 := by
  induction s with
  | zero => simpa using P.ζQ_zero
  | succ s ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem levSum_mem_Ks {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s j : ℕ) {ι : Type}
    (T : Finset ι) (c : ι → ↥(K0 K)) (m : ι → ℕ) (d : ↥(K0 K)) :
    levSum P K s j T c m d ∈ Ks K s := by
  have h0 : ∀ x : ↥(K0 K), (x : Om l) ∈ Ks K s := fun x => (le_sup_left : K0 K ≤ Ks K s) x.2
  have hζ : P.ζQ s ∈ Ks K s := by
    refine (le_sup_right : _ ≤ Ks K s) (IntermediateField.subset_adjoin _ _ ?_)
    exact zetaQ_pow_level P s
  unfold levSum
  refine add_mem (sum_mem fun i _ => mul_mem (pow_mem (natCast_mem _ _) _) (sum_mem fun a _ =>
    mul_mem (mul_mem (h0 _) (pow_mem (natCast_mem _ _) _)) (pow_mem hζ _)))
    (mul_mem (pow_mem (natCast_mem _ _) _) (h0 _))

theorem expStar_levSum : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (g : GQ l), g ∈ Gj K s → ((LT l).χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ (ι : Type) (T : Finset ι) (c : ι → ↥(K0 K)) (m : ι → ℕ) (d : ℕ → ↥(K0 K)), (∀ i ∈ T, ‖(c i : Om l)‖ ≤ 1 ∧ ¬ l ∣ m i) → (∀ j ≤ e, ‖(d j : Om l)‖ ≤ 1 ∧ d j - (l : ↥(K0 K)) ^ j * frK (LT l) K (d j) = (frK (LT l) K ^ s) (∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j)) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) (logZl l ((1 + l ^ s : ℕ) : ℚ_[l]) * ((e.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * e)))⁻¹ * levSum (LT l) K s e T c m (d e)) := by
  intro LT l _ AI hT K s hs e g hg hχ ι T c m d hc hd
  classical
  obtain ⟨U, hU, hU1⟩ := exists_inv_pow_one_add hs.1 e ((LT l).χQ g) hχ
  have hgen : IsGen (LT l).χQ K s g := by
    refine ⟨hg, ?_⟩
    rw [hχ]
    push_cast
    rw [add_sub_cancel_left, Padic.norm_p_pow]
  have hw : ∀ i, ∃ w : Ainf l, i ∈ T → Lifts AI K w (c i) := by
    intro i
    by_cases hi : i ∈ T
    · obtain ⟨w, hw⟩ := GlobalTheory.T.exists_lifts_of_norm_le_one_alt l (LT l) AI hT K (c i) (hc i hi).1
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose w hw using hw
  obtain ⟨y, hy, hexp⟩ := GlobalTheory.T.frobeniusSolution_expansion_mod_filtration l (LT l) AI hT K s ι T w c m (e + 1) d (by omega) hw
    (fun j hj => hd j (by omega))
  have hsolv : Solv AI K s g U (y - WittVector.frobenius y) := by
    rw [hy]
    refine Solv.sum T _ fun i hi => ?_
    exact (GlobalTheory.T.ainfCocycleSolution_teichmullerEpsilonRoot_pow l (LT l) AI K s hs g hχ U hU1 (m i) (hc i hi).2).mul
      ((hw i hi).act (Gj_le_fix s hg)) (fun h hh => (hw i hi).act (Hinf_le_fix hh))
  obtain ⟨b, hb0, hbH, z₀, hz₀⟩ := GlobalTheory.T.exists_deRham_element_of_cocycleRecursion l (LT l) AI hT K s hs g U (e + 1) (by omega) y hsolv
  obtain ⟨z, hz, hE⟩ := GlobalTheory.T.expStar_of_low_terms_removed LT l AI hT K s hs e g hgen
    (fun j => algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ *
      levSum (LT l) K s j T c m (d j))
    (fun j => mul_mem (IntermediateField.algebraMap_mem _ _) (levSum_mem_Ks _ _ _ _ _ _ _ _))
    b hb0 hbH ⟨z₀, by
      have := add_mem hz₀ hexp
      rw [hU] at this
      convert this using 1
      ring⟩
  refine ⟨z, hz, ?_⟩
  rw [hχ, ← mul_assoc, ← map_mul, ← mul_inv] at hE
  exact hE

end GlobalTheory.ExpImage
end
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualExp_teichmuller_power_sum_formula : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (g : GQ l), g ∈ Gj K s → ((LT l).χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ (ι : Type) (T : Finset ι) (c : ι → ↥(K0 K)) (m : ι → ℕ) (d : ℕ → ↥(K0 K)), (∀ i ∈ T, ‖(c i : Om l)‖ ≤ 1 ∧ ¬ l ∣ m i) → (∀ j ≤ e, ‖(d j : Om l)‖ ≤ 1 ∧ d j - (l : ↥(K0 K)) ^ j * frK (LT l) K (d j) = (frK (LT l) K ^ s) (∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j)) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) (logZl l ((1 + l ^ s : ℕ) : ℚ_[l]) * ((e.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * e)))⁻¹ * levSum (LT l) K s e T c m (d e)) := by
  atlas_forward_decl GlobalTheory.ExpImage.expStar_levSum
end

section
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

noncomputable section

namespace GlobalTheory.ExpImage.PosWeight

variable {l : ℕ} [Fact l.Prime]

theorem zeta_pow_self (P : LocPrime l) (m : ℕ) : P.ζQ m ^ (l ^ m) = 1 := by
  induction m with
  | zero => simp [P.ζQ_zero]
  | succ k ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem norm_nat_eq_one {a : ℕ} (ha : ¬ l ∣ a) : ‖(a : Om l)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr ha)

theorem norm_frK_pow (P : LocPrime l) (K : FinExt l) (n : ℕ) (c : ↥(K0 K)) :
    ‖(((frK P K ^ n) c : ↥(K0 K)) : Om l)‖ = ‖(c : Om l)‖ := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ', AlgHom.mul_apply, (GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq l P K).1, ih]

def co {K : FinExt l} (e : ℕ) (lam : ℕ → ↥(K0 K)) (i : ℕ × Bool) : ↥(K0 K) :=
  if i.2 then lam i.1 * ((i.1 : ↥(K0 K)) ^ e)⁻¹ else -(lam i.1 * ((i.1 : ↥(K0 K)) ^ e)⁻¹)

def ex (l s : ℕ) (i : ℕ × Bool) : ℕ := if i.2 then (1 + l ^ s) * i.1 else i.1

theorem formula_pos : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ), 1 ≤ e → ∀ (g : GQ l), g ∈ Gj K s → ((LT l).χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) → ‖(d : Om l)‖ ≤ 1 → d - (l : ↥(K0 K)) ^ e * frK (LT l) K d = (frK (LT l) K ^ s) (∑ a ∈ primeTo l s, lam a) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) ((((1 + l ^ s : ℕ) : ℚ_[l]) ^ e - 1) / (logZl l ((1 + l ^ s : ℕ) : ℚ_[l]) * ((e.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * e)))) * cycVal (LT l) K s e lam d) := by
  intro LT l _ AI hT K s hs e he g hg hχ lam d hlam hd hrec
  have hl : l.Prime := Fact.out
  have hu : ¬ l ∣ 1 + l ^ s := by
    intro h
    have h1 : l ∣ l ^ s := dvd_pow_self l (by have := hs.1; omega)
    exact hl.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_left h1).mp h))
  have hmem : ∀ a ∈ primeTo l s, ¬ l ∣ a := fun a ha => (Finset.mem_filter.mp ha).2
  have hne : ∀ a ∈ primeTo l s, (a : Om l) ≠ 0 := fun a ha h => by
    have := norm_nat_eq_one (hmem a ha)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hne' : ∀ a ∈ primeTo l s, (a : ↥(K0 K)) ≠ 0 := fun a ha h =>
    hne a ha (by simpa using congrArg (fun x : ↥(K0 K) => (x : Om l)) h)
  set T : Finset (ℕ × Bool) := primeTo l s ×ˢ Finset.univ with hTdef
  have hc : ∀ i ∈ T, ‖(co e lam i : Om l)‖ ≤ 1 ∧ ¬ l ∣ ex l s i := by
    rintro ⟨a, b⟩ hi
    have ha : a ∈ primeTo l s := (Finset.mem_product.mp hi).1
    have h1 := norm_nat_eq_one (hmem a ha)
    have h2 : ‖(lam a : Om l) * ((a : Om l) ^ e)⁻¹‖ ≤ 1 := by
      rw [norm_mul, norm_inv, norm_pow, h1]
      simpa using hlam a
    cases b
    · refine ⟨?_, hmem a ha⟩
      simpa [co, -norm_mul] using h2
    · refine ⟨by simpa [co, -norm_mul] using h2, ?_⟩
      intro h
      rcases (Nat.Prime.dvd_mul hl).mp h with h | h
      · exact hu h
      · exact hmem a ha h
  have hall : ∀ j : ℕ, ∃ dj : ↥(K0 K), j ≤ e → (‖(dj : Om l)‖ ≤ 1 ∧
      dj - (l : ↥(K0 K)) ^ j * frK (LT l) K dj =
        (frK (LT l) K ^ s) (∑ i ∈ T, co e lam i * (ex l s i : ↥(K0 K)) ^ j)) ∧
      (j = e → dj = (((1 + l ^ s : ℕ) : ↥(K0 K)) ^ e - 1) * d) := by
    intro j
    by_cases hje : j = e
    · subst hje
      refine ⟨(((1 + l ^ s : ℕ) : ↥(K0 K)) ^ j - 1) * d, fun _ => ⟨⟨?_, ?_⟩, fun _ => rfl⟩⟩
      · have h1 : ‖((1 + l ^ s : ℕ) : Om l) ^ j - 1‖ ≤ 1 := by
          have := IsUltrametricDist.norm_intCast_le_one (Om l) (((1 + l ^ s : ℕ) : ℤ) ^ j - 1)
          simpa using this
        have h2 : ((((((1 + l ^ s : ℕ) : ↥(K0 K)) ^ j - 1) * d : ↥(K0 K))) : Om l) =
            (((1 + l ^ s : ℕ) : Om l) ^ j - 1) * (d : Om l) := by simp
        rw [h2, norm_mul]
        exact mul_le_one₀ h1 (norm_nonneg _) hd
      · have h3 : ∑ i ∈ T, co j lam i * (ex l s i : ↥(K0 K)) ^ j =
            (((1 + l ^ s : ℕ) : ↥(K0 K)) ^ j - 1) * ∑ a ∈ primeTo l s, lam a := by
          rw [hTdef, Finset.sum_product, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a ha => ?_
          have := hne' a ha
          simp only [Fintype.sum_bool, co, ex, if_true, Bool.false_eq_true, if_false, Nat.cast_mul]
          field_simp
          ring
        rw [h3, map_mul, map_mul, ← hrec]
        simp only [map_sub, map_pow, map_natCast, map_one]
        ring
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · refine ⟨0, fun _ => ⟨⟨by simp, ?_⟩, fun h => absurd h hje⟩⟩
        rw [hTdef, Finset.sum_product]
        simp [co]
      · obtain ⟨dj, h1, h2⟩ := (GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq l (LT l) K).2 j hj
          ((frK (LT l) K ^ s) (∑ i ∈ T, co e lam i * (ex l s i : ↥(K0 K)) ^ j)) (by
            rw [norm_frK_pow, AddSubmonoidClass.coe_finset_sum]
            refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i hi => ?_
            have h2 : ((co e lam i * (ex l s i : ↥(K0 K)) ^ j : ↥(K0 K)) : Om l) =
              (co e lam i : Om l) * (ex l s i : Om l) ^ j := by simp
            rw [h2, norm_mul, norm_pow, norm_nat_eq_one (hc i hi).2]
            simpa using (hc i hi).1)
        exact ⟨dj, fun _ => ⟨⟨h1, h2⟩, fun h => absurd h hje⟩⟩
  choose D hD using hall
  obtain ⟨z, hz, hE⟩ := GlobalTheory.T.dualExp_teichmuller_power_sum_formula LT l AI hT K s hs e g hg hχ (ℕ × Bool) T (co e lam) (ex l s) D hc
    (fun j hj => (hD j hj).1)
  refine ⟨z, hz, ?_⟩
  have hlev : levSum (LT l) K s e T (co e lam) (ex l s) (D e) =
      (((1 + l ^ s : ℕ) : Om l) ^ e - 1) * cycVal (LT l) K s e lam d := by
    rw [(hD e le_rfl).2 rfl]
    unfold levSum cycVal
    rw [mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_left_comm]
      congr 1
      rw [hTdef, Finset.sum_product, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have h0 := hne a ha
      have hz : (LT l).ζQ s ^ ((1 + l ^ s) * a * l ^ i) = (LT l).ζQ s ^ (a * l ^ i) := by
        rw [mul_assoc, add_mul, one_mul, pow_add, pow_mul _ (l ^ s), zeta_pow_self, one_pow, mul_one]
      have hco : (((frK (LT l) K ^ i) (lam a * ((a : ↥(K0 K)) ^ e)⁻¹) : ↥(K0 K)) : Om l) =
          (((frK (LT l) K ^ i) (lam a) : ↥(K0 K)) : Om l) * ((a : Om l) ^ e)⁻¹ := by
        rw [map_mul, map_inv₀, map_pow, map_natCast]
        simp
      simp only [Fintype.sum_bool, co, ex, if_true, Bool.false_eq_true, if_false, map_neg,
        NegMemClass.coe_neg, hco, hz, Nat.cast_mul]
      field_simp
      ring
    · have h2 : ((((((1 + l ^ s : ℕ) : ↥(K0 K)) ^ e - 1) * d : ↥(K0 K))) : Om l) =
            (((1 + l ^ s : ℕ) : Om l) ^ e - 1) * (d : Om l) := by simp
      rw [h2]
      ring
  rw [hlev] at hE
  convert hE using 1
  rw [div_eq_mul_inv, map_mul, map_sub, map_pow, map_natCast, map_one]
  ring

end GlobalTheory.ExpImage.PosWeight
end
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicTower_frobenius_formula_pos_weight : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ), 1 ≤ e → ∀ (g : GQ l), g ∈ Gj K s → ((LT l).χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) → ‖(d : Om l)‖ ≤ 1 → d - (l : ↥(K0 K)) ^ e * frK (LT l) K d = (frK (LT l) K ^ s) (∑ a ∈ primeTo l s, lam a) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) ((((1 + l ^ s : ℕ) : ℚ_[l]) ^ e - 1) / (logZl l ((1 + l ^ s : ℕ) : ℚ_[l]) * ((e.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * e)))) * cycVal (LT l) K s e lam d) := by
  atlas_forward_decl GlobalTheory.ExpImage.PosWeight.formula_pos
end
