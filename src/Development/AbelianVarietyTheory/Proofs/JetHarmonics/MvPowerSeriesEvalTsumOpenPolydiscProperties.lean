import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesConvergentSubstHasSumAndBoundsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosureStatement
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesConvergentSubstHasSumAndBounds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosure

section
section
noncomputable section

namespace GlobalTheory.ConvSer.Bridge

def unitExp : ℕ ≃ (Unit →₀ ℕ) where
  toFun n := Finsupp.single () n
  invFun ν := ν ()
  left_inv n := by simp
  right_inv ν := by ext; simp

variable {K : Type} [NormedField K]

theorem powerSeriesConvergentSubstMv_eq_mv {τ : Type} (s : MvPowerSeries τ K) (f : PowerSeries K) :
    csub1 s f = csub (fun _ : Unit => s) f := by
  ext μ
  change ∑' n : ℕ, PowerSeries.coeff n f * MvPowerSeries.coeff μ (s ^ n) =
    ∑' ν : Unit →₀ ℕ, MvPowerSeries.coeff ν f * MvPowerSeries.coeff μ (∏ i : Unit, s ^ ν i)
  rw [← unitExp.tsum_eq]
  refine tsum_congr fun n => ?_
  simp [unitExp]

theorem powerSeriesEvalTsum_eq_mvPowerSeriesEvalTsum (f : PowerSeries K) (t : K) : ev1 f t = ev f (fun _ : Unit => t) := by
  unfold ev1 ev
  rw [← unitExp.tsum_eq]
  refine tsum_congr fun n => ?_
  simp [unitExp]

theorem powerSeriesHasSumAt_iff_mvPowerSeriesHasSumAt (f : PowerSeries K) (t a : K) : PowerSeriesHasSumAt f t a ↔ HS f (fun _ : Unit => t) a := by
  unfold PowerSeriesHasSumAt HS
  rw [← unitExp.hasSum_iff]
  have h : (fun ν : Unit →₀ ℕ => MvPowerSeries.coeff ν f * ∏ i : Unit, t ^ ν i) ∘ unitExp =
      fun n : ℕ => PowerSeries.coeff n f * t ^ n := by
    funext n
    simp [unitExp]
  rw [h]

theorem csub_C {σ τ : Type} [Fintype σ] (S : MvPowerSeries σ K) (x : σ → K) :
    csub (fun i => (MvPowerSeries.C (x i) : MvPowerSeries τ K)) S = MvPowerSeries.C (ev S x) := by
  have hC : ∀ ν : σ →₀ ℕ, (∏ i, (MvPowerSeries.C (x i) : MvPowerSeries τ K) ^ ν i) =
      MvPowerSeries.C (∏ i, x i ^ ν i) := fun ν => by simp [map_prod, map_pow]
  ext μ
  change ∑' ν : σ →₀ ℕ, MvPowerSeries.coeff ν S *
      MvPowerSeries.coeff μ (∏ i, (MvPowerSeries.C (x i) : MvPowerSeries τ K) ^ ν i) = _
  simp only [hC]
  by_cases h : μ = 0
  · subst h
    simp only [MvPowerSeries.coeff_zero_C]
    rfl
  · simp only [MvPowerSeries.coeff_C_of_ne_zero h, mul_zero, tsum_zero]

theorem shift1_eq_csub (F : MvPowerSeries (Fin 2) K) (y : K) :
    shift1 F y = csub (![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) F := by
  ext m
  have hc : ∀ p : PowerSeries K, MvPowerSeries.coeff (unitExp m) p = PowerSeries.coeff m p :=
    fun p => by simp [unitExp]
  change PowerSeries.coeff m (shift1 F y) = ∑' ν : Fin 2 →₀ ℕ, MvPowerSeries.coeff ν F *
    MvPowerSeries.coeff (unitExp m)
      (∏ i, (![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) i ^ ν i)
  have hterm : ∀ ν : Fin 2 →₀ ℕ, MvPowerSeries.coeff ν F * MvPowerSeries.coeff (unitExp m)
      (∏ i, (![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) i ^ ν i) =
      MvPowerSeries.coeff ν F * (if m = ν 0 then y ^ ν 1 else 0) := by
    intro ν
    rw [hc, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← map_pow, mul_comm (PowerSeries.X ^ _), PowerSeries.coeff_C_mul_X_pow]
  simp only [hterm]
  rw [shift1, PowerSeries.coeff_mk]
  have hinj : Function.Injective
      (fun b : ℕ => Finsupp.single (0 : Fin 2) m + Finsupp.single 1 b) := by
    intro b b' h
    have h1 := congrArg (fun ν : Fin 2 →₀ ℕ => ν 1) h
    simpa using h1
  have hsupp : Function.support
      (fun ν : Fin 2 →₀ ℕ => MvPowerSeries.coeff ν F * (if m = ν 0 then y ^ ν 1 else 0)) ⊆
      Set.range (fun b : ℕ => Finsupp.single (0 : Fin 2) m + Finsupp.single 1 b) := by
    intro ν hν
    have h0 : m = ν 0 := by
      by_contra h
      exact hν (by simp [h])
    refine ⟨ν 1, ?_⟩
    ext i
    fin_cases i <;> simp [h0]
  refine Eq.trans ?_ (hinj.tsum_eq hsupp)
  refine tsum_congr fun b => ?_
  simp

theorem csub_eq_subst {σ τ : Type} [Fintype σ] (a : σ → MvPowerSeries τ K)
    (S : MvPowerSeries σ K) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    csub a S = MvPowerSeries.subst a S := by
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  ext μ
  rw [MvPowerSeries.coeff_subst hs, ← tsum_eq_finsum (L := SummationFilter.unconditional (σ →₀ ℕ))
    (MvPowerSeries.coeff_subst_finite hs S μ)]
  change ∑' ν : σ →₀ ℕ, MvPowerSeries.coeff ν S * MvPowerSeries.coeff μ (∏ i, a i ^ ν i) = _
  refine tsum_congr fun ν => ?_
  rw [smul_eq_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]

theorem powerSeriesConvergentSubstMv_eq_subst {τ : Type} (a : MvPowerSeries τ K) (f : PowerSeries K)
    (ha : MvPowerSeries.constantCoeff a = 0) : csub1 a f = f.subst a := by
  rw [powerSeriesConvergentSubstMv_eq_mv, csub_eq_subst _ _ (fun _ => ha)]
  rfl

theorem csub_bridge : ∀ (K : Type) [NormedField K], (∀ (τ : Type) (s : MvPowerSeries τ K) (f : PowerSeries K), csub1 s f = csub (fun _ : Unit => s) f) ∧ (∀ (f : PowerSeries K) (t : K), ev1 f t = ev f (fun _ : Unit => t)) ∧ (∀ (f : PowerSeries K) (t a : K), PowerSeriesHasSumAt f t a ↔ HS f (fun _ : Unit => t) a) ∧ (∀ (σ τ : Type) [Fintype σ] (S : MvPowerSeries σ K) (x : σ → K), csub (fun i => (MvPowerSeries.C (x i) : MvPowerSeries τ K)) S = MvPowerSeries.C (ev S x)) ∧ (∀ (F : MvPowerSeries (Fin 2) K) (y : K), shift1 F y = csub (![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) F) ∧ (∀ (σ τ : Type) [Fintype σ] (a : σ → MvPowerSeries τ K) (S : MvPowerSeries σ K), (∀ i, MvPowerSeries.constantCoeff (a i) = 0) → csub a S = MvPowerSeries.subst a S) ∧ (∀ (τ : Type) (a : MvPowerSeries τ K) (f : PowerSeries K), MvPowerSeries.constantCoeff a = 0 → csub1 a f = f.subst a) := by
  intro K _
  exact ⟨fun _ s f => powerSeriesConvergentSubstMv_eq_mv s f, fun f t => powerSeriesEvalTsum_eq_mvPowerSeriesEvalTsum f t, fun f t a => powerSeriesHasSumAt_iff_mvPowerSeriesHasSumAt f t a,
    fun _ _ _ S x => csub_C S x, fun F y => shift1_eq_csub F y,
    fun _ _ _ a S ha => csub_eq_subst a S ha, fun _ a f ha => powerSeriesConvergentSubstMv_eq_subst a f ha⟩

end GlobalTheory.ConvSer.Bridge
end
end

open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergentSubst_oneVariable_and_formal_agreement : ∀ (K : Type) [NormedField K], (∀ (τ : Type) (s : MvPowerSeries τ K) (f : PowerSeries K), csub1 s f = csub (fun _ : Unit => s) f) ∧ (∀ (f : PowerSeries K) (t : K), ev1 f t = ev f (fun _ : Unit => t)) ∧ (∀ (f : PowerSeries K) (t a : K), PowerSeriesHasSumAt f t a ↔ HS f (fun _ : Unit => t) a) ∧ (∀ (σ τ : Type) [Fintype σ] (S : MvPowerSeries σ K) (x : σ → K), csub (fun i => (MvPowerSeries.C (x i) : MvPowerSeries τ K)) S = MvPowerSeries.C (ev S x)) ∧ (∀ (F : MvPowerSeries (Fin 2) K) (y : K), shift1 F y = csub (![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) F) ∧ (∀ (σ τ : Type) [Fintype σ] (a : σ → MvPowerSeries τ K) (S : MvPowerSeries σ K), (∀ i, MvPowerSeries.constantCoeff (a i) = 0) → csub a S = MvPowerSeries.subst a S) ∧ (∀ (τ : Type) (a : MvPowerSeries τ K) (f : PowerSeries K), MvPowerSeries.constantCoeff a = 0 → csub1 a f = f.subst a) := by
  atlas_forward_decl GlobalTheory.ConvSer.Bridge.csub_bridge
end

section
section
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

section
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] {σ τ : Type}
  [Fintype σ] {s : σ → MvPowerSeries τ K}

theorem csub_add_of_bdd (hs : ∀ i, Small (s i)) {S T : MvPowerSeries σ K} (hS : Bdd S)
    (hT : Bdd T) : csub s (S + T) = csub s S + csub s T := by
  ext μ
  have h1 := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s S hs hS).1 μ
  have h2 := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s T hs hT).1 μ
  have h3 := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s _ hs ((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.1 S T hS hT).1).1 μ
  rw [map_add]
  refine h3.unique ?_
  simpa only [map_add, add_mul] using h1.add h2

theorem csub_sub_of_bdd (hs : ∀ i, Small (s i)) {S T : MvPowerSeries σ K} (hS : Bdd S)
    (hT : Bdd T) : csub s (S - T) = csub s S - csub s T := by
  ext μ
  have h1 := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s S hs hS).1 μ
  have h2 := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s T hs hT).1 μ
  have h3 := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s _ hs ((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.1 S T hS hT).2.1).1 μ
  rw [map_sub]
  refine h3.unique ?_
  simpa only [map_sub, sub_mul] using h1.sub h2

theorem csub_mul_of_bdd (hs : ∀ i, Small (s i)) {S T : MvPowerSeries σ K} (hS : Bdd S)
    (hT : Bdd T) : csub s (S * T) = csub s S * csub s T := by
  classical
  ext μ
  have h3 := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s _ hs ((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.1 S T hS hT).2.2).1 μ
  refine h3.unique ?_
  haveI : NonarchimedeanRing K := ⟨NonarchimedeanAddGroup.is_nonarchimedean⟩
  have h4 : HasSum (fun p : (σ →₀ ℕ) × (σ →₀ ℕ) =>
      MvPowerSeries.coeff p.1 S * MvPowerSeries.coeff p.2 T *
        MvPowerSeries.coeff μ (∏ i, s i ^ (p.1 + p.2) i))
      (MvPowerSeries.coeff μ (csub s S * csub s T)) := by
    rw [MvPowerSeries.coeff_mul]
    have h5 := hasSum_sum (s := Finset.HasAntidiagonal.antidiagonal μ) (fun q _ =>
      ((GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s S hs hS).1 q.1).mul_of_nonarchimedean
        ((GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ τ s T hs hT).1 q.2))
    convert h5 using 2 with p
    simp only [Finsupp.add_apply, pow_add, Finset.prod_mul_distrib, MvPowerSeries.coeff_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  have h6 := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.2 h4
  refine h6.sigma fun ν => ?_
  rw [MvPowerSeries.coeff_mul, Finset.sum_mul, ← Finset.sum_coe_sort]
  convert hasSum_fintype _ using 2 with q
  have := Finset.HasAntidiagonal.mem_antidiagonal.1 q.2
  simp only [Function.comp, Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply, this]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem csub_monomial (s : σ → MvPowerSeries τ K) (ν : σ →₀ ℕ) (a : K) :
    csub s (MvPowerSeries.monomial ν a) = MvPowerSeries.C a * ∏ i, s i ^ ν i := by
  classical
  ext μ
  rw [MvPowerSeries.coeff_C_mul]
  change ∑' ν' : σ →₀ ℕ, MvPowerSeries.coeff ν' (MvPowerSeries.monomial ν a) *
    MvPowerSeries.coeff μ (∏ i, s i ^ ν' i) = _
  rw [tsum_eq_single ν]
  · rw [MvPowerSeries.coeff_monomial_same]
  · intro b hb
    rw [MvPowerSeries.coeff_monomial_ne hb, zero_mul]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem csub_C (s : σ → MvPowerSeries τ K) (a : K) :
    csub s (MvPowerSeries.C a) = MvPowerSeries.C a := by
  rw [← MvPowerSeries.monomial_zero_eq_C_apply, csub_monomial]
  simp

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem csub_X (s : σ → MvPowerSeries τ K) (i : σ) :
    csub s (MvPowerSeries.X i) = s i := by
  classical
  rw [MvPowerSeries.X_def, csub_monomial, map_one, one_mul, Finset.prod_eq_single i]
  · simp
  · intro b _ hb
    rw [Finsupp.single_eq_of_ne hb, pow_zero]
  · simp

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem csub_one (s : σ → MvPowerSeries τ K) : csub s 1 = 1 := by
  simpa using csub_C s (1 : K)

theorem csub_pow_of_bdd (hs : ∀ i, Small (s i)) {S : MvPowerSeries σ K} (hS : Bdd S) (n : ℕ) :
    csub s (S ^ n) = csub s S ^ n := by
  induction n with
  | zero => simpa using csub_one s
  | succ n ih =>
    rw [pow_succ, pow_succ, csub_mul_of_bdd hs (((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.2.1 S n).2.1 hS) hS, ih]

theorem csub_prod_of_bdd (hs : ∀ i, Small (s i)) {ι : Type} (t : Finset ι)
    (f : ι → MvPowerSeries σ K) (hf : ∀ i ∈ t, Bdd (f i)) :
    csub s (∏ i ∈ t, f i) = ∏ i ∈ t, csub s (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using csub_one s
  | insert a t ha ih =>
    have ht : ∀ i ∈ t, Bdd (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      csub_mul_of_bdd hs (hf a (Finset.mem_insert_self a t))
        (((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.2.2.2.2.1 ι t f).2 ht).1, ih ht]

theorem csub_eval₂_of_bdd (hs : ∀ i, Small (s i)) {k ι : Type} [CommRing k] (φ : k →+* K)
    (a : ι → MvPowerSeries σ K) (A : MvPolynomial ι k) (ha : ∀ j, Bdd (a j)) :
    csub s (MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries σ K).comp φ) a A) =
      MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries τ K).comp φ)
        (fun j => csub s (a j)) A := by
  have hb := fun B => (GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ).2.2.2.2.2.2.2.2.1 k ι φ a B ha
  induction A using MvPolynomial.induction_on with
  | C c => simp [csub_C]
  | add p q hp hq =>
    rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_add, csub_add_of_bdd hs (hb p) (hb q), hp, hq]
  | mul_X p j hp =>
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval₂_X,
      csub_mul_of_bdd hs (hb p) (ha j), hp]

end

theorem csub_ring_map : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (σ τ : Type) [Fintype σ] (s : σ → MvPowerSeries τ K), (∀ i, Small (s i)) → (∀ S T : MvPowerSeries σ K, Bdd S → Bdd T → csub s (S + T) = csub s S + csub s T ∧ csub s (S - T) = csub s S - csub s T ∧ csub s (S * T) = csub s S * csub s T) ∧ (∀ a : K, csub s (MvPowerSeries.C a) = MvPowerSeries.C a) ∧ (∀ i, csub s (MvPowerSeries.X i) = s i) ∧ (∀ (S : MvPowerSeries σ K) (n : ℕ), Bdd S → csub s (S ^ n) = csub s S ^ n) ∧ (∀ (ι : Type) (t : Finset ι) (f : ι → MvPowerSeries σ K), (∀ i ∈ t, Bdd (f i)) → csub s (∏ i ∈ t, f i) = ∏ i ∈ t, csub s (f i)) ∧ (∀ (k ι : Type) [CommRing k] (φ : k →+* K) (a : ι → MvPowerSeries σ K) (A : MvPolynomial ι k), (∀ j, Bdd (a j)) → csub s (MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries σ K).comp φ) a A) = MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries τ K).comp φ) (fun j => csub s (a j)) A) := by
  intro K _ _ _ σ τ _ s hs
  exact ⟨fun S T hS hT => ⟨csub_add_of_bdd hs hS hT, csub_sub_of_bdd hs hS hT,
      csub_mul_of_bdd hs hS hT⟩, csub_C s, csub_X s, fun S n hS => csub_pow_of_bdd hs hS n,
    fun ι t f hf => csub_prod_of_bdd hs t f hf,
    fun k ι _ φ a A ha => csub_eval₂_of_bdd hs φ a A ha⟩

end GlobalTheory.ConvSer
end

open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeriesConvergentSubst_isRingHom_on_bounded : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (σ τ : Type) [Fintype σ] (s : σ → MvPowerSeries τ K), (∀ i, Small (s i)) → (∀ S T : MvPowerSeries σ K, Bdd S → Bdd T → csub s (S + T) = csub s S + csub s T ∧ csub s (S - T) = csub s S - csub s T ∧ csub s (S * T) = csub s S * csub s T) ∧ (∀ a : K, csub s (MvPowerSeries.C a) = MvPowerSeries.C a) ∧ (∀ i, csub s (MvPowerSeries.X i) = s i) ∧ (∀ (S : MvPowerSeries σ K) (n : ℕ), Bdd S → csub s (S ^ n) = csub s S ^ n) ∧ (∀ (ι : Type) (t : Finset ι) (f : ι → MvPowerSeries σ K), (∀ i ∈ t, Bdd (f i)) → csub s (∏ i ∈ t, f i) = ∏ i ∈ t, csub s (f i)) ∧ (∀ (k ι : Type) [CommRing k] (φ : k →+* K) (a : ι → MvPowerSeries σ K) (A : MvPolynomial ι k), (∀ j, Bdd (a j)) → csub s (MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries σ K).comp φ) a A) = MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries τ K).comp φ) (fun j => csub s (a j)) A) := by
  atlas_forward_decl GlobalTheory.ConvSer.csub_ring_map
end

section
section
open GlobalTheory.ConvSer Filter Topology

namespace GlobalTheory.ConvSer

theorem tendsto_cofinite_double {K α β : Type*} [NormedField K] (c : α → β → K) (d : β → K)
    (C : ℝ) (hC : ∀ a b, ‖c a b‖ ≤ C) (hc : ∀ b, Tendsto (fun a => c a b) cofinite (𝓝 0))
    (hd : Tendsto d cofinite (𝓝 0)) :
    Tendsto (fun p : α × β => c p.1 p.2 * d p.2) cofinite (𝓝 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have h1 : Tendsto (fun b => C * ‖d b‖) cofinite (𝓝 0) := by
    simpa using (tendsto_zero_iff_norm_tendsto_zero.1 hd).const_mul C
  have h2 : {b | ¬ C * ‖d b‖ < ε}.Finite :=
    eventually_cofinite.1 (h1.eventually (gt_mem_nhds hε))
  have h3 : ∀ b, {a | ¬ ‖c a b * d b‖ < ε}.Finite := by
    intro b
    have : Tendsto (fun a => c a b * d b) cofinite (𝓝 0) := by
      simpa using (hc b).mul_const (d b)
    exact eventually_cofinite.1 (NormedAddGroup.tendsto_nhds_zero.1 this ε hε)
  rw [eventually_cofinite]
  refine (h2.biUnion (t := fun b => (fun a => (a, b)) '' {a | ¬ ‖c a b * d b‖ < ε})
    (fun b _ => (h3 b).image _)).subset ?_
  rintro ⟨a, b⟩ hp
  simp only [Set.mem_ofPred_eq] at hp
  simp only [Set.mem_iUnion]
  refine ⟨b, ?_, a, hp, rfl⟩
  intro hlt
  apply hp
  rw [norm_mul]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hC a b) (norm_nonneg _)) hlt

theorem small_csub_of_small (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (σ τ : Type) [Fintype σ] (t : σ → MvPowerSeries τ K) (ht : ∀ i, Small (t i))
    (u : MvPowerSeries σ K) (hu : Small u) : Small (csub t u) := by
  obtain ⟨hI, hB, hP, hC, -⟩ := GlobalTheory.BddAlg.bdd_alg K σ
  set c := MvPowerSeries.constantCoeff u with hc
  have hCi : Intg (MvPowerSeries.C c : MvPowerSeries σ K) := (hC c).2.1 hu.2.le
  have h1 : Intg (u - MvPowerSeries.C c) := (hI _ _ hu.1 hCi).2.1
  have hb1 : Bdd (u - MvPowerSeries.C c) := (hP _ 0).2.2 h1
  have hbu : Bdd u := (hP _ 0).2.2 hu.1
  have h2 : Small (csub t (u - MvPowerSeries.C c)) :=
    (GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ t _ ht hb1).2.2.2 h1 (by simp [hc])
  obtain ⟨hR, hRC, -⟩ := GlobalTheory.T.mvPowerSeriesConvergentSubst_isRingHom_on_bounded K σ τ t ht
  have h3 : csub t u = csub t (u - MvPowerSeries.C c) + MvPowerSeries.C c := by
    rw [(hR _ _ hbu (hC c).1).2.1, hRC]; ring
  refine ⟨(GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ t _ ht hbu).2.2.1 hu.1, ?_⟩
  rw [h3, map_add, MvPowerSeries.constantCoeff_C]
  exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h2.2 hu.2)

theorem csub_assoc : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (ρ σ τ : Type) [Fintype ρ] [Fintype σ] (s : ρ → MvPowerSeries σ K)
    (t : σ → MvPowerSeries τ K) (S : MvPowerSeries ρ K), (∀ j, Small (s j)) →
    (∀ i, Small (t i)) → Bdd S →
    (∀ j, Small (csub t (s j))) ∧ csub t (csub s S) = csub (fun j => csub t (s j)) S := by
  intro K _ _ _ ρ σ τ _ _ s t S hs ht hS
  have hst : ∀ j, Small (csub t (s j)) := fun j => small_csub_of_small K σ τ t ht _ (hs j)
  refine ⟨hst, ?_⟩
  obtain ⟨hI, hB, hP, hC, -, hF, -⟩ := GlobalTheory.BddAlg.bdd_alg K σ
  obtain ⟨-, -, -, hRP, hRF, -⟩ := GlobalTheory.T.mvPowerSeriesConvergentSubst_isRingHom_on_bounded K σ τ t ht
  have hint : ∀ ν : ρ →₀ ℕ, Intg (∏ j, s j ^ ν j) := fun ν =>
    ((hF ρ Finset.univ _).1 fun j _ => (hP _ _).1 (hs j).1).1
  have hbd : ∀ ν : ρ →₀ ℕ, Bdd (∏ j, s j ^ ν j) := fun ν => (hP _ 0).2.2 (hint ν)
  have hprod : ∀ ν : ρ →₀ ℕ, csub t (∏ j, s j ^ ν j) = ∏ j, csub t (s j) ^ ν j := by
    intro ν
    rw [hRF ρ Finset.univ _ fun j _ => (hP _ 0).2.2 ((hP _ _).1 (hs j).1)]
    exact Finset.prod_congr rfl fun j _ => hRP _ _ ((hP _ 0).2.2 (hs j).1)
  ext μ
  obtain ⟨C, hCS⟩ := id hS
  let c : (ρ →₀ ℕ) → (σ →₀ ℕ) → K := fun ν l =>
    MvPowerSeries.coeff ν S * MvPowerSeries.coeff l (∏ j, s j ^ ν j)
  let d : (σ →₀ ℕ) → K := fun l => MvPowerSeries.coeff μ (∏ i, t i ^ l i)
  have hcs : ∀ l, HasSum (fun ν => c ν l) (MvPowerSeries.coeff l (csub s S)) :=
    (GlobalTheory.ConvSer.csub_hasSum_and_bounds K ρ σ s S hs hS).1
  have hd : Tendsto d cofinite (𝓝 0) := by
    let U : MvPowerSeries σ K := fun _ => 1
    have hU : ∀ l, MvPowerSeries.coeff l U = 1 := fun _ => rfl
    have := ((GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ t U ht ⟨1, fun l => by simp [hU]⟩).1 μ).summable.tendsto_cofinite_zero
    simpa only [hU, one_mul] using this
  have hsum : Summable (fun p : (ρ →₀ ℕ) × (σ →₀ ℕ) => c p.1 p.2 * d p.2) := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    refine tendsto_cofinite_double c d C ?_ (fun l => (hcs l).summable.tendsto_cofinite_zero) hd
    intro ν l
    simp only [c, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hint ν l)).trans (hCS ν)
  have hA : HasSum (fun ν : ρ →₀ ℕ => MvPowerSeries.coeff ν S *
      MvPowerSeries.coeff μ (∏ j, csub t (s j) ^ ν j))
      (∑' p : (ρ →₀ ℕ) × (σ →₀ ℕ), c p.1 p.2 * d p.2) := by
    refine hsum.hasSum.prod_fiberwise fun ν => ?_
    rw [← hprod]
    have := ((GlobalTheory.ConvSer.csub_hasSum_and_bounds K σ τ t _ ht (hbd ν)).1 μ).mul_left (MvPowerSeries.coeff ν S)
    simpa only [c, d, mul_assoc] using this
  have hB' : HasSum (fun l : σ →₀ ℕ => MvPowerSeries.coeff l (csub s S) * d l)
      (∑' p : (ρ →₀ ℕ) × (σ →₀ ℕ), c p.1 p.2 * d p.2) := by
    refine ((Equiv.prodComm _ _).hasSum_iff.2 hsum.hasSum).prod_fiberwise fun l => ?_
    exact (hcs l).mul_right (d l)
  exact hB'.tsum_eq.trans hA.tsum_eq.symm

end GlobalTheory.ConvSer
end

open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeriesConvergentSubst_assoc : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (ρ σ τ : Type) [Fintype ρ] [Fintype σ] (s : ρ → MvPowerSeries σ K) (t : σ → MvPowerSeries τ K) (S : MvPowerSeries ρ K), (∀ j, Small (s j)) → (∀ i, Small (t i)) → Bdd S → (∀ j, Small (csub t (s j))) ∧ csub t (csub s S) = csub (fun j => csub t (s j)) S := by
  atlas_forward_decl GlobalTheory.ConvSer.csub_assoc
end

section
section
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem ev_algebra : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (σ : Type) [Fintype σ] (x : σ → K), (∀ i, ‖x i‖ < 1) → (∀ S : MvPowerSeries σ K, Bdd S → HS S x (ev S x)) ∧ (∀ S T : MvPowerSeries σ K, Bdd S → Bdd T → ev (S + T) x = ev S x + ev T x ∧ ev (S - T) x = ev S x - ev T x ∧ ev (S * T) x = ev S x * ev T x) ∧ (∀ a : K, ev (MvPowerSeries.C a : MvPowerSeries σ K) x = a) ∧ (∀ i, ev (MvPowerSeries.X i : MvPowerSeries σ K) x = x i) ∧ (∀ S : MvPowerSeries σ K, Intg S → ‖ev S x‖ ≤ 1 ∧ (Small S → ‖ev S x‖ < 1)) ∧ (∀ (ρ : Type) [Fintype ρ] (s : ρ → MvPowerSeries σ K) (S : MvPowerSeries ρ K), (∀ j, Small (s j)) → Bdd S → ev (csub s S) x = ev S (fun j => ev (s j) x)) ∧ (∀ (ρ : Type) [Fintype ρ] (a : ρ → MvPowerSeries σ K) (S : MvPowerSeries ρ K), (∀ j, Intg (a j)) → (∀ j, MvPowerSeries.constantCoeff (a j) = 0) → Bdd S → ev (MvPowerSeries.subst a S) x = ev S (fun j => ev (a j) x)) ∧ (∀ (a : MvPowerSeries σ K) (f : PowerSeries K), Intg a → MvPowerSeries.constantCoeff a = 0 → Bdd f → ev (f.subst a) x = ev1 f (ev a x)) := by
  intro K _ _ _ σ _ x hx
  have Cinj : ∀ a b : K, (MvPowerSeries.C a : MvPowerSeries Unit K) = MvPowerSeries.C b → a = b := by
    intro a b h
    simpa using congrArg MvPowerSeries.constantCoeff h
  have E : ∀ (ρ : Type) [Fintype ρ] (S : MvPowerSeries ρ K) (y : ρ → K),
      csub (fun i => (MvPowerSeries.C (y i) : MvPowerSeries Unit K)) S = MvPowerSeries.C (ev S y) := by
    intro ρ _ S y
    exact (GlobalTheory.T.convergentSubst_oneVariable_and_formal_agreement K).2.2.2.1 ρ Unit S y
  obtain ⟨c, hc⟩ : ∃ c : σ → MvPowerSeries Unit K, c = fun i => MvPowerSeries.C (x i) := ⟨_, rfl⟩
  have E' : ∀ S : MvPowerSeries σ K, csub c S = MvPowerSeries.C (ev S x) := by
    intro S
    subst hc
    exact E σ S x
  have B := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ
  have hcs : ∀ i, Small (c i) := by
    intro i
    subst hc
    exact ((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit).2.2.2.1 (x i)).2.2 (hx i)
  have R := GlobalTheory.T.mvPowerSeriesConvergentSubst_isRingHom_on_bounded K σ Unit c hcs

  have p1 : ∀ S : MvPowerSeries σ K, Bdd S → HS S x (ev S x) := by
    intro S hS
    have h := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ Unit c S hcs hS).1 0
    rw [E' S] at h
    have hm : ∀ ν : σ →₀ ℕ, MvPowerSeries.coeff 0 (∏ i, c i ^ ν i) = ∏ i, x i ^ ν i := by
      intro ν
      subst hc
      simp [map_prod, map_pow]
    simp only [hm] at h
    unfold HS
    simpa using h
  have p2 : ∀ S T : MvPowerSeries σ K, Bdd S → Bdd T →
      ev (S + T) x = ev S x + ev T x ∧ ev (S - T) x = ev S x - ev T x ∧
        ev (S * T) x = ev S x * ev T x := by
    intro S T hS hT
    obtain ⟨h1, h2, h3⟩ := R.1 S T hS hT
    simp only [E'] at h1 h2 h3
    exact ⟨by simpa using congrArg MvPowerSeries.constantCoeff h1,
      by simpa using congrArg MvPowerSeries.constantCoeff h2,
      by simpa using congrArg MvPowerSeries.constantCoeff h3⟩
  have p3 : ∀ a : K, ev (MvPowerSeries.C a : MvPowerSeries σ K) x = a := by
    intro a
    have h := R.2.1 a
    rw [E'] at h
    exact Cinj _ _ h
  have p4 : ∀ i, ev (MvPowerSeries.X i : MvPowerSeries σ K) x = x i := by
    intro i
    have h := R.2.2.1 i
    rw [E'] at h
    exact Cinj _ _ (h.trans (by rw [hc]))
  have p5 : ∀ S : MvPowerSeries σ K, Intg S → ‖ev S x‖ ≤ 1 ∧ (Small S → ‖ev S x‖ < 1) := by
    intro S hS
    have hSB : Bdd S := (B.2.2.1 S 0).2.2 hS
    have hI := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ Unit c S hcs hSB).2.2.1 hS
    rw [E'] at hI
    refine ⟨by simpa using hI 0, fun hSm => ?_⟩

    set c0 := MvPowerSeries.constantCoeff S with hc0d
    have hc0 : ‖c0‖ ≤ 1 := by simpa [hc0d] using hS 0
    have hCI : Intg (MvPowerSeries.C c0 : MvPowerSeries σ K) := (B.2.2.2.1 c0).2.1 hc0
    have hCB : Bdd (MvPowerSeries.C c0 : MvPowerSeries σ K) := (B.2.2.2.1 c0).1
    have hT : Intg (S - MvPowerSeries.C c0) := (B.1 S _ hS hCI).2.1
    have hT0 : MvPowerSeries.constantCoeff (S - MvPowerSeries.C c0) = 0 := by simp [hc0d]
    have hTB : Bdd (S - MvPowerSeries.C c0) := (B.2.2.1 _ 0).2.2 hT
    have hsm := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ Unit c _ hcs hTB).2.2.2 hT hT0
    rw [E'] at hsm
    have hlt : ‖ev (S - MvPowerSeries.C c0) x‖ < 1 := by simpa using hsm.2
    have hadd : ev S x = ev (S - MvPowerSeries.C c0) x + c0 := by
      have h := (p2 (S - MvPowerSeries.C c0) _ hTB hCB).1
      rw [sub_add_cancel, p3] at h
      exact h
    have hlt0 : ‖c0‖ < 1 := hSm.2
    calc ‖ev S x‖ = ‖ev (S - MvPowerSeries.C c0) x + c0‖ := by rw [← hadd]
      _ ≤ max ‖ev (S - MvPowerSeries.C c0) x‖ ‖c0‖ := IsUltrametricDist.norm_add_le_max _ _
      _ < 1 := max_lt hlt hlt0
  have p6 : ∀ (ρ : Type) [Fintype ρ] (s : ρ → MvPowerSeries σ K) (S : MvPowerSeries ρ K),
      (∀ j, Small (s j)) → Bdd S → ev (csub s S) x = ev S (fun j => ev (s j) x) := by
    intro ρ _ s S hs hS
    have h := (GlobalTheory.T.mvPowerSeriesConvergentSubst_assoc K ρ σ Unit s c S hs hcs hS).2
    have hf : (fun j => csub c (s j)) = fun j => (MvPowerSeries.C (ev (s j) x) : MvPowerSeries Unit K) :=
      funext fun j => E' (s j)
    rw [hf, E'] at h
    exact Cinj _ _ (h.trans (E ρ S (fun j => ev (s j) x)))
  have small0 : ∀ a : MvPowerSeries σ K, Intg a → MvPowerSeries.constantCoeff a = 0 → Small a := by
    intro a ha ha0
    show Intg a ∧ ‖MvPowerSeries.constantCoeff a‖ < 1
    exact ⟨ha, by rw [ha0]; simp⟩
  have p7 : ∀ (ρ : Type) [Fintype ρ] (a : ρ → MvPowerSeries σ K) (S : MvPowerSeries ρ K),
      (∀ j, Intg (a j)) → (∀ j, MvPowerSeries.constantCoeff (a j) = 0) → Bdd S →
        ev (MvPowerSeries.subst a S) x = ev S (fun j => ev (a j) x) := by
    intro ρ _ a S ha ha0 hS
    rw [← (GlobalTheory.T.convergentSubst_oneVariable_and_formal_agreement K).2.2.2.2.2.1 ρ σ a S ha0]
    exact p6 ρ a S (fun j => small0 _ (ha j) (ha0 j)) hS
  have p8 : ∀ (a : MvPowerSeries σ K) (f : PowerSeries K), Intg a →
      MvPowerSeries.constantCoeff a = 0 → Bdd f → ev (f.subst a) x = ev1 f (ev a x) := by
    intro a f ha ha0 hf
    rw [← (GlobalTheory.T.convergentSubst_oneVariable_and_formal_agreement K).2.2.2.2.2.2 σ a f ha0, (GlobalTheory.T.convergentSubst_oneVariable_and_formal_agreement K).1 σ a f,
      (GlobalTheory.T.convergentSubst_oneVariable_and_formal_agreement K).2.1 f (ev a x)]
    exact p6 Unit (fun _ => a) f (fun _ => small0 a ha ha0) hf
  exact ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩

end GlobalTheory.ConvSer
end

open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeriesEvalTsum_openPolydisc_properties : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (σ : Type) [Fintype σ] (x : σ → K), (∀ i, ‖x i‖ < 1) → (∀ S : MvPowerSeries σ K, Bdd S → HS S x (ev S x)) ∧ (∀ S T : MvPowerSeries σ K, Bdd S → Bdd T → ev (S + T) x = ev S x + ev T x ∧ ev (S - T) x = ev S x - ev T x ∧ ev (S * T) x = ev S x * ev T x) ∧ (∀ a : K, ev (MvPowerSeries.C a : MvPowerSeries σ K) x = a) ∧ (∀ i, ev (MvPowerSeries.X i : MvPowerSeries σ K) x = x i) ∧ (∀ S : MvPowerSeries σ K, Intg S → ‖ev S x‖ ≤ 1 ∧ (Small S → ‖ev S x‖ < 1)) ∧ (∀ (ρ : Type) [Fintype ρ] (s : ρ → MvPowerSeries σ K) (S : MvPowerSeries ρ K), (∀ j, Small (s j)) → Bdd S → ev (csub s S) x = ev S (fun j => ev (s j) x)) ∧ (∀ (ρ : Type) [Fintype ρ] (a : ρ → MvPowerSeries σ K) (S : MvPowerSeries ρ K), (∀ j, Intg (a j)) → (∀ j, MvPowerSeries.constantCoeff (a j) = 0) → Bdd S → ev (MvPowerSeries.subst a S) x = ev S (fun j => ev (a j) x)) ∧ (∀ (a : MvPowerSeries σ K) (f : PowerSeries K), Intg a → MvPowerSeries.constantCoeff a = 0 → Bdd f → ev (f.subst a) x = ev1 f (ev a x)) := by
  atlas_forward_decl GlobalTheory.ConvSer.ev_algebra
end
