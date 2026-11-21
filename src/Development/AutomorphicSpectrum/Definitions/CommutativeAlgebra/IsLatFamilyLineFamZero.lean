import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod

namespace GlobalTheory.CompanionTheory.Ar.Num.QuotModel

open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles GlobalTheory.CompanionTheory.Ar.Num

section General

variable {o : Type*} [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁]
  [AddCommGroup V₂] [Module Ω V₂]




def idGraph (A B' : (∀ k, ι k) → AddSubgroup V) : (∀ k, ι k) → AddSubgroup (V × V) := fun s =>
  (A s).comap (AddMonoidHom.fst V V) ⊓
    (B' s).comap (AddMonoidHom.snd V V - AddMonoidHom.fst V V)

theorem mem_idGraph {A B' : (∀ k, ι k) → AddSubgroup V} {s} {v w : V} :
    (v, w) ∈ idGraph A B' s ↔ v ∈ A s ∧ w - v ∈ B' s := by
  simp [idGraph, AddSubgroup.mem_comap]





theorem quotEquiv_symm {x : (Σ k, ι k) → Ω} {A A' : (∀ k, ι k) → AddSubgroup V}
    {B B' : (∀ k, ι k) → AddSubgroup V₁} (h : QuotEquiv o x A A' B B') :
    QuotEquiv o x B B' A A' := by
  obtain ⟨Γ, ⟨hΓ, h1⟩, h2⟩ := h
  refine ⟨fun s => (Γ s).comap (AddEquiv.prodComm : V₁ × V ≃+ V × V₁).toAddMonoidHom,
    ⟨⟨fun s hs a ha ⟨w, v⟩ h => hΓ.1 s hs a ha (v, w) h,
      fun s t hs ht ⟨w, v⟩ h => hΓ.2 s t hs ht (v, w) h⟩, fun s hs => ⟨fun w v h => ?_, ?_, ?_, ?_⟩⟩,
    fun s hs => ⟨fun w h => ?_, ?_⟩⟩
  · exact ((h1 s hs).1 v w h).symm
  · exact (h2 s hs).2
  · exact fun v => ⟨(h2 s hs).1 v, (h1 s hs).2.2.2 v⟩
  · exact fun w hw => ((h1 s hs).2.2.1 w).2 hw
  · exact ((h1 s hs).2.2.1 w).1 h
  · exact (h1 s hs).2.1

theorem le_of_quotEquiv_zero {x : (Σ k, ι k) → Ω} {A A' : (∀ k, ι k) → AddSubgroup V}
    {B : (∀ k, ι k) → AddSubgroup V₁} (h : QuotEquiv o x A A' B B) {s} (hs : mseg x s ≠ 0) :
    A s ≤ A' s := by
  obtain ⟨Γ, ⟨-, h1⟩, h2⟩ := h
  intro v hv
  obtain ⟨w, hw⟩ := (h1 s hs).2.1 v hv
  have h0 := ((h1 s hs).2.2.1 w).2 ((h1 s hs).1 v w hw).2
  exact (h2 s hs).1 v (by simpa using sub_mem hw h0)

def lineFam (o : Type*) [CommRing o] [Algebra o Ω] (x : (Σ k, ι k) → Ω) (u : Ω) (a : K → ℤ) :
    (∀ k, ι k) → AddSubgroup Ω := fun s =>
  (chartRing o (mseg x) s).toSubring.toAddSubgroup.map (AddMonoidHom.mulRight (u * chartMon x s a))

theorem isLine_lineFam (x : (Σ k, ι k) → Ω) (u : Ω) (a : K → ℤ) :
    IsLine o x u a (lineFam o x u a) := by
  intro s _ v
  simp only [lineFam, AddSubgroup.mem_map]
  exact ⟨fun ⟨r, hr, h⟩ => ⟨r, hr, h.symm⟩, fun ⟨r, hr, h⟩ => ⟨r, hr, h.symm⟩⟩




end General

section Line

variable {o : Type*} [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]

def pt (t : Ω) : (Σ _ : Unit, Fin 2) → Ω := fun p => ![1, t] p.2

theorem mseg_pt (t : Ω) (s : Unit → Fin 2) : mseg (pt t) s = ![1, t] (s ()) := by
  simp [mseg, pt]

theorem chartMon_pt (t : Ω) (s : Unit → Fin 2) (a : Unit → ℤ) :
    chartMon (pt t) s a = ![1, t] (s ()) ^ a () := by
  simp [chartMon, pt]

theorem t_mem (t : Ω) : t ∈ chartRing o (mseg (pt t)) (fun _ => 0) := by
  simpa [mseg_pt] using div_mem_chartRing (o := o) (mseg (pt t)) (fun _ => 0) (fun _ => 1)


theorem chart_cases (s : Unit → Fin 2) : s = (fun _ => 0) ∨ s = fun _ => 1 := by
  have : s = fun _ => s () := rfl
  rw [this]
  generalize s () = i
  fin_cases i <;> simp


theorem exists_poly_zero {t a : Ω} (ha : a ∈ chartRing o (mseg (pt t)) (fun _ => 0)) :
    ∃ P : Polynomial o, Polynomial.aeval t P = a := by
  have : chartRing o (mseg (pt t)) (fun _ => 0) ≤ (Polynomial.aeval t).range := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨s, rfl⟩
    rcases chart_cases s with rfl | rfl
    · exact ⟨1, by simp [mseg_pt]⟩
    · exact ⟨Polynomial.X, by simp [mseg_pt]⟩
  exact this ha

theorem exists_poly_one {t a : Ω} (ht : t ≠ 0) (ha : a ∈ chartRing o (mseg (pt t)) (fun _ => 1)) :
    ∃ P : Polynomial o, Polynomial.aeval t⁻¹ P = a := by
  have : chartRing o (mseg (pt t)) (fun _ => 1) ≤ (Polynomial.aeval t⁻¹).range := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨s, rfl⟩
    rcases chart_cases s with rfl | rfl
    · exact ⟨Polynomial.X, by simp [mseg_pt]⟩
    · exact ⟨1, by simp [mseg_pt, ht]⟩
  exact this ha

open Polynomial in
theorem dvd_of_overlap {t : Ω} (ht0 : t ≠ 0) (ht : Function.Injective (aeval (R := o) t)) (ϖ : o)
    (G D Z : o[X]) (m : ℕ)
    (h : t ^ m * aeval t⁻¹ G = aeval t D * (t ^ m * t) + algebraMap o Ω ϖ * aeval t Z) :
    C ϖ ∣ G := by
  set k := G.natDegree
  letI : Invertible t⁻¹ := invertibleOfNonzero (inv_ne_zero ht0)
  have hr := eval₂_reflect_mul_pow (algebraMap o Ω) t⁻¹ k G le_rfl
  rw [invOf_eq_inv, inv_inv, ← aeval_def, ← aeval_def] at hr
  have hp : reflect k G * X ^ m = D * X ^ (m + k + 1) + C ϖ * (Z * X ^ k) := by
    apply ht
    simp only [map_mul, map_add, map_pow, aeval_X, aeval_C]
    have : aeval t (reflect k G) = aeval t⁻¹ G * t ^ k := by
      rw [← hr, mul_assoc, ← mul_pow, inv_mul_cancel₀ ht0, one_pow, mul_one]
    rw [this]
    linear_combination t ^ k * h
  rw [C_dvd_iff_dvd_coeff]
  intro i
  by_cases hi : i ≤ k
  · have := congrArg (fun P => coeff P (k - i + m)) hp
    simp only [coeff_mul_X_pow, coeff_add, coeff_C_mul, coeff_reflect] at this
    rw [coeff_mul_X_pow', if_neg (by omega), zero_add, revAt_le (by omega),
      show k - (k - i) = i by omega] at this
    exact ⟨_, this⟩
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    exact dvd_zero _

open Polynomial in

theorem not_trivFlagMod_one {ϖ : o} (hϖ : ¬ IsUnit ϖ) {t : Ω} (ht0 : t ≠ 0)
    (ht : Function.Injective (aeval (R := o) t)) (ht' : Function.Injective (aeval (R := o) t⁻¹))
    {N : ℕ} (b : Fin (N + 1) → Unit → ℤ) (hb : b 0 () = 1) :
    ¬ TrivFlagMod o ϖ (pt t) (N + 1) b := by
  rintro ⟨g, h1, h2⟩
  have n0 : mseg (pt t) (fun _ => 0) ≠ 0 := by simp [mseg_pt]
  have n1 : mseg (pt t) (fun _ => 1) ≠ 0 := by simp [mseg_pt, ht0]
  obtain ⟨m, U, Z, -, hZ, hU, hd, -, he⟩ := h2 _ _ n1 n0
  obtain ⟨hg1, h, hh, r, hr, hdet⟩ := h1 _ n1
  have col : ∀ i, ∃ W : o[X], g (fun _ => 1) i 0 = algebraMap o Ω ϖ * aeval t⁻¹ W := by
    intro i
    obtain ⟨G, hG⟩ := exists_poly_one ht0 (hg1 i 0)
    obtain ⟨D, hD⟩ := exists_poly_zero ((h1 _ n0).1 i 0)
    obtain ⟨Z', hZ'⟩ := exists_poly_zero (hZ i 0)
    have e := congrFun (congrFun he i) 0
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.mul_apply,
      Finset.sum_eq_single 0 (fun j _ hj => by rw [hU j 0 (Fin.pos_iff_ne_zero.2 hj), mul_zero])
        (by simp), hd 0, ← hG, ← hD, ← hZ'] at e
    obtain ⟨W, hW⟩ := dvd_of_overlap ht0 ht ϖ G D Z' m
      (by simpa [mseg_pt, chartMon_pt, hb] using e)
    exact ⟨W, by rw [← hG, hW]; simp⟩
  choose W hW using col
  choose P hP using fun i j => exists_poly_one ht0 (hg1 i j)
  obtain ⟨H, hH⟩ := exists_poly_one ht0 hh
  obtain ⟨R, hR⟩ := exists_poly_one ht0 hr
  have hPW : ∀ i, P i 0 = C ϖ * W i := fun i => ht' (by rw [hP, hW]; simp)
  have hdP : (Matrix.of P).det * H = 1 + C ϖ * R := by
    apply ht'
    have : g (fun _ => 1) = (aeval t⁻¹).mapMatrix (Matrix.of P) := by
      ext i j; simp [hP]
    rw [map_mul, AlgHom.map_det, ← this, hH, hdet]
    simp [hR]
  have hdiv : C ϖ ∣ (Matrix.of P).det := by
    rw [Matrix.det_succ_column_zero]
    refine Finset.dvd_sum fun i _ => ?_
    rw [Matrix.of_apply, hPW]
    exact ((dvd_mul_right _ _).mul_left _).mul_right _
  have h1' : C ϖ ∣ (1 : o[X]) := by
    have := hdiv.mul_right H
    rw [hdP] at this
    exact (dvd_add_left (dvd_mul_right _ _)).1 this
  exact hϖ (isUnit_C.1 (isUnit_of_dvd_one h1'))




open Polynomial in

theorem not_quotEquiv_zero {ϖ : o} (hϖ : ¬ IsUnit ϖ) {t : Ω}
    (ht : Function.Injective (aeval (R := o) t)) (B : (Unit → Fin 2) → AddSubgroup Ω) :
    ¬ QuotEquiv o (pt t) (lineFam o (pt t) 1 0) (lineFam o (pt t) (algebraMap o Ω ϖ * 1) 0) B B := by
  intro h
  have n0 : mseg (pt t) (fun _ => 0) ≠ 0 := by simp [mseg_pt]
  obtain ⟨r, hr, e⟩ := le_of_quotEquiv_zero h n0
    ((isLine_lineFam (pt t) 1 0 _ n0 1).2 ⟨1, one_mem _, by simp [chartMon]⟩)
  obtain ⟨P, rfl⟩ := exists_poly_zero hr
  have : C ϖ * P = 1 := ht (by simpa [chartMon, mul_comm] using e)
  exact hϖ (isUnit_C.1 (IsUnit.of_mul_eq_one _ this))

end Line

section Concrete

open Polynomial

noncomputable def genT : FractionRing ℤ[X] := algebraMap ℤ[X] (FractionRing ℤ[X]) X





end Concrete

end GlobalTheory.CompanionTheory.Ar.Num.QuotModel
