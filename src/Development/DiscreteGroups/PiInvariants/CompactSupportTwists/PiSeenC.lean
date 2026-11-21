import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

section
set_option linter.all false

noncomputable section

open NumberField Matrix MeasureTheory Filter Set
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped ENNReal

namespace DiscreteGroups.T1.G.Dcy

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem conj_sum_mul {ι : Type*} (s : Finset ι) (c f : ι → ℂ) (U V : ℂ) :
    starRingEnd ℂ ((∑ a ∈ s, c a * f a) * U) * V = ∑ a ∈ s, starRingEnd ℂ (c a) * (starRingEnd ℂ (f a * U) * V) := by
  rw [Finset.sum_mul, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [map_mul]
  ring

theorem conj_self (w : ℂ) : starRingEnd ℂ w * w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.conj_mul']
  push_cast
  ring

theorem integrable_sq (hn : 1 ≤ n) (D : Dom E n 0) {π : CuspSub E n} (hθ : ThetaFix π) {φ : Sm E n} (hφ : φ ∈ π.V)
    (G : ℝ → ℂ) (hG : Continuous G) (R : ℝ) (hGs : ∀ s, R < |s| → G s = 0) :
    Integrable (fun x : H E n 0 => ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * G (ldet x)) D.ν := by
  obtain ⟨Cφ, hCφ0, hCφ⟩ := bdd_of_mem hθ hφ R
  obtain ⟨KG, hKG⟩ := (isCompact_Icc : IsCompact (Icc (-R) R)).exists_bound_of_continuousOn hG.continuousOn
  have hc : Continuous fun x : H E n 0 => ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * G (ldet x) :=
    (Complex.continuous_ofReal.comp ((((continuous_of_mem π hφ).comp
      (continuous_fst (X := GA E n) (Y := GA E 0))).norm).pow 2)).mul (hG.comp (continuous_ldet (E := E) (n := n)))
  refine integrable_of_ldet hn D _ hc R (Cφ ^ 2 * KG) (fun x hx => by simp [hGs _ hx]) fun x hx => ?_
  have hI : ldet x ∈ Icc (-R) R := abs_le.1 hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hCφ x hx) 2) (hKG _ hI) (norm_nonneg _) (by positivity)

theorem chi_zero_of {N : ℕ} {s : ℝ} (h : (N : ℝ) + 1 < |s|) : chi N s = 0 := chi_eq_zero h.le

theorem poly_vanish (hn : 1 ≤ n) (D : Dom E n 0) {π : CuspSub E n} (hθ : ThetaFix π) {φ : Sm E n} (hφ : φ ∈ π.V)
    (z : ℂ) (N : ℕ)
    (h : ∀ k : ℕ, ∫ x, ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * ldet x ^ k : ℝ) : ℂ) * Complex.exp (z * ldet x) ∂D.ν = 0)
    (q : Polynomial ℝ) :
    ∫ x, ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * q.eval (ldet x) : ℝ) : ℂ) * Complex.exp (z * ldet x) ∂D.ν = 0 := by
  have e : ∀ x : H E n 0, ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * q.eval (ldet x) : ℝ) : ℂ) * Complex.exp (z * ldet x) =
      ∑ k ∈ Finset.range (q.natDegree + 1), (q.coeff k : ℂ) *
        (((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * ldet x ^ k : ℝ) : ℂ) * Complex.exp (z * ldet x)) := by
    intro x
    rw [Polynomial.eval_eq_sum_range]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [e]
  rw [integral_finset_sum]
  · refine Finset.sum_eq_zero fun k _ => ?_
    rw [integral_const_mul, h k, mul_zero]
  · intro k _
    refine Integrable.const_mul ?_ _
    have hi := integrable_sq hn D hθ hφ (fun s => ((chi N s * s ^ k : ℝ) : ℂ) * Complex.exp (z * s))
      ((Complex.continuous_ofReal.comp ((continuous_chi N).mul (continuous_pow k))).mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))) ((N : ℝ) + 1)
      (fun s hs => by simp [chi_zero_of hs])
    refine hi.congr (Eventually.of_forall fun x => ?_)
    simp only
    ring

theorem sq_zero (hn : 1 ≤ n) (D : Dom E n 0) {π : CuspSub E n} (hθ : ThetaFix π) {φ : Sm E n} (hφ : φ ∈ π.V)
    (z : ℂ) (N : ℕ)
    (hpoly : ∀ q : Polynomial ℝ,
      ∫ x, ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * q.eval (ldet x) : ℝ) : ℂ) * Complex.exp (z * ldet x) ∂D.ν = 0) :
    ∫ x, ‖φ.1 x.1‖ ^ 2 * chi N (ldet x) ∂D.ν = 0 := by
  set a : ℝ := (N : ℝ) + 1 with ha
  have ha0 : 0 ≤ a := by positivity
  set B : ℝ := Real.exp (‖z‖ * a) with hB
  have hB0 : 0 < B := Real.exp_pos _
  set ε : ℝ := 1 / (4 * B) with hε
  have hε0 : 0 < ε := by positivity
  have hre : Continuous fun s : ℝ => (Complex.exp (-(z * s))).re :=
    Complex.continuous_re.comp (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg)
  have him : Continuous fun s : ℝ => (Complex.exp (-(z * s))).im :=
    Complex.continuous_im.comp (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg)
  obtain ⟨p1, hp1⟩ := exists_polynomial_near_of_continuousOn (-a) a _ hre.continuousOn ε hε0
  obtain ⟨p2, hp2⟩ := exists_polynomial_near_of_continuousOn (-a) a _ him.continuousOn ε hε0

  have hpt : ∀ s : ℝ, |s| ≤ a →
      ‖1 - (((p1.eval s : ℝ) : ℂ) + Complex.I * ((p2.eval s : ℝ) : ℂ)) * Complex.exp (z * s)‖ ≤ 1 / 2 := by
    intro s hs
    have hsI : s ∈ Icc (-a) a := abs_le.1 hs
    have h1 : ‖Complex.exp (-(z * s)) - (((p1.eval s : ℝ) : ℂ) + Complex.I * ((p2.eval s : ℝ) : ℂ))‖ ≤ 2 * ε := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      have e1 : (Complex.exp (-(z * s)) - (((p1.eval s : ℝ) : ℂ) + Complex.I * ((p2.eval s : ℝ) : ℂ))).re =
          (Complex.exp (-(z * s))).re - p1.eval s := by simp
      have e2 : (Complex.exp (-(z * s)) - (((p1.eval s : ℝ) : ℂ) + Complex.I * ((p2.eval s : ℝ) : ℂ))).im =
          (Complex.exp (-(z * s))).im - p2.eval s := by simp
      rw [e1, e2, abs_sub_comm _ (p1.eval s), abs_sub_comm _ (p2.eval s)]
      linarith [hp1 s hsI, hp2 s hsI]
    have h2 : ‖Complex.exp (z * s)‖ ≤ B := by
      rw [Complex.norm_exp, hB]
      refine Real.exp_le_exp.2 ((Complex.re_le_norm _).trans ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hs (norm_nonneg _)
    have e3 : 1 - (((p1.eval s : ℝ) : ℂ) + Complex.I * ((p2.eval s : ℝ) : ℂ)) * Complex.exp (z * s) =
        Complex.exp (z * s) * (Complex.exp (-(z * s)) - (((p1.eval s : ℝ) : ℂ) + Complex.I * ((p2.eval s : ℝ) : ℂ))) := by
      rw [mul_sub, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      ring
    rw [e3, norm_mul]
    calc ‖Complex.exp (z * s)‖ * ‖Complex.exp (-(z * s)) - (((p1.eval s : ℝ) : ℂ) + Complex.I * ((p2.eval s : ℝ) : ℂ))‖
        ≤ B * (2 * ε) := mul_le_mul h2 h1 (norm_nonneg _) hB0.le
      _ = 1 / 2 := by rw [hε]; field_simp; ring

  have hΦ := integrable_sq hn D hθ hφ (fun s => ((chi N s : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (continuous_chi N)) a (fun s hs => by simp [chi_zero_of hs])
  have hr : Integrable (fun x : H E n 0 => ‖φ.1 x.1‖ ^ 2 * chi N (ldet x)) D.ν := by
    refine hΦ.norm.congr (Eventually.of_forall fun x => ?_)
    show ‖((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) : ℝ) : ℂ)‖ = ‖φ.1 x.1‖ ^ 2 * chi N (ldet x)
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), abs_of_nonneg (chi_nonneg _ _)]
  have hT0 : 0 ≤ ∫ x, ‖φ.1 x.1‖ ^ 2 * chi N (ldet x) ∂D.ν :=
    integral_nonneg fun x => mul_nonneg (by positivity) (chi_nonneg _ _)
  set T := ∫ x, ‖φ.1 x.1‖ ^ 2 * chi N (ldet x) ∂D.ν with hT
  have hP1 := hpoly p1
  have hP2 := hpoly p2
  have hint : ∀ q : Polynomial ℝ, Integrable (fun x : H E n 0 =>
      ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * q.eval (ldet x) : ℝ) : ℂ) * Complex.exp (z * ldet x)) D.ν := fun q => by
    have hi := integrable_sq hn D hθ hφ (fun s => ((chi N s * q.eval s : ℝ) : ℂ) * Complex.exp (z * s))
      ((Complex.continuous_ofReal.comp ((continuous_chi N).mul (Polynomial.continuous q))).mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))) a
      (fun s hs => by simp [chi_zero_of hs])
    refine hi.congr (Eventually.of_forall fun x => ?_)
    simp only
    ring
  have hcomb : (T : ℂ) = ∫ x, ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) : ℝ) : ℂ) *
      (1 - (((p1.eval (ldet x) : ℝ) : ℂ) + Complex.I * ((p2.eval (ldet x) : ℝ) : ℂ)) * Complex.exp (z * ldet x)) ∂D.ν := by
    have e0 : (T : ℂ) = ∫ x, ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) : ℝ) : ℂ) ∂D.ν := by
      rw [hT, ← integral_complex_ofReal]
      simp only [Complex.ofReal_mul]
    rw [e0]
    have e1 : (∫ x, ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) : ℝ) : ℂ) *
        (1 - (((p1.eval (ldet x) : ℝ) : ℂ) + Complex.I * ((p2.eval (ldet x) : ℝ) : ℂ)) * Complex.exp (z * ldet x)) ∂D.ν) =
        (∫ x, ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) : ℝ) : ℂ) ∂D.ν) -
          ((∫ x, ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * p1.eval (ldet x) : ℝ) : ℂ) * Complex.exp (z * ldet x) ∂D.ν) +
            Complex.I * ∫ x, ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * p2.eval (ldet x) : ℝ) : ℂ) *
              Complex.exp (z * ldet x) ∂D.ν) := by
      have hΦ' : Integrable (fun x : H E n 0 => ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) : ℝ) : ℂ)) D.ν := hΦ
      have hpt2 : (fun x : H E n 0 => ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) : ℝ) : ℂ) *
          (1 - (((p1.eval (ldet x) : ℝ) : ℂ) + Complex.I * ((p2.eval (ldet x) : ℝ) : ℂ)) * Complex.exp (z * ldet x))) =
          fun x => ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) : ℝ) : ℂ) -
            (((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * p1.eval (ldet x) : ℝ) : ℂ) * Complex.exp (z * ldet x) +
              Complex.I * (((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * p2.eval (ldet x) : ℝ) : ℂ) *
                Complex.exp (z * ldet x))) := by
        funext x
        push_cast
        ring
      have hsum : Integrable (fun x : H E n 0 =>
          ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * p1.eval (ldet x) : ℝ) : ℂ) * Complex.exp (z * ldet x) +
            Complex.I * (((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * p2.eval (ldet x) : ℝ) : ℂ) *
              Complex.exp (z * ldet x))) D.ν := (hint p1).add ((hint p2).const_mul Complex.I)
      have hI2 : Integrable (fun x : H E n 0 => Complex.I * (((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) *
          ((chi N (ldet x) * p2.eval (ldet x) : ℝ) : ℂ) * Complex.exp (z * ldet x))) D.ν := (hint p2).const_mul Complex.I
      rw [hpt2, integral_sub hΦ' hsum,
        integral_add (hint p1) hI2, integral_const_mul]
    rw [e1, hP1, hP2]
    ring
  have hle : ‖(T : ℂ)‖ ≤ ∫ x, (1 / 2 : ℝ) * (‖φ.1 x.1‖ ^ 2 * chi N (ldet x)) ∂D.ν := by
    rw [hcomb]
    refine norm_integral_le_of_norm_le (hr.const_mul _) (Eventually.of_forall fun x => ?_)
    by_cases hx : |ldet x| ≤ a
    · rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), abs_of_nonneg (chi_nonneg _ _)]
      have := hpt _ hx
      have h0 : 0 ≤ ‖φ.1 x.1‖ ^ 2 * chi N (ldet x) := mul_nonneg (by positivity) (chi_nonneg _ _)
      nlinarith
    · rw [chi_zero_of (lt_of_not_ge hx)]
      simp
  rw [integral_const_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT0] at hle
  linarith

end DiscreteGroups.T1.G.Dcy

end
end

section
set_option linter.all false

noncomputable section

open NumberField Matrix MeasureTheory Filter Set
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped ENNReal Pointwise

namespace DiscreteGroups.T1.G.Dcy

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem eq_zero_of_ae (D : Dom E n 0) {π : CuspSub E n} {φ : Sm E n} (hφ : φ ∈ π.V)
    (h : ∀ᵐ x ∂D.ν, φ.1 x.1 = 0) : φ = 0 := by
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  have := D.haar.1
  haveI := D.haar.2.2.1
  have : MeasurableConstSMul (ratH E n 0) (H E n 0) := ⟨fun γ => measurable_const_mul (γ : H E n 0)⟩
  have : SMulInvariantMeasure (ratH E n 0) (H E n 0) D.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  have := countable_ratH' (E := E) (n := n)
  set Z : Set (H E n 0) := {x | φ.1 x.1 ≠ 0} with hZ
  have hφc := continuous_of_mem π hφ
  have hZo : IsOpen Z := isOpen_ne_fun (hφc.comp (continuous_fst (X := GA E n) (Y := GA E 0))) continuous_const
  have hνZ : D.ν Z = 0 := ae_iff.1 h
  have hμZF : D.μ (Z ∩ D.F) = 0 := by
    rw [← Measure.restrict_apply hZo.measurableSet]
    exact hνZ
  have hinv : ∀ γ : ratH E n 0, γ • Z = Z := by
    intro γ
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    obtain ⟨p, hp⟩ := (γ⁻¹).2
    have h1 : ((γ⁻¹ • y : H E n 0)).1 = ratGL E n p.1 * y.1 := by
      rw [Subgroup.smul_def, smul_eq_mul, Prod.fst_mul, ← hp]
      rfl
    simp only [hZ, Set.mem_setOf_eq, h1, (π.cusp φ hφ).1.left]
  have hμZ : D.μ Z = 0 := D.fd.measure_zero_of_invariant Z hinv hμZF
  have hZe : Z = ∅ := (hZo.measure_eq_zero_iff D.μ).1 hμZ
  refine Subtype.ext (funext fun g => ?_)
  by_contra hg
  have : ((g, 1) : H E n 0) ∈ Z := hg
  rw [hZe] at this
  exact this

theorem piSeen_holds : PiSeen := by
  intro E _ _ _ n hn D π hθ W hWle hWfd
  haveI := hWfd
  set r := Module.finrank ℂ W with hr
  set b := Module.finBasis ℂ W with hb
  set e : ℕ ≃ ℕ × ℕ × ℕ := (Denumerable.eqv (ℕ × ℕ × ℕ)).symm with he
  refine ⟨fun j => if h : (e j).1 < r then ((b ⟨(e j).1, h⟩ : W) : Sm E n) else 0,
    fun j s => ((chi (e j).2.1 s * s ^ (e j).2.2 : ℝ) : ℂ), fun j => ⟨?_, ?_, ?_⟩, ?_⟩
  · dsimp only
    split_ifs
    · exact hWle (b _).2
    · exact π.V.zero_mem
  · exact Complex.continuous_ofReal.comp ((continuous_chi _).mul (continuous_pow _))
  · exact (hasCompactSupport_chi_pow _ _).comp_left Complex.ofReal_zero
  intro φ hφ z hz
  have hφV : φ ∈ π.V := hWle hφ

  have hbv : ∀ (a : Fin r) (N k : ℕ), ∫ x, starRingEnd ℂ (((b a : W) : Sm E n).1 x.1 *
      ((chi N (ldet x) * ldet x ^ k : ℝ) : ℂ)) * (φ.1 x.1 * Complex.exp (z * ldet x)) ∂D.ν = 0 := by
    intro a N k
    have h := hz (e.symm (a.1, N, k))
    simp only [Equiv.apply_symm_apply, dif_pos a.2, Fin.eta] at h
    exact h
  have hrep : ∀ g, φ.1 g = ∑ a, (b.repr ⟨φ, hφ⟩ a) * ((b a : W) : Sm E n).1 g := by
    intro g
    have h := congrArg (fun w : W => ((w : Sm E n) : GA E n → ℂ) g) (b.sum_repr ⟨φ, hφ⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h.symm

  have hself : ∀ N k : ℕ, ∫ x, ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * ldet x ^ k : ℝ) : ℂ) *
      Complex.exp (z * ldet x) ∂D.ν = 0 := by
    intro N k
    have hpt : ∀ x : H E n 0, ((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) * ldet x ^ k : ℝ) : ℂ) *
        Complex.exp (z * ldet x) = ∑ a, starRingEnd ℂ (b.repr ⟨φ, hφ⟩ a) *
          (starRingEnd ℂ (((b a : W) : Sm E n).1 x.1 * ((chi N (ldet x) * ldet x ^ k : ℝ) : ℂ)) *
            (φ.1 x.1 * Complex.exp (z * ldet x))) := by
      intro x
      rw [← conj_sum_mul Finset.univ (fun a => b.repr ⟨φ, hφ⟩ a) (fun a => ((b a : W) : Sm E n).1 x.1)
        (((chi N (ldet x) * ldet x ^ k : ℝ) : ℂ)) (φ.1 x.1 * Complex.exp (z * ldet x)), ← hrep x.1,
        map_mul, Complex.conj_ofReal, ← conj_self]
      ring
    simp_rw [hpt]
    rw [integral_finset_sum]
    · refine Finset.sum_eq_zero fun a _ => ?_
      rw [integral_const_mul, hbv a N k, mul_zero]
    · intro a _
      refine Integrable.const_mul ?_ _
      exact integrable_pair hn D hθ (hWle (b a).2) hφV (fun s => ((chi N s * s ^ k : ℝ) : ℂ))
        (fun s => Complex.exp (z * s)) (Complex.continuous_ofReal.comp ((continuous_chi N).mul (continuous_pow k)))
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)) ((N : ℝ) + 1)
        (fun s hs => by simp [chi_zero_of hs])
  have hT : ∀ N : ℕ, ∫ x, ‖φ.1 x.1‖ ^ 2 * chi N (ldet x) ∂D.ν = 0 := fun N =>
    sq_zero hn D hθ hφV z N (poly_vanish hn D hθ hφV z N (hself N))
  have hae : ∀ N : ℕ, (fun x : H E n 0 => ‖φ.1 x.1‖ ^ 2 * chi N (ldet x)) =ᵐ[D.ν] 0 := by
    intro N
    have hΦ := integrable_sq hn D hθ hφV (fun s => ((chi N s : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp (continuous_chi N)) ((N : ℝ) + 1) (fun s hs => by simp [chi_zero_of hs])
    have hr : Integrable (fun x : H E n 0 => ‖φ.1 x.1‖ ^ 2 * chi N (ldet x)) D.ν := by
      refine hΦ.norm.congr (Eventually.of_forall fun x => ?_)
      show ‖((‖φ.1 x.1‖ ^ 2 : ℝ) : ℂ) * ((chi N (ldet x) : ℝ) : ℂ)‖ = ‖φ.1 x.1‖ ^ 2 * chi N (ldet x)
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), abs_of_nonneg (chi_nonneg _ _)]
    exact (integral_eq_zero_iff_of_nonneg (fun x => mul_nonneg (by positivity) (chi_nonneg _ _)) hr).1 (hT N)
  have hall : ∀ᵐ x ∂D.ν, ∀ N : ℕ, ‖φ.1 x.1‖ ^ 2 * chi N (ldet x) = 0 := ae_all_iff.2 hae
  refine eq_zero_of_ae D hφV (hall.mono fun x hx => ?_)
  have h1 := hx ⌈|ldet x|⌉₊
  rw [chi_eq_one (Nat.le_ceil _), mul_one] at h1
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)

end DiscreteGroups.T1.G.Dcy

end
end
