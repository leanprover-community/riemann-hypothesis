import Formalism.SharpRestriction.CuspSpanNormBounds.HCFiniteKMultiplicityGapped
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FamilyDegreeRatioOfL2Uniqueness

section
open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.S.Pv.DegI

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.BridgeLemma Formalism.MainNotions.PlaceDegreeData

theorem frob_eq_sqrt_hs {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : frob M = Real.sqrt (Formalism.REAL.hs M) := by
  unfold frob Formalism.REAL.hs
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_norm_sq]

theorem continuous_frob {n : ℕ} : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => frob M) := by
  unfold frob
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))

theorem gap_near {N : ℕ} {ε : Fin N → Bool} {lam ν : Fin N → ℝ} {G ρ : ℝ} (hG : GapAtLeast ε lam G)
    (hν : l1dist ν lam ≤ ρ) : GapAtLeast ε ν (G - 2 * ρ) := by
  intro a b hab
  have h1 := hG a b hab
  have hco : ∀ j, |ν j - lam j| ≤ ρ := fun j =>
    le_trans (Finset.single_le_sum (f := fun j => |ν j - lam j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)) hν
  have h2 := hco a
  have h3 := hco b
  have h4 : |lam a - lam b| ≤ |ν a - ν b| + |ν a - lam a| + |ν b - lam b| := by
    have e : lam a - lam b = (ν a - ν b) - (ν a - lam a) + (ν b - lam b) := by ring
    rw [e]
    exact le_trans (abs_add_le _ _) (by have := abs_sub (ν a - ν b) (ν a - lam a); linarith)
  linarith

section Rec

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

variable [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOneG] in

theorem lowK_fd (hlam : IsHCParam lam) {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsDS ε lam σ) {h : ℝ}
    (hgap : GapAtLeast ε lam h) (hth : Formalism.MainNotions.GapDS.thrDS ε < h) : FiniteDimensional ℂ (lowKSub ε lam σ) := by
  obtain ⟨S, hS⟩ := hσ.2.2.2.2.2.1
  have hset : {S' | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S'} = {S} := by
    ext S'
    constructor
    · intro h'
      exact BridgeDS3.lowest_K_type_mult_one_gapped n ε lam H σ hlam hσ h hgap hth S' S h' hS
    · intro h'
      rw [Set.mem_singleton_iff] at h'
      rw [h']
      exact hS
  have e : lowKSub ε lam σ = S := by
    unfold lowKSub
    rw [hset, sSup_singleton]
  rw [e]
  exact hS.1

variable [Fact Formalism.MainNotions.BridgeCPX.HCMultDSG] [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOneG] in

theorem memLp_frob_coef (D0 : Formalism.BasicNotions.D7) (hDec : DiscreteSeriesDecayBound D0) (hlam : IsHCParam lam)
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsDS ε lam σ) {h : ℝ} (hgap : GapAtLeast ε lam h)
    (hh : 200 * (n : ℝ) ^ 3 ≤ h) (hpos : 1 ≤ min (pOf ε) (qOf ε)) {v w : H} (hv : IsKFin ε σ v)
    (hw : IsKFin ε σ w) :
    MemLp (fun g : Formalism.REAL.UJ ε => (frob (umat g) : ℂ) * coefOn σ v w g) 2 (Formalism.REAL.muG ε) := by
  obtain ⟨s, hcs⟩ := L1.exists_sign ε
  set q0 : ℕ := min (pOf ε) (qOf ε) with hq0
  have hqn : q0 ≤ n := hcs ▸ L1.card_SgIx_le ε s
  have hn1 : 1 ≤ n := le_trans hpos hqn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hqR : (1 : ℝ) ≤ q0 := by exact_mod_cast hpos
  have hqnR : (q0 : ℝ) ≤ n := by exact_mod_cast hqn
  have hn3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hnR
  have hh0 : 0 ≤ h := le_trans (by positivity) hh

  have hth : Formalism.MainNotions.GapDS.thrDS ε < h := by
    have := Formalism.MainNotions.GapDS.thrDS_le ε
    linarith
  have h120 : 120 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h := by
    rw [← hq0]
    have e1 : (q0 : ℝ) ^ ((3 : ℝ) / 2) ≤ (n : ℝ) ^ (2 : ℕ) := by
      calc (q0 : ℝ) ^ ((3 : ℝ) / 2) ≤ (q0 : ℝ) ^ ((2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hqR (by norm_num)
        _ = (q0 : ℝ) ^ (2 : ℕ) := by rw [← Real.rpow_natCast]; norm_num
        _ ≤ (n : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ (by linarith) hqnR 2
    calc 120 * (n : ℝ) * (q0 : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (n : ℝ) * (n : ℝ) ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_left e1 (by positivity)
      _ = 120 * (n : ℝ) ^ 3 := by ring
      _ ≤ h := by linarith

  have := lowK_fd hlam hσ hgap hth
  have hE : IsOrthProjOnto (lowKSub ε lam σ).starProjection (lowKSub ε lam σ) :=
    ⟨(lowKSub ε lam σ).isIdempotentElem_starProjection,
      fun x y => Submodule.inner_starProjection_left_eq_right _ x y, Submodule.range_starProjection _⟩
  obtain ⟨w0, hw0⟩ := exists_highest_weight_unit ε lam σ hσ
  have hlow : IsLowUnit ε lam σ w0 := ⟨hw0.1, hw0.2.1⟩
  have hw00 : w0 ≠ 0 := by
    intro h0
    have := hw0.1
    rw [h0, norm_zero] at this
    norm_num at this

  set A : ℝ := h / (8 * Real.sqrt (2 * (q0 : ℝ))) with hA
  set C0 : ℝ := Real.sqrt n ^ A * Real.exp (A / Real.sqrt (2 * (q0 : ℝ))) with hC0
  have hsq0 : 0 < Real.sqrt (2 * (q0 : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hC00 : 0 ≤ C0 := by rw [hC0]; positivity
  have hdec : ∀ g : Formalism.REAL.UJ ε, ‖⟪w0, σ (umat g) w0⟫_ℂ‖ ≤ C0 * Real.sqrt (Formalism.REAL.hs (umat g)) ^ (-A) := by
    intro g
    have := poly_decay_of_decay_statement D0 hDec n ε lam hlam H σ hσ _ hE h hgap h120 hpos w0 hlow (umat g) g.2
    rw [← hq0] at this
    exact this

  have hU := hσ.2.2.1
  have hadm := BridgeCPX.HCAdmDSG_of_mult BridgeDS3.HC_finite_K_multiplicity_gapped n ε lam H σ hlam hσ h hgap hth
  obtain ⟨Cf, hCf⟩ := BridgeCPX.kfin_decay_UJ hU hσ.2.2.2.1 hadm hw00 hA0 hC00 hdec hv hw [] []
    (by simp) (by simp)
  have hbd : ∀ g : Formalism.REAL.UJ ε, ‖coefOn σ v w g‖ ≤ Cf * Real.sqrt (Formalism.REAL.hs (umat g)) ^ (-A) := fun g =>
    hCf (umat g) g.2

  have hA1 : (n : ℝ) * q0 + 2 ≤ A := by
    have hs2 : Real.sqrt (2 * (q0 : ℝ)) ≤ 2 * n := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    rw [hA, le_div_iff₀ (by positivity)]
    have e1 : ((n : ℝ) * q0 + 2) * (8 * Real.sqrt (2 * (q0 : ℝ))) ≤ ((n : ℝ) * n + 2) * (8 * (2 * n)) := by
      apply mul_le_mul (by nlinarith) (by linarith) (by positivity) (by positivity)
    have e2 : ((n : ℝ) * n + 2) * (8 * (2 * n)) ≤ 200 * (n : ℝ) ^ 3 := by nlinarith
    linarith
  have hnq : 0 ≤ (n : ℝ) * q0 := by positivity
  have hA1' : 1 ≤ A := by linarith

  set F : Formalism.REAL.UJ ε → ℂ := fun g => (frob (umat g) : ℂ) * coefOn σ v w g with hF
  have hFc : Continuous F := by
    have h1 : Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) v :=
      (hU.2.2 v).comp_continuous (Formalism.REAL.continuous_coeMatrix ε) (fun g => g.2)
    have h2 : Continuous fun g : Formalism.REAL.UJ ε => coefOn σ v w g := continuous_const.inner h1
    exact (Complex.continuous_ofReal.comp (continuous_frob.comp (Formalism.REAL.continuous_coeMatrix ε))).mul h2
  have hs1 : ∀ g : Formalism.REAL.UJ ε, 1 ≤ Formalism.REAL.hs (umat g) := fun g => one_le_hilbert_schmidt_of_mem ε _ g.2 ⟨0, by omega⟩

  have hFb : ∀ g : Formalism.REAL.UJ ε, ‖F g‖ ^ 2 ≤ Cf ^ 2 * Formalism.REAL.hs (umat g) ^ (1 - A) := by
    intro g
    set B : ℝ := Formalism.REAL.hs (umat g) with hB
    have hB1 : 1 ≤ B := hs1 g
    have hB0 : 0 < B := by linarith
    have hsB : 0 < Real.sqrt B := Real.sqrt_pos.2 hB0
    have hc := hbd g
    rw [← hB] at hc
    have hc0 : 0 ≤ ‖coefOn σ v w g‖ := norm_nonneg _
    have hCf0 : 0 ≤ Cf * Real.sqrt B ^ (-A) := le_trans hc0 hc
    have hnF : ‖F g‖ = Real.sqrt B * ‖coefOn σ v w g‖ := by
      simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs, frob_eq_sqrt_hs, ← hB,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [hnF, mul_pow, Real.sq_sqrt hB0.le]
    have e1 : ‖coefOn σ v w g‖ ^ 2 ≤ (Cf * Real.sqrt B ^ (-A)) ^ 2 := pow_le_pow_left₀ hc0 hc 2
    have e2 : (Cf * Real.sqrt B ^ (-A)) ^ 2 = Cf ^ 2 * B ^ (-A) := by
      rw [mul_pow, ← Real.rpow_natCast (Real.sqrt B ^ (-A)), ← Real.rpow_mul hsB.le, Real.sqrt_eq_rpow,
        ← Real.rpow_mul hB0.le]
      congr 2
      push_cast
      ring
    have e3 : B * (Cf ^ 2 * B ^ (-A)) = Cf ^ 2 * B ^ (1 - A) := by
      rw [sub_eq_add_neg, Real.rpow_add hB0, Real.rpow_one]
      ring
    calc B * ‖coefOn σ v w g‖ ^ 2 ≤ B * (Cf ^ 2 * B ^ (-A)) := by
          rw [← e2]; exact mul_le_mul_of_nonneg_left e1 hB0.le
      _ = Cf ^ 2 * B ^ (1 - A) := e3

  set M : ℝ := max (Cf ^ 2) 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM0 : 0 < M := by linarith
  have hCM : Cf ^ 2 ≤ M := le_max_left _ _
  set f : Formalism.REAL.UJ ε → ℂ := fun g => ((‖F g‖ ^ 2 / M : ℝ) : ℂ) with hf
  have hfc : Continuous f := Complex.continuous_ofReal.comp ((hFc.norm.pow 2).div_const M)
  have hfle : ∀ g, ‖F g‖ ^ 2 / M ≤ Formalism.REAL.hs (umat g) ^ (1 - A) := by
    intro g
    rw [div_le_iff₀ hM0]
    have hp : 0 ≤ Formalism.REAL.hs (umat g) ^ (1 - A) := Real.rpow_nonneg (by linarith [hs1 g]) _
    calc ‖F g‖ ^ 2 ≤ Cf ^ 2 * Formalism.REAL.hs (umat g) ^ (1 - A) := hFb g
      _ ≤ M * Formalism.REAL.hs (umat g) ^ (1 - A) := mul_le_mul_of_nonneg_right hCM hp
      _ = Formalism.REAL.hs (umat g) ^ (1 - A) * M := by ring
  have hfn : ∀ g, ‖f g‖ = ‖F g‖ ^ 2 / M := by
    intro g
    simp only [hf, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  have hone : ∀ g, ‖f g‖ ≤ 1 := by
    intro g
    rw [hfn]
    exact (hfle g).trans (Real.rpow_le_one_of_one_le_of_nonpos (hs1 g) (by linarith))
  have hint : Integrable f (Formalism.REAL.muG ε) := by
    refine L1.integrable_of_decay ε s f hfc hone (2 * (A - 1)) ?_ (fun g hg => ?_)
    · rw [hcs]
      push_cast
      linarith
    · have hG0 : 0 < Formalism.REAL.hsG g := lt_trans (by positivity) hg
      have hn0 : (0 : ℝ) < n := by linarith
      have hx0 : 0 < Formalism.REAL.hsG g / n := div_pos hG0 hn0
      refine ⟨Real.log (Formalism.REAL.hsG g / n) / 2, ?_, ?_⟩
      · rw [show 2 * (Real.log (Formalism.REAL.hsG g / n) / 2) = Real.log (Formalism.REAL.hsG g / n) by ring,
          Real.exp_log hx0]
        rw [mul_div_cancel₀ _ hn0.ne']
      · have hgeq : Formalism.REAL.hsG g = Formalism.REAL.hs (umat g) := rfl
        rw [hfn]
        refine (hfle g).trans ?_
        set t : ℝ := Real.log (Formalism.REAL.hsG g / n) / 2 with ht
        have e2 : (n : ℝ) ^ (1 - A) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hnR (by linarith)
        have e3 : (Formalism.REAL.hsG g / n) ^ (1 - A) = Real.exp (-(2 * (A - 1) * t)) := by
          rw [Real.rpow_def_of_pos hx0, ht]
          congr 1
          ring
        have e0 : Formalism.REAL.hs (umat g) = n * (Formalism.REAL.hsG g / n) := by
          rw [← hgeq]; field_simp
        calc Formalism.REAL.hs (umat g) ^ (1 - A) = (n * (Formalism.REAL.hsG g / n)) ^ (1 - A) := by rw [e0]
          _ = (n : ℝ) ^ (1 - A) * (Formalism.REAL.hsG g / n) ^ (1 - A) := Real.mul_rpow hn0.le hx0.le
          _ ≤ 1 * (Formalism.REAL.hsG g / n) ^ (1 - A) :=
              mul_le_mul_of_nonneg_right e2 (Real.rpow_nonneg hx0.le _)
          _ = Real.exp (-(2 * (A - 1) * t)) := by rw [one_mul, e3]
  have hsq : Integrable (fun g => ‖F g‖ ^ 2) (Formalism.REAL.muG ε) := by
    have h1 := (hint.re).const_mul M
    refine h1.congr (Filter.Eventually.of_forall fun g => ?_)
    have e : (f g).re = ‖F g‖ ^ 2 / M := by rw [hf]; exact Complex.ofReal_re _
    show M * (f g).re = ‖F g‖ ^ 2
    rw [e]
    field_simp
  exact (memLp_two_iff_integrable_sq_norm hFc.aestronglyMeasurable).2 hsq

end Rec

end Formalism.MainNotions.S.Pv.DegI

end
end

section
noncomputable section

namespace Formalism.MainNotions.S.Pv.DegI

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma Formalism.MainNotions.BridgeLemma₂ Formalism.MainNotions.PlaceDegreeData MeasureTheory
open scoped InnerProductSpace ENNReal

theorem size_gap (D : D7) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT ρ : ℝ} (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCL : 1 ≤ Cl * large₂.sc.L) (hρ : 2 * ρ + 2 ≤ (D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) :
    200 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L - 2 * ρ := by
  rw [nS_cast D]
  have hN6 : (6 : ℝ) ≤ (D.R.r : ℝ) := six_le_n D
  set N : ℝ := (D.R.r : ℝ) with hN
  have hmf : D.R.m ^ 4 ≤ D.R.f := by unfold StandingHypotheses at hH; exact hH.2.2.1
  have hf : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have h2 := D.R.two_le_m
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    exact_mod_cast le_trans this hmf
  have hf5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ hf
  have hmn : (D.R.m : ℝ) ≤ N := by
    have : D.R.m ≤ D.R.r := by
      have := D.R.m_add_three_le_k
      simp only [Ranks.r]; omega
    rw [hN]; exact_mod_cast this
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hm10 : (D.R.m : ℝ) ^ 10 ≤ N ^ 10 := pow_le_pow_left₀ hm0 hmn 10
  have hG : N ^ 19 ≤ Cl * N ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    have e6 : N ^ 19 ≤ N ^ 19 * (D.R.f : ℝ) ^ 5 := le_mul_of_one_le_right (by positivity) hf5
    have e7 : N ^ 19 * (D.R.f : ℝ) ^ 5 ≤ (Cl * large₂.sc.L) * (N ^ 19 * (D.R.f : ℝ) ^ 5) :=
      le_mul_of_one_le_left (by positivity) hCL
    have e8 : Cl * N ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L = (Cl * large₂.sc.L) * (N ^ 19 * (D.R.f : ℝ) ^ 5) := by ring
    rw [e8]; linarith
  have h8 : (200 : ℝ) ≤ N ^ 8 := by
    have : (6 : ℝ) ^ 8 ≤ N ^ 8 := pow_le_pow_left₀ (by norm_num) hN6 8
    norm_num at this
    linarith
  have hX : (1 : ℝ) ≤ N ^ 3 := one_le_pow₀ (by linarith)
  have e1 : N * (D.R.m : ℝ) ^ 10 ≤ N ^ 3 * N ^ 8 := by
    calc N * (D.R.m : ℝ) ^ 10 ≤ N * N ^ 10 := mul_le_mul_of_nonneg_left hm10 (by linarith)
      _ = N ^ 3 * N ^ 8 := by ring
  have e2 : N ^ 19 = N ^ 3 * N ^ 8 * N ^ 8 := by ring
  have e4 : N ^ 3 * N ^ 8 * 200 ≤ N ^ 3 * N ^ 8 * N ^ 8 := mul_le_mul_of_nonneg_left h8 (by positivity)
  have e5 : 200 * N ^ 3 ≤ 199 * (N ^ 3 * N ^ 8) := by nlinarith
  linarith

theorem minpq_pos (D : D7) : 1 ≤ min (pOf (epsSH D.R)) (qOf (epsSH D.R)) := by
  have hk1 : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hq : min (PlaceDegreeData.pOf (epsSH D.R)) (PlaceDegreeData.qOf (epsSH D.R)) = D.R.rS + 1 := by
    rw [← epsilon_signature_eq D, negative_count_of_sign_pattern _ _ hk1]
    exact min_eq_right (positive_count_of_sign_pattern _ _ hk1)
  rw [hq]; omega

variable [Fact Formalism.MainNotions.BridgeCPX.HCMultDSG] [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOneG] in

theorem degree_L2_of_decay (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ) (hCL : 1 ≤ Cl * large₂.sc.L)
    (hm : 2 * max Cn 0 + 8 ≤ (D.R.m : ℝ)) (h30 : PlaceDegreeData.DiscreteSeriesDecayBound D) : DegreeL2RangeHypothesis D large₂ C' Cl Cg cb Cu cT CT C0 Cn := by
  intro hH τ ν hν hl H _ _ _ σ hDS v w hv hw
  have hc0 : 0 ≤ max Cn 0 := le_max_right _ _
  have hcn : Cn ≤ max Cn 0 := le_max_left _ _
  have hm8 : (8 : ℝ) ≤ D.R.m := by linarith
  have hm1 : (1 : ℝ) ≤ D.R.m := by linarith
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hkr := Formalism.MainNotions.BridgeLemma.k_le_r D
  have hrk : (D.R.r : ℝ) ≤ 2 * D.R.k := by
    have h3 := D.R.m_add_three_le_k
    have : D.R.r ≤ 2 * D.R.k := by unfold Ranks.r; omega
    exact_mod_cast this
  have hr1 : (1 : ℝ) ≤ D.R.r := by
    have h : 1 ≤ D.R.r := by
      have := D.R.two_le_m
      unfold Ranks.r
      omega
    exact_mod_cast h
  have hm3 : (D.R.m : ℝ) ≤ (D.R.m : ℝ) ^ 3 := by
    calc (D.R.m : ℝ) = (D.R.m : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (D.R.m : ℝ) ^ 3 := pow_le_pow_right₀ hm1 (by norm_num)
  have hN : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = D.R.r := deg_cast_r D
  have hN2 : 2 * (D.R.r : ℝ) ≤ D.R.k * (D.R.m : ℝ) ^ 3 := by nlinarith
  have hcard : ∀ J : Finset (Fin (2 * D.R.rS + D.R.k + 1)), (J.card : ℝ) ≤ D.R.r := by
    intro J
    rw [← hN]
    have : J.card ≤ 2 * D.R.rS + D.R.k + 1 := by
      have := Finset.card_le_univ J
      rwa [Fintype.card_fin] at this
    exact_mod_cast this
  have hρ : 2 * ((Cn + 1) * D.R.k * (D.R.m : ℝ) ^ 3) + 2 ≤ (D.R.r : ℝ) * (D.R.m : ℝ) ^ 10 := by
    have hm30 : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 3 := by positivity
    have hm31 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 3 := one_le_pow₀ hm1
    have hm6 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 6 := one_le_pow₀ hm1
    have e1 : (Cn + 1) * D.R.k * (D.R.m : ℝ) ^ 3 ≤ (max Cn 0 + 1) * D.R.r * (D.R.m : ℝ) ^ 3 := by
      have : (Cn + 1) * D.R.k ≤ (max Cn 0 + 1) * D.R.r :=
        mul_le_mul (by linarith) hkr hk0 (by linarith)
      exact mul_le_mul_of_nonneg_right this hm30
    have e2 : (1 : ℝ) ≤ D.R.r * (D.R.m : ℝ) ^ 3 := by nlinarith
    calc 2 * ((Cn + 1) * D.R.k * (D.R.m : ℝ) ^ 3) + 2
        ≤ (D.R.r : ℝ) * ((D.R.m : ℝ) ^ 3 * (2 * max Cn 0 + 4)) := by nlinarith
      _ ≤ (D.R.r : ℝ) * ((D.R.m : ℝ) ^ 3 * (D.R.m : ℝ)) := by gcongr; linarith
      _ = (D.R.r : ℝ) * ((D.R.m : ℝ) ^ 3 * (D.R.m : ℝ) * 1) := by ring
      _ ≤ (D.R.r : ℝ) * ((D.R.m : ℝ) ^ 3 * (D.R.m : ℝ) * (D.R.m : ℝ) ^ 6) := by gcongr
      _ = (D.R.r : ℝ) * (D.R.m : ℝ) ^ 10 := by ring
  have e : (Cn + 1) * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 = Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.k * (D.R.m : ℝ) ^ 3 := by ring
  have hkm : (0 : ℝ) ≤ D.R.k * (D.R.m : ℝ) ^ 3 := by positivity
  have hl' : l1dist ν (lamD D τ) ≤ (Cn + 1) * D.R.k * (D.R.m : ℝ) ^ 3 := by rw [e]; linarith
  have hg := gap_near (szh_gap hH.1 τ) hl'
  exact memLp_frob_coef D h30 hν hDS hg (size_gap D large₂ hH.1 hCL hρ) (minpq_pos D) hv hw

variable [Fact Formalism.MainNotions.BridgeCPX.HCMultDSG] [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOneG] in

theorem family_degree_L2_of_decay {eps : ℝ} (Fm : FamP eps) (hCl : 1 ≤ sCl Fm) (h30 : PlaceDegreeData.FamilyDiscreteSeriesDecay Fm) :
    ∀ Cg cb Cu cT CT C0, deg_L2F Fm Cg cb Cu cT CT C0 := by
  intro Cg cb Cu cT CT C0 Cn
  obtain ⟨x1, _, h1⟩ := ev_m Fm (2 * max Cn 0 + 8)
  refine ⟨x1, fun x hx i => degree_L2_of_decay _ _ _ _ _ _ _ _ _ _ Cn ?_ (h1 x hx i) (h30 x i)⟩
  have hL : 1 ≤ (Fm.L x i).sc.L :=
    Real.one_le_rpow (le_of_lt (Fm.L x i).sc.one_lt_alt) (le_of_lt (Fm.L x i).sc.eps_pos)
  exact one_le_mul_of_one_le_of_one_le hCl hL

variable [Fact Formalism.MainNotions.BridgeLemma₂.deg_DSUniqG] in
theorem up_G (D : D7) (h18 : OnePlaceEstimates.adm18 D) (h90 : OnePlaceEstimates.FormalDegreeRatioAlt D) {W : LocW D.R.k D.R.rS}
    {μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} (I : Finset (Fin (2 * D.R.rS + D.R.k + 1)))
    (hgap : ∀ J : Finset (Fin (2 * D.R.rS + D.R.k + 1)), AllGaps (μ + epsI J) 2)
    (hL2 : ∀ J : Finset (Fin (2 * D.R.rS + D.R.k + 1)), IsHCParam (μ + epsI J) → ∀ (H : Type) [NormedAddCommGroup H]
      [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)),
      IsDS (epsSH D.R) (μ + epsI J) σ → ∀ v w : H, IsKFin (epsSH D.R) σ v → IsKFin (epsSH D.R) σ w →
        MemLp (fun g : Formalism.REAL.UJ (epsSH D.R) => (frob (umat g) : ℂ) * coefOn σ v w g) 2 (Formalism.REAL.muG (epsSH D.R)))
    (hUq : ∃ hb : ℝ, GapAtLeast (epsSH D.R) (μ + epsI I) hb ∧ Formalism.MainNotions.GapDS.thrDS (epsSH D.R) < hb)
    {A A' : LocS W} (hA : GoodS D μ A) (hA' : GoodS D (μ + epsI I) A') :
    A'.deg / A.deg = fdegHC (μ + epsI I) / fdegHC μ := by
  obtain ⟨P, hDS, hf⟩ := deg_datum D hA
  obtain ⟨P', hDS', hf'⟩ := deg_datum D hA'
  have hv0 : A.v0 ≠ 0 := hA.2.2.2.2.2.1
  have hc : (0 : ℝ) < ((D.s.cdScale _ (epsSH D.R) : NNReal) : ℝ) := by exact_mod_cast D.s.cdScale_pos _ _
  have hd := formal_degree_pos D hA
  obtain ⟨H, i1, i2, i3, σ, v, hv, hDSe, hr⟩ := deg_chain D h18 h90 hA.1 hgap hL2 A.H _ hDS A.v0 hv0
    (by rw [hf _ hv0]; positivity) I hA'.1
  obtain ⟨hb, hgb, hthb⟩ := hUq
  obtain ⟨U, hUi⟩ := BridgeDS3.discrete_series_unique_gapped _ (epsSH D.R) (μ + epsI I) H A'.H σ _ hA'.1 hDSe hDS' hb hgb hthb
  have hUv : U v ≠ 0 := fun h0 => hv (U.map_eq_zero_iff.1 h0)
  rw [deg_fdegOf_equiv _ σ _ U hUi v, hf' _ hUv, hf _ hv0, mul_div_mul_left _ _ hc.ne'] at hr
  exact hr

end Formalism.MainNotions.S.Pv.DegI

end
end
