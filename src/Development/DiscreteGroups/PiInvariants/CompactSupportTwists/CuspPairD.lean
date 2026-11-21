import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.UniformInitialGrowth.InitBnd
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ContinuousPA
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.OnlyIsotropic
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiClosT
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RSplitCore2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeL2InnerProduct
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PPrAut
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CuspRapidDecayGL.CuspRapidDecaySiegelGL
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero

section
set_option linter.all false

noncomputable section

open NumberField Matrix
open GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic
  GroundTheory.Automorphic.Reduction
open PositivityTheory.Rg.BcB PositivityTheory.Rg.Rs.JInitBnd

namespace DiscreteGroups.T1.G.CP

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [abs_le]; constructor <;> linarith [le_abs_self a, le_abs_self b, neg_abs_le a, neg_abs_le b]

theorem abs_add_le_abs_add_abs (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  rw [abs_le]; constructor <;> linarith [le_abs_self a, le_abs_self b, neg_abs_le a, neg_abs_le b]

theorem lAbs_mul (x y : GA E n) : logAbs (x * y).val.det = logAbs x.val.det + logAbs y.val.det := by
  rw [Units.val_mul, Matrix.det_mul]
  exact (D1.logAbsBasic E).2.1 _ _ (Matrix.isUnits_det_units x) (Matrix.isUnits_det_units y)


theorem lAbs_one : logAbs (1 : GA E n).val.det = 0 := by
  have h := lAbs_mul (E := E) (n := n) 1 1
  rw [mul_one] at h
  linarith

theorem lAbs_pow (k : GA E n) (m : ℕ) : logAbs (k ^ m).val.det = m * logAbs k.val.det := by
  induction m with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul]; exact lAbs_one
  | succ m ih => rw [pow_succ, lAbs_mul, ih]; push_cast; ring

theorem eq_zero_of_nat_mul_le {a C : ℝ} (h : ∀ m : ℕ, (m : ℝ) * |a| ≤ C) : a = 0 := by
  by_contra ha
  have hpos : 0 < |a| := abs_pos.2 ha
  obtain ⟨m, hm⟩ := exists_nat_gt (C / |a|)
  have h1 := h m
  have h2 : C / |a| * |a| < m * |a| := mul_lt_mul_of_pos_right hm hpos
  rw [div_mul_cancel₀ _ hpos.ne'] at h2
  linarith

theorem lAbs_maxCompact {k : GA E n} (hk : k ∈ maxCompact (K := E) (n := n)) : logAbs k.val.det = 0 := by
  obtain ⟨C, hC⟩ := (isCompact_maxCompact (K := E) (n := n)).exists_bound_of_continuousOn
    (DiscreteGroups.T1.G.continuous_logAbs_det (E := E) (n := n)).continuousOn
  refine eq_zero_of_nat_mul_le (C := C) fun m => ?_
  have h := hC (k ^ m) (pow_mem hk m)
  rw [Real.norm_eq_abs, lAbs_pow, abs_mul, Nat.abs_cast] at h
  exact h





theorem coord_bound (ℓ : Fin n → ℝ) (hn : 0 < n) (t₀ S : ℝ) (ht : ∀ r, -t₀ ≤ PositivityTheory.Rg.Rs.An.sr ℓ r)
    (hS : |∑ i, ℓ i| ≤ S) (i : Fin n) :
    |ℓ i| ≤ S + 2 * (∑ r ∈ Finset.range n, PositivityTheory.Rg.Rs.An.sr ℓ r + 2 * (n : ℝ) * t₀) := by
  have hc0 : n - 1 < n := by omega
  set c := ℓ ⟨n - 1, hc0⟩ with hcdef
  set x' : Fin n → ℝ := fun j => ℓ j - c with hx'
  have hsr : ∀ r, PositivityTheory.Rg.Rs.An.sr x' r = PositivityTheory.Rg.Rs.An.sr ℓ r := fun r => by
    unfold PositivityTheory.Rg.Rs.An.sr; split_ifs <;> simp [hx']
  have hx'' : ∀ r, -t₀ ≤ PositivityTheory.Rg.Rs.An.sr x' r := fun r => (hsr r).symm ▸ ht r
  have hlast : ∀ j : Fin n, (j : ℕ) + 1 = n → x' j = 0 := fun j hj => by
    have hj' : j = ⟨n - 1, hc0⟩ := Fin.ext (by simp only; omega)
    simp only [hx', hcdef, hj', sub_self]
  have hS' : ∑ r ∈ Finset.range n, PositivityTheory.Rg.Rs.An.sr x' r = ∑ r ∈ Finset.range n, PositivityTheory.Rg.Rs.An.sr ℓ r :=
    Finset.sum_congr rfl fun r _ => hsr r
  set B := ∑ r ∈ Finset.range n, PositivityTheory.Rg.Rs.An.sr ℓ r + 2 * (n : ℝ) * t₀ with hB
  have hB0 : 0 ≤ B := bound_nonneg ℓ t₀ ht
  have hb : ∀ j, |ℓ j - c| ≤ B := fun j => by
    have h := abs_le_bound x' t₀ hx'' hlast j
    rw [hS'] at h
    exact h
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hS0 : 0 ≤ S := (abs_nonneg _).trans hS
  have e : (n : ℝ) * c = ∑ j, ℓ j - ∑ j, (ℓ j - c) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have h1 : |∑ j, (ℓ j - c)| ≤ n * B := by
    calc _ ≤ ∑ j, |ℓ j - c| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n, B := Finset.sum_le_sum fun j _ => hb j
      _ = n * B := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : |(n : ℝ) * c| ≤ S + n * B := by
    rw [e]
    exact (abs_sub_le_abs_add_abs _ _).trans (add_le_add hS h1)
  rw [abs_mul, abs_of_pos hnpos] at h2
  have h3 : (n : ℝ) * |c| ≤ n * (S + B) := by nlinarith [mul_nonneg (sub_nonneg.2 hn1) hS0]
  have hc : |c| ≤ S + B := le_of_mul_le_mul_left h3 hnpos
  calc |ℓ i| = |(ℓ i - c) + c| := by rw [sub_add_cancel]
    _ ≤ |ℓ i - c| + |c| := abs_add_le_abs_add_abs _ _
    _ ≤ B + (S + B) := add_le_add (hb i) hc
    _ = S + 2 * B := by ring

end DiscreteGroups.T1.G.CP

end
end

section
set_option linter.all false

noncomputable section

open NumberField Matrix
open GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic
  GroundTheory.Automorphic.Reduction
open PositivityTheory.Rg.BcB PositivityTheory.Rg.Rs.JInitBnd
open scoped Pointwise

namespace DiscreteGroups.T1.G.CP

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}


end DiscreteGroups.T1.G.CP

end
end

section
set_option linter.all false

noncomputable section

open NumberField Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped Pointwise

namespace DiscreteGroups.T1.G.CP

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}



end DiscreteGroups.T1.G.CP

end
end

section
noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def OrthLie : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0)
  (π : CuspSub E n), ThetaFix π → ∀ φ : Sm E n, IsAutForm φ → Orth D π φ → ∀ X, Orth D π (act (Op.lie X) φ)

theorem countable_GL (m : ℕ) : Countable (GL (Fin m) E) := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have : Countable (Matrix (Fin m) (Fin m) E) := inferInstanceAs (Countable (Fin m → Fin m → E))
  exact Function.Injective.countable (f := (Units.val : GL (Fin m) E → Matrix (Fin m) (Fin m) E)) fun a b hab => Units.ext hab

theorem countable_ratH : Countable (ratH E n 0) := by
  have := countable_GL (E := E) n
  have := countable_GL (E := E) 0
  show Countable ((ratGL E n).prodMap (ratGL E 0)).range
  exact (MonoidHom.rangeRestrict_surjective ((ratGL E n).prodMap (ratGL E 0))).countable











end DiscreteGroups.T1.G

end
end

section
noncomputable section

set_option linter.all false

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc GlobalTheory.ExpDeriv

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

def PairBd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0)
  (ψ φ : Sm E n) (u : ℝ → ℂ) (Ω : Set (GA E n)), IsCuspForm ψ → (∀ t g, ψ.1 (splitCentre E n t * g) = ψ.1 g) →
  IsAutForm φ → Continuous u → HasCompactSupport u → IsCompact Ω →
  ∃ C : ℝ, (∀ x : H E n 0, ∀ y ∈ Ω, ∀ y' ∈ Ω, ‖ψ.1 (x.1 * y) * u (ldet x) * φ.1 (x.1 * y')‖ ≤ C) ∧
    D.ν {x | u (ldet x) ≠ 0} < ⊤

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem cont_infGL : Continuous (infGL E n) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf E : Cinf E → Ad E) := (continuous_infEq E).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)



theorem major_one (v : ℝ → ℂ) {M R : ℝ} (hM : ∀ x, ‖v x‖ ≤ M) (hR : tsupport v ⊆ Metric.closedBall 0 R) (c : ℝ)
    {R' M' : ℝ} (hRR : R ≤ R') (hMM : M ≤ M') (hM0 : 0 ≤ M') (s t : ℝ) (ht : |t| ≤ 1) :
    ‖v (s + t * c)‖ ≤ M' * max 0 (min 1 (R' + |c| + 1 - |s|)) := by
  by_cases h : s + t * c ∈ tsupport v
  · have h1 := hR h
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
    have h2 : |t * c| ≤ |c| := by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) ht
    obtain ⟨a1, a2⟩ := abs_le.1 h1
    obtain ⟨b1, b2⟩ := abs_le.1 h2
    have h3 : |s| ≤ R' + |c| := abs_le.2 ⟨by linarith, by linarith⟩
    rw [min_eq_left (by linarith), max_eq_right zero_le_one, mul_one]
    exact (hM _).trans hMM
  · have h0 : v (s + t * c) = 0 := by
      by_contra hne
      exact h (subset_tsupport _ (Function.mem_support.2 hne))
    rw [h0, norm_zero]
    exact mul_nonneg hM0 (le_max_left _ _)

theorem exists_major (v₁ v₂ : ℝ → ℂ) (h₁ : Continuous v₁) (h₂ : Continuous v₂) (s₁ : HasCompactSupport v₁)
    (s₂ : HasCompactSupport v₂) (c : ℝ) : ∃ w : ℝ → ℝ, Continuous w ∧ HasCompactSupport w ∧ (∀ s, 0 ≤ w s) ∧
      ∀ s t, |t| ≤ 1 → ‖v₁ (s + t * c)‖ ≤ w s ∧ ‖v₂ (s + t * c)‖ ≤ w s := by
  obtain ⟨M₁, hM₁⟩ := h₁.bounded_above_of_compact_support s₁
  obtain ⟨M₂, hM₂⟩ := h₂.bounded_above_of_compact_support s₂
  obtain ⟨R₁, hR₁⟩ := s₁.isCompact.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨R₂, hR₂⟩ := s₂.isCompact.isBounded.subset_closedBall (0 : ℝ)
  set R := max R₁ R₂
  set M := max M₁ 0 + max M₂ 0
  have hM0 : 0 ≤ M := add_nonneg (le_max_right _ _) (le_max_right _ _)
  refine ⟨fun s => M * max 0 (min 1 (R + |c| + 1 - |s|)), ?_, ?_, ?_, ?_⟩
  · exact continuous_const.mul (continuous_const.max (continuous_const.min (continuous_const.sub continuous_abs)))
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (R + |c| + 1)) fun s hs => ?_
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at hs
    have : min 1 (R + |c| + 1 - |s|) ≤ 0 := (min_le_right _ _).trans (by linarith)
    simp only [max_eq_left this, mul_zero]
  · exact fun s => mul_nonneg hM0 (le_max_left _ _)
  · intro s t ht
    exact ⟨major_one v₁ hM₁ hR₁ c (le_max_left _ _) ((le_max_left _ _).trans (le_add_of_nonneg_right (le_max_right _ _)))
        hM0 s t ht,
      major_one v₂ hM₂ hR₂ c (le_max_right _ _) ((le_max_left _ _).trans (le_add_of_nonneg_left (le_max_right _ _)))
        hM0 s t ht⟩

theorem pt_bd {a b v : ℂ} {s k C : ℝ} (hs : 0 ≤ s) (hk : 0 ≤ k) (hv : ‖v‖ ≤ k * s)
    (h : ‖a * ((s : ℝ) : ℂ) * b‖ ≤ C) : ‖star (a * v) * b‖ ≤ k * C ∧ (s = 0 → star (a * v) * b = 0) := by
  have e : ‖a * ((s : ℝ) : ℂ) * b‖ = ‖a‖ * s * ‖b‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
  have h1 : ‖star (a * v) * b‖ ≤ k * (‖a‖ * s * ‖b‖) := by
    rw [norm_mul, norm_star, norm_mul]
    calc ‖a‖ * ‖v‖ * ‖b‖ ≤ ‖a‖ * (k * s) * ‖b‖ := by gcongr
      _ = k * (‖a‖ * s * ‖b‖) := by ring
  refine ⟨h1.trans (mul_le_mul_of_nonneg_left (by rw [← e]; exact h) hk), fun h0 => ?_⟩
  rw [h0] at h1
  simp only [mul_zero, zero_mul] at h1
  exact norm_le_zero_iff.1 h1




end DiscreteGroups.T1.G

end
end

section
set_option linter.all false

noncomputable section

open NumberField Matrix MeasureTheory Set
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped ENNReal Pointwise

namespace DiscreteGroups.T1.G.CP

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def bump (R : ℝ) (s : ℝ) : ℂ := ((max 0 (min 1 (R + 1 - |s|)) : ℝ) : ℂ)

theorem continuous_bump (R : ℝ) : Continuous (bump R) :=
  Complex.continuous_ofReal.comp (continuous_const.max (continuous_const.min (continuous_const.sub continuous_abs)))

theorem hasCompactSupport_bump (R : ℝ) : HasCompactSupport (bump R) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(R + 1)) (b := R + 1)) fun s hs => ?_
  have h : R + 1 < |s| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at hs
    rcases hs with h | h
    · have := neg_abs_le s; linarith
    · have := le_abs_self s; linarith
  simp only [bump]
  rw [max_eq_left (min_le_of_right_le (by linarith)), Complex.ofReal_zero]

theorem norm_bump_eq_one {R s : ℝ} (hs : |s| ≤ R) : ‖bump R s‖ = 1 := by
  simp only [bump]
  rw [min_eq_left (by linarith), max_eq_right zero_le_one, Complex.ofReal_one, norm_one]

theorem cp_vol (hn : 1 ≤ n) (D : Dom E n 0) (R : ℝ) : D.ν {x | |ldet x| ≤ R} < ⊤ := by
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E n (muG D)
  obtain ⟨K, hK, hKs⟩ := tsum_shift_le (bump R) (continuous_bump R) (hasCompactSupport_bump R) _
    (lg_e_pos (E := E) hn)
  have hS : MeasurableSet {x : H E n 0 | |ldet x| ≤ R} := by
    haveI := borelSpace_H (E := E) (n := n)
    exact (isClosed_le (continuous_abs.comp continuous_ldet) continuous_const).measurableSet
  have h1 : D.ν {x | |ldet x| ≤ R} ≤ ∫⁻ x, ‖bump R (lg x.1)‖ₑ ^ (2 : ℝ) ∂D.ν := by
    rw [← lintegral_indicator_one hS]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ {x : H E n 0 | |ldet x| ≤ R}
    · rw [indicator_of_mem hx, Pi.one_apply, ← ofReal_norm_eq_enorm, norm_bump_eq_one (s := lg x.1) hx,
        ENNReal.ofReal_one, ENNReal.one_rpow]
    · rw [indicator_of_notMem hx]
      exact zero_le
  have h2 : ∫⁻ x, ‖bump R (lg x.1)‖ₑ ^ (2 : ℝ) ∂D.ν =
      ∫⁻ g in stdDom (ratGL E n).range, ‖bump R (lg g)‖ₑ ^ (2 : ℝ) ∂muG D :=
    lintegral_nu D (fun g => ‖bump R (lg g)‖ₑ ^ (2 : ℝ)) fun γ hγ g => by rw [lg_rat_mul γ hγ g]
  have h3 : ∫⁻ g in stdDom (ratGL E n).range, ‖bump R (lg g)‖ₑ ^ (2 : ℝ) ∂muG D =
      ∫⁻ q, ∑' m : ℤ, ‖bump R (lg q.out + m * lg (splitCentre E n 1))‖ₑ ^ (2 : ℝ)
        ∂quotMeasure (latticeGL E n) (muG D) := by
    have h := lintegral_unfold (muG D) hn (fun _ => 1) (by intro _ _ _; rfl) aemeasurable_const
      (fun s => ‖bump R s‖ₑ ^ (2 : ℝ)) ((continuous_bump R).measurable.enorm.pow_const _)
    simpa only [one_mul] using h
  calc D.ν {x | |ldet x| ≤ R} ≤ _ := h1
    _ = _ := h2
    _ = _ := h3
    _ ≤ ∫⁻ _q, K ∂quotMeasure (latticeGL E n) (muG D) := lintegral_mono fun q => hKs _
    _ < ⊤ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top hK.lt_top (measure_lt_top _ _)




end DiscreteGroups.T1.G.CP

end
end
