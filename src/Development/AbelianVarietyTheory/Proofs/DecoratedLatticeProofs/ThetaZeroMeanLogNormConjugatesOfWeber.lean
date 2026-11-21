import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignedLogMeans
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ClassMeanPeriods
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.EquidistributedConjugates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JacobiThetaHalfCharacteristic
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PeriodLatticeAgreement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsPeriodLatticeIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaZeroNorm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UniformizationHolds
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedAreaClassInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanLogPeriodConjugatesEqChowlaSelberg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIntegralPeriodElement

section
section
noncomputable section

namespace GlobalTheory.ConjLatticeCore

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

theorem conj_lattice_core :
    ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
      (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∀ ρ : M →ₐ[ℚ] ℂ,
      Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧ ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ, x ≠ 0 ∧
        lamConj M ρ (lamOf D cc δ) = lamOf D c x := by
  intro D cc δ M _ t hS ρ
  obtain ⟨hcc, hδ, hM, -⟩ := hS
  have hC := GlobalTheory.ConjLattice.containsData hM
  have hm : ∀ a : D.host.K, D.host.φ₀ (a : D.host.E) ∈ M := hC.1
  have h1 : Formalism.MainNotions.TaylorLogMetric.discr (lamOf D cc δ) = 1 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  have h2 : g2 (lamOf D cc δ) ∈ M := hM.2.1
  have h3 : g3 (lamOf D cc δ) ∈ M := hM.2.2
  have hsp := fun ρ' => GlobalTheory.ConjLattice.lamConj_spec GlobalTheory.ConjLattice.uniformization_holds M ρ'
    (lamOf D cc δ) h2 h3 h1
  refine ⟨(hsp ρ).2.2, ?_⟩
  have hfix : ∀ ρ' : M →ₐ[ℚ] ℂ, EquidistributedConjugates.FixesK D M ρ' → ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ,
      x ≠ 0 ∧ lamConj M ρ' (lamOf D cc δ) = lamOf D c x := by
    intro ρ' hρ'
    obtain ⟨cc', δ', hc', -, he⟩ := GlobalTheory.ConjCurve.galCurve_holds D cc δ ⟨hcc, hδ⟩ M ρ'
      (GlobalTheory.ConjEquidistrib.fixK_of_fixesK D M ρ' hm hρ') h2 h3 1 one_pos
    exact ⟨cc', hc'.1.1, δ', Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc' hc'.1 δ' hc'.2, he⟩
  by_cases hρ : EquidistributedConjugates.FixesK D M ρ
  · exact hfix ρ hρ
  · have hρ' : EquidistributedConjugates.FixesK D M (EquidistributedConjugates.conjEmb M ρ) :=
      (GlobalTheory.ConjEquidistrib.fixesK_conjEmb_iff D M ρ hm).2 hρ
    obtain ⟨c, hc, x, hx, hxe⟩ := hfix _ hρ'
    have hUI : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.UniqInv :=
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.uniqInv_of_lat Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.latOfDiscr_holds
        GlobalTheory.ConjLattice.uniformization_holds
    have hmap : (lamConj M ρ (lamOf D cc δ)).map GlobalTheory.ConjLattice.cj =
        lamConj M (EquidistributedConjugates.conjEmb M ρ) (lamOf D cc δ) := by
      apply hUI
      · rw [GlobalTheory.ConjLattice.discr_map_cj, (hsp ρ).2.2, map_one]; exact one_ne_zero
      · rw [GlobalTheory.ConjLattice.eisenstein_g_two_map_conj, (hsp ρ).1, (hsp _).1]; exact (EquidistributedConjugates.conjEmb_apply _ _ _).symm
      · rw [GlobalTheory.ConjLattice.eisenstein_g_three_map_conj, (hsp ρ).2.1, (hsp _).2.1]; exact (EquidistributedConjugates.conjEmb_apply _ _ _).symm
    have hback : lamConj M ρ (lamOf D cc δ) =
        (lamConj M (EquidistributedConjugates.conjEmb M ρ) (lamOf D cc δ)).map GlobalTheory.ConjLattice.cj := by
      rw [← hmap, GlobalTheory.ConjLattice.map_cj_map_cj]
    refine ⟨c.map (GlobalTheory.ConjLattice.conjO D), ?_, starRingEnd ℂ x, (map_ne_zero _).2 hx,
      by rw [hback, hxe, GlobalTheory.ConjLattice.lamOf_map_cj]⟩
    intro hbot
    rw [Ideal.map_eq_bot_iff_of_injective (GlobalTheory.ConjLattice.conjO D).injective] at hbot
    exact hc hbot

end GlobalTheory.ConjLatticeCore
end
end

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateIdealLattice_discr_one_homothetic_ideal : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∀ ρ : M →ₐ[ℚ] ℂ, Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧ ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ, x ≠ 0 ∧ lamConj M ρ (lamOf D cc δ) = lamOf D c x := by
  atlas_forward_decl GlobalTheory.ConjLatticeCore.conj_lattice_core
end

section
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

noncomputable section

namespace GlobalTheory.MeanLogArea

theorem mean_log_area : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)))) / (Module.finrank ℚ M : ℝ) = Real.log Real.pi + ClassMeanPeriods.classMeanValue D := by
  intro D cc δ M _ t hS
  obtain ⟨hcc, hδ, hM, -⟩ := hS
  have hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have hmean := GlobalTheory.PeriodMean.mean_log_period D (GlobalTheory.InducedType.induced_type D).1 cc δ hc M
    hM.2.1 hM.2.2
  have hpos : ∀ ρ : M →ₐ[ℚ] ℂ, 0 < area (lamConj M ρ (lamOf D cc δ)) :=
    fun ρ => GlobalTheory.Glob.area_lamConj_pos hc hM ρ
  have hcard : (Fintype.card (M →ₐ[ℚ] ℂ) : ℝ) = (Module.finrank ℚ M : ℝ) := by
    exact_mod_cast AlgHom.card ℚ M ℂ
  have hn : (Module.finrank ℚ M : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := M)).ne'
  have hsplit : (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)))) =
      (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)) / Real.pi)) +
        (Fintype.card (M →ₐ[ℚ] ℂ) : ℝ) * Real.log Real.pi := by
    rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Real.log_div (hpos ρ).ne' Real.pi_pos.ne']
    ring
  rw [hsplit, add_div, hcard, mul_div_cancel_left₀ _ hn]
  unfold ClassMeanPeriods.classMeanValue
  rw [hmean]
  ring

end GlobalTheory.MeanLogArea
end
end

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mean_log_covolume_conjugateLattices_eq : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ (lamOf D cc δ)))) / (Module.finrank ℚ M : ℝ) = Real.log Real.pi + ClassMeanPeriods.classMeanValue D := by
  atlas_forward_decl GlobalTheory.MeanLogArea.mean_log_area
end

section
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

noncomputable section

namespace GlobalTheory.IntegralXCore

theorem exists_integral_theta_ratio : PeriodLatticeAgreement.LatticePeriodEta → ThetaConstantWeber.ThetaWeberStatement → ∀ (D : D7), Formalism.MainNotions.GL3Theta.admJ D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∃ X : M, X ≠ 0 ∧ IsIntegral ℤ (X : ℂ) ∧ ∀ (ρ : M →ₐ[ℚ] ℂ) (ω₁ τ : ℂ), ω₁ ≠ 0 → 0 < τ.im → JacobiThetaHalfCharacteristic.IsPeriodLattice (lamConj M ρ (lamOf D cc δ)) ω₁ τ → ∀ a b : Fin 2, JacobiThetaHalfCharacteristic.IsEvenChar a b → JacobiThetaHalfCharacteristic.thetaChar a b (t ρ / ω₁) τ = 0 → ‖ρ X‖ = (‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ / ‖ModularForm.eta τ‖) ^ 12 := by
  intro hL hT D hJ cc δ M _ t hS
  obtain ⟨e, g, hg, hval, hρ⟩ := GlobalTheory.T.halfPeriod_weierstrassValue_mem_conj D cc δ M t hS
  have crv : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ := ⟨hS.1, hS.2.1⟩
  have hYρ : ∀ ρ : M →ₐ[ℚ] ℂ, ρ ((12 * e ^ 2 - g) / 4) =
      (12 * Formalism.MainNotions.StandardLatticesGL3.wpF (lamConj M ρ (lamOf D cc δ)) (t ρ) ^ 2 - g2 (lamConj M ρ (lamOf D cc δ))) / 4 := by
    intro ρ
    obtain ⟨-, h2, -, h4⟩ := hρ ρ
    rw [h2, h4]
    simp only [map_div₀, map_sub, map_mul, map_pow, map_ofNat]
  obtain ⟨d0, -, n0, -⟩ := hρ M.val
  have h20 := (hS.2.2.2 M.val).1
  have hY0 : (((12 * e ^ 2 - g) / 4 : M) : ℂ) =
      (12 * Formalism.MainNotions.StandardLatticesGL3.wpF (lamOf D cc δ) (t M.val) ^ 2 - g2 (lamOf D cc δ)) / 4 := by
    have h := hYρ M.val
    rw [hval] at h
    exact h
  rw [hval] at d0 n0 h20
  obtain ⟨L, hLL⟩ := (GlobalTheory.ThetaConj.isLat_lamOf crv).exists_periodPair
  obtain ⟨ω, τ, hω, hτ⟩ := GlobalTheory.exists_lattice_eq_mul_tau L
  have hP : JacobiThetaHalfCharacteristic.IsPeriodLattice (lamOf D cc δ) ω (τ : ℂ) := fun x => by
    rw [hLL, hτ]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨n, m, by ring⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨n, m, by ring⟩
  obtain ⟨a, b, hab, hz⟩ := GlobalTheory.IntegralX.exists_char hω hP (hT τ).2.1 h20 n0
  obtain ⟨hne, s, hs, hX⟩ := GlobalTheory.IntegralX.modulus hL hT _ ω τ _ hω hP d0 h20 n0 a b hab hz
  rw [← hY0] at hne hX
  have hYne : ((12 * e ^ 2 - g) / 4 : M) ≠ 0 := fun h => hne (by rw [h]; simp)
  refine ⟨1 / ((12 * e ^ 2 - g) / 4) ^ 3, one_div_ne_zero (pow_ne_zero _ hYne), ?_, ?_⟩
  · have e1 : ((1 / ((12 * e ^ 2 - g) / 4) ^ 3 : M) : ℂ) = 1 / (((12 * e ^ 2 - g) / 4 : M) : ℂ) ^ 3 := by
      push_cast
      rfl
    rw [e1, hX]
    exact GlobalTheory.IntegralX.integral hT _ ω τ hω hP d0 (hJ cc δ hS.1 hS.2.1) a b hab s hs
  · intro ρ ω₁ τ' hω₁ hτ' hP' a' b' hab' hz'
    obtain ⟨dρ, -, nρ, -⟩ := hρ ρ
    obtain ⟨-, s', hs', hX'⟩ := GlobalTheory.IntegralX.modulus hL hT _ ω₁ ⟨τ', hτ'⟩ (t ρ) hω₁ hP' dρ
      (hS.2.2.2 ρ).1 nρ a' b' hab' hz'
    rw [map_div₀, map_one, map_pow, hYρ, hX']
    have hs1 : ‖s'‖ = 1 := by rcases hs' with rfl | rfl <;> simp
    rw [norm_mul, hs1, one_mul, norm_pow, norm_div]

end GlobalTheory.IntegralXCore
end
end

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_thetaEta_twelfth_power_conjugates : PeriodLatticeAgreement.LatticePeriodEta → ThetaConstantWeber.ThetaWeberStatement → ∀ (D : D7), Formalism.MainNotions.GL3Theta.admJ D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∃ X : M, X ≠ 0 ∧ IsIntegral ℤ (X : ℂ) ∧ ∀ (ρ : M →ₐ[ℚ] ℂ) (ω₁ τ : ℂ), ω₁ ≠ 0 → 0 < τ.im → JacobiThetaHalfCharacteristic.IsPeriodLattice (lamConj M ρ (lamOf D cc δ)) ω₁ τ → ∀ a b : Fin 2, JacobiThetaHalfCharacteristic.IsEvenChar a b → JacobiThetaHalfCharacteristic.thetaChar a b (t ρ / ω₁) τ = 0 → ‖ρ X‖ = (‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ / ‖ModularForm.eta τ‖) ^ 12 := by
  atlas_forward_decl GlobalTheory.IntegralXCore.exists_integral_theta_ratio
end

section
section
noncomputable section

namespace GlobalTheory.Theta0MeanCore

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke
open scoped nonZeroDivisors
open GlobalTheory.Theta0MeanProof (lemA lemD log_normSq log_area sum_log_nonneg bound_le_half log_d_le half_le_log_v)

theorem core (hP : PeriodLatticeAgreement.LatticePeriodEta) (hW : ThetaConstantWeber.ThetaWeberStatement) {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hth : ∀ (a b : Fin 2) (τ : ℂ), 1 / 2 ≤ τ.im → ‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ ≤ C₀)
    (D : D7) (hJ : Formalism.MainNotions.GL3Theta.admJ D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ) (hS : SignedLogMeans.HidaSetting D cc δ M t) :
    SignedLogMeans.meanLog M (lamOf D cc δ) t ≤ SignedLogMeans.bound D ∧
      SignedLogMeans.meanPosLog M (lamOf D cc δ) t ≤
        SignedLogMeans.meanLog M (lamOf D cc δ) t + ((1 / 4) * Real.log D.host.d + max 0 (2 * Real.log C₀)) := by
  classical
  have hArea := GlobalTheory.T.mean_log_covolume_conjugateLattices_eq D cc δ M t hS
  obtain ⟨X, hX0, hXi, hXρ⟩ := GlobalTheory.T.exists_integral_thetaEta_twelfth_power_conjugates hP hW D hJ cc δ M t hS
  have hInt := sum_log_nonneg M X hX0 hXi
  have hB := GlobalTheory.T.conjugateIdealLattice_discr_one_homothetic_ideal D cc δ M t hS
  have hT0 := hS.2.2.2
  set Λ := lamOf D cc δ with hΛ
  choose hdisc c hc x hx hΛeq using hB
  have hA := fun ρ => lemA D (c ρ) (hc ρ) (x ρ) (hx ρ)
  choose hstab ω τ hω hτ hLat hy1 hy2 using hA
  have hLat' : ∀ ρ, JacobiThetaHalfCharacteristic.IsPeriodLattice (lamConj M ρ Λ) (ω ρ) (τ ρ) := by
    intro ρ; rw [hΛeq ρ]; exact hLat ρ
  have htn : ∀ ρ, t ρ ∉ lamConj M ρ Λ := by
    intro ρ ht
    apply (hT0 ρ).2.1
    rw [hΛeq ρ] at ht ⊢
    exact hstab ρ _ ht
  have hNρ := fun ρ => GlobalTheory.Proof.ThetaZeroNormGlobalInterpolation.normTheta0 _ (ω ρ) (τ ρ) (t ρ) (hω ρ) (hτ ρ) (hLat' ρ) (hT0 ρ).1 (htn ρ)
  have hex : ∀ ρ, ∃ ab : Fin 2 × Fin 2, JacobiThetaHalfCharacteristic.IsEvenChar ab.1 ab.2 ∧
      JacobiThetaHalfCharacteristic.thetaChar ab.1 ab.2 (t ρ / ω ρ) (τ ρ) = 0 := fun ρ => (hNρ ρ).1.exists
  choose ab hab0 hab1 using hex
  set th : (M →ₐ[ℚ] ℂ) → ℝ := fun ρ => ‖JacobiThetaHalfCharacteristic.thetaChar (ab ρ).1 (ab ρ).2 0 (τ ρ)‖ with hthdef
  set et : (M →ₐ[ℚ] ℂ) → ℝ := fun ρ => ‖ModularForm.eta (τ ρ)‖ with hetdef
  have F1 : ∀ ρ, 0 < th ρ ∧ Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ)) =
      -(1 / 2) * Real.log 2 - (1 / 2) * Real.log (τ ρ).im - 2 * Real.log (th ρ) :=
    fun ρ => log_normSq (hNρ ρ).2.1 (hτ ρ) ((hNρ ρ).2.2 _ _ (hab0 ρ) (hab1 ρ))
  have F2 := fun ρ => log_area hP (hω ρ) (hτ ρ) (hLat' ρ) (hdisc ρ)
  have F3 : ∀ ρ, Real.log ‖ρ X‖ = 12 * (Real.log (th ρ) - Real.log (et ρ)) := by
    intro ρ
    rw [hXρ ρ (ω ρ) (τ ρ) (hω ρ) (hτ ρ) (hLat' ρ) _ _ (hab0 ρ) (hab1 ρ), Real.log_pow,
      Real.log_div (F1 ρ).1.ne' (F2 ρ).1.ne']
    push_cast; ring

  set n : ℝ := (Module.finrank ℚ M : ℝ) with hn
  have hcard : (Finset.univ : Finset (M →ₐ[ℚ] ℂ)).card = Module.finrank ℚ M := by
    rw [Finset.card_univ]; exact AlgHom.card ℚ M ℂ
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast Module.finrank_pos
  set St := ∑ ρ, Real.log (th ρ)
  set Se := ∑ ρ, Real.log (et ρ)
  set Sy := ∑ ρ, Real.log (τ ρ).im
  have e1 : ∑ ρ, Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ)) = -(1 / 2) * Real.log 2 * n - (1 / 2) * Sy - 2 * St := by
    rw [Finset.sum_congr rfl fun ρ _ => (F1 ρ).2]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, hcard, nsmul_eq_mul]
    rw [hn]; ring
  have e2 : ∑ ρ, Real.log (area (lamConj M ρ Λ)) = (Real.log 4 + 2 * Real.log Real.pi) * n + Sy + 4 * Se := by
    rw [Finset.sum_congr rfl fun ρ _ => (F2 ρ).2]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, hcard, nsmul_eq_mul]
    rw [hn]; ring
  have e3 : 0 ≤ St - Se := by
    have : ∑ ρ : M →ₐ[ℚ] ℂ, Real.log ‖ρ X‖ = 12 * (St - Se) := by
      rw [Finset.sum_congr rfl fun ρ _ => F3 ρ, ← Finset.mul_sum, Finset.sum_sub_distrib]
    linarith
  rw [e2] at hArea
  have hA2 : (Real.log 4 + 2 * Real.log Real.pi) * n + Sy + 4 * Se = (Real.log Real.pi + ClassMeanPeriods.classMeanValue D) * n := by
    rw [← hArea]; field_simp
  have hsd : 0 < Real.sqrt (D.host.d : ℝ) := Real.sqrt_pos.2 (by
    have := GlobalTheory.Theta0MeanCompare.one_le_d D; linarith)
  have hcmv : ClassMeanPeriods.classMeanValue D = Real.eulerMascheroniConstant + Real.log 2 + Real.log Real.pi -
      Real.log (Real.sqrt D.host.d) - logDerivativeAtOne D := by
    unfold ClassMeanPeriods.classMeanValue
    rw [Real.log_div (by positivity) hsd.ne', Real.log_mul two_ne_zero Real.pi_ne_zero]; ring
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  constructor
  · unfold SignedLogMeans.meanLog
    rw [div_le_iff₀ hnpos]
    change ∑ ρ, Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ)) ≤ _
    rw [e1]
    unfold SignedLogMeans.bound
    rw [hcmv, hl4] at hA2
    nlinarith
  ·
    have hK : ∀ ρ, max 0 (Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ))) ≤
        Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ)) + ((1 / 4) * Real.log D.host.d + max 0 (2 * Real.log C₀)) := by
      intro ρ
      have hd1 : 0 ≤ Real.log (D.host.d : ℝ) := Real.log_nonneg (GlobalTheory.Theta0MeanCompare.one_le_d D)
      have hm := le_max_right 0 (2 * Real.log C₀)
      have hm0 := le_max_left 0 (2 * Real.log C₀)
      have h1 := (F1 ρ).2
      have h2 : Real.log (th ρ) ≤ Real.log C₀ :=
        Real.log_le_log (F1 ρ).1 (hth _ _ _ (hy1 ρ))
      have h3 : Real.log (2 * (τ ρ).im) ≤ Real.log (Real.sqrt D.host.d) :=
        Real.log_le_log (by linarith [hτ ρ]) (hy2 ρ)
      rw [Real.log_mul two_ne_zero (hτ ρ).ne'] at h3
      have h4 : Real.log (Real.sqrt (D.host.d : ℝ)) = (1 / 2) * Real.log D.host.d := by
        rw [Real.log_sqrt (by positivity)]; ring
      apply max_le
      · change _ ≤ Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ)) + _
        rw [h1]; linarith
      · linarith
    set K := (1 / 4) * Real.log D.host.d + max 0 (2 * Real.log C₀)
    have hs := Finset.sum_le_sum fun ρ (_ : ρ ∈ (Finset.univ : Finset (M →ₐ[ℚ] ℂ))) => hK ρ
    rw [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul] at hs
    unfold SignedLogMeans.meanPosLog SignedLogMeans.meanLog
    change (∑ ρ, max 0 (Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ)))) / n ≤
      (∑ ρ, Real.log (SignedLogMeans.conjNormSq M Λ ρ (t ρ))) / n + K
    rw [div_add' _ _ _ hnpos.ne', div_le_div_iff_of_pos_right hnpos]
    rw [hn]; linarith

theorem theta0Mean (hP : PeriodLatticeAgreement.LatticePeriodEta) (hW : ThetaConstantWeber.ThetaWeberStatement) :
    SignedLogMeans.Theta0Mean := by
  have hJ : ∀ D : D7, Formalism.MainNotions.GL3Theta.admJ D := fun D =>
    (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D ⟨GlobalTheory.InducedType.restrict_K D, GlobalTheory.InducedType.sum_eq_trace D⟩).1
  obtain ⟨C₀, hC₀, hth⟩ := lemD
  set C := max 0 (2 * Real.log C₀) with hCdef
  have hC0 : 0 ≤ C := le_max_left _ _
  refine ⟨⟨fun D cc δ M _ t hS => (core hP hW hC₀ hth D (hJ D) cc δ M t hS).1,
    fun D cc δ M _ t hS L hL => ?_, ⟨1 / 2, by norm_num, fun D cc δ M _ t hS L hL => ?_⟩⟩,
    ⟨C, hC0, fun D cc δ M _ t hS => ?_⟩, ⟨1 + 2 * C, by linarith, fun D cc δ M _ t hS L hL => ?_⟩⟩
  · have := (core hP hW hC₀ hth D (hJ D) cc δ M t hS).1
    rw [GlobalTheory.Theta0MeanCompare.bound_eq] at this
    exact this.trans (GlobalTheory.Theta0MeanCompare.kronBound_le D hL)
  · exact (core hP hW hC₀ hth D (hJ D) cc δ M t hS).1.trans (bound_le_half D hL)
  · obtain ⟨h1, h2⟩ := core hP hW hC₀ hth D (hJ D) cc δ M t hS
    linarith
  · obtain ⟨h1, h2⟩ := core hP hW hC₀ hth D (hJ D) cc δ M t hS
    have a1 := bound_le_half D hL
    have a2 := log_d_le D hL
    have a3 : 1 / 2 ≤ L := by have := half_le_log_v D; have := abs_nonneg (logDerivativeAtOne D); linarith
    have a4 : C ≤ 2 * C * L := by nlinarith
    linarith

end GlobalTheory.Theta0MeanCore
end
end

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaZero_mean_log_norm_conjugates_of_weber : PeriodLatticeAgreement.LatticePeriodEta → ThetaConstantWeber.ThetaWeberStatement → SignedLogMeans.Theta0Mean := by
  atlas_forward_decl GlobalTheory.Theta0MeanCore.theta0Mean
end
