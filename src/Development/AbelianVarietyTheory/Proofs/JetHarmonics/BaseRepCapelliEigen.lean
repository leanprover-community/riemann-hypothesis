import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.Jets.TauZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSettingUniformConstantStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliKFiniteCoefficient
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselNormSqEqBigCellNormSqStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFamilyFunctionals
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsKTypeNonzeroBessel
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorMomentEstimateStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PieriTensorDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselDatumBothSidesAreSidesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FixesWedgeAndForm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilyThroughDiscreteSeries

section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_k_finite_coefficient : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (l : R.H → Wp) (l' : R.H → Wq), R.IsDS ε mu → (∀ f : Mx k r → (Wq →L[ℂ] Wp), PI.CapelliEig.IsKFinCoefT (k := k) (r := r) R.σ f → ∃ s, IsCoef R l l' f s) ∧ (∀ F s (t : ℂ), IsCoef R l l' F s → IsCoef R l l' (fun g => t • F g) (t * s)) ∧ ((∃ x ∈ R.TK, l x ≠ 0) → (∃ y ∈ R.TK, l' y ≠ 0) → ∀ s : ℂ, ∃ F, IsCoef R l l' F s) := by
  first | exact @GlobalTheory.isCoef_of_translate_smul_exists | exact GlobalTheory.isCoef_of_translate_smul_exists | (intros; apply GlobalTheory.isCoef_of_translate_smul_exists <;> assumption)
end

section
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_coef_family : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (s₀ : ℂ), IsFam lam q0 R → (haveI := FiniteDimensional.complete ℂ Wp; SideFam p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN p.T.base.μG q0 R l dg) → (haveI := FiniteDimensional.complete ℂ Wq; SideFam p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN p.T.base.μG q0 R l' dg) → IsCoef (R 0) (l 0) (l' 0) f s₀ → s₀ ≠ 0 → ∃ (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (t : ℝ), 0 < t ∧ J 0 = (fun g => (t : ℂ) • f g) ∧ (NzOn (R 0) (l 0) ∧ NzOn (R 0) (l' 0)) ∧ (∀ ν, n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) → IsCoef (R ν) (l ν) (l' ν) (J ν) (s ν) ∧ ‖s ν‖ = dg ν) ∧ (∀ ν, ¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → J ν = 0) := by
  intro hH P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg f s₀ hfam hL hR hf hs₀
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  classical
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have h0 : n1 (0 : Fin (2 * P.r + P.k + 1) → ℤ) ≤ q0 := by simp [n1]
  have hDS : ∀ ν, n1 ν ≤ q0 → (R ν).IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν a : ℝ)) :=
    fun ν hν => hfam ν hν
  have hdg0 : 0 < dg 0 := (hL 0 h0).2.1
  have hsn : 0 < ‖s₀‖ := norm_pos_iff.mpr hs₀
  have hnz : NzOn (R 0) (l 0) ∧ NzOn (R 0) (l' 0) := by
    obtain ⟨m, x, y, X, hxy, -, hs⟩ := hf
    have hsm := (GlobalTheory.rep_basic_of_isDS hK _ _ _ _ (R 0) (hDS 0 h0)).2.2.2.2.1
    rw [hs] at hs₀
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs₀
    refine ⟨⟨x i, hsm _ (hxy i).1, fun h => hi ?_⟩, ⟨y i, hsm _ (hxy i).2, fun h => hi ?_⟩⟩
    · rw [h, inner_zero_left]
    · rw [h, map_zero, inner_zero_right]
  have hex : ∀ ν, ∃ (s : ℂ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)),
      (ν = 0 → F = fun g => ((dg 0 / ‖s₀‖ : ℝ) : ℂ) • f g) ∧
      (n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) → IsCoef (R ν) (l ν) (l' ν) F s ∧ ‖s‖ = dg ν) ∧
      (¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → F = 0) := by
    intro ν
    by_cases hν : ν = 0
    · subst hν
      refine ⟨((dg 0 / ‖s₀‖ : ℝ) : ℂ) * s₀, _, fun _ => rfl, fun _ _ _ => ⟨?_, ?_⟩, fun hn => ?_⟩
      · exact (GlobalTheory.isCoef_of_translate_smul_exists hK _ _ _ _ (R 0) Wp Wq (l 0) (l' 0) (hDS 0 h0)).2.1 f s₀ _ hf
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_pos hdg0 hsn).le]
        field_simp
      · exact absurd ⟨h0, hnz⟩ hn
    · by_cases hc : n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)
      · obtain ⟨h1, h2, h3⟩ := hc
        have e1 := GlobalTheory.bessel_nonzero_on_translates hH _ _ _ _ (R ν) Wp _ _ (l ν) (hDS ν h1) (hL ν h1).1.1 h2
        have e2 := GlobalTheory.bessel_nonzero_on_translates hH _ _ _ _ (R ν) Wq _ _ (l' ν) (hDS ν h1) (hR ν h1).1.1 h3
        obtain ⟨F, hF⟩ := (GlobalTheory.isCoef_of_translate_smul_exists hK _ _ _ _ (R ν) Wp Wq (l ν) (l' ν)
          (hDS ν h1)).2.2 e1 e2 (dg ν : ℂ)
        refine ⟨_, F, fun h => absurd h hν, fun _ _ _ => ⟨hF, ?_⟩, fun hn => absurd ⟨h1, h2, h3⟩ hn⟩
        rw [Complex.norm_real, Real.norm_of_nonneg (hL ν h1).2.1.le]
      · exact ⟨0, 0, fun h => absurd h hν, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hc, fun _ => rfl⟩
  choose s J h1 h2 h3 using hex
  exact ⟨s, J, dg 0 / ‖s₀‖, div_pos hdg0 hsn, h1 0 rfl, hnz, h2, h3⟩

end GlobalTheory
end

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_functional_coefficient : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (s₀ : ℂ), IsFam lam q0 R → (haveI := FiniteDimensional.complete ℂ Wp; SideFam p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN p.T.base.μG q0 R l dg) → (haveI := FiniteDimensional.complete ℂ Wq; SideFam p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN p.T.base.μG q0 R l' dg) → IsCoef (R 0) (l 0) (l' 0) f s₀ → s₀ ≠ 0 → ∃ (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (t : ℝ), 0 < t ∧ J 0 = (fun g => (t : ℂ) • f g) ∧ (NzOn (R 0) (l 0) ∧ NzOn (R 0) (l' 0)) ∧ (∀ ν, n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) → IsCoef (R ν) (l ν) (l' ν) (J ν) (s ν) ∧ ‖s ν‖ = dg ν) ∧ (∀ ν, ¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → J ν = 0) := by
  atlas_forward_decl GlobalTheory.exists_coef_family
end

section
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TauChoice

theorem exists_tau : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)), Num P.k P.r lam P.u b bv ga h q0 → IsFam lam q0 R → (haveI := FiniteDimensional.complete ℂ Wp; SideFam p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN p.T.base.μG q0 R l dg) → (haveI := FiniteDimensional.complete ℂ Wq; SideFam p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN p.T.base.μG q0 R l' dg) → (NzOn (R 0) (l 0) ∧ NzOn (R 0) (l' 0)) → (∀ ν, n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) → IsCoef (R ν) (l ν) (l' ν) (J ν) (s ν) ∧ ‖s ν‖ = dg ν) → (∀ ν, ¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → J ν = 0) → ∃ tau, Sup p lam q0 R l l' dg s J tau := by
  intro hH P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg s J hNum hFam hL hR hnz hco hz
  classical
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  obtain ⟨-, hz1, hz2, -, -, ht1, ht2⟩ := p.hP
  obtain ⟨νq, νq', hS, hS'⟩ := GlobalTheory.T.besselDatum_both_sides_are_sides P.k P.r Wp Wq p.T.base P.u P.u' ht1 ht2
  have key : ∀ ν, ∃ t : Finset (Fin (2 * P.r + P.k + 1)) → ℂ,
      (∀ I, J ν = 0 ∨ J (ν + eZ I) = 0 → t I = 0) ∧
      (n1 ν + (P.r + 1) * (P.r + 2) ≤ q0 →
    ∃ io pr ep, TensH (cmp (P.r + 1)) (cmp (P.r + 1) (Formalism.QuantumDeterminants.Hpk P.k P.r)) (R ν)
        (fun I : Sub (2 * P.r + P.k + 1) (P.r + 1) => R (ν + eZ I.1)) io pr ep ∧
      ∀ I : Sub (2 * P.r + P.k + 1) (P.r + 1), J ν ≠ 0 → J (ν + eZ I.1) ≠ 0 → ∃ κ κ' : ℂ,
        (∀ v ∈ (R ν).sm, l (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z)) v c)) = κ • l ν v) ∧
        (∀ v ∈ (R ν).sm, l' (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z')) v c)) = κ' • l' ν v) ∧
        t I.1 = (ep I : ℂ) * κ' * star κ * s ν / s (ν + eZ I.1)) := by
    intro ν
    by_cases hν : n1 ν + (P.r + 1) * (P.r + 2) ≤ q0
    swap
    · exact ⟨fun _ => 0, fun _ _ => rfl, fun h => absurd h hν⟩
    have hν1 : n1 ν + (P.r + 1) ≤ q0 := by nlinarith
    have hν0 : n1 ν ≤ q0 := by omega
    obtain ⟨io, pr, ep, hT⟩ := (GlobalTheory.T.pieri_tensor_decomposition hH P.k P.r lam P.u b bv ga h q0 R hNum hFam ν).1 (P.r + 1) hν1
    have hI : ∀ I : Sub (2 * P.r + P.k + 1) (P.r + 1), n1 (ν + eZ I.1) ≤ q0 := by
      intro I
      have h1 : n1 (ν + eZ I.1) ≤ n1 ν + I.1.card := by
        unfold n1 eZ
        calc ∑ i, ((ν + fun i => if i ∈ I.1 then (1 : ℤ) else 0) i).natAbs
            ≤ ∑ i, ((ν i).natAbs + if i ∈ I.1 then 1 else 0) := by
              refine Finset.sum_le_sum fun i _ => ?_
              simp only [Pi.add_apply]
              split_ifs <;> omega
          _ = ∑ i, (ν i).natAbs + I.1.card := by
              rw [Finset.sum_add_distrib]; simp
      rw [I.2] at h1
      omega
    have hk : ∀ I : Sub (2 * P.r + P.k + 1) (P.r + 1), ∃ κ κ' : ℂ, J ν ≠ 0 →
        (∀ v ∈ (R ν).sm, l (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z)) v c)) = κ • l ν v) ∧
        (∀ v ∈ (R ν).sm, l' (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z')) v c)) = κ' • l' ν v) := by
      intro I
      by_cases hJ : J ν = 0
      · exact ⟨0, 0, fun h => absurd hJ h⟩
      have hn : n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν) := by
        by_contra hc
        exact hJ (hz ν hc)
      obtain ⟨κ, hκ⟩ := (GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint hH P.k P.r _ _ _ _ (P.r + 1) (R ν)
        (fun I : Sub (2 * P.r + P.k + 1) (P.r + 1) => R (ν + eZ I.1)) io pr ep _ _ _ Wp
        p.T.base.z p.T.base.π P.u p.T.base.μW p.T.base.μN p.T.base.μG νq
        (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z)) (l ν) (hFam ν hν0) (fun I => hFam _ (hI I))
        (GlobalTheory.WedgeFRep.isFRep_cmp P.k P.r (P.r + 1)) hT hS
        (fun g hg => (GlobalTheory.FlagFix.fixes_wedge_and_form P.k P.r _ hz1 g hg).1) (hL ν hν0).1 hn.2.1 I
        (l (ν + eZ I.1)) (hL _ (hI I)).1).1
      obtain ⟨κ', hκ'⟩ := (GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint hH P.k P.r _ _ _ _ (P.r + 1) (R ν)
        (fun I : Sub (2 * P.r + P.k + 1) (P.r + 1) => R (ν + eZ I.1)) io pr ep _ _ _ Wq
        p.T.base.z' p.T.base.π' P.u' p.T.base.μW' p.T.base.μN p.T.base.μG νq'
        (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z')) (l' ν) (hFam ν hν0) (fun I => hFam _ (hI I))
        (GlobalTheory.WedgeFRep.isFRep_cmp P.k P.r (P.r + 1)) hT hS'
        (fun g hg => (GlobalTheory.FlagFix.fixes_wedge_and_form P.k P.r _ hz2 g hg).1) (hR ν hν0).1 hn.2.2 I
        (l' (ν + eZ I.1)) (hR _ (hI I)).1).1
      exact ⟨κ, κ', fun _ => ⟨hκ, hκ'⟩⟩
    choose κ κ' hκ using hk
    refine ⟨fun I => if hc : I.card = P.r + 1 ∧ J ν ≠ 0 ∧ J (ν + eZ I) ≠ 0 then
      (ep ⟨I, hc.1⟩ : ℂ) * κ' ⟨I, hc.1⟩ * star (κ ⟨I, hc.1⟩) * s ν / s (ν + eZ I) else 0, ?_, fun _ => ?_⟩
    · intro I hI0
      refine dif_neg ?_
      rintro ⟨-, h1, h2⟩
      exact hI0.elim h1 h2
    · refine ⟨io, pr, ep, hT, fun I h1 h2 => ⟨κ I, κ' I, (hκ I h1).1, (hκ I h1).2, ?_⟩⟩
      exact dif_pos (⟨I.2, h1, h2⟩ : I.1.card = P.r + 1 ∧ J ν ≠ 0 ∧ J (ν + eZ I.1) ≠ 0)
  choose tau h1 h2 using key
  exact ⟨tau, ⟨hFam, hL, hR, hnz, hco, hz, h1, h2⟩⟩

end GlobalTheory.TauChoice
end

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_functional_span : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)), Num P.k P.r lam P.u b bv ga h q0 → IsFam lam q0 R → (haveI := FiniteDimensional.complete ℂ Wp; SideFam p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN p.T.base.μG q0 R l dg) → (haveI := FiniteDimensional.complete ℂ Wq; SideFam p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN p.T.base.μG q0 R l' dg) → (NzOn (R 0) (l 0) ∧ NzOn (R 0) (l' 0)) → (∀ ν, n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) → IsCoef (R ν) (l ν) (l' ν) (J ν) (s ν) ∧ ‖s ν‖ = dg ν) → (∀ ν, ¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → J ν = 0) → ∃ tau, Sup p lam q0 R l l' dg s J tau := by
  atlas_forward_decl GlobalTheory.TauChoice.exists_tau
end

section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory


end GlobalTheory
end
