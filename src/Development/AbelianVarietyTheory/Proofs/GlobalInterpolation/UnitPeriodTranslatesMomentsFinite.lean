import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomEquiv
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MkLeContinuumOfDenseRange
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmLatticeTranslationOperatorEqPhaseMulNegComp
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaLawsUnitPeriod
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MomentMeasureNormLeOneIffLatticeIntegral
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DiscOneScaleRatioIdealRingAlgebraicUnit
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntStd
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsProdAndSum
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsPullback
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseThetaTensorPowerTranslatesIntegral
import BuildAid.ForwardExisting
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWAPlaces
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntEasy
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodLiftEqIdempotentLift
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IteratedFDerivAlgebraicDirectionsJetTransport
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAnalyticSetupPeriodLatticePair
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.GlobalTheory.GL3.LinkThetaStatementFamily
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.RCauchy
import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFacts

section
open PowerSeries GlobalTheory.MomOne GlobalTheory.MomN
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomN.PeriodData

variable {q : ℕ} [Fact q.Prime]

theorem laws_and_chart (d : ℕ) (ι : ℂ ≃+* ℂ_[q]) (δ : ℂ) (θ : ℂ → ℂ) (L : PeriodPair)
    (hd : d.Prime) (h7 : d % 16 = 7) (hs : Split d q) (hL : IsOK d L)
    (hD : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = discr d) (hδ : δ ^ 12 = discr d) (hδ0 : δ ≠ 0) (hθ : IsTh d θ) :
    ∃ Ω : ℂ_[q], ‖Ω‖ = 1 ∧ ThetaLaws ι d (Ω / ι δ) θ ∧
      ∃ M : Mdl q, M.ι = ι ∧ IsOK d M.L ∧ M.MChart (Ω / ι δ) := by
  obtain ⟨M, rfl, rfl, hok, a1, a2, a3, a4, a6⟩ := GlobalTheory.T.exists_goodReduction_algebraic_weierstrass_model d q ι L hd h7 hL
  obtain ⟨ω₀, hω₀⟩ := GlobalTheory.T.exists_multiplicativeChart_at_splitPrime d q M hd h7 hs hL hok a1 a2 a3 a4 a6
  obtain ⟨a, -, hω, hn⟩ := GlobalTheory.T.exists_normalised_multiplicativeChart d q M ω₀ hd h7 hs hL hω₀
  set ω := ω₀ * zc a
  have hι : M.ι δ ≠ 0 := by simpa using hδ0
  refine ⟨ω * M.ι δ, ?_, ?_, M, rfl, hL, ?_⟩
  · rw [norm_mul, (GenusOne.norm_root_eq M hok δ (hδ.trans hD.symm)).1, GenusOne.norm_period M ω hω]
  · rw [mul_div_cancel_right₀ _ hι]
    have hN := GlobalTheory.T.norm_translate_powerComb_le_coprimeTranslation d q M ω θ hd h7 hs hL hω hθ
    refine ⟨fun t ht => ?_, GlobalTheory.T.weilOperator_theta_translate_shift_prime_to_q d q M ω θ hd h7 hs hL hω hθ hn, hN⟩
    have hU := (GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd.pos).2.1
    have h0 : PrimeTo d q 0 := ⟨1, one_pos, Nat.coprime_one_left _, 0, 0, by simp⟩
    have := hN 1 1 (fun _ => 1) (fun _ => 0) t 1 (fun _ => h0) ht
      (by simpa [hU] using GlobalTheory.T.cm_even_theta_series_chart_coeff_integral d q M ω θ hd h7 hs hL hω hθ)
    simpa [hU] using this
  · rw [mul_div_cancel_right₀ _ hι]; exact hω

end GlobalTheory.MomN.PeriodData

namespace GlobalTheory.MomN

theorem exists_per : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]), d.Prime → d % 16 = 7 → Split d q →
    ∃ (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per d ι δ₀ θ Ω := by
  intro d q _ ι hd h7 hs
  obtain ⟨δ₀, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (discr d) (by norm_num : 0 < 12)
  obtain ⟨⟨L, hL, hD⟩, θ, hθ⟩ := GlobalTheory.T.exists_imagQuadOrder_pair_and_evenTheta d hd h7
  have hδ0 : δ₀ ≠ 0 := (GenusOne.thetaLaws_unit_period d q δ₀ hd h7 hs hδ).choose_spec.2.1
  obtain ⟨Ω, hΩ, hT, hM⟩ := PeriodData.laws_and_chart d ι δ₀ θ L hd h7 hs hL hD hδ hδ0 hθ
  refine ⟨δ₀, θ, Ω, hθ, hδ, hδ0, fun ι' => ?_, hΩ, hT, hM⟩
  obtain ⟨Ω', h1, h2, -⟩ := PeriodData.laws_and_chart d ι' δ₀ θ L hd h7 hs hL hD hδ hδ0 hθ
  exact ⟨Ω', h1, h2⟩

end GlobalTheory.MomN
end

section
section
noncomputable section

namespace GlobalTheory.MomN

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.KerInert Formalism.L2.KerInert.ISd

theorem transl_normVec_int : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ χ : IdE D → ℂ, IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → EqAt D p (StandardLatticesGL3.stdL D N) L → EqAt D p (StandardLatticesGL3.stdL D N') L' → ∀ t : VC D N N', TorsPrime D p (La D B.tor L L') t → ∃ (m : ℕ) (c : Fin m → ℂ) (s : Fin m → VC D N N'), (∀ k, c k ∈ Qbar ∧ IsIntP (lamC lam (c k))) ∧ (∀ k, TorsPrime D p (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (s k)) ∧ U D B.tor t (B.eNat χ N N' L L') = fun z => ∑ k, c k * U D B.tor (s k) (B.thZero N N') z := by
  intro D cc δ B hcc hδ χ hχ p _ lam N N' M M' hAdm hM hM' t ht
  obtain ⟨s, hs, hsM, hMs⟩ := hM
  obtain ⟨s', hs', hsM', hMs'⟩ := hM'
  have hp : p.Prime := Fact.out
  have spos : 0 < s := Nat.pos_of_ne_zero (by rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left p |>.mp hs))
  have spos' : 0 < s' := Nat.pos_of_ne_zero (by rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left p |>.mp hs'))
  set La0 := La D (tor0 D cc δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N') with hLa0
  set La1 := La D (tor0 D cc δ) M (Formalism.MainNotions.StandardLatticesGL3.stdL D N') with hLa1
  set La2 := La D (tor0 D cc δ) M M' with hLa2
  have one_std : ∀ y ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N', ((1 : ℕ) : D.host.E) • y ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N' := by
    intro y hy; simpa using hy
  have one_M : ∀ y ∈ M, ((1 : ℕ) : D.host.E) • y ∈ M := by
    intro y hy; simpa using hy
  have k10 : ∀ z ∈ La1, (s * 1) • z ∈ La0 := fun z hz => La_smul cc δ s 1 hsM one_std hz
  have k21 : ∀ z ∈ La2, (1 * s') • z ∈ La1 := fun z hz => La_smul cc δ 1 s' one_M hMs' hz
  have k20 : ∀ z ∈ La2, (s * s') • z ∈ La0 := fun z hz => La_smul cc δ s s' hsM hMs' hz
  have k12 : ∀ z ∈ La1, (1 * s') • z ∈ La2 := fun z hz => La_smul cc δ 1 s' one_M hsM' hz
  have hδ0 : δ ≠ 0 := delta_nonzero_link D cc hcc δ hδ
  have hI : IO.HfInt (tor0 D cc δ) La2 := hermitian_form_integral_values D cc hcc δ hδ hδ0 N N' M M' hAdm

  let Q2 : VC D N N' → Prop := fun y => ∃ n : ℕ, 0 < n ∧ n • y ∈ La2
  have q2_add : ∀ x y, Q2 x → Q2 y → Q2 (x + y) := by
    rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have e : (n * m) • (x + y) = m • (n • x) + n • (m • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm m n]
    rw [e]
    exact add_mem (AddSubgroup.nsmul_mem _ hx m) (AddSubgroup.nsmul_mem _ hy n)
  have q2_2 : ∀ x ∈ La2, Q2 x := fun x hx => ⟨1, one_pos, by simpa using hx⟩
  have q2_1 : ∀ x ∈ La1, Q2 x := fun x hx => ⟨1 * s', by omega, k12 x hx⟩
  have cf_good : ∀ x y, Q2 x → Q2 y → Good lam (IO.cf (tor0 D cc δ) x y) := by
    rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    obtain ⟨q, hq⟩ := im_rat (tor0 D cc δ) hI hn hm hx hy
    exact good_cf lam _ x y q hq

  have R1 : Rep lam B.tor (fun y => y ∈ La1) (B.thHalf N N' M) (B.thZero N N') := by
    show Rep lam B.tor (fun y => y ∈ La1) (Iop D B.tor La0 La1 (B.thZero N N')) (B.thZero N N')
    refine rep_Iop (Pt := fun y => y = 0) (rep_self rfl) ?_ ?_
    · rintro x hx y rfl
      exact ⟨cf_good x 0 (q2_1 x hx) (q2_2 0 (zero_mem _)), by simpa using hx⟩
    · exact idx_coprime La0 La1 (s * 1) (by simpa using hs) k10

  have R2 : Rep lam B.tor (fun y => ∃ a ∈ La2, ∃ b ∈ La1, y = a + b) (B.thMoved N N' M M') (B.thZero N N') := by
    show Rep lam B.tor _ (Iop D B.tor La1 La2 (B.thHalf N N' M)) (B.thZero N N')
    refine rep_Iop R1 ?_ ?_
    · intro x hx y hy
      exact ⟨cf_good x y (q2_2 x hx) (q2_1 y hy), x, hx, y, hy, rfl⟩
    · exact idx_coprime La1 La2 (1 * s') (by simpa using hs') k21

  obtain ⟨n, hn, hnp, hnt⟩ := ht
  have R3 : Rep lam B.tor (TorsPrime D p La0) (U D B.tor t (B.thMoved N N' M M')) (B.thZero N N') := by
    refine rep_U t R2 ?_
    rintro y ⟨a, ha, b, hb, rfl⟩
    refine ⟨cf_good t _ ⟨n, hn, hnt⟩ (q2_add a b (q2_2 a ha) (q2_1 b hb)), ?_⟩
    refine ⟨n * (s * s'), Nat.mul_pos hn (Nat.mul_pos spos spos'), Nat.Coprime.mul hnp (Nat.Coprime.mul hs hs'), ?_⟩
    have e : (n * (s * s')) • (t + (a + b)) = (s * s') • (n • t) + (n • ((s * s') • a) + (n * s') • ((s * 1) • b)) := by
      simp only [smul_add, smul_smul]
      congr 1
      · rw [mul_comm]
      · congr 1
        rw [mul_one, mul_assoc, mul_comm s' s]
    rw [e]
    exact add_mem (k20 _ hnt) (add_mem (AddSubgroup.nsmul_mem _ (k20 a ha) n)
      (AddSubgroup.nsmul_mem _ (k10 b hb) (n * s')))

  have hchi := RestC.chiFacUnit (D := D) χ hχ p lam N N' M M' hAdm ⟨s, hs, hsM, hMs⟩ ⟨s', hs', hsM', hMs'⟩
  have hgood : Good lam (Base.chiFac χ N N' M M') := ⟨hchi.1, le_of_eq hchi.2⟩
  have R4 := rep_smul hgood R3
  have e : U D B.tor t (B.eNat χ N N' M M') = fun z => Base.chiFac χ N N' M M' * U D B.tor t (B.thMoved N N' M M') z := by
    funext z
    exact IO.U_smul _ t _ _ z
  rw [e]
  obtain ⟨m, c, s₀, hc, hs₀, hF⟩ := R4
  exact ⟨m, c, s₀, hc, hs₀, hF⟩

end GlobalTheory.MomN
end
end

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_normalized_vector_integral_comb_tensor_power : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ χ : IdE D → ℂ, IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → EqAt D p (StandardLatticesGL3.stdL D N) L → EqAt D p (StandardLatticesGL3.stdL D N') L' → ∀ t : VC D N N', TorsPrime D p (La D B.tor L L') t → ∃ (m : ℕ) (c : Fin m → ℂ) (s : Fin m → VC D N N'), (∀ k, c k ∈ Qbar ∧ IsIntP (lamC lam (c k))) ∧ (∀ k, TorsPrime D p (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (s k)) ∧ U D B.tor t (B.eNat χ N N' L L') = fun z => ∑ k, c k * U D B.tor (s k) (B.thZero N N') z := by
  atlas_forward_decl GlobalTheory.MomN.transl_normVec_int
end

section
section
noncomputable section

namespace GlobalTheory.MomN

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem weakApprox_split : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p ≠ 2 → jacobiSym (-(D.host.d : ℤ)) p = 1 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → letI := D.host.cmStar; ∃ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' M M' ∧ EqAt D p (StandardLatticesGL3.stdL D N) M ∧ EqAt D p (StandardLatticesGL3.stdL D N') M' ∧ L = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M ∧ L' = SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M' := by
  intro D p _ _ _ N N' L L' hAdm
  let _ := D.host.cmStar
  obtain ⟨hN, hN', hL, hL'⟩ := hAdm
  have hCM : PI.UG.IsCMUnram D.host.E := D.sp.cm.cmUnram
  have hp : p.Prime := Fact.out
  obtain ⟨γ, M, hM, hEq, hLM⟩ := Formalism.L2.KerInert.wa_main Formalism.L2.KerInert.weak_approximation_places hCM p hp N L hL
  obtain ⟨γ', M', hM', hEq', hLM'⟩ := Formalism.L2.KerInert.wa_main Formalism.L2.KerInert.weak_approximation_places hCM p hp N' L' hL'
  exact ⟨γ, γ', M, M', ⟨hN, hN', hM, hM'⟩, hEq, hEq', hLM, hLM'⟩

end GlobalTheory.MomN
end
end

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weakApproximation_unitaryLattices_splitPrime : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p ≠ 2 → jacobiSym (-(D.host.d : ℤ)) p = 1 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → letI := D.host.cmStar; ∃ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' M M' ∧ EqAt D p (StandardLatticesGL3.stdL D N) M ∧ EqAt D p (StandardLatticesGL3.stdL D N') M' ∧ L = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M ∧ L' = SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M' := by
  atlas_forward_decl GlobalTheory.MomN.weakApprox_split
end

section
section
noncomputable section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomPull

variable {D : D7} {N N' : ℕ}

def tPullL (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) : VC D N N' →ₗ[ℂ] VC D N N' where
  toFun := Formalism.L2.KerInert.tPull D (tor0 D cc δ) γ γ'
  map_add' := Formalism.L2.KerInert.ie_tPull_add cc δ γ γ'
  map_smul' := Formalism.L2.KerInert.ie_tPull_smul cc δ γ γ'

theorem hf_tPull (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (hγ : (letI := D.host.cmStar; γ * star γ) = 1)
    (hγ' : (letI := D.host.cmStar; γ' * star γ') = 1) (z w : VC D N N') :
    Hf D (tor0 D cc δ) (Formalism.L2.KerInert.tPull D (tor0 D cc δ) γ γ' z)
      (Formalism.L2.KerInert.tPull D (tor0 D cc δ) γ γ' w) = Hf D (tor0 D cc δ) z w := by
  letI := D.host.cmStar
  unfold Hf
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h1 := Formalism.L2.KerInert.PullbackComparison.map_mul_star D (embT D τ) γ hγ
  have h2 := Formalism.L2.KerInert.PullbackComparison.map_mul_star D (embT D τ) γ' hγ'
  rw [Matrix.star_eq_conjTranspose] at h1 h2
  exact Formalism.L2.KerInert.PullbackComparison.sum_mul_star_conj (γ.map (embT D τ)) (γ'.map (embT D τ)) h1 h2
    (Matrix.of (z τ)) (Matrix.of (w τ))

end GlobalTheory.MomPull

open GlobalTheory.MomPull in

theorem GlobalTheory.MomPull.pull_unitary : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ), letI := D.host.cmStar; ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), ∃ g : VC D N N' →L[ℂ] VC D N N', (∀ x ∈ La D (tor0 D cc δ) (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M) (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M'), g x ∈ La D (tor0 D cc δ) M M') ∧ ∀ (t : VC D N N') (G : VC D N N' → ℂ), U D (tor0 D cc δ) t (pull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) G) = fun z => U D (tor0 D cc δ) (g t) G (g z) := by
  intro D cc δ N N'
  letI := D.host.cmStar
  intro γ γ' M M'
  have h1' : star (γ' : Matrix (Fin N') (Fin N') D.host.E) * γ' = 1 := Matrix.mem_unitaryGroup_iff'.mp γ'.2
  have hγ : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp γ.2
  have hγ' : (γ' : Matrix (Fin N') (Fin N') D.host.E) * star (γ' : Matrix (Fin N') (Fin N') D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp γ'.2
  refine ⟨LinearMap.toContinuousLinearMap (tPullL cc δ (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E)), fun x hx => ?_, fun t G => ?_⟩
  · have h := Formalism.L2.KerInert.ie_La_pull cc δ _ _ h1' M M' hx
    exact h
  · funext z
    show G (Formalism.L2.KerInert.tPull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
        (γ' : Matrix (Fin N') (Fin N') D.host.E) (z + t)) * _ =
      G (Formalism.L2.KerInert.tPull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
        (γ' : Matrix (Fin N') (Fin N') D.host.E) z + Formalism.L2.KerInert.tPull D (tor0 D cc δ)
        (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) t) * _
    have e : ∀ y, (LinearMap.toContinuousLinearMap (tPullL cc δ (γ : Matrix (Fin N) (Fin N) D.host.E)
        (γ' : Matrix (Fin N') (Fin N') D.host.E))) y = Formalism.L2.KerInert.tPull D (tor0 D cc δ)
        (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) y := fun _ => rfl
    simp only [e]
    rw [hf_tPull cc δ _ _ hγ hγ', hf_tPull cc δ _ _ hγ hγ', Formalism.L2.KerInert.ie_tPull_add]
end
end

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryPairPullback_lattices_translates : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ), letI := D.host.cmStar; ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), ∃ g : VC D N N' →L[ℂ] VC D N N', (∀ x ∈ La D (tor0 D cc δ) (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M) (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M'), g x ∈ La D (tor0 D cc δ) M M') ∧ ∀ (t : VC D N N') (G : VC D N N' → ℂ), U D (tor0 D cc δ) t (pull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) G) = fun z => U D (tor0 D cc δ) (g t) G (g z) := by
  atlas_forward_decl GlobalTheory.MomPull.pull_unitary
end

section
section
noncomputable section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomN

theorem contDiff_U {D : D7} {N N' : ℕ} (T : Tor D) (t : VC D N N') {G : VC D N N' → ℂ} (hG : ContDiff ℂ ⊤ G) :
    ContDiff ℂ ⊤ (U D T t G) := by
  have hH : ContDiff ℂ ⊤ fun z : VC D N N' => Hf D T z t := by
    unfold Hf
    refine ContDiff.div_const ?_ _
    refine ContDiff.sum fun τ _ => ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
    refine ContDiff.mul ?_ contDiff_const
    fun_prop
  unfold U
  refine ContDiff.mul (hG.comp (contDiff_id.add contDiff_const)) ?_
  exact ContDiff.cexp ((contDiff_const.mul hH).sub contDiff_const)

theorem transPrime_int : (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ) → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ χ : IdE D → ℂ, IsChi D χ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ t : VC D N N', TorsPrime D q (La D B.tor L L') t → LatInt ι (Ω / ι δ₀) (La D B.tor L L') (U D B.tor t (B.eNat χ N N' L L')) := by
  intro hEq D cc δ B hcc hδ q _ hq2 hsplit hcop ι δ₀ θ Ω hPer χ hχ N N' L L' hA t ht
  letI := D.host.cmStar
  obtain ⟨γ, γ', M, M', hAM, hE, hE', rfl, rfl⟩ := GlobalTheory.T.weakApproximation_unitaryLattices_splitPrime D q hq2 hsplit N N' L L' hA
  obtain ⟨hN, hN', hSM, hSM'⟩ := id hAM
  have hcov : pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
      (B.eNat χ N N' M M') =
      B.eNat χ N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M)
        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M') :=
    (hEq D cc δ B χ hcc hδ hχ).1 N N' ⟨M, hSM⟩ ⟨M', hSM'⟩ hN hN' γ γ'
  obtain ⟨g, hg, hU⟩ := GlobalTheory.T.unitaryPairPullback_lattices_translates D cc δ N N' γ γ' M M'
  have ht' : TorsPrime D q (La D B.tor M M') (g t) := by
    obtain ⟨n, hn, hc, hm⟩ := ht
    refine ⟨n, hn, hc, ?_⟩
    have := hg _ hm
    rwa [map_nsmul] at this
  let lam : Qbar →+* ℂ_[q] := (ι : ℂ →+* ℂ_[q]).comp (algebraMap Qbar ℂ)
  obtain ⟨m, c, s, hc, hs, heq⟩ :=
    GlobalTheory.T.translate_normalized_vector_integral_comb_tensor_power D cc δ B hcc hδ χ hχ q lam N N' M M' hAM hE hE' (g t) ht'
  have hzero : ∀ k, LatInt ι (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
      (U D B.tor (s k) (B.thZero N N')) := fun k =>
    GlobalTheory.T.cm_base_theta_tensor_power_translates_integral D cc δ B hcc hδ q hq2 hsplit hcop ι δ₀ θ Ω hPer N N' (s k) (hs k)
  have hd : ContDiff ℂ ⊤ (B.thZero N N') :=
    AnalyticOnNhd.contDiff (B.thZeroMem (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ) N N').1
  have hsm : ∀ k, ContDiff ℂ ⊤ (U D B.tor (s k) (B.thZero N N')) := fun k => contDiff_U _ _ hd
  have hcn : ∀ k, ‖ι (c k)‖ ≤ 1 := by
    intro k
    obtain ⟨h1, h2⟩ := hc k
    have e : lamC lam (c k) = ι (c k) := by
      unfold lamC
      rw [dif_pos h1]
      rfl
    rw [← e]
    exact h2
  have hsum := (GlobalTheory.T.latticeJetsAreBoundedMoments_prod_and_sum q ι (VC D N N') (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))).2
    (Fin m) Finset.univ c (fun k => U D B.tor (s k) (B.thZero N N')) (fun k _ => hsm k) (fun k _ => hcn k)
    (fun k _ => hzero k)
  have hGs : ContDiff ℂ ⊤ fun z => ∑ k, c k * U D B.tor (s k) (B.thZero N N') z :=
    ContDiff.sum fun k _ => contDiff_const.mul (hsm k)
  obtain ⟨a, ha, hsM, hMs⟩ := hE
  obtain ⟨b, hb, hsM', hMs'⟩ := hE'
  have hpull := GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι (VC D N N') (VC D N N') (Ω / ι δ₀)
    (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
    (La D B.tor (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M)
      (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M')) g _ hGs
    (fun x hx => ⟨a * b, Nat.Coprime.mul_left ha hb,
      Formalism.L2.KerInert.ISd.La_smul cc δ a b hsM hMs' (hg x hx)⟩) hsum
  rw [← hcov, show U D B.tor t (pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E)
      (γ' : Matrix (Fin N') (Fin N') D.host.E) (B.eNat χ N N' M M')) =
      fun z => U D B.tor (g t) (B.eNat χ N N' M M') (g z) from hU t _, heq]
  exact hpull

end GlobalTheory.MomN
end
end

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedVector_translates_prime_order_integral : (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ) → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ χ : IdE D → ℂ, IsChi D χ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ t : VC D N N', TorsPrime D q (La D B.tor L L') t → LatInt ι (Ω / ι δ₀) (La D B.tor L L') (U D B.tor t (B.eNat χ N N' L L')) := by
  atlas_forward_decl GlobalTheory.MomN.transPrime_int
end

section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedFDeriv_algebraic_directions_jet_transport : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ) (G : VC D N N' → ℂ), ContDiff ℂ ⊤ G → CoefIn D G Qbar → ∀ (m : ℕ) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E), iteratedFDeriv ℂ m G 0 (fun j => embV D (tor0 D cc δ) (y j)) ∈ Qbar ∧ jet D lam y (pSer D lam G) = lamC lam (iteratedFDeriv ℂ m G 0 fun j => embV D (tor0 D cc δ) (y j)) := by
  first | exact @GlobalTheory.JetTransport.jet_pSer | exact GlobalTheory.JetTransport.jet_pSer | (intros; apply GlobalTheory.JetTransport.jet_pSer <;> assumption)
end

section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analyticSetup_periodLatticePair : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∃ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), S.d = D.host.d ∧ S.Ok ∧ (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') ∧ (∀ x y, JMB.hf S.Hm (e x) (e y) = Hf D B.tor x y) ∧ (∀ x y : Matrix (Fin N') (Fin N) D.host.E, JMB.beta S.d S.Hm (e (δ • embV D B.tor x)) (e (δ • embV D B.tor y)) = D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) / (Ideal.absNorm cc : ℂ)) ∧ (∀ x ∈ La D B.tor L L', ∃ (n : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E), 0 < n ∧ x = δ • embV D B.tor A ∧ (n : D.host.E) • A ∈ YYl D L L') ∧ ∀ (q r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), Nat.Coprime (Ideal.absNorm cc) q → NNBasis D B.tor δ q L L' b → S.NNBasis q fun i => e (δ • embV D B.tor (b i)) := by
  first | exact @GlobalTheory.MomSetup.periodSetup | exact GlobalTheory.MomSetup.periodSetup | (intros; apply GlobalTheory.MomSetup.periodSetup <;> assumption)
end

section
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.IsomTheta

theorem isTheta_eNat_comp : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → δ ≠ 0 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), S.d = D.host.d → (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') → (∀ x y, JMB.hf S.Hm (e x) (e y) = Hf D B.tor x y) → S.IsTheta (fun z => B.eNat χ N N' L L' (e.symm z)) := by
  intro D cc δ B χ hcc hδ hχ h0 N N' L L' hA g S e hd hLa hH
  have hS : B.StdOK := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ
  have hmem := (B.vec_mem_ne hcc hδ h0 hS χ hχ N N' L L' hA).1
  have hQ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.rational_integrality_link D cc hcc δ hδ B N N' L L' hA
  simp only [Th, ThSp, Set.mem_setOf_eq] at hmem
  refine ⟨?_, ?_⟩
  · have hdiff : Differentiable ℂ (fun z => B.eNat χ N N' L L' (e.symm z)) :=
      hmem.1.comp e.symm.differentiable
    exact ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_differentiable hdiff
  · intro x hx
    have hx0 : e.symm x ∈ La D B.tor L L' := by
      rw [← hLa]; simpa using hx
    obtain ⟨m, hm⟩ := hQ _ hx0
    funext z
    have key := hmem.2 (e.symm x) hx0 (e.symm z)
    have h1 : JMB.hf S.Hm z x = Hf D B.tor (e.symm z) (e.symm x) := by
      simpa using hH (e.symm z) (e.symm x)
    have h2 : JMB.hf S.Hm x x = Hf D B.tor (e.symm x) (e.symm x) := by
      simpa using hH (e.symm x) (e.symm x)
    have hre : (JMB.beta S.d S.Hm x x).re = (m : ℝ) := by
      rw [JMB.beta, h2, hd, Complex.re_ofReal_mul]; exact hm
    have hal : al D B.tor (e.symm x) = (-1 : ℂ) ^ m := by
      rw [al, hm, round_intCast]
    have hph : Complex.exp ((Real.pi : ℂ) * Complex.I * (((JMB.beta S.d S.Hm x x).re : ℝ) : ℂ)) = (-1 : ℂ) ^ m := by
      rw [hre, show (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ) = (m : ℂ) * ((Real.pi : ℂ) * Complex.I) by push_cast; ring,
        Complex.exp_int_mul, Complex.exp_pi_mul_I]
    show Complex.exp ((Real.pi : ℂ) * Complex.I * (((JMB.beta S.d S.Hm x x).re : ℝ) : ℂ)) *
        (B.eNat χ N N' L L' (e.symm (z + x)) *
          Complex.exp (-(Real.pi : ℂ) * JMB.hf S.Hm z x - (Real.pi : ℂ) / 2 * JMB.hf S.Hm x x)) =
      B.eNat χ N N' L L' (e.symm z)
    rw [← key, hph, ← hal, h1, h2, map_add]
    unfold U
    ring_nf

end GlobalTheory.IsomTheta
end

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedThetaVector_isometry_isTheta : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → δ ≠ 0 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), S.d = D.host.d → (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') → (∀ x y, JMB.hf S.Hm (e x) (e y) = Hf D B.tor x y) → S.IsTheta (fun z => B.eNat χ N N' L L' (e.symm z)) := by
  atlas_forward_decl GlobalTheory.IsomTheta.isTheta_eNat_comp
end

section
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.AlgJetsRat

variable {D : D7} {N N' : ℕ}

theorem jet_embV_mem (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (F : VC D N N' → ℂ) (hF : ContDiff ℂ ⊤ F)
    (hT : ∀ α, taylor D F α ∈ Qbar) {m : ℕ} (A : Fin m → Matrix (Fin N') (Fin N) D.host.E) :
    iteratedFDeriv ℂ m F 0 (fun j => embV D (tor0 D cc δ) (A j)) ∈ Qbar := by
  rw [GlobalTheory.JetTransport.mlin_expand]
  refine IntermediateField.sum_mem _ fun f _ => IntermediateField.mul_mem _ ?_ ?_
  · exact IntermediateField.prod_mem _ fun j _ => GlobalTheory.JetTransport.embT_mem _ _
  · rw [GlobalTheory.JetTransport.iFD_coord F hF f]
    refine IntermediateField.mul_mem _ (IntermediateField.prod_mem _ fun i _ => ?_) (hT _)
    exact IntermediateField.natCast_mem _ _

end GlobalTheory.AlgJetsRat

open GlobalTheory.AlgJetsRat in
theorem GlobalTheory.algJets_of_taylor : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ) (B : Base D cc δ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (F : VC D N N' → ℂ), δ / δ₀ ∈ Qbar → δ₀ ≠ 0 → ContDiff ℂ ⊤ F → (∀ α, taylor D F α ∈ Qbar) → ∀ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') → (∀ x ∈ La D B.tor L L', ∃ (n : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E), 0 < n ∧ x = δ • embV D B.tor A ∧ (n : D.host.E) • A ∈ YYl D L L') → S.AlgJets δ₀ (fun z => F (e.symm z)) := by
  intro D cc δ δ₀ B N N' L L' F hδ hδ₀ hF hT g S e he hLa k ys hys
  have hc : ∀ j, ∃ (c : ℂ) (A : Matrix (Fin N') (Fin N) D.host.E),
      c ∈ Qbar ∧ e.symm (δ₀⁻¹ • ys j) = c • embV D B.tor A := by
    intro j
    obtain ⟨s, hs, hsy⟩ := hys j
    have hx : e.symm ((s : ℂ) • ys j) ∈ La D B.tor L L' := (he _).1 (by simpa using hsy)
    obtain ⟨n, A, -, hA, -⟩ := hLa _ hx
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    refine ⟨δ / δ₀ * (s : ℂ)⁻¹, A, IntermediateField.mul_mem _ hδ
      (IntermediateField.inv_mem _ (IntermediateField.natCast_mem _ s)), ?_⟩
    have h1 : e.symm (ys j) = (s : ℂ)⁻¹ • (δ • embV D B.tor A) := by
      rw [← hA, map_smul, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [map_smul, h1, smul_smul, smul_smul]
    congr 1
    field_simp
  choose c A hcQ hcA using hc
  show iteratedFDeriv ℂ k (F ∘ ((e.symm : (Fin g → ℂ) ≃L[ℂ] VC D N N') : (Fin g → ℂ) →L[ℂ] VC D N N')) 0
    (fun j => δ₀⁻¹ • ys j) ∈ Qbar
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ hF _ le_top,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [ContinuousLinearEquiv.coe_coe, map_zero, hcA]
  rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
  exact IntermediateField.mul_mem _ (IntermediateField.prod_mem _ fun j _ => hcQ j)
    (jet_embV_mem cc δ F hF hT A)
end
end

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicJets_of_algebraic_taylor : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ) (B : Base D cc δ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (F : VC D N N' → ℂ), δ / δ₀ ∈ Qbar → δ₀ ≠ 0 → ContDiff ℂ ⊤ F → (∀ α, taylor D F α ∈ Qbar) → ∀ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') → (∀ x ∈ La D B.tor L L', ∃ (n : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E), 0 < n ∧ x = δ • embV D B.tor A ∧ (n : D.host.E) • A ∈ YYl D L L') → S.AlgJets δ₀ (fun z => F (e.symm z)) := by
  atlas_forward_decl GlobalTheory.algJets_of_taylor
end

section
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.MomFin

theorem pairing_scaled : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ) (B : Base D cc δ) (N N' : ℕ) (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p]) (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (y : Matrix (Fin N') (Fin N) D.host.E) (a : Fin r → ℤ_[p]), δ / δ₀ ∈ Qbar → δ / δ₀ ≠ 0 → Nat.Coprime (Ideal.absNorm cc) p → (∀ x y : Matrix (Fin N') (Fin N) D.host.E, JMB.beta S.d S.Hm (e (δ • embV D B.tor x)) (e (δ • embV D B.tor y)) = D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) / (Ideal.absNorm cc : ℂ)) → JMB.pairD lam Ω S.d S.Hm (fun i => e (δ • embV D B.tor (b i))) ((δ₀ / δ) • e (δ • embV D B.tor y)) a = pairN D lam (Ω * (Ideal.absNorm cc : ℂ_[p]) * lamC lam (δ / δ₀)) b y a := by
  intro D cc δ δ₀ B N N' g S e p _ lam Ω r b y a hq _ _ hb
  have hphi : ∀ z : D.host.E, D.host.φ₀ z ∈ Qbar := fun z => by
    have hx : IsAlgebraic ℚ z := Algebra.IsAlgebraic.isAlgebraic z
    exact (mem_algebraicClosure_iff).2 (hx.algHom D.host.φ₀.toRatAlgHom)

  have hlin : ∀ (c : ℂ) (z w : Fin g → ℂ), JMB.beta S.d S.Hm (c • z) w = c * JMB.beta S.d S.Hm z w := by
    intro c z w
    simp only [JMB.beta, JMB.hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  set n := Ideal.absNorm cc
  have key : ∀ i, JMB.lamA lam (JMB.beta S.d S.Hm ((δ₀ / δ) • e (δ • embV D B.tor y)) (e (δ • embV D B.tor (b i))))
      = (lamC lam (δ / δ₀))⁻¹ * ((n : ℂ_[p]))⁻¹ * lamC lam (D.host.φ₀ ((hYY D y (b i) : D.host.K) : D.host.E)) := by
    intro i
    rw [hlin, hb]
    set z := D.host.φ₀ ((hYY D y (b i) : D.host.K) : D.host.E)
    have hz := hphi ((hYY D y (b i) : D.host.K) : D.host.E)
    have heq : δ₀ / δ * (z / (n : ℂ)) = (((⟨δ / δ₀, hq⟩ : Qbar)⁻¹ * ((n : Qbar))⁻¹ * ⟨z, hz⟩ : Qbar) : ℂ) := by
      have hc : (((n : Qbar)) : ℂ) = (n : ℂ) := by norm_cast
      simp only [IntermediateField.coe_mul, IntermediateField.coe_inv, hc]
      rw [inv_div]; ring
    have hmem : δ₀ / δ * (z / (n : ℂ)) ∈ Qbar := by rw [heq]; exact SetLike.coe_mem _
    unfold JMB.lamA lamC
    rw [dif_pos hmem, dif_pos hq, dif_pos hz]
    have : (⟨δ₀ / δ * (z / (n : ℂ)), hmem⟩ : Qbar) = (⟨δ / δ₀, hq⟩ : Qbar)⁻¹ * ((n : Qbar))⁻¹ * ⟨z, hz⟩ := Subtype.ext heq
    rw [this, map_mul, map_mul, map_inv₀, map_inv₀, map_natCast]
  unfold JMB.pairD pairN
  simp only [key]
  have hzc : ∀ i, JMB.zc (a i) = zc (a i) := fun i => rfl
  simp only [hzc, mul_inv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.MomFin
end

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_scaledDirections_eq_period_pairing : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ) (B : Base D cc δ) (N N' : ℕ) (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p]) (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (y : Matrix (Fin N') (Fin N) D.host.E) (a : Fin r → ℤ_[p]), δ / δ₀ ∈ Qbar → δ / δ₀ ≠ 0 → Nat.Coprime (Ideal.absNorm cc) p → (∀ x y : Matrix (Fin N') (Fin N) D.host.E, JMB.beta S.d S.Hm (e (δ • embV D B.tor x)) (e (δ • embV D B.tor y)) = D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) / (Ideal.absNorm cc : ℂ)) → JMB.pairD lam Ω S.d S.Hm (fun i => e (δ • embV D B.tor (b i))) ((δ₀ / δ) • e (δ • embV D B.tor y)) a = pairN D lam (Ω * (Ideal.absNorm cc : ℂ_[p]) * lamC lam (δ / δ₀)) b y a := by
  atlas_forward_decl GlobalTheory.MomFin.pairing_scaled
end

section
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.AlgDirMom

theorem exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * c) := by
  have hc : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨z, hz0, hz⟩ := hc.exists_integral_multiple
  refine ⟨z.natAbs, Int.natAbs_pos.2 hz0, ?_⟩
  rw [zsmul_eq_mul] at hz
  rcases Int.natAbs_eq z with h | h
  · rw [h] at hz; simpa using hz
  · rw [h] at hz
    have := hz.neg
    simpa using this

theorem exists_nat_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (L' : Submodule (𝓞 E) (Fin n → E))
    (hL' : Submodule.span E (L' : Set (Fin n → E)) = ⊤) (v : Fin n → E) :
    ∃ k : ℕ, 0 < k ∧ (k : E) • v ∈ L' := by
  have hv : v ∈ Submodule.span E (L' : Set (Fin n → E)) := hL' ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    have e : ((a * b : ℕ) : E) • (x + y) = b • ((a : E) • x) + a • ((b : E) • y) := by
      rw [smul_add, ← Nat.cast_smul_eq_nsmul E b, ← Nat.cast_smul_eq_nsmul E a, smul_smul, smul_smul]
      push_cast
      rw [mul_comm (b : E) (a : E)]
    rw [e]
    exact L'.add_mem (L'.toAddSubmonoid.nsmul_mem hax b) (L'.toAddSubmonoid.nsmul_mem hby a)
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨m, hm, hint⟩ := exists_nat_mul_isIntegral c
    refine ⟨m * a, Nat.mul_pos hm ha, ?_⟩
    have h2 : (⟨(m : E) * c, hint⟩ : 𝓞 E) • ((a : E) • x) ∈ L' := L'.smul_mem _ hax
    rw [← algebraMap_smul E] at h2
    convert h2 using 1
    change _ = ((m : E) * c) • ((a : E) • x)
    rw [smul_smul, smul_smul]
    push_cast
    ring_nf

theorem exists_nat_smul_maps {E : Type} [Field E] [NumberField E] {N N' : ℕ}
    (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)) (hL : L.FG)
    (hL' : Submodule.span E (L' : Set (Fin N' → E)) = ⊤) (y : Matrix (Fin N') (Fin N) E) :
    ∃ k : ℕ, 0 < k ∧ ∀ x ∈ L, ((k : E) • y).mulVec x ∈ L' := by
  obtain ⟨s, hs⟩ := hL
  have hk : ∀ g ∈ s, ∃ k : ℕ, 0 < k ∧ (k : E) • y.mulVec g ∈ L' := fun g _ => exists_nat_smul_mem L' hL' _
  choose! kf hkpos hkmem using hk
  refine ⟨∏ g ∈ s, kf g, Finset.prod_pos fun g hg => hkpos g hg, ?_⟩
  intro x hx
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    rw [Matrix.smul_mulVec]
    rw [← Finset.mul_prod_erase s kf hg]
    push_cast
    rw [mul_comm, ← smul_smul]
    rw [← Nat.cast_prod, Nat.cast_smul_eq_nsmul]
    exact L'.toAddSubmonoid.nsmul_mem (hkmem g hg) _
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact L'.add_mem hx hy
  | smul r x _ hx =>
    rw [Matrix.mulVec_smul]
    exact L'.smul_mem r hx

end GlobalTheory.AlgDirMom

namespace GlobalTheory.AlgDirMom

theorem embV_natCast_smul {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) {N N' : ℕ} (n : ℕ)
    (y : Matrix (Fin N') (Fin N) D.host.E) :
    embV D B.tor ((n : D.host.E) • y) = (n : ℂ) • embV D B.tor y := by
  funext τ i j
  simp [embV, Base.tor, tor0]

theorem algDir_smul_embV : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ) (B : Base D cc δ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), IsCurveIdeal D cc → admitted D N N' L L' → δ / δ₀ ∈ Qbar → δ / δ₀ ≠ 0 → ∀ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') → ∀ y : Matrix (Fin N') (Fin N) D.host.E, S.AlgDir ((δ₀ / δ) • e (δ • embV D B.tor y)) := by
  intro D cc δ δ₀ B N N' L L' hcc hadm hq hq0 g S e he y
  have hδ : δ ≠ 0 := fun h => hq0 (by simp [h])
  have hδ₀ : δ₀ ≠ 0 := fun h => hq0 (by simp [h])
  obtain ⟨-, -, ⟨hLfg, -, -⟩, ⟨-, hL'sp, -⟩⟩ := hadm
  obtain ⟨n, hn, hnmap⟩ := exists_nat_smul_maps L L' hLfg hL'sp y
  have hNc : Ideal.absNorm cc ≠ 0 := fun h => hcc.1 (Ideal.absNorm_eq_zero_iff.1 h)
  have hA : (n : D.host.E) • y ∈ YYl D L L' :=
    Submodule.subset_span ⟨1, Formalism.L2.Pj.one_mem_inverse_halfDifferent D, _, Submodule.subset_span (fun x hx => hnmap x hx),
      (one_smul _ _).symm⟩
  have hw : δ * (Ideal.absNorm cc : ℂ) ∈ B.tor.abelian₂ := by
    change _ ∈ lamOf D cc δ
    exact AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem cc, by simp⟩
  have hx : (δ * (Ideal.absNorm cc : ℂ)) • embV D B.tor ((n : D.host.E) • y) ∈ La D B.tor L L' :=
    AddSubgroup.subset_closure ⟨_, hw, _, hA, rfl⟩
  have hu := (he _).2 hx
  have hc : (δ₀ / δ) / ((n : ℂ) * (Ideal.absNorm cc : ℂ)) ∈ JMB.Qbar := by
    have h1 : δ₀ / δ = (δ / δ₀)⁻¹ := (inv_div δ δ₀).symm
    rw [h1]
    exact div_mem (inv_mem hq) (mul_mem (natCast_mem _ n) (natCast_mem _ _))
  refine ⟨1, fun _ => (δ₀ / δ) / ((n : ℂ) * (Ideal.absNorm cc : ℂ)),
    fun _ => e ((δ * (Ideal.absNorm cc : ℂ)) • embV D B.tor ((n : D.host.E) • y)), fun _ => hc, fun _ => hu, ?_⟩
  rw [Fin.sum_univ_one, embV_natCast_smul, smul_smul, map_smul, map_smul, smul_smul, smul_smul]
  congr 1
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hN0 : (Ideal.absNorm cc : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hNc
  field_simp

end GlobalTheory.AlgDirMom
end
end

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicDirection_scaled_embedding : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ) (B : Base D cc δ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), IsCurveIdeal D cc → admitted D N N' L L' → δ / δ₀ ∈ Qbar → δ / δ₀ ≠ 0 → ∀ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') → ∀ y : Matrix (Fin N') (Fin N) D.host.E, S.AlgDir ((δ₀ / δ) • e (δ • embV D B.tor y)) := by
  atlas_forward_decl GlobalTheory.AlgDirMom.algDir_smul_embV
end

section
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.MomGood

theorem inOK_iff_mem_OK (d : ℕ) (z : ℂ) : GlobalTheory.MomOne.InOK d z ↔ z ∈ JMB.OK d := Iff.rfl

theorem lamA_eq_lamC {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (x : ℂ) : JMB.lamA lam x = lamC lam x := rfl

theorem main : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N₀ n : ℕ), S.d = D.host.d → (∀ x, e x ∈ S.La ↔ x ∈ La D (tor0 D cc δ) L L') → ∀ y ∈ GlobalTheory.MomT.goodLifts D (tor0 D cc δ) lam N₀ n L L', e y ∈ AddSubgroup.closure {y : Fin g → ℂ | ∃ κ ∈ JMB.OK S.d, ‖JMB.lamA lam ((starRingEnd ℂ) κ)‖ ≤ (p : ℝ) ^ (-(2 * n : ℤ)) ∧ ∃ x ∈ S.La, y = (κ * (N₀ : ℂ) / (p : ℂ) ^ n) • x} := by
  intro D cc δ N N' L L' g S e p _ lam N₀ n hd hLa y hy
  obtain ⟨-, -, hOK, hconj, -⟩ := GlobalTheory.MomDict.main D
  unfold GlobalTheory.MomT.goodLifts at hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨κ, hκ, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨D.host.φ₀ ((κ : D.host.K) : D.host.E), ?_, ?_, e x, (hLa x).2 hx, ?_⟩
    · rw [hd]
      exact (inOK_iff_mem_OK _ _).1 ((hOK _).2 ⟨κ, rfl⟩)
    · rw [lamA_eq_lamC, ← hconj]
      exact hκ
    · exact map_smul e _ x
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

end GlobalTheory.MomGood
end

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodLiftsLattice_map_mem_setup_goodLifts : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N₀ n : ℕ), S.d = D.host.d → (∀ x, e x ∈ S.La ↔ x ∈ La D (tor0 D cc δ) L L') → ∀ y ∈ GlobalTheory.MomT.goodLifts D (tor0 D cc δ) lam N₀ n L L', e y ∈ AddSubgroup.closure {y : Fin g → ℂ | ∃ κ ∈ JMB.OK S.d, ‖JMB.lamA lam ((starRingEnd ℂ) κ)‖ ≤ (p : ℝ) ^ (-(2 * n : ℤ)) ∧ ∃ x ∈ S.La, y = (κ * (N₀ : ℂ) / (p : ℂ) ^ n) • x} := by
  atlas_forward_decl GlobalTheory.MomGood.main
end

section
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory

theorem goodLift_pow_smul_mem : ∀ (g : ℕ) (S : JMB.Setup g) (p : ℕ) [Fact p.Prime] (lam : JMB.Qbar →+* ℂ_[p]) (N₀ n : ℕ), S.Ok →
    ∀ y ∈ AddSubgroup.closure {y : Fin g → ℂ | ∃ κ ∈ JMB.OK S.d,
      ‖JMB.lamA lam ((starRingEnd ℂ) κ)‖ ≤ (p : ℝ) ^ (-(2 * n : ℤ)) ∧
      ∃ x ∈ S.La, y = (κ * (N₀ : ℂ) / (p : ℂ) ^ n) • x}, ((p : ℂ) ^ n) • y ∈ S.La := by
  intro g S p _ lam N₀ n hS y hy
  have hw : ∀ x ∈ S.La, JMB.w0 S.d • x ∈ S.La := hS.2.2.2.2.2.1
  have hzs : ∀ (z : ℤ) (x : Fin g → ℂ), x ∈ S.La → ((z : ℂ)) • x ∈ S.La := by
    intro z x hx
    rw [Int.cast_smul_eq_zsmul ℂ z x]
    exact S.La.smul_mem z hx
  have hp : ((p : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨κ, ⟨u, v, hκ⟩, _, x, hx, rfl⟩ := hy
    rw [smul_smul, mul_div_cancel₀ _ hp, hκ]
    have : ((u : ℂ) + (v : ℂ) * JMB.w0 S.d) * (N₀ : ℂ) = ((u * N₀ : ℤ) : ℂ) + ((v * N₀ : ℤ) : ℂ) * JMB.w0 S.d := by
      push_cast; ring
    rw [this, add_smul, mul_smul]
    exact S.La.add_mem (hzs _ _ hx) (hzs _ _ (hw x hx))
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact S.La.add_mem ha hb
  | neg a _ ha => rw [smul_neg]; exact S.La.neg_mem ha

end GlobalTheory
end

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_pow_smul_goodLift_mem_setupLattice : ∀ (g : ℕ) (S : JMB.Setup g) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N₀ n : ℕ), S.Ok → ∀ y ∈ AddSubgroup.closure {y : Fin g → ℂ | ∃ κ ∈ JMB.OK S.d, ‖JMB.lamA lam ((starRingEnd ℂ) κ)‖ ≤ (p : ℝ) ^ (-(2 * n : ℤ)) ∧ ∃ x ∈ S.La, y = (κ * (N₀ : ℂ) / (p : ℂ) ^ n) • x}, ((p : ℂ) ^ n) • y ∈ S.La := by
  atlas_forward_decl GlobalTheory.goodLift_pow_smul_mem
end

section
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.CoefWop

lemma Hf_add_left (D : D7) (T : Tor D) {N N' : ℕ} (a b w : VC D N N') :
    Hf D T (a + b) w = Hf D T a w + Hf D T b w := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

lemma Hf_add_right (D : D7) (T : Tor D) {N N' : ℕ} (a b w : VC D N N') :
    Hf D T w (a + b) = Hf D T w a + Hf D T w b := by
  simp only [Hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, add_div]

lemma Hf_nsmul (D : D7) (T : Tor D) {N N' : ℕ} (a b : ℕ) (y t : VC D N N') :
    Hf D T (a • y) (b • t) = (a * b : ℂ) * Hf D T y t := by
  simp only [Hf, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast, mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

lemma U_U (D : D7) (T : Tor D) {N N' : ℕ} (y t : VC D N N') (F : VC D N N' → ℂ) (z : VC D N N') :
    U D T y (U D T t F) z
      = Complex.exp (-(Real.pi : ℂ) * ((Hf D T y t - Hf D T t y) / 2)) * U D T (y + t) F z := by
  simp only [U]
  rw [show z + y + t = z + (y + t) by abel]
  rw [mul_comm (Complex.exp _) (F _ * _), mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  simp only [Hf_add_left, Hf_add_right]
  ring

lemma taylor_const_mul (D : D7) {N N' : ℕ} (c : ℂ) (G : VC D N N' → ℂ) (hG : ContDiff ℂ ⊤ G)
    (α : Mono D N N') : taylor D (fun z => c * G z) α = c * taylor D G α := by
  simp only [taylor]
  have h := iteratedFDeriv_const_smul_apply (𝕜 := ℂ) (i := (Finsupp.toMultiset α).card) (a := c) (x := (0 : VC D N N'))
    (hG.contDiffAt.of_le (by exact_mod_cast le_top))
  rw [show (fun z => c * G z) = c • G from rfl, h]
  rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_div_assoc]

lemma contDiff_U (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (F : VC D N N' → ℂ)
    (hF : ContDiff ℂ ⊤ F) : ContDiff ℂ ⊤ (U D T x F) := by
  unfold U Hf
  apply ContDiff.mul
  · exact hF.comp (contDiff_id.add contDiff_const)
  · apply ContDiff.cexp
    apply ContDiff.sub _ contDiff_const
    apply ContDiff.mul contDiff_const
    apply ContDiff.div_const
    apply ContDiff.sum fun τ _ => ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
    apply ContDiff.mul _ contDiff_const
    exact (contDiff_apply ℂ _ j).comp ((contDiff_apply ℂ _ i).comp (contDiff_apply ℂ _ τ))

lemma sq_one_alg {c : ℂ} {n : ℕ} (hn : 0 < n) (h : c ^ n = 1) : c ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  apply IsIntegral.isAlgebraic
  exact IsIntegral.of_pow hn (by rw [h]; exact isIntegral_one)

lemma Hf_swap (D : D7) (T : Tor D) {N N' : ℕ} (y t : VC D N N') :
    Hf D T t y = (starRingEnd ℂ) (Hf D T y t) := by
  simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

lemma wPh_sq (D : D7) (T : Tor D) {N N' : ℕ} (p : ℕ) (y : VC D N N') (m : ℤ) (hm : qH D T y = m) :
    wPh D T p y ^ 2 = 1 := by
  unfold wPh
  split_ifs with hp
  · rw [← Complex.exp_nat_mul, hm]
    have : ((2 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) = (m : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  · have hex : ∃ s : ℂ, ∃ k : ℕ, ∃ m' : ℤ, (p : ℝ) ^ k * qH D T y = m' ∧ s = (-1) ^ m' :=
      ⟨(-1) ^ m, 0, m, by simp [hm], rfl⟩
    obtain ⟨k, m', -, hs⟩ := Classical.epsilon_spec hex
    rw [hs, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    norm_num

lemma root_alg (D : D7) (T : Tor D) {N N' : ℕ} (y t : VC D N N') (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (k : ℤ)
    (hk : (Hf D T (a • y) (b • t)).im = k) :
    Complex.exp (-(Real.pi : ℂ) * ((Hf D T y t - Hf D T t y) / 2)) ∈ Qbar := by
  rw [Hf_nsmul] at hk
  have hk' : ((a * b : ℕ) : ℝ) * (Hf D T y t).im = k := by
    rw [← hk]; push_cast
    rw [show ((a : ℂ) * b) = (((a * b : ℝ)) : ℂ) by push_cast; ring, Complex.im_ofReal_mul]
  have hdiff : Hf D T y t - Hf D T t y = 2 * Complex.I * ((Hf D T y t).im : ℂ) := by
    rw [Hf_swap]
    apply Complex.ext <;> simp <;> ring
  apply sq_one_alg (n := 2 * (a * b)) (by positivity)
  rw [hdiff, ← Complex.exp_nat_mul]
  have : ((2 * (a * b) : ℕ) : ℂ) * (-(Real.pi : ℂ) * (2 * Complex.I * ((Hf D T y t).im : ℂ) / 2))
      = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    have hk'' : ((a * b : ℕ) : ℂ) * ((Hf D T y t).im : ℂ) = (k : ℂ) := by exact_mod_cast hk'
    push_cast at hk'' ⊢
    linear_combination (-(Real.pi : ℂ) * 2 * Complex.I) * hk''
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

end GlobalTheory.CoefWop

namespace GlobalTheory

open GlobalTheory.CoefWop in

theorem coefIn_Wop_U_translate : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (F : VC D N N' → ℂ) (Λ : AddSubgroup (VC D N N')) (p : ℕ) [Fact p.Prime] (y t : VC D N N'), ContDiff ℂ ⊤ F → (∀ s : VC D N N', (∃ a : ℕ, 0 < a ∧ a • s ∈ Λ) → CoefIn D (U D T s F) Qbar) → (∃ a : ℕ, 0 < a ∧ a • t ∈ Λ) → (∃ a : ℕ, 0 < a ∧ a • y ∈ Λ) → (∀ x ∈ Λ, ∀ x' ∈ Λ, ∃ k : ℤ, (Hf D T x x').im = k) → (∃ m : ℤ, qH D T y = m) → CoefIn D (Wop D T p y (U D T t F)) Qbar := by
  intro D T N N' F Λ p _ y t hF hΛ ⟨b, hb, hbt⟩ ⟨a, ha, hay⟩ hHf ⟨m, hm⟩
  have hfun : Wop D T p y (U D T t F)
      = fun z => (wPh D T p y * Complex.exp (-(Real.pi : ℂ) * ((Hf D T y t - Hf D T t y) / 2)))
          * U D T (y + t) F z := by
    funext z
    simp only [Wop, U_U]
    ring
  have hyt : CoefIn D (U D T (y + t) F) Qbar := by
    refine hΛ _ ⟨a * b, by positivity, ?_⟩
    rw [smul_add, mul_comm a b, mul_smul, mul_comm b a, mul_smul]
    exact Λ.add_mem (Λ.nsmul_mem hay b) (Λ.nsmul_mem hbt a)
  obtain ⟨k, hk⟩ := hHf _ hay _ hbt
  have hw : wPh D T p y ∈ Qbar := sq_one_alg (n := 2) (by norm_num) (wPh_sq D T p y m hm)
  unfold CoefIn
  intro α
  rw [hfun, taylor_const_mul D _ _ (contDiff_U D T _ F hF)]
  exact Qbar.mul_mem (Qbar.mul_mem hw (root_alg D T y t a b ha hb k hk)) (hyt α)

end GlobalTheory
end

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefIn_weilOperator_translate_algebraic : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (F : VC D N N' → ℂ) (Λ : AddSubgroup (VC D N N')) (p : ℕ) [Fact p.Prime] (y t : VC D N N'), ContDiff ℂ ⊤ F → (∀ s : VC D N N', (∃ a : ℕ, 0 < a ∧ a • s ∈ Λ) → CoefIn D (U D T s F) Qbar) → (∃ a : ℕ, 0 < a ∧ a • t ∈ Λ) → (∃ a : ℕ, 0 < a ∧ a • y ∈ Λ) → (∀ x ∈ Λ, ∀ x' ∈ Λ, ∃ k : ℤ, (Hf D T x x').im = k) → (∃ m : ℤ, qH D T y = m) → CoefIn D (Wop D T p y (U D T t F)) Qbar := by
  atlas_forward_decl GlobalTheory.coefIn_Wop_U_translate
end

section
section
noncomputable section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.MomentPinned

theorem isLocallyConstant_toZModPow {p : ℕ} [Fact p.Prime] (n : ℕ) :
    IsLocallyConstant (PadicInt.toZModPow (p := p) n) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hq : (0 : ℝ) < (p : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  filter_upwards [Metric.ball_mem_nhds x hq] with y hy
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
  rw [Metric.mem_ball, dist_eq_norm] at hy
  exact hy.le

theorem isLocallyConstant_red {p : ℕ} [Fact p.Prime] (r n : ℕ) :
    IsLocallyConstant (fun a : Fin r → ℤ_[p] => fun i => PadicInt.toZModPow n (a i)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have : ∀ i, ∀ᶠ y in nhds x, PadicInt.toZModPow n (y i) = PadicInt.toZModPow n (x i) := fun i =>
    ((isLocallyConstant_toZModPow n).comp_continuous (continuous_apply i)).eventually_eq x
  filter_upwards [Filter.eventually_all.2 this] with y hy using funext hy

theorem continuous_zc {p : ℕ} [Fact p.Prime] : Continuous (JMB.zc : ℤ_[p] → ℂ_[p]) := by
  unfold JMB.zc
  exact (continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val

theorem continuous_pairD {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p]) {g : ℕ} (d : ℕ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) {r : ℕ} (b : Fin r → Fin g → ℂ) (y : Fin g → ℂ) :
    Continuous (JMB.pairD lam Ω d Hm b y) := by
  unfold JMB.pairD
  have := continuous_zc (p := p)
  fun_prop

theorem continuous_charPart {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {g : ℕ}
    (Hm : Matrix (Fin g) (Fin g) ℂ) {r : ℕ} (n : ℕ) (b : Fin r → Fin g → ℂ) (Y : Fin g → ℂ) :
    Continuous fun a : Fin r → ℤ_[p] => JMB.lamA lam (JMB.kap Hm (JMB.vecA n b a) Y) :=
  ((isLocallyConstant_red (p := p) r n).comp (fun s : Fin r → ZMod (p ^ n) =>
    JMB.lamA lam (JMB.kap Hm (∑ i, (((s i).val : ℕ) : ℂ) • b i) Y))).continuous

theorem eq_of_natCast : ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p]) (g : ℕ) (S : JMB.Setup g) (r n k : ℕ) (bS : Fin r → Fin g → ℂ) (Y : Fin g → ℂ) (ys : Fin k → Fin g → ℂ) (f : C(Fin r → ℤ_[p], ℂ_[p])), (∀ a : Fin r → ℕ, f (fun i => (a i : ℤ_[p])) = JMB.lamA lam (JMB.kap S.Hm (JMB.vecA n bS (fun i => (a i : ℤ_[p]))) Y) * ∏ j, JMB.pairD lam Ω S.d S.Hm bS (ys j) (fun i => (a i : ℤ_[p]))) → ∀ a, f a = JMB.lamA lam (JMB.kap S.Hm (JMB.vecA n bS a) Y) * ∏ j, JMB.pairD lam Ω S.d S.Hm bS (ys j) a := by
  intro p _ lam Ω g S r n k bS Y ys f h a
  have hR : Continuous fun a : Fin r → ℤ_[p] =>
      JMB.lamA lam (JMB.kap S.Hm (JMB.vecA n bS a) Y) * ∏ j, JMB.pairD lam Ω S.d S.Hm bS (ys j) a :=
    (continuous_charPart lam S.Hm n bS Y).mul
      (continuous_finsetProd Finset.univ fun j _ => continuous_pairD lam Ω S.d S.Hm bS (ys j))
  have hd : DenseRange (fun a : Fin r → ℕ => fun i => (a i : ℤ_[p])) :=
    DenseRange.piMap fun _ : Fin r => PadicInt.denseRange_natCast (p := p)
  exact congr_fun (hd.equalizer f.continuous hR (funext h)) a

end GlobalTheory.MomentPinned
end
end

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_on_padicInt_of_eq_on_naturals_moment : ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p]) (g : ℕ) (S : JMB.Setup g) (r n k : ℕ) (bS : Fin r → Fin g → ℂ) (Y : Fin g → ℂ) (ys : Fin k → Fin g → ℂ) (f : C(Fin r → ℤ_[p], ℂ_[p])), (∀ a : Fin r → ℕ, f (fun i => (a i : ℤ_[p])) = JMB.lamA lam (JMB.kap S.Hm (JMB.vecA n bS (fun i => (a i : ℤ_[p]))) Y) * ∏ j, JMB.pairD lam Ω S.d S.Hm bS (ys j) (fun i => (a i : ℤ_[p]))) → ∀ a, f a = JMB.lamA lam (JMB.kap S.Hm (JMB.vecA n bS a) Y) * ∏ j, JMB.pairD lam Ω S.d S.Hm bS (ys j) a := by
  atlas_forward_decl GlobalTheory.MomentPinned.eq_of_natCast
end

section
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomFin

theorem U_zero (D : D7) (T : Tor D) {N N' : ℕ} (G : VC D N N' → ℂ) : U D T 0 G = G := by
  funext z; simp [U, Hf]

theorem U_transport (D : D7) (T : Tor D) {N N' g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ))
    (hhf : ∀ x y, JMB.hf Hm (e x) (e y) = Hf D T x y) (t : VC D N N') (F : VC D N N' → ℂ) :
    JMB.opU Hm (e t) (fun z => F (e.symm z)) = fun z => U D T t F (e.symm z) := by
  funext z
  have h1 : JMB.hf Hm z (e t) = Hf D T (e.symm z) t := by
    rw [← hhf]; simp
  simp only [JMB.opU, U, map_add, ContinuousLinearEquiv.symm_apply_apply, h1, hhf]
  congr 2
  ring

theorem wop_transport (D : D7) (T : Tor D) {N N' g : ℕ} (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ))
    (hhf : ∀ x y, JMB.hf S.Hm (e x) (e y) = Hf D T x y) (hd : S.d = D.host.d) (p : ℕ) [Fact p.Prime]
    (y t : VC D N N') (F : VC D N N' → ℂ) (hq : ∃ m : ℤ, (JMB.beta S.d S.Hm (e y) (e y)).re = m) :
    JMB.opW S.d S.Hm (e y) (JMB.opU S.Hm (e t) (fun z => F (e.symm z))) =
      fun z => Wop D T p y (U D T t F) (e.symm z) := by
  obtain ⟨m, hm⟩ := hq
  have hqH : qH D T y = (JMB.beta S.d S.Hm (e y) (e y)).re := by
    rw [qH, JMB.beta, hhf, hd, Complex.re_ofReal_mul]
  have hU := U_transport D T S.Hm e hhf t F
  have hUy := U_transport D T S.Hm e hhf y (U D T t F)
  funext z
  rw [JMB.opW, hU, Wop, I3.JetMomEq.wPh_of_int T y m (hqH.trans hm), hqH]
  rw [hUy]

theorem jet_transport (D : D7) {N N' g : ℕ} (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)) (G : VC D N N' → ℂ)
    (hG : ContDiff ℂ ⊤ G) (k : ℕ) (v : Fin k → VC D N N') :
    JMB.jetV (fun z => G (e.symm z)) (fun j => e (v j)) = iteratedFDeriv ℂ k G 0 v := by
  have h := (e.symm : (Fin g → ℂ) →L[ℂ] VC D N N').iteratedFDeriv_comp_right hG (0 : Fin g → ℂ) (i := k) le_top
  simp only [JMB.jetV]
  rw [show (fun z => G (e.symm z)) = G ∘ (e.symm : (Fin g → ℂ) →L[ℂ] VC D N N') from rfl, h]
  simp

theorem embV_sum (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' r : ℕ} (a : Fin r → ℕ)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (∑ i, ((a i : ℕ) : D.host.E) • b i) = ∑ i, ((a i : ℕ) : ℂ) • embV D (tor0 D cc δ) (b i) := by
  funext τ i j
  simp [embV, tor0, Finset.sum_apply, Matrix.sum_apply, map_sum]

theorem kap_transport (D : D7) (T : Tor D) {N N' g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ))
    (hhf : ∀ x y, JMB.hf Hm (e x) (e y) = Hf D T x y) (x y : VC D N N') : kap D T x y = JMB.kap Hm (e x) (e y) := by
  simp only [kap, JMB.kap, hhf]

theorem moments_fin : (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ) → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ t : VC D N N', (∃ a : ℕ, 0 < a ∧ a • t ∈ La D B.tor L L') → ∀ α, taylor D (U D B.tor t (B.eNat χ N N' L L')) α ∈ Qbar) → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ≠ 2 → jacobiSym (-(D.host.d : ℤ)) p = 1 → Nat.Coprime (Ideal.absNorm cc) p → ∃ Ω : ℂ_[p], ‖Ω‖ = 1 ∧ GlobalTheory.MomT.MomentsAt D cc δ (B.eNat χ) lam Ω) := by
  intro hMv hAlg D cc δ B χ hcc hδ hχ p _ lam hp2 hjac hcop
  obtain ⟨hdp, hd16, -, -, -⟩ := GlobalTheory.T.cmBaseField_integers_and_curveIdeal_facts D
  have hSplit : GlobalTheory.MomOne.Split D.host.d p := Or.inr ⟨hp2, hjac⟩
  obtain ⟨ι, hι⟩ := GlobalTheory.PadicComplexIso.exists_ringEquiv_extending p lam
  obtain ⟨δ₀, θ, Ω, hPer⟩ := GlobalTheory.MomN.exists_per D.host.d p ι hdp hd16 hSplit
  obtain ⟨hTh, h12, hδ₀, hAll, hΩ, hLaws, hPerM⟩ := hPer
  obtain ⟨hQ, hUn⟩ := GlobalTheory.T.discOneScale_ratio_ideal_ring_algebraic_unit D cc δ δ₀ hcc hδ h12 p hp2 hcop
  have hne : δ / δ₀ ≠ 0 := by
    intro h; have := hUn ι; rw [h, map_zero, norm_zero] at this; exact zero_ne_one this
  have hδ0 : δ ≠ 0 := by intro h; apply hne; rw [h, zero_div]
  have hlam : lamC lam (δ / δ₀) = ι (δ / δ₀) := by rw [lamC, dif_pos hQ]; exact (hι ⟨_, hQ⟩).symm
  refine ⟨Ω * (Ideal.absNorm cc : ℂ_[p]) * lamC lam (δ / δ₀), ?_, ?_⟩
  · rw [norm_mul, norm_mul, hΩ, hlam, hUn ι, GlobalTheory.MomOne.Basic.norm_nat_eq_one (Nat.Coprime.symm hcop)]
    norm_num
  intro N N' L L' hA t ht
  obtain ⟨g, S, e, hSd, hSok, hLa, hhf, hbeta, hLaRep, hNN⟩ := GlobalTheory.T.exists_analyticSetup_periodLatticePair D cc δ B hcc hδ N N' L L' hA
  obtain ⟨N₀, hN₀, hN₀p, hN₀t⟩ := ht
  have hHm : S.Hm.IsHermitian := hSok.2.2.1.1
  have hd0 : 0 < S.d := hSd ▸ hdp.pos
  have hH := GlobalTheory.HeisOps.heisenberg g S.d S.Hm hd0 hHm
  refine ⟨N₀, hN₀p, fun r b hb => ?_⟩
  set F := B.eNat χ N N' L L' with hFdef
  set e' : (Fin g → ℂ) → ℂ := fun z => F (e.symm z) with he'
  have hTheta : S.IsTheta e' := GlobalTheory.T.normalizedThetaVector_isometry_isTheta D cc δ B χ hcc hδ hχ hδ0 N N' L L' hA g S e hSd hLa hhf
  have hF : ContDiff ℂ ⊤ F := by
    have : F = fun x => e' (e x) := by funext x; simp [e']
    rw [this]; exact hTheta.1.comp e.contDiff
  have hAlg0 : ∀ α, taylor D F α ∈ Qbar := by
    have := hAlg D cc δ B χ hcc hδ hχ N N' L L' hA 0 ⟨1, one_pos, by simp⟩
    simpa [U_zero] using this
  have hAJ : S.AlgJets δ₀ e' := GlobalTheory.T.algebraicJets_of_algebraic_taylor D cc δ δ₀ B N N' L L' F hQ hδ₀ hF hAlg0 g S e hLa hLaRep
  set bS : Fin r → Fin g → ℂ := fun i => e (δ • embV D B.tor (b i)) with hbSdef
  have hbS : S.NNBasis p bS := hNN p r b hcop hb
  have hN₀S : (N₀ : ℂ) • e t ∈ S.La := by
    rw [← map_smul, Nat.cast_smul_eq_nsmul, hLa]; exact hN₀t
  have ht' : S.PrimeTo p (e t) := ⟨N₀, hN₀, hN₀p, hN₀S⟩
  obtain ⟨Nμ, hμall⟩ := GlobalTheory.MomOne.Translates.moments_of_translates D.host.d p lam δ₀ θ ι Ω hdp hd16 hSplit hTh hδ₀
    hAll hι hΩ hLaws g S hSd hSok r bS hbS e' hTheta hAJ
  obtain ⟨μ, -, hM1⟩ := hμall (e t) ht'
  have hUt : JMB.opU S.Hm (e t) e' = fun z => U D B.tor t F (e.symm z) := U_transport D B.tor S.Hm e hhf t F
  have hUF : ContDiff ℂ ⊤ (U D B.tor t F) := by
    have : U D B.tor t F = fun x => JMB.opU S.Hm (e t) e' (e x) := by funext x; rw [hUt]; simp
    rw [this]; exact ((hH.2.2.1 (e t) e' hTheta.1).1).comp e.contDiff
  have hnorm : ‖μ‖ ≤ 1 := by
    have hG : ContDiff ℂ ⊤ (JMB.opU S.Hm (e t) e') := (hH.2.2.1 (e t) e' hTheta.1).1
    refine (GlobalTheory.T.momentMeasure_norm_le_one_iff_latticeIntegral p ι lam δ₀ Ω g S r bS (e t) _ μ hι hδ₀ hΩ hSok (hSd ▸ hSplit) hbS ht' hG hM1).2 ?_
    rw [hUt]
    have hE := GlobalTheory.T.normalizedVector_translates_prime_order_integral hMv D cc δ B hcc hδ p hp2 hjac hcop ι δ₀ θ Ω ⟨hTh, h12, hδ₀, hAll, hΩ, hLaws, hPerM⟩ χ hχ
      N N' L L' hA t ⟨N₀, hN₀, hN₀p, hN₀t⟩
    exact GlobalTheory.T.latticeJetsAreBoundedMoments_pullback p ι (VC D N N') (Fin g → ℂ) _ (La D B.tor L L') S.La.toAddSubgroup
      (e.symm : (Fin g → ℂ) →L[ℂ] VC D N N') (U D B.tor t F) hUF
      (fun x hx => ⟨1, Nat.coprime_one_left _, by
        rw [one_smul, ← hLa]; simpa using hx⟩) hE
  refine ⟨μ, hnorm, fun n y hy => ?_⟩
  have hyS := GlobalTheory.T.goodLiftsLattice_map_mem_setup_goodLifts D cc δ N N' L L' g S e p lam N₀ n hSd hLa y hy
  obtain ⟨hqy, m, eps, yt, hId, hm, hIm, hW, hK⟩ :=
    GlobalTheory.T.goodLift_eq_idempotent_lift p lam g S r bS e' (e t) hSok (hSd ▸ hSplit) hbS hTheta N₀ hN₀ hN₀p hN₀S n (e y) hyS
  set G := Wop D B.tor p y (U D B.tor t F) with hGdef
  have hWt : JMB.opW S.d S.Hm (e y) (JMB.opU S.Hm (e t) e') = fun z => G (e.symm z) :=
    wop_transport D B.tor S e hhf hSd p y t F hqy
  have hGc : ContDiff ℂ ⊤ G := by
    have : G = fun x => JMB.opW S.d S.Hm (e y) (JMB.opU S.Hm (e t) e') (e x) := by funext x; rw [hWt]; simp
    rw [this]; exact ((hH.2.2.1 (e y) _ (hH.2.2.1 (e t) e' hTheta.1).1).2).comp e.contDiff
  have hImLa : ∀ x ∈ La D B.tor L L', ∀ x' ∈ La D B.tor L L', ∃ k : ℤ, (Hf D B.tor x x').im = k := by
    intro x hx x' hx'
    obtain ⟨u, v, huv⟩ := hSok.2.2.2.2.2.2.1 (e x) ((hLa x).2 hx) (e x') ((hLa x').2 hx')
    exact ⟨v, by rw [← hhf]; exact hH.2.2.2.2.1 _ _ u v huv⟩
  have hyT : ∃ a : ℕ, 0 < a ∧ a • y ∈ La D B.tor L L' := by
    refine ⟨p ^ n, pow_pos (Fact.out : p.Prime).pos n, ?_⟩
    rw [← hLa, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ]
    push_cast
    exact GlobalTheory.T.prime_pow_smul_goodLift_mem_setupLattice g S p lam N₀ n hSok (e y) hyS
  have hqH : ∃ m : ℤ, qH D B.tor y = m := by
    obtain ⟨z, hz⟩ := hqy
    refine ⟨z, ?_⟩
    rw [qH, ← hz, JMB.beta, hhf, hSd, Complex.re_ofReal_mul]
  have hCoef : CoefIn D G Qbar := GlobalTheory.T.coefIn_weilOperator_translate_algebraic D B.tor N N' F (La D B.tor L L') p y t hF
    (fun s hs α => hAlg D cc δ B χ hcc hδ hχ N N' L L' hA s hs α) ⟨N₀, hN₀, hN₀t⟩ hyT hImLa hqH
  refine ⟨hCoef, fun k y' gf hg => ?_⟩
  set ys : Fin k → Fin g → ℂ := fun j => (δ₀ / δ) • e (δ • embV D B.tor (y' j)) with hysdef
  have hys : ∀ j, S.AlgDir (ys j) := fun j => GlobalTheory.T.algebraicDirection_scaled_embedding D cc δ δ₀ B N N' L L' hcc hA hQ hne g S e hLa (y' j)
  have hdir : ∀ j, δ₀⁻¹ • ys j = e (embV D B.tor (y' j)) := by
    intro j
    simp only [ys, map_smul, smul_smul]
    rw [show δ₀⁻¹ * (δ₀ / δ * δ) = 1 by field_simp, one_smul]
  have hf := GlobalTheory.T.eq_on_padicInt_of_eq_on_naturals_moment p lam Ω g S r n k bS (JMB.liftY p n eps bS yt) ys gf (fun a => by
    rw [hg a, ← hK a, kap_transport D B.tor S.Hm e hhf, embV_sum]
    have hs : e (δ • ∑ i, ((a i : ℕ) : ℂ) • embV D (tor0 D cc δ) (b i)) = ∑ i, ((a i : ℕ) : ℂ) • bS i := by
      simp only [bS, Finset.smul_sum, map_sum, map_smul, smul_comm δ]
    rw [hs]
    congr 1
    exact Finset.prod_congr rfl fun j _ => (GlobalTheory.T.pairing_scaledDirections_eq_period_pairing D cc δ δ₀ B N N' g S e p lam Ω r b (y' j) _ hQ hne hcop hbeta).symm)
  obtain ⟨-, hμf⟩ := hM1 n m eps hId hm (fun _ i => hIm i) yt k ys hys gf hf
  rw [← hW, hWt] at hμf
  simp only [hdir] at hμf
  rw [jet_transport D e G hGc k] at hμf
  obtain ⟨-, hjet⟩ := GlobalTheory.T.iteratedFDeriv_algebraic_directions_jet_transport D cc δ p lam N N' G hGc hCoef k y'
  rw [hjet, ← hμf]
  rfl

end GlobalTheory.MomFin
end

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitPeriodTranslates_moments_finite : (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ) → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ t : VC D N N', (∃ a : ℕ, 0 < a ∧ a • t ∈ La D B.tor L L') → ∀ α, taylor D (U D B.tor t (B.eNat χ N N' L L')) α ∈ Qbar) → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ≠ 2 → jacobiSym (-(D.host.d : ℤ)) p = 1 → Nat.Coprime (Ideal.absNorm cc) p → ∃ Ω : ℂ_[p], ‖Ω‖ = 1 ∧ GlobalTheory.MomT.MomentsAt D cc δ (B.eNat χ) lam Ω) := by
  atlas_forward_decl GlobalTheory.MomFin.moments_fin
end
