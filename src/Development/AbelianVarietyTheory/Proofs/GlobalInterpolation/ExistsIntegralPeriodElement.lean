import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignedLogMeans
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.EquidistributedConjugates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PeriodLatticeAgreement
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JacobiThetaHalfCharacteristic
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DifferentiableAtDerivAtZero
import Formalism.GL3MeanSquares.HookFormulaTorsion.FourFoldOrthogonalSum

section
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.Glob.ThetaParity

open Complex

theorem jacobiTheta₂_add_int (z τ : ℂ) (k : ℤ) :
    jacobiTheta₂ (z + (k : ℂ)) τ = jacobiTheta₂ z τ := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have : z + ((k + 1 : ℤ) : ℂ) = (z + (k : ℂ)) + 1 := by push_cast; ring
    rw [this, jacobiTheta₂_add_left]; exact_mod_cast ih
  | pred k ih =>
    have : z + ((-(k : ℤ) : ℤ) : ℂ) = (z + ((-(k : ℤ) - 1 : ℤ) : ℂ)) + 1 := by push_cast; ring
    have ih' : jacobiTheta₂ (z + ((-(k : ℤ) : ℤ) : ℂ)) τ = jacobiTheta₂ z τ := by exact_mod_cast ih
    rw [← ih', this, jacobiTheta₂_add_left]

theorem jacobiTheta₂_add_int_mul_eq_zero_iff (z τ : ℂ) (l : ℤ) :
    jacobiTheta₂ (z + (l : ℂ) * τ) τ = 0 ↔ jacobiTheta₂ z τ = 0 := by
  induction l using Int.induction_on with
  | zero => simp
  | succ l ih =>
    have : z + ((l + 1 : ℤ) : ℂ) * τ = (z + (l : ℂ) * τ) + τ := by push_cast; ring
    have ih' : jacobiTheta₂ (z + ((l : ℤ) : ℂ) * τ) τ = 0 ↔ jacobiTheta₂ z τ = 0 := by exact_mod_cast ih
    rw [this, jacobiTheta₂_add_left', mul_eq_zero, or_iff_right (Complex.exp_ne_zero _)]
    exact_mod_cast ih'
  | pred l ih =>
    have : z + ((-(l : ℤ) : ℤ) : ℂ) * τ = (z + ((-(l : ℤ) - 1 : ℤ) : ℂ) * τ) + τ := by push_cast; ring
    have ih' : jacobiTheta₂ (z + ((-(l : ℤ) : ℤ) : ℂ) * τ) τ = 0 ↔ jacobiTheta₂ z τ = 0 := by exact_mod_cast ih
    rw [← ih', this, jacobiTheta₂_add_left', mul_eq_zero, or_iff_right (Complex.exp_ne_zero _)]

theorem jacobiTheta₂_shift_eq_zero_iff (z τ : ℂ) (k l : ℤ) :
    jacobiTheta₂ (z + (k : ℂ) + (l : ℂ) * τ) τ = 0 ↔ jacobiTheta₂ z τ = 0 := by
  rw [jacobiTheta₂_add_int_mul_eq_zero_iff, jacobiTheta₂_add_int]

theorem thetaChar_half_period_eq_zero_iff :
    ∀ τ : UpperHalfPlane, ThetaConstantWeber.JacobiProduct τ → ∀ (m n : ℤ) (a b : Fin 2),
    JacobiThetaHalfCharacteristic.IsEvenChar a b →
    (JacobiThetaHalfCharacteristic.thetaChar a b (((m : ℂ) + (n : ℂ) * (τ : ℂ)) / 2) (τ : ℂ) = 0 ↔
      Odd (m + ((b : ℕ) : ℤ)) ∧ Odd (n + ((a : ℕ) : ℤ))) := by
  intro τ hJ m n a b _
  set t : ℂ := (τ : ℂ)

  have hprod : ThetaConstantWeber.thetaConst 0 0 τ * ThetaConstantWeber.thetaConst 0 1 τ * ThetaConstantWeber.thetaConst 1 0 τ ≠ 0 := by
    rw [hJ]
    exact mul_ne_zero two_ne_zero (pow_ne_zero _ (ModularForm.eta_ne_zero τ.2))
  have h00 : jacobiTheta₂ 0 t ≠ 0 := by
    have := left_ne_zero_of_mul (left_ne_zero_of_mul hprod)
    simpa [ThetaConstantWeber.thetaConst, t] using this
  have h01 : jacobiTheta₂ (1 / 2) t ≠ 0 := by
    have := right_ne_zero_of_mul (left_ne_zero_of_mul hprod)
    simpa [ThetaConstantWeber.thetaConst, t] using this
  have h10 : jacobiTheta₂ (t / 2) t ≠ 0 := by
    have := right_ne_zero_of_mul hprod
    simp only [ThetaConstantWeber.thetaConst, mul_eq_zero, Complex.exp_ne_zero, false_or, ne_eq] at this
    simpa [t] using this
  have h11 : jacobiTheta₂ ((1 + t) / 2) t = 0 := by
    rw [add_comm]; exact GlobalTheory.JacobiDeriv.jacobiTheta₂_half_period t

  set p : ℤ := m + ((b : ℕ) : ℤ)
  set q : ℤ := n + ((a : ℕ) : ℤ)
  have hred : JacobiThetaHalfCharacteristic.thetaChar a b (((m : ℂ) + (n : ℂ) * t) / 2) t = 0 ↔
      jacobiTheta₂ ((((p % 2 : ℤ) : ℂ) + ((q % 2 : ℤ) : ℂ) * t) / 2 + ((p / 2 : ℤ) : ℂ) +
        ((q / 2 : ℤ) : ℂ) * t) t = 0 := by
    unfold JacobiThetaHalfCharacteristic.thetaChar
    rw [mul_eq_zero, or_iff_right (Complex.exp_ne_zero _)]
    have hp := Int.emod_add_mul_ediv p 2
    have hq := Int.emod_add_mul_ediv q 2
    have hp' : ((p % 2 : ℤ) : ℂ) + 2 * ((p / 2 : ℤ) : ℂ) = (m : ℂ) + ((b : ℕ) : ℂ) := by
      exact_mod_cast hp
    have hq' : ((q % 2 : ℤ) : ℂ) + 2 * ((q / 2 : ℤ) : ℂ) = (n : ℂ) + ((a : ℕ) : ℂ) := by
      exact_mod_cast hq
    have : ((m : ℂ) + (n : ℂ) * t) / 2 + (((a : ℕ) : ℂ) * t + ((b : ℕ) : ℂ)) / 2 =
        ((((p % 2 : ℤ) : ℂ) + ((q % 2 : ℤ) : ℂ) * t) / 2 + ((p / 2 : ℤ) : ℂ) +
        ((q / 2 : ℤ) : ℂ) * t) := by
      linear_combination (-(1:ℂ)/2) * hp' + (-(t:ℂ)/2) * hq'
    rw [this]
  rw [hred, jacobiTheta₂_shift_eq_zero_iff, Int.odd_iff, Int.odd_iff]
  rcases Int.emod_two_eq_zero_or_one p with hp | hp <;>
    rcases Int.emod_two_eq_zero_or_one q with hq | hq <;>
    rw [hp, hq] <;> push_cast
  · simpa using h00
  · simpa using h10
  · simpa using h01
  · simpa [add_comm] using h11

end GlobalTheory.Glob.ThetaParity
end

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChar_half_period_eq_zero_iff_odd_add_odd_add : ∀ τ : UpperHalfPlane, ThetaConstantWeber.JacobiProduct τ → ∀ (m n : ℤ) (a b : Fin 2),
    JacobiThetaHalfCharacteristic.IsEvenChar a b →
    (JacobiThetaHalfCharacteristic.thetaChar a b (((m : ℂ) + (n : ℂ) * (τ : ℂ)) / 2) (τ : ℂ) = 0 ↔
      Odd (m + ((b : ℕ) : ℤ)) ∧ Odd (n + ((a : ℕ) : ℤ))) := by
  atlas_forward_decl GlobalTheory.Glob.ThetaParity.thetaChar_half_period_eq_zero_iff
end

section
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

noncomputable section

namespace GlobalTheory.HalfPeriodValue

open Formalism.MainNotions.StandardLatticesGL3 (wpF cj FixK rhoBar StarPt w0 InRationalLattice)

theorem wpF_add_of_mem {Λ : AddSubgroup ℂ} (h : GlobalTheory.ThetaConj.IsLat Λ) {z ω : ℂ} (hz : z ∉ Λ)
    (hω : ω ∈ Λ) : wpF Λ (z + ω) = wpF Λ z := by
  obtain ⟨L, hL⟩ := h.exists_periodPair
  have hd := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ hL
  have hzω : z + ω ∉ Λ := fun hh => hz (by simpa using Λ.sub_mem hh hω)
  rw [(hd.2.2.2.2.1 _ hzω).1, (hd.2.2.2.2.1 _ hz).1]
  exact L.weierstrassP_add_coe z ⟨ω, (hL ω).1 hω⟩

theorem cmGenerator_mul_mem_curveLattice {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) :
    ∀ z ∈ lamOf D cc δ, w0 D * z ∈ lamOf D cc δ := by
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  rw [← ha]
  exact (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ h).2.2.2.2 a

theorem key_of_fix {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ)
    (ρ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (hK : FixK D ⊤ ρ) {t t' : ℂ}
    (ht : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t)
    (ht' : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamConj ⊤ ρ (lamOf D cc δ)) t') :
    t' ∉ lamConj ⊤ ρ (lamOf D cc δ) ∧
      wpF (lamConj ⊤ ρ (lamOf D cc δ)) t' = cj ⊤ ρ (wpF (lamOf D cc δ) t) := by
  obtain ⟨hex, -, -, -, hmul, hord, -⟩ :=
    GlobalTheory.T.galStar_complexMultiplication_points D cc δ h ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top
  obtain ⟨cc', δ', h', -, hL⟩ :=
    GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D cc δ h ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top 1 one_pos
  rw [GlobalTheory.ThetaConj.twoTorsionCMPoint_iff] at ht ht'
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have ha' : D.host.φ₀ ((((1 - a : 𝓞 D.host.K) : D.host.K) : D.host.E)) = 1 - w0 D := by
    rw [← ha]
    change D.host.φ₀ (algebraMap D.host.K D.host.E (algebraMap (𝓞 D.host.K) D.host.K (1 - a))) = _
    rw [map_sub, map_sub, map_sub, map_one, map_one, map_one]
    rfl
  have htn : t ∉ lamOf D cc δ := fun hh => ht.2.1 (cmGenerator_mul_mem_curveLattice h _ hh)
  obtain ⟨t'', ht''⟩ := hex t ⟨2, by norm_num, by exact_mod_cast ht.1⟩
    (Or.inr ⟨IntermediateField.mem_top, IntermediateField.mem_top⟩)
  have e2 := (hord 2 _ _ ht'').1 (by exact_mod_cast ht.1)
  have ea := (hord 1 _ _ (hmul a _ _ ht'')).2
  have eb := (hord 1 _ _ (hmul (1 - a) _ _ ht'')).2
  rw [ha] at ea
  rw [ha'] at eb
  simp only [Nat.cast_one, one_mul, Nat.cast_ofNat] at e2 ea eb
  obtain ⟨k, hk⟩ := GlobalTheory.ThetaConj.weylMatrix_mul_apply D
  have hlat : GlobalTheory.ThetaConj.IsLat (lamConj ⊤ ρ (lamOf D cc δ)) := hL ▸ GlobalTheory.ThetaConj.isLat_lamOf h'
  have hdiff : t' - t'' ∈ lamConj ⊤ ρ (lamOf D cc δ) :=
    GlobalTheory.ThetaConj.two_torsion_unique hlat (w0 D) k hk ht'.1 ht'.2.1 ht'.2.2 e2
      (fun hh => ht.2.1 (ea hh)) (fun hh => ht.2.2 (eb hh)) (by rw [hL]; exact cmGenerator_mul_mem_curveLattice h')
  rcases ht'' with ⟨hin, -⟩ | ⟨-, hn'', -, -, hwp, -⟩
  · exact absurd hin htn
  · refine ⟨fun hh => hn'' (by simpa using (lamConj ⊤ ρ (lamOf D cc δ)).sub_mem hh hdiff), ?_⟩
    rw [← hwp, ← wpF_add_of_mem hlat hn'' hdiff, add_sub_cancel]

theorem wpF_conj (Λ : AddSubgroup ℂ) (z : ℂ) :
    wpF (Λ.map (starRingEnd ℂ).toAddMonoidHom) (starRingEnd ℂ z) = starRingEnd ℂ (wpF Λ z) := by
  let e : {w : ℂ // w ∈ Λ ∧ w ≠ 0} ≃
      {w : ℂ // w ∈ Λ.map (starRingEnd ℂ).toAddMonoidHom ∧ w ≠ 0} :=
    { toFun := fun w => ⟨starRingEnd ℂ w, by rw [GlobalTheory.ThetaConj.mem_conj, Complex.conj_conj]; exact w.2.1,
        by simpa using w.2.2⟩
      invFun := fun w => ⟨starRingEnd ℂ w, GlobalTheory.ThetaConj.mem_conj.1 w.2.1, by simpa using w.2.2⟩
      left_inv := fun w => by ext; simp
      right_inv := fun w => by ext; simp }
  unfold wpF
  rw [map_add, Complex.conj_tsum, ← e.tsum_eq]
  simp [e, map_sub]
  rfl

theorem key_top {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ)
    (ρ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) {t t' : ℂ}
    (ht : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t)
    (ht' : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamConj ⊤ ρ (lamOf D cc δ)) t') :
    t' ∉ lamConj ⊤ ρ (lamOf D cc δ) ∧
      wpF (lamConj ⊤ ρ (lamOf D cc δ)) t' = cj ⊤ ρ (wpF (lamOf D cc δ) t) := by
  obtain ⟨hK, hT, -⟩ := GlobalTheory.T.cmTheta_complexConjugation_compatible D cc δ h ⊤ ρ
    ⟨fun _ _ => IntermediateField.mem_top, IntermediateField.mem_top, IntermediateField.mem_top⟩
  rcases hK with hK | hK
  · exact key_of_fix h ρ hK ht ht'
  · have hL : lamConj ⊤ (rhoBar ⊤ ρ) (lamOf D cc δ) =
        (lamConj ⊤ ρ (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom := congrArg Tor.abelian₂ hT
    obtain ⟨hn, hw⟩ := key_of_fix h _ hK (t' := starRingEnd ℂ t') ht (hL ▸ GlobalTheory.ThetaConj.twoTorsionCMPoint_complexConj ht')
    rw [hL, wpF_conj, GlobalTheory.ThetaConj.cj_rhoBar] at hw
    rw [hL, GlobalTheory.ThetaConj.mem_conj, Complex.conj_conj] at hn
    exact ⟨hn, (starRingEnd ℂ).injective hw⟩

theorem halfPeriod_value : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t →
    ∃ e g : M, (g : ℂ) = g2 (lamOf D cc δ) ∧ lamConj M M.val (lamOf D cc δ) = lamOf D cc δ ∧
      ∀ ρ : M →ₐ[ℚ] ℂ, Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧
        g2 (lamConj M ρ (lamOf D cc δ)) = ρ g ∧ t ρ ∉ lamConj M ρ (lamOf D cc δ) ∧
        Formalism.MainNotions.StandardLatticesGL3.wpF (lamConj M ρ (lamOf D cc δ)) (t ρ) = ρ e := by
  intro D cc δ M _ t hS
  obtain ⟨hcc, hδ, hdata, ht⟩ := hS
  have h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have hg2 : g2 (lamOf D cc δ) ∈ M := hdata.2.1
  have hg3 : g3 (lamOf D cc δ) ∈ M := hdata.2.2
  have hlat := GlobalTheory.ThetaConj.isLat_lamOf h
  have hdisc : Formalism.MainNotions.TaylorLogMetric.discr (lamOf D cc δ) = 1 :=
    (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ h).2.2.1
  have hself : lamConj M M.val (lamOf D cc δ) = lamOf D cc δ :=
    GlobalTheory.ThetaConj.lamConj_eq_self hlat
      (by unfold Formalism.MainNotions.StandardLatticesGL3.cj Formalism.MainNotions.TaylorLogMetric.liftM; rw [dif_pos hg2]; rfl)
      (by unfold Formalism.MainNotions.StandardLatticesGL3.cj Formalism.MainNotions.TaylorLogMetric.liftM; rw [dif_pos hg3]; rfl)
  have ht0 : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) (t M.val) := by
    have := ht M.val
    rw [hself] at this
    exact this
  have he : wpF (lamOf D cc δ) (t M.val) ∈ M := by
    obtain ⟨y, hy⟩ := GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := M)
      (wpF (lamOf D cc δ) (t M.val)) (fun σ => by
        have hσ : ∀ z ∈ M, cj ⊤ (GlobalTheory.ThetaConj.topHom (σ : ℂ →+* ℂ)) z = z := fun z hz => by
          rw [GlobalTheory.ThetaConj.cj_top]; exact σ.commutes ⟨z, hz⟩
        have hL := GlobalTheory.ThetaConj.lamConj_eq_self hlat (hσ _ hg2) (hσ _ hg3)
        have := (key_top h (GlobalTheory.ThetaConj.topHom (σ : ℂ →+* ℂ)) ht0 (by rw [hL]; exact ht0)).2
        rw [hL, GlobalTheory.ThetaConj.cj_top] at this
        exact this.symm)
    rw [← hy]
    exact y.2
  have hg2M : Formalism.MainNotions.TaylorLogMetric.liftM M (g2 (lamOf D cc δ)) = ⟨_, hg2⟩ := by simp [Formalism.MainNotions.TaylorLogMetric.liftM, hg2]
  have hg3M : Formalism.MainNotions.TaylorLogMetric.liftM M (g3 (lamOf D cc δ)) = ⟨_, hg3⟩ := by simp [Formalism.MainNotions.TaylorLogMetric.liftM, hg3]
  have hone : (⟨_, hg2⟩ : M) ^ 3 - 27 * (⟨_, hg3⟩ : M) ^ 2 = 1 :=
    by
    have := hdisc
    unfold Formalism.MainNotions.TaylorLogMetric.discr at this
    ext; push_cast; exact this
  refine ⟨⟨_, he⟩, ⟨_, hg2⟩, rfl, hself, fun ρ => ?_⟩
  have hρ1 : ρ ⟨_, hg2⟩ ^ 3 - 27 * ρ ⟨_, hg3⟩ ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, ← map_ofNat ρ 27, ← map_mul, ← map_sub, hone, map_one]
  have hspec : g2 (lamConj M ρ (lamOf D cc δ)) = ρ ⟨_, hg2⟩ ∧
      g3 (lamConj M ρ (lamOf D cc δ)) = ρ ⟨_, hg3⟩ := by
    obtain ⟨L0, hL0⟩ := hlat.exists_periodPair
    obtain ⟨L', h2', h3'⟩ := (GlobalTheory.LatticeInvariants.invariants_dictionary L0 _ hL0).2.2.2.2.2.2 _ _
      (by rw [hρ1]; exact one_ne_zero)
    have hw := GlobalTheory.LatticeInvariants.invariants_dictionary L' L'.lattice.toAddSubgroup (fun _ => Iff.rfl)
    have hs := Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ =>
      g2 Λ' = ρ (Formalism.MainNotions.TaylorLogMetric.liftM M (g2 (lamOf D cc δ))) ∧
        g3 Λ' = ρ (Formalism.MainNotions.TaylorLogMetric.liftM M (g3 (lamOf D cc δ))))
      ⟨L'.lattice.toAddSubgroup, by rw [hw.1, h2', hg2M], by rw [hw.2.1, h3', hg3M]⟩
    exact ⟨hs.1.trans (congrArg ρ hg2M), hs.2.trans (congrArg ρ hg3M)⟩
  have hcM : Set.Countable (M : Set ℂ) := (Algebraic.countable ℚ ℂ).mono fun x hx =>
    show IsAlgebraic ℚ x from
      (IntermediateField.isAlgebraic_iff (x := (⟨x, hx⟩ : M))).mp (Algebra.IsAlgebraic.isAlgebraic _)
  haveI : Countable M := hcM.to_subtype
  obtain ⟨σ, hσ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq (K := M) M.val.toRingHom ρ.toRingHom
  have hcj : ∀ z (hz : z ∈ M), cj M ρ z = cj ⊤ (GlobalTheory.ThetaConj.topHom σ.toRingHom) z := fun z hz => by
    rw [GlobalTheory.ThetaConj.cj_of_mem _ _ hz, GlobalTheory.ThetaConj.cj_top]
    exact (hσ ⟨z, hz⟩).symm
  have hL : lamConj M ρ (lamOf D cc δ) = lamConj ⊤ (GlobalTheory.ThetaConj.topHom σ.toRingHom) (lamOf D cc δ) :=
    GlobalTheory.ThetaConj.lamConj_congr (hcj _ hg2) (hcj _ hg3)
  have ht' : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamConj ⊤ (GlobalTheory.ThetaConj.topHom σ.toRingHom) (lamOf D cc δ)) (t ρ) := by
    have := ht ρ
    rw [hL] at this
    exact this
  obtain ⟨hn, hw⟩ := key_top h (GlobalTheory.ThetaConj.topHom σ.toRingHom) ht0 ht'
  refine ⟨?_, hspec.1, hL ▸ hn, ?_⟩
  · unfold Formalism.MainNotions.TaylorLogMetric.discr
    rw [hspec.1, hspec.2, hρ1]
  · rw [hL, hw, GlobalTheory.ThetaConj.cj_top]
    exact hσ ⟨_, he⟩

end GlobalTheory.HalfPeriodValue
end
end

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfPeriod_weierstrassValue_mem_conj : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t →
    ∃ e g : M, (g : ℂ) = g2 (lamOf D cc δ) ∧ lamConj M M.val (lamOf D cc δ) = lamOf D cc δ ∧
      ∀ ρ : M →ₐ[ℚ] ℂ, Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧
        g2 (lamConj M ρ (lamOf D cc δ)) = ρ g ∧ t ρ ∉ lamConj M ρ (lamOf D cc δ) ∧
        Formalism.MainNotions.StandardLatticesGL3.wpF (lamConj M ρ (lamOf D cc δ)) (t ρ) = ρ e := by
  atlas_forward_decl GlobalTheory.HalfPeriodValue.halfPeriod_value
end

section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

noncomputable section
namespace GlobalTheory.IntegralX

lemma cubic_alg {e1 e2 e3 g h : ℂ} (h12 : e1 ≠ e2) (h13 : e1 ≠ e3) (h23 : e2 ≠ e3)
    (r1 : 4 * e1 ^ 3 - g * e1 - h = 0) (r2 : 4 * e2 ^ 3 - g * e2 - h = 0)
    (r3 : 4 * e3 ^ 3 - g * e3 - h = 0) :
    12 * e1 ^ 2 - g = 4 * (e1 - e2) * (e1 - e3) ∧ 12 * e2 ^ 2 - g = 4 * (e2 - e1) * (e2 - e3) ∧
      12 * e3 ^ 2 - g = 4 * (e3 - e1) * (e3 - e2) := by
  have a12 : 4 * (e1 ^ 2 + e1 * e2 + e2 ^ 2) = g :=
    mul_left_cancel₀ (sub_ne_zero.2 h12) (by linear_combination r1 - r2)
  have a13 : 4 * (e1 ^ 2 + e1 * e3 + e3 ^ 2) = g :=
    mul_left_cancel₀ (sub_ne_zero.2 h13) (by linear_combination r1 - r3)
  have s : e1 + e2 + e3 = 0 := by
    have : (e2 - e3) * (e1 + e2 + e3) = (e2 - e3) * 0 := by linear_combination (a12 - a13) / 4
    exact mul_left_cancel₀ (sub_ne_zero.2 h23) this
  obtain rfl : e3 = -e1 - e2 := by linear_combination s
  refine ⟨?_, ?_, ?_⟩ <;> linear_combination a12

lemma half_root (L : PeriodPair) {t : ℂ} (h2 : 2 * t ∈ L.lattice) (ht : t ∉ L.lattice) :
    4 * L.weierstrassP t ^ 3 - L.g₂ * L.weierstrassP t - L.g₃ = 0 := by
  have e1 := L.derivWeierstrassP_add_coe (-t) ⟨2 * t, h2⟩
  rw [L.derivWeierstrassP_neg] at e1
  have e2 : -t + 2 * t = t := by ring
  simp only [e2] at e1
  have e3 : L.derivWeierstrassP t = 0 := by linear_combination e1 / 2
  rw [← L.derivWeierstrassP_sq t ht, e3]
  simp

theorem cubic : ∀ τ : UpperHalfPlane, ThetaConstantWeber.HalfPeriodDiff τ → ThetaConstantWeber.JacobiProduct τ →
    12 * ThetaConstantWeber.wp τ (1 / 2) ^ 2 - (GlobalTheory.periodPairOfTau τ).g₂ =
        4 * (ThetaConstantWeber.wp τ (1 / 2) - ThetaConstantWeber.wp τ ((τ : ℂ) / 2)) * (ThetaConstantWeber.wp τ (1 / 2) - ThetaConstantWeber.wp τ ((1 + (τ : ℂ)) / 2)) ∧
    12 * ThetaConstantWeber.wp τ ((τ : ℂ) / 2) ^ 2 - (GlobalTheory.periodPairOfTau τ).g₂ =
        4 * (ThetaConstantWeber.wp τ ((τ : ℂ) / 2) - ThetaConstantWeber.wp τ (1 / 2)) * (ThetaConstantWeber.wp τ ((τ : ℂ) / 2) - ThetaConstantWeber.wp τ ((1 + (τ : ℂ)) / 2)) ∧
    12 * ThetaConstantWeber.wp τ ((1 + (τ : ℂ)) / 2) ^ 2 - (GlobalTheory.periodPairOfTau τ).g₂ =
        4 * (ThetaConstantWeber.wp τ ((1 + (τ : ℂ)) / 2) - ThetaConstantWeber.wp τ (1 / 2)) * (ThetaConstantWeber.wp τ ((1 + (τ : ℂ)) / 2) - ThetaConstantWeber.wp τ ((τ : ℂ) / 2)) := by
  intro τ hd hj
  obtain ⟨d1, d2, d3⟩ := hd
  unfold ThetaConstantWeber.JacobiProduct at hj
  have hη : ModularForm.eta (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero τ.2
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hprod : ThetaConstantWeber.thetaConst 0 0 τ * ThetaConstantWeber.thetaConst 0 1 τ * ThetaConstantWeber.thetaConst 1 0 τ ≠ 0 := by
    rw [hj]
    exact mul_ne_zero two_ne_zero (pow_ne_zero _ hη)
  have t0 : ThetaConstantWeber.thetaConst 0 0 τ ≠ 0 := fun h => hprod (by simp [h])
  have t1 : ThetaConstantWeber.thetaConst 0 1 τ ≠ 0 := fun h => hprod (by simp [h])
  have t2 : ThetaConstantWeber.thetaConst 1 0 τ ≠ 0 := fun h => hprod (by simp [h])
  obtain ⟨n1, n2, n3⟩ := ThetaConstantWeber.halfPeriods_notMem τ
  have mem : ∀ p q : ℤ, ((p : ℂ) * (τ : ℂ) + q) ∈ (GlobalTheory.periodPairOfTau τ).lattice := fun p q => by
    rw [GlobalTheory.mem_lattice_periodPairOfTau]
    exact ⟨p, q, by ring⟩
  have r1 := half_root (GlobalTheory.periodPairOfTau τ) (t := 1 / 2) (by simpa using mem 0 1) n1
  have r2 := half_root (GlobalTheory.periodPairOfTau τ) (t := (τ : ℂ) / 2) (by
    have := mem 1 0
    convert this using 1
    push_cast
    ring) n2
  have r3 := half_root (GlobalTheory.periodPairOfTau τ) (t := (1 + (τ : ℂ)) / 2) (by
    have := mem 1 1
    convert this using 1
    push_cast
    ring) n3
  refine cubic_alg (e1 := ThetaConstantWeber.wp τ (1 / 2)) (e2 := ThetaConstantWeber.wp τ ((τ : ℂ) / 2))
    (e3 := ThetaConstantWeber.wp τ ((1 + (τ : ℂ)) / 2)) (h := (GlobalTheory.periodPairOfTau τ).g₃) ?_ ?_ ?_ r1 r2 r3
  · rw [← sub_ne_zero, d1]
    exact mul_ne_zero (pow_ne_zero _ hp) (pow_ne_zero _ t0)
  · rw [← sub_ne_zero, d2]
    exact mul_ne_zero (pow_ne_zero _ hp) (pow_ne_zero _ t1)
  · intro h
    have h' : ThetaConstantWeber.wp τ ((1 + (τ : ℂ)) / 2) - ThetaConstantWeber.wp τ ((τ : ℂ) / 2) = 0 := by rw [h]; ring
    rw [d3] at h'
    exact mul_ne_zero (pow_ne_zero _ hp) (pow_ne_zero _ t2) h'

theorem scaling : ∀ (Λ : AddSubgroup ℂ) (ω₁ : ℂ) (τ : UpperHalfPlane), ω₁ ≠ 0 →
    JacobiThetaHalfCharacteristic.IsPeriodLattice Λ ω₁ (τ : ℂ) →
    g2 Λ = (GlobalTheory.periodPairOfTau τ).g₂ / ω₁ ^ 4 ∧ g3 Λ = (GlobalTheory.periodPairOfTau τ).g₃ / ω₁ ^ 6 ∧
    ∀ z : ℂ, z ∉ Λ → Formalism.MainNotions.StandardLatticesGL3.wpF Λ z = ThetaConstantWeber.wp τ (z / ω₁) / ω₁ ^ 2 := by
  intro Λ ω₁ τ hω hP
  have H := GlobalTheory.isHomothetic_scalePeriods (GlobalTheory.periodPairOfTau τ) ω₁ hω
  have hmem : ∀ z, z ∈ Λ ↔ z ∈ (GlobalTheory.scalePeriods (GlobalTheory.periodPairOfTau τ) ω₁ hω).lattice := by
    intro z
    have hz : ω₁ * (z / ω₁) = z := by field_simp
    rw [hP z, ← hz, H (z / ω₁), hz, GlobalTheory.mem_lattice_periodPairOfTau]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨n, m, by field_simp; ring⟩
    · rintro ⟨m, n, h⟩
      refine ⟨n, m, ?_⟩
      rw [← hz, ← h]
      ring
  obtain ⟨e2, e3, -, -, hw, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary _ Λ hmem
  refine ⟨by rw [e2, H.g₂_eq]; field_simp, by rw [e3, H.g₃_eq]; field_simp, fun z hz => ?_⟩
  have hz' : ω₁ * (z / ω₁) = z := by field_simp
  rw [(hw z hz).1]
  have h := H.weierstrassP_mul (z / ω₁)
  rw [hz'] at h
  rw [h]
  unfold ThetaConstantWeber.wp
  field_simp

lemma thetaChar_zero (a b : Fin 2) (τ : UpperHalfPlane) :
    JacobiThetaHalfCharacteristic.thetaChar a b 0 (τ : ℂ) = ThetaConstantWeber.thetaConst (a : ℕ) (b : ℕ) τ := by
  simp only [JacobiThetaHalfCharacteristic.thetaChar, ThetaConstantWeber.thetaConst, zero_add]
  congr 2
  ring

lemma wp_shift (τ : UpperHalfPlane) (z : ℂ) (p q : ℤ) :
    ThetaConstantWeber.wp τ (z + ((p : ℂ) + (q : ℂ) * (τ : ℂ))) = ThetaConstantWeber.wp τ z := by
  have h : (((p : ℂ) + (q : ℂ) * (τ : ℂ))) ∈ (GlobalTheory.periodPairOfTau τ).lattice := by
    rw [GlobalTheory.mem_lattice_periodPairOfTau]
    exact ⟨q, p, by ring⟩
  exact (GlobalTheory.periodPairOfTau τ).weierstrassP_add_coe z ⟨_, h⟩

lemma alg {A B C η W P Y σ : ℂ} (hW : W ≠ 0) (hη : η ≠ 0) (hσ : σ = 1 ∨ σ = -1)
    (hABC : A * B * C = 2 * η ^ 3) (hD : (2 * P / W) ^ 12 * η ^ 24 = 1)
    (hY : Y = σ * (P ^ 4 * A ^ 4 * B ^ 4) / W ^ 4) :
    Y ≠ 0 ∧ 1 / Y ^ 3 = σ * (C / η) ^ 12 := by
  have hσ4 : σ ^ 4 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hk : Y ^ 3 * (σ * (C / η) ^ 12) = 1 := by
    have h1 : Y ^ 3 * (σ * (C / η) ^ 12) = σ ^ 4 * (A * B * C) ^ 12 * P ^ 12 / (W ^ 12 * η ^ 12) := by
      rw [hY]
      field_simp
    have h2 : σ ^ 4 * (A * B * C) ^ 12 * P ^ 12 / (W ^ 12 * η ^ 12) = (2 * P / W) ^ 12 * η ^ 24 := by
      rw [hσ4, hABC]
      field_simp
    rw [h1, h2, hD]
  have hY0 : Y ≠ 0 := by
    rintro rfl
    simp at hk
  refine ⟨hY0, ?_⟩
  rw [div_eq_iff (pow_ne_zero _ hY0)]
  linear_combination -hk

lemma half_coords {Λ : AddSubgroup ℂ} {ω₁ : ℂ} {τ : UpperHalfPlane} {t : ℂ} (hω : ω₁ ≠ 0)
    (hΛ : JacobiThetaHalfCharacteristic.IsPeriodLattice Λ ω₁ (τ : ℂ)) (h2 : 2 * t ∈ Λ) :
    ∃ m n : ℤ, t / ω₁ = ((m : ℂ) + (n : ℂ) * (τ : ℂ)) / 2 := by
  obtain ⟨m, n, h⟩ := (hΛ _).1 h2
  refine ⟨m, n, ?_⟩
  field_simp
  linear_combination h

lemma discr_eta (hL : PeriodLatticeAgreement.LatticePeriodEta) {Λ : AddSubgroup ℂ} {ω₁ : ℂ} {τ : UpperHalfPlane}
    (hω : ω₁ ≠ 0) (hΛ : JacobiThetaHalfCharacteristic.IsPeriodLattice Λ ω₁ (τ : ℂ)) (hd : discr Λ = 1) :
    (2 * (Real.pi : ℂ) / ω₁) ^ 12 * ModularForm.eta (τ : ℂ) ^ 24 = 1 := by
  have e : Λ = PeriodLatticeAgreement.latt ω₁ (τ : ℂ) := by
    ext w
    rw [hΛ w, PeriodLatticeAgreement.mem_latt]
  rw [← hL.1 ω₁ τ hω, ← e, hd]

theorem modulus (hL : PeriodLatticeAgreement.LatticePeriodEta) (hT : ThetaConstantWeber.ThetaWeberStatement)
    (Λ : AddSubgroup ℂ) (ω₁ : ℂ) (τ : UpperHalfPlane) (t : ℂ) (hω : ω₁ ≠ 0)
    (hΛ : JacobiThetaHalfCharacteristic.IsPeriodLattice Λ ω₁ (τ : ℂ)) (hd : discr Λ = 1) (h2 : 2 * t ∈ Λ) (ht : t ∉ Λ)
    (a b : Fin 2) (hab : JacobiThetaHalfCharacteristic.IsEvenChar a b) (hz : JacobiThetaHalfCharacteristic.thetaChar a b (t / ω₁) (τ : ℂ) = 0) :
    (12 * Formalism.MainNotions.StandardLatticesGL3.wpF Λ t ^ 2 - g2 Λ) / 4 ≠ 0 ∧ ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
      1 / ((12 * Formalism.MainNotions.StandardLatticesGL3.wpF Λ t ^ 2 - g2 Λ) / 4) ^ 3 =
        s * (JacobiThetaHalfCharacteristic.thetaChar a b 0 (τ : ℂ) / ModularForm.eta (τ : ℂ)) ^ 12 := by
  obtain ⟨hdiff, hjac, -, -⟩ := hT τ
  obtain ⟨c1, c2, c3⟩ := cubic τ hdiff hjac
  obtain ⟨d1, d2, d3⟩ := hdiff
  obtain ⟨hg2, -, hwp⟩ := scaling Λ ω₁ τ hω hΛ
  obtain ⟨m, n, hmn⟩ := half_coords hω hΛ h2
  have hη : ModularForm.eta (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero τ.2
  have hD := discr_eta hL hω hΛ hd
  have hpar := (GlobalTheory.T.thetaChar_half_period_eq_zero_iff_odd_add_odd_add τ hjac m n a b hab).1 (by rw [← hmn]; exact hz)
  rw [hg2, hwp t ht, hmn, thetaChar_zero]
  unfold ThetaConstantWeber.JacobiProduct at hjac
  have hY : ∀ e g : ℂ, (12 * (e / ω₁ ^ 2) ^ 2 - g / ω₁ ^ 4) / 4 = (12 * e ^ 2 - g) / 4 / ω₁ ^ 4 := by
    intro e g
    field_simp
  rw [hY]
  have key : ∀ (A B C Y σ : ℂ), (σ = 1 ∨ σ = -1) → A * B * C = 2 * ModularForm.eta (τ : ℂ) ^ 3 →
      Y = σ * ((Real.pi : ℂ) ^ 4 * A ^ 4 * B ^ 4) →
      Y / ω₁ ^ 4 ≠ 0 ∧ ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
        1 / (Y / ω₁ ^ 4) ^ 3 = s * (C / ModularForm.eta (τ : ℂ)) ^ 12 := fun A B C Y σ hσ hABC hY' => by
    have h := alg hω hη hσ hABC hD (Y := Y / ω₁ ^ 4) (by rw [hY'])
    exact ⟨h.1, σ, hσ, h.2⟩
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hpar
  have hcases : (a = 0 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
    unfold JacobiThetaHalfCharacteristic.IsEvenChar at hab
    fin_cases a <;> fin_cases b <;> simp_all
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  ·
    have hm : m = 2 * p + 1 := by simpa using hp
    have hn : n = 2 * q + 1 := by simpa using hq
    have e : ((m : ℂ) + (n : ℂ) * (τ : ℂ)) / 2 = (1 + (τ : ℂ)) / 2 + ((p : ℂ) + (q : ℂ) * (τ : ℂ)) := by
      rw [hm, hn]; push_cast; ring
    rw [e, wp_shift]
    refine key (ThetaConstantWeber.thetaConst 0 1 τ) (ThetaConstantWeber.thetaConst 1 0 τ) (ThetaConstantWeber.thetaConst 0 0 τ) _ (-1)
      (Or.inr rfl) (by linear_combination hjac) ?_
    rw [c3]
    linear_combination (-(ThetaConstantWeber.wp τ ((1 + (τ : ℂ)) / 2) - ThetaConstantWeber.wp τ ((τ : ℂ) / 2))) * d2 +
      (-(Real.pi : ℂ) ^ 2 * ThetaConstantWeber.thetaConst 0 1 τ ^ 4) * d3
  ·
    have hm : m = 2 * p := by simp at hp; omega
    have hn : n = 2 * q + 1 := by simpa using hq
    have e : ((m : ℂ) + (n : ℂ) * (τ : ℂ)) / 2 = (τ : ℂ) / 2 + ((p : ℂ) + (q : ℂ) * (τ : ℂ)) := by
      rw [hm, hn]; push_cast; ring
    rw [e, wp_shift]
    refine key (ThetaConstantWeber.thetaConst 0 0 τ) (ThetaConstantWeber.thetaConst 1 0 τ) (ThetaConstantWeber.thetaConst 0 1 τ) _ 1
      (Or.inl rfl) (by linear_combination hjac) ?_
    rw [c2]
    linear_combination (-(ThetaConstantWeber.wp τ ((τ : ℂ) / 2) - ThetaConstantWeber.wp τ ((1 + (τ : ℂ)) / 2))) * d1 +
      ((Real.pi : ℂ) ^ 2 * ThetaConstantWeber.thetaConst 0 0 τ ^ 4) * d3
  ·
    have hm : m = 2 * p + 1 := by simpa using hp
    have hn : n = 2 * q := by simp at hq; omega
    have e : ((m : ℂ) + (n : ℂ) * (τ : ℂ)) / 2 = 1 / 2 + ((p : ℂ) + (q : ℂ) * (τ : ℂ)) := by
      rw [hm, hn]; push_cast; ring
    rw [e, wp_shift]
    refine key (ThetaConstantWeber.thetaConst 0 0 τ) (ThetaConstantWeber.thetaConst 0 1 τ) (ThetaConstantWeber.thetaConst 1 0 τ) _ 1
      (Or.inl rfl) (by linear_combination hjac) ?_
    rw [c1]
    linear_combination (ThetaConstantWeber.wp τ (1 / 2) - ThetaConstantWeber.wp τ ((1 + (τ : ℂ)) / 2)) * d1 +
      ((Real.pi : ℂ) ^ 2 * ThetaConstantWeber.thetaConst 0 0 τ ^ 4) * d2

theorem integral (hT : ThetaConstantWeber.ThetaWeberStatement) (Λ : AddSubgroup ℂ) (ω₁ : ℂ) (τ : UpperHalfPlane)
    (hω : ω₁ ≠ 0) (hΛ : JacobiThetaHalfCharacteristic.IsPeriodLattice Λ ω₁ (τ : ℂ)) (hd : discr Λ = 1)
    (hj : IsIntegral ℤ (1728 * g2 Λ ^ 3)) (a b : Fin 2) (hab : JacobiThetaHalfCharacteristic.IsEvenChar a b) (s : ℂ)
    (hs : s = 1 ∨ s = -1) :
    IsIntegral ℤ (s * (JacobiThetaHalfCharacteristic.thetaChar a b 0 (τ : ℂ) / ModularForm.eta (τ : ℂ)) ^ 12) := by
  obtain ⟨-, -, hW, hC⟩ := hT τ
  obtain ⟨hg2, hg3, -⟩ := scaling Λ ω₁ τ hω hΛ
  have hjj : ThetaConstantWeber.jLat τ = 1728 * g2 Λ ^ 3 := by
    have hdd : (GlobalTheory.periodPairOfTau τ).g₂ ^ 3 - 27 * (GlobalTheory.periodPairOfTau τ).g₃ ^ 2 = ω₁ ^ 12 := by
      have h := hd
      rw [Formalism.MainNotions.TaylorLogMetric.discr, hg2, hg3] at h
      field_simp at h
      linear_combination h
    rw [ThetaConstantWeber.jLat_eq, hdd, hg2]
    field_simp
  obtain ⟨p0, p1, p2⟩ := hW.pow_twelve
  have root : ∀ x : ℂ, (x = ThetaConstantWeber.weberF τ ^ 24 ∨ x = -ThetaConstantWeber.weberF₁ τ ^ 24 ∨ x = -ThetaConstantWeber.weberF₂ τ ^ 24) →
      IsIntegral ℤ x := by
    intro x hx
    have h := congrArg (Polynomial.eval x) hC
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at h
    have h0 : (x - 16) ^ 3 - ThetaConstantWeber.jLat τ * x = 0 := by
      rw [h]
      rcases hx with rfl | rfl | rfl <;> simp
    refine (Formalism.HermitianLattices.IntegralLatticeDensity.weber_function_root x (ThetaConstantWeber.jLat τ) 16 (Or.inl rfl) (hjj ▸ hj) ?_).1
    push_cast
    linear_combination h0
  have hx : IsIntegral ℤ ((JacobiThetaHalfCharacteristic.thetaChar a b 0 (τ : ℂ) / ModularForm.eta (τ : ℂ)) ^ 12) := by
    rw [thetaChar_zero]
    have hcases : (a = 0 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
      unfold JacobiThetaHalfCharacteristic.IsEvenChar at hab
      fin_cases a <;> fin_cases b <;> simp_all
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact p0 ▸ root _ (Or.inl rfl)
    · have := (root _ (Or.inr (Or.inl rfl))).neg
      rw [neg_neg] at this
      exact p1 ▸ this
    · have := (root _ (Or.inr (Or.inr rfl))).neg
      rw [neg_neg] at this
      exact p2 ▸ this
  rcases hs with rfl | rfl
  · simpa using hx
  · simpa using hx.neg

theorem exists_char {Λ : AddSubgroup ℂ} {ω₁ : ℂ} {τ : UpperHalfPlane} {t : ℂ} (hω : ω₁ ≠ 0)
    (hΛ : JacobiThetaHalfCharacteristic.IsPeriodLattice Λ ω₁ (τ : ℂ)) (hj : ThetaConstantWeber.JacobiProduct τ) (h2 : 2 * t ∈ Λ)
    (ht : t ∉ Λ) : ∃ a b : Fin 2, JacobiThetaHalfCharacteristic.IsEvenChar a b ∧ JacobiThetaHalfCharacteristic.thetaChar a b (t / ω₁) (τ : ℂ) = 0 := by
  obtain ⟨m, n, hmn⟩ := half_coords hω hΛ h2
  rw [show t / ω₁ = _ from hmn]
  rcases Int.even_or_odd m with hm | hm <;> rcases Int.even_or_odd n with hn | hn
  · exfalso
    obtain ⟨p, rfl⟩ := hm
    obtain ⟨q, rfl⟩ := hn
    refine ht ((hΛ t).2 ⟨p, q, ?_⟩)
    have : t = ω₁ * (t / ω₁) := by field_simp
    rw [this, hmn]
    push_cast
    ring
  · exact ⟨0, 1, by simp [JacobiThetaHalfCharacteristic.IsEvenChar], (GlobalTheory.T.thetaChar_half_period_eq_zero_iff_odd_add_odd_add τ hj m n 0 1 (by simp [JacobiThetaHalfCharacteristic.IsEvenChar])).2
      ⟨by simpa using hm.add_one, by simpa using hn⟩⟩
  · exact ⟨1, 0, by simp [JacobiThetaHalfCharacteristic.IsEvenChar], (GlobalTheory.T.thetaChar_half_period_eq_zero_iff_odd_add_odd_add τ hj m n 1 0 (by simp [JacobiThetaHalfCharacteristic.IsEvenChar])).2
      ⟨by simpa using hm, by simpa using hn.add_one⟩⟩
  · exact ⟨0, 0, by simp [JacobiThetaHalfCharacteristic.IsEvenChar], (GlobalTheory.T.thetaChar_half_period_eq_zero_iff_odd_add_odd_add τ hj m n 0 0 (by simp [JacobiThetaHalfCharacteristic.IsEvenChar])).2
      ⟨by simpa using hm, by simpa using hn⟩⟩

theorem exists_integral_theta_ratio : EquidistributedConjugates.ConjugatesEquidistributed → PeriodLatticeAgreement.LatticePeriodEta → ThetaConstantWeber.ThetaWeberStatement →
    ∀ (D : D7), Formalism.MainNotions.GL3Theta.admJ D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
      [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t →
      ∃ X : M, X ≠ 0 ∧ IsIntegral ℤ (X : ℂ) ∧ ∀ (ρ : M →ₐ[ℚ] ℂ) (ω₁ τ : ℂ), ω₁ ≠ 0 → 0 < τ.im →
        JacobiThetaHalfCharacteristic.IsPeriodLattice (lamConj M ρ (lamOf D cc δ)) ω₁ τ → ∀ a b : Fin 2, JacobiThetaHalfCharacteristic.IsEvenChar a b →
        JacobiThetaHalfCharacteristic.thetaChar a b (t ρ / ω₁) τ = 0 →
        ‖ρ X‖ = (‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ / ‖ModularForm.eta τ‖) ^ 12 := by
  intro _ hL hT D hJ cc δ M _ t hS
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
  obtain ⟨a, b, hab, hz⟩ := exists_char hω hP (hT τ).2.1 h20 n0
  obtain ⟨hne, s, hs, hX⟩ := modulus hL hT _ ω τ _ hω hP d0 h20 n0 a b hab hz
  rw [← hY0] at hne hX
  have hYne : ((12 * e ^ 2 - g) / 4 : M) ≠ 0 := fun h => hne (by rw [h]; simp)
  refine ⟨1 / ((12 * e ^ 2 - g) / 4) ^ 3, one_div_ne_zero (pow_ne_zero _ hYne), ?_, ?_⟩
  · have e1 : ((1 / ((12 * e ^ 2 - g) / 4) ^ 3 : M) : ℂ) = 1 / (((12 * e ^ 2 - g) / 4 : M) : ℂ) ^ 3 := by
      push_cast
      rfl
    rw [e1, hX]
    exact integral hT _ ω τ hω hP d0 (hJ cc δ hS.1 hS.2.1) a b hab s hs
  · intro ρ ω₁ τ' hω₁ hτ' hP' a' b' hab' hz'
    obtain ⟨dρ, -, nρ, -⟩ := hρ ρ
    obtain ⟨-, s', hs', hX'⟩ := modulus hL hT _ ω₁ ⟨τ', hτ'⟩ (t ρ) hω₁ hP' dρ (hS.2.2.2 ρ).1 nρ a' b' hab' hz'
    rw [map_div₀, map_one, map_pow, hYρ, hX']
    have hs1 : ‖s'‖ = 1 := by rcases hs' with rfl | rfl <;> simp
    rw [norm_mul, hs1, one_mul, norm_pow, norm_div]

end GlobalTheory.IntegralX
end
end
