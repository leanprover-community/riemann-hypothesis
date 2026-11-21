import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRingEmbeddingProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusLiftLubinTate
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaOfTiltCompatibleSequence
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusCompatibleThetaZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompatiblePowerSeriesValueStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateTorsionSequence
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EvaluationPowerSeriesShift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTatePeriodThetaKernel

section
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK

namespace GlobalTheory.PMC.PeriodVector

theorem exists_casimir (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Algebra.IsSeparable F K] :
    ∃ (n : ℕ) (b d : Fin n → K), (∑ j, Algebra.trace F K (d j) • b j = 1) ∧
      ∀ (M : Type) [AddCommGroup M] [Module F M] (β : K →ₗ[F] K →ₗ[F] M) (c : K),
        ∑ j, β (c * b j) (d j) = ∑ j, β (b j) (c * d j) := by
  classical
  let b := Module.finBasis F K
  let B := Algebra.traceForm F K
  let d := B.dualBasis (traceForm_nondegenerate F K) b
  have h1 : ∀ x, ∑ k, Algebra.trace F K (x * b k) • d k = x := fun x => by
    conv_rhs => rw [← d.sum_repr x]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply]
    rfl
  have h2 : ∀ x, ∑ k, Algebra.trace F K (d k * x) • b k = x := fun x => by
    conv_rhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    have : B (d k) = b.coord k := b.ext fun j => by
      rw [LinearMap.BilinForm.apply_dualBasis_left]
      simp [Finsupp.single_apply]
    exact LinearMap.congr_fun this x
  refine ⟨_, b, d, by simpa using h2 1, fun M _ _ β c => ?_⟩
  calc ∑ j, β (c * b j) (d j) = ∑ j, ∑ k, Algebra.trace F K (d k * (c * b j)) • β (b k) (d j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        conv_lhs => rw [← h2 (c * b j)]
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    _ = ∑ k, ∑ j, Algebra.trace F K (c * d k * b j) • β (b k) (d j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
        rw [show d k * (c * b j) = c * d k * b j by ring]
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        conv_rhs => rw [← h1 (c * d k)]
        simp only [map_sum, map_smul]

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]

theorem exists_vector [Algebra.IsSeparable Qp K] (χ : G →* Kˣ) (τ : K →ₐ[Qp] LL)
    (ρ : Representation LL G (Fin 1 → LL)) (hρ : ∀ g v, ρ g v = (τ (χ g : K))⁻¹ • v) (Y : BdR)
    (hY : ∀ g, PD.actdR g Y = algebraMap K BdR (χ g : K) * Y) (h1 : Y ∈ PD.Fil 1) (h2 : Y ∉ PD.Fil 2) :
    ∃ x ∈ DdRE PD ρ τ, x ∈ FilV PD (LL := LL) (V := Fin 1 → LL) 1 ∧
      x ∉ FilV PD (LL := LL) (V := Fin 1 → LL) 2 := by
  have := PD.finK
  obtain ⟨n, b, d, hbd, hcas⟩ := exists_casimir Qp K
  let e : Fin 1 → LL := fun _ => 1
  let β : K →ₗ[Qp] K →ₗ[Qp] ((Fin 1 → LL) ⊗[Qp] BdR) :=
    (TensorProduct.mk Qp (Fin 1 → LL) BdR).compl₁₂
      (((LinearMap.toSpanSingleton LL _ e).restrictScalars Qp) ∘ₗ τ.toLinearMap)
      ((LinearMap.toSpanSingleton K _ Y).restrictScalars Qp)
  have hβ : ∀ u v, β u v = (τ u • e) ⊗ₜ[Qp] (v • Y) := fun _ _ => rfl
  have hmul : ∀ c : K, mulVdR (K := K) (BdR := BdR) (V := Fin 1 → LL) (LL := LL) c (∑ j, β (b j) (d j)) =
      τ c • ∑ j, β (b j) (d j) := fun c => by
    have hl : ∀ j, mulVdR (K := K) (BdR := BdR) (V := Fin 1 → LL) (LL := LL) c (β (b j) (d j)) =
        β (b j) (c * d j) := fun j => by
      rw [hβ, hβ, mulVdR, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply,
        ← Algebra.smul_def, smul_smul]
    rw [map_sum, Finset.smul_sum]
    simp only [hl]
    rw [← hcas]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hβ, hβ, map_mul, mul_smul, TensorProduct.smul_tmul']
  refine ⟨∑ j, β (b j) (d j), ⟨?_, ?_⟩, ?_, ?_⟩
  · refine (Submodule.mem_iInf _).2 fun g => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    have hne : τ (χ g : K) ≠ 0 := (map_ne_zero τ).2 (χ g).ne_zero
    have : actVdR PD ρ g (∑ j, β (b j) (d j)) = (τ (χ g : K))⁻¹ •
        mulVdR (K := K) (BdR := BdR) (V := Fin 1 → LL) (LL := LL) (χ g : K) (∑ j, β (b j) (d j)) := by
      rw [map_sum, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hβ, actVdR, mulVdR, AlgebraTensorModule.map_tmul, AlgebraTensorModule.map_tmul, hρ,
        ← TensorProduct.smul_tmul', LinearMap.id_apply, LinearMap.mulLeft_apply]
      congr 2
      change PD.actdR g (d j • Y) = _
      rw [map_smul, hY, mul_smul_comm]
    rw [this, hmul, smul_smul, inv_mul_cancel₀ hne, one_smul]
  · refine (Submodule.mem_iInf _).2 fun c => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hmul, sub_self]
  · refine Submodule.sum_mem _ fun j _ => ?_
    exact ⟨(τ (b j) • e) ⊗ₜ[Qp] ⟨d j • Y, (PD.Fil 1).smul_mem _ h1⟩, rfl⟩
  · rintro ⟨z, hz⟩
    obtain ⟨lam, hlam⟩ : ∃ lam : LL →ₗ[Qp] Qp, lam 1 ≠ 0 := by
      by_contra h
      push Not at h
      exact one_ne_zero ((Module.forall_dual_apply_eq_zero_iff Qp (1 : LL)).1 h)
    let Λ : ((Fin 1 → LL) ⊗[Qp] BdR) →ₗ[Qp] BdR :=
      TensorProduct.lift ((LinearMap.lsmul Qp BdR) ∘ₗ lam ∘ₗ LinearMap.proj 0)
    have hΛ : ∀ v y, Λ (v ⊗ₜ[Qp] y) = lam (v 0) • y := fun _ _ => rfl
    have hmem : ∀ z, Λ (AlgebraTensorModule.map (LinearMap.id : (Fin 1 → LL) →ₗ[LL] (Fin 1 → LL))
        ((PD.Fil 2).restrictScalars Qp).subtype z) ∈ PD.Fil 2 := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul v y =>
        rw [AlgebraTensorModule.map_tmul, hΛ]
        exact ((PD.Fil 2).restrictScalars Qp).smul_mem _ y.2
      | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
    have hx := hmem z
    rw [hz] at hx
    have hκ : Λ (∑ j, β (b j) (d j)) = (∑ j, lam (τ (b j)) • d j) • Y := by
      rw [map_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hβ, hΛ, smul_assoc]
      simp [e]
    have hκ0 : (∑ j, lam (τ (b j)) • d j) ≠ 0 := fun h => hlam (by
      have h' := congrArg (Algebra.trace Qp K) h
      have h'' := congrArg (fun u => lam (τ u)) hbd
      simp only [map_sum, map_smul, map_zero, map_one, smul_eq_mul] at h' h''
      rw [← h'', ← h']
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _)
    rw [hκ] at hx
    exact h2 (((PD.Fil 2).smul_mem_iff hκ0).1 hx)

end General

theorem exists_degree_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ)
    (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (Y : P.R.BdR),
    (∀ g : ↥(GK K), (P.PD K).actdR g Y = algebraMap ↥K.1 P.R.BdR (χ g : ↥K.1) * Y) →
    Y ∈ (P.PD K).Fil 1 → Y ∉ (P.PD K).Fil 2 →
    ∃ x ∈ DdRE (P.PD K) (lineRep (K := K) (LL := LL) (ltChar τ₀ χ⁻¹)) τ₀,
      x ∈ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) 1 ∧
      x ∉ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) 2 := by
  intro l _ P K LL χ τ₀ Y hY h1 h2
  have := (P.PD K).finK
  refine exists_vector (P.PD K) χ τ₀ _ (fun g v => ?_) Y hY h1 h2
  simp [lineRep, ltChar]

end GlobalTheory.PMC.PeriodVector

end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_period_filtration_exact : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ)
    (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (Y : P.R.BdR),
    (∀ g : ↥(GK K), (P.PD K).actdR g Y = algebraMap ↥K.1 P.R.BdR (χ g : ↥K.1) * Y) →
    Y ∈ (P.PD K).Fil 1 → Y ∉ (P.PD K).Fil 2 →
    ∃ x ∈ DdRE (P.PD K) (lineRep (K := K) (LL := LL) (ltChar τ₀ χ⁻¹)) τ₀,
      x ∈ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) 1 ∧
      x ∉ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) 2 := by
  atlas_forward_decl GlobalTheory.PMC.PeriodVector.exists_degree_one
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_ring_embedding_properties : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ K : FinExt l, ∃ Ψ : BK K →+* P.R.BdR,
      (∀ c : ↥K.1, Ψ (inK K c) = algebraMap ↥K.1 P.R.BdR c) ∧
      (∀ (g : ↥(GK K)) (b : BK K), (P.PD K).actdR g (Ψ b) = Ψ (galB g b)) ∧
      (∀ b, Ψ b ∈ (P.PD K).Fil 0) ∧
      (∀ x : AK K, thetaK K x = 0 → Ψ (toB K (ofA K x)) ∈ (P.PD K).Fil 1) ∧
      (∀ x : AK K, thetaK K x = 0 → x ∉ RingHom.ker (thetaK K) ^ 2 → Ψ (toB K (ofA K x)) ∉ (P.PD K).Fil 2) := by
  first | exact @GlobalTheory.CrisToDR.exists_map | exact GlobalTheory.CrisToDR.exists_map | (intros; apply GlobalTheory.CrisToDR.exists_map <;> assumption)
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK
open GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.LTPeriodShape

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l),
    LTData K χ π z → ∃ (ω : AK K) (t u : BK K), thetaK K ω = 0 ∧ ω ∉ RingHom.ker (thetaK K) ^ 2 ∧
      t = toB K (ofA K ω) * (1 + toB K (ofA K ω) * u) ∧ ∀ g : ↥(GK K), galB g t = inK K (χ g : ↥K.1) * t := by
  intro l _ K χ π z h
  obtain ⟨hπ, hF, v, hv0, hv1, hv, hg⟩ := GlobalTheory.T.lubin_tate_torsion_sequence l K χ π z h
  have hπu := GlobalTheory.LTTilt.not_isUnit_intToOC K hπ
  have hcomp : ∀ n, v (n + 1) ^ (l ^ fK K) - v n ∈ Ideal.span {intToOC K π} := fun n =>
    Ideal.mem_span_singleton.2 ⟨-v (n + 1), by rw [← hv n]; ring⟩
  obtain ⟨x, hx, -⟩ := GlobalTheory.LTTilt.existsUnique_isTiltOf (fK K) (NeZero.pos _) (intToOC K π) hπu
    (GlobalTheory.LTTilt.natCast_mem_span_intToOC K hπ) v hcomp
  obtain ⟨ω₀, hred, hω₀⟩ := GlobalTheory.T.exists_frobenius_lift_lubin_tate l K π hπ x
  choose r hr using (frobq_bijective K).2
  let ω : ℕ → AK K := fun n => r^[n] ω₀
  have hch : ∀ n, frobq K (ω (n + 1)) = ω n := fun n => by
    simp only [ω, Function.iterate_succ_apply', hr]
  have hθ : ∀ n, thetaK K (ω n) = v n := GlobalTheory.T.theta_of_tilt_compatible_sequence l K π hπ v ω hv (hred ▸ hx) hch hω₀
  have h0 : thetaK K ω₀ = 0 := (hθ 0).trans hv0
  have hne : ω₀ ≠ 0 := fun e => hv1 (by
    have : ω 1 = 0 := (frobq_bijective K).1 (by rw [hch, map_zero]; exact e)
    rw [← hθ, this, map_zero])
  have hker : ∀ (M : ℕ) (y : AK K), ω₀ ^ M ∣ y → y ∈ RingHom.ker (thetaK K) ^ M := fun M y ⟨c, hc⟩ =>
    hc ▸ Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (show ω₀ ∈ RingHom.ker (thetaK K) from h0) M)
  have hev := ev_ltLog hπ hF ω₀ h0
  have hq : resCard K = l ^ fK K := rfl
  have hsq : ω₀ ∉ RingHom.ker (thetaK K) ^ 2 :=
    GlobalTheory.LTPeriodKerSq.not_mem_sq hπ hne h0 (by rw [hq]; exact hω₀)
  obtain ⟨L', u₁, hL', hc, hu₁, ht⟩ := GlobalTheory.AcrisK.ev_shift l K _ (onDisc_log hπ hF) ω₀ h0 _ hev
  obtain ⟨L'', u, -, -, -, hu⟩ := GlobalTheory.AcrisK.ev_shift l K L' hL' ω₀ h0 u₁ hu₁
  refine ⟨ω₀, ltLog hπ hF ω₀ h0, u, h0, hsq, ?_, fun g => ?_⟩
  · rw [ht, hu, hc, PowerSeries.coeff_zero_eq_constantCoeff_apply, GlobalTheory.LTLog.constantCoeff_log _ hπ hF,
      GlobalTheory.LTLog.coeff_one_log _ hπ hF, map_zero, map_one, zero_add]
  · obtain ⟨a, ha, hs⟩ := hg g
    obtain ⟨y, hy1, hy2, hy3⟩ := GlobalTheory.T.exists_compatible_power_series_value l K ω (lubinTateHom hπ hF hF a).toPowerSeries
      (fun n => Per.σO (g : GQ l) (v n)) hch
      (fun n => by rw [hθ]; exact GlobalTheory.LTTilt.norm_lt_one_of_compat K hπ hcomp hv0 n)
      (fun n => by rw [hθ]; exact hs n)
    have hy : gal K g ω₀ = y 0 := sub_eq_zero.1 (GlobalTheory.T.frobenius_compatible_theta_zero l K (fun n => gal K g (ω n) - y n)
      (fun n => by rw [map_sub, hy1, ← gal_frobq, hch])
      (fun n => by rw [map_sub, hy2, thetaK_gal, hθ, sub_self]))
    rw [← ha]
    exact ev_log_hom hπ hF a h0 (fun n => hker n _ (hy ▸ hy3 n)) (hev.gal g)

end GlobalTheory.LTPeriodShape

end
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lubin_tate_period_element : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l),
    LTData K χ π z → ∃ (ω : AK K) (t u : BK K), thetaK K ω = 0 ∧ ω ∉ RingHom.ker (thetaK K) ^ 2 ∧
      t = toB K (ofA K ω) * (1 + toB K (ofA K ω) * u) ∧ ∀ g : ↥(GK K), galB g t = inK K (χ g : ↥K.1) * t := by
  first | exact @GlobalTheory.LTPeriodShape.main | exact GlobalTheory.LTPeriodShape.main | (intros; apply GlobalTheory.LTPeriodShape.main <;> assumption)
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK

theorem GlobalTheory.LTDegOne.main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (K LL : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l), LTData K χ π z →
    ∀ τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ x ∈ DdRE (P.PD K) (lineRep (K := K) (LL := LL) (ltChar τ₀ χ⁻¹)) τ₀, x ∈ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) 1 ∧
      x ∉ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) 2 := by
  intro l _ P AI hT K LL χ π z hLT τ₀
  obtain ⟨ω, t, u, hω0, hω2, ht, hg⟩ := GlobalTheory.T.exists_lubin_tate_period_element l K χ π z hLT
  obtain ⟨Ψ, hK, hG, h0, h1, h2⟩ := GlobalTheory.T.period_ring_embedding_properties l P AI hT K
  have hX1 : Ψ (toB K (ofA K ω)) ∈ (P.PD K).Fil 1 := h1 ω hω0
  have hX2 : Ψ (toB K (ofA K ω)) ∉ (P.PD K).Fil 2 := h2 ω hω0 hω2
  have hXU : Ψ (toB K (ofA K ω)) * Ψ u ∈ (P.PD K).Fil 1 := by
    simpa using (P.PD K).Fil_mul 1 0 _ _ hX1 (h0 u)
  have hXXU : Ψ (toB K (ofA K ω)) * (Ψ (toB K (ofA K ω)) * Ψ u) ∈ (P.PD K).Fil 2 := by
    simpa [one_add_one_eq_two] using (P.PD K).Fil_mul 1 1 _ _ hX1 hXU
  have hY : Ψ t = Ψ (toB K (ofA K ω)) + Ψ (toB K (ofA K ω)) * (Ψ (toB K (ofA K ω)) * Ψ u) := by
    rw [ht, map_mul, map_add, map_one, map_mul]; ring
  refine GlobalTheory.T.lubin_tate_period_filtration_exact l P K LL χ τ₀ (Ψ t) (fun g => ?_) ?_ ?_
  · rw [hG, hg, map_mul, hK]
  · rw [hY]
    exact add_mem hX1 ((P.PD K).Fil_anti 1 (by simpa [one_add_one_eq_two] using hXXU))
  · intro h
    apply hX2
    have := sub_mem h hXXU
    rwa [hY, add_sub_cancel_right] at this
end
