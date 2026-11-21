import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.CondAllPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.HermitianBasisBelowSecond
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TraceEqAdd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.NormOneUnitFixedPoints
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.EtaVCases
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OmAtComplZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.IsCompactSpanRange
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.HRSumSmulRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.UnitaryOrbitCounting
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.UnitNormOfRes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TrOntoHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.EtaSpHolds
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OmFibreUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualContinuity.SdExistsHolds

section
noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

theorem oEv_basis2 (hfin : Module.finrank F E = 2) : ∃ β : Fin 2 → Fv F v ⊗[F] E, LinearIndependent (Fv F v) β ∧
    ∀ x, x ∈ OEv (E := E) v ↔ ∃ c : Fin 2 → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • β i := by
  have h := oEv_basis (E := E) v
  rw [hfin] at h
  exact h

theorem sigR_smulF (c : Fv F v) (x : Fv F v ⊗[F] E) : sigR (Fv F v) σ (c • x) = c • sigR (Fv F v) σ x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul a b => simp [sigR, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem hb_li {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (hβ : LinearIndependent (Fv F v) β) :
    LinearIndependent (Fv F v) (hb σ v hinv β (a := a)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc p
  have hent : ∀ i j, ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) :
      Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = 0 := by
    intro i j
    rw [hc]
    rfl
  have hβ2 := Fintype.linearIndependent_iff.1 hβ
  obtain ⟨i, j⟩ := p
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 := hent i j
    rw [sum_lt σ v hinv β c h] at h1
    have h0 := hβ2 ![c (i, j), c (j, i)] (by simpa [Fin.sum_univ_two] using h1)
    simpa using h0 0
  · have h1 := hent i i
    rw [sum_diag σ v hinv β c i, b_sc_eq] at h1
    exact (map_eq_zero_iff _ (algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective).1 h1
  · have h1 := hent j i
    rw [sum_lt σ v hinv β c h] at h1
    have h0 := hβ2 ![c (j, i), c (i, j)] (by simpa [Fin.sum_univ_two] using h1)
    simpa using h0 1

theorem fix_int' (hcm : IsCMExt F E σ) {t : Fv F v ⊗[F] E} (ht : t ∈ OEv (E := E) v)
    (hf : sigR (Fv F v) σ t = t) : ∃ r ∈ v.adicCompletionIntegers F, t = sc (E := E) v r := by
  have hinv := b_sig_sig σ hcm
  have hnt := b_sig_nt σ hcm
  have hfin := hcm.2.2.1
  set r : Fv F v := algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) t with hr
  have hsc : sc (E := E) v r = t := by
    calc sc (E := E) v r
        = algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) (1 / 2)) * (t + t) := by
          rw [b_sc_eq, hr, map_mul, trace_v v σ hinv hnt hfin, hf]
      _ = algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) (1 / 2) * 2) * t := by
          rw [map_mul, map_ofNat, mul_assoc, two_mul]
      _ = t := by rw [half_two, map_one, one_mul]
  refine ⟨r, b_int_of_sc v (hsc ▸ ht), hsc.symm⟩

theorem hb_mem {a : ℕ} (hcm : IsCMExt F E σ) (β : Fin 2 → Fv F v ⊗[F] E)
    (hβ : ∀ x, x ∈ OEv (E := E) v ↔ ∃ c : Fin 2 → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • β i)
    (T : HermR (Fv F v) σ a) :
    T ∈ HO σ v a ↔ ∃ c : Fin a × Fin a → v.adicCompletionIntegers F,
      T = ∑ p, (c p : Fv F v) • hb σ v (b_sig_sig σ hcm) β p := by
  have hinv := b_sig_sig σ hcm
  constructor
  · intro hT
    have hT' : ∀ i j, (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ OEv (E := E) v := hT
    have hH : ∀ i j, sigR (Fv F v) σ ((T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) j i) =
        (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j := fun i j => T.2 i j
    choose d hd using fun i j => (hβ _).1 (hT' i j)
    choose r hr hrT using fun i => fix_int' σ v hcm (hT' i i) (hH i i)
    refine ⟨fun p => if p.1 < p.2 then d p.1 p.2 0 else if p.2 < p.1 then d p.2 p.1 1 else ⟨r p.1, hr p.1⟩, ?_⟩
    apply Subtype.ext
    ext i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [sum_lt σ v hinv β _ h, hd i j, Fin.sum_univ_two]
      simp [h, not_lt.2 h.le]
    · rw [sum_diag σ v hinv β _ i, hrT i]
      simp
    · rw [sum_gt σ v hinv β _ h, ← hH i j, hd j i, Fin.sum_univ_two, map_add, sigR_smulF, sigR_smulF, add_comm]
      simp [h, not_lt.2 h.le]
  · rintro ⟨c, rfl⟩
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [sum_lt σ v hinv β _ h]
      exact (hβ _).2 ⟨![c (i, j), c (j, i)], by simp [Fin.sum_univ_two]⟩
    · rw [sum_diag σ v hinv β _ i]
      exact b_sc_mem v (c (i, i)).2
    · rw [sum_gt σ v hinv β _ h]
      have hm := b_sigR_mem v σ ((hβ ((c (j, i) : Fv F v) • β 0 + (c (i, j) : Fv F v) • β 1)).2
        ⟨![c (j, i), c (i, j)], by simp [Fin.sum_univ_two]⟩)
      rwa [map_add, sigR_smulF, sigR_smulF, add_comm] at hm

theorem idxPiH_std (a : ℕ) (hS : StdHyp σ J ψ) : IdxPiH σ v a := by
  intro _ ϖ hϖ
  have hcm := hS.1
  obtain ⟨β, hli, hβ⟩ := oEv_basis2 v hcm.2.2.1
  rw [genIdx v (HO σ v a) (hb σ v (b_sig_sig σ hcm) β) (hb_li σ v (b_sig_sig σ hcm) β hli)
    (hb_mem σ v hcm β hβ) ϖ hϖ, qv, Fintype.card_prod, Fintype.card_fin]
  push_cast
  ring

end PI.OmLocU.SdB
end
end

section
noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

def CondAllF : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    IsStdChar ψ → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (x : Fv F v),
      (∀ y ∈ v.adicCompletionIntegers F, psiV F ψ v (x * y) = 1) ↔ dV v * x ∈ v.adicCompletionIntegers F

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem condV_of_all (h : CondAllF) : CondV σ J ψ v := by
  intro hs t
  rw [← h F hs.1.1 ψ hs.2.2.1 hs.2.2.2 v t]
  exact forall₂_congr fun s _ => by rw [mul_comm]

theorem sdVolW_of_cond (a : ℕ) (hC : CondAllF) (hP : TrPerf σ J ψ v) : SdVolW σ J ψ v Λ a := by
  intro hS
  exact sdVolW_of_pi σ J ψ v Λ a (condV_of_all σ J ψ v hC) (dualW_of_perf σ J ψ v Λ a hP)
    (idxPiW_std σ J ψ v Λ a hS) hS

theorem sdVolH_of_cond (a : ℕ) (hC : CondAllF) (hP : TrPerf σ J ψ v) :
    SdVolH σ J ψ v a := by
  intro hS
  exact sdVolH_of_pi σ J ψ v a (condV_of_all σ J ψ v hC) (dualH_of_perf σ J ψ v a hP)
    (idxPiH_std σ J ψ v a hS) hS

end PI.OmLocU.SdB
end
end

section
noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU

theorem condAllF_holds : CondAllF := Formalism.L2.SG.Pf.conductor_inverse_different

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))


theorem sdVolW_of_perf (a : ℕ) (hP : TrPerf σ J ψ v) : SdVolW σ J ψ v Λ a :=
  sdVolW_of_cond σ J ψ v Λ a condAllF_holds hP

theorem sdVolH_of_perf (a : ℕ) (hP : TrPerf σ J ψ v) : SdVolH σ J ψ v a :=
  sdVolH_of_cond σ J ψ v a condAllF_holds hP

end PI.OmLocU.SdB
end
end

section
noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

theorem sig_nt (hcm : IsCMExt F E σ) : ∃ x, σ x ≠ x := by
  obtain ⟨-, htc, -, hst⟩ := hcm
  have hne : Nonempty (E →+* ℂ) := by
    rw [← Fintype.card_pos_iff, NumberField.Embeddings.card]
    exact Module.finrank_pos
  obtain ⟨φ⟩ := hne
  have hc := htc.isComplex (NumberField.InfinitePlace.mk φ)
  rw [NumberField.InfinitePlace.isComplex_mk_iff, NumberField.ComplexEmbedding.isReal_iff] at hc
  by_contra h
  push_neg at h
  apply hc
  ext x
  simp only [NumberField.ComplexEmbedding.conjugate_coe_eq]
  have hx := hst φ x
  rw [h x] at hx
  rw [starRingEnd_apply]
  exact hx.symm

private theorem sc_of_isUnif_of_mem_integers {ϖ r : Fv F v} (hϖ : IsUnif v ϖ)
    (hr : r ∈ v.adicCompletionIntegers F) (hn : sc (E := E) v r ∉ PO (E := E) v ϖ) :
    r ≠ 0 ∧ r⁻¹ ∈ v.adicCompletionIntegers F := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hn ⟨0, Orb.oev_zero v, by simp [sc]⟩
  refine ⟨hr0, ?_⟩
  have hv0 : Valued.v r ≠ 0 := (Valuation.ne_zero_iff _).mpr hr0
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hv0)]
  by_contra hlt
  push_neg at hlt
  apply hn
  have hle : Valued.v r ≤ ↑(Multiplicative.ofAdd (-1 : ℤ)) := by
    rw [WithZero.le_ofAdd_iff hv0]
    rw [← WithZero.coe_one, ← ofAdd_zero, WithZero.lt_ofAdd_iff hv0] at hlt
    omega
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    unfold IsUnif at hϖ
    simp at hϖ
  refine ⟨sc v (r * ϖ⁻¹), NormOneUnitFixedPoints.sc_mem v ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]
    unfold IsUnif at hϖ
    rw [hϖ]
    rw [mul_inv_le_iff₀ (zero_lt_iff.mpr (by simp)), one_mul]
    exact hle
  · rw [NormOneUnitFixedPoints.sc_mul_sc, mul_comm r, ← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]

theorem mem_of_theta (hcm : IsCMExt F E σ) {ϖ : Fv F v} (hϖ : IsUnif v ϖ) (θ : Fv F v ⊗[F] E)
    (hθ : θ ∈ OEv (E := E) v) (hnd : (θ - sigR (Fv F v) σ θ) * (θ - sigR (Fv F v) σ θ) ∉ PO (E := E) v ϖ)
    (z : Fv F v ⊗[F] E)
    (hz : ∀ x ∈ OEv (E := E) v, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * z) ∈ v.adicCompletionIntegers F) :
    z ∈ OEv (E := E) v := by
  have hσσ := b_sig_sig σ hcm
  have htr := trace_v v σ hσσ (sig_nt σ hcm) hcm.2.2.1
  have hsθ := UnN.sigR_mem σ v hθ
  have hδ : θ - sigR (Fv F v) σ θ ∈ OEv (E := E) v := by
    rw [sub_eq_add_neg]
    exact Orb.oev_add v hθ (Orb.oev_neg v hsθ)
  have hfix : sigR (Fv F v) σ ((θ - sigR (Fv F v) σ θ) * (θ - sigR (Fv F v) σ θ))
      = (θ - sigR (Fv F v) σ θ) * (θ - sigR (Fv F v) σ θ) := by
    rw [map_mul, map_sub, sigR_sigR v σ hσσ θ]
    ring
  obtain ⟨r, hr, hreq⟩ := NormOneUnitFixedPoints.fix_int_sc σ v hcm (b_mul_mem v hδ hδ) hfix
  obtain ⟨hr0, hrinv⟩ := sc_of_isUnif_of_mem_integers v hϖ hr (hreq ▸ hnd)
  have ha := hz 1 (b_one_mem v)
  rw [one_mul] at ha
  have hb := hz θ hθ
  have key : (θ - sigR (Fv F v) σ θ) * z
      = algebraMap (Fv F v) _ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (θ * z))
        - sigR (Fv F v) σ θ * algebraMap (Fv F v) _ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z) := by
    rw [htr, htr, map_mul]
    ring
  have hy : (θ - sigR (Fv F v) σ θ) * z ∈ OEv (E := E) v := by
    rw [key, sub_eq_add_neg]
    refine Orb.oev_add v ?_ (Orb.oev_neg v (b_mul_mem v hsθ ?_))
    · rw [← b_sc_eq]
      exact b_sc_mem v hb
    · rw [← b_sc_eq]
      exact b_sc_mem v ha
  have hz' : z = sc v r⁻¹ * ((θ - sigR (Fv F v) σ θ) * ((θ - sigR (Fv F v) σ θ) * z)) := by
    rw [← mul_assoc (θ - sigR (Fv F v) σ θ), hreq, ← mul_assoc, NormOneUnitFixedPoints.sc_mul_sc,
      inv_mul_cancel₀ hr0, NormOneUnitFixedPoints.sc_one, one_mul]
  rw [hz']
  exact b_mul_mem v (b_sc_mem v hrinv) (b_mul_mem v hδ hy)

private theorem exists_isUnif' : ∃ ϖ : Fv F v, IsUnif v ϖ := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  refine ⟨(π : Fv F v), ?_⟩
  unfold IsUnif
  rw [HeightOneSpectrum.adicCompletion.valued_coe, hπ]
  rfl

theorem trPerf_of_res (hR : Red.ResAlg σ J ψ v) : TrPerf σ J ψ v := by
  intro hstd hun z hz
  have hcm : IsCMExt F E σ := hstd.1
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif' v
  obtain ⟨θ, hθ, hnd⟩ := NormOneUnitFixedPoints.exists_theta σ J ψ v hR hstd hun hϖ
  exact mem_of_theta σ v hcm hϖ θ hθ hnd z hz

end PI.OmLocU.SdB
end
end

section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem omLocU_of' (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a) (hU : UnifEx v)
    (h1 : OrbAll σ J ψ v Λ a Y) (h2 : FibU' σ J ψ v Λ a Y) (h3 : CountU σ J ψ v Λ a Y)
    (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y := by
  have h2' : FibU σ J ψ v Λ a Y := by
    intro hG hfib ϖ hϖ
    obtain ⟨hW, hH⟩ := hSd hG.1
    exact h2 hG hW hH hfib ϖ hϖ
  exact omLocU_of σ J ψ v Λ a Y hSd hOm hU h1 h2' h3 h4 h5

theorem omLocU_of_fib (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a)
    (h1 : OrbAll σ J ψ v Λ a Y) (hL : LamOC v Λ a) (hH : HermOC σ v a) (hHe : FibHens σ J ψ v Λ a Y)
    (h3 : CountU σ J ψ v Λ a Y) (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y :=
  omLocU_of' σ J ψ v Λ a Y hSd hOm (unifEx_holds v) h1 (fibU'_of σ J ψ v Λ a Y hL hH hHe) h3 h4 h5


theorem omLocU_of_hens (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a) (h1 : OrbAll σ J ψ v Λ a Y) (hHe : FibHens σ J ψ v Λ a Y)
    (h3 : CountU σ J ψ v Λ a Y) (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y :=
  omLocU_of_fib σ J ψ v Λ a Y hSd hOm h1 (lamOC_holds v Λ a) (hermOC_holds v σ a) hHe h3 h4 h5

end PI.OmLocU
end
end

section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))


theorem omLocU_of_onto (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a) (h1 : OrbAll σ J ψ v Λ a Y) (hO : HensOnto σ J v Λ ψ a Y)
    (h3 : CountU σ J ψ v Λ a Y) (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y :=
  omLocU_of_hens σ J ψ v Λ a Y hSd hOm h1 (fibHens_of σ J v Λ ψ a Y hO) h3 h4 h5

theorem omLocU_of_tr (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : (StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν))
    (hOm : OmUnique σ J ψ v a) (h1 : OrbAll σ J ψ v Λ a Y) (hGI : GramInvO σ J v Λ ψ a Y) (hTr : TrOnto σ v)
    (h3 : CountU σ J ψ v Λ a Y) (h4 : SdVolW σ J ψ v Λ a) (h5 : SdVolH σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y :=
  omLocU_of_onto σ J ψ v Λ a Y hSd hOm h1 (hensOnto_of σ J v Λ ψ a Y hGI hTr) h3 h4 h5

end PI.OmLocU
end
end

section
noncomputable section

namespace PI.OmLocU.Done

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU

theorem local_omega_volume_unique {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E)) (a : ℕ) (Y : TupV (E := E) v n a)
    (hSd : StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧
      ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν)
    (hOm : OmUnique σ J ψ v a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y := by
  have hR : Red.ResAlg σ J ψ v := Red.resAlg_of_sp σ J ψ v (Red.etaSp_holds σ J ψ v)
  have hUN := UnN.unitNorm_of_res σ J ψ v Λ hR
  have hP : SdB.TrPerf σ J ψ v := SdB.trPerf_of_res σ J ψ v hR
  intro hS
  exact omLocU_of_tr σ J ψ v Λ a Y hSd hOm (UnitaryOrbitCounting.orbAll_of_res σ J ψ v Λ a Y hR hUN)
    (gramInvO_holds σ J v Λ ψ a Y) (Red.trOnto_holds σ J ψ v hS) (UnitaryOrbitCounting.countU_of_res' σ J ψ v Λ a Y hR hUN)
    (SdB.sdVolW_of_perf σ J ψ v Λ a hP) (SdB.sdVolH_of_perf σ J ψ v a hP) hS

theorem omLocU_closed {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E)) (a : ℕ) (Y : TupV (E := E) v n a) :
    Formalism.L2.SG.Pf.NcLoc.OmLocU σ J ψ v Λ a Y :=
  local_omega_volume_unique σ J ψ v Λ a Y
    (fun hS => ⟨(PI.SelfDualBridge.W.sdExists_holds σ J ψ v a (Fin 1) hS).1,
      (PI.SelfDualBridge.W.sdExists_holds σ J ψ v a (Fin 1) hS).2.1⟩)
    (omUnique σ J ψ v a)

end PI.OmLocU.Done
end
end
