import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLiftGraphMetric
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerBlockMetric

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def LiftGraphFactor.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a r : ℕ) (v : Fin r → Ω),
    (∀ j, v j ∈ chartLat y (a • N.a) 1) → KH.GeneratesOn y (a • N.a) v →
    ∃ Φ : ((Σ k, ι k) → ℂ) → ℝ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {w | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} ∧
      (∀ w : (Σ k, ι k) → ℂ, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → 0 < Φ w) ∧
      (∀ (c : K → ℂ) (w : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) →
        Φ (fun p => c p.1 * w p) = (∏ k, ‖c k‖ ^ ((a • N.a) k)) ^ 2 * Φ w) ∧
      (∀ w : (Σ k, ι k) → ℂ, Φ (fun p => (starRingEnd ℂ) (w p)) = Φ w) ∧
      (∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin r,
        secNormAt y N a (v j) (basePart₂ z) * N.h (basePart₂ z) ^ a * Real.sqrt (∑ i : Fin r, ‖z ⟨none, i⟩‖ ^ 2) =
          ‖z ⟨none, j⟩‖ * Real.sqrt (Φ (basePart₂ z))) ∧
      (∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ ξ : (Σ k, addIdx ι r k) → ℂ,
        IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal (addBlock y v)) z ξ →
        leviForm (fun z => Real.log (Φ (basePart₂ z))) z ξ =
          leviForm (fun z : (Σ k, addIdx ι r k) → ℂ => Real.log (∑ i : Fin r, ‖z ⟨none, i⟩‖ ^ 2)) z ξ)

end

end GroundTheory.Heights₂.Heights.Targets
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace LiftGraphMetric

theorem pderiv_rename_of_injective {σ τ R : Type*} [CommSemiring R] {f : σ → τ} (hf : Function.Injective f)
    (x : σ) (p : MvPolynomial σ R) : pderiv (f x) (rename f p) = rename f (pderiv x p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, rename_X, Derivation.leibniz, hp, smul_eq_mul, map_add]
    congr 1
    rw [pderiv_X, pderiv_X]
    by_cases hnx : n = x
    · subst hnx; simp
    · rw [Pi.single_eq_of_ne (hf.ne hnx), Pi.single_eq_of_ne hnx]; simp

theorem pderiv_rename_of_not_mem_range {σ τ R : Type*} [CommSemiring R] {f : σ → τ} {t : τ}
    (ht : t ∉ Set.range f) (p : MvPolynomial σ R) : pderiv t (rename f p) = 0 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp =>
    have hne : f n ≠ t := fun h => ht ⟨n, h⟩
    simp only [map_mul, rename_X, Derivation.leibniz, hp, smul_eq_mul]
    rw [pderiv_X, Pi.single_eq_of_ne hne]
    simp

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {r : ℕ}

def oldEmb (r : ℕ) : (Σ k, ι k) → (Σ k, addIdx ι r k) := fun p => ⟨some p.1, p.2⟩

theorem oldEmb_injective : Function.Injective (oldEmb (ι := ι) r) := by
  rintro ⟨k, i⟩ ⟨k', i'⟩ h
  have h1 : k = k' := Option.some.inj (congrArg Sigma.fst h)
  subst h1
  have h2 := eq_of_heq (Sigma.mk.inj h).2
  subst h2
  rfl

def oldCLM (r : ℕ) : ((Σ k, addIdx ι r k) → ℂ) →L[ℂ] ((Σ k, ι k) → ℂ) :=
  ContinuousLinearMap.pi fun p => ContinuousLinearMap.proj (oldEmb r p)


theorem isOpen_allNZ {κ : Type} [Fintype κ] {ρ : κ → Type} :
    IsOpen {z : (Σ k, ρ k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, ρ k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext; simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

variable {Ω : Type} [Field Ω]

theorem rename_mem_mCoordIdeal (y : (Σ k, ι k) → Ω) (v : Fin r → Ω) {f : MRing ι}
    (hf : f ∈ mCoordIdeal y) : rename (oldEmb r) f ∈ mCoordIdeal (addBlock y v) := by
  rw [mCoordIdeal, RingHom.mem_ker] at hf ⊢
  have key : ∀ g : MRing ι, mConeMap (addBlock y v) (rename (oldEmb r) g) = rename some (mConeMap y g) := by
    intro g
    simp only [mConeMap, aeval_rename]
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p n hp =>
      simp only [map_mul, aeval_X, hp, Function.comp_apply, rename_C, rename_X]
      rfl
  rw [key, hf, map_zero]

theorem oldPart_mem_mcPts {y : (Σ k, ι k) → Ω} {v : Fin r → Ω} {z : (Σ k, addIdx ι r k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal (addBlock y v))) : basePart₂ z ∈ mcPts (mCoordIdeal y) := by
  refine ⟨fun k => hz.1 (some k), fun f hf => ?_⟩
  have h := hz.2 _ (rename_mem_mCoordIdeal y v hf)
  rw [map_rename, eval_rename] at h
  exact h

theorem isConeTangent_oldPart {y : (Σ k, ι k) → Ω} {v : Fin r → Ω} {P0 : Ideal (MRing ι)}
    (hP0 : P0 ≤ mCoordIdeal y) {z ξ : (Σ k, addIdx ι r k) → ℂ}
    (hξ : IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal (addBlock y v)) z ξ) :
    IsConeTangent (Int.castRingHom ℂ) P0 (basePart₂ z) (basePart₂ ξ) := by
  intro f hf
  have h := hξ _ (rename_mem_mCoordIdeal y v (hP0 hf))
  rw [map_rename] at h
  have hnone : ∀ i : Fin r, pderiv (⟨none, i⟩ : Σ k, addIdx ι r k)
      (rename (oldEmb r) (map (Int.castRingHom ℂ) f)) = 0 := by
    intro i
    refine pderiv_rename_of_not_mem_range ?_ _
    rintro ⟨p, hp⟩
    exact Option.some_ne_none _ (congrArg Sigma.fst hp)
  have hsum : ∑ q : (Σ k, addIdx ι r k),
      eval z (pderiv q (rename (oldEmb r) (map (Int.castRingHom ℂ) f))) * ξ q =
      ∑ p : (Σ k, ι k), eval (basePart₂ z) (pderiv p (map (Int.castRingHom ℂ) f)) * basePart₂ ξ p := by
    rw [Fintype.sum_sigma, Fintype.sum_sigma, Fintype.sum_option]
    rw [Finset.sum_eq_zero (fun i _ => by rw [hnone i]; simp), zero_add]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    have e := pderiv_rename_of_injective (oldEmb_injective (r := r)) (⟨k, i⟩ : Σ k, ι k)
      (map (Int.castRingHom ℂ) f)
    simp only [oldEmb] at e
    rw [e, eval_rename]
    rfl
  rw [← hsum]
  exact h

theorem levi_const_mul {κ : Type} [Fintype κ] {g : (κ → ℂ) → ℝ} {z : κ → ℂ} (c : ℝ)
    (hg : ContDiffAt ℝ 2 g z) (w : κ → ℂ) :
    ReciprocityTheory.AnForm.levi (fun y => c * g y) z w = c * ReciprocityTheory.AnForm.levi g z w := by
  have h := ReciprocityTheory.AnForm.levi_add_smul (f := fun _ => (0 : ℝ)) c contDiffAt_const hg w
  simp only [zero_add] at h
  rw [h]
  have h0 : ReciprocityTheory.AnForm.levi (fun _ : κ → ℂ => (0 : ℝ)) z w = 0 := by
    simp [ReciprocityTheory.AnForm.levi]
  rw [h0, zero_add]

theorem proof (hF : LiftGraphFactor.Statement) : LiftGraphMetric.Statement := by
  intro K _ _ ι _ Ω _ y N P0 a r v hP0 hN hNc hv hgen
  classical
  obtain ⟨Φ, hΦs, hΦp, hΦh, hΦc, hΦv, hΦl⟩ := hF K ι Ω y N a r v hv hgen
  let U : Set ((Σ k, addIdx ι r k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  let U0 : Set ((Σ k, ι k) → ℂ) := {w | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0}
  let S : ((Σ k, addIdx ι r k) → ℂ) → ℝ := fun z => ∑ i : Fin r, ‖z ⟨none, i⟩‖ ^ 2
  let F : ((Σ k, addIdx ι r k) → ℂ) → ℝ := fun z =>
    N.h (basePart₂ z) ^ a * Real.sqrt (S z) / Real.sqrt (Φ (basePart₂ z))
  have hUo : IsOpen U := isOpen_allNZ
  have hU0o : IsOpen U0 := isOpen_allNZ
  have hold : ∀ z ∈ U, basePart₂ z ∈ U0 := fun z hz k => hz (some k)
  have hSpos : ∀ z ∈ U, 0 < S z := by
    intro z hz
    obtain ⟨i, hi⟩ := hz none
    have hi' : 0 < ‖z ⟨none, i⟩‖ ^ 2 := by positivity
    exact lt_of_lt_of_le hi' (Finset.single_le_sum (f := fun i : Fin r => ‖z ⟨none, i⟩‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ i))
  have hNpos : ∀ z ∈ U, 0 < N.h (basePart₂ z) := fun z hz => N.pos _ (hold z hz)
  have hΦpos : ∀ z ∈ U, 0 < Φ (basePart₂ z) := fun z hz => hΦp _ (hold z hz)
  have hFpos : ∀ z ∈ U, 0 < F z := fun z hz =>
    div_pos (mul_pos (pow_pos (hNpos z hz) _) (Real.sqrt_pos.2 (hSpos z hz))) (Real.sqrt_pos.2 (hΦpos z hz))
  have hmemU : ∀ c : Option K → ℂ, (∀ k, c k ≠ 0) → ∀ z : (Σ k, addIdx ι r k) → ℂ,
      ((fun p => c p.1 * z p) ∈ U ↔ z ∈ U) := by
    intro c hc z
    simp only [U, Set.mem_setOf_eq, ne_eq, mul_eq_zero, not_or]
    exact forall_congr' fun k => exists_congr fun i => and_iff_right (hc k)
  let A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (addIdx ι r) :=
    { a := unitDeg none
      h := fun z => if z ∈ U then F z else 0
      pos := fun z hz => by
        simp only [if_pos (show z ∈ U from hz)]
        exact hFpos z hz
      smul := by
        intro c z hc
        by_cases hz : z ∈ U
        · rw [if_pos ((hmemU c hc z).2 hz), if_pos hz]
          let c' : K → ℂ := fun k => c (some k)
          have hc' : ∀ k, c' k ≠ 0 := fun k => hc _
          have h1 : N.h (basePart₂ (fun p => c p.1 * z p)) = (∏ k, ‖c' k‖ ^ N.a k) * N.h (basePart₂ z) :=
            N.smul c' (basePart₂ z) hc'
          have h2 : Φ (basePart₂ (fun p => c p.1 * z p)) =
              (∏ k, ‖c' k‖ ^ ((a • N.a) k)) ^ 2 * Φ (basePart₂ z) :=
            hΦh c' (basePart₂ z) hc' (hold z hz)
          have h3 : S (fun p => c p.1 * z p) = ‖c none‖ ^ 2 * S z := by
            simp only [S, norm_mul, mul_pow, Finset.mul_sum]
          have hprod : ∏ k : Option K, ‖c k‖ ^ (unitDeg (none : Option K) k) = ‖c none‖ := by
            rw [Fintype.prod_option]
            simp [unitDeg]
          have hpow : (∏ k, ‖c' k‖ ^ N.a k) ^ a = ∏ k, ‖c' k‖ ^ ((a • N.a) k) := by
            rw [← Finset.prod_pow]
            refine Finset.prod_congr rfl fun k _ => ?_
            rw [Pi.smul_apply, nsmul_eq_mul, mul_comm, zpow_mul, zpow_natCast]
          have hPpos : 0 < ∏ k, ‖c' k‖ ^ ((a • N.a) k) :=
            Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hc' k)) _
          have hs1 : Real.sqrt (S (fun p => c p.1 * z p)) = ‖c none‖ * Real.sqrt (S z) := by
            rw [h3, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
          have hs2 : Real.sqrt (Φ (basePart₂ (fun p => c p.1 * z p))) =
              (∏ k, ‖c' k‖ ^ ((a • N.a) k)) * Real.sqrt (Φ (basePart₂ z)) := by
            rw [h2, Real.sqrt_mul (by positivity), Real.sqrt_sq hPpos.le]
          have hΦ0 : 0 < Real.sqrt (Φ (basePart₂ z)) := Real.sqrt_pos.2 (hΦpos z hz)
          simp only [F]
          rw [hprod, hs1, hs2, h1, mul_pow, hpow]
          field_simp
        · rw [if_neg (mt (hmemU c hc z).1 hz), if_neg hz, mul_zero] }
  have hAh : ∀ z, A.h z = if z ∈ U then F z else 0 := fun z => rfl
  have h2le : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
  have hoR : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, addIdx ι r k) → ℂ => basePart₂ z) :=
    ((oldCLM (ι := ι) r).restrictScalars ℝ).contDiff
  have hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S :=
    ContDiff.sum fun i _ => (contDiff_norm_sq ℂ).comp (contDiff_apply ℝ ℂ _)
  have hNs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) N.h U0 := hN.1
  have hNo : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => N.h (basePart₂ z)) U :=
    hNs.comp hoR.contDiffOn fun z hz => hold z hz
  have hΦo : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Φ (basePart₂ z)) U :=
    hΦs.comp hoR.contDiffOn fun z hz => hold z hz
  have hFs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U :=
    ((hNo.pow a).mul (hS.contDiffOn.sqrt fun z hz => (hSpos z hz).ne')).div
      (hΦo.sqrt fun z hz => (hΦpos z hz).ne') fun z hz => (Real.sqrt_pos.2 (hΦpos z hz)).ne'
  have hAs : IsSmoothHerm A := hFs.congr fun z hz => by rw [hAh, if_pos hz]
  refine ⟨A, rfl, ?_, ⟨hAs, ?_⟩, ?_⟩
  ·
    intro z
    have hmem : (fun p => (starRingEnd ℂ) (z p)) ∈ U ↔ z ∈ U := by
      simp only [U, Set.mem_setOf_eq, ne_eq, map_eq_zero]
    rw [hAh, hAh]
    by_cases hz : z ∈ U
    · rw [if_pos (hmem.2 hz), if_pos hz]
      have e1 : N.h (basePart₂ fun p => (starRingEnd ℂ) (z p)) = N.h (basePart₂ z) := hNc (basePart₂ z)
      have e2 : Φ (basePart₂ fun p => (starRingEnd ℂ) (z p)) = Φ (basePart₂ z) := hΦc (basePart₂ z)
      simp only [F, S]
      rw [e1, e2]
      simp only [Complex.norm_conj]
    · rw [if_neg (mt hmem.1 hz), if_neg hz]
  ·
    intro z hz ξ hξ
    have hzU : z ∈ U := hz.1
    have hw := oldPart_mem_mcPts hz
    have hwU : basePart₂ z ∈ U0 := hw.1
    have hev : (fun x => Real.log (A.h x)) =ᶠ[𝓝 z] fun x =>
        (a : ℝ) * Real.log (N.h (basePart₂ x)) +
          (1 / 2 : ℝ) * (Real.log (S x) + (-1 : ℝ) * Real.log (Φ (basePart₂ x))) := by
      filter_upwards [hUo.mem_nhds hzU] with x hx
      rw [hAh, if_pos hx]
      have hN0 := hNpos x hx
      have hS0 := hSpos x hx
      have hΦ0 := hΦpos x hx
      simp only [F]
      rw [Real.log_div (by positivity) (Real.sqrt_pos.2 hΦ0).ne', Real.log_mul (by positivity)
        (Real.sqrt_pos.2 hS0).ne', Real.log_pow, Real.log_sqrt hS0.le, Real.log_sqrt hΦ0.le]
      ring
    have hNlog : ContDiffAt ℝ 2 (fun w => Real.log (N.h w)) (basePart₂ z) :=
      ((hNs.contDiffAt (hU0o.mem_nhds hwU)).of_le h2le).log (N.pos _ hwU).ne'
    have hL1 : ContDiffAt ℝ 2 (fun x => Real.log (N.h (basePart₂ x))) z :=
      hNlog.comp z (hoR.contDiffAt.of_le h2le)
    have hL2 : ContDiffAt ℝ 2 (fun x => Real.log (S x)) z :=
      (hS.contDiffAt.of_le h2le).log (hSpos z hzU).ne'
    have hL3 : ContDiffAt ℝ 2 (fun x => Real.log (Φ (basePart₂ x))) z :=
      (((hΦs.contDiffAt (hU0o.mem_nhds hwU)).of_le h2le).log (hΦp _ hwU).ne').comp z
        (hoR.contDiffAt.of_le h2le)
    have hcomp : ReciprocityTheory.AnForm.levi (fun x => Real.log (N.h (basePart₂ x))) z ξ =
        ReciprocityTheory.AnForm.levi (fun w => Real.log (N.h w)) (basePart₂ z) (basePart₂ ξ) := by
      have h := ReciprocityTheory.AnForm.levi_comp (φ := fun w => Real.log (N.h w))
        (τ := ⇑(oldCLM (ι := ι) r)) (z := z) ξ ((oldCLM (ι := ι) r).analyticAt z) hNlog
      rw [ContinuousLinearMap.fderiv] at h
      exact h
    have hsemi : 0 ≤ ReciprocityTheory.AnForm.levi (fun w => Real.log (N.h w)) (basePart₂ z) (basePart₂ ξ) :=
      hN.2 (basePart₂ z) hw (basePart₂ ξ) (isConeTangent_oldPart hP0 hξ)
    have hfac : ReciprocityTheory.AnForm.levi (fun x => Real.log (Φ (basePart₂ x))) z ξ =
        ReciprocityTheory.AnForm.levi (fun x => Real.log (S x)) z ξ := hΦl z hz ξ hξ
    show 0 ≤ ReciprocityTheory.AnForm.levi (fun x => Real.log (A.h x)) z ξ
    rw [ReciprocityTheory.AnForm.levi_congr hev,
      ReciprocityTheory.AnForm.levi_add_smul (f := fun x => (a : ℝ) * Real.log (N.h (basePart₂ x)))
        (1 / 2 : ℝ) (contDiffAt_const.mul hL1) (hL2.add (contDiffAt_const.mul hL3)) ξ,
      levi_const_mul (a : ℝ) hL1 ξ,
      ReciprocityTheory.AnForm.levi_add_smul (-1 : ℝ) hL2 hL3 ξ, hcomp, hfac]
    have := mul_nonneg (Nat.cast_nonneg a) hsemi
    linarith
  ·
    intro z hz j
    have hzU : z ∈ U := hz.1
    have h := hΦv z hz j
    have hΦ0 : 0 < Real.sqrt (Φ (basePart₂ z)) := Real.sqrt_pos.2 (hΦpos z hzU)
    rw [hAh, if_pos hzU]
    simp only [F]
    rw [mul_div_assoc', ← mul_assoc, h, mul_div_assoc, div_self hΦ0.ne', mul_one]

end LiftGraphMetric

end

end GroundTheory.Heights₂.Heights.Targets
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

set_option linter.unusedSectionVars false

namespace LiftGraphFactor

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def blkNorm (w : (Σ k, ι k) → ℂ) (k : K) : ℝ := Real.sqrt (∑ i, ‖w ⟨k, i⟩‖ ^ 2)

theorem blkSq_pos {w : (Σ k, ι k) → ℂ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (k : K) :
    0 < ∑ i, ‖w ⟨k, i⟩‖ ^ 2 := by
  obtain ⟨i, hi⟩ := hw k
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hi) 2)
    (Finset.single_le_sum (f := fun i => ‖w ⟨k, i⟩‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i))

theorem blkNorm_pos {w : (Σ k, ι k) → ℂ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (k : K) : 0 < blkNorm w k :=
  Real.sqrt_pos.2 (blkSq_pos hw k)

theorem blkNorm_smul (c : K → ℂ) (w : (Σ k, ι k) → ℂ) (k : K) :
    blkNorm (fun p => c p.1 * w p) k = ‖c k‖ * blkNorm w k := by
  unfold blkNorm
  have : ∑ i, ‖c k * w ⟨k, i⟩‖ ^ 2 = ‖c k‖ ^ 2 * ∑ i, ‖w ⟨k, i⟩‖ ^ 2 := by
    simp only [norm_mul, mul_pow, Finset.mul_sum]
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem blkNorm_conj (w : (Σ k, ι k) → ℂ) (k : K) :
    blkNorm (fun p => (starRingEnd ℂ) (w p)) k = blkNorm w k := by
  simp [blkNorm]

def fsLineZ (n : K → ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι where
  a := n
  h w := ∏ k, blkNorm w k ^ n k
  pos w hw := Finset.prod_pos fun k _ => zpow_pos (blkNorm_pos hw k) _
  smul c w hc := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [blkNorm_smul, mul_zpow]

theorem contDiffAt_zpow_of_ne {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E}
    {N : WithTop ℕ∞} (hf : ContDiffAt ℝ N f x) (hx : f x ≠ 0) (m : ℤ) :
    ContDiffAt ℝ N (fun y => f y ^ m) x := by
  cases m with
  | ofNat k =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact hf.pow k
  | negSucc k =>
    simp only [zpow_negSucc]
    exact (hf.pow (k + 1)).inv (pow_ne_zero _ hx)

theorem isSmoothHerm_fsLineZ (n : K → ℤ) : IsSmoothHerm (fsLineZ (ι := ι) n) := by
  intro w hw
  refine ContDiffAt.contDiffWithinAt ?_
  show ContDiffAt ℝ _ (fun x => ∏ k, blkNorm x k ^ n k) w
  refine contDiffAt_prod (t := Finset.univ) (f := fun k x => blkNorm x k ^ n k) fun k _ => ?_
  refine contDiffAt_zpow_of_ne (f := fun x => blkNorm x k) ?_ (blkNorm_pos hw k).ne' (n k)
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : (Σ k, ι k) → ℂ => ∑ i, ‖x ⟨k, i⟩‖ ^ 2) :=
    ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ _)
  exact hs.contDiffAt.sqrt (blkSq_pos hw k).ne'

theorem conj_fsLineZ (n : K → ℤ) : IsConjInvariantH (fsLineZ (ι := ι) n) := by
  intro w
  show ∏ k, blkNorm _ k ^ n k = ∏ k, blkNorm w k ^ n k
  simp only [blkNorm_conj]

end LiftGraphFactor

open LiftGraphFactor in

theorem LiftGraphFactor.proof (hExt : SectionNormSqExtension.Statement) : LiftGraphFactor.Statement := by
  intro K _ _ ι _ Ω _ y N a r v hv hgen
  classical
  let A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fsLineZ (a • N.a)
  have hA1 : ∀ j, v j ∈ chartLat y A.a 1 := hv
  have hgen' : KH.GeneratesOn y (fun k => ((1 : ℕ) : ℤ) * A.a k) v := by
    have e : (fun k => ((1 : ℕ) : ℤ) * A.a k) = a • N.a := by
      funext k
      simp [A, fsLineZ]
    rw [e]
    exact hgen
  obtain ⟨S, hSs, hSp, hSt, hSc, hSv, hSl⟩ :=
    hExt K ι Ω y A 1 r v (isSmoothHerm_fsLineZ _) (conj_fsLineZ _) hA1 hgen'
  let U0 : Set ((Σ k, ι k) → ℂ) := {w | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0}
  have hAs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.h U0 := isSmoothHerm_fsLineZ _
  refine ⟨fun w => S w * A.h w ^ 2, hSs.mul (hAs.pow 2), fun w hw => mul_pos (hSp w hw) (pow_pos (A.pos w hw) 2),
    ?_, ?_, ?_, ?_⟩
  ·
    intro c w hc hw
    show S _ * A.h _ ^ 2 = _ * (S w * A.h w ^ 2)
    rw [hSt c w hc, A.smul c w hc]
    have hAa : A.a = a • N.a := rfl
    rw [hAa]
    ring
  ·
    intro w
    show S _ * A.h _ ^ 2 = S w * A.h w ^ 2
    rw [hSc w, conj_fsLineZ _ w]
  ·
    intro z hz j
    have hx := PowerBlockMetric.oldPart_mem hz
    obtain ⟨c, hc⟩ := PowerBlockMetric.graph_prop (A := A) (m := 1) hA1 hgen' hz
    have hvN : ∀ j, v j ∈ chartLat y N.a a := by
      intro j c' hc'
      have h := hv j c' hc'
      have e : ∀ k, -(((1 : ℕ) : ℤ) * (a • N.a) k) = -((a : ℤ) * N.a k) := fun k => by
        simp [Pi.smul_apply]
      simp only [e] at h
      exact h

    have key : ∀ j, secNormAt y N a (v j) (basePart₂ z) * N.h (basePart₂ z) ^ a =
        ‖PowerBlockMetric.val y A 1 (v j) (basePart₂ z)‖ * A.h (basePart₂ z) := by
      intro j
      obtain ⟨⟨g, h⟩, hr, hne⟩ := PowerBlockMetric.exists_rep_at (hA1 j) hx
      have hrN : PowerBlockMetric.IsRep y N.a a (v j) g h := by
        obtain ⟨dg, dh, hg, hh, hd, hy⟩ := hr
        refine ⟨dg, dh, hg, hh, fun k => ?_, hy⟩
        rw [hd k]
        simp [A, fsLineZ, Pi.smul_apply]
      have eA := PowerBlockMetric.val_spec (hA1 j) hx hr
      have eN := PowerBlockMetric.val_spec (hvN j) hx hrN
      have hNp : 0 < N.h (basePart₂ z) := N.pos _ hx.1
      have hAp : 0 < A.h (basePart₂ z) := A.pos _ hx.1
      have e2 : PowerBlockMetric.val y N a (v j) (basePart₂ z) * (N.h (basePart₂ z) : ℂ) ^ a =
          PowerBlockMetric.val y A 1 (v j) (basePart₂ z) * (A.h (basePart₂ z) : ℂ) := by
        apply mul_right_cancel₀ hne
        have := eN.symm.trans eA
        simp only [pow_one] at this
        linear_combination this
      rw [PowerBlockMetric.secNormAt_eq (hvN j) hx]
      have := congrArg norm e2
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hNp.le,
        Real.norm_of_nonneg hAp.le] at this
      exact this
    have hS : S (basePart₂ z) = ∑ i, ‖PowerBlockMetric.val y A 1 (v i) (basePart₂ z)‖ ^ 2 := by
      rw [hSv _ hx]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [PowerBlockMetric.secNormAt_eq (hA1 i) hx]
    have hN : ∑ i : Fin r, ‖z ⟨none, i⟩‖ ^ 2 = ‖c‖ ^ 2 * S (basePart₂ z) := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc i, norm_mul, mul_pow]
    have hSp' : 0 ≤ S (basePart₂ z) := (hSp _ hx.1).le
    have hAp : 0 < A.h (basePart₂ z) := A.pos _ hx.1
    rw [key j, hN, hc j, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_mul hSp', Real.sqrt_sq hAp.le, norm_mul]
    ring
  ·
    intro z hz ξ hξ
    have hx := PowerBlockMetric.oldPart_mem hz
    have hw : basePart₂ z ∈ U0 := hx.1
    have hU0o : IsOpen U0 := LiftGraphMetric.isOpen_allNZ
    have hUo : IsOpen {z : (Σ k, addIdx ι r k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := LiftGraphMetric.isOpen_allNZ
    have h2le : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
    have hoR : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, addIdx ι r k) → ℂ => basePart₂ z) :=
      ((LiftGraphMetric.oldCLM (ι := ι) r).restrictScalars ℝ).contDiff
    have hSlog : ContDiffAt ℝ 2 (fun w => Real.log (S w)) (basePart₂ z) :=
      ((hSs.contDiffAt (hU0o.mem_nhds hw)).of_le h2le).log (hSp _ hw).ne'
    have hAlog : ContDiffAt ℝ 2 (fun w => Real.log (A.h w)) (basePart₂ z) :=
      ((hAs.contDiffAt (hU0o.mem_nhds hw)).of_le h2le).log (A.pos _ hw).ne'
    have hL1 : ContDiffAt ℝ 2 (fun x : (Σ k, addIdx ι r k) → ℂ => Real.log (∑ i : Fin r, ‖x ⟨none, i⟩‖ ^ 2)) z :=
      (PowerBlockMetric.contDiff_newSq.contDiffAt).log (PowerBlockMetric.newSq_pos hz.1).ne'
    have hL2 : ContDiffAt ℝ 2 (fun x : (Σ k, addIdx ι r k) → ℂ => Real.log (S (basePart₂ x))) z :=
      hSlog.comp z (hoR.contDiffAt.of_le h2le)
    have hL3 : ContDiffAt ℝ 2 (fun x : (Σ k, addIdx ι r k) → ℂ => Real.log (A.h (basePart₂ x))) z :=
      hAlog.comp z (hoR.contDiffAt.of_le h2le)
    have hcomp : ReciprocityTheory.AnForm.levi (fun x => Real.log (A.h (basePart₂ x))) z ξ =
        ReciprocityTheory.AnForm.levi (fun w => Real.log (A.h w)) (basePart₂ z) (basePart₂ ξ) := by
      have h := ReciprocityTheory.AnForm.levi_comp (φ := fun w => Real.log (A.h w))
        (τ := ⇑(LiftGraphMetric.oldCLM (ι := ι) r)) (z := z) ξ
        ((LiftGraphMetric.oldCLM (ι := ι) r).analyticAt z) hAlog
      rw [ContinuousLinearMap.fderiv] at h
      exact h
    have hev : (fun x : (Σ k, addIdx ι r k) → ℂ => Real.log (S (basePart₂ x) * A.h (basePart₂ x) ^ 2)) =ᶠ[𝓝 z]
        fun x => Real.log (S (basePart₂ x)) + (2 : ℝ) * Real.log (A.h (basePart₂ x)) := by
      filter_upwards [hUo.mem_nhds hz.1] with x hx'
      have hw' : basePart₂ x ∈ U0 := fun k => hx' (some k)
      rw [Real.log_mul (hSp _ hw').ne' (pow_pos (A.pos _ hw') 2).ne', Real.log_pow]
      norm_num
    have hgraph := hSl z hz ξ hξ
    have hsplit : (fun z' : (Σ k, addIdx ι r k) → ℂ =>
        Real.log (∑ j, ‖z' ⟨none, j⟩‖ ^ 2) / 2 - Real.log (S (basePart₂ z')) / 2) =
        fun z' => (1 / 2 : ℝ) * Real.log (∑ j, ‖z' ⟨none, j⟩‖ ^ 2) +
          (-1 / 2 : ℝ) * Real.log (S (basePart₂ z')) := by
      funext z'
      ring
    show ReciprocityTheory.AnForm.levi _ z ξ = ReciprocityTheory.AnForm.levi _ z ξ
    change ReciprocityTheory.AnForm.levi _ z ξ = (1 : ℕ) * ReciprocityTheory.AnForm.levi _ (basePart₂ z) (basePart₂ ξ) at hgraph
    rw [hsplit, ReciprocityTheory.AnForm.levi_add_smul (f := fun x : (Σ k, addIdx ι r k) → ℂ =>
        (1 / 2 : ℝ) * Real.log (∑ j, ‖x ⟨none, j⟩‖ ^ 2)) (-1 / 2 : ℝ) (contDiffAt_const.mul hL1) hL2 ξ,
      ] at hgraph
    have hhalf := LiftGraphMetric.levi_const_mul (1 / 2 : ℝ) hL1 ξ
    erw [hhalf] at hgraph
    rw [← hcomp] at hgraph
    rw [ReciprocityTheory.AnForm.levi_congr hev, ReciprocityTheory.AnForm.levi_add_smul (2 : ℝ) hL2 hL3 ξ]
    push_cast at hgraph
    linarith

end

end GroundTheory.Heights₂.Heights.Targets
end
