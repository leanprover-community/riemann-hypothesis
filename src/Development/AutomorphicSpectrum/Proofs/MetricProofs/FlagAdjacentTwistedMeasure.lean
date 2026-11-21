import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedAtlasCompatibility
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HoloOnDivCongr
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeScalarFactor
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentFrameComparison
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverTwoFramesComparison
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryTwistMinorOtherSteps
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryTwistMinorScalar
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedAtlasCompatibilityStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolution

section
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem log_refNorm_blocks {κ : Type} [Fintype κ] {ρ : κ → Type} [∀ k, Fintype (ρ k)] (d : κ → ℤ)
    {z : (Σ k, ρ k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (refNorm d z) = ∑ k, (d k : ℝ) / 2 * Real.log (∑ i, ‖z ⟨k, i⟩‖ ^ 2) := by
  have hpos : ∀ k, 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2)
      (Finset.single_le_sum (fun i _ => sq_nonneg ‖z ⟨k, i⟩‖) (Finset.mem_univ i))
  unfold refNorm
  rw [Real.log_prod fun k _ => (Real.rpow_pos_of_pos (hpos k) _).ne']
  exact Finset.sum_congr rfl fun k _ => Real.log_rpow (hpos k) _

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem xiDeg_self (M : FlagModel y Ψ N j) {τ : Ψ} {a : Fin N} {k₀ : K} (hk : M.blk (τ, a) = some k₀) :
    xiDeg M τ a k₀ = -2 := by
  have hd : ∀ p, M.dy p k₀ = if p = (τ, a) then 1 else 0 := fun p => by
    have hn : ¬ ∀ p', M.blk p' ≠ some k₀ := fun h => h _ hk
    unfold FlagModel.dy
    rw [dif_neg hn]
    by_cases hp : p = (τ, a)
    · rw [if_pos (hp ▸ hk), if_pos hp]
    · rw [if_neg fun e => hp (M.blk_inj _ _ k₀ e hk), if_neg hp]
  unfold xiDeg
  simp only [hd, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [xiCoef]

theorem log_potA : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K), M.blk (τ, a) = some k₀ → ∀ zz : (Σ o : Option K, ι (o.getD k₀)) → ℂ, (∀ o, ∃ i, zz ⟨o, i⟩ ≠ 0) → Real.log ((potA M τ a k₀).h zz) = -(1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h (fstPt k₀ zz)) + Real.log ((fsHerm ι (M.dy p)).h (sndPt k₀ zz))) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a k₀ hk zz hz
  have hf : ∀ k, ∃ i, fstPt k₀ zz ⟨k, i⟩ ≠ 0 := fun k => hz (some k)
  have hs : ∀ k, ∃ i, sndPt k₀ zz ⟨k, i⟩ ≠ 0 := fun k => by
    by_cases e : k = k₀
    · subst e
      obtain ⟨i, hi⟩ := hz none
      refine ⟨i, ?_⟩
      simpa [sndPt, v₁_self] using hi
    · obtain ⟨i, hi⟩ := hz (some k)
      refine ⟨i, ?_⟩
      simpa [sndPt, v₁_ne (p := ⟨k, i⟩) e] using hi
  set A : K → ℝ := fun k => Real.log (∑ i, ‖fstPt k₀ zz ⟨k, i⟩‖ ^ 2) with hA
  set B : K → ℝ := fun k => Real.log (∑ i, ‖sndPt k₀ zz ⟨k, i⟩‖ ^ 2) with hB
  set Ln : ℝ := Real.log (∑ i : ι k₀, ‖zz ⟨none, i⟩‖ ^ 2) with hLn
  have hB₀ : B k₀ = Ln := by
    simp only [hB, hLn, sndPt, Function.comp_apply, v₁_self]
  have hBne : ∀ k, k ≠ k₀ → B k = A k := fun k e => by
    simp only [hA, hB, fstPt, sndPt, Function.comp_apply, v₀]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [v₁_ne (p := ⟨k, i⟩) e]
  have hlhs : Real.log ((potA M τ a k₀).h zz) = 1 / 2 * Ln + ∑ k, (aDeg M τ a k₀ (some k) : ℝ) / 2 * A k := by
    show Real.log (refNorm (aDeg M τ a k₀) zz) = _
    rw [log_refNorm_blocks _ hz, Fintype.sum_option]
    simp only [aDeg, hLn, hA]
    norm_num
    rfl
  have hrhs : ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h (fstPt k₀ zz)) +
      Real.log ((fsHerm ι (M.dy p)).h (sndPt k₀ zz))) = ∑ k, (xiDeg M τ a k : ℝ) / 2 * (A k + B k) := by
    have hp : ∀ p, Real.log ((fsHerm ι (M.dy p)).h (fstPt k₀ zz)) + Real.log ((fsHerm ι (M.dy p)).h (sndPt k₀ zz)) =
        ∑ k, (M.dy p k : ℝ) / 2 * (A k + B k) := fun p => by
      rw [fsHerm_h, fsHerm_h, log_refNorm_blocks _ hf, log_refNorm_blocks _ hs, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by simp only [hA, hB]; ring
    simp only [hp, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [xiDeg]
    push_cast
    rw [Finset.sum_div, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hlhs, hrhs]
  have hterm : ∀ k, (aDeg M τ a k₀ (some k) : ℝ) / 2 * A k + 1 / 2 * ((xiDeg M τ a k : ℝ) / 2 * (A k + B k)) =
      if k = k₀ then -(1 / 2) * Ln else 0 := fun k => by
    by_cases e : k = k₀
    · subst e
      rw [if_pos rfl, hB₀, xiDeg_self M hk]
      simp only [aDeg, if_true]
      push_cast
      ring
    · rw [if_neg e, hBne k e]
      simp only [aDeg, if_neg e]
      push_cast
      ring
  have hsum := Finset.sum_congr (rfl : (Finset.univ : Finset K) = _) fun k _ => hterm k
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ k₀, if_pos (Finset.mem_univ _)] at hsum
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_metric_log_formula : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K), M.blk (τ, a) = some k₀ → ∀ zz : (Σ o : Option K, ι (o.getD k₀)) → ℂ, (∀ o, ∃ i, zz ⟨o, i⟩ ≠ 0) → Real.log ((potA M τ a k₀).h zz) = -(1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h (fstPt k₀ zz)) + Real.log ((fsHerm ι (M.dy p)).h (sndPt k₀ zz))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.log_potA
end

section
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Factor

section Holo

variable {e : ℕ} {S : Type} [TopologicalSpace S]

theorem holoOn_mono (A : FinHolAtlas e S) {U V : Set S} {f : S → ℂ} (h : A.HoloOn V f) (hU : U ⊆ V) :
    A.HoloOn U f :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hU))

theorem holoOn_const (A : FinHolAtlas e S) (U : Set S) (c : ℂ) : A.HoloOn U fun _ => c := fun _ _ _ =>
  analyticAt_const

theorem holoOn_mul (A : FinHolAtlas e S) {U : Set S} {f g : S → ℂ} (hf : A.HoloOn U f) (hg : A.HoloOn U g) :
    A.HoloOn U fun w => f w * g w := fun j u hu => (hf j u hu).mul (hg j u hu)

theorem holoOn_zpow (A : FinHolAtlas e S) {U : Set S} {f : S → ℂ} (hf : A.HoloOn U f)
    (h0 : ∀ w ∈ U, f w ≠ 0) (n : ℤ) : A.HoloOn U fun w => f w ^ n := fun j u hu =>
  (hf j u hu).zpow (h0 _ hu.2)

theorem holoOn_prod (A : FinHolAtlas e S) {U : Set S} {κ : Type} (s : Finset κ) {f : κ → S → ℂ}
    (hf : ∀ i ∈ s, A.HoloOn U (f i)) : A.HoloOn U fun w => ∏ i ∈ s, f i w := by
  induction s using Finset.induction_on with
  | empty => simpa using holoOn_const A U 1
  | insert i s hi ih =>
    have h := holoOn_mul A (hf i (Finset.mem_insert_self i s))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
    simpa only [Finset.prod_insert hi] using h

theorem holoOn_minor (A : FinHolAtlas e S) {U : Set S} {N : ℕ} {H : S → Matrix (Fin N) (Fin N) ℂ}
    (hH : ∀ r s, A.HoloOn U fun w => H w r s) (I J : Finset (Fin N)) :
    A.HoloOn U fun w => minorIJ (H w) I J := by
  have h := StepW.ValHolo.holoOn_eval A (b := fun w (q : Fin N × Fin N) => H w q.1 q.2) (fun q => hH q.1 q.2)
    (minorIJ (Matrix.of fun r s => (MvPolynomial.X (r, s) : MvPolynomial (Fin N × Fin N) ℤ)) I J)
  have e : (fun w => minorIJ (H w) I J) = fun w => eval (fun q : Fin N × Fin N => H w q.1 q.2)
      (map (Int.castRingHom ℂ)
        (minorIJ (Matrix.of fun r s => (MvPolynomial.X (r, s) : MvPolynomial (Fin N × Fin N) ℤ)) I J)) := by
    funext w
    let f : MvPolynomial (Fin N × Fin N) ℤ →+* ℂ :=
      (eval fun q : Fin N × Fin N => H w q.1 q.2).comp (map (Int.castRingHom ℂ))
    have hm : (Matrix.of fun r s => (MvPolynomial.X (r, s) : MvPolynomial (Fin N × Fin N) ℤ)).map f = H w := by
      ext r s
      simp [f]
    have := minorIJ_map f (Matrix.of fun r s => (MvPolynomial.X (r, s) : MvPolynomial (Fin N × Fin N) ℤ)) I J
    rw [hm] at this
    exact this
  rw [e]
  exact h

theorem prod_local (A : FinHolAtlas e S) {V : Set S} {y₀ : S} {N : ℕ} (hV : IsOpen V) (hy : y₀ ∈ V)
    (g : Fin N → S → ℂ) (n : Fin N → ℤ)
    (key : ∀ i, ∃ W : Set S, IsOpen W ∧ y₀ ∈ W ∧ W ⊆ V ∧ A.HoloOn W (g i) ∧ ∀ w ∈ W, g i w ≠ 0) :
    ∃ V' : Set S, IsOpen V' ∧ y₀ ∈ V' ∧ V' ⊆ V ∧ A.HoloOn V' (fun w => ∏ i, g i w ^ n i) ∧
      ∀ w ∈ V', ∏ i, g i w ^ n i ≠ 0 := by
  choose W hW hyW hWV hh h0 using key
  have hsub : ∀ i, V ∩ ⋂ i, W i ⊆ W i := fun i => Set.inter_subset_right.trans (Set.iInter_subset _ i)
  refine ⟨V ∩ ⋂ i, W i, hV.inter (isOpen_iInter_of_finite hW), ⟨hy, Set.mem_iInter.2 hyW⟩,
    Set.inter_subset_left, ?_, ?_⟩
  · exact holoOn_prod A _ fun i _ =>
      holoOn_zpow A (holoOn_mono A (hh i) (hsub i)) (fun w hw => h0 i w (hsub i hw)) (n i)
  · exact fun w hw => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (h0 i w (hsub i hw))

end Holo

theorem minor_w_ne {N j : ℕ} (hj : j ≤ N) (i : Fin N) (hi : (i : ℕ) + 1 = j) {T : Matrix (Fin N) (Fin N) ℂ}
    (hT : IsBlockDiag j T) (hd : T.det ≠ 0) : minorIJ T (wIdx N j) (wIdx N j) ≠ 0 := by
  have h := FrameChange.detFac_ne_zero hj i hT hd
  rw [detFac, if_pos hi.ge] at h
  exact left_ne_zero_of_mul h

theorem minor_om_ne {N j : ℕ} (hj : j ≤ N) (i : Fin N) (hi : (i : ℕ) + 1 = N) {T : Matrix (Fin N) (Fin N) ℂ}
    (hT : IsBlockDiag j T) (hd : T.det ≠ 0) : minorIJ T (omIdx N j) (omIdx N j) ≠ 0 := by
  have h := FrameChange.detFac_ne_zero hj i hT hd
  rw [detFac, if_pos hi] at h
  exact right_ne_zero_of_mul h

theorem val_ne {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) {s : Ω} (h0 : s ≠ 0)
    (hs : RegAt x (mCoordIdeal z) s) (hi : RegAt x (mCoordIdeal z) s⁻¹) : valAt x s z ≠ 0 := by
  intro e
  have h := (reg_mul hz hs hi).2
  rw [mul_inv_cancel₀ h0, e, zero_mul] at h
  exact one_ne_zero (((ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.1).symm.trans h)

theorem improper_factor : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (V : Set X) (y₀ : X) (zb : X → (Σ k, baseIdx ι M.blk k) → ℂ) (Hm : X → Matrix (Fin N) (Fin N) ℂ) (F : FrameData ι Ψ N M.Ω M.blk) (τ : Ψ) (a : Fin N), IsOpen V → y₀ ∈ V → (∀ q, A.HoloOn V fun w => zb w q) → (∀ w ∈ V, zb w ∈ mcPts (mCoordIdeal M.x)) → (∀ w ∈ V, M.GoodAt F (mCoordIdeal (zb w))) → (∀ r s, A.HoloOn V fun w => Hm w r s) → (∀ w ∈ V, IsBlockDiag j (Hm w) ∧ (Hm w).det ≠ 0) → ∃ V' : Set X, IsOpen V' ∧ y₀ ∈ V' ∧ V' ⊆ V ∧ A.HoloOn V' (fun w => ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (zb w) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1) else minorIJ (Hm w) (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)) ∧ ∀ w ∈ V', (∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (zb w) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1) else minorIJ (Hm w) (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)) ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M e X _ A V y₀ zb Hm F τ a hV hy hzb hpt hgood hHm hdiag
  refine prod_local A hV hy (fun i w => if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (zb w) *
    (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1)
      else minorIJ (Hm w) (omIdx N j) (omIdx N j))) (fun i => xiCoef τ a (τ, i)) fun i => ?_
  by_cases hp : IsProperStep N j i
  · refine ⟨V, hV, hy, subset_rfl, ?_, fun w _ => ?_⟩
    · simp only [if_pos hp]
      exact holoOn_const A V 1
    · simp only [if_pos hp]
      exact one_ne_zero
  · have hnone : M.blk (τ, i) = none := (M.blk_none (τ, i)).2 hp
    obtain ⟨W, hW, hyW, hWV, hval⟩ := StepW.ValHolo.holoOn_valAt _ _ M.Ω M.x (F.υ (τ, i)) e X A V zb y₀ hV hy hzb hpt
      ((hgood y₀ hy).2.2 _ hnone).2.1
    have hm : A.HoloOn W fun w => (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1)
        else minorIJ (Hm w) (omIdx N j) (omIdx N j)) := by
      have hH : ∀ r s, A.HoloOn W fun w => Hm w r s := fun r s => holoOn_mono A (hHm r s) hWV
      by_cases h1 : (i : ℕ) + 1 = j
      · by_cases h2 : (a : ℕ) < j
        · simp only [if_pos h1, if_pos h2]
          exact holoOn_minor A hH _ _
        · simp only [if_pos h1, if_neg h2]
          exact holoOn_const A W 1
      · simp only [if_neg h1]
        exact holoOn_minor A hH _ _
    refine ⟨W, hW, hyW, hWV, ?_, fun w hw => ?_⟩
    · simp only [if_neg hp]
      exact holoOn_mul A hval hm
    · simp only [if_neg hp]
      have hwV := hWV hw
      have hv : valAt M.x (F.υ (τ, i)) (zb w) ≠ 0 :=
        val_ne (hpt w hwV) ((hgood w hwV).2.2 _ hnone).1 ((hgood w hwV).2.2 _ hnone).2.1
          ((hgood w hwV).2.2 _ hnone).2.2
      refine mul_ne_zero hv ?_
      by_cases h1 : (i : ℕ) + 1 = j
      · by_cases h2 : (a : ℕ) < j
        · simp only [if_pos h1, if_pos h2]
          exact minor_w_ne M.j_le i h1 (hdiag w hwV).1 (hdiag w hwV).2
        · simp only [if_pos h1, if_neg h2]
          exact one_ne_zero
      · simp only [if_neg h1]
        have h3 : (i : ℕ) + 1 = N := by
          by_contra h3
          exact hp ⟨h1, h3⟩
        exact minor_om_ne M.j_le i h3 (hdiag w hwV).1 (hdiag w hwV).2

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Factor
end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_frame_metric_near_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (V : Set X) (y₀ : X) (zb : X → (Σ k, baseIdx ι M.blk k) → ℂ) (Hm : X → Matrix (Fin N) (Fin N) ℂ) (F : FrameData ι Ψ N M.Ω M.blk) (τ : Ψ) (a : Fin N), IsOpen V → y₀ ∈ V → (∀ q, A.HoloOn V fun w => zb w q) → (∀ w ∈ V, zb w ∈ mcPts (mCoordIdeal M.x)) → (∀ w ∈ V, M.GoodAt F (mCoordIdeal (zb w))) → (∀ r s, A.HoloOn V fun w => Hm w r s) → (∀ w ∈ V, IsBlockDiag j (Hm w) ∧ (Hm w).det ≠ 0) → ∃ V' : Set X, IsOpen V' ∧ y₀ ∈ V' ∧ V' ⊆ V ∧ A.HoloOn V' (fun w => ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (zb w) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1) else minorIJ (Hm w) (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)) ∧ ∀ w ∈ V', (∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (zb w) * (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (Hm w) (wIdx N j) (wIdx N j) else 1) else minorIJ (Hm w) (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i)) ≠ 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Factor.improper_factor
end

section
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TriStep

open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

variable {N : ℕ}

theorem minorIJ_one_of_ne {I S : Finset (Fin N)} (hI : I ≠ S) :
    minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I S = 0 := by
  by_cases e : I.card = S.card
  · have hs : ¬ I ⊆ S := fun hs => hI (Finset.eq_of_subset_of_card_le hs e.ge)
    obtain ⟨a, ha, has⟩ := Finset.not_subset.mp hs
    exact minorIJ_eq_zero_of_row _ ha fun c hc => Matrix.one_apply_ne fun h => has (h ▸ hc)
  · exact minorIJ_of_card_ne _ e

theorem minorIJ_one_self' (S : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) S S = 1 := by
  rw [minorIJ_eq_det _ S S _ rfl rfl, Matrix.submatrix_one _ (S.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem det_submatrix_eq_zero (A : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N))
    (hA : ∀ I, I ≠ S → minorIJ A I S = 0) (f : Fin S.card → Fin N) (x : Fin S.card) (hx : f x ∉ S) :
    (A.submatrix f (S.orderEmbOfFin rfl)).det = 0 := by
  by_cases hf : Function.Injective f
  · let σ := Tuple.sort f
    have hm : StrictMono (f ∘ σ) :=
      (Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)
    have hc : (Finset.univ.image f).card = S.card := by
      rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
    have hu : f ∘ σ = (Finset.univ.image f).orderEmbOfFin hc :=
      Finset.orderEmbOfFin_unique hc (fun y => Finset.mem_image_of_mem _ (Finset.mem_univ _)) hm
    have hI : Finset.univ.image f ≠ S := fun e => hx (e ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _))
    have h0 := hA _ hI
    rw [minorIJ_eq_det A _ S _ hc rfl, ← hu] at h0
    have h1 : A.submatrix (f ∘ σ) (S.orderEmbOfFin rfl) =
        (A.submatrix f (S.orderEmbOfFin rfl)).submatrix σ id := by
      ext a b; rfl
    rw [h1, Matrix.det_permute] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exfalso
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e] at h
    · exact h
  · obtain ⟨a, b, hab, hne⟩ : ∃ a b, f a = f b ∧ a ≠ b := by
      simpa [Function.Injective] using hf
    exact Matrix.det_zero_of_row_eq hne (by ext y; simp [hab])

theorem eq_zero_of_minors (B : Matrix (Fin N) (Fin N) ℂ) (hB : B.det ≠ 0) (S : Finset (Fin N))
    (hA : ∀ I, I ≠ S → minorIJ B I S = 0) (r c : Fin N) (hr : r ∉ S) (hc : c ∈ S) : B r c = 0 := by
  set e := S.orderEmbOfFin rfl with he
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have hS : minorIJ B S S ≠ 0 := by
    intro h0
    have h1 := minorIJ_mul B⁻¹ B S S
    rw [Matrix.nonsing_inv_mul _ hu, minorIJ_one_self',
      Finset.sum_eq_single S (fun I _ hI => by rw [hA I hI, mul_zero]) (by simp), h0, mul_zero] at h1
    exact one_ne_zero h1
  rw [minorIJ_eq_det B S S _ rfl rfl] at hS
  let M := B.submatrix e e
  let v : Fin S.card → ℂ := fun y => B r (e y)
  have hcr : Matrix.cramer Mᵀ v = 0 := by
    funext x
    have h1 : Mᵀ.updateCol x v = (B.submatrix (Function.update e x r) e)ᵀ := by
      ext a b
      by_cases hb : b = x
      · subst hb; simp [Matrix.updateCol_apply, v]
      · simp [Matrix.updateCol_apply, hb, M, Function.update_of_ne hb]
    rw [Matrix.cramer_apply, h1, Matrix.det_transpose]
    exact det_submatrix_eq_zero B S hA _ x (by simpa using hr)
  have hv : Mᵀ.det • v = 0 := by rw [← Matrix.mulVec_cramer, hcr, Matrix.mulVec_zero]
  have hv0 : v = 0 := by
    rcases smul_eq_zero.mp hv with h | h
    · rw [Matrix.det_transpose] at h; exact absurd h hS
    · exact h
  have hr' : c ∈ Set.range e := by rw [he, Finset.range_orderEmbOfFin]; exact hc
  obtain ⟨y, rfl⟩ := hr'
  exact congrFun hv0 y

theorem triangular_of_minors_proportional : ∀ (N j : ℕ) (h g : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsBlockDiag j h →
    IsBlockDiag j g → h.det ≠ 0 → g.det ≠ 0 →
    (∀ i : Fin N, IsProperStep N j i → ∃ μ : ℂ, ∀ I, minorIJ g I (stepCols N j i) = μ * minorIJ h I (stepCols N j i)) →
    (h⁻¹ * g).BlockTriangular id := by
  intro N j h g hj hh hg hdh hdg hμ
  have huh : IsUnit h.det := isUnit_iff_ne_zero.mpr hdh
  have hbd : IsBlockDiag j (h⁻¹ * g) := (hh.inv huh).mul hg
  have hdet : (h⁻¹ * g).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv]
    exact mul_ne_zero (by simpa using hdh) hdg
  have hstep : ∀ i : Fin N, IsProperStep N j i → ∀ r c : Fin N, r ∉ stepCols N j i → c ∈ stepCols N j i →
      (h⁻¹ * g) r c = 0 := by
    intro i hi r c hr hc
    obtain ⟨μ, hm⟩ := hμ i hi
    refine eq_zero_of_minors _ hdet _ (fun I hI => ?_) r c hr hc
    have h1 : minorIJ (h⁻¹ * g) I (stepCols N j i) =
        μ * minorIJ (h⁻¹ * h) I (stepCols N j i) := by
      rw [minorIJ_mul, minorIJ_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun I' _ => by rw [hm I']; ring
    rw [h1, Matrix.nonsing_inv_mul _ huh, minorIJ_one_of_ne hI, mul_zero]
  intro r s hrs
  have hsr : (s : ℕ) < r := hrs
  have hrN := r.2
  by_cases hb : ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)
  · by_cases hω : (r : ℕ) < N - j
    · have hi : (s : ℕ) + j < N := by omega
      refine hstep ⟨(s : ℕ) + j, hi⟩ ⟨?_, ?_⟩ r s ?_ ?_
      · simp only; omega
      · simp only; omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_neg (by omega)]; omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_neg (by omega)]; omega
    · have hs' : N - j ≤ (s : ℕ) := by
        by_contra hc; exact hω (hb.mpr (by omega))
      have hi : (s : ℕ) - (N - j) < N := by omega
      refine hstep ⟨(s : ℕ) - (N - j), hi⟩ ⟨?_, ?_⟩ r s ?_ ?_
      · simp only; omega
      · simp only; omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_pos (by omega)]; omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_pos (by omega)]; omega
  · exact hbd r s hb

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TriStep
end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_triangular_of_proportional_minors : ∀ (N j : ℕ) (h g : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsBlockDiag j h → IsBlockDiag j g → h.det ≠ 0 → g.det ≠ 0 → (∀ i : Fin N, IsProperStep N j i → ∃ μ : ℂ, ∀ I, minorIJ g I (stepCols N j i) = μ * minorIJ h I (stepCols N j i)) → (h⁻¹ * g).BlockTriangular id := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TriStep.triangular_of_minors_proportional
end

section
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Same

section Cols

variable {N j : ℕ} {a b ca cb : Fin N}

theorem cols_next (hj : j ≤ N) (hb : (b : ℕ) = a + 1) (hcase : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) :
    stepCols N j b = insert cb (stepCols N j a) ∧ cb ∉ stepCols N j a ∧ ca ∈ stepCols N j a := by
  have hbN := b.2
  rcases hcase with h | h
  · have h1 : (a : ℕ) + 1 ≤ j := by omega
    have h2 : (b : ℕ) + 1 ≤ j := by omega
    simp only [lastCol, if_pos h1] at hca
    refine ⟨?_, ?_, ?_⟩
    · ext c
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h1, if_pos h2,
        Finset.mem_insert, Fin.ext_iff]
      omega
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h1]
      omega
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h1]
      omega
  · have h1 : ¬ (a : ℕ) + 1 ≤ j := by omega
    have h2 : ¬ (b : ℕ) + 1 ≤ j := by omega
    simp only [lastCol, if_neg h1] at hca
    refine ⟨?_, ?_, ?_⟩
    · ext c
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h1, if_neg h2,
        Finset.mem_insert, Fin.ext_iff]
      omega
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h1]
      omega
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h1]
      omega

theorem cols_prev (hj : j ≤ N) (hb : (b : ℕ) = a + 1) (hcase : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) {a' : Fin N} (ha' : (a' : ℕ) + 1 = a) (hp : IsProperStep N j a') :
    stepCols N j a' = (stepCols N j a).erase ca := by
  have hbN := b.2
  have hp1 := hp.1
  rcases hcase with h | h
  · have h1 : (a : ℕ) + 1 ≤ j := by omega
    have h2 : (a' : ℕ) + 1 ≤ j := by omega
    simp only [lastCol, if_pos h1] at hca
    ext c
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h1, if_pos h2,
      Finset.mem_erase, ne_eq, Fin.ext_iff]
    omega
  · have h1 : ¬ (a : ℕ) + 1 ≤ j := by omega
    have h2 : ¬ (a' : ℕ) + 1 ≤ j := by omega
    simp only [lastCol, if_neg h1] at hca
    ext c
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h1, if_neg h2,
      Finset.mem_erase, ne_eq, Fin.ext_iff]
    omega

theorem cols_first (hj : j ≤ N) (hb : (b : ℕ) = a + 1) (hcase : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (h0 : (a : ℕ) = 0 ∨ (a : ℕ) = j) :
    (stepCols N j a).erase ca = ∅ := by
  have hbN := b.2
  rw [Finset.eq_empty_iff_forall_notMem]
  intro c
  by_cases h1 : (a : ℕ) + 1 ≤ j
  · simp only [lastCol, if_pos h1] at hca
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h1,
      Finset.mem_erase, ne_eq, Fin.ext_iff]
    omega
  · simp only [lastCol, if_neg h1] at hca
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h1,
      Finset.mem_erase, ne_eq, Fin.ext_iff]
    omega

theorem transv_blockDiag (hj : j ≤ N) (hb : (b : ℕ) = a + 1) (hcase : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := by
  have hbN := b.2
  have hs : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j := by
    by_cases h1 : (a : ℕ) + 1 ≤ j
    · simp only [lastCol, if_pos h1] at hca
      omega
    · simp only [lastCol, if_neg h1] at hca
      omega
  intro r s h
  have hrs : r ≠ s := fun e => h (by rw [e])
  rw [Matrix.add_apply, Matrix.one_apply_ne hrs, zero_add, Matrix.single_apply_of_ne]
  rintro ⟨rfl, rfl⟩
  exact h hs.symm

theorem fac_next (hj : j ≤ N) (hb : (b : ℕ) = a + 1) (hcase : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hp : ¬ IsProperStep N j b) (h : Matrix (Fin N) (Fin N) ℂ) :
    Fib.facOf N j a h b = minorIJ h (stepCols N j b) (stepCols N j b) := by
  have hbN := b.2
  by_cases h1 : (b : ℕ) + 1 = j
  · have h2 : (a : ℕ) < j := by omega
    have e : stepCols N j b = wIdx N j := by
      ext c
      have := c.2
      simp only [stepCols, wIdx, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h1.le]
      omega
    rw [e]
    simp only [Fib.facOf, if_pos h1, if_pos h2]
  · have h3 : (b : ℕ) + 1 = N := by
      by_contra h3
      exact hp ⟨h1, h3⟩
    have h4 : ¬ (b : ℕ) + 1 ≤ j := by omega
    have e : stepCols N j b = omIdx N j := by
      ext c
      simp only [stepCols, omIdx, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h4]
      omega
    rw [e]
    simp only [Fib.facOf, if_neg h1]

theorem fac_prev (hb : (b : ℕ) = a + 1) {a' : Fin N} (ha' : (a' : ℕ) + 1 = a) (hp : ¬ IsProperStep N j a')
    (h : Matrix (Fin N) (Fin N) ℂ) : Fib.facOf N j a h a' = 1 ∧ (a : ℕ) = j := by
  have hbN := b.2
  have h1 : (a' : ℕ) + 1 = j := by
    by_contra h1
    exact hp ⟨h1, by omega⟩
  have h2 : ¬ (a : ℕ) < j := by omega
  exact ⟨by simp only [Fib.facOf, if_pos h1, if_neg h2], by omega⟩

theorem fac_ne_zero (hj : j ≤ N) (i : Fin N) {h : Matrix (Fin N) (Fin N) ℂ} (hh : IsBlockDiag j h) (hd : h.det ≠ 0)
    (a : Fin N) : Fib.facOf N j a h i ≠ 0 := by
  have hN : 0 < N := by have := i.2; omega
  have hd' := GlobalTheory.CompanionTheory.Ar.PB.CPts.detFac_ne_zero hj (⟨N - 1, by omega⟩ : Fin N) hh hd
  have e1 : j ≤ N - 1 + 1 := by omega
  simp only [detFac, if_pos e1, show N - 1 + 1 = N by omega, if_true, if_pos hj] at hd'
  simp only [Fib.facOf]
  have := left_ne_zero_of_mul hd'
  have := right_ne_zero_of_mul hd'
  split_ifs <;> first | assumption | simp

end Cols

section Xi

variable {Ψ : Type} [DecidableEq Ψ] {N : ℕ}

theorem xi_sum (τ : Ψ) {a b : Fin N} (hb : (b : ℕ) = a + 1) (D : Fin N → ℝ) (D₀ : ℝ)
    (hD : ∀ a' : Fin N, (a' : ℕ) + 1 = a → D a' = D₀) (h0 : (a : ℕ) = 0 → D₀ = 0) :
    ∑ i, (xiCoef τ a (τ, i) : ℝ) * D i = D₀ + D b - 2 * D a := by
  have e : ∀ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * D i =
      (if (i : ℕ) + 1 = a then D i else 0) + (if i = b then D i else 0) - (if i = a then 2 * D i else 0) := by
    intro i
    have e1 : ((i : ℕ) = (a : ℕ) + 1) ↔ i = b := by rw [Fin.ext_iff, hb]
    simp only [xiCoef, if_true, e1]
    push_cast
    split_ifs <;> first | ring | simp
  simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  congr 2
  by_cases ha : (a : ℕ) = 0
  · rw [h0 ha]
    exact Finset.sum_eq_zero fun i _ => if_neg (by omega)
  · have hlt := a.2
    rw [Finset.sum_eq_single (⟨a - 1, by omega⟩ : Fin N)]
    · rw [if_pos (show ((a : ℕ) - 1) + 1 = a by omega)]
      exact hD _ (show ((a : ℕ) - 1) + 1 = a by omega)
    · intro i _ hne
      refine if_neg fun e => hne (Fin.ext ?_)
      show (i : ℕ) = (a : ℕ) - 1
      omega
    · simp

end Xi

section Lines

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ}

theorem log_fs_smul (d : K → ℤ) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log ((fsHerm ι d).h fun p => c p.1 * z p) =
      Real.log ((fsHerm ι d).h z) + ∑ k, (d k : ℝ) * Real.log ‖c k‖ := by
  have hn : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.2 (hc k)
  rw [(fsHerm ι d).smul c z hc,
    Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hn k)) ((fsHerm ι d).pos z hz).ne',
    Real.log_prod (fun k _ => zpow_ne_zero _ (hn k)), add_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ => Real.log_zpow _ _

theorem dy_sum_some (M : FlagModel y Ψ N j) {p : Ψ × Fin N} {k₀ : K} (hk : M.blk p = some k₀) {c : K → ℂ}
    (hc : ∀ k, (∀ p', M.blk p' ≠ some k) → c k = 1) :
    ∑ k, (M.dy p k : ℝ) * Real.log ‖c k‖ = Real.log ‖c k₀‖ := by
  rw [Finset.sum_eq_single k₀]
  · have e : M.dy p k₀ = 1 := by
      unfold FlagModel.dy
      rw [dif_neg (fun h => h p hk), if_pos hk]
    rw [e]
    simp
  · intro k _ hne
    by_cases h : ∀ p', M.blk p' ≠ some k
    · rw [hc k h]
      simp
    · have e : M.dy p k = 0 := by
        unfold FlagModel.dy
        rw [dif_neg h, if_neg fun e => hne (by rw [hk] at e; exact (Option.some_injective _ e).symm)]
      rw [e]
      simp
  · simp

theorem dy_sum_none (M : FlagModel y Ψ N j) {p : Ψ × Fin N} (hp : M.blk p = none) {c : K → ℂ}
    (hc : ∀ k, (∀ p', M.blk p' ≠ some k) → c k = 1) :
    ∑ k, (M.dy p k : ℝ) * Real.log ‖c k‖ = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h : ∀ p', M.blk p' ≠ some k
  · rw [hc k h]
    simp
  · have e : M.dy p k = 0 := by
      unfold FlagModel.dy
      rw [dif_neg h, if_neg fun e => by rw [hp] at e; exact absurd e (by simp)]
    rw [e]
    simp

theorem base_one (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {z z' : (Σ k, ι k) → ℂ} {c : K → ℂ}
    (hz' : z' = fun p => c p.1 * z p) (h₁ : ∀ k, basePart M.blk z ⟨k, F.c k⟩ = 1)
    (h₂ : ∀ k, basePart M.blk z' ⟨k, F.c k⟩ = 1) : ∀ k, (∀ p', M.blk p' ≠ some k) → c k = 1 := by
  intro k hk
  have a₁ : z ⟨k, F.c ⟨k, hk⟩⟩ = 1 := h₁ ⟨k, hk⟩
  have a₂ : z' ⟨k, F.c ⟨k, hk⟩⟩ = 1 := h₂ ⟨k, hk⟩
  rw [hz'] at a₂
  have a₃ : c k * z ⟨k, F.c ⟨k, hk⟩⟩ = 1 := a₂
  rwa [a₁, mul_one] at a₃

theorem base_eq {blk : Ψ × Fin N → Option K} {z z' : (Σ k, ι k) → ℂ} {c : K → ℂ}
    (hz' : z' = fun p => c p.1 * z p) (hc : ∀ k, (∀ p', blk p' ≠ some k) → c k = 1) :
    basePart blk z' = basePart blk z := by
  funext q
  show z' ⟨q.1.1, q.2⟩ = z ⟨q.1.1, q.2⟩
  rw [hz']
  show c q.1.1 * _ = _
  rw [hc _ q.1.2, one_mul]

theorem minors_prop (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} {bp : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hb : bp ∈ mcPts (mCoordIdeal M.x)) (hF : M.IsFrame F) (hG : M.GoodAt F (mCoordIdeal bp)) {p : Ψ × Fin N} {k : K}
    (hk : M.blk p = some k) {z z' : (Σ k, ι k) → ℂ} {c : K → ℂ} (hz' : z' = fun q => c q.1 * z q)
    (hz : basePart M.blk z = bp) (hzb : basePart M.blk z' = bp) {g g' : Matrix (Fin N) (Fin N) ℂ}
    (hg : IsBlockDiag j g) (hg' : IsBlockDiag j g') (e : M.ExactAt F p z g) (e' : M.ExactAt F p z' g')
    (I : Finset (Fin N)) : minorIJ g' I (stepCols N j p.2) = c k * minorIJ g I (stepCols N j p.2) := by
  refine Ind.minor_eq_of_plk M hb hF hG hk hg' hg (fun m => ?_) I
  have a := e.2 k hk m
  have a' := e'.2 k hk m
  rw [hz] at a
  rw [hzb] at a'
  simp only [plk]
  rw [← a, ← a', hz']

theorem val_ups_ne (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} {bp : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hb : bp ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal bp)) {p : Ψ × Fin N} (hp : M.blk p = none) :
    valAt M.x (F.υ p) bp ≠ 0 := by
  obtain ⟨h0, r1, r2⟩ := hG.2.2 p hp
  have e := (reg_mul hb r1 r2).2
  rw [mul_inv_cancel₀ h0] at e
  have e1 : valAt M.x (1 : M.Ω) bp = 1 := map_one (regVal M.x hb)
  rw [e1] at e
  exact left_ne_zero_of_mul (e ▸ one_ne_zero)

end Lines

section Scal

variable {N j : ℕ}

theorem minor_one (S : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) S S = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.submatrix_one _ (S.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem exists_minor_ne (hj : j ≤ N) (i : Fin N) {h : Matrix (Fin N) (Fin N) ℂ} (hd : h.det ≠ 0) :
    ∃ I, minorIJ h I (stepCols N j i) ≠ 0 := by
  by_contra hc
  push_neg at hc
  have e := (GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j i hj).1 h⁻¹ h (stepCols N j i) (stepCols N j i)
  rw [Matrix.nonsing_inv_mul _ hd.isUnit, minor_one, Finset.sum_eq_zero fun I _ => by rw [hc I, mul_zero]] at e
  exact one_ne_zero e

theorem scal_eq (hj : j ≤ N) (i : Fin N) {h B : Matrix (Fin N) (Fin N) ℂ} (hd : h.det ≠ 0) (hB : IsBlockDiag j B)
    (hBt : B.BlockTriangular id) {c : ℂ}
    (e : ∀ I, minorIJ (h * B) I (stepCols N j i) = c * minorIJ h I (stepCols N j i)) :
    c = ∏ x ∈ stepCols N j i, B x x := by
  obtain ⟨I, hI⟩ := exists_minor_ne hj i hd
  have a := e I
  rw [(GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j i hj).2.2.1 h B I hB hBt] at a
  apply mul_right_cancel₀ hI
  rw [← a, mul_comm]

end Scal

section Main

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def wt (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (F : FrameData ι Ψ N M.Ω M.blk)
    (bp : (Σ k, baseIdx ι M.blk k) → ℂ) (g : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) : ℝ :=
  if IsProperStep N j i then 0 else Real.log ‖valAt M.x (F.υ (τ, i)) bp * Fib.facOf N j a g i‖

theorem normRhs_eq (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (F : FrameData ι Ψ N M.Ω M.blk)
    (z₀ z₁ : (Σ k, ι k) → ℂ) (h : Matrix (Fin N) (Fin N) ℂ) {t : ℂ} (ht : t ≠ 0)
    (hv : ∀ i, ¬ IsProperStep N j i → valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) ≠ 0)
    (hf : ∀ i, Fib.facOf N j a h i ≠ 0) :
    normRhs M τ a F z₀ z₁ h t = Real.log ‖t‖ + ∑ i, (xiCoef τ a (τ, i) : ℝ) *
      (wt M τ a F (basePart M.blk z₀) h i + (1 / 2) * (Real.log ((fsHerm ι (M.dy (τ, i))).h z₀) +
        Real.log ((fsHerm ι (M.dy (τ, i))).h z₁))) := by
  have hu : ∀ i, (if IsProperStep N j i then (1 : ℂ) else
      valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) * Fib.facOf N j a h i) ≠ 0 := fun i => by
    split_ifs with hp
    · exact one_ne_zero
    · exact mul_ne_zero (hv i hp) (hf i)
  have hn : ∀ i, ‖(if IsProperStep N j i then (1 : ℂ) else
      valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) * Fib.facOf N j a h i) ^ xiCoef τ a (τ, i)‖ ≠ 0 :=
    fun i => norm_ne_zero_iff.2 (zpow_ne_zero _ (hu i))
  have e1 : Real.log ‖t * ∏ i : Fin N, (if IsProperStep N j i then (1 : ℂ) else
      valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) * Fib.facOf N j a h i) ^ xiCoef τ a (τ, i)‖ =
      Real.log ‖t‖ + ∑ i, (xiCoef τ a (τ, i) : ℝ) * wt M τ a F (basePart M.blk z₀) h i := by
    rw [norm_mul, norm_prod, Real.log_mul (norm_ne_zero_iff.2 ht)
      (Finset.prod_ne_zero_iff.2 fun i _ => hn i), Real.log_prod fun i _ => hn i]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_zpow, Real.log_zpow]
    simp only [wt]
    split_ifs <;> simp
  have e2 : ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁)) =
      ∑ i, (xiCoef τ a (τ, i) : ℝ) * (Real.log ((fsHerm ι (M.dy (τ, i))).h z₀) +
        Real.log ((fsHerm ι (M.dy (τ, i))).h z₁)) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
    · intro τ' _ hne
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [xiCoef, hne]
    · simp
  unfold normRhs
  rw [e2]
  refine (congrArg₂ (· + ·) e1 rfl).trans ?_
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, add_assoc]
  congr 2
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

end Main

section Thm

theorem normRhs_same : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (F : FrameData ι Ψ N M.Ω M.blk) (z₀ z₁ z₀' z₁' : (Σ k, ι k) → ℂ) (h h' : Matrix (Fin N) (Fin N) ℂ) (t t' : ℂ), basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) → (∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) → (∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0) → basePart M.blk z₁ = basePart M.blk z₀ → M.IsFrame F → M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → SameOrbit z₀ z₀' → SameOrbit z₁ z₁' → IsBlockDiag j h → h.det ≠ 0 → IsBlockDiag j h' → h'.det ≠ 0 → t ≠ 0 → t' ≠ 0 → (∀ i, M.ExactAt F (τ, i) z₀ h) → (∀ i, M.ExactAt F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → (∀ i, M.ExactAt F (τ, i) z₀' h') → (∀ i, M.ExactAt F (τ, i) z₁' (h' * (1 + Matrix.single cb ca t'))) → normRhs M τ a F z₀ z₁ h t = normRhs M τ a F z₀' z₁' h' t' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a b k₀ ca cb hb hcase hk₀ hca hcb F z₀ z₁ z₀' z₁' h h' t t' hbp hn0 hn1 hb1 hF hG
    ho0 ho1 hh hd hh' hd' ht ht' e0 e1 e0' e1'
  have hj := M.j_le
  obtain ⟨c0, hc0, q0⟩ := orbit_symm ho0
  obtain ⟨c1, hc1, q1⟩ := orbit_symm ho1
  have ob0 := base_one M F q0 (e0 a).1 (e0' a).1
  have ob1 := base_one M F q1 (e1 a).1 (e1' a).1
  have bz0 : basePart M.blk z₀' = basePart M.blk z₀ := base_eq q0 ob0
  have bz1 : basePart M.blk z₁' = basePart M.blk z₀ := (base_eq q1 ob1).trans hb1
  have hT := transv_blockDiag (a := a) (b := b) (ca := ca) (cb := cb) hj hb hcase hca hcb
  have m0 : ∀ i k, M.blk (τ, i) = some k → ∀ I, minorIJ h' I (stepCols N j i) = c0 k * minorIJ h I (stepCols N j i) :=
    fun i k hk I => minors_prop M hbp hF hG hk q0 rfl bz0 hh hh' (e0 i) (e0' i) I
  have m1 : ∀ i k, M.blk (τ, i) = some k → ∀ I, minorIJ (h' * (1 + Matrix.single cb ca t')) I (stepCols N j i) =
      c1 k * minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j i) :=
    fun i k hk I => minors_prop M hbp hF hG hk q1 hb1 bz1 (hh.mul (hT t)) (hh'.mul (hT t')) (e1 i) (e1' i) I
  have hsome : ∀ i, IsProperStep N j i → ∃ k, M.blk (τ, i) = some k := fun i hi =>
    Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hi
  have tri : (h⁻¹ * h').BlockTriangular id := GlobalTheory.T.block_triangular_of_proportional_minors N j h h' hj hh hh' hd hd' fun i hi => by
    obtain ⟨k, hk⟩ := hsome i hi
    exact ⟨c0 k, m0 i k hk⟩
  obtain ⟨B, hBd⟩ : ∃ B, B = h⁻¹ * h' := ⟨_, rfl⟩
  have hBt : B.BlockTriangular id := hBd ▸ tri
  have hBb : IsBlockDiag j B := hBd ▸ (hh.inv hd.isUnit).mul hh'
  have hhB : h' = h * B := by rw [hBd, Matrix.mul_nonsing_inv_cancel_left _ _ hd.isUnit]
  have hBdet : B.det ≠ 0 := fun e => hd' (by rw [hhB, Matrix.det_mul, e, mul_zero])
  have hdiag : ∀ c, B c c ≠ 0 := fun c => by
    rw [Matrix.det_of_upperTriangular hBt] at hBdet
    exact Finset.prod_ne_zero_iff.1 hBdet c (Finset.mem_univ c)
  have hΛ : ∀ S : Finset (Fin N), ∏ x ∈ S, B x x ≠ 0 := fun S => Finset.prod_ne_zero_iff.2 fun c _ => hdiag c
  have s0 : ∀ i k, M.blk (τ, i) = some k → c0 k = ∏ x ∈ stepCols N j i, B x x := fun i k hk =>
    scal_eq hj i hd hBb hBt fun I => by rw [← hhB]; exact m0 i k hk I
  have s1 : ∀ i k, M.blk (τ, i) = some k → i ≠ a → c1 k = ∏ x ∈ stepCols N j i, B x x := fun i k hk hi =>
    scal_eq hj i hd hBb hBt fun I => by
      have e := m1 i k hk I
      rw [GlobalTheory.T.elementary_twist_minor_other_steps N j a b ca cb hj hb hcase hca hcb h' t' i hi I,
        GlobalTheory.T.elementary_twist_minor_other_steps N j a b ca cb hj hb hcase hca hcb h t i hi I, hhB] at e
      exact e
  obtain ⟨-, p2⟩ := GlobalTheory.T.elementary_twist_minor_scalar N j a b ca cb hj hb hcase hca hcb h B t t' (c1 k₀) hd hBb hBt fun I => by
    rw [← hhB]; exact m1 a k₀ hk₀ I
  have hv : ∀ i, ¬ IsProperStep N j i → valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) ≠ 0 := fun i hi =>
    val_ups_ne M hbp hG ((M.blk_none _).2 hi)
  have hv' : ∀ i, ¬ IsProperStep N j i → valAt M.x (F.υ (τ, i)) (basePart M.blk z₀') ≠ 0 := by
    rw [bz0]; exact hv
  rw [normRhs_eq M τ a F z₀ z₁ h ht hv (fun i => fac_ne_zero hj i hh hd a),
    normRhs_eq M τ a F z₀' z₁' h' ht' hv' (fun i => fac_ne_zero hj i hh' hd' a), bz0]
  have f0 : ∀ i, Real.log ((fsHerm ι (M.dy (τ, i))).h z₀') = Real.log ((fsHerm ι (M.dy (τ, i))).h z₀) +
      ∑ k, (M.dy (τ, i) k : ℝ) * Real.log ‖c0 k‖ := fun i => by
    rw [q0]; exact log_fs_smul _ hc0 hn0
  have f1 : ∀ i, Real.log ((fsHerm ι (M.dy (τ, i))).h z₁') = Real.log ((fsHerm ι (M.dy (τ, i))).h z₁) +
      ∑ k, (M.dy (τ, i) k : ℝ) * Real.log ‖c1 k‖ := fun i => by
    rw [q1]; exact log_fs_smul _ hc1 hn1
  obtain ⟨D, hD⟩ : ∃ D : Fin N → ℝ, D = fun i => wt M τ a F (basePart M.blk z₀) h' i -
      wt M τ a F (basePart M.blk z₀) h i + (1 / 2) * (∑ k, (M.dy (τ, i) k : ℝ) * Real.log ‖c0 k‖ +
        ∑ k, (M.dy (τ, i) k : ℝ) * Real.log ‖c1 k‖) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = ∏ x ∈ (stepCols N j a).erase ca, B x x := ⟨_, rfl⟩
  have hβ0 : β ≠ 0 := hβ ▸ hΛ _
  have hproper : ∀ i, IsProperStep N j i → i ≠ a → D i = Real.log ‖∏ x ∈ stepCols N j i, B x x‖ := fun i hi hia => by
    obtain ⟨k, hk⟩ := hsome i hi
    rw [hD]
    simp only [wt, if_pos hi]
    rw [dy_sum_some M hk ob0, dy_sum_some M hk ob1, s0 i k hk, s1 i k hk hia]
    ring
  have hprev : ∀ a' : Fin N, (a' : ℕ) + 1 = a → D a' = Real.log ‖β‖ := fun a' ha' => by
    have hne : a' ≠ a := fun e => by rw [e] at ha'; omega
    by_cases hp : IsProperStep N j a'
    · rw [hproper a' hp hne, cols_prev hj hb hcase hca ha' hp, hβ]
    · obtain ⟨g1, g2⟩ := fac_prev (j := j) hb ha' hp h
      obtain ⟨g3, -⟩ := fac_prev (j := j) hb ha' hp h'
      have hbl := (M.blk_none (τ, a')).2 hp
      rw [hD]
      simp only [wt, if_neg hp]
      rw [dy_sum_none M hbl ob0, dy_sum_none M hbl ob1, g1, g3, hβ, cols_first hj hb hcase hca (Or.inr g2)]
      simp
  have hzero : (a : ℕ) = 0 → Real.log ‖β‖ = 0 := fun h0 => by
    rw [hβ, cols_first hj hb hcase hca (Or.inl h0)]
    simp
  obtain ⟨cn, hcbn, hcam⟩ := cols_next hj hb hcase hca hcb
  have hDb : D b = Real.log ‖∏ x ∈ stepCols N j b, B x x‖ := by
    have hne : b ≠ a := fun e => by rw [e] at hb; omega
    by_cases hp : IsProperStep N j b
    · exact hproper b hp hne
    · have hbl := (M.blk_none (τ, b)).2 hp
      have e : Fib.facOf N j a h' b = Fib.facOf N j a h b * ∏ x ∈ stepCols N j b, B x x := by
        rw [fac_next hj hb hcase hp, fac_next hj hb hcase hp, hhB]
        exact (GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j b hj).2.2.1 h B _ hBb hBt
      rw [hD]
      simp only [wt, if_neg hp]
      rw [dy_sum_none M hbl ob0, dy_sum_none M hbl ob1, e, ← mul_assoc, norm_mul _ (∏ x ∈ stepCols N j b, B x x),
        Real.log_mul (norm_ne_zero_iff.2 (mul_ne_zero (hv b hp) (fac_ne_zero hj b hh hd a)))
          (norm_ne_zero_iff.2 (hΛ _))]
      ring
  have hap : IsProperStep N j a := by
    by_contra hp
    have := (M.blk_none (τ, a)).2 hp
    rw [hk₀] at this
    exact absurd this (by simp)
  have hDa : 2 * D a = Real.log ‖∏ x ∈ stepCols N j a, B x x‖ + Real.log ‖c1 k₀‖ := by
    rw [hD]
    simp only [wt, if_pos hap]
    rw [dy_sum_some M hk₀ ob0, dy_sum_some M hk₀ ob1, s0 a k₀ hk₀]
    ring
  have key := xi_sum τ hb D (Real.log ‖β‖) hprev hzero
  have hlogs : Real.log ‖c1 k₀‖ + Real.log ‖t‖ = Real.log ‖β‖ + (Real.log ‖t'‖ + Real.log ‖B cb cb‖) := by
    rw [← Real.log_mul (norm_ne_zero_iff.2 (hc1 k₀)) (norm_ne_zero_iff.2 ht),
      ← Real.log_mul (norm_ne_zero_iff.2 ht') (norm_ne_zero_iff.2 (hdiag cb)),
      ← Real.log_mul (norm_ne_zero_iff.2 hβ0) (mul_ne_zero (norm_ne_zero_iff.2 ht') (norm_ne_zero_iff.2 (hdiag cb))),
      ← norm_mul, ← norm_mul, ← norm_mul, p2, hβ]
  have hDb' : D b = Real.log ‖∏ x ∈ stepCols N j a, B x x‖ + Real.log ‖B cb cb‖ := by
    rw [hDb, cn, Finset.prod_insert hcbn, norm_mul, mul_comm,
      Real.log_mul (norm_ne_zero_iff.2 (hΛ _)) (norm_ne_zero_iff.2 (hdiag cb))]
  have hsum : ∑ i, (xiCoef τ a (τ, i) : ℝ) * D i = Real.log ‖t‖ - Real.log ‖t'‖ := by
    rw [key, hDb', hDa]
    linarith
  have hsplit : ∑ i, (xiCoef τ a (τ, i) : ℝ) * (wt M τ a F (basePart M.blk z₀) h' i +
      (1 / 2) * (Real.log ((fsHerm ι (M.dy (τ, i))).h z₀') + Real.log ((fsHerm ι (M.dy (τ, i))).h z₁'))) =
      ∑ i, (xiCoef τ a (τ, i) : ℝ) * (wt M τ a F (basePart M.blk z₀) h i +
        (1 / 2) * (Real.log ((fsHerm ι (M.dy (τ, i))).h z₀) + Real.log ((fsHerm ι (M.dy (τ, i))).h z₁))) +
      ∑ i, (xiCoef τ a (τ, i) : ℝ) * D i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [f0 i, f1 i, hD]
    ring
  rw [hsplit, hsum]
  ring

end Thm

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Same
end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_orbit_comparison : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (F : FrameData ι Ψ N M.Ω M.blk) (z₀ z₁ z₀' z₁' : (Σ k, ι k) → ℂ) (h h' : Matrix (Fin N) (Fin N) ℂ) (t t' : ℂ), basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) → (∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) → (∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0) → basePart M.blk z₁ = basePart M.blk z₀ → M.IsFrame F → M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → SameOrbit z₀ z₀' → SameOrbit z₁ z₁' → IsBlockDiag j h → h.det ≠ 0 → IsBlockDiag j h' → h'.det ≠ 0 → t ≠ 0 → t' ≠ 0 → (∀ i, M.ExactAt F (τ, i) z₀ h) → (∀ i, M.ExactAt F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → (∀ i, M.ExactAt F (τ, i) z₀' h') → (∀ i, M.ExactAt F (τ, i) z₁' (h' * (1 + Matrix.single cb ca t'))) → normRhs M τ a F z₀ z₁ h t = normRhs M τ a F z₀' z₁' h' t' := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Same.normRhs_same
end

section
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Indep

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem basePart_orbit {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem orbit_ne {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z' z) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  intro k
  obtain ⟨i, hi⟩ := hz k
  exact ⟨i, mul_ne_zero (hc k) hi⟩

theorem eq_of_orbit_of_normalised {u v : (Σ k, ι k) → ℂ} (h : SameOrbit u v) (e : ∀ k, ι k)
    (hu : ∀ k, u ⟨k, e k⟩ = 1) (hv : ∀ k, v ⟨k, e k⟩ = 1) : u = v := by
  obtain ⟨c, hc, rfl⟩ := h
  have h1 : ∀ k, c k = 1 := fun k => by
    have h2 : c k * v ⟨k, e k⟩ = 1 := hu k
    rwa [hv k, mul_one] at h2
  funext p
  show c p.1 * v p = v p
  rw [h1 p.1, one_mul]

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem base_of_orbit (M : FlagModel y Ψ N j) {z z' : (Σ k, ι k) → ℂ} (ho : SameOrbit z z')
    (hz : basePart M.blk z ∈ mcPts (mCoordIdeal M.x)) :
    mCoordIdeal (basePart M.blk z') = mCoordIdeal (basePart M.blk z) ∧
      basePart M.blk z' ∈ mcPts (mCoordIdeal M.x) := by
  obtain ⟨c, hc, rfl⟩ := GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm ho
  have h := GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x (basePart M.blk z)
    (fun k => c k.1) (fun k => hc k.1)
  exact ⟨h.1, (h.2 hz).1⟩

theorem normRhs_indep : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (F F' : FrameData ι Ψ N M.Ω M.blk) (z₀ z₁ z₀' z₁' : (Σ k, ι k) → ℂ) (h h' : Matrix (Fin N) (Fin N) ℂ) (t t' : ℂ), basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) → (∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) → (∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0) → basePart M.blk z₁ = basePart M.blk z₀ → M.IsFrame F → M.IsFrame F' → M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → M.GoodAt F' (mCoordIdeal (basePart M.blk z₀')) → SameOrbit z₀ z₀' → SameOrbit z₁ z₁' → IsBlockDiag j h → h.det ≠ 0 → IsBlockDiag j h' → h'.det ≠ 0 → t ≠ 0 → t' ≠ 0 → (∀ i, M.ExactAt F (τ, i) z₀ h) → (∀ i, M.ExactAt F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → (∀ i, M.ExactAt F' (τ, i) z₀' h') → (∀ i, M.ExactAt F' (τ, i) z₁' (h' * (1 + Matrix.single cb ca t'))) → normRhs M τ a F z₀ z₁ h t = normRhs M τ a F' z₀' z₁' h' t' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a b k₀ ca cb hab hstep hblk hca hcb F F' z₀ z₁ z₀' z₁' h h' t t' hmc hn₀ hn₁ hbase
    hF hF' hG hG' ho₀ ho₁ hh hd hh' hd' ht ht' hE₀ hE₁ hE₀' hE₁'
  obtain ⟨hid, hmc'⟩ := base_of_orbit M ho₀ hmc
  have hn₀' := orbit_ne (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm ho₀) hn₀
  have hn₁' := orbit_ne (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm ho₁) hn₁
  have hbase' : basePart M.blk z₁' = basePart M.blk z₀' := by
    have h1 : SameOrbit (basePart M.blk z₁') (basePart M.blk z₁) :=
      basePart_orbit M.blk (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm ho₁)
    rw [hbase] at h1
    exact eq_of_orbit_of_normalised
      (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_trans h1 (basePart_orbit M.blk ho₀)) F'.c (hE₁' a).1 (hE₀' a).1
  obtain ⟨w₀, w₁, S, hw₀, hw₁, hS, hSd, hX₀, hX₁, hnorm⟩ :=
    GlobalTheory.T.flag_adjacent_frame_comparison K ι Φ y Ψ N j M τ a b k₀ ca cb hab hstep hblk hca hcb F F' z₀' z₁' h' t' hmc' hn₀' hn₁' hbase'
      hF hF' (by rw [hid]; exact hG) hG' hh' hd' ht' hE₀' hE₁'
  rw [← hnorm]
  exact GlobalTheory.T.flag_adjacent_orbit_comparison K ι Φ y Ψ N j M τ a b k₀ ca cb hab hstep hblk hca hcb F z₀ z₁ w₀ w₁ h (S * h') t t' hmc hn₀ hn₁
    hbase hF hG (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_trans ho₀ (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm hw₀))
    (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_trans ho₁ (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm hw₁)) hh hd (hS.mul hh')
    (by rw [Matrix.det_mul]; exact mul_ne_zero hSd hd') ht ht' hE₀ hE₁ hX₀ hX₁

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Indep
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_two_frames_orbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (F F' : FrameData ι Ψ N M.Ω M.blk) (z₀ z₁ z₀' z₁' : (Σ k, ι k) → ℂ) (h h' : Matrix (Fin N) (Fin N) ℂ) (t t' : ℂ), basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) → (∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) → (∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0) → basePart M.blk z₁ = basePart M.blk z₀ → M.IsFrame F → M.IsFrame F' → M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → M.GoodAt F' (mCoordIdeal (basePart M.blk z₀')) → SameOrbit z₀ z₀' → SameOrbit z₁ z₁' → IsBlockDiag j h → h.det ≠ 0 → IsBlockDiag j h' → h'.det ≠ 0 → t ≠ 0 → t' ≠ 0 → (∀ i, M.ExactAt F (τ, i) z₀ h) → (∀ i, M.ExactAt F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → (∀ i, M.ExactAt F' (τ, i) z₀' h') → (∀ i, M.ExactAt F' (τ, i) z₁' (h' * (1 + Matrix.single cb ca t'))) → normRhs M τ a F z₀ z₁ h t = normRhs M τ a F' z₀' z₁' h' t' := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Indep.normRhs_indep
end

section
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LForm

section Holo

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem holoOn_congr' {V : Set X} {f g : X → ℂ} (hV : IsOpen V) (h : A.HoloOn V f)
    (hfg : ∀ w ∈ V, g w = f w) : A.HoloOn V g := fun j =>
  (h j).congr ((A.chart j).isOpen_inter_preimage_symm hV) fun u hu => (hfg _ hu.2).symm

theorem holoOn_mono' {U V : Set X} {g : X → ℂ} (h : A.HoloOn U g) (hVU : V ⊆ U) : A.HoloOn V g :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hVU))

theorem holoOn_mul' {U : Set X} {f g : X → ℂ} (hf : A.HoloOn U f) (hg : A.HoloOn U g) :
    A.HoloOn U fun x => f x * g x :=
  fun j z hz => (hf j z hz).mul (hg j z hz)

theorem holoOn_add' {U : Set X} {f g : X → ℂ} (hf : A.HoloOn U f) (hg : A.HoloOn U g) :
    A.HoloOn U fun x => f x + g x :=
  fun j z hz => (hf j z hz).add (hg j z hz)

theorem holoOn_const' (V : Set X) (c : ℂ) : A.HoloOn V fun _ => c := fun _ _ _ => analyticAt_const

theorem holoOn_sum' {σ : Type} (s : Finset σ) {V : Set X} {f : σ → X → ℂ} (h : ∀ a, A.HoloOn V (f a)) :
    A.HoloOn V fun y => ∑ a ∈ s, f a y := fun k z hz =>
  Finset.analyticAt_fun_sum s fun a _ => h a k z hz

theorem holoOn_prod' {σ : Type} (s : Finset σ) {V : Set X} {f : σ → X → ℂ} (h : ∀ a, A.HoloOn V (f a)) :
    A.HoloOn V fun y => ∏ a ∈ s, f a y := fun k z hz =>
  Finset.analyticAt_fun_prod s fun a _ => h a k z hz

theorem holoOn_minor' {N : ℕ} {V : Set X} {m : X → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ a b, A.HoloOn V fun y => m y a b) (I J : Finset (Fin N)) :
    A.HoloOn V fun y => minorIJ (m y) I J := by
  unfold minorIJ
  by_cases e : I.card = J.card
  · simp only [dif_pos e, Matrix.det_apply']
    exact holoOn_sum' _ fun s => holoOn_mul' (holoOn_const' _ _) (holoOn_prod' _ fun a => h _ _)
  · simp only [dif_neg e]
    exact holoOn_const' _ _

theorem holoOn_of_chart {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : IsCompatChart A ψ)
    {g : (Fin e → ℂ) → ℂ} (hg : AnalyticOnNhd ℂ g ψ.target) : A.HoloOn ψ.source fun w => g (ψ w) :=
  fun j u hu => AnalyticAt.comp (g := g) (f := ψ ∘ (A.chart j).symm) (hg _ (ψ.map_source hu.2)) ((hψ j).1 u hu)

theorem holoOn_transv {N : ℕ} {V : Set X} {h : X → Matrix (Fin N) (Fin N) ℂ} {t : X → ℂ}
    (hh : ∀ a b, A.HoloOn V fun y => h y a b) (ht : A.HoloOn V t) (cb ca : Fin N) (a b : Fin N) :
    A.HoloOn V fun y => (h y * (1 + Matrix.single cb ca (t y))) a b := by
  simp only [Matrix.mul_apply]
  refine holoOn_sum' _ fun c => holoOn_mul' (hh _ _) ?_
  simp only [Matrix.add_apply, Matrix.single_apply]
  refine holoOn_add' (holoOn_const' _ _) ?_
  by_cases e : cb = c ∧ ca = b
  · simpa only [if_pos e] using ht
  · simpa only [if_neg e] using holoOn_const' V 0

end Holo

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem lift_fst {k₀ : K} {L' L : (Σ o : Option K, ι (o.getD k₀)) → ℂ} {z : (Σ k, ι k) → ℂ}
    (hz : SameOrbit z (fstPt k₀ L)) (hL : SameOrbit L' L) :
    ∃ b : K → ℂ, (∀ k, b k ≠ 0) ∧ ∀ q : Σ k, ι k, L' ⟨some q.1, q.2⟩ = b q.1 * z q := by
  obtain ⟨c, hc, rfl⟩ := hz
  obtain ⟨d, hd, rfl⟩ := hL
  refine ⟨fun k => d (some k) * (c k)⁻¹, fun k => mul_ne_zero (hd _) (inv_ne_zero (hc k)), fun q => ?_⟩
  have hq : c q.1 ≠ 0 := hc q.1
  show d (some q.1) * L ⟨some q.1, q.2⟩ = d (some q.1) * (c q.1)⁻¹ * (c q.1 * L ⟨some q.1, q.2⟩)
  field_simp

theorem lift_snd {k₀ : K} {L' L : (Σ o : Option K, ι (o.getD k₀)) → ℂ} {z : (Σ k, ι k) → ℂ}
    (hz : SameOrbit z (sndPt k₀ L)) (hL : SameOrbit L' L) :
    ∃ b : ℂ, b ≠ 0 ∧ ∀ m : ι k₀, L' ⟨none, m⟩ = b * z ⟨k₀, m⟩ := by
  obtain ⟨c, hc, rfl⟩ := hz
  obtain ⟨d, hd, rfl⟩ := hL
  refine ⟨d none * (c k₀)⁻¹, mul_ne_zero (hd _) (inv_ne_zero (hc k₀)), fun m => ?_⟩
  have hq : c k₀ ≠ 0 := hc k₀
  show d none * L ⟨none, m⟩ = d none * (c k₀)⁻¹ * (c k₀ * L (v₁ k₀ ⟨k₀, m⟩))
  rw [v₁_self]
  field_simp

theorem basePart_orbit' {σ : Type} {blk : σ → Option K} {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem eq_of_orbit_normal {κ : Type} {ρ : κ → Type} {z z' : (Σ k, ρ k) → ℂ} (h : SameOrbit z z')
    (c₀ : ∀ k, ρ k) (h₁ : ∀ k, z ⟨k, c₀ k⟩ = 1) (h₂ : ∀ k, z' ⟨k, c₀ k⟩ = 1) : z = z' := by
  obtain ⟨c, hc, rfl⟩ := h
  have hc1 : ∀ k, c k = 1 := fun k => by
    have := h₁ k
    simp only [h₂ k, mul_one] at this
    exact this
  funext q
  simp only [hc1, one_mul]

end Orbit

theorem holoOn_step {N e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {V : Set X} (hV : IsOpen V)
    {S : Finset (Fin N)} {f : X → ℂ} {v : Finset (Fin N) → X → ℂ} {h : X → Matrix (Fin N) (Fin N) ℂ}
    (hv : ∀ I, A.HoloOn V (v I)) (hh : ∀ a b, A.HoloOn V fun y => h y a b)
    (hf : ∀ w ∈ V, f w = ∑ I, v I w * minorIJ (h w) I S) : A.HoloOn V f :=
  holoOn_congr' hV (holoOn_sum' _ fun I => holoOn_mul' (hv I) (holoOn_minor' hh I S)) hf

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ (x : RW.X) (ψ : OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e) (i₀ : Fin e) (F : FrameData ι Ψ N M.Ω M.blk) (H : Ψ → (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ), x ∈ ψ.source → IsWChart M Rb τ a k₀ ca cb RW pr ψ kb σ i₀ F H → ∃ (V : Set RW.X) (z₀ z₁ : RW.X → (Σ k, ι k) → ℂ) (c : Option K → RW.X → ℂ), IsOpen V ∧ x ∈ V ∧ V ⊆ ψ.source ∧ V ⊆ RW.U x ∧ (∀ q, RW.A.HoloOn V fun w => z₀ w q) ∧ (∀ o, RW.A.HoloOn V (c o)) ∧ (∀ o, ∀ w ∈ V, c o w ≠ 0) ∧ ∀ w ∈ V, SameOrbit (z₀ w) (fstPt k₀ (RW.lift w w)) ∧ SameOrbit (z₁ w) (sndPt k₀ (RW.lift w w)) ∧ (∀ τ' i, M.ExactAt F (τ', i) (z₀ w) (H τ' (ψ w)) ∧ M.ExactAt F (τ', i) (z₁ w) (if τ' = τ then H τ (ψ w) * (1 + Matrix.single cb ca (ψ w i₀)) else H τ' (ψ w))) ∧ (∀ q : Σ k, ι k, q.1 ≠ k₀ → z₁ w q = z₀ w q) ∧ (∀ q : Σ k, ι k, RW.lift x w ⟨some q.1, q.2⟩ = c (some q.1) w * z₀ w q) ∧ ∀ m : ι k₀, RW.lift x w ⟨none, m⟩ = c none w * z₁ w ⟨k₀, m⟩ := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a b k₀ ca cb hb hab hk hca hcb RW pr hA x ψ kb σ i₀ F H hx hw
  obtain ⟨hcc, hfr, -, -, hHan, hpts⟩ := hw
  have hex : ∀ w, ∃ z₀ z₁ : (Σ k, ι k) → ℂ, w ∈ ψ.source →
      SameOrbit z₀ (fstPt k₀ (RW.lift w w)) ∧ SameOrbit z₁ (sndPt k₀ (RW.lift w w)) ∧
        ∀ τ' i, M.ExactAt F (τ', i) z₀ (H τ' (ψ w)) ∧
          M.ExactAt F (τ', i) z₁
            (if τ' = τ then H τ (ψ w) * (1 + Matrix.single cb ca (ψ w i₀)) else H τ' (ψ w)) := fun w => by
    by_cases hwS : w ∈ ψ.source
    · obtain ⟨-, -, z₀, z₁, h⟩ := hpts w hwS
      exact ⟨z₀, z₁, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hwS⟩
  choose z₀ z₁ hz using hex
  have hpb := fun w (hwS : w ∈ ψ.source) => GlobalTheory.T.twisted_atlas_compatibility K ι Φ y Ψ N j M n e Rb τ a k₀ ca cb RW pr hk hA w
    (z₀ w) (z₁ w) (hz w hwS).1 (hz w hwS).2.1
  have hn₀ : ∀ w ∈ ψ.source, ∀ k, basePart M.blk (z₀ w) ⟨k, F.c k⟩ = 1 := fun w hwS =>
    ((hz w hwS).2.2 τ a).1.1
  have hn₁ : ∀ w ∈ ψ.source, ∀ k, basePart M.blk (z₁ w) ⟨k, F.c k⟩ = 1 := fun w hwS =>
    ((hz w hwS).2.2 τ a).2.1
  have hbeq : ∀ w ∈ ψ.source, basePart M.blk (z₁ w) = basePart M.blk (z₀ w) := fun w hwS =>
    eq_of_orbit_normal (hpb w hwS).2.1 F.c (hn₁ w hwS) (hn₀ w hwS)
  obtain ⟨W, hWdef⟩ : ∃ W, W = ψ.source ∩ RW.U x := ⟨_, rfl⟩
  have hWo : IsOpen W := hWdef ▸ ψ.open_source.inter (RW.isOpen_U x)
  have hxW : x ∈ W := hWdef ▸ ⟨hx, RW.mem_U x⟩
  have hWS : W ⊆ ψ.source := hWdef ▸ Set.inter_subset_left
  have hWU : W ⊆ RW.U x := hWdef ▸ Set.inter_subset_right
  have hlift : ∀ w ∈ W, SameOrbit (RW.lift x w) (RW.lift w w) := fun w hwW =>
    RW.compat x w w ⟨hWU hwW, RW.mem_U w⟩
  have hb₀ := fun w (hwW : w ∈ W) => lift_fst (hz w (hWS hwW)).1 (hlift w hwW)
  have hb₁ := fun w (hwW : w ∈ W) => lift_snd (hz w (hWS hwW)).2.1 (hlift w hwW)
  have hbase : ∀ (k : NonPluckerBlocks M.blk) (m : ι k.1), RW.A.HoloOn W fun w => z₀ w ⟨k.1, m⟩ := fun k m => by
    refine StepW.ValHolo.holoOn_div_congr RW.A hWo (f := fun w => RW.lift x w ⟨some k.1, m⟩)
      (g := fun w => RW.lift x w ⟨some k.1, F.c k⟩) (holoOn_mono' (RW.holo x _) hWU)
      (holoOn_mono' (RW.holo x _) hWU) ?_ ?_
    · intro w hwW
      obtain ⟨d, hd, hq⟩ := hb₀ w hwW
      have h1 := hq ⟨k.1, F.c k⟩
      have h2 : z₀ w ⟨k.1, F.c k⟩ = 1 := hn₀ w (hWS hwW) k
      rw [h2, mul_one] at h1
      exact h1 ▸ hd k.1
    · intro w hwW
      obtain ⟨d, hd, hq⟩ := hb₀ w hwW
      have h1 := hq ⟨k.1, F.c k⟩
      have h2 : z₀ w ⟨k.1, F.c k⟩ = 1 := hn₀ w (hWS hwW) k
      rw [h2, mul_one] at h1
      have h3 := hq ⟨k.1, m⟩
      show z₀ w ⟨k.1, m⟩ = RW.lift x w ⟨some k.1, m⟩ / RW.lift x w ⟨some k.1, F.c k⟩
      rw [h3, h1, mul_div_cancel_left₀ _ (hd k.1)]
  have hbH : ∀ q, RW.A.HoloOn W fun w => basePart M.blk (z₀ w) q := fun q => hbase q.1 q.2
  have hid : mCoordIdeal (basePart M.blk (z₀ x)) = mCoordIdeal (basePart M.blk (fstPt k₀ (RW.lift x x))) := by
    obtain ⟨c, hc, hce⟩ := basePart_orbit' (blk := M.blk) (hz x hx).1
    rw [hce]
    exact StepW.TorusAct.mCoordIdeal_torus c hc _
  have hreg : ∀ q I, RegAt M.x (mCoordIdeal (basePart M.blk (z₀ x))) (F.u q I) := fun q I => by
    rw [hid]
    exact ((hpts x hx).2.1.2.1 q I).1
  have hval := fun q I => StepW.ValHolo.holoOn_valAt _ _ _ M.x (F.u q I) e RW.X RW.A W
    (fun w => basePart M.blk (z₀ w)) x hWo hxW hbH (fun w hwW => (hpb w (hWS hwW)).1) (hreg q I)
  choose Wv hWv₁ hWv₂ hWv₃ hWv₄ using hval
  obtain ⟨V₁, hV₁def⟩ : ∃ V₁, V₁ = W ∩ ⋂ q, ⋂ I, Wv q I := ⟨_, rfl⟩
  have hV₁o : IsOpen V₁ := hV₁def ▸ hWo.inter
    (isOpen_iInter_of_finite fun q => isOpen_iInter_of_finite fun I => hWv₁ q I)
  have hxV₁ : x ∈ V₁ := hV₁def ▸ ⟨hxW, Set.mem_iInter.2 fun q => Set.mem_iInter.2 fun I => hWv₂ q I⟩
  have hV₁W : V₁ ⊆ W := hV₁def ▸ Set.inter_subset_left
  have hV₁S : V₁ ⊆ ψ.source := hV₁W.trans hWS
  have hvV : ∀ q I, RW.A.HoloOn V₁ fun w => valAt M.x (F.u q I) (basePart M.blk (z₀ w)) := fun q I =>
    holoOn_mono' (hWv₄ q I) fun w hwV => by
      rw [hV₁def] at hwV
      exact Set.mem_iInter.1 (Set.mem_iInter.1 hwV.2 q) I
  have hHH : ∀ τ' r s, RW.A.HoloOn ψ.source fun w => H τ' (ψ w) r s := fun τ' r s =>
    holoOn_of_chart hcc (hHan τ' r s)
  have hti : RW.A.HoloOn ψ.source fun w => ψ w i₀ := holoOn_of_chart hcc (g := fun v => v i₀)
    fun v _ => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) i₀).analyticAt v
  have hzH : ∀ q, RW.A.HoloOn V₁ fun w => z₀ w q := fun q => by
    by_cases hq : ∀ p, M.blk p ≠ some q.1
    · exact holoOn_mono' (hbase ⟨q.1, hq⟩ q.2) hV₁W
    · push_neg at hq
      obtain ⟨⟨τ', i⟩, hp⟩ := hq
      exact holoOn_step hV₁o (v := fun I w => valAt M.x (F.u q I) (basePart M.blk (z₀ w)))
        (h := fun w => H τ' (ψ w)) (S := stepCols N j i) (fun I => hvV q I)
        (fun r s => holoOn_mono' (hHH τ' r s) hV₁S)
        fun w hwV => ((hz w (hV₁S hwV)).2.2 τ' i).1.2 q.1 hp q.2
  have hz₁H : ∀ m : ι k₀, RW.A.HoloOn V₁ fun w => z₁ w ⟨k₀, m⟩ := fun m => by
    refine holoOn_step hV₁o (v := fun I w => valAt M.x (F.u ⟨k₀, m⟩ I) (basePart M.blk (z₀ w)))
      (h := fun w => H τ (ψ w) * (1 + Matrix.single cb ca (ψ w i₀))) (S := stepCols N j a)
      (fun I => hvV _ I)
      (fun r s => holoOn_transv (fun r s => holoOn_mono' (hHH τ r s) hV₁S) (holoOn_mono' hti hV₁S) cb ca r s)
      fun w hwV => ?_
    have h1 := ((hz w (hV₁S hwV)).2.2 τ a).2.2 k₀ hk m
    rw [if_pos rfl, hbeq w (hV₁S hwV)] at h1
    exact h1
  choose mk hmk using (hpb x hx).2.2.1
  obtain ⟨m₁, hm₁⟩ := (hpb x hx).2.2.2 k₀
  obtain ⟨V, hVdef⟩ : ∃ V, V = (⋂ k, (V₁ ∩ {w | z₀ w ⟨k, mk k⟩ ≠ 0})) ∩ (V₁ ∩ {w | z₁ w ⟨k₀, m₁⟩ ≠ 0}) :=
    ⟨_, rfl⟩
  have hVo : IsOpen V := hVdef ▸ (isOpen_iInter_of_finite fun k =>
    StepW.ValHolo.isOpen_inter_ne RW.A hV₁o (hzH ⟨k, mk k⟩)).inter
      (StepW.ValHolo.isOpen_inter_ne RW.A hV₁o (hz₁H m₁))
  have hxV : x ∈ V := hVdef ▸ ⟨Set.mem_iInter.2 fun k => ⟨hxV₁, hmk k⟩, hxV₁, hm₁⟩
  have hVV₁ : V ⊆ V₁ := fun w hwV => by
    rw [hVdef] at hwV
    exact hwV.2.1
  have hV0 : ∀ w ∈ V, ∀ k, z₀ w ⟨k, mk k⟩ ≠ 0 := fun w hwV k => by
    rw [hVdef] at hwV
    exact (Set.mem_iInter.1 hwV.1 k).2
  have hV1 : ∀ w ∈ V, z₁ w ⟨k₀, m₁⟩ ≠ 0 := fun w hwV => by
    rw [hVdef] at hwV
    exact hwV.2.2
  have hVW : V ⊆ W := hVV₁.trans hV₁W
  have hVS : V ⊆ ψ.source := hVW.trans hWS
  obtain ⟨c, hcs, hcn⟩ : ∃ c : Option K → RW.X → ℂ,
      (∀ k w, c (some k) w = RW.lift x w ⟨some k, mk k⟩ / z₀ w ⟨k, mk k⟩) ∧
        ∀ w, c none w = RW.lift x w ⟨none, m₁⟩ / z₁ w ⟨k₀, m₁⟩ :=
    ⟨fun o w => o.elim (RW.lift x w ⟨none, m₁⟩ / z₁ w ⟨k₀, m₁⟩)
      fun k => RW.lift x w ⟨some k, mk k⟩ / z₀ w ⟨k, mk k⟩, fun _ _ => rfl, fun _ => rfl⟩
  have hcs' : ∀ w ∈ V, ∀ (d : K → ℂ), (∀ q : Σ k, ι k, RW.lift x w ⟨some q.1, q.2⟩ = d q.1 * z₀ w q) →
      ∀ k, c (some k) w = d k := fun w hwV d hq k => by
    rw [hcs]
    have h1 := hq ⟨k, mk k⟩
    exact h1 ▸ mul_div_cancel_right₀ _ (hV0 w hwV k)
  have hcn' : ∀ w ∈ V, ∀ d : ℂ, (∀ m : ι k₀, RW.lift x w ⟨none, m⟩ = d * z₁ w ⟨k₀, m⟩) → c none w = d :=
    fun w hwV d hq => by
      rw [hcn, hq m₁]
      exact mul_div_cancel_right₀ _ (hV1 w hwV)
  refine ⟨V, z₀, z₁, c, hVo, hxV, hVS, hVW.trans hWU, fun q => holoOn_mono' (hzH q) hVV₁, ?_, ?_, ?_⟩
  · rintro (_ | k)
    · exact StepW.ValHolo.holoOn_div_congr RW.A hVo (holoOn_mono' (RW.holo x _) (hVW.trans hWU))
        (holoOn_mono' (hz₁H m₁) hVV₁) hV1 fun w _ => hcn w
    · exact StepW.ValHolo.holoOn_div_congr RW.A hVo (holoOn_mono' (RW.holo x _) (hVW.trans hWU))
        (holoOn_mono' (hzH ⟨k, mk k⟩) hVV₁) (fun w hwV => hV0 w hwV k) fun w _ => hcs k w
  · rintro (_ | k) w hwV
    · obtain ⟨d, hd, hq⟩ := hb₁ w (hVW hwV)
      rw [hcn' w hwV d hq]
      exact hd
    · obtain ⟨d, hd, hq⟩ := hb₀ w (hVW hwV)
      rw [hcs' w hwV d hq k]
      exact hd k
  · intro w hwV
    have hwS := hVS hwV
    refine ⟨(hz w hwS).1, (hz w hwS).2.1, (hz w hwS).2.2, fun q hq₀ => ?_, fun q => ?_, fun m => ?_⟩
    · by_cases hq : ∀ p, M.blk p ≠ some q.1
      · exact congrFun (hbeq w hwS) ⟨⟨q.1, hq⟩, q.2⟩
      · push_neg at hq
        obtain ⟨⟨τ', i⟩, hp⟩ := hq
        have e₀ := ((hz w hwS).2.2 τ' i).1.2 q.1 hp q.2
        have e₁ := ((hz w hwS).2.2 τ' i).2.2 q.1 hp q.2
        refine e₁.trans (Eq.trans ?_ e₀.symm)
        rw [hbeq w hwS]
        refine Finset.sum_congr rfl fun I _ => ?_
        congr 1
        by_cases ht : τ' = τ
        · subst ht
          rw [if_pos rfl]
          have hia : i ≠ a := fun hia => hq₀ (by
            subst hia
            exact Option.some_injective _ (hp.symm.trans hk))
          exact GlobalTheory.T.elementary_twist_minor_other_steps N j a b ca cb M.j_le hb hab hca hcb _ _ i hia I
        · rw [if_neg ht]
    · obtain ⟨d, hd, hq'⟩ := hb₀ w (hVW hwV)
      rw [hcs' w hwV d hq' q.1]
      exact hq' q
    · obtain ⟨d, hd, hq'⟩ := hb₁ w (hVW hwV)
      rw [hcn' w hwV d hq']
      exact hq' m

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LForm
end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_twisted_resolution_alt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ (x : RW.X) (ψ : OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e) (i₀ : Fin e) (F : FrameData ι Ψ N M.Ω M.blk) (H : Ψ → (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ), x ∈ ψ.source → IsWChart M Rb τ a k₀ ca cb RW pr ψ kb σ i₀ F H → ∃ (V : Set RW.X) (z₀ z₁ : RW.X → (Σ k, ι k) → ℂ) (c : Option K → RW.X → ℂ), IsOpen V ∧ x ∈ V ∧ V ⊆ ψ.source ∧ V ⊆ RW.U x ∧ (∀ q, RW.A.HoloOn V fun w => z₀ w q) ∧ (∀ o, RW.A.HoloOn V (c o)) ∧ (∀ o, ∀ w ∈ V, c o w ≠ 0) ∧ ∀ w ∈ V, SameOrbit (z₀ w) (fstPt k₀ (RW.lift w w)) ∧ SameOrbit (z₁ w) (sndPt k₀ (RW.lift w w)) ∧ (∀ τ' i, M.ExactAt F (τ', i) (z₀ w) (H τ' (ψ w)) ∧ M.ExactAt F (τ', i) (z₁ w) (if τ' = τ then H τ (ψ w) * (1 + Matrix.single cb ca (ψ w i₀)) else H τ' (ψ w))) ∧ (∀ q : Σ k, ι k, q.1 ≠ k₀ → z₁ w q = z₀ w q) ∧ (∀ q : Σ k, ι k, RW.lift x w ⟨some q.1, q.2⟩ = c (some q.1) w * z₀ w q) ∧ ∀ m : ι k₀, RW.lift x w ⟨none, m⟩ = c none w * z₁ w ⟨k₀, m⟩ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LForm.main
end

section
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LocGen

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem holoOn_mul_prod_zpow {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {U : Set X} {κ : Type}
    [Fintype κ] {f : X → ℂ} {c : κ → X → ℂ} (d : κ → ℤ) (hf : A.HoloOn U f) (hc : ∀ k, A.HoloOn U (c k))
    (h0 : ∀ k, ∀ y ∈ U, c k y ≠ 0) : A.HoloOn U fun y => f y * ∏ k, c k y ^ d k := by
  intro j z hz
  have h1 : AnalyticAt ℂ (fun v => ∏ k, ((c k ∘ (A.chart j).symm) v) ^ d k) z :=
    Finset.analyticAt_fun_prod _ fun k _ => (hc k j z hz).zpow (h0 k _ hz.2)
  exact (hf j z hz).mul h1

theorem holoOn_comp_chart {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : IsCompatChart A ψ) {g : (Fin e → ℂ) → ℂ}
    (hg : AnalyticOnNhd ℂ g ψ.target) {V : Set X} (hV : V ⊆ ψ.source) : A.HoloOn V fun w => g (ψ w) := by
  intro j z hz
  have hs : (A.chart j).symm z ∈ ψ.source := hV hz.2
  have h1 : AnalyticAt ℂ (g ∘ (ψ ∘ (A.chart j).symm)) z :=
    AnalyticAt.comp (g := g) (f := ψ ∘ (A.chart j).symm) (hg _ (ψ.map_source hs)) ((hψ j).1 z ⟨hz.1, hs⟩)
  exact h1

def mixPt (k₀ : K) (z₀ z₁ : (Σ k, ι k) → ℂ) : (Σ o : Option K, ι (o.getD k₀)) → ℂ := fun p =>
  match p with
  | ⟨some k, m⟩ => z₀ ⟨k, m⟩
  | ⟨none, m⟩ => z₁ ⟨k₀, m⟩

theorem fstPt_mixPt (k₀ : K) (z₀ z₁ : (Σ k, ι k) → ℂ) : fstPt k₀ (mixPt k₀ z₀ z₁) = z₀ := by
  funext q
  obtain ⟨k, m⟩ := q
  rfl

theorem sndPt_mixPt {k₀ : K} {z₀ z₁ : (Σ k, ι k) → ℂ} (h : ∀ q : Σ k, ι k, q.1 ≠ k₀ → z₁ q = z₀ q) :
    sndPt k₀ (mixPt k₀ z₀ z₁) = z₁ := by
  funext q
  obtain ⟨k, m⟩ := q
  by_cases e : k = k₀
  · subst e
    change mixPt k z₀ z₁ (v₁ k ⟨k, m⟩) = _
    rw [v₁_self]
    rfl
  · change mixPt k₀ z₀ z₁ (v₁ k₀ ⟨k, m⟩) = _
    rw [v₁_ne (p := ⟨k, m⟩) e]
    exact (h ⟨k, m⟩ e).symm

theorem mixPt_blocks {k₀ : K} {z₀ z₁ : (Σ k, ι k) → ℂ} (h₀ : ∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0)
    (h₁ : ∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0) : ∀ o, ∃ i, mixPt k₀ z₀ z₁ ⟨o, i⟩ ≠ 0 := by
  intro o
  cases o with
  | none => exact h₁ k₀
  | some k => exact h₀ k

theorem log_norm_sub {k₀ : K} (A : HermLine fun o : Option K => ι (o.getD k₀)) {c : Option K → ℂ}
    (hc : ∀ o, c o ≠ 0) {z zz : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (hz : z = fun p => c p.1 * zz p)
    (hzz : ∀ o, ∃ i, zz ⟨o, i⟩ ≠ 0) {f t : ℂ} (hf : f ≠ 0) (ht : t ≠ 0) :
    Real.log ‖f * (∏ o, c o ^ A.a o) * t‖ - Real.log (A.h z) = Real.log ‖t * f‖ - Real.log (A.h zz) := by
  have hC : (∏ o, ‖c o‖ ^ A.a o) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun o _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc o))
  have hP : ‖∏ o, c o ^ A.a o‖ = ∏ o, ‖c o‖ ^ A.a o := by
    rw [norm_prod]
    exact Finset.prod_congr rfl fun o _ => norm_zpow _ _
  have hN : ‖f * (∏ o, c o ^ A.a o) * t‖ = (∏ o, ‖c o‖ ^ A.a o) * ‖t * f‖ := by
    rw [norm_mul, norm_mul, norm_mul, hP]
    ring
  have hA : A.h z = (∏ o, ‖c o‖ ^ A.a o) * A.h zz := by
    rw [hz]
    exact A.smul c zz hc
  have hp : A.h zz ≠ 0 := (A.pos zz hzz).ne'
  have hn : ‖t * f‖ ≠ 0 := norm_ne_zero_iff.2 (mul_ne_zero ht hf)
  rw [hN, hA, Real.log_mul hC hn, Real.log_mul hC hp]
  ring

theorem goodAt_of_orbit {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j)
    {F : FrameData ι Ψ N M.Ω M.blk} {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z')
    (hG : M.GoodAt F (mCoordIdeal (basePart M.blk z'))) : M.GoodAt F (mCoordIdeal (basePart M.blk z)) := by
  obtain ⟨c, hc0, hzc⟩ := h
  have e₀ : basePart M.blk z = fun q : Σ k, baseIdx ι M.blk k =>
      (fun k : NonPluckerBlocks M.blk => c k.1) q.1 * basePart M.blk z' q := by
    rw [hzc]; rfl
  rw [e₀, GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.mCoordIdeal_torus (K := NonPluckerBlocks M.blk) (ι := baseIdx ι M.blk)
    (fun k : NonPluckerBlocks M.blk => c k.1) (fun k => hc0 k.1) (basePart M.blk z')]
  exact hG

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ x, ∃ ψ kb σ i₀ V u, IsLocSec M Rb τ a k₀ ca cb RW pr x ψ kb σ i₀ V u := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a b k₀ ca cb hb hj hk hca hcb RW pr hW x
  obtain ⟨ψ, kb, σ, i₀, F, H, hx, hC⟩ := hW.2.2 x
  obtain ⟨V, z₀, z₁, c, hVo, hxV, hVs, hVU, hz₀h, hch, hc0, hL⟩ :=
    GlobalTheory.T.flag_adjacent_twisted_resolution_alt K ι Φ y Ψ N j M n e Rb τ a b k₀ ca cb hb hj hk hca hcb RW pr hW x ψ kb σ i₀ F H hx hC
  have hFr : M.IsFrame F := hC.2.1
  have hsrc := hC.2.2.2.2.2
  have hfacts : ∀ w ∈ V, basePart M.blk (z₀ w) ∈ mcPts (mCoordIdeal M.x) ∧ (∀ k, ∃ i, z₀ w ⟨k, i⟩ ≠ 0) ∧
      (∀ k, ∃ i, z₁ w ⟨k, i⟩ ≠ 0) ∧ basePart M.blk (z₁ w) = basePart M.blk (z₀ w) ∧
      M.GoodAt F (mCoordIdeal (basePart M.blk (z₀ w))) := by
    intro w hw
    obtain ⟨ho₀, ho₁, -, hoff, -, -⟩ := hL w hw
    obtain ⟨h1, -, h3, h4⟩ := PtBase.main K ι Φ y Ψ N j M n e Rb τ a k₀ ca cb RW pr hk hW w (z₀ w) (z₁ w) ho₀ ho₁
    refine ⟨h1, h3, h4, ?_, goodAt_of_orbit M ho₀ (hsrc w (hVs hw)).2.1⟩
    funext q
    exact hoff ⟨q.1.1, q.2⟩ fun e' => q.1.2 (τ, a) (hk.trans (congrArg some (Eq.symm e')))
  have hdata : ∀ w ∈ V, ψ w i₀ ≠ 0 → IsPtData M τ a k₀ ca cb RW w (z₀ w) (z₁ w) F (H τ (ψ w)) (ψ w i₀) := by
    intro w hw h0
    obtain ⟨ho₀, ho₁, hex, -⟩ := hL w hw
    have hH := (hsrc w (hVs hw)).1 τ
    exact ⟨hFr, (hfacts w hw).2.2.2.2, ho₀, ho₁, hH.1, hH.2, h0, fun i => (hex τ i).1, fun i => by
      simpa using (hex τ i).2⟩
  obtain ⟨V', hV'o, hxV', hV'V, hfh, hf0⟩ := GlobalTheory.T.holomorphic_frame_metric_near_point K ι Φ y Ψ N j M e RW.X RW.A V x
    (fun w => basePart M.blk (z₀ w)) (fun w => H τ (ψ w)) F τ a hVo hxV (fun q => hz₀h ⟨q.1.1, q.2⟩)
    (fun w hw => (hfacts w hw).1) (fun w hw => (hfacts w hw).2.2.2.2)
    (fun r s => holoOn_comp_chart RW.A hC.1 (hC.2.2.2.2.1 τ r s) hVs) (fun w hw => (hsrc w (hVs hw)).1 τ)
  obtain ⟨f, hfh, hf0, hfd⟩ : ∃ f : RW.X → ℂ, RW.A.HoloOn V' f ∧ (∀ w ∈ V', f w ≠ 0) ∧ ∀ w, f w =
      ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (basePart M.blk (z₀ w)) *
        (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (H τ (ψ w)) (wIdx N j) (wIdx N j) else 1)
          else minorIJ (H τ (ψ w)) (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i) :=
    ⟨_, hfh, hf0, fun _ => rfl⟩
  refine ⟨ψ, kb, σ, i₀, V', fun w => f w * ∏ o, c o w ^ aDeg M τ a k₀ o, ⟨F, H, hC⟩, hV'o, hxV',
    hV'V.trans hVs, hV'V.trans hVU, ?_, ?_, ?_, ?_⟩
  · exact holoOn_mul_prod_zpow RW.A _ hfh (fun o j' => (hch o j').mono
      (Set.inter_subset_inter_right _ (Set.preimage_mono hV'V))) fun o w hw => hc0 o w (hV'V hw)
  · intro w hw
    exact mul_ne_zero (hf0 w hw) (Finset.prod_ne_zero_iff.2 fun o _ => zpow_ne_zero _ (hc0 o w (hV'V hw)))
  · intro w hw
    have hwV := hV'V hw
    constructor
    · intro h0
      obtain ⟨ho₀, ho₁, hex, hoff, -, -⟩ := hL w hwV
      have hbase := (hfacts w hwV).2.2.2.1
      have hz : z₁ w = z₀ w := by
        funext q
        obtain ⟨k, m⟩ := q
        by_cases e' : k = k₀
        · subst e'
          have h1 := (hex τ a).1.2 k hk m
          have h2 := (hex τ a).2.2 k hk m
          rw [if_pos rfl, h0, Matrix.single_zero, add_zero, mul_one, hbase] at h2
          exact h2.trans h1.symm
        · exact hoff ⟨k, m⟩ e'
      rw [hz] at ho₁
      exact orbit_trans (orbit_symm ho₀) ho₁
    · intro hs
      by_contra h0
      exact GlobalTheory.T.flag_adjacent_twisted_resolution K ι Φ y Ψ N j M n e Rb τ a b k₀ ca cb hb hj hk hca hcb RW pr hW w _ _ _ _ _
        (hdata w hwV h0) hs
  · intro w hw h0 z₀' z₁' F' h' t' hD
    have hwV := hV'V hw
    obtain ⟨ho₀, ho₁, -, hoff, hl0, hl1⟩ := hL w hwV
    obtain ⟨hmc, hn₀, hn₁, hbase, hG⟩ := hfacts w hwV
    obtain ⟨hF', hG', hp₀, hp₁, hB', hd', ht', he₀', he₁'⟩ := hD
    have hd := hdata w hwV h0
    have hind := GlobalTheory.T.flag_adjacent_two_frames_orbit K ι Φ y Ψ N j M τ a b k₀ ca cb hb hj hk hca hcb F F' (z₀ w) (z₁ w) z₀' z₁'
      (H τ (ψ w)) h' (ψ w i₀) t' hmc hn₀ hn₁ hbase hFr hF' hG hG' (orbit_trans ho₀ (orbit_symm hp₀))
      (orbit_trans ho₁ (orbit_symm hp₁)) hd.2.2.2.2.1 hd.2.2.2.2.2.1 hB' hd' h0 ht' hd.2.2.2.2.2.2.2.1
      hd.2.2.2.2.2.2.2.2 he₀' he₁'
    rw [← hind]
    have hlift : RW.lift x w = fun p => c p.1 w * mixPt k₀ (z₀ w) (z₁ w) p := by
      funext p
      obtain ⟨o, m⟩ := p
      cases o with
      | none => exact hl1 m
      | some k => exact hl0 ⟨k, m⟩
    have hzz := mixPt_blocks (k₀ := k₀) hn₀ hn₁
    have hnorm := log_norm_sub (potA M τ a k₀) (c := fun o => c o w) (fun o => hc0 o w hwV) hlift hzz
      (hf0 w hw) h0
    have hcombo := GlobalTheory.T.twisted_metric_log_formula K ι Φ y Ψ N j M τ a k₀ hk _ hzz
    rw [fstPt_mixPt, sndPt_mixPt hoff] at hcombo
    have e₁ : Real.log ‖(f w * ∏ o, c o w ^ aDeg M τ a k₀ o) * ψ w i₀‖ -
        Real.log ((potA M τ a k₀).h (RW.lift x w)) = _ := hnorm
    refine e₁.trans ?_
    rw [hcombo, normRhs, ← hfd w]
    ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LocGen
end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_twisted_measure : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ x, ∃ ψ kb σ i₀ V u, IsLocSec M Rb τ a k₀ ca cb RW pr x ψ kb σ i₀ V u := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LocGen.main
end
