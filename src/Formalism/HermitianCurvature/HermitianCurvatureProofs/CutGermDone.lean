import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermContinuityAllLevels
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLow
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermPartsCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FmSmulLeft
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowFibre
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRateLowerBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimE
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopAll

section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.crystallineComparison Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal InnerProductSpace

noncomputable section

open Classical

theorem meanInf_le_limsup {f : ℕ} (Λ : AddSubgroup (V f)) (LIM : (Λ → ℂ) → ℂ) (hL : IsMeanInf Λ LIM)
    (g : Λ → ℂ) (hg : Bdd g) :
    (‖LIM g‖₊ : ℝ≥0∞) ≤
      limsup (fun x : Λ => (‖g x‖₊ : ℝ≥0∞)) (Filter.comap (fun x : Λ => (x : V f)) (atInfAll f)) := by
  refine le_of_forall_gt_imp_ge_of_dense fun b hb => ?_
  by_cases hbt : b = ⊤
  · rw [hbt]; exact le_top
  have hev := Filter.eventually_lt_of_limsup_lt hb
  set B : ℝ := b.toReal with hB
  obtain ⟨Bg, hBg⟩ := hg
  set g₁ : Λ → ℂ := fun x => if ‖g x‖ ≤ B then g x else 0 with hg₁
  set g₂ : Λ → ℂ := fun x => g x - g₁ x with hg₂
  have hb1 : Bdd g₁ := ⟨max B 0, fun x => by
    simp only [hg₁]; split_ifs with h
    · exact h.trans (le_max_left _ _)
    · simp⟩
  have hb2 : Bdd g₂ := ⟨Bg + max B 0, fun x => by
    simp only [hg₂]
    refine (norm_sub_le _ _).trans (add_le_add (hBg x) ?_)
    simp only [hg₁]; split_ifs with h
    · exact h.trans (le_max_left _ _)
    · simp⟩
  have hz : Tendsto g₂ (Filter.comap (fun x : Λ => (x : V f)) (atInfAll f)) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with x hx
    have hx' : ‖g x‖ ≤ B :=
      (ENNReal.ofReal_le_iff_le_toReal hbt).1 (by rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm] at hx; exact hx.le)
    simp [hg₂, hg₁, hx']
  have hsplit : g = g₁ + g₂ := by
    funext x; simp [hg₂]
  have h0 : LIM g₂ = 0 := hL.2 g₂ hb2 hz
  have hLg : LIM g = LIM g₁ := by
    rw [hsplit, hL.1.1 g₁ g₂ hb1 hb2, h0, add_zero]
  have hle : ‖LIM g₁‖ ≤ max B 0 := Formalism.FourierDecayAlt.P.mean_bound_estimate Λ LIM g₁ (max B 0) hL.1 fun x => by
    simp only [hg₁]; split_ifs with h
    · exact h.trans (le_max_left _ _)
    · simp
  rw [hLg]
  have hB0 : max B 0 = B := max_eq_left ENNReal.toReal_nonneg
  rw [hB0] at hle
  calc (‖LIM g₁‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖LIM g₁‖ := by rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
    _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hle
    _ = b := by rw [hB, ENNReal.ofReal_toReal hbt]

def bD {f : ℕ} (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La] :
    Module.Basis (Fin (Module.finrank ℤ La)) ℝ (V f) :=
  (Pi.basisFun ℝ (Fin (Module.finrank ℤ La))).map (PairingConjugationLemmas.Le La).symm

theorem dual_sub_span {f : ℕ} (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La] (σ : V f)
    (hσ : σ ∈ dualSet La) : σ ∈ Submodule.span ℤ (Set.range (bD La)) := by
  obtain ⟨m, rfl⟩ := PairingConjugationLemmas.ψd_surj La σ hσ
  have hrep : ∀ j, (bD La).repr (PairingConjugationLemmas.ψd La m) j = (m j : ℝ) := by
    intro j
    simp [bD, PairingConjugationLemmas.ψd]
  rw [← (bD La).sum_repr (PairingConjugationLemmas.ψd La m)]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [hrep j, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

example {f : ℕ} (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La] :
    ∃ LIM : ((Submodule.span ℤ (Set.range (bD La))).toAddSubgroup → ℂ) → ℂ,
      IsMeanInf (Submodule.span ℤ (Set.range (bD La))).toAddSubgroup LIM :=
  Formalism.FourierDecayAlt.P.invariantMeanExists f _

theorem inDual_neg {ω₁ ω₂ σ : ℂ} (h : TBB.InDual ω₁ ω₂ σ) : TBB.InDual ω₁ ω₂ (-σ) := by
  intro a b
  have h1 := h (-a) (-b)
  have e : P5.fsv (-σ) ((a : ℂ) * ω₁ + (b : ℂ) * ω₂) =
      P5.fsv σ (((-a : ℤ) : ℂ) * ω₁ + ((-b : ℤ) : ℂ) * ω₂) := by
    simp only [P5.fsv, map_neg, map_add, map_mul, Int.cast_neg]
    congr 1
    ring
  rw [e, h1]

theorem pdDual_of_pdOn (ω₁ ω₂ : ℂ) (T : Set (V 1)) (A0 : V 1 → ℂ) (hA0 : PDOn T A0) (φ : ℂ → V 1)
    (hφ : Function.Injective φ) (hlin : ∀ a b, φ (a - b) = φ a - φ b)
    (hmem : ∀ σ, TBB.InDual ω₁ ω₂ σ → φ σ ∈ T) (c0 : ℝ) (hc0 : 0 ≤ c0) :
    PDDual ω₁ ω₂ (fun σ => (c0 : ℂ) * A0 (φ σ)) := by
  classical
  intro S c hS
  have hinv : ∀ σ, Function.invFun φ (φ σ) = σ := Function.leftInverse_invFun hφ
  have h0 := hA0 (S.image φ) (fun τ => c (Function.invFun φ τ)) (by
    intro τ hτ
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hτ
    exact hmem σ (hS σ hσ))
  simp only [Finset.sum_image hφ.injOn] at h0
  have e : (∑ σ ∈ S, ∑ σ' ∈ S, (c0 : ℂ) * A0 (φ (σ - σ')) * c σ * conj (c σ')) =
      (c0 : ℂ) * ∑ σ ∈ S, ∑ σ' ∈ S,
        A0 (φ σ - φ σ') * c (Function.invFun φ (φ σ)) * conj (c (Function.invFun φ (φ σ'))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ' _ => ?_
    rw [hinv, hinv, hlin]
    ring
  show 0 ≤ (∑ σ ∈ S, ∑ σ' ∈ S, (c0 : ℂ) * A0 (φ (σ - σ')) * c σ * conj (c σ')).re
  rw [e, Complex.re_ofReal_mul]
  exact mul_nonneg hc0 h0

section vec

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {s : ℕ} {β ε' : ℂ}
  {ut : ℂ → ℂ → H} {bt : ℂ → H} {SS : ℝ}

def uL (hG : PBK.GermD s β ε' ({()} : Finset Unit) (fun _ => ut) (fun _ => bt) SS) (x : ℂ) :
    Lp H 2 (volume : Measure ℂ) :=
  if hx : x ≠ 0 then
    ((PBK.memLp_cvec s ut x hx).1 (hG.memU () (Finset.mem_singleton_self _) x hx)).toLp (PBK.cvec s ut x)
  else 0

def aL (hG : PBK.GermD s β ε' ({()} : Finset Unit) (fun _ => ut) (fun _ => bt) SS) (x : ℂ) :
    Lp H 2 (volume : Measure ℂ) :=
  if hx : x ≠ 0 then
    ((PBK.memLp_cvec s (fun x D => PBK.mainD s β ε' bt x D) x hx).1
      (hG.memLp_mainD (Finset.mem_singleton_self ()) x)).toLp (PBK.cvec s (fun x D => PBK.mainD s β ε' bt x D) x)
  else 0

variable (hG : PBK.GermD s β ε' ({()} : Finset Unit) (fun _ => ut) (fun _ => bt) SS)

theorem inner_uL_uL {x x' : ℂ} (hx : x ≠ 0) (hx' : x' ≠ 0) :
    ⟪uL hG x, uL hG x'⟫_ℂ =
      PBK.gramL volume (PBK.Uc s fun _ => ut) (PBK.Uc s fun _ => ut) ((), x) ((), x') := by
  simp only [uL, aL, dif_pos hx, dif_pos hx']
  rw [MeasureTheory.L2.inner_def, PBK.gramL]
  refine integral_congr_ae ?_
  filter_upwards [((PBK.memLp_cvec s ut x hx).1 (hG.memU () (Finset.mem_singleton_self _) x hx)).coeFn_toLp, ((PBK.memLp_cvec s ut x' hx').1 (hG.memU () (Finset.mem_singleton_self _) x' hx')).coeFn_toLp] with D h1 h2
  rw [h1, h2]
  rfl

theorem inner_uL_aL {x x' : ℂ} (hx : x ≠ 0) (hx' : x' ≠ 0) :
    ⟪uL hG x, aL hG x'⟫_ℂ =
      PBK.gramL volume (PBK.Uc s fun _ => ut) (PBK.Ac s β ε' fun _ => bt) ((), x) ((), x') := by
  simp only [uL, aL, dif_pos hx, dif_pos hx']
  rw [MeasureTheory.L2.inner_def, PBK.gramL]
  refine integral_congr_ae ?_
  filter_upwards [((PBK.memLp_cvec s ut x hx).1 (hG.memU () (Finset.mem_singleton_self _) x hx)).coeFn_toLp, ((PBK.memLp_cvec s (fun x D => PBK.mainD s β ε' bt x D) x' hx').1
      (hG.memLp_mainD (Finset.mem_singleton_self ()) x')).coeFn_toLp] with D h1 h2
  rw [h1, h2]
  rfl

theorem inner_aL_aL {x x' : ℂ} (hx : x ≠ 0) (hx' : x' ≠ 0) :
    ⟪aL hG x, aL hG x'⟫_ℂ =
      PBK.gramL volume (PBK.Ac s β ε' fun _ => bt) (PBK.Ac s β ε' fun _ => bt) ((), x) ((), x') := by
  simp only [uL, aL, dif_pos hx, dif_pos hx']
  rw [MeasureTheory.L2.inner_def, PBK.gramL]
  refine integral_congr_ae ?_
  filter_upwards [((PBK.memLp_cvec s (fun x D => PBK.mainD s β ε' bt x D) x hx).1
      (hG.memLp_mainD (Finset.mem_singleton_self ()) x)).coeFn_toLp, ((PBK.memLp_cvec s (fun x D => PBK.mainD s β ε' bt x D) x' hx').1
      (hG.memLp_mainD (Finset.mem_singleton_self ()) x')).coeFn_toLp] with D h1 h2
  rw [h1, h2]
  rfl

theorem norm_sq_of_inner {v : Lp H 2 (volume : Measure ℂ)} {C : ℝ} (h : ‖⟪v, v⟫_ℂ‖ ≤ C) : ‖v‖ ≤ √C := by
  have h2 : ‖v‖ ^ 2 ≤ C := by
    have e : ‖⟪v, v⟫_ℂ‖ = ‖v‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      simp
    linarith
  calc ‖v‖ = √(‖v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg v)).symm
    _ ≤ √C := Real.sqrt_le_sqrt h2

theorem norm_uL_le (x : ℂ) : ‖uL hG x‖ ≤ √SS := by
  by_cases hx : x = 0
  · simp [uL, hx]
  · refine norm_sq_of_inner ?_
    rw [inner_uL_uL hG hx hx, PBK.gramL]
    refine (norm_integral_le_integral_norm _).trans ?_
    have e : ∀ D, ‖⟪PBK.Uc s (fun _ => ut) ((), x) D, PBK.Uc s (fun _ => ut) ((), x) D⟫_ℂ‖ =
        ‖PBK.cvec s ut x D‖ ^ 2 := by
      intro D
      rw [inner_self_eq_norm_sq_to_K]
      simp [PBK.Uc]
    simp_rw [e]
    rw [PBK.integral_norm_cvec_sq s ut x hx]
    exact hG.sup () (Finset.mem_singleton_self _) x hx

theorem norm_aL_le {B' : ℝ} (hB : ∀ x : ℂ, x ≠ 0 →
    ‖PBK.gramL volume (PBK.Ac s β ε' fun _ => bt) (PBK.Ac s β ε' fun _ => bt) ((), x) ((), x)‖ ≤ B') (x : ℂ) :
    ‖aL hG x‖ ≤ √B' := by
  by_cases hx : x = 0
  · simp [aL, hx]
  · exact norm_sq_of_inner (by rw [inner_aL_aL hG hx hx]; exact hB x hx)

end vec

theorem enn_nnnorm (z : ℂ) : (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ := by
  rw [ENNReal.ofReal]
  congr 1
  ext
  simp

theorem limsup_link {α : Type} {F : Filter α} (g : α → ℂ) (m : α → ℂ) (Nk : ℂ → ℂ → ℂ) (σ : ℂ) (κ₁ : ℝ)
    (hκ₁ : 0 ≤ κ₁) (hm : Tendsto m F (𝓝[≠] 0))
    (he : ∀ᶠ x in F, ‖Nk (m x) ((m x)⁻¹ + σ)⁻¹‖ = κ₁ * ‖g x‖) :
    ENNReal.ofReal κ₁ * limsup (fun x => (‖g x‖₊ : ℝ≥0∞)) F ≤
      limsup (fun t : ℂ => (‖Nk t (t⁻¹ + σ)⁻¹‖₊ : ℝ≥0∞)) (𝓝[≠] 0) := by
  have heq : (fun x => (‖Nk (m x) ((m x)⁻¹ + σ)⁻¹‖₊ : ℝ≥0∞)) =ᶠ[F]
      fun x => ENNReal.ofReal κ₁ * (‖g x‖₊ : ℝ≥0∞) := by
    filter_upwards [he] with x hx
    rw [enn_nnnorm, enn_nnnorm, hx, ENNReal.ofReal_mul hκ₁]
  rw [← ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top, ← limsup_congr heq]
  calc limsup (fun x => (‖Nk (m x) ((m x)⁻¹ + σ)⁻¹‖₊ : ℝ≥0∞)) F
      = limsup (fun t : ℂ => (‖Nk t (t⁻¹ + σ)⁻¹‖₊ : ℝ≥0∞)) (map m F) :=
        Filter.limsup_comp (fun t : ℂ => (‖Nk t (t⁻¹ + σ)⁻¹‖₊ : ℝ≥0∞)) m F
    _ ≤ _ := limsup_le_limsup_of_le hm

theorem tendsto_inv_shift {α : Type} {F : Filter α} (X : α → ℂ) (δ : ℂ) (hX : Tendsto X F (cocompact ℂ)) :
    Tendsto (fun x => (X x + δ)⁻¹) F (𝓝[≠] 0) := by
  have hn : Tendsto (fun x => ‖X x‖) F atTop := tendsto_norm_cocompact_atTop.comp hX
  have hY : Tendsto (fun x => ‖X x + δ‖) F atTop := by
    refine tendsto_atTop_mono (fun x => ?_) (tendsto_atTop_add_const_right _ (-‖δ‖) hn)
    have := norm_sub_norm_le (X x) (-δ)
    rw [norm_neg, sub_neg_eq_add] at this
    linarith
  rw [tendsto_nhdsWithin_iff]
  constructor
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_inv]
    exact hY.inv_tendsto_atTop
  · filter_upwards [hY.eventually_gt_atTop 0] with x hx
    simpa using norm_pos_iff.mp hx

theorem germ_mean_property : PropGMean := by
  intro H _ _ _ s β ε' η ut bt SS κ₁ κ₂ E Nk hs hκ₂ hκ hη hGD hpsi hNk hE
  have hmem : () ∈ ({()} : Finset Unit) := Finset.mem_singleton_self _
  obtain ⟨hb, -, ⟨B', hB'⟩, hlim⟩ := PBK.GermD.propG hGD
  have hbz : MemLp (PBK.bz s bt) 2 volume := (hb () hmem).1
  have hsq : Integrable (fun z => ‖PBK.bz s bt z‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hbz.1).1 hbz
  have hae : ∀ᵐ z : ℂ, z ≠ 0 := by
    rw [ae_iff]
    simp [measure_singleton]
  have hEae : (fun z => κ₂ * ‖PBK.bz s bt z‖ ^ 2) =ᵐ[volume] E := by
    filter_upwards [hae] with z hz
    exact (hE z hz).symm
  have hEint : Integrable E := (hsq.const_mul κ₂).congr hEae
  refine ⟨hEint, fun ω₁ ω₂ hω => ?_⟩
  have hpi : 0 < Real.pi := Real.pi_pos

  set Nh : ℂ → ℂ := fun σ => PBK.Nhat s β (fun _ => bt) σ () () with hNh
  have hT : ∀ σ : ℂ, (Real.pi⁻¹ : ℂ) * (∫ z, P5.fsv σ z * (E z : ℂ)) =
      ((κ₂ / Real.pi : ℝ) : ℂ) * Nh (η * σ) := by
    intro σ
    have e0 : Nh (η * σ) = ∫ z, G.psi β (η * σ * z) • ⟪PBK.bz s bt z, PBK.bz s bt z⟫_ℂ := rfl
    have e1 : (∫ z, P5.fsv σ z * (E z : ℂ)) =
        (κ₂ : ℂ) * ∫ z, G.psi β (η * σ * z) • ⟪PBK.bz s bt z, PBK.bz s bt z⟫_ℂ := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hae] with z hz
      have hin : ⟪PBK.bz s bt z, PBK.bz s bt z⟫_ℂ = ((‖PBK.bz s bt z‖ ^ 2 : ℝ) : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K]; norm_cast
      rw [hE z hz, hpsi, hin, smul_eq_mul]
      push_cast
      ring
    rw [e1, e0]
    push_cast
    ring

  set La := Submodule.span ℤ (Set.range (TBBx5.lp_b ω₁ ω₂ hω)) with hLa
  set Λs := Submodule.span ℤ (Set.range (bD La)) with hΛs
  obtain ⟨LIM, hLIM⟩ := Formalism.FourierDecayAlt.P.invariantMeanExists 1 Λs
  set X : V 1 → ℂ := fun y => 2 * Real.pi * Complex.I * y 0 with hX
  have hXadd : ∀ y y' : V 1, X (y + y') = X y + X y' := by
    intro y y'
    simp only [hX, Pi.add_apply]
    ring
  have hXt : Tendsto X (atInfAll 1) (cocompact ℂ) := by
    have hn0 : Tendsto (fun y : V 1 => ‖y 0‖) (atInfAll 1) atTop := by
      unfold atInfAll
      exact tendsto_iInf' 0 tendsto_comap
    have hn : Tendsto (fun y : V 1 => ‖X y‖) (atInfAll 1) atTop := by
      have e : (fun y : V 1 => ‖X y‖) = fun y => (2 * Real.pi) * ‖y 0‖ := by
        funext y
        simp only [hX, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi,
          Complex.norm_ofNat, mul_one]
      rw [e]
      exact hn0.const_mul_atTop (by positivity)
    refine (Filter.hasBasis_cocompact.tendsto_right_iff).2 fun K hK => ?_
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    filter_upwards [hn.eventually_gt_atTop R] with x hx hxK
    have := hR hxK
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  have hne : ∀ c : ℂ, ∀ᶠ y in atInfAll 1, X y + c ≠ 0 := by
    intro c
    filter_upwards [hXt (isCompact_singleton (x := -c)).compl_mem_cocompact] with y hy
    exact fun e => hy (Set.mem_singleton_iff.2 (eq_neg_of_add_eq_zero_left e))
  have hne0 : ∀ᶠ y in atInfAll 1, X y ≠ 0 := by
    filter_upwards [hne 0] with y hy
    simpa using hy
  set a : V 1 → Lp H 2 (volume : Measure ℂ) := fun y => aL hGD (X y) with ha
  set u : V 1 → Lp H 2 (volume : Measure ℂ) := fun y => uL hGD (X y) with hu
  set r : V 1 → Lp H 2 (volume : Measure ℂ) := fun y => u y - a y with hr
  have hau : ∀ y, a y + r y = u y := fun y => by simp only [hr]; abel
  have hBa : ∀ y, ‖a y‖ ≤ √B' := fun y => norm_aL_le hGD (fun x hx => hB' () hmem x hx) (X y)
  have hBu : ∀ y, ‖u y‖ ≤ √SS := fun y => norm_uL_le hGD (X y)
  have hbnd : ∀ y, ‖a y‖ ≤ √SS + √B' ∧ ‖r y‖ ≤ √SS + √B' := by
    intro y
    refine ⟨(hBa y).trans (le_add_of_nonneg_left (Real.sqrt_nonneg _)), ?_⟩
    exact (norm_sub_le _ _).trans (add_le_add (hBu y) (hBa y))
  set Nh' : V 1 → ℂ := fun σ => Nh (X σ) with hNh'
  have hAA : ∀ σ ∈ Λs.toAddSubgroup, Tendsto (fun x => ⟪a x, a (x + σ)⟫_ℂ) (atInfAll 1) (𝓝 (Nh' σ)) := by
    intro σ _
    refine ((hlim () hmem () hmem (X σ)).1.comp hXt).congr' ?_
    filter_upwards [hne0, hne (X σ)] with y h1 h2
    simp only [Function.comp_apply, ha, hXadd]
    exact (inner_aL_aL hGD h1 h2).symm
  have hAR : ∀ σ ∈ Λs.toAddSubgroup, Tendsto (fun x => ⟪a x, r (x + σ)⟫_ℂ) (atInfAll 1) (𝓝 0) := by
    intro σ _
    have h3 := ((hlim () hmem () hmem (X σ)).2.2.comp hXt)
    have h1 := ((hlim () hmem () hmem (X σ)).1.comp hXt)
    rw [← sub_self (Nh' σ)]
    refine (h3.sub h1).congr' ?_
    filter_upwards [hne0, hne (X σ)] with y hy1 hy2
    simp only [Function.comp_apply, hr, ha, hu, hXadd, inner_sub_right]
    rw [← inner_aL_aL hGD hy1 hy2, ← inner_uL_aL hGD hy2 hy1, inner_conj_symm]
  have hRA : ∀ σ ∈ Λs.toAddSubgroup, Tendsto (fun x => ⟪r x, a (x + σ)⟫_ℂ) (atInfAll 1) (𝓝 0) := by
    intro σ _
    have h2 := ((hlim () hmem () hmem (X σ)).2.1.comp hXt)
    have h1 := ((hlim () hmem () hmem (X σ)).1.comp hXt)
    rw [← sub_self (Nh' σ)]
    refine (h2.sub h1).congr' ?_
    filter_upwards [hne0, hne (X σ)] with y hy1 hy2
    simp only [Function.comp_apply, hr, ha, hu, hXadd, inner_sub_left]
    rw [← inner_aL_aL hGD hy1 hy2, ← inner_uL_aL hGD hy1 hy2]
  obtain ⟨hsplit, hpd⟩ := Formalism.FourierDecayAlt.P.mean_split_identity 1 Λs.toAddSubgroup LIM (Lp H 2 (volume : Measure ℂ)) a r
    Nh' (√SS + √B') hLIM hbnd hAA hAR hRA
  set A0 : V 1 → ℂ := fun σ => LIM (fun x : Λs.toAddSubgroup => ⟪r x, r ((x : V 1) + σ)⟫_ℂ) with hA0

  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := TBBx5.lp_ne
  have hη0 : η ≠ 0 := by rcases hη with h | h <;> simp [h]
  set φ : ℂ → V 1 := fun σ => fun _ => η * σ / (2 * Real.pi * Complex.I) with hφ
  have hXφ : ∀ σ, X (φ σ) = η * σ := by
    intro σ
    simp only [hX, hφ]
    field_simp
  have hφmem : ∀ σ, TBB.InDual ω₁ ω₂ σ → φ σ ∈ Λs := by
    intro σ hσ
    refine dual_sub_span La (φ σ) ((TBBx5.lp_dual ω₁ ω₂ hω (φ σ)).2 ?_)
    have e : 2 * Real.pi * Complex.I * φ σ 0 = η * σ := hXφ σ
    rw [e]
    rcases hη with h | h
    · simpa [h] using hσ
    · simpa [h] using inDual_neg hσ
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have := congrFun hxy 0
    simp only [hφ] at this
    have := (div_left_inj' h2pi).1 this
    exact mul_left_cancel₀ hη0 this
  have hφlin : ∀ x y, φ (x - y) = φ x - φ y := by
    intro x y
    funext i
    simp only [hφ, Pi.sub_apply]
    ring
  have hc0 : 0 ≤ κ₂ / Real.pi := div_nonneg hκ₂ hpi.le
  refine ⟨fun σ => ((κ₂ / Real.pi : ℝ) : ℂ) * A0 (φ σ),
    pdDual_of_pdOn ω₁ ω₂ (Λs.toAddSubgroup : Set (V 1)) A0 hpd φ hφinj hφlin hφmem _ hc0, fun σ hσ => ?_⟩

  have hΛφ : φ σ ∈ Λs.toAddSubgroup := hφmem σ hσ
  have hLg := hsplit (φ σ) hΛφ
  simp_rw [hau] at hLg
  set g : Λs.toAddSubgroup → ℂ := fun x => ⟪u x, u ((x : V 1) + φ σ)⟫_ℂ with hg
  have hgB : Bdd g := ⟨√SS * √SS, fun x => (norm_inner_le_norm _ _).trans
    (mul_le_mul (hBu _) (hBu _) (norm_nonneg _) (Real.sqrt_nonneg _))⟩
  have hmean := meanInf_le_limsup Λs.toAddSubgroup LIM hLIM g hgB
  have hsum : (Real.pi⁻¹ : ℂ) * (∫ z, P5.fsv σ z * (E z : ℂ)) + ((κ₂ / Real.pi : ℝ) : ℂ) * A0 (φ σ) =
      ((κ₂ / Real.pi : ℝ) : ℂ) * LIM g := by
    rw [hT σ, hLg, ← hXφ σ]
    ring
  rw [hsum, enn_nnnorm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0,
    ENNReal.ofReal_mul hc0, ← enn_nnnorm]

  have hκ₁ : 0 ≤ κ₁ := by
    have := hκ₂.trans hκ
    exact nonneg_of_mul_nonneg_right (by linarith) hpi
  have hcle : ENNReal.ofReal (κ₂ / Real.pi) ≤ ENNReal.ofReal κ₁ :=
    ENNReal.ofReal_le_ofReal ((div_le_iff₀ hpi).2 (by linarith))
  set F : Filter Λs.toAddSubgroup := Filter.comap (fun x : Λs.toAddSubgroup => (x : V 1)) (atInfAll 1) with hF
  have hXtF : Tendsto (fun x : Λs.toAddSubgroup => X x) F (cocompact ℂ) := hXt.comp tendsto_comap
  have hneF : ∀ c : ℂ, ∀ᶠ x : Λs.toAddSubgroup in F, X x + c ≠ 0 := fun c => tendsto_comap.eventually (hne c)
  set δ : ℂ := if η = 1 then 0 else -σ with hδ
  have hlink : ∀ᶠ x : Λs.toAddSubgroup in F, ‖Nk ((X x + δ)⁻¹) (((X x + δ)⁻¹)⁻¹ + σ)⁻¹‖ = κ₁ * ‖g x‖ := by
    filter_upwards [hneF δ, hneF (δ + σ), hneF 0, hneF (η * σ)] with x h1 h2 h3 h4
    rw [inv_inv]
    have h3' : X x ≠ 0 := by simpa using h3
    rw [hNk _ _ (inv_ne_zero h1) (inv_ne_zero (by rwa [add_assoc])), inv_inv, inv_inv]
    congr 1
    simp only [hg, hu]
    rw [hXadd, hXφ σ]
    rcases hη with h | h
    · have hd : δ = 0 := by simp [hδ, h]
      simp only [hd, add_zero, h, one_mul]
      rw [inner_uL_uL hGD h3' (by simpa [h] using h4)]
    · have hd : δ = -σ := by rw [hδ, if_neg (by rw [h]; norm_num)]
      simp only [hd, h, neg_one_mul, neg_add_cancel_right]
      have h4' : X x + -σ ≠ 0 := by simpa [h] using h4
      rw [← sub_eq_add_neg, ← inner_uL_uL hGD (by rwa [sub_eq_add_neg]) h3', sub_eq_add_neg, norm_inner_symm]
  have hfin := limsup_link g (fun x => (X x + δ)⁻¹) Nk σ κ₁ hκ₁ (tendsto_inv_shift _ δ hXtF) hlink
  calc ENNReal.ofReal (κ₂ / Real.pi) * (‖LIM g‖₊ : ℝ≥0∞)
      ≤ ENNReal.ofReal κ₁ * limsup (fun x => (‖g x‖₊ : ℝ≥0∞)) F := mul_le_mul' hcle hmean
    _ ≤ _ := hfin

end

end Formalism.FourierDecayAlt.P.CutBP
end

section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt

theorem germCutPD_of_data (hA : P5.ThmPActual) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
    (p : KB.Pl P Wp Wq) (nn χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ)
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : KB.CptCoef p.T.base F) (hχ : C6.IsCut0 χ)
    (hnn : ∀ y, 0 < nn y) (hL : GermDataLowAll) (hT : GermDataTopAll) : GermCutPD p nn χ F Y K N :=
  germCutPD_of_parts hA p nn χ F Y K N Cb hCb hF hχ hnn germ_continuity_all_levels hL hT germ_mean_property

theorem block_growth_bound_of_compact_coef_of_germ_data (hA : P5.ThmPActual) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ)
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hG : KB.CptCoef p.T.base G) (hnn : ∀ y, 0 < nn y)
    (hL : GermDataLowAll) (hT : GermDataTopAll) : TBB.BlockGrowthBound p nn G Y K N :=
  block_growth_bound_of_germ_data hA p nn G Y K N Cb hCb hG hnn germ_continuity_all_levels hL hT germ_mean_property

end Formalism.FourierDecayAlt.P.CutBP
end

section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

theorem gl_isLocPt_snoc {a : C.LPt} {j m : ℕ} (ha : D.IsLocPt a j) (hm : 1 ≤ m) {c : ℂ} (hc : c ≠ 0) :
    D.IsLocPt (a ++ [(m, c)]) (j + m) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases List.mem_append.1 hx with hx | hx
    · exact ha.1 x hx
    · simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨hm, hc⟩
  · rw [← ha.2]
    simp [D.ptSize, List.map_append, List.sum_append]

theorem gl_fsv (σ z : ℂ) : P5.fsv σ z = G.psi (-U.betaU) (1 * σ * z) := by
  rw [TBBx1.fsv_eq]
  unfold G.psi U.betaU Formalism.QuantumDeterminants.cStd
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.re_ofNat, Complex.im_ofNat, Complex.one_re, Complex.one_im]
  push_cast
  ring

section vec

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem gl_inner_self (u : H) : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl

end vec

theorem germDataLowAll_of_parts (hGr : GLGram) (hFi : GLFibre) (hCo : GLCont) (hGe : GLGerm) : GermDataLowAll := by
  intro hA Wp Wq _ _ _ _ _ _ P p nn F Y K N Cb hCb hF hnn b s hb hs hbs hlev h hh w hw hN hBdd
  have hi : b + s - 1 ≤ P.r := hlev
  have hN' : w.length ≤ N := by omega
  obtain ⟨H, i1, i2, i3, Vec, hVec⟩ := hGr hA Wp Wq P p nn F Y N Cb hCb hF hnn (b + s - 1) hi w hw hN'
  let _ := i1; let _ := i2; have _ := i3
  have hs0 : s ≠ 0 := by omega
  have hpi : (0 : ℝ) < Real.pi ^ (s - 1) := pow_pos Real.pi_pos _
  set κ : ℝ := (Real.pi ^ (s - 1))⁻¹ with hκ
  have hκκ : Real.pi ^ (2 * (s - 1)) * (κ * κ) = 1 := by
    rw [hκ, pow_mul', sq, ← mul_inv, mul_inv_cancel₀ (by positivity)]
  let ut : ℂ → ℂ → H := fun x D => (((κ * ‖x‖ ^ (s - 1)) : ℝ) : ℂ) • Vec (h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)])
  let bt : ℂ → H := fun z => if z = 0 then 0 else ((((s : ℝ) * ‖z‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • Vec (h ++ [(s, z)])

  have hcv : ∀ x : ℂ, x ≠ 0 → ∀ c : ℂ, PBK.cvec s ut x c = (κ : ℂ) • Vec ((h ++ [(s - 1, x⁻¹)]) ++ [(1, c)]) := by
    intro x hx c
    have ha : x ^ (s - 1) ≠ 0 := pow_ne_zero _ hx
    have hn : (‖x‖ ^ (s - 1) : ℝ) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
    simp only [PBK.cvec, ut, smul_smul, List.append_assoc, List.cons_append, List.nil_append]
    rw [mul_div_cancel₀ c ha, ← Complex.ofReal_mul]
    congr 2
    field_simp

  have hj : b + s - 2 + 1 = b + s - 1 := by omega
  have hloc : ∀ t : ℂ, t ≠ 0 → D.IsLocPt (h ++ [(s - 1, t)]) (b + s - 2) := by
    intro t ht
    have := gl_isLocPt_snoc hh (by omega : 1 ≤ s - 1) ht
    rwa [show b - 1 + (s - 1) = b + s - 2 by omega] at this

  have hgram : ∀ x x' : ℂ, x ≠ 0 → x' ≠ 0 →
      ∫ c, ⟪PBK.cvec s ut x c, PBK.cvec s ut x' c⟫_ℂ =
        ((κ * κ : ℝ) : ℂ) * TBB.NP p nn F (b + s - 2) w (h ++ [(s - 1, x⁻¹)]) (h ++ [(s - 1, x'⁻¹)]) := by
    intro x x' hx hx'
    obtain ⟨-, hfib⟩ := hFi hA Wp Wq P p nn F Y N Cb hCb hF hnn (b + s - 2) (by omega) w hw hN'
      (h ++ [(s - 1, x⁻¹)]) (h ++ [(s - 1, x'⁻¹)]) (hloc _ (inv_ne_zero hx)) (hloc _ (inv_ne_zero hx'))
    rw [hj] at hfib
    rw [← hfib, ← integral_const_mul]
    congr 1
    funext c
    rw [hcv x hx c, hcv x' hx' c, GermFibreKernels.inner_real_smul_smul, hVec]

  have hbz : ∀ z : ℂ, z ≠ 0 → PBK.bz s bt z = Vec (h ++ [(s, z)]) := by
    intro z hz
    simp only [PBK.bz, bt, if_neg hz, smul_smul, ← Complex.ofReal_mul]
    rw [mul_inv_cancel₀, Complex.ofReal_one, one_smul]
    have : (0 : ℝ) < ‖z‖ ^ (s - 1) := pow_pos (norm_pos_iff.mpr hz) _
    have hs' : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs0
    positivity

  have hVecR : ∀ i (hi' : i = b + s - 1) a a', TBB.NP p nn F i w a a' = ⟪Vec a, Vec a'⟫_ℂ := by
    intro i hi' a a'; subst hi'; exact hVec a a'
  have hcont1 : ∀ t : ℂ, t ≠ 0 → ContinuousOn (fun c : ℂ => Vec ((h ++ [(s - 1, t)]) ++ [(1, c)])) {0}ᶜ := by
    intro t ht
    have hk := hCo hA Wp Wq P p nn F Y N Cb hCb hF hnn (b + s - 2) 1 le_rfl (by omega) w hw hN' _ (hloc t ht)
    exact GermFibreKernels.vec_continuousOn _ Vec (hVecR _ hj) (fun c => (h ++ [(s - 1, t)]) ++ [(1, c)]) {0}ᶜ hk
  have hcontS : ContinuousOn (fun z : ℂ => Vec (h ++ [(s, z)])) {0}ᶜ := by
    have hk := hCo hA Wp Wq P p nn F Y N Cb hCb hF hnn (b - 1) s (by omega) (by omega) w hw hN' h hh
    exact GermFibreKernels.vec_continuousOn _ Vec (hVecR _ (by omega)) (fun z => h ++ [(s, z)]) {0}ᶜ hk

  obtain ⟨B0, hB0⟩ := hBdd w (TBBx1.isExt_self hw hN')
  refine ⟨H, i1, i2, i3, ut, bt, -U.betaU, (-1) ^ (s + 1), 1, κ * κ * B0, Real.pi ^ (2 * (s - 1)), 1,
    zero_le_one, ?_, Or.inl rfl, ?_, gl_fsv, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    exact one_le_mul_of_one_le_of_one_le h1 (one_le_pow₀ h1)
  · have hae : ∀ᵐ z : ℂ ∂volume, z ∈ ({0}ᶜ : Set ℂ) :=
      measure_eq_zero_iff_ae_notMem.mp (measure_singleton (0 : ℂ))
    have hmeas0 : MeasurableSet ({0}ᶜ : Set ℂ) := (measurableSet_singleton 0).compl
    refine ⟨hs0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold U.betaU Formalism.QuantumDeterminants.cStd
      simp [Complex.I_ne_zero]
    · simp [norm_pow]
    ·
      intro _ _ x hx
      refine (PBK.memLp_cvec s ut x hx).2 ?_
      have hfun : PBK.cvec s ut x = fun c => (κ : ℂ) • Vec ((h ++ [(s - 1, x⁻¹)]) ++ [(1, c)]) := funext (hcv x hx)
      rw [hfun]
      refine MemLp.const_smul ?_ _
      have hmeas : AEStronglyMeasurable (fun c : ℂ => Vec ((h ++ [(s - 1, x⁻¹)]) ++ [(1, c)])) volume := by
        have h2 := (hcont1 x⁻¹ (inv_ne_zero hx)).aestronglyMeasurable (μ := volume) hmeas0
        rwa [Measure.restrict_eq_self_of_ae_mem hae] at h2
      refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
      obtain ⟨hint, -⟩ := hFi hA Wp Wq P p nn F Y N Cb hCb hF hnn (b + s - 2) (by omega) w hw hN' _ _
        (hloc _ (inv_ne_zero hx)) (hloc _ (inv_ne_zero hx))
      rw [hj] at hint
      refine (Complex.reCLM.integrable_comp hint).congr (Eventually.of_forall fun c => ?_)
      simp only [Complex.reCLM_apply]
      rw [hVec, gl_inner_self, Complex.ofReal_re]
    ·
      intro _ _ x hx
      have e1 := PBK.cvec_inner s ut ut x x hx hx
      simp only [div_self (pow_ne_zero _ hx), norm_one, Complex.ofReal_one, one_smul, one_mul] at e1
      have e2 : ∫ D, ⟪ut x D, ut x D⟫_ℂ = ((∫ D, ‖ut x D‖ ^ 2 : ℝ) : ℂ) := by
        simp_rw [gl_inner_self]; exact integral_ofReal
      rw [e2, hgram x x hx hx] at e1
      have e3 := congrArg Complex.re e1
      rw [Complex.ofReal_re, Complex.re_ofReal_mul] at e3
      rw [← e3]
      have hE : (TBB.NP p nn F (b + s - 2) w (h ++ [(s - 1, x⁻¹)]) (h ++ [(s - 1, x⁻¹)])).re ≤ B0 :=
        hB0 ⟨⟨x⁻¹, inv_ne_zero hx⟩, rfl⟩
      exact mul_le_mul_of_nonneg_left hE (mul_self_nonneg κ)
    ·
      intro _ _
      let _ : MeasurableSpace H := borel H
      have _ : BorelSpace H := ⟨rfl⟩
      let g : ℂ → H := fun z => ((((s : ℝ) * ‖z‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • Vec (h ++ [(s, z)])
      have hgc : ContinuousOn g {0}ᶜ := by
        refine ContinuousOn.smul ?_ hcontS
        refine Complex.continuous_ofReal.comp_continuousOn ?_
        refine ContinuousOn.inv₀ (Continuous.continuousOn (by fun_prop)) fun z hz => ?_
        have : (0 : ℝ) < ‖z‖ ^ (s - 1) := pow_pos (norm_pos_iff.mpr hz) _
        have hs' : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs0
        positivity
      have hbt' : bt = ({0}ᶜ : Set ℂ).piecewise g (fun _ => 0) := by
        funext z
        by_cases hz : z = 0
        · simp [bt, hz]
        · simp [bt, hz, Set.piecewise, g]
      show StronglyMeasurable bt
      rw [stronglyMeasurable_iff_measurable_separable, hbt']
      refine ⟨ContinuousOn.measurable_piecewise hgc continuousOn_const hmeas0, ?_⟩
      refine TopologicalSpace.IsSeparable.mono (s := g '' {0}ᶜ ∪ {0}) ?_ (Set.range_subset_iff.2 fun z => ?_)
      · exact (hgc.isSeparable_image (TopologicalSpace.IsSeparable.of_separableSpace _)).union
          (Set.finite_singleton (0 : H)).isSeparable
      · by_cases hz : z ∈ ({0}ᶜ : Set ℂ)
        · left; rw [Set.piecewise_eq_of_mem _ _ _ hz]; exact ⟨z, hz, rfl⟩
        · right; rw [Set.piecewise_eq_of_notMem _ _ _ hz]; rfl
    ·
      intro _ _ K' hK hK0
      have hsub : K' ⊆ {0}ᶜ := fun z hz hz0 => hK0 (by rw [Set.mem_singleton_iff.1 hz0] at hz; exact hz)
      have hc : ContinuousOn (fun z => ‖Vec (h ++ [(s, z)])‖ ^ 2) K' := (hcontS.norm.pow 2).mono hsub
      refine (hc.congr fun z hz => ?_).integrableOn_compact hK
      rw [hbz z (fun h0 => hK0 (h0 ▸ hz))]
    ·
      intro _ _ K' hK hK0
      obtain ⟨C, hC⟩ := hGe hA Wp Wq P p nn F Y N Cb hCb hF hnn b s hb hs hi h hh w hw hN' H Vec hVec K' hK hK0
      refine ⟨C, fun x hx => Eventually.of_forall fun D hD => ?_⟩
      have hD0 : D ≠ 0 := fun h0 => hK0 (h0 ▸ hD)
      refine le_of_eq_of_le ?_ (hC x hx D hD)
      congr 2
      unfold PBK.mainD
      refine Finset.sum_congr rfl fun z hz => ?_
      have hz0 : z ≠ 0 := by
        rintro rfl
        have hr := (Polynomial.mem_nthRoots (by omega : 0 < s)).1 (Multiset.mem_toFinset.1 hz)
        rw [zero_pow hs0] at hr
        exact hD0 (by simpa using hr.symm)
      exact congrArg (fun v => G.psi (-U.betaU) ((s : ℂ) * z * x) • v) (if_neg hz0)
  · intro t t' ht ht'
    have hg := hgram t⁻¹ t'⁻¹ (inv_ne_zero ht) (inv_ne_zero ht')
    simp only [inv_inv] at hg
    show _ = _ * ‖∫ c, ⟪PBK.cvec s ut t⁻¹ c, PBK.cvec s ut t'⁻¹ c⟫_ℂ‖
    rw [hg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_self_nonneg κ), ← mul_assoc, hκκ,
      one_mul]
  · intro z hz
    unfold TBB.Ew
    rw [hbz z hz, hVec, gl_inner_self, Complex.ofReal_re, one_mul]

end

end Formalism.FourierDecayAlt.P.CutBP
end

section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt
open scoped ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

open Classical

section forms

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
  (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter)

theorem formC_zero_l (y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hy : PBL.CV (p.T.bs j) y) : p.form j hj w 0 y = 0 := by
  have h := PBL.form_slC p j hj w 0 0 y 1 PBL.cv_zero PBL.cv_zero hy
  simp only [one_smul, add_zero, one_mul] at h
  linear_combination -h

theorem formC_zero_r (x : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hx : PBL.CV (p.T.bs j) x) : p.form j hj w x 0 = 0 := by
  have h := PBL.form_srC p j hj w x 0 0 1 hx PBL.cv_zero PBL.cv_zero
  simp only [one_smul, add_zero, map_one, one_mul] at h
  linear_combination -h

theorem formC_smul_l (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : PBL.CV (p.T.bs j) x) (hy : PBL.CV (p.T.bs j) y) : p.form j hj w (c • x) y = c * p.form j hj w x y := by
  have h := PBL.form_slC p j hj w 0 x y c PBL.cv_zero hx hy
  rwa [zero_add, formC_zero_l p j hj w y hy, zero_add] at h

theorem formC_smul_r (x y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : PBL.CV (p.T.bs j) x) (hy : PBL.CV (p.T.bs j) y) : p.form j hj w x (c • y) = conj c * p.form j hj w x y := by
  have h := PBL.form_srC p j hj w x 0 y c hx PBL.cv_zero hy
  rwa [zero_add, formC_zero_r p j hj w x hx, zero_add] at h

end forms

theorem glGram : GLGram := by
  intro hA Wp Wq _ _ _ _ _ _ P p nn F Y N Cb hCb hF hnn i hi w hw hN
  have hpos : TBBx5.FormNonneg p := TBBx5.formNonneg_of hA (Formalism.FourierDecayAlt.P.pb_formPos : PBL.FormPos) p
  have hnC : 0 < TBB.normC nn w := by
    unfold TBB.normC
    refine List.prod_pos fun x hx => ?_
    obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx
    exact hnn _
  set c0 : ℝ := 1 / TBB.normC nn w with hc0
  have hc0n : 0 ≤ c0 := by positivity
  let sq : C.LPt → ℝ := fun a => Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) a)
  let u : C.LPt → (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - i) → (Wq →L[ℂ] Wp)) := fun a =>
    if ha : D.IsLocPt a i then ((sq a : ℝ) : ℂ) • KB.slv p.T F i hi w a ha.2 else 0
  have hslv : ∀ a (ha : D.IsLocPt a i), PBL.CV (p.T.bs i) (KB.slv p.T F i hi w a ha.2) :=
    fun a ha e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F i hi w a ha hF e
  have hu : ∀ a, PBL.CV (p.T.bs i) (u a) := by
    intro a
    by_cases ha : D.IsLocPt a i
    · simp only [u, dif_pos ha]; exact PBL.cv_smul _ (hslv a ha)
    · simp only [u, dif_neg ha]; exact PBL.cv_zero
  let β : (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - i) → (Wq →L[ℂ] Wp)) →
      (Wd.Ix (Fin w.length) → B.Mat P.k (P.r - i) → (Wq →L[ℂ] Wp)) → ℂ :=
    fun x y => (c0 : ℂ) * p.form i hi w x y
  have hpsd : ∀ Y' : Finset C.LPt, TB.PSDOn Y' (fun a b => β (u a) (u b)) := by
    intro Y'
    refine PBL.gram_psd (PBL.CV (S := Fin w.length) (p.T.bs i)) β PBL.cv_zero (fun x y hx hy => PBL.cv_add hx hy)
      (fun c x hx => PBL.cv_smul c hx) ?_ ?_ ?_ Y' u hu
    · intro x₁ x₂ y c h₁ h₂ hy
      simp only [β, PBL.form_slC p i hi w x₁ x₂ y c h₁ h₂ hy]; ring
    · intro x y₁ y₂ c hx h₁ h₂
      simp only [β, PBL.form_srC p i hi w x y₁ y₂ c hx h₁ h₂]; ring
    · intro x hx
      obtain ⟨ε, hε, hnv⟩ := PBL.nv_of_cv hx
      exact mul_nonneg (by exact_mod_cast hc0n) (hpos i hi w hw.1 x ε hε hnv)
  obtain ⟨H, i1, i2, i3, V, hV⟩ := Formalism.FourierDecayAlt.P.GermFibreKernels.kolmogorov _ hpsd
  refine ⟨H, i1, i2, i3, V, fun a b => ?_⟩
  rw [← hV]
  simp only [β]
  by_cases ha : D.IsLocPt a i
  · by_cases hb : D.IsLocPt b i
    · simp only [u, dif_pos ha, dif_pos hb]
      rw [formC_smul_l p i hi w _ _ _ (hslv a ha) (PBL.cv_smul _ (hslv b hb)),
        formC_smul_r p i hi w _ _ _ (hslv a ha) (hslv b hb), Complex.conj_ofReal]
      have hrr : p.RR F i w a b = p.form i hi w (KB.slv p.T F i hi w a ha.2) (KB.slv p.T F i hi w b hb.2) := by
        unfold KB.Pl.RR D.RRplace
        rw [dif_pos ⟨ha, hb⟩, dif_pos hi]
        rfl
      unfold TBB.NP
      rw [hrr, hc0]
      simp only [sq]
      push_cast
      ring
    · simp only [u, dif_neg hb]
      rw [formC_zero_r p i hi w _ (hu a)]
      unfold TBB.NP KB.Pl.RR D.RRplace
      rw [dif_neg (fun h => hb h.2)]
      simp
  · simp only [u, dif_neg ha]
    rw [formC_zero_l p i hi w _ (hu b)]
    unfold TBB.NP KB.Pl.RR D.RRplace
    rw [dif_neg (fun h => ha h.1)]
    simp

end

end Formalism.FourierDecayAlt.P.CutBP

theorem Formalism.FourierDecayAlt.P.CutBP.low_level_gram : Formalism.FourierDecayAlt.P.CutBP.GLGram := Formalism.FourierDecayAlt.P.CutBP.glGram
end

section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

theorem low_level_continuity : GLCont := by
  intro _ Wp Wq _ _ _ _ _ _ P p nn F Y N Cb _ hF _ j m hm hjm w hw _ a ha
  have hsz : D.ptSize a + m = j + m := by rw [ha.2]
  have hRR := rank_below_compact Wp Wq P p F hF (j + m) hjm w hw.1 a a m hm hsz hsz
  have hn := nPt_app_cont (P := P) (TBB.TTp p) a m
  have e1 : ContinuousOn (fun cc : ℂ × ℂ => TBB.nPt P.k P.r (TBB.TTp p) (a ++ [(m, cc.1)]))
      (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) := hn.comp continuousOn_fst (fun cc hcc => hcc.1)
  have e2 : ContinuousOn (fun cc : ℂ × ℂ => TBB.nPt P.k P.r (TBB.TTp p) (a ++ [(m, cc.2)]))
      (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) := hn.comp continuousOn_snd (fun cc hcc => hcc.2)
  have hw' : ContinuousOn (fun cc : ℂ × ℂ => ((Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (a ++ [(m, cc.1)])) *
      Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (a ++ [(m, cc.2)])) / TBB.normC nn w : ℝ) : ℂ))
      (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) :=
    Complex.continuous_ofReal.comp_continuousOn
      (((Real.continuous_sqrt.comp_continuousOn e1).mul (Real.continuous_sqrt.comp_continuousOn e2)).div_const _)
  exact hw'.mul hRR

end

end Formalism.FourierDecayAlt.P.CutBP
end

section
namespace Formalism.FourierDecayAlt.P.CutBP.GLG

open Formalism.FourierDecayAlt

noncomputable section

theorem zpow_two_nat (x : ℝ) (e : ℤ) (n : ℕ) (he : e = 2 * (n : ℤ)) : x ^ e = (x ^ n) ^ 2 := by
  subst he
  rw [show (2 * (n : ℤ)) = ((2 * n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul']

theorem nPt_block {P : M.Par} (TT : ℝ) (b m : ℕ) (hb : 1 ≤ b) (hi : b + (m + 2) - 1 ≤ P.r) (h : C.LPt)
    (hh : D.ptSize h = b - 1) (t c : ℂ) :
    TBB.nPt P.k P.r TT (h ++ [(m + 1, t), (1, c)]) =
      C.nAux P.k P.r 0 (fun _ _ => 1) 1 h *
        ((‖t‖ ^ ((m + 1) * (U.Mlev P.k (P.r - (b + (m + 2) - 1)) + m))) ^ 2 *
          (‖c‖ ^ (U.Mlev P.k (P.r - (b + (m + 2) - 1)) - 2)) ^ 2) := by
  have e : h ++ [(m + 1, t), (1, c)] = (h ++ [(m + 1, t)]) ++ [(1, c)] := by simp
  have hs1 : D.ptSize (h ++ [(m + 1, t)]) = b - 1 + (m + 1) := by
    simp only [D.ptSize, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] at hh ⊢
    omega
  unfold TBB.nPt
  rw [e, PBD.weight_product_append, PBD.weight_product_append, PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 _ h 1 le_rfl (by omega), hs1, hh]
  simp only [C.nAux, one_mul, mul_one]
  rw [if_neg (by omega), if_neg (by omega), mul_assoc]
  congr 2
  · apply zpow_two_nat
    unfold C.Mlev U.Mlev
    have e1 : 1 + (b - 1) + (m + 1) - 1 = b + m := by omega
    rw [e1]
    push_cast [Nat.cast_sub (show b + (m + 2) - 1 ≤ P.r from hi), Nat.cast_sub (show b + m ≤ P.r + 1 by omega)]
    rw [Nat.cast_sub (show 1 ≤ b + (m + 2) by omega)]
    push_cast
    ring
  · apply zpow_two_nat
    unfold C.Mlev U.Mlev
    have e1 : 1 + (b - 1 + (m + 1)) + 1 - 1 = b + (m + 2) - 1 := by omega
    rw [e1]
    have h3 : 2 ≤ P.k + 2 * (P.r - (b + (m + 2) - 1)) + 3 := by omega
    push_cast [Nat.cast_sub h3, Nat.cast_sub hi]
    rw [Nat.cast_sub (show 1 ≤ b + (m + 2) by omega)]
    push_cast
    ring

theorem nPt_long {P : M.Par} (TT : ℝ) (b m : ℕ) (hb : 1 ≤ b) (hi : b + (m + 2) - 1 ≤ P.r) (h : C.LPt)
    (hh : D.ptSize h = b - 1) (z : ℂ) :
    TBB.nPt P.k P.r TT (h ++ [(m + 2, z)]) =
      C.nAux P.k P.r 0 (fun _ _ => 1) 1 h * (‖z‖ ^ ((m + 2) * (U.Mlev P.k (P.r - (b + (m + 2) - 1)) + m - 1))) ^ 2 := by
  unfold TBB.nPt
  rw [PBD.weight_product_append, PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 _ h 1 le_rfl (by omega), hh]
  simp only [C.nAux, one_mul, mul_one]
  rw [if_neg (by omega)]
  congr 1
  apply zpow_two_nat
  unfold C.Mlev U.Mlev
  have e1 : 1 + (b - 1) + (m + 2) - 1 = b + (m + 2) - 1 := by omega
  rw [e1]
  have h3 : 1 ≤ P.k + 2 * (P.r - (b + (m + 2) - 1)) + 3 + m := by omega
  push_cast [Nat.cast_sub h3, Nat.cast_sub hi]
  rw [Nat.cast_sub (show 1 ≤ b + (m + 2) by omega)]
  push_cast
  ring

end

end Formalism.FourierDecayAlt.P.CutBP.GLG
end

section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

namespace GLG

theorem rr_congr_belowG {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) {F F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef p.T.base F)
    (hE : ∀ g ∈ B.GV P.k P.r, F g = F₂ g) (i : ℕ) (hi : i ≤ P.r) (hi1 : 1 ≤ i) (w : List C.Letter)
    (a b : C.LPt) : p.RR F i w a b = p.RR F₂ i w a b := by
  by_cases hl : D.IsLocPt a i ∧ D.IsLocPt b i
  · unfold KB.Pl.RR D.RRplace
    rw [dif_pos hl, dif_pos hl, dif_pos hi, dif_pos hi]
    have hU : ∀ (e : Wd.Ix (Fin w.length)), ∀ g ∈ B.GV P.k P.r,
        D.uwG P.k P.r p.T.base.z p.T.base.z' F₂ i hi w e g = D.uwG P.k P.r p.T.base.z p.T.base.z' F i hi w e g :=
      fun e g hg => (Formalism.FourierDecayAlt.P.CutEXUw.uwG_congrG p.T.base.z p.T.base.z' i hi isOpen_univ
        (fun x _ hx => (hE x hx).symm) w e g (Set.mem_univ _) hg)
    have hS : ∀ (q : C.LPt), D.IsLocPt q i → ∀ (e : Wd.Ix (Fin w.length)),
        ∀ γ ∈ B.GV P.k (P.r - D.ptSize q),
        D.sliceAt P.k P.r p.T.base.z p.T.base.z' (D.uwG P.k P.r p.T.base.z p.T.base.z' F i hi w e) q γ =
          D.sliceAt P.k P.r p.T.base.z p.T.base.z' (D.uwG P.k P.r p.T.base.z p.T.base.z' F₂ i hi w e) q γ := by
      intro q hq e γ hγ
      have h1 := Formalism.FourierDecayAlt.P.PBG.sliceAt_lincomb P.k P.r Wp Wq p.T F hF i hi hi1 q hq ({()} : Finset Unit)
        (fun _ => 1) (fun _ => w) (fun _ => e) (D.uwG P.k P.r p.T.base.z p.T.base.z' F₂ i hi w e)
        (fun g hg _ => by simp [hU e g hg]) γ hγ
      simp only [Finset.sum_singleton, one_smul] at h1
      exact h1.symm
    refine Formalism.FourierDecayAlt.P.PBG.formLev_congrGV p.T _ _ w _ _ _ _ (fun e g hg => ?_) (fun e g hg => ?_)
    · simp only [D.castF]
      exact hS a hl.1 e _ (Formalism.FourierDecayAlt.P.PBE.castM_GV _ hg)
    · simp only [D.castF]
      exact hS b hl.2 e _ (Formalism.FourierDecayAlt.P.PBE.castM_GV _ hg)
  · rw [PBL.rr_zero_of_not p F i w a b hl, PBL.rr_zero_of_not p F₂ i w a b hl]

def PP (m : ℕ) (h : C.LPt) (x Dv : ℂ) : Option ℂ → C.LPt
  | none => h ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * Dv)]
  | some z => h ++ [(m + 2, z)]

def qG (m : ℕ) (x Dv : ℂ) : Option ℂ → (ℂ × ℂ) ⊕ ℂ
  | none => Sum.inl (x⁻¹, x ^ (m + 1) * Dv)
  | some z => Sum.inr z

theorem PP_eq (m : ℕ) (h : C.LPt) (x Dv : ℂ) (j : Option ℂ) : PP m h x Dv j = FormNormSumIdentities.ptG h m (qG m x Dv j) := by
  cases j <;> rfl

theorem mem_root {m : ℕ} {a z : ℂ} : z ∈ G.rootSet (m + 2) a ↔ z ^ (m + 2) = a :=
  FormNormSumIdentities.mem_rootSet4 (by omega)

theorem isLocPt_PP (m : ℕ) (b : ℕ) (hb : 1 ≤ b) (h : C.LPt) (hh : D.IsLocPt h (b - 1)) (x Dv : ℂ) (hx : x ≠ 0)
    (hD : Dv ≠ 0) (j : Option ℂ) (hj : j ∈ Finset.insertNone (G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv))) :
    D.IsLocPt (PP m h x Dv j) (b + (m + 2) - 1) := by
  obtain ⟨hloc, hsz⟩ := hh
  cases j with
  | none =>
    refine ⟨fun y hy => ?_, ?_⟩
    · simp only [PP, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hy | rfl | rfl
      · exact hloc y hy
      · exact ⟨by omega, inv_ne_zero hx⟩
      · exact ⟨le_rfl, mul_ne_zero (pow_ne_zero _ hx) hD⟩
    · simp [PP, D.ptSize, List.map_append, List.sum_append] at hsz ⊢; omega
  | some z =>
    have hj' : z ∈ G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv) := Finset.mem_insertNone.1 hj z rfl
    have hz := mem_root.1 hj'
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega)] at hz
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hD hz.symm
    refine ⟨fun y hy => ?_, ?_⟩
    · simp only [PP, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hy | rfl
      · exact hloc y hy
      · exact ⟨by omega, hz0⟩
    · simp [PP, D.ptSize, List.map_append, List.sum_append] at hsz ⊢; omega

theorem okG_qG (m : ℕ) (K : Set ℂ) (x Dv : ℂ) (hx : x ≠ 0) (hD : Dv ∈ K) (j : Option ℂ)
    (hj : j ∈ Finset.insertNone (G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv))) : FormNormSumIdentities.okG m K (qG m x Dv j) := by
  cases j with
  | none =>
    refine ⟨inv_ne_zero hx, ?_⟩
    have e : x ^ (m + 1) * Dv * x⁻¹ ^ (m + 1) = Dv := by rw [inv_pow]; field_simp
    show x ^ (m + 1) * Dv * x⁻¹ ^ (m + 1) ∈ K
    rw [e]; exact hD
  | some z =>
    have hj' : z ∈ G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv) := Finset.mem_insertNone.1 hj z rfl
    exact ⟨Dv, hD, mem_root.1 hj'⟩

end GLG

namespace GLG

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem rr_eq_formLev (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (i : ℕ) (hi : i ≤ P.r)
    (w : List C.Letter) (a b : C.LPt) (ha : D.IsLocPt a i) (hb : D.IsLocPt b i) :
    p.RR F i w a b = D.formLev p.T (M.sgn P p.l0) ⟨i, by omega⟩ w (KB.slv p.T F i hi w a ha.2)
      (KB.slv p.T F i hi w b hb.2) := by
  unfold KB.Pl.RR D.RRplace
  rw [dif_pos ⟨ha, hb⟩, dif_pos hi]
  rfl

def lam (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (w : List C.Letter) (a : C.LPt) : ℝ :=
  √(TBB.nPt P.k P.r (TBB.TTp p) a) / √(TBB.normC nn w)

theorem normC_pos (nn : ℝ → ℝ) (hnn : ∀ y, 0 < nn y) (w : List C.Letter) : 0 < TBB.normC nn w := by
  unfold TBB.normC
  refine List.prod_pos fun x hx => ?_
  obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx
  exact hnn _

theorem np_eq_lam (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (hnn : ∀ y, 0 < nn y) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (i : ℕ) (w : List C.Letter) (a b : C.LPt) :
    TBB.NP p nn F i w a b = ((lam p nn w a * lam p nn w b : ℝ) : ℂ) * p.RR F i w a b := by
  unfold TBB.NP lam
  congr 2
  have hc := normC_pos nn hnn w
  rw [div_mul_div_comm, Real.mul_self_sqrt hc.le]

theorem np_PP (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (hnn : ∀ y, 0 < nn y) (F F' : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (w : List C.Letter) (b m : ℕ) (hb : 1 ≤ b) (hi : b + (m + 2) - 1 ≤ P.r)
    (hRR : ∀ a a', p.RR F (b + (m + 2) - 1) w a a' = p.RR F' (b + (m + 2) - 1) w a a')
    (h : C.LPt) (hh : D.IsLocPt h (b - 1)) (hsz : D.ptSize h + (m + 2) = b + (m + 2) - 1)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (Φ : G.Mat (m + 2) → V)
    (K : Set ℂ)
    (hker : ∀ q1 q2, FormNormSumIdentities.okG m K q1 → FormNormSumIdentities.okG m K q2 →
      D.formLev p.T (M.sgn P p.l0) ⟨b + (m + 2) - 1, by omega⟩ w
        (KB.slv p.T F' (b + (m + 2) - 1) hi w (FormNormSumIdentities.ptG h m q1) (by rw [FormNormSumIdentities.ptSize_ptG, hsz]))
        (KB.slv p.T F' (b + (m + 2) - 1) hi w (FormNormSumIdentities.ptG h m q2) (by rw [FormNormSumIdentities.ptSize_ptG, hsz])) =
      Bf (FormNormSumIdentities.yG U.betaU m Φ q1) (FormNormSumIdentities.yG U.betaU m Φ q2))
    (x Dv : ℂ) (hx : x ≠ 0) (hDK : Dv ∈ K) (hD : Dv ≠ 0) :
    ∀ j ∈ Finset.insertNone (G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv)),
    ∀ l ∈ Finset.insertNone (G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv)),
      TBB.NP p nn F (b + (m + 2) - 1) w (PP m h x Dv j) (PP m h x Dv l) =
        Bf (((lam p nn w (PP m h x Dv j) : ℝ) : ℂ) • FormNormSumIdentities.yG U.betaU m Φ (qG m x Dv j))
          (((lam p nn w (PP m h x Dv l) : ℝ) : ℂ) • FormNormSumIdentities.yG U.betaU m Φ (qG m x Dv l)) := by
  intro j hj l hl
  have hPj := isLocPt_PP m b hb h hh x Dv hx hD j hj
  have hPl := isLocPt_PP m b hb h hh x Dv hx hD l hl
  rw [np_eq_lam p nn hnn, hRR, rr_eq_formLev p F' _ hi w _ _ hPj hPl,
    FormNormSumIdentities.slv_congr _ _ _ _ _ (PP_eq m h x Dv j) _ (by rw [FormNormSumIdentities.ptSize_ptG, hsz]),
    FormNormSumIdentities.slv_congr _ _ _ _ _ (PP_eq m h x Dv l) _ (by rw [FormNormSumIdentities.ptSize_ptG, hsz]),
    hker _ _ (okG_qG m K x Dv hx hDK j hj) (okG_qG m K x Dv hx hDK l hl)]
  rw [LinearMap.map_smulₛₗ, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, Complex.conj_ofReal]
  push_cast
  ring

end GLG

namespace GLG

def aC (m : ℕ) (x : ℂ) : Option ℂ → ℂ
  | none => (((Real.pi ^ (m + 1))⁻¹ * ‖x‖ ^ (m + 1) : ℝ) : ℂ)
  | some z => -(G.psi (-U.betaU) (((m + 2 : ℕ) : ℂ) * z * x) * (((((m + 2 : ℕ) : ℝ) * ‖z‖ ^ (m + 1))⁻¹ : ℝ) : ℂ))

theorem psi_neg_conj (β w : ℂ) : conj (G.psi (-β) w) = G.psi β w := by
  have e : G.psi (-β) w = G.psi β (-w) := by unfold G.psi; congr 1; simp [neg_mul, mul_neg]
  rw [e, FormNormSumIdentities.psi_conj, neg_neg]

theorem kapB_eq (m : ℕ) : FormNormSumIdentities.kapB m = Real.pi ^ (m + 1) * Real.pi ^ ((m + 2) * (m + 1) / 2) := by
  unfold FormNormSumIdentities.kapB
  rw [← pow_add]
  congr 1
  have e : (m + 1) * (m + 4) = (m + 2) * (m + 1) + 2 * (m + 1) := by ring
  rw [e, Nat.add_mul_div_left _ _ two_pos]
  omega

theorem conjSum_TBB {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (m M : ℕ) (hM : 2 ≤ M)
    (Φ : G.Mat (m + 2) → V) (x Dv : ℂ) (hx : x ≠ 0) (hD : Dv ≠ 0) (μ0 : ℝ) (lam : Option ℂ → ℝ)
    (h1 : lam none = μ0 * ((‖x⁻¹‖ ^ ((m + 1) * (M + m))) * ‖x ^ (m + 1) * Dv‖ ^ (M - 2)))
    (h2 : ∀ z ∈ G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv), lam (some z) = μ0 * ‖z‖ ^ ((m + 2) * (M + m - 1))) :
    ∑ j ∈ Finset.insertNone (G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv)),
        conj (aC m x j) • (((lam j : ℝ) : ℂ) • FormNormSumIdentities.yG U.betaU m Φ (qG m x Dv j)) =
      (((μ0 * Real.pi ^ ((m + 2) * (m + 1) / 2)) : ℝ) : ℂ) •
        (U.uD U.betaU m M Φ x⁻¹ Dv - U.aD U.betaU m M Φ x⁻¹ Dv) := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 2 := ⟨M - 2, by omega⟩
  have eM1 : M' + 2 - 2 = M' := by omega
  have eM2 : M' + 2 + m - 1 = M' + m + 1 := by omega
  rw [eM1] at h1
  rw [eM2] at h2
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  rw [Finset.sum_insertNone, smul_sub, sub_eq_add_neg]
  congr 1
  ·
    show conj (aC m x none) • (((lam none : ℝ) : ℂ) • (((FormNormSumIdentities.kapB m : ℝ) : ℂ) •
        G.OmBlock U.betaU (m + 1) Φ x⁻¹ (x ^ (m + 1) * Dv))) = _
    unfold U.uD
    have hc : Dv / x⁻¹ ^ (m + 1) = x ^ (m + 1) * Dv := by rw [inv_pow]; field_simp
    rw [hc, eM1]
    simp only [aC, Complex.conj_ofReal, smul_smul, ← Complex.ofReal_mul]
    congr 2
    rw [h1, kapB_eq, norm_inv]
    simp only [inv_pow, inv_inv]
    field_simp
  ·
    unfold U.aD G.mainTerm
    rw [eM1, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hz' := mem_root.1 hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega)] at hz'
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hD hz'.symm
    have hzn : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
    have hDn : ‖Dv‖ = ‖z‖ ^ (m + 2) := by
      rw [← norm_pow, hz', norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    simp only [aC, qG, FormNormSumIdentities.yG, smul_smul, ← neg_smul]
    congr 1
    rw [map_neg, map_mul, psi_neg_conj, Complex.conj_ofReal, h2 z hz, hDn]
    have hψ : ((m : ℂ) + 2) * z / x⁻¹ = ((m + 2 : ℕ) : ℂ) * z * x := by push_cast; field_simp
    rw [hψ]
    have hz1 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hzn.ne'
    have hm2 : (m : ℂ) + 2 ≠ 0 := by exact_mod_cast (show (m + 2 : ℕ) ≠ 0 by omega)
    push_cast
    field_simp
    ring

end GLG

namespace GLG

theorem lhs_eq_sum {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (m : ℕ) (h : C.LPt) (Vec : C.LPt → H)
    (x Dv : ℂ) :
    ((((Real.pi ^ (m + 2 - 1))⁻¹ * ‖x‖ ^ (m + 2 - 1) : ℝ) : ℂ) •
        Vec (h ++ [(m + 2 - 1, x⁻¹), (1, x ^ (m + 2 - 1) * Dv)])) -
      ∑ z ∈ G.rootSet (m + 2) ((-1) ^ (m + 2 + 1) * Dv),
        G.psi (-U.betaU) (((m + 2 : ℕ) : ℂ) * z * x) •
          (((((m + 2 : ℕ) : ℝ) * ‖z‖ ^ (m + 2 - 1))⁻¹ : ℝ) : ℂ) • Vec (h ++ [(m + 2, z)]) =
      ∑ j ∈ Finset.insertNone (G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv)), aC m x j • Vec (PP m h x Dv j) := by
  rw [Finset.sum_insertNone, sub_eq_add_neg, ← Finset.sum_neg_distrib, show m + 2 + 1 = m + 3 from rfl]
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [aC, PP, neg_smul, mul_smul]
  rfl

end GLG

open GLG in
theorem low_level_germ : GLGerm := by
  intro _hA Wp Wq _ _ _ _ _ _ P p nn F Y N Cb _hCb hF hnn b s hb hs hbs h hh w _hw _hN H _ _ _ Vec hVec K hK hK0
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 2 := ⟨s - 2, by omega⟩
  have hF0 := hF
  obtain ⟨hCk, hsupp, δ, hδ, hG⟩ := hF
  have heq : ∀ g ∈ B.GV P.k P.r, D.cutF p.T.base Formalism.FourierDecayAlt.P.Topx2.chi0 F δ g = F g :=
    cutF_eq_on_gv p.T.base Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation hG hδ le_rfl
  have hRR : ∀ a a', p.RR F (b + (m + 2) - 1) w a a' =
      p.RR (D.cutF p.T.base Formalism.FourierDecayAlt.P.Topx2.chi0 F δ) (b + (m + 2) - 1) w a a' :=
    fun a a' => rr_congr_belowG p hF0 (fun g hg => (heq g hg).symm) _ hbs (by omega) w a a'
  have hsz : D.ptSize h + (m + 2) = b + (m + 2) - 1 := by rw [hh.2]; omega
  have hloc : D.IsLocPt h (D.ptSize h) := ⟨hh.1, rfl⟩
  obtain ⟨V, i1, i2, i3, Bf, Φ, Cp, Cst, hCp, hBf, hker, hgerm⟩ :=
    Formalism.FourierDecayAlt.P.germ_at_place Wp Wq P p.T (M.sgn P p.l0) w F Formalism.FourierDecayAlt.P.Topx2.chi0 δ h m (b + (m + 2) - 1) hbs
      hsz hCk hsupp Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation hδ p.hl.2.2 hloc K hK hK0
  set Mv : ℕ := U.Mlev P.k (P.r - (b + (m + 2) - 1)) with hMv
  have hM : 2 ≤ Mv := by rw [hMv]; unfold U.Mlev; omega
  set nH : ℝ := C.nAux P.k P.r 0 (fun _ _ => 1) 1 h with hnH
  have hnH0 : 0 ≤ nH := Formalism.FourierDecayAlt.P.FormNormSumIdentities.weight_product_nonneg P.k P.r (fun _ _ => 1) (fun _ _ => zero_le_one) 1 h
  set μ0 : ℝ := √nH / √(TBB.normC nn w) with hμ0
  refine ⟨Cp * |μ0 * Real.pi ^ ((m + 2) * (m + 1) / 2)| * Cst, fun x hx Dv hDv => ?_⟩
  have hD0 : Dv ≠ 0 := fun e => hK0 (e ▸ hDv)
  rw [lhs_eq_sum]
  have hy := np_PP p nn hnn F _ w b m hb hbs hRR h hh hsz Bf Φ K hker x Dv hx hDv hD0
  have hle := Formalism.FourierDecayAlt.P.FormNormSumIdentities.norm_sum_le_of_form (TBB.NP p nn F (b + (m + 2) - 1) w) Vec hVec Bf Cp hCp hBf
    (Finset.insertNone (G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv))) (aC m x) (PP m h x Dv)
    (fun j => ((lam p nn w (PP m h x Dv j) : ℝ) : ℂ) • FormNormSumIdentities.yG U.betaU m Φ (qG m x Dv j)) hy
  have hl1 : lam p nn w (PP m h x Dv none) =
      μ0 * ((‖x⁻¹‖ ^ ((m + 1) * (Mv + m))) * ‖x ^ (m + 1) * Dv‖ ^ (Mv - 2)) := by
    show √(TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * Dv)])) / √(TBB.normC nn w) = _
    rw [nPt_block (TBB.TTp p) b m hb hbs h hh.2, Real.sqrt_mul hnH0, ← mul_pow, Real.sqrt_sq (by positivity), hμ0]
    ring
  have hl2 : ∀ z ∈ G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv),
      lam p nn w (PP m h x Dv (some z)) = μ0 * ‖z‖ ^ ((m + 2) * (Mv + m - 1)) := by
    intro z _
    show √(TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(m + 2, z)])) / √(TBB.normC nn w) = _
    rw [nPt_long (TBB.TTp p) b m hb hbs h hh.2, Real.sqrt_mul hnH0, Real.sqrt_sq (by positivity), hμ0]
    ring
  have hcs := conjSum_TBB m Mv hM Φ x Dv hx hD0 μ0 (fun j => lam p nn w (PP m h x Dv j)) hl1 hl2
  rw [hcs, norm_smul, Complex.norm_real, Real.norm_eq_abs] at hle
  have hg' := hgerm x⁻¹ Dv (inv_ne_zero hx) hDv
  rw [norm_inv] at hg'
  calc _ ≤ Cp * (|μ0 * Real.pi ^ ((m + 2) * (m + 1) / 2)| *
        ‖U.uD U.betaU m Mv Φ x⁻¹ Dv - U.aD U.betaU m Mv Φ x⁻¹ Dv‖) := hle
    _ ≤ Cp * (|μ0 * Real.pi ^ ((m + 2) * (m + 1) / 2)| * (Cst * ‖x‖⁻¹)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg' (abs_nonneg _)) hCp
    _ = _ := by ring

end

end Formalism.FourierDecayAlt.P.CutBP
end

section
namespace Formalism.FourierDecayAlt.P.CutBP

theorem germ_data_low_levels : GermDataLowAll :=
  germDataLowAll_of_parts low_level_gram low_level_fibre low_level_continuity low_level_germ

end Formalism.FourierDecayAlt.P.CutBP
end

section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt

theorem germ_truncation_positive (hA : P5.ThmPActual) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
    (p : KB.Pl P Wp Wq) (nn χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ)
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : KB.CptCoef p.T.base F) (hχ : C6.IsCut0 χ)
    (hnn : ∀ y, 0 < nn y) : GermCutPD p nn χ F Y K N :=
  germCutPD_of_data hA p nn χ F Y K N Cb hCb hF hχ hnn germ_data_low_levels germ_data_top_level

theorem block_growth_bound_of_compact_coef (hA : P5.ThmPActual) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ)
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hG : KB.CptCoef p.T.base G) (hnn : ∀ y, 0 < nn y) :
    TBB.BlockGrowthBound p nn G Y K N :=
  block_growth_bound_of_compact_coef_of_germ_data hA p nn G Y K N Cb hCb hG hnn germ_data_low_levels germ_data_top_level

end Formalism.FourierDecayAlt.P.CutBP
end
