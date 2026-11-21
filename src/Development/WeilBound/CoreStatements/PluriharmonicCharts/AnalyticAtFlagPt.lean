import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameLUMinorValue
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockLUFactorization
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseChartHolomorphicComposition
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFlagPointInOrbit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPointTriangularChangeOrbitStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartFirst

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace PositivityTheory.Xgp.c_unif

section Gen

variable {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem exists_inv [CompactSpace Y] [T2Space X] (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (π : Y → X)
    (hπ : HoloMap B A π) (hd : IsDegreeOff A B π 1 ∅) (hb : Function.Bijective π) :
    ∃ σ : X → Y, (∀ x, π (σ x) = x) ∧ (∀ y, σ (π y) = y) ∧ HoloMap A B σ ∧
      ∀ x k j, x ∈ (A.chart k).source → σ x ∈ (B.chart j).source →
        Function.Injective (fderiv ℂ (B.chart j ∘ σ ∘ (A.chart k).symm) (A.chart k x)) := by
  obtain ⟨hπc, hπa⟩ := hπ
  obtain ⟨-, -, -, -, -, hdd⟩ := hd
  let Φ : Y ≃ₜ X := (show Continuous (Equiv.ofBijective π hb) from hπc).homeoOfEquivCompactToT2
  let Ψ : Fin A.n → Fin B.n → OpenPartialHomeomorph (Fin e → ℂ) (Fin e → ℂ) :=
    fun i j => (B.chart j).symm.trans (Φ.toOpenPartialHomeomorph.trans (A.chart i))
  have key : ∀ i j z, z ∈ (Ψ i j).target →
      AnalyticAt ℂ (Ψ i j).symm z ∧ Function.Injective (fderiv ℂ (Ψ i j).symm z) := by
    intro i j z hz
    have hw : (Ψ i j).symm z ∈ (Ψ i j).source := (Ψ i j).map_target hz
    have han : AnalyticAt ℂ (Ψ i j) ((Ψ i j).symm z) := hπa j i _ ⟨hw.1, hw.2.2⟩
    have hdet : LinearMap.det (fderiv ℂ (Ψ i j) ((Ψ i j).symm z) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 :=
      hdd j i _ hw.1 (by simp) hw.2.2
    let L : (Fin e → ℂ) ≃L[ℂ] (Fin e → ℂ) :=
      (LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv
    have hL : fderiv ℂ (Ψ i j) ((Ψ i j).symm z) = (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :=
      ContinuousLinearMap.ext fun v => rfl
    have hsymm : AnalyticAt ℂ (Ψ i j).symm z := (Ψ i j).analyticAt_symm hz han hL
    have hder : HasFDerivAt (Ψ i j).symm (L.symm : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) z :=
      (Ψ i j).hasFDerivAt_symm hz (hL ▸ han.differentiableAt.hasFDerivAt)
    refine ⟨hsymm, ?_⟩
    rw [hder.fderiv]
    exact L.symm.injective
  refine ⟨⇑Φ.symm, fun x => Φ.apply_symm_apply x, fun y => Φ.symm_apply_apply y,
    ⟨Φ.symm.continuous, ?_⟩, ?_⟩
  · intro i j z hz
    exact (key i j z ⟨⟨hz.1, Set.mem_univ _⟩, hz.2⟩).1
  · intro x k j hxk hxj
    have hz : A.chart k x ∈ (Ψ k j).target := by
      refine ⟨⟨(A.chart k).map_source hxk, Set.mem_univ _⟩, ?_⟩
      show Φ.symm ((A.chart k).symm (A.chart k x)) ∈ (B.chart j).source
      rw [(A.chart k).left_inv hxk]
      exact hxj
    exact (key k j _ hz).2

theorem holoOn_comp {A : FinHolAtlas e X} {B : FinHolAtlas e' Y} {h : Y → X} (hh : HoloMap B A h) {W : Set X}
    {f : X → ℂ} (hf : A.HoloOn W f) : B.HoloOn (h ⁻¹' W) (fun y => f (h y)) := by
  intro j z hz
  obtain ⟨hzt, hzW⟩ := hz
  obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm z))
  obtain ⟨hhc, hha⟩ := hh
  have hin : AnalyticAt ℂ ((A.chart k) ∘ h ∘ (B.chart j).symm) z := hha j k z ⟨hzt, hk⟩
  have hout : AnalyticAt ℂ (f ∘ (A.chart k).symm) (((A.chart k) ∘ h ∘ (B.chart j).symm) z) := by
    apply hf k
    refine ⟨(A.chart k).map_source hk, ?_⟩
    show (A.chart k).symm (A.chart k (h ((B.chart j).symm z))) ∈ W
    rw [(A.chart k).left_inv hk]
    exact hzW
  have hev : ∀ᶠ w in 𝓝 z, h ((B.chart j).symm w) ∈ (A.chart k).source := by
    have hc : ContinuousAt (h ∘ (B.chart j).symm) z :=
      hhc.continuousAt.comp ((B.chart j).continuousAt_symm hzt)
    exact hc.preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)
  refine (hout.comp hin).congr ?_
  filter_upwards [hev] with w hw
  simp only [Function.comp_apply]
  rw [(A.chart k).left_inv hw]

theorem holoOn_mono {A : FinHolAtlas e X} {W W' : Set X} {f : X → ℂ} (h : A.HoloOn W f) (s : W' ⊆ W) :
    A.HoloOn W' f := by
  intro j
  exact (h j).mono (fun z hz => ⟨hz.1, s hz.2⟩)

theorem holoOn_at {A : FinHolAtlas e X} {W : Set X} {f : X → ℂ} (h : A.HoloOn W f) {x : X} (hx : x ∈ W) {k : Fin A.n}
    (hk : x ∈ (A.chart k).source) : AnalyticAt ℂ (fun w => f ((A.chart k).symm w)) (A.chart k x) := by
  have := h k (A.chart k x) ⟨(A.chart k).map_source hk, by
    show (A.chart k).symm (A.chart k x) ∈ W
    rw [(A.chart k).left_inv hk]
    exact hx⟩
  exact this

theorem exists_holoOn_of_germ (A : FinHolAtlas e X) {x : X} {k : Fin A.n} (hk : x ∈ (A.chart k).source)
    {f : X → ℝ} {H : (Fin e → ℂ) → ℂ} (hH : AnalyticAt ℂ H (A.chart k x))
    (hf : ∀ᶠ w in 𝓝 (A.chart k x), f ((A.chart k).symm w) = (H w).re) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, f y = (G y).re := by
  have hev : ∀ᶠ w in 𝓝 (A.chart k x), AnalyticAt ℂ H w ∧ f ((A.chart k).symm w) = (H w).re :=
    hH.eventually_analyticAt.and hf
  obtain ⟨U, hU, hUo, hxU⟩ := eventually_nhds_iff.mp hev
  refine ⟨(A.chart k).source ∩ (A.chart k) ⁻¹' U, (A.chart k).isOpen_inter_preimage hUo, ⟨hk, hxU⟩,
    fun y => H (A.chart k y), ?_, ?_⟩
  · intro j z hz
    obtain ⟨hzt, hzs, hzU⟩ := hz
    have hin : AnalyticAt ℂ ((A.chart k) ∘ (A.chart j).symm) z := A.holo j k z ⟨hzt, hzs⟩
    have hout : AnalyticAt ℂ H (((A.chart k) ∘ (A.chart j).symm) z) := (hU _ hzU).1
    exact hout.comp hin
  · rintro y ⟨hy, hyU⟩
    have := (hU _ hyU).2
    rwa [(A.chart k).left_inv hy] at this

theorem isOpen_ne {A : FinHolAtlas e X} {W : Set X} (hW : IsOpen W) {T : Type} [Finite T] {f : T → X → ℂ}
    (hf : ∀ t, A.HoloOn W (f t)) : IsOpen {y | y ∈ W ∧ ∀ t, f t y ≠ 0} := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyW, hy⟩
  obtain ⟨k, hk⟩ := A.cover y
  have hcont : ∀ t, ContinuousAt (f t) y := by
    intro t
    have han : AnalyticAt ℂ (f t ∘ (A.chart k).symm) (A.chart k y) :=
      hf t k (A.chart k y) ⟨(A.chart k).map_source hk, by
        show (A.chart k).symm (A.chart k y) ∈ W
        rw [(A.chart k).left_inv hk]
        exact hyW⟩
    have hc : ContinuousAt ((f t ∘ (A.chart k).symm) ∘ (A.chart k)) y :=
      han.continuousAt.comp ((A.chart k).continuousAt hk)
    refine hc.congr ?_
    filter_upwards [(A.chart k).open_source.mem_nhds hk] with z hz
    simp only [Function.comp_apply, (A.chart k).left_inv hz]
  have hev : ∀ᶠ z in 𝓝 y, ∀ t, f t z ≠ 0 := by
    rw [Filter.eventually_all]
    intro t
    exact (hcont t).eventually_ne (hy t)
  filter_upwards [hW.mem_nhds hyW, hev] with z hz1 hz2
  exact ⟨hz1, hz2⟩

end Gen

section Mat

variable {N j : ℕ}

theorem lower_left_zero {H X D : Matrix (Fin N) (Fin N) ℂ} (hH : IsBlockDiag j H) (hd : H.det ≠ 0)
    (hD : IsBlockDiag j D) (ht : (H⁻¹ * (X * H + D)).BlockTriangular id) (a b : Fin N) (ha : N - j ≤ (a : ℕ))
    (hb : (b : ℕ) < N - j) : X a b = 0 := by
  classical
  have hunit : IsUnit H.det := isUnit_iff_ne_zero.mpr hd
  letI : Invertible H := Matrix.invertibleOfIsUnitDet _ hunit
  have h1 : H.BlockTriangular (fun i : Fin N => if (i : ℕ) < N - j then 0 else 1) := by
    intro r s hrs
    apply hH
    by_cases hr : (r : ℕ) < N - j <;> by_cases hs : (s : ℕ) < N - j <;> simp [hr, hs] at hrs ⊢
  have h2 : H.BlockTriangular (fun i : Fin N => if (i : ℕ) < N - j then 1 else 0) := by
    intro r s hrs
    apply hH
    by_cases hr : (r : ℕ) < N - j <;> by_cases hs : (s : ℕ) < N - j <;> simp [hr, hs] at hrs ⊢
  have g1 := Matrix.blockTriangular_inv_of_blockTriangular h1
  have g2 := Matrix.blockTriangular_inv_of_blockTriangular h2
  have hI : ∀ r s : Fin N, ¬((r : ℕ) < N - j ↔ (s : ℕ) < N - j) → H⁻¹ r s = 0 := by
    intro r s hrs
    by_cases hr : (r : ℕ) < N - j <;> by_cases hs : (s : ℕ) < N - j
    · exact absurd (iff_of_true hr hs) hrs
    · exact g2 (by simp [hr, hs])
    · exact g1 (by simp [hr, hs])
    · exact absurd (iff_of_false hr hs) hrs
  have hY : ∀ c d : Fin N, N - j ≤ (c : ℕ) → (d : ℕ) < N - j → (H⁻¹ * X * H) c d = 0 := by
    intro c d hc hdd
    have hT := ht (show d < c from Fin.lt_def.mpr (by omega))
    rw [Matrix.mul_add, Matrix.add_apply, ← Matrix.mul_assoc] at hT
    have hHD : (H⁻¹ * D) c d = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero (fun m _ => ?_)
      by_cases hm : (m : ℕ) < N - j
      · rw [hI c m (fun hiff => by have := hiff.mpr hm; omega), zero_mul]
      · rw [hD m d (fun hiff => hm (hiff.mpr hdd)), mul_zero]
    rw [hHD, add_zero] at hT
    exact hT
  have hX : X = H * (H⁻¹ * X * H) * H⁻¹ := by
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.mul_one]
  rw [hX, Matrix.mul_apply]
  refine Finset.sum_eq_zero (fun m _ => ?_)
  by_cases hm : (m : ℕ) < N - j
  · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro c _
    by_cases hc : (c : ℕ) < N - j
    · rw [hH a c (fun hiff => by have := hiff.mpr hc; omega), zero_mul]
    · rw [hY c m (by omega) hm, mul_zero]
  · rw [hI m b (fun hiff => hm (hiff.mpr hb)), mul_zero]

theorem eq_zero_of_lower {L D : Matrix (Fin N) (Fin N) ℂ} (hL : IsLowerUni L) (hD : ∀ a b, a ≤ b → D a b = 0)
    (ht : (L⁻¹ * D).BlockTriangular id) : D = 0 := by
  classical
  obtain ⟨hL1, hL2⟩ := hL
  have hlow : L.BlockTriangular OrderDual.toDual :=
    fun i j hij => hL2 i j (OrderDual.toDual_lt_toDual.mp hij)
  have hunit : IsUnit L.det := by
    rw [Matrix.det_of_isLowerTriangular L hlow]
    simp [hL1]
  letI : Invertible L := Matrix.invertibleOfIsUnitDet _ hunit
  have hlow' : L⁻¹.BlockTriangular OrderDual.toDual :=
    Matrix.blockTriangular_inv_of_blockTriangular hlow
  have hM : L⁻¹ * D = 0 := by
    ext a b
    rw [Matrix.zero_apply]
    rcases lt_or_ge b a with hba | hab
    · exact ht hba
    · rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero (fun c _ => ?_)
      rcases lt_or_ge a c with hac | hca
      · rw [hlow' (OrderDual.toDual_lt_toDual.mpr hac), zero_mul]
      · rw [hD c b (hca.trans hab), mul_zero]
  have h2 := congrArg (fun M => L * M) hM
  simpa [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit] using h2

theorem fderiv_mul_of {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {P Q : E → Matrix (Fin N) (Fin N) ℂ}
    {w : E} (hP : ∀ a b, DifferentiableAt ℂ (fun u => P u a b) w) (hQ : ∀ a b, DifferentiableAt ℂ (fun u => Q u a b) w)
    (v : E) : (Matrix.of fun a b => fderiv ℂ (fun u => (P u * Q u) a b) w v) =
      (Matrix.of fun a b => fderiv ℂ (fun u => P u a b) w v) * Q w +
        P w * Matrix.of fun a b => fderiv ℂ (fun u => Q u a b) w v := by
  ext a b
  have h1 : HasFDerivAt (fun u => ∑ c, P u a c * Q u c b)
      (∑ c, (P w a c • fderiv ℂ (fun u => Q u c b) w + Q w c b • fderiv ℂ (fun u => P u a c) w)) w :=
    HasFDerivAt.fun_sum fun c _ => (hP a c).hasFDerivAt.fun_mul (hQ c b).hasFDerivAt
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply]
  rw [h1.fderiv, ← Finset.sum_add_distrib]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun c _ => by ring

end Mat

end PositivityTheory.Xgp.c_unif
end
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace PositivityTheory.Xgp.c_unif

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {M : FlagModel y Ψ N j} {n : ℕ}

theorem analyticAt_flagPt {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (F : FrameData ι Ψ N M.Ω M.blk)
    {b : E → (Σ k, baseIdx ι M.blk k) → ℂ} {h : Ψ → E → Matrix (Fin N) (Fin N) ℂ} {w : E}
    (hb : ∀ q, AnalyticAt ℂ (fun u => b u q) w) (hv : ∀ q I, AnalyticAt ℂ (fun u => valAt M.x (F.u q I) (b u)) w)
    (hh : ∀ τ r s, AnalyticAt ℂ (fun u => h τ u r s) w) (q : Σ k, ι k) :
    AnalyticAt ℂ (fun u => FC.flagPt M F (b u) (fun τ => h τ u) q) w := by
  by_cases hk : ∀ p, M.blk p ≠ some q.1
  · simp only [FC.flagPt, dif_pos hk]
    exact hb _
  · simp only [FC.flagPt, dif_neg hk]
    exact Finset.analyticAt_fun_sum _ fun I _ => (hv q I).mul
      (Fib.analyticAt_minorIJ_of_entries _ w (hh _) _ _)

variable (BM : BaseMetric M n) {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {pr : X → BM.Rb.X}

theorem bvec_holo (hp : HoloMap A BM.Rb.A pr) {W : Set X} (hW : IsOpen W) {l : Fin BM.q}
    (hl : ∀ x ∈ W, pr x ∈ BM.O l) :
    (∀ q, A.HoloOn W fun x => FC.bvec BM l (pr x) q) ∧
      ∀ s : M.Ω, (∀ b ∈ BM.O l, RegAt M.x (mCoordIdeal (FC.bvec BM l b)) s) →
        A.HoloOn W fun x => valAt M.x s (FC.bvec BM l (pr x)) := by
  have key := fun k => GlobalTheory.T.base_chart_holomorphic_composition K ι Φ y Ψ N j M n BM l e ((A.chart k).target ∩ (A.chart k).symm ⁻¹' W)
    (pr ∘ (A.chart k).symm) ((A.chart k).isOpen_inter_preimage_symm hW)
    (hp.1.comp_continuousOn ((A.chart k).continuousOn_symm.mono Set.inter_subset_left))
    (fun m => (hp.2 k m).mono fun t ht => ⟨ht.1.1, ht.2⟩) (fun u hu => hl _ hu.2)
  exact ⟨fun q k => (key k).1 q, fun s hs k => (key k).2 s hs⟩

theorem step_of_orbit {F : FrameData ι Ψ N M.Ω M.blk} {b : (Σ k, baseIdx ι M.blk k) → ℂ} {z : (Σ k, ι k) → ℂ}
    {h : Ψ → Matrix (Fin N) (Fin N) ℂ} (ho : SameOrbit z (FC.flagPt M F b h)) (p : Ψ × Fin N) (k : K)
    (hk : M.blk p = some k) : ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k,
      z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) b * minorIJ (h p.1) I (stepCols N j p.2) := by
  obtain ⟨c, hc, rfl⟩ := ho
  exact ⟨c k, hc k, fun m => by rw [← FC.flagPt_step M F b h hk m]⟩

theorem lowMat_props (c : LowIdx Ψ N j → ℂ) (τ : Ψ) : IsBlockDiag j (lowMat c τ) ∧ IsLowerUni (lowMat c τ) :=
  ⟨fun a b h => (dif_neg fun e => h e.2).trans (if_neg fun e => h (by rw [e])),
    fun _ => (dif_neg fun e => lt_irrefl _ e.1).trans (if_pos rfl),
    fun _ _ h => (dif_neg fun e => lt_asymm h e.1).trans (if_neg h.ne)⟩

theorem lowMat_eq {c : LowIdx Ψ N j → ℂ} {τ : Ψ} {L : Matrix (Fin N) (Fin N) ℂ} (hb : IsBlockDiag j L)
    (hL : IsLowerUni L) (h : ∀ (a b : Fin N) (e : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)), c ⟨(τ, a, b), e⟩ = L a b) :
    lowMat c τ = L := by
  ext a b
  unfold lowMat
  split_ifs with h1 h2
  · exact h a b h1
  · rw [h2, hL.1]
  · rcases lt_or_gt_of_ne h2 with e | e
    · exact (hL.2 a b e).symm
    · exact (hb a b fun e' => h1 ⟨e, e'⟩).symm

theorem exists_holo_flags (hp : HoloMap A BM.Rb.A pr) {W : Set X} (hW : IsOpen W) {z : X → (Σ k, ι k) → ℂ}
    (hz : ∀ q, A.HoloOn W fun x => z x q) (hm : ∀ x ∈ W, z x ∈ mcPts (mCoordIdeal y))
    (hb : ∀ x ∈ W, SameOrbit (basePart M.blk (z x)) (BM.Rb.lift (pr x) (pr x))) {l : Fin BM.q}
    (hl : ∀ x ∈ W, pr x ∈ BM.O l) {x₀ : X} (hx₀ : x₀ ∈ W) :
    ∃ W' : Set X, IsOpen W' ∧ x₀ ∈ W' ∧ W' ⊆ W ∧ ∃ (h₀ : Ψ → Matrix (Fin N) (Fin N) ℂ)
      (L : Ψ → X → Matrix (Fin N) (Fin N) ℂ), (∀ τ, IsBlockDiag j (h₀ τ) ∧ (h₀ τ).det ≠ 0) ∧
      (∀ τ a b, A.HoloOn W' fun x => L τ x a b) ∧ (∀ τ x, IsBlockDiag j (L τ x) ∧ IsLowerUni (L τ x)) ∧
      ∀ x ∈ W', SameOrbit (z x) (FC.flagPt M (BM.F l) (FC.bvec BM l (pr x)) fun τ => h₀ τ * L τ x) := by
  have hj := M.j_le
  have hF := BM.isFrame l
  have hg := GlobalTheory.T.base_vector_properties K ι Φ y Ψ N j M n BM l
  have hex := fun x (hx : x ∈ W) => GlobalTheory.T.exists_flag_point_in_orbit K ι Φ y Ψ N j M n BM l (pr x) (hl x hx) (z x) (hm x hx) (hb x hx)
  obtain ⟨h₀, hh₀, ho₀⟩ := hex x₀ hx₀
  let tw : Fin N → K → Ψ → Finset (Fin N) → X → ℂ := fun i k τ J x =>
    twMinor M (BM.F l) (FC.bvec BM l (pr x)) i k (h₀ τ)⁻¹ (z x) J
  have htw : ∀ i k τ J, A.HoloOn W (tw i k τ J) := by
    intro i k τ J m t ht
    have hv := fun I (q : Σ k, ι k) => (bvec_holo BM hp hW hl).2 ((BM.F l).u' I q)
      (fun b hb => ((hg b hb).2.1.2.1 q I).2) m t ht
    show AnalyticAt ℂ (fun w => tw i k τ J ((A.chart m).symm w)) t
    simp only [tw, twMinor, pluck]
    exact Finset.analyticAt_fun_sum _ fun I _ => analyticAt_const.mul
      (Finset.analyticAt_fun_sum _ fun r _ => (hv I ⟨k, r⟩).mul (hz ⟨k, r⟩ m t ht))
  let T := {pk : (Ψ × Fin N) × K // M.blk pk.1 = some pk.2}
  let den : T → X → ℂ := fun t => tw t.1.1.2 t.1.2 t.1.1.1 (stepCols N j t.1.1.2)
  have tweq : ∀ x ∈ W, ∀ h' : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ, IsBlockDiag j (h' τ)) →
      SameOrbit (z x) (FC.flagPt M (BM.F l) (FC.bvec BM l (pr x)) h') → ∀ t : T, ∃ α : ℂ, α ≠ 0 ∧
        den t x = α * minorIJ ((h₀ t.1.1.1)⁻¹ * h' t.1.1.1) (stepCols N j t.1.1.2) (stepCols N j t.1.1.2) := by
    intro x hx h' hb' ho t
    obtain ⟨α, hα, hzk⟩ := step_of_orbit ho t.1.1 t.1.2 t.2
    exact ⟨α, hα, GlobalTheory.T.frame_minor_value_formula K ι Φ y Ψ N j M (BM.F l) _ t.1.1 t.1.2 _ _ _ α _ hF (hg _ (hl x hx)).1
      (hg _ (hl x hx)).2.1 t.2 (hb' _) hzk⟩
  refine ⟨{x | x ∈ W ∧ ∀ t, den t x ≠ 0}, isOpen_ne hW fun t => htw _ _ _ _, ⟨hx₀, fun t => ?_⟩, fun x hx => hx.1, h₀,
    fun τ x => lowMat (fun q : LowIdx Ψ N j =>
      lowRead M (BM.F l) (FC.bvec BM l (pr x)) h₀ (z x) q.1.1 q.1.2.1 q.1.2.2) τ, hh₀, fun τ a b => ?_,
    fun τ x => lowMat_props _ _, fun x hx => ?_⟩
  · obtain ⟨α, hα, e⟩ := tweq x₀ hx₀ h₀ (fun τ => (hh₀ τ).1) ho₀ t
    rw [e, Matrix.nonsing_inv_mul _ (hh₀ _).2.isUnit, CPts.minorIJ_one, mul_one]
    exact hα
  · by_cases h1 : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
    · simp only [lowMat, dif_pos h1, lowRead]
      rcases hk : M.blk (τ, stepOf N j b) with _ | k
      · exact fun _ => analyticOnNhd_const
      · intro m t ht
        exact AnalyticAt.div (htw (stepOf N j b) k τ _ m t ⟨ht.1, ht.2.1⟩) (htw (stepOf N j b) k τ _ m t ⟨ht.1, ht.2.1⟩)
          (ht.2.2 ⟨((τ, stepOf N j b), k), hk⟩)
    · simp only [lowMat, dif_neg h1]
      exact fun _ => analyticOnNhd_const
  · obtain ⟨h', hh', ho⟩ := hex x hx.1
    have hLU : ∀ τ, ∃ L U : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j L ∧ IsLowerUni L ∧ IsBlockDiag j U ∧
        U.BlockTriangular id ∧ (∀ c, U c c ≠ 0) ∧ (h₀ τ)⁻¹ * h' τ = L * U := by
      intro τ
      refine GlobalTheory.T.block_LU_factorization N j _ hj (((hh₀ τ).1.inv (hh₀ τ).2.isUnit).mul (hh' τ).1) ?_ fun i hi => ?_
      · rw [Matrix.det_mul]
        exact mul_ne_zero (Matrix.isUnit_nonsing_inv_det _ (hh₀ τ).2.isUnit).ne_zero (hh' τ).2
      · obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 fun e => (M.blk_none (τ, i)).1 e hi
        obtain ⟨α, -, e⟩ := tweq x hx.1 h' (fun τ => (hh' τ).1) ho ⟨((τ, i), k), hk⟩
        have := hx.2 ⟨((τ, i), k), hk⟩
        rw [e] at this
        exact right_ne_zero_of_mul this
    choose L U hLb hLu hUb hUt hUd hLU using hLU
    have e1 : ∀ τ, lowMat (fun q : LowIdx Ψ N j =>
        lowRead M (BM.F l) (FC.bvec BM l (pr x)) h₀ (z x) q.1.1 q.1.2.1 q.1.2.2) τ = L τ := fun τ =>
      lowMat_eq (hLb τ) (hLu τ) fun a b e => LowRead.main K ι Φ y Ψ N j M (BM.F l) _ h₀ τ a b (z x) (h' τ) (L τ) (U τ)
        hF (hg _ (hl x hx.1)).1 (hg _ (hl x hx.1)).2.1 (hh' τ).1 (hLU τ) (hLb τ) (hLu τ) (hUb τ) (hUt τ)
        (fun c _ => hUd τ c) e.1 e.2 fun k hk => step_of_orbit ho (τ, stepOf N j b) k hk
    simp only [e1]
    have e2 : h' = fun τ => (h₀ τ * L τ) * U τ := funext fun τ => by
      rw [Matrix.mul_assoc, ← hLU, Matrix.mul_nonsing_inv_cancel_left _ _ (hh₀ τ).2.isUnit]
    refine orbit_trans ho ?_
    rw [e2]
    refine GlobalTheory.T.flag_point_triangular_change_orbit K ι Φ y Ψ N j M _ _ (fun τ => h₀ τ * L τ) U fun τ => ⟨hUb τ, hUt τ, ?_⟩
    rw [Matrix.det_of_upperTriangular (hUt τ)]
    exact Finset.prod_ne_zero_iff.2 fun c _ => hUd τ c

end PositivityTheory.Xgp.c_unif
end
end
