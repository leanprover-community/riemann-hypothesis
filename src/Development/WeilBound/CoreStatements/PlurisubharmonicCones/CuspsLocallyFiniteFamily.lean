import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicFamilySmoothEntriesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeGramDeterminant
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.UniLatA

section
open Matrix Filter Topology

namespace LevelTowerAlt.LocFin

variable {Λ : Type} [AddCommGroup Λ] {N m : ℕ}

noncomputable def coords (e : Module.Basis (Fin N) ℤ Λ) (v : Fin m → Λ) : Matrix (Fin m) (Fin N) ℤ :=
  Matrix.of fun i k => e.repr (v i) k

theorem repr_sum (e : Module.Basis (Fin N) ℤ Λ) (v : Fin m → Λ) (y : Fin m → ℤ) :
    (fun k => e.repr (∑ i, y i • v i) k) = (coords e v)ᵀ *ᵥ y := by
  funext k
  simp [coords, mulVec, dotProduct, map_sum, Finsupp.finset_sum_apply, mul_comm]

theorem eq_of_repr (e : Module.Basis (Fin N) ℤ Λ) {x y : Λ}
    (h : (fun k => e.repr x k) = fun k => e.repr y k) : x = y :=
  e.repr.injective (Finsupp.ext fun k => congrFun h k)

theorem det_ne_zero (e : Module.Basis (Fin N) ℤ Λ) {v : Fin m → Λ} (hv : LinearIndependent ℤ v) :
    (coords e v * (coords e v)ᵀ).det ≠ 0 := by
  intro h
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have h1 : ((coords e v)ᵀ *ᵥ y) ⬝ᵥ ((coords e v)ᵀ *ᵥ y) = 0 := by
    have : ((coords e v)ᵀ *ᵥ y) ⬝ᵥ ((coords e v)ᵀ *ᵥ y) = y ⬝ᵥ ((coords e v * (coords e v)ᵀ) *ᵥ y) := by
      rw [← mulVec_mulVec, dotProduct_mulVec y, ← mulVec_transpose]
    rw [this, hy, dotProduct_zero]
  have h2 : (coords e v)ᵀ *ᵥ y = 0 := dotProduct_self_eq_zero.1 h1
  have h3 : ∑ i, y i • v i = 0 := by
    apply eq_of_repr e
    rw [repr_sum, h2]
    funext k
    simp
  exact hy0 (funext (Fintype.linearIndependent_iff.1 hv y h3))

theorem exists_proj (e : Module.Basis (Fin N) ℤ Λ) {v : Fin m → Λ} {A : Set Λ}
    (hA : ∀ x, x ∈ A ↔ ∃ y : Fin m → ℤ, ∑ i, y i • v i = x)
    (hsat : ∀ (x : Λ) (n : ℤ), n ≠ 0 → n • x ∈ A → x ∈ A)
    (hd : 0 < (coords e v * (coords e v)ᵀ).det) :
    ∃ Q : Matrix (Fin N) (Fin N) ℤ, (∀ i j, |Q i j| ≤ (coords e v * (coords e v)ᵀ).det) ∧
      A = {x | Q *ᵥ (fun k => e.repr x k) = (coords e v * (coords e v)ᵀ).det • fun k => e.repr x k} := by
  obtain ⟨B, hB⟩ : ∃ B, B = coords e v := ⟨_, rfl⟩
  have hr := repr_sum e v
  rw [← hB] at hd hr ⊢
  obtain ⟨d, hdd⟩ : ∃ d, d = (B * Bᵀ).det := ⟨_, rfl⟩
  rw [← hdd] at hd ⊢
  have hQB : Bᵀ * (B * Bᵀ).adjugate * B * Bᵀ = d • Bᵀ := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, adjugate_mul, ← hdd, Matrix.mul_smul, Matrix.mul_one]
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = Bᵀ * (B * Bᵀ).adjugate * B := ⟨_, rfl⟩
  have hQQ : Q * Q = d • Q := by
    calc Q * Q = (Bᵀ * (B * Bᵀ).adjugate * B * Bᵀ) * ((B * Bᵀ).adjugate * B) := by
          rw [hQ]; simp only [Matrix.mul_assoc]
      _ = d • Q := by rw [hQB, hQ, Matrix.smul_mul, Matrix.mul_assoc]
  have hQt : Qᵀ = Q := by
    rw [hQ, transpose_mul, transpose_mul, transpose_transpose, adjugate_transpose, transpose_mul,
      transpose_transpose, Matrix.mul_assoc]
  refine ⟨Q, fun i j => ?_, ?_⟩
  · have h1 : ∑ k, Q i k ^ 2 = d * Q i i := by
      have := congrFun (congrFun hQQ i) i
      rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at this
      rw [← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      have : Q k i = Q i k := by
        have := congrFun (congrFun hQt i) k
        rwa [transpose_apply] at this
      rw [this, sq]
    have h2 : ∀ k, Q i k ^ 2 ≤ d * Q i i := fun k => h1 ▸
      Finset.single_le_sum (f := fun k => Q i k ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
    have h3 := h2 i
    have h4 := h2 j
    have h5 : Q i i ≤ d := by
      by_contra hc
      push Not at hc
      nlinarith
    have h6 : Q i j ^ 2 ≤ d ^ 2 := by nlinarith
    exact abs_le_of_sq_le_sq h6 hd.le
  · ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := (hA x).1 hx
      rw [hr, mulVec_mulVec, hQ, hQB, smul_mulVec]
    · intro hx
      refine hsat x d hd.ne' ((hA _).2 ⟨((B * Bᵀ).adjugate * B) *ᵥ (fun k => e.repr x k), ?_⟩)
      apply eq_of_repr e
      rw [hr, mulVec_mulVec, ← Matrix.mul_assoc, ← hQ, hx]
      funext k
      simp

theorem finite_sat (e : Module.Basis (Fin N) ℤ Λ) (T : ℤ) :
    {A : Set Λ | ∃ (m : ℕ) (v : Fin m → Λ), (∀ x, x ∈ A ↔ ∃ y : Fin m → ℤ, ∑ i, y i • v i = x) ∧
      (∀ (x : Λ) (n : ℤ), n ≠ 0 → n • x ∈ A → x ∈ A) ∧ 0 < (coords e v * (coords e v)ᵀ).det ∧
      (coords e v * (coords e v)ᵀ).det ≤ T}.Finite := by
  have h1 : {Q : Fin N → Fin N → ℤ | ∀ i, Q i ∈ {r : Fin N → ℤ | ∀ j, r j ∈ Set.Icc (-T) T}}.Finite :=
    Set.Finite.pi' fun _ => Set.Finite.pi' fun _ => Set.finite_Icc _ _
  have h2 := ((Set.finite_Icc 0 T).prod h1).image
    (fun p : ℤ × (Fin N → Fin N → ℤ) =>
      {x : Λ | (Matrix.of p.2) *ᵥ (fun k => e.repr x k) = p.1 • fun k => e.repr x k})
  refine h2.subset ?_
  rintro A ⟨m, v, hA, hsat, hd, hT⟩
  obtain ⟨Q, hQ, hAQ⟩ := exists_proj e hA hsat hd
  refine ⟨(_, Matrix.of.symm Q), ⟨⟨hd.le, hT⟩, fun i j => ?_⟩, hAQ.symm⟩
  exact abs_le.1 ((hQ i j).trans hT)

theorem unif_pos (S0 : Matrix (Fin N) (Fin N) ℝ) (h0 : ∀ x : Fin N → ℝ, x ≠ 0 → 0 < x ⬝ᵥ S0 *ᵥ x) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ S in 𝓝 S0, ∀ x : Fin N → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ S *ᵥ x := by
  have hc : Continuous fun z : (ℝ × Matrix (Fin N) (Fin N) ℝ) × (Fin N → ℝ) =>
      z.2 ⬝ᵥ z.1.2 *ᵥ z.2 - z.1.1 * (z.2 ⬝ᵥ z.2) :=
    (continuous_snd.dotProduct ((continuous_snd.comp continuous_fst).matrix_mulVec continuous_snd)).sub
      ((continuous_fst.comp continuous_fst).mul (continuous_snd.dotProduct continuous_snd))
  have h1 := (isCompact_sphere (0 : Fin N → ℝ) 1).eventually_forall_of_forall_eventually
    (x₀ := ((0 : ℝ), S0)) (P := fun p x => 0 < x ⬝ᵥ p.2 *ᵥ x - p.1 * (x ⬝ᵥ x)) (fun y hy => by
      have hy0 : y ≠ 0 := by
        rintro rfl
        simp at hy
      refine hc.continuousAt.eventually (lt_mem_nhds ?_)
      simpa using h0 y hy0)
  have h2 : ∀ᶠ c in 𝓝[>] (0 : ℝ), ∀ᶠ S in 𝓝 S0, ∀ x ∈ Metric.sphere (0 : Fin N → ℝ) 1,
      0 < x ⬝ᵥ S *ᵥ x - c * (x ⬝ᵥ x) := h1.curry_nhds.filter_mono nhdsWithin_le_nhds
  obtain ⟨c, hc1, hc0⟩ := (h2.and self_mem_nhdsWithin).exists
  refine ⟨c, hc0, hc1.mono fun S hS x => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h3 := hS (‖x‖⁻¹ • x) (by simp [norm_smul, hn.ne'])
  simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h3
  have h4 : 0 < ‖x‖⁻¹ * ‖x‖⁻¹ * (x ⬝ᵥ S *ᵥ x - c * (x ⬝ᵥ x)) := by linarith
  have h5 := (mul_pos_iff_of_pos_left (by positivity)).1 h4
  linarith

theorem det_bound (B : Matrix (Fin m) (Fin N) ℤ) (hB : (B * Bᵀ).det ≠ 0) (S : Matrix (Fin N) (Fin N) ℝ)
    (hS : Sᵀ = S) {c : ℝ} (hc : 0 < c) (h : ∀ x : Fin N → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ S *ᵥ x) :
    0 < (B * Bᵀ).det ∧ c ^ m * ((B * Bᵀ).det : ℝ) ≤
      (B.map (Int.castRingHom ℝ) * S * (B.map (Int.castRingHom ℝ))ᵀ).det := by
  obtain ⟨Br, hBr⟩ : ∃ Br, Br = B.map (Int.castRingHom ℝ) := ⟨_, rfl⟩
  have hdet : ((B * Bᵀ).det : ℝ) = (Br * Brᵀ).det := by
    have := (Int.castRingHom ℝ).map_det (B * Bᵀ)
    rw [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map, ← hBr] at this
    exact this
  rw [← hBr]
  have hpsd : (Br * Brᵀ).PosSemidef := by
    have := posSemidef_self_mul_conjTranspose Br
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hne : (Br * Brᵀ).det ≠ 0 := by
    rw [← hdet]; exact_mod_cast hB
  have hpd : (Br * Brᵀ).PosDef :=
    hpsd.posDef_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hne))
  have hpos : 0 < (Br * Brᵀ).det := hpd.det_pos
  refine ⟨by rw [← hdet] at hpos; exact_mod_cast hpos, ?_⟩
  have h1 : (S - c • (1 : Matrix (Fin N) (Fin N) ℝ)).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, hS, transpose_smul, transpose_one]
    · have := h x
      simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      linarith
  have h2 := h1.mul_mul_conjTranspose_same Br
  rw [conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul] at h2
  have h3 := ReciprocityTheory.L2DbarEstimates.Y.uniLat_det_le_of_sub (hpd.smul hc) h2
  rwa [det_smul, Fintype.card_fin, ← hdet] at h3

end LevelTowerAlt.LocFin
end

section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace LevelTowerAlt.LocFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

noncomputable def rg (R : RiemLat E g Λ) {N : ℕ} (e : Fin N → Λ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun k l => (R.ip (R.P (e k)) (R.P (e l))).re

theorem conj_ip (R : RiemLat E g Λ) (x y : Fin g → ℂ) : star (R.ip y x) = R.ip x y := by
  show star (x ⬝ᵥ R.Hm *ᵥ star y) = y ⬝ᵥ R.Hm *ᵥ star x
  rw [← star_dotProduct_star, star_mulVec, star_star, R.herm.eq, dotProduct_mulVec]

theorem rg_symm (R : RiemLat E g Λ) {N : ℕ} (e : Fin N → Λ) : (rg R e)ᵀ = rg R e := by
  ext k l
  simp only [rg, transpose_apply, of_apply]
  rw [← conj_ip R (R.P (e l)) (R.P (e k))]
  simp

theorem ip_sum (R : RiemLat E g Λ) {N : ℕ} (u : Fin N → Fin g → ℂ) (x y : Fin N → ℝ) :
    (R.ip (∑ k, (x k : ℂ) • u k) (∑ l, (y l : ℂ) • u l)).re = ∑ k, ∑ l, x k * (R.ip (u k) (u l)).re * y l := by
  have : R.ip (∑ k, (x k : ℂ) • u k) (∑ l, (y l : ℂ) • u l) =
      ∑ k, ∑ l, (x k : ℂ) * R.ip (u k) (u l) * (y l : ℂ) := by
    unfold RiemLat.ip
    rw [star_sum, mulVec_sum, dotProduct_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sum_dotProduct]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    rw [show star (x k : ℂ) = (x k : ℂ) from Complex.conj_ofReal _]
    ring
  rw [this, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp

theorem rg_pos (R : RiemLat E g Λ) {N : ℕ} (e : Module.Basis (Fin N) ℤ Λ) (x : Fin N → ℝ) (hx : x ≠ 0) :
    0 < x ⬝ᵥ rg R e *ᵥ x := by
  have h1 : x ⬝ᵥ rg R e *ᵥ x =
      (R.ip (∑ k, (x k : ℂ) • R.P (e k)) (∑ l, (x l : ℂ) • R.P (e l))).re := by
    rw [ip_sum]
    simp only [dotProduct, mulVec, rg, of_apply, Finset.mul_sum, mul_assoc]
  rw [h1]
  refine R.pos _ fun h0 => hx ?_
  funext k
  obtain ⟨w, hw⟩ := R.unimod.2 (e.coord k)
  have h2 : ∀ l, R.form (e l) w = -(if l = k then 1 else 0) := by
    intro l
    have ha := R.alt (e l + w)
    simp only [map_add, LinearMap.add_apply, R.alt] at ha
    have hb : R.form w (e l) = if l = k then 1 else 0 := by
      rw [hw]; simp [Finsupp.single_apply]
    linarith
  have h3 : ((∑ l, (x l : ℂ) • R.P (e l)) ⬝ᵥ R.Hm *ᵥ star (R.P w)).im = ∑ l, x l * (R.form (e l) w : ℝ) := by
    rw [sum_dotProduct, Complex.im_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_dotProduct, smul_eq_mul, Complex.im_ofReal_mul, R.im]
  rw [h0] at h3
  simp only [h2] at h3
  simpa using h3

theorem rg_coords (R : RiemLat E g Λ) {N m : ℕ} (e : Module.Basis (Fin N) ℤ Λ) (v : Fin m → Λ) :
    rg R v = (coords e v).map (Int.castRingHom ℝ) * rg R e * ((coords e v).map (Int.castRingHom ℝ))ᵀ := by
  have h : ∀ i, R.P (v i) = ∑ k, (((e.repr (v i) k : ℤ) : ℝ) : ℂ) • R.P (e k) := by
    intro i
    conv_lhs => rw [← e.sum_repr (v i)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, Complex.ofReal_intCast, Int.cast_smul_eq_zsmul]
  ext i j
  have : rg R v i j = ∑ k, ∑ l, ((e.repr (v i) k : ℤ) : ℝ) * (R.ip (R.P (e k)) (R.P (e l))).re *
      ((e.repr (v j) l : ℤ) : ℝ) := by
    rw [← ip_sum, ← h, ← h]
    rfl
  rw [this, Finset.sum_comm]
  simp only [Matrix.mul_apply, Finset.sum_mul, map_apply, transpose_apply, coords, rg, of_apply, eq_intCast]

end LevelTowerAlt.LocFin

open LevelTowerAlt.LocFin in
theorem LevelTowerAlt.cusps_locally_finite_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ), IsOpen U → IsHolFam U R → IsCMFam σ → (∀ t ∈ U, (R t).HasRank σ m) → ∀ t₀ ∈ U, ∃ (ε : ℝ) (F : Finset (Submodule (𝓞 E) Λ)), 0 < ε ∧ ∀ t ∈ U ∩ Metric.ball t₀ ε, (∀ I ∈ F, (R t).IsCusp I) ∧ ∀ I, (R t).IsCusp I → (R t).nz σ I ≤ 1 → I ∈ F := by
  intro E _ _ _ g Λ _ _ Ψ _ n U R σ m hU hHol hCM _ t₀ ht₀
  classical
  haveI := (R t₀).free
  haveI := (R t₀).fin
  let e := Module.finBasis ℤ Λ
  have hHm : ∀ i j, ContinuousOn (fun t => (R t).Hm i j) U := by
    intro i j
    obtain ⟨h1, h2⟩ := (GlobalTheory.T.holomorphic_family_smooth_entries E g Λ Ψ n U R hU hHol).1 i j
    have e : (fun t => (R t).Hm i j) = fun t => (((R t).Hm i j).re : ℂ) + (((R t).Hm i j).im : ℂ) * Complex.I := by
      funext t; exact (Complex.re_add_im _).symm
    rw [e]
    exact (Complex.continuous_ofReal.comp_continuousOn h1.continuousOn).add
      ((Complex.continuous_ofReal.comp_continuousOn h2.continuousOn).mul continuousOn_const)
  have hip : ∀ x y, ContinuousOn (fun t => (R t).ip ((R t).P x) ((R t).P y)) U := by
    intro x y
    unfold RiemLat.ip
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
    refine continuousOn_finsetSum _ fun i _ => ((continuousOn_pi.1 (hHol.2 y).continuousOn i)).mul ?_
    refine continuousOn_finsetSum _ fun j _ => (hHm i j).mul ?_
    exact (continuous_star.comp_continuousOn (continuousOn_pi.1 (hHol.2 x).continuousOn j))
  have hS : ContinuousOn (fun t => rg (R t) e) U :=
    continuousOn_pi.2 fun k => continuousOn_pi.2 fun l =>
      Complex.continuous_re.comp_continuousOn (hip (e k) (e l))
  obtain ⟨c, hc, hev⟩ := unif_pos (rg (R t₀) e) (rg_pos (R t₀) e)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
    ((hS.continuousAt (hU.mem_nhds ht₀)).eventually hev)
  obtain ⟨Dk, hDk⟩ : ∃ Dk : ℝ, Dk = |(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ)) := ⟨_, rfl⟩
  have hD0 : 0 ≤ Dk := hDk ▸ Real.rpow_nonneg (abs_nonneg _) _
  have hfin := (finite_sat e ⌈(max 1 (Dk / c)) ^ Module.finrank ℤ Λ⌉).preimage
    (SetLike.coe_injective (A := Submodule (𝓞 E) Λ)).injOn
  have hcusp : ∀ t ∈ U, ∀ t' ∈ U, ∀ I, (R t).IsCusp I → (R t').IsCusp I := fun t ht t' ht' I h =>
    ⟨h.1, h.2.1, hHol.1 t ht t' ht' ▸ h.2.2⟩
  refine ⟨ε, hfin.toFinset.filter fun I => (R t₀).IsCusp I, hε, fun t ht =>
    ⟨fun I hI => hcusp t₀ ht₀ t ht.1 I (Finset.mem_filter.1 hI).2, fun I hI hnz => ?_⟩⟩
  refine Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ?_, hcusp t ht.1 t₀ ht₀ I hI⟩
  have hinj : Function.Injective (I.subtype.toAddMonoidHom.toIntLinearMap) := Subtype.val_injective
  haveI : Module.Finite ℤ I := Module.Finite.of_injective _ hinj
  haveI : Module.IsTorsionFree ℤ I := Function.Injective.moduleIsTorsionFree _ hinj (fun _ _ => map_smul _ _ _)
  haveI : Module.Free ℤ I := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ I
  have hli : LinearIndependent ℤ fun i => (b i : Λ) :=
    b.linearIndependent.map' (I.subtype.toAddMonoidHom.toIntLinearMap) (LinearMap.ker_eq_bot.2 hinj)
  obtain ⟨hm, hdet⟩ := GlobalTheory.T.isotropic_sublattice_gram_determinant E g Λ Ψ (R t) σ I hCM hI.2.2 hI.1 _ b
  obtain ⟨⟨r, v, hv⟩, hN⟩ := GlobalTheory.T.isotropic_sublattice_covolume_positive E g Λ Ψ (R t) σ I hCM hI.2.2 hI.1
  have hnz0 := (hN r v hv).2.1
  obtain ⟨hd0, hd1⟩ := det_bound (coords e fun i => (b i : Λ)) (det_ne_zero e hli) (rg (R t) e)
    (rg_symm _ _) hc (hball t ht.2)
  rw [← rg_coords] at hd1
  have hle : Module.finrank ℤ I ≤ Module.finrank ℤ Λ := by
    simpa using hli.fintype_card_le_finrank
  refine ⟨_, fun i => (b i : Λ), fun x => ⟨fun hx => ⟨fun i => b.repr ⟨x, hx⟩ i, ?_⟩, ?_⟩,
    fun x k hk hx => hI.2.1 x k hk hx, hd0, ?_⟩
  · have := congrArg (I.subtype.toAddMonoidHom.toIntLinearMap) (b.sum_repr ⟨x, hx⟩)
    rw [map_sum] at this
    simpa using this
  · rintro ⟨y, rfl⟩
    exact I.sum_mem fun i _ => zsmul_mem (b i).2 _
  · have h1 : (rg (R t) fun i => (b i : Λ)).det ≤ Dk ^ Module.finrank ℤ I := by
      refine hdet.le.trans ?_
      rw [← hDk, hm, mul_assoc, mul_comm 2, pow_mul Dk _ 2]
      have h0 : 0 ≤ Dk ^ (Fintype.card Ψ * Module.finrank (𝓞 E) I) := pow_nonneg hD0 _
      exact pow_le_pow_left₀ (mul_nonneg hnz0.le h0) (mul_le_of_le_one_left h0 hnz) 2
    have h2 : (((coords e fun i => (b i : Λ)) * (coords e fun i => (b i : Λ))ᵀ).det : ℝ) ≤
        (Dk / c) ^ Module.finrank ℤ I := by
      rw [div_pow, le_div_iff₀ (pow_pos hc _), mul_comm]
      exact hd1.trans h1
    have h3 : (Dk / c) ^ Module.finrank ℤ I ≤ (max 1 (Dk / c)) ^ Module.finrank ℤ Λ :=
      (pow_le_pow_left₀ (div_nonneg hD0 hc.le) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) hle)
    exact_mod_cast (h2.trans h3).trans (Int.le_ceil _)
end
