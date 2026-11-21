import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodFrameOfHolomorphicLatticeFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
import BuildAid.ForwardExisting

section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh.ConstForm

theorem constForm : ∀ (n a g r₀ : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (Pair : ℕ → (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℂˣ → Prop), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∃ C : ℝ, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ‖ζ z‖ ≤ C) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → (∀ N z v w c c', Pair N z v w c → Pair N z v w c' → c = c') → (∀ (m N : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ) (v w : (Fin m → ℂ) → Fin g → ℂ) (c : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → _root_.IsPreconnected B → DifferentiableOn ℂ φ B → Set.MapsTo φ B (Metric.ball 0 1) → DifferentiableOn ℂ v B → DifferentiableOn ℂ w B → (∀ b ∈ B, v b ∈ K (φ b) ∧ w b ∈ K (φ b)) → b₀ ∈ B → b₁ ∈ B → Pair N (φ b₀) (v b₀) (w b₀) c → Pair N (φ b₁) (v b₁) (w b₁) c) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ Submodule.span ℝ (K z) = ⊤ ∧ (∀ v ∈ K z, ∀ w ∈ K z, ∃ m : ℤ, (hermForm Hm v w).im = m) ∧ ∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K z → w ∈ K z → Pair N z v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N)) (Complex.exp_ne_zero _))) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ a a' : Fin r₀ → ℤ, (fun j => (a j : ZMod N)) ∈ S → Pair N 0 (∑ j, a j • ζ 0 j) (∑ j, a' j • ζ 0 j) 1) → ∃ (r : ℕ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), ContinuousOn lam (logDom n a) ∧ (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) ∧ (∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) ∧ (∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ v ∈ K (logExp a s), ∀ w ∈ K (logExp a s), ∃ m : ℤ, (hermForm Hm v w).im = m) → (∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K (logExp a s) → w ∈ K (logExp a s) → Pair N (logExp a s) v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N)) (Complex.exp_ne_zero _))) → ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) ∧ ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ u u' : Fin r₀ → ℤ, (fun j => (u j : ZMod N)) ∈ S → ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → ∃ m : ℤ, (hermForm Hm (∑ i, u i • ζ (logExp a s) i) (∑ j, u' j • ζ (logExp a s) j)).im = N * m := by
  intro n a g r₀ K ζ Pair hK hζan hζli hζK hζ0 hζbd hstd huniq hprop hinner hS
  obtain ⟨hDo, hDc, hEa, hEm⟩ := Core.logDom_facts n a
  have hDp : _root_.IsPreconnected (logDom n a) := hDc.isPreconnected
  have hEd : Differentiable ℂ (logExp a : (Fin n → ℂ) → Fin n → ℂ) := fun s => (hEa s).differentiableAt
  have hK' : IsLatFam (logDom n a) (fun s => K (logExp a s)) :=
    Core.isLatFam_comp n n g _ _ K (logExp a) hK hDo (fun s _ => hEa s) hEm
  have hin := fun s (hs : s ∈ logDom n a) => hinner _ (hEm hs) (fun k hk => Core.logExp_ne_zero n a s k hk)
  obtain ⟨lam, hlamD, hlamB⟩ := GlobalTheory.T.exists_global_holomorphic_lattice_basis_convex n g (2 * g) (logDom n a) (fun s => K (logExp a s)) hDo hDc
    (fun s hs => GlobalTheory.T.exists_analytic_local_lattice_basis n g (logDom n a) (fun s => K (logExp a s)) s hK' hs (hin s hs).choose_spec.2.2.1)
  have hmem : ∀ s ∈ logDom n a, ∀ i, lam s i ∈ K (logExp a s) := fun s hs i => Core.mem_of_isLatBasis (hlamB s hs) i
  have hlamDi : ∀ i, DifferentiableOn ℂ (fun s => lam s i) (logDom n a) := fun i => differentiableOn_pi.1 hlamD i
  let s₀ : Fin n → ℂ := fun _ => (-1 / 2 : ℂ)
  have hs₀ : s₀ ∈ logDom n a := by
    simp only [logDom, Set.mem_setOf_eq]
    intro k
    split_ifs <;> norm_num [s₀]
  obtain ⟨Hm₀, -, hpos₀, hspan₀, hint₀, hpair₀⟩ := hin s₀ hs₀
  have hMex : ∀ i j, ∃ m : ℤ, (hermForm Hm₀ (lam s₀ i) (lam s₀ j)).im = m := fun i j =>
    hint₀ _ (hmem s₀ hs₀ i) _ (hmem s₀ hs₀ j)
  obtain ⟨M, hM₀⟩ : ∃ M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ, ∀ i j, (hermForm Hm₀ (lam s₀ i) (lam s₀ j)).im = M i j :=
    ⟨fun i j => (hMex i j).choose, fun i j => (hMex i j).choose_spec⟩
  have hM : ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ,
      (∀ v ∈ K (logExp a s), ∀ w ∈ K (logExp a s), ∃ m : ℤ, (hermForm Hm v w).im = m) →
      (∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K (logExp a s) → w ∈ K (logExp a s) →
        Pair N (logExp a s) v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N))
          (Complex.exp_ne_zero _))) →
      ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j := by
    intro s hs Hm hint hpair i j
    obtain ⟨m', hm'⟩ := hint _ (hmem s hs i) _ (hmem s hs j)
    have key : m' = M i j := by
      apply Core.eq_of_exp_eq
      intro N hN
      have h1 := hpair₀ N _ _ hN (hmem s₀ hs₀ i) (hmem s₀ hs₀ j)
      have h2 := hprop n N (logDom n a) (logExp a) (fun s => lam s i) (fun s => lam s j) _ s₀ s hN hDo hDp
        hEd.differentiableOn hEm (hlamDi i) (hlamDi j) (fun b hb => ⟨hmem b hb i, hmem b hb j⟩) hs₀ hs h1
      have h3 := hpair N _ _ hN (hmem s hs i) (hmem s hs j)
      have h4 := congrArg Units.val (huniq _ _ _ _ _ _ h3 h2)
      simp only [Units.val_mk0, hm', hM₀, Complex.ofReal_intCast] at h4
      exact h4
    rw [hm', key]
  have hζc : ContinuousOn ζ (Metric.ball 0 1) := hζan.continuousOn
  have hζEc : ∀ i, ContinuousOn (fun s => ζ (logExp a s) i) (logDom n a) := fun i =>
    (continuousOn_pi.1 (hζc.comp hEd.continuous.continuousOn hEm)) i
  have hAex : ∀ i, ∃ m : Fin (2 * g) → ℤ, ∀ s ∈ logDom n a, ζ (logExp a s) i = ∑ k, m k • lam s k := fun i =>
    GlobalTheory.T.exists_const_integral_coords_lattice_section n g (2 * g) (logDom n a) (fun s => K (logExp a s)) lam (fun s => ζ (logExp a s) i) s₀ hDp
      hlamD.continuousOn (hζEc i) hlamB (fun s hs => hζK _ (hEm hs) i) hs₀
  choose A hA using hAex
  have hz₁ : logExp a s₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 := hEm hs₀
  have hsumK : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ c : Fin r₀ → ℤ, ∑ j, c j • ζ z j ∈ K z := by
    intro z hz c
    obtain ⟨H, hH⟩ := hK.2.1 z hz
    have hj : ∀ j, ζ z j ∈ H := fun j => by rw [← SetLike.mem_coe, hH]; exact hζK z hz j
    rw [← hH]
    exact H.sum_mem fun j _ => H.zsmul_mem (hj j) _
  have hζd : DifferentiableOn ℂ ζ (Metric.ball 0 1) := hζan.differentiableOn
  have hsumD : ∀ c : Fin r₀ → ℤ, DifferentiableOn ℂ (fun z => ∑ j, c j • ζ z j) (Metric.ball 0 1) := by
    intro c
    have h : ∀ j ∈ (Finset.univ : Finset (Fin r₀)), DifferentiableOn ℂ (fun z => c j • ζ z j) (Metric.ball 0 1) :=
      fun j _ => (differentiableOn_pi.1 hζd j).const_smul (c j)
    refine (DifferentiableOn.sum h).congr fun z _ => ?_
    simp [Finset.sum_apply]
  have hsum_eq : ∀ s ∈ logDom n a, ∀ c : Fin r₀ → ℤ,
      ∑ j, c j • ζ (logExp a s) j = ∑ k, (∑ i, c i • A i) k • lam s k := by
    intro s hs c
    simp only [fun i => hA i s hs, Finset.smul_sum, smul_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_smul]
    exact Finset.sum_comm
  have hform : ∀ (s : Fin n → ℂ) (Hm : Matrix (Fin g) (Fin g) ℂ),
      (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → ∀ x y : Fin (2 * g) → ℤ,
      (hermForm Hm (∑ k, x k • lam s k) (∑ k, y k • lam s k)).im =
      ((x ⬝ᵥ (M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) *ᵥ y : ℤ) : ℝ) := by
    intro s Hm hHm x y
    rw [Core.hermForm_im_sum]
    simp only [hHm, dotProduct, Matrix.mulVec, Int.cast_sum, Int.cast_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hdvd : ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧
      ∀ c c' : Fin r₀ → ℤ, (fun j => (c j : ZMod N)) ∈ S →
        (N : ℤ) ∣ (∑ i, c i • A i) ⬝ᵥ (M : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) *ᵥ (∑ i, c' i • A i) := by
    intro N hN
    obtain ⟨S, hcard, hSp⟩ := hS N hN
    refine ⟨S, hcard, fun c c' hc => ?_⟩
    have h1 := hSp c c' hc
    have h2 := hprop n N (Metric.ball 0 1) id (fun z => ∑ j, c j • ζ z j) (fun z => ∑ j, c' j • ζ z j) 1 0
      (logExp a s₀) hN Metric.isOpen_ball (convex_ball 0 1).isPreconnected differentiableOn_id (Set.mapsTo_id _)
      (hsumD c) (hsumD c') (fun b hb => ⟨hsumK b hb c, hsumK b hb c'⟩) (Metric.mem_ball_self one_pos) hz₁ h1
    have h3 := hpair₀ N _ _ hN (hsumK _ hz₁ c) (hsumK _ hz₁ c')
    have h4 := congrArg Units.val (huniq _ _ _ _ _ _ h3 h2)
    simp only [Units.val_mk0, Units.val_one, id, hsum_eq s₀ hs₀, hform s₀ Hm₀ hM₀, Complex.ofReal_intCast] at h4
    exact Core.dvd_of_exp_eq_one _ N hN h4
  refine ⟨2 * g, lam, M, hlamD.continuousOn, fun s hs => ⟨(hlamB s hs).1.restrict_scalars' ℤ,
    Core.span_top_of_isLatBasis (hlamB s hs) (hin s hs).choose_spec.2.2.1, (hlamB s hs).2⟩, fun s hs => ?_, hM,
    fun N hN => ?_⟩
  · obtain ⟨Hm, -, hpos, -, hint, hpair⟩ := hin s hs
    exact ⟨Hm, hpos, hM s hs Hm hint hpair⟩
  · obtain ⟨S, hcard, hSd⟩ := hdvd N hN
    refine ⟨S, hcard, fun u u' hu s hs Hm hHm => ?_⟩
    obtain ⟨m, hm⟩ := hSd u u' hu
    refine ⟨m, ?_⟩
    rw [hsum_eq s hs u, hsum_eq s hs u', hform s Hm hHm, hm]
    push_cast
    ring

end GlobalTheory.ShFam.Hor.LogCh.ConstForm
end
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem intPsd_common_kernel_of_sum_not_posDef : ∀ (a g rk : ℕ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), (∀ k, ((B k).map (Int.cast : ℤ → ℝ)).PosSemidef) → (∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → B k j l = 0) → ¬ (((∑ k, B k).map (Int.cast : ℤ → ℝ)).submatrix (Subtype.val : {j : Fin g // j.val < rk} → Fin g) Subtype.val).PosDef → ∃ v : Fin g → ℤ, v ≠ 0 ∧ (∀ j : Fin g, rk ≤ j.val → v j = 0) ∧ ∀ k, (B k).mulVec v = 0 := by
  intro a g rk B hpsd hsupp hnot
  set S : Matrix (Fin g) (Fin g) ℤ := ∑ k, B k with hS
  let e : {j : Fin g // j.val < rk} → Fin g := Subtype.val
  have hcast : ∀ (M : Matrix (Fin g) (Fin g) ℤ) (u : Fin g → ℤ) (i : Fin g),
      ((M.map (Int.cast : ℤ → ℝ)) *ᵥ (fun j => (u j : ℝ))) i = (((M *ᵥ u) i : ℤ) : ℝ) := by
    intro M u i
    simp [mulVec, dotProduct]
  have hSmap : S.map (Int.cast : ℤ → ℝ) = ∑ k, (B k).map (Int.cast : ℤ → ℝ) := by
    ext i j; simp [hS, Matrix.sum_apply]
  have hSR : ((S.map (Int.cast : ℤ → ℝ)).submatrix e e).PosSemidef := by
    rw [hSmap]
    exact (posSemidef_sum _ (fun k _ => hpsd k)).submatrix e
  have hdetR : ((S.map (Int.cast : ℤ → ℝ)).submatrix e e).det = 0 := by
    by_contra hdet
    apply hnot
    rw [posDef_iff_dotProduct_mulVec]
    refine ⟨hSR.isHermitian, fun x hx => ?_⟩
    have hnn := (posSemidef_iff_dotProduct_mulVec.1 hSR).2 x
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exfalso
      have hk := (hSR.dotProduct_mulVec_zero_iff x).1 h.symm
      exact hdet (exists_mulVec_eq_zero_iff.1 ⟨x, hx, hk⟩)
  have hdetZ : (S.submatrix e e).det = 0 := by
    have h := (Int.castRingHom ℝ).map_det (S.submatrix e e)
    have h2 : (Int.castRingHom ℝ).mapMatrix (S.submatrix e e)
        = (S.map (Int.cast : ℤ → ℝ)).submatrix e e := rfl
    rw [h2, hdetR, eq_intCast] at h
    exact_mod_cast h
  obtain ⟨w, hw0, hw⟩ := exists_mulVec_eq_zero_iff.2 hdetZ
  let v : Fin g → ℤ := fun j => if h : j.val < rk then w ⟨j, h⟩ else 0
  have hSi : ∀ i j : Fin g, rk ≤ i.val → S i j = 0 := by
    intro i j hi
    simp [hS, Matrix.sum_apply, hsupp _ i j (Or.inl hi)]
  have hsplit : ∀ i : Fin g, (S *ᵥ v) i = ∑ j : {j : Fin g // j.val < rk}, S i j * w j := by
    intro i
    simp only [mulVec, dotProduct]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun j : Fin g => j.val < rk)]
    have h2 : ∑ j : {j : Fin g // ¬ j.val < rk}, S i j * v j = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [v, j.2]
    rw [h2, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [v, j.2]
  have hSv : S *ᵥ v = 0 := by
    funext i
    rw [hsplit]
    by_cases hi : i.val < rk
    · have := congrFun hw ⟨i, hi⟩
      simpa [mulVec, dotProduct, e] using this
    · push_neg at hi
      simp [hSi i _ hi]
  refine ⟨v, ?_, ?_, ?_⟩
  · intro hv
    apply hw0
    funext j
    have := congrFun hv j.val
    simpa [v, j.2] using this
  · intro j hj
    simp [v, not_lt.2 hj]
  · intro k
    let vR : Fin g → ℝ := fun j => (v j : ℝ)
    have hQnn : ∀ k, 0 ≤ star vR ⬝ᵥ (((B k).map (Int.cast : ℤ → ℝ)) *ᵥ vR) := fun k =>
      (posSemidef_iff_dotProduct_mulVec.1 (hpsd k)).2 vR
    have hsum : ∑ k, star vR ⬝ᵥ (((B k).map (Int.cast : ℤ → ℝ)) *ᵥ vR) = 0 := by
      rw [← dotProduct_sum, ← sum_mulVec, ← hSmap]
      have : (S.map (Int.cast : ℤ → ℝ)) *ᵥ vR = 0 := by
        funext i; rw [hcast, hSv]; simp
      rw [this, dotProduct_zero]
    have hk0 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hQnn k)).1 hsum k (Finset.mem_univ _)
    have hker := ((hpsd k).dotProduct_mulVec_zero_iff vR).1 hk0
    funext i
    have := congrFun hker i
    rw [hcast] at this
    simpa using this

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_int_kernel_psd_block_not_posDef : ∀ (a g rk : ℕ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), (∀ k, ((B k).map (Int.cast : ℤ → ℝ)).PosSemidef) → (∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → B k j l = 0) → ¬ (((∑ k, B k).map (Int.cast : ℤ → ℝ)).submatrix (Subtype.val : {j : Fin g // j.val < rk} → Fin g) Subtype.val).PosDef → ∃ v : Fin g → ℤ, v ≠ 0 ∧ (∀ j : Fin g, rk ≤ j.val → v j = 0) ∧ ∀ k, (B k).mulVec v = 0 := by
  atlas_forward_decl GlobalTheory.intPsd_common_kernel_of_sum_not_posDef
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase.HodgeChart

open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram in

theorem periodChart_rescale_ball : ∀ (n a g rk : ℕ) (ha : a ≤ n) (ρ : ℝ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < ρ → ρ ≤ 1 → rk ≤ g → (∀ j k, DifferentiableOn ℂ (fun z => τ₀ z j k) (Metric.ball 0 ρ)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (τ₀ z).IsSymm) → (∀ i, ((B i).map (Int.cast : ℤ → ℝ)).PosSemidef) → (∀ i (j k : Fin g), (rk ≤ j.val ∨ rk ≤ k.val) → B i j k = 0) → (((∑ i, B i).map (Int.cast : ℤ → ℝ)).submatrix (Subtype.val : {j : Fin g // j.val < rk} → Fin g) Subtype.val).PosDef → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (((τ₀ z).map Complex.im).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val).PosDef) → GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk (fun u => τ₀ (ρ • u) + ∑ i, (((Real.log ρ : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) • (B i).map (Int.cast : ℤ → ℂ)) B ∧ ∀ z : Fin n → ℂ, (∀ i : Fin a, z (Fin.castLE ha i) ≠ 0) → GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha (fun u => τ₀ (ρ • u) + ∑ i, (((Real.log ρ : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) • (B i).map (Int.cast : ℤ → ℂ)) B (ρ⁻¹ • z) = GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B z := by
  intro n a g rk ha ρ τ₀ B hr hr1 hrk hholo hsymm hpsd hsupp htoric habel
  set cst : ℂ := (((Real.log ρ : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) with hcst
  have him : cst.im = -Real.log ρ / (2 * Real.pi) := by
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have e : cst = ((-Real.log ρ / (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      rw [hcst]; push_cast; field_simp; rw [Complex.I_sq]; ring
    rw [e, Complex.im_ofReal_mul, Complex.I_im, _root_.mul_one]
  have hBs : ∀ i (j k : Fin g), B i k j = B i j k := fun i j k => by
    have := (hpsd i).isHermitian.apply j k
    simp at this
    exact_mod_cast this
  have hmaps : ∀ z ∈ polydisc n 1, ρ • z ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
    intro u hu
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hr.le]
    have : ‖u‖ < 1 := (pi_norm_lt_iff one_pos).2 hu
    calc ρ * ‖u‖ < ρ * 1 := by gcongr
      _ = ρ := _root_.mul_one ρ
  have hdiff : DifferentiableOn ℂ (fun z : Fin n → ℂ => ρ • z) (polydisc n 1) :=
    ((differentiable_id.const_smul (ρ : ℂ)).differentiableOn).congr fun u _ => by
      funext k; simp [Complex.real_smul]
  refine ⟨⟨hrk, fun j k => ?_, fun z hz => ?_, hpsd, hsupp, htoric, fun z hz => ?_⟩, fun u hu => ?_⟩
  · have h1 := (hholo j k).comp hdiff hmaps
    refine (h1.add (differentiableOn_const (∑ i, cst * (B i j k : ℂ)))).congr fun z _ => ?_
    simp [Matrix.add_apply, Matrix.sum_apply, Function.comp]
  · refine Matrix.IsSymm.ext fun j k => ?_
    have := (hsymm _ (hmaps z hz)).apply j k
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, hBs, this]
  · have h1 := habel _ (hmaps z hz)
    convert h1 using 1
    ext ⟨j, hj⟩ ⟨k, hk⟩
    simp [Matrix.sum_apply, hsupp _ j k (Or.inl hj)]
  · have hρu : ρ • (ρ⁻¹ • u) = u := smul_inv_smul₀ hr.ne' u
    ext j k
    have hu' : ∀ i : Fin a, tlog ((ρ⁻¹ • u) (Fin.castLE ha i)) = Real.log ρ / (2 * Real.pi) + tlog (u (Fin.castLE ha i)) := by
      intro i
      rw [Pi.smul_apply, tlog, tlog, norm_smul, Real.norm_of_nonneg (inv_pos.2 hr).le,
        Real.log_mul (inv_pos.2 hr).ne' (norm_ne_zero_iff.2 (hu i)), Real.log_inv]
      ring
    simp only [hodgeGram, imPeriod, Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      hu', hρu, Complex.add_im, Complex.im_sum, smul_eq_mul]
    push_cast
    simp only [Complex.smul_im, Complex.intCast_im, Complex.intCast_re, smul_eq_mul, him, add_mul, Finset.sum_add_distrib]
    simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, mul_zero, add_zero, him]
    push_cast
    simp only [zero_add]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring

end GlobalTheory.LieBase.HodgeChart
end
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodChart_rescale_ball_to_unitPolydisc : ∀ (n a g rk : ℕ) (ha : a ≤ n) (ρ : ℝ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < ρ → ρ ≤ 1 → rk ≤ g → (∀ j k, DifferentiableOn ℂ (fun z => τ₀ z j k) (Metric.ball 0 ρ)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (τ₀ z).IsSymm) → (∀ i, ((B i).map (Int.cast : ℤ → ℝ)).PosSemidef) → (∀ i (j k : Fin g), (rk ≤ j.val ∨ rk ≤ k.val) → B i j k = 0) → (((∑ i, B i).map (Int.cast : ℤ → ℝ)).submatrix (Subtype.val : {j : Fin g // j.val < rk} → Fin g) Subtype.val).PosDef → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (((τ₀ z).map Complex.im).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val).PosDef) → GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk (fun u => τ₀ (ρ • u) + ∑ i, (((Real.log ρ : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) • (B i).map (Int.cast : ℤ → ℂ)) B ∧ ∀ z : Fin n → ℂ, (∀ i : Fin a, z (Fin.castLE ha i) ≠ 0) → GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha (fun u => τ₀ (ρ • u) + ∑ i, (((Real.log ρ : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) • (B i).map (Int.cast : ℤ → ℂ)) B (ρ⁻¹ • z) = GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B z := by
  atlas_forward_decl GlobalTheory.LieBase.HodgeChart.periodChart_rescale_ball
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.ShFam.Hor.LogCh.exists_periodChart_of_latFam : ∀ (n a g r₀ r : ℕ) (ha : a ≤ n) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → ContinuousOn lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → (∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ ∀ s' ∈ logDom n a, logExp a s' = logExp a s → ∀ i j, (hermForm Hm (lam s' i) (lam s' j)).im = M i j) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ u u' : Fin r₀ → ℤ, (fun j => (u j : ZMod N)) ∈ S → ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → ∃ m : ℤ, (hermForm Hm (∑ i, u i • ζ (logExp a s) i) (∑ j, u' j • ζ (logExp a s) j)).im = N * m) → ∃ (rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (P : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (ρ d : ℝ), 0 < ρ ∧ ρ ≤ 1 ∧ 0 < d ∧ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ (∀ i j, DifferentiableOn ℂ (fun z => P z i j) (Metric.ball 0 ρ)) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, IsUnit (P z).det) ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → (P (logExp a s))ᵀ * Hm * (P (logExp a s))ᵀᴴ = ((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ρ⁻¹ • logExp a s))⁻¹ := by
  intro n a g r₀ r ha K ζ lam M hK hζ hζi hζK hζ0 hstd hlam hlamB hH htor
  obtain ⟨rk, d, ρ, P, τ, B, Δ, hρ, hρ1, hd, hrk, hP, hPdet, hτd, hτs, hτm, hB, hPH, hΔc, hΔp, hτΔ, hcl⟩ :=
    GlobalTheory.T.exists_periodFrame_of_holomorphicLatticeFamily n a g r₀ r ha K ζ lam M hK hζ hζi hζK hζ0 hstd hlam hlamB hH htor
  obtain ⟨hpsd, τ₀, hτ₀d, hτ₀s, hτ₀e⟩ := GlobalTheory.T.periodMatrix_boundaryExtension_monodromy_posSemidef n a g ha ρ τ B hρ hρ1 hτd hτs hτm
  have hcont : ∀ j l, ContinuousOn (fun z => τ₀ z j l) (Metric.ball 0 ρ) := fun j l => (hτ₀d j l).continuousOn
  have hmv : ∀ (k : Fin a) (v : Fin g → ℤ), ((B k).map (Int.cast : ℤ → ℂ)).mulVec (fun j => (v j : ℂ)) =
      fun i => (((B k).mulVec v i : ℤ) : ℂ) := by
    intro k v; ext i; simp [Matrix.mulVec, dotProduct]
  have htoric : (((∑ k, B k).map (Int.cast : ℤ → ℝ)).submatrix
      (Subtype.val : {j : Fin g // j.val < rk} → Fin g) Subtype.val).PosDef := by
    by_contra hnot
    obtain ⟨v, hv0, hvs, hBv⟩ := GlobalTheory.T.exists_common_int_kernel_psd_block_not_posDef a g rk B hpsd hB hnot
    refine hcl v hv0 hvs (fun z => (τ₀ z).mulVec (fun j => (v j : ℂ))) ?_ ?_
    · refine continuousOn_pi.2 fun j => ?_
      simp only [Matrix.mulVec, dotProduct]
      exact continuousOn_finset_sum _ fun l _ => (hcont j l).mul continuousOn_const
    · intro s hs hz
      rw [hτ₀e s hs hz, Matrix.add_mulVec]
      have h0 : (∑ k, (s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ)).mulVec
          (fun j => (v j : ℂ)) = 0 := by
        rw [Matrix.sum_mulVec]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [Matrix.smul_mulVec, hmv, hBv k]
        ext i; simp
      rw [h0, add_zero]
  have hagree : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ →
      (τ₀ (logExp a s)).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val = Δ (logExp a s) := by
    intro s hs hz
    rw [← hτΔ s hs hz, hτ₀e s hs hz]
    ext ⟨j, hj⟩ ⟨l, hl⟩
    simp [Matrix.sum_apply, hB _ j l (Or.inl hj)]
  have heq := GlobalTheory.T.eqOn_ball_of_eqOn_punctPolydiscCoveringExp_image n a ρ _
    (fun z => (τ₀ z).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val) Δ hρ1
    (continuousOn_pi.2 fun j => continuousOn_pi.2 fun l => hcont j.1 l.1) hΔc hagree
  have habel : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (((τ₀ z).map Complex.im).submatrix
      (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val).PosDef := by
    intro z hz
    have h1 := hΔp z hz
    rw [← heq z hz] at h1
    exact h1
  obtain ⟨hPC, hY⟩ := GlobalTheory.T.periodChart_rescale_ball_to_unitPolydisc n a g rk ha ρ τ₀ B hρ hρ1 hrk hτ₀d hτ₀s hpsd hB htoric habel
  refine ⟨rk, _, B, P, ρ, d, hρ, hρ1, hd, hPC, hP, hPdet, ?_⟩
  intro s hs hz Hm hHm
  have hnz : ∀ i : Fin a, logExp a s (Fin.castLE ha i) ≠ 0 := by
    intro i
    simp only [logExp, Fin.coe_castLE, i.isLt, if_true]
    exact Complex.exp_ne_zero _
  rw [hPH s hs hz Hm hHm, hY _ hnz]
  congr 2
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram
  congr 1
  rw [← GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.im_period ha τ₀ B (logExp a s) (fun k => s (Fin.castLE ha k)) ?_]
  · rw [hτ₀e s hs hz]; rfl
  · intro i
    simp only [logExp, Fin.coe_castLE, i.isLt, if_true]
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodChart_holomorphicLatticeFamily : ∀ (n a g r₀ r : ℕ) (ha : a ≤ n) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → ContinuousOn lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → (∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ ∀ s' ∈ logDom n a, logExp a s' = logExp a s → ∀ i j, (hermForm Hm (lam s' i) (lam s' j)).im = M i j) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ u u' : Fin r₀ → ℤ, (fun j => (u j : ZMod N)) ∈ S → ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → ∃ m : ℤ, (hermForm Hm (∑ i, u i • ζ (logExp a s) i) (∑ j, u' j • ζ (logExp a s) j)).im = N * m) → ∃ (rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (P : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (ρ d : ℝ), 0 < ρ ∧ ρ ≤ 1 ∧ 0 < d ∧ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ (∀ i j, DifferentiableOn ℂ (fun z => P z i j) (Metric.ball 0 ρ)) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, IsUnit (P z).det) ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → (P (logExp a s))ᵀ * Hm * (P (logExp a s))ᵀᴴ = ((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ρ⁻¹ • logExp a s))⁻¹ := by
  atlas_forward_decl GlobalTheory.ShFam.Hor.LogCh.exists_periodChart_of_latFam
end

section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem isExpChart_rescale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (n g : ℕ) (e : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g) (P : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (ρ : ℝ), IsExpChart e ex → 0 < ρ → ρ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun z => P z i j) (Metric.ball 0 ρ)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, IsUnit (P z).det) → ∃ ch : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr Z) σ) (Fin n → ℂ), IsExpChart ch (fun x v => ex x (P (e x) *ᵥ v)) ∧ (∀ x, x ∈ ch.source ↔ x ∈ e.source ∧ e x ∈ Metric.ball (0 : Fin n → ℂ) ρ) ∧ ∀ x ∈ ch.source, e x = ρ • ch x := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ n g e ex P ρ hE hρ hρ1 hP hPu
  obtain ⟨htarget, hholE, hsymmHol, hadd, hjoint, htan⟩ := hE
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have hSo : IsOpen (e.source ∩ e ⁻¹' Metric.ball (0 : Fin n → ℂ) ρ) :=
    e.isOpen_inter_preimage Metric.isOpen_ball
  let ch : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr Z) σ) (Fin n → ℂ) :=
    (e.restrOpen _ hSo).transHomeomorph (Homeomorph.smulOfNeZero (ρ⁻¹ : ℝ) (inv_ne_zero hρ0))
  have hch : ∀ x, ch x = (ρ⁻¹ : ℝ) • e x := fun x ↦ rfl
  have hchs : ∀ z, ch.symm z = e.symm (ρ • z) := fun z ↦ by
    show e.symm ((ρ⁻¹ : ℝ)⁻¹ • z) = _
    rw [inv_inv]
  have hsrc : ∀ x, x ∈ ch.source ↔ x ∈ e.source ∧ e x ∈ Metric.ball (0 : Fin n → ℂ) ρ := fun x ↦ by
    show x ∈ e.source ∩ (e.source ∩ e ⁻¹' Metric.ball (0 : Fin n → ℂ) ρ) ↔ _
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    tauto
  have hball : ∀ z : Fin n → ℂ, ρ • z ∈ Metric.ball (0 : Fin n → ℂ) ρ ↔ z ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
    intro z
    simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  have hsub : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ρ • z ∈ e.target := fun z hz ↦ by
    rw [htarget]; exact Metric.ball_subset_ball hρ1 ((hball z).2 hz)
  have htgt : ch.target = Metric.ball 0 1 := by
    ext z
    show (Homeomorph.smulOfNeZero (ρ⁻¹ : ℝ) (inv_ne_zero hρ0)).symm z ∈
      e.target ∩ e.symm ⁻¹' (e.source ∩ e ⁻¹' Metric.ball (0 : Fin n → ℂ) ρ) ↔ _
    have hz : (Homeomorph.smulOfNeZero (ρ⁻¹ : ℝ) (inv_ne_zero hρ0)).symm z = ρ • z := by
      show (ρ⁻¹ : ℝ)⁻¹ • z = _
      rw [inv_inv]
    rw [hz]
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨h1, -, h⟩
      rw [e.right_inv h1] at h
      exact (hball z).1 h
    · intro h
      have h2 := hsub z h
      exact ⟨h2, e.map_target h2, by rw [e.right_inv h2]; exact (hball z).2 h⟩
  refine ⟨ch, ⟨htgt, ?_, ?_, ?_, ?_, ?_⟩, hsrc, ?_⟩
  · intro k V _ _ _ B x hB hx hm
    have := hholE k V B x hB hx fun b hb ↦ ((hsrc _).1 (hm hb)).1
    simp only [hch, Pi.smul_apply]
    exact this.const_smul (ρ⁻¹ : ℝ)
  · rw [htgt]
    have := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun z : Fin n → ℂ ↦ ρ • z) hsymmHol Metric.isOpen_ball
      (differentiableOn_id.const_smul ρ) fun z hz ↦ hsub z hz
    refine GlobalTheory.HolPeriods.isHolTo_congr this fun z _ ↦ ?_
    simp only [hchs]
  · intro x hx v w
    simp only [Matrix.mulVec_add]
    exact hadd x ((hsrc x).1 hx).1 _ _
  · rw [htgt]
    have hφ : DifferentiableOn ℂ (fun zw : (Fin n → ℂ) × (Fin g → ℂ) ↦ (ρ • zw.1, P (ρ • zw.1) *ᵥ zw.2))
        (Metric.ball 0 1 ×ˢ Set.univ) := by
      refine (differentiableOn_fst.const_smul ρ).prodMk ?_
      refine differentiableOn_pi.2 fun i ↦ ?_
      simp only [Matrix.mulVec, dotProduct]
      refine DifferentiableOn.fun_sum fun j _ ↦ ?_
      exact ((hP i j).comp (differentiableOn_fst.const_smul ρ) fun zw hzw ↦ (hball _).2 hzw.1).mul
        (by fun_prop : Differentiable ℂ fun zw : (Fin n → ℂ) × (Fin g → ℂ) ↦ zw.2 j).differentiableOn
    have := GlobalTheory.HolPeriods.isHolTo_comp hjoint (Metric.isOpen_ball.prod isOpen_univ) hφ
      fun zw hzw ↦ ⟨hsub _ hzw.1, Set.mem_univ _⟩
    refine GlobalTheory.HolPeriods.isHolTo_congr this fun zw hzw ↦ ?_
    dsimp only
    rw [hchs, e.right_inv (hsub _ hzw.1)]
  · intro x hx
    have hxe := (hsrc x).1 hx
    have hhol : IsHolTo Set.univ (fun w ↦ (ex x w).left) := by
      have := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun w : Fin g → ℂ ↦ (e x, w)) hjoint isOpen_univ
        ((differentiableOn_const _).prodMk differentiableOn_id)
        fun w _ ↦ Set.mk_mem_prod (e.map_source hxe.1) (Set.mem_univ w)
      refine GlobalTheory.HolPeriods.isHolTo_congr this fun w _ ↦ ?_
      dsimp only
      rw [e.left_inv hxe.1]
    have hex : IsExpAt Z.t (x.1 ≫ genι Z) (ex x) := ⟨hadd x hxe.1, (htan x hxe.1).1, (htan x hxe.1).2⟩
    have := isExpAt_mulVec H _ Z.t (x.1 ≫ genι Z) g (ex x) (P (e x)) (hPu _ hxe.2) hhol hex
    exact ⟨this.2.1, this.2.2⟩
  · intro x _
    rw [hch, smul_smul, mul_inv_cancel₀ hρ0, one_smul]

end GlobalTheory.ShFam.Hor.LogCh
end

section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open Limits

namespace GlobalTheory.ShFam.Hor.LogCh

theorem kernel_lattice_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (g : ℕ) (x : GlobalTheory.CxPts (genStr Z) σ) (ex : (Fin g → ℂ) → (Over.mk (x.1 ≫ genι Z) ⟶ Z.t.G)), Inner x → IsExpAt Z.t (x.1 ≫ genι Z) ex → IsHolTo Set.univ (fun w => (ex w).left) → Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) = g ∧ ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ Submodule.span ℝ {w | ex w = 1} = ⊤ ∧ (∀ v w, ex v = 1 → ex w = 1 → ∃ m : ℤ, (hermForm Hm v w).im = m) ∧ ∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex v = 1 → ex w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (ex ((k : ℂ)⁻¹ • v)) (ex ((k : ℂ)⁻¹ • w)) (unitOn ζ) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ U _hσ hU g x ex hx hex hhol
  obtain ⟨y, hy⟩ := hx.exists_lift
  obtain ⟨W₀⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf E H Dw l Xo c σ _ U hU
  have hs : y ≫ pullback.snd _ _ = spMap σ := by
    rw [← Z.jQ_over, ← Category.assoc, hy]
    exact x.2
  obtain ⟨i, P, hP, hu⟩ := W₀.F.onto (y ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, OpenReg.spMap_comp])
  obtain ⟨e', he', hhol', hker, hweil⟩ := exists_pushed_exp E H Dw l Xo c O β Z _ _ _ W₀.F y i P (x.1 ≫ genι Z) hP hu
    (by rw [← hy, Category.assoc])
  obtain ⟨L, hL⟩ := exp_eq_comp_linearEquiv E H Z.X Z.t (x.1 ≫ genι Z) g _ ex e' hex hhol he' hhol'
  have hg : W₀.g = g := by
    have := L.finrank_eq
    simpa using this
  obtain ⟨Hm₀, hH₀, hpos₀, hEF⟩ := hP.2.2.2.2
  obtain ⟨Hm, hH, hpos, hform⟩ := exists_hermForm_transport _ _ L Hm₀ hH₀ hpos₀
  have hkerex : ∀ w, ex w = 1 ↔ ∃ a, w = L (P a) := by
    intro w
    constructor
    · intro h
      have h' : e' (L.symm w) = 1 := by rw [hL, L.apply_symm_apply, h]
      obtain ⟨a, ha⟩ := (hker _).1 h'
      exact ⟨a, by rw [ha, L.apply_symm_apply]⟩
    · rintro ⟨a, rfl⟩
      rw [← hL]
      exact (hker _).2 ⟨a, rfl⟩
  refine ⟨?_, Hm, hH, hpos, ?_, ?_, ?_⟩
  · rw [← hg, ← Fintype.card_congr W₀.e, Fintype.card_fin]
  · have hset : {w | ex w = 1} = (L.toLinearMap.restrictScalars ℝ) '' Set.range P := by
      ext w
      simp only [Set.mem_setOf_eq, hkerex, Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨P a, ⟨a, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨a, rfl⟩
    rw [hset, Submodule.span_image, hP.2.2.2.1, Submodule.map_top, LinearMap.range_eq_top]
    exact L.surjective
  · intro v w hv hw
    obtain ⟨a, rfl⟩ := (hkerex v).1 hv
    obtain ⟨b, rfl⟩ := (hkerex w).1 hw
    exact ⟨(W₀.F.Di i).EF a b, by rw [hform, hEF]⟩
  · intro k v w ζ hk hv hw hζ
    obtain ⟨a, rfl⟩ := (hkerex v).1 hv
    obtain ⟨b, rfl⟩ := (hkerex w).1 hw
    rw [← L.map_smul, ← L.map_smul, ← hL, ← hL]
    refine hweil k a b ζ hk ?_
    rw [hζ, hform, hEF, Complex.ofReal_intCast]

end GlobalTheory.ShFam.Hor.LogCh
end
end

section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh.PerChart

theorem hermForm_pull' {g g' : ℕ} (M : Matrix (Fin g') (Fin g) ℂ) (Hm : Matrix (Fin g') (Fin g') ℂ) (z w : Fin g → ℂ) :
    hermForm (Mᵀ * Hm * Mᵀᴴ) z w = hermForm Hm (M *ᵥ z) (M *ᵥ w) := by
  have : Mᵀᴴ *ᵥ (star w) = star (M *ᵥ w) := by
    rw [Matrix.star_mulVec, ← Matrix.mulVec_transpose]
    rfl
  rw [hermForm, hermForm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, this, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

theorem exists_logExp_eq (n a : ℕ) (z : Fin n → ℂ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1)
    (hnz : ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) : ∃ s ∈ logDom n a, logExp a s = z := by
  refine ⟨fun k => if (k : ℕ) < a then Complex.log (z k) else z k, fun k => ?_, funext fun k => ?_⟩
  · have hk1 : ‖z k‖ < 1 := (pi_norm_lt_iff one_pos).1 (mem_ball_zero_iff.1 hz) k
    by_cases hk : (k : ℕ) < a
    · simp only [hk, if_true]
      rw [Complex.log_re]
      exact Real.log_neg (norm_pos_iff.2 (hnz k hk)) hk1
    · simp only [hk, if_false]
      exact hk1
  · by_cases hk : (k : ℕ) < a
    · simp only [logExp, hk, if_true]
      exact Complex.exp_log (hnz k hk)
    · simp only [logExp, hk, if_false]

theorem exists_riemann_period_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ x₀ : GlobalTheory.CxPts (genStr T.Z) σ, ∃ (n a : ℕ) (ha : a ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g) (d : ℝ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ IsExpChart ch₀ ex ∧ x₀ ∈ ch₀.source ∧ ch₀ x₀ = 0 ∧ Fintype.card ((Σ τ : E →+* ℂ, Fin (Dw.mult τ))) = g ∧ 0 < d ∧ (∀ x ∈ ch₀.source, Inner x ↔ ∀ i : Fin a, ch₀ x (Fin.castLE ha i) ≠ 0) ∧ ∀ x ∈ ch₀.source, Inner x → ((((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹).IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm (((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹) u u).re) ∧ (∀ v w : Fin g → ℂ, ex x v = 1 → ex x w = 1 → ∃ m : ℤ, (hermForm (((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹) v w).im = m) ∧ ∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex x v = 1 → ex x w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm (((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹) v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil T.Z.t.cub k (ex x ((k : ℂ)⁻¹ • v)) (ex x ((k : ℂ)⁻¹ • w)) (unitOn ζ)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T σ U hσ hU x₀
  obtain ⟨n, a₁, g, r₀, e, ex, ζ, hx₀, he0, hEC, hbd, hsurj, hζan, hζli, hζK, hζB, hζC, hζstd⟩ :=
    GlobalTheory.T.exists_framedChart_exponential_toroidalModel E H Dw l Xo c O β Y T σ x₀
  have hEC' := hEC
  obtain ⟨htarget, hholE, hsymmHol, hadd, hjoint, htan⟩ := hEC'
  let a := min a₁ n
  have ha : a ≤ n := min_le_right _ _
  have hka : ∀ k : Fin n, ((k : ℕ) < a ↔ (k : ℕ) < a₁) := fun k => by
    simp only [a, lt_min_iff, k.isLt, and_true]
  have hsymm : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, e.symm z ∈ e.source := fun z hz =>
    e.map_target (by rw [htarget]; exact hz)
  have hExpAt : ∀ x ∈ e.source, IsExpAt T.Z.t (x.1 ≫ genι T.Z) (ex x) := fun x hx =>
    ⟨hadd x hx, (htan x hx).1, (htan x hx).2⟩
  have hzero : ∀ x ∈ e.source, ex x 0 = 1 := fun x hx => by
    have := hadd x hx 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hHol : IsHolTo (Metric.ball (0 : Fin n → ℂ) 1 ×ˢ Set.univ)
      (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ex (e.symm zw.1) zw.2).left) := htarget ▸ hjoint
  have hslice : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, IsHolTo Set.univ (fun w => (ex (e.symm z) w).left) :=
    fun z hz => by
      have := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun w : Fin g → ℂ => (z, w)) hHol isOpen_univ
        ((differentiableOn_const z).prodMk differentiableOn_id) fun w _ => Set.mk_mem_prod hz (Set.mem_univ w)
      dsimp only at this
      exact this
  have h0 : e.symm 0 = x₀ := by rw [← he0]; exact e.left_inv hx₀
  have hmem0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have hinner : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → Inner (e.symm z) :=
    fun z hz hnz => (hbd _ (hsymm z hz)).2 fun k hk => by
      rw [e.right_inv (by rw [htarget]; exact hz)]
      exact hnz k ((hka k).2 hk)
  let K : (Fin n → ℂ) → Set (Fin g → ℂ) := fun z => {w | ex (e.symm z) w = 1}
  let Pair : ℕ → (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℂˣ → Prop := fun N z v w c =>
    GlobalTheory.UU.CubWeil T.Z.t.cub N (ex (e.symm z) ((N : ℂ)⁻¹ • v)) (ex (e.symm z) ((N : ℂ)⁻¹ • w)) (unitOn c)
  have hLF : IsLatFam (Metric.ball 0 1) K :=
    GlobalTheory.T.exponentialKernels_isHolomorphicLatticeFamily E H T.Z.X T.Z.t n g (Metric.ball 0 1) (fun z => (e.symm z).1 ≫ genι T.Z) (fun z => ex (e.symm z))
      Metric.isOpen_ball hHol fun z hz => hExpAt _ (hsymm z hz)
  have hB0 : IsLatBasis (K 0) (ζ 0) := by
    show IsLatBasis {w | ex (e.symm 0) w = 1} (ζ 0)
    rw [h0]
    exact hζB
  have hP1 : ∀ N z v w c c', Pair N z v w c → Pair N z v w c' → c = c' := fun N z v w c c' h h' =>
    unitOn_injective (h.unique h')
  have hP2 : ∀ (m N : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ) (v w : (Fin m → ℂ) → Fin g → ℂ)
      (c : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → _root_.IsPreconnected B → DifferentiableOn ℂ φ B →
      Set.MapsTo φ B (Metric.ball 0 1) → DifferentiableOn ℂ v B → DifferentiableOn ℂ w B →
      (∀ b ∈ B, v b ∈ K (φ b) ∧ w b ∈ K (φ b)) → b₀ ∈ B → b₁ ∈ B →
      Pair N (φ b₀) (v b₀) (w b₀) c → Pair N (φ b₁) (v b₁) (w b₁) c := by
    intro m N B φ v w c b₀ b₁ hN hB hBc hφ hφm hv hw hK hb₀ hb₁ h
    have h1 := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun b => (φ b, (N : ℂ)⁻¹ • v b)) hHol hB
      (hφ.prodMk ((differentiableOn_const ((N : ℂ)⁻¹)).smul hv)) fun b hb => Set.mk_mem_prod (hφm hb) (Set.mem_univ _)
    have h2 := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun b => (φ b, (N : ℂ)⁻¹ • w b)) hHol hB
      (hφ.prodMk ((differentiableOn_const ((N : ℂ)⁻¹)).smul hw)) fun b hb => Set.mk_mem_prod (hφm hb) (Set.mem_univ _)
    dsimp only at h1 h2
    exact GlobalTheory.T.cubicalWeilPairing_torsion_const_holomorphic_family T.Z.X T.Z.t.G T.Z.t.PP T.Z.t.cub m N B (fun b => (e.symm (φ b)).1 ≫ genι T.Z)
      (fun b => ex (e.symm (φ b)) ((N : ℂ)⁻¹ • v b)) (fun b => ex (e.symm (φ b)) ((N : ℂ)⁻¹ • w b)) c b₀ b₁ hN hB hBc
      h1 h2
      (fun b hb => ⟨pow_eq_one_of_map _ (hadd _ (hsymm _ (hφm hb))) (hzero _ (hsymm _ (hφm hb))) hN (hK b hb).1,
        pow_eq_one_of_map _ (hadd _ (hsymm _ (hφm hb))) (hzero _ (hsymm _ (hφm hb))) hN (hK b hb).2⟩) hb₀ hb₁ h
  have hP3 : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) →
      ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧
        Submodule.span ℝ (K z) = ⊤ ∧ (∀ v ∈ K z, ∀ w ∈ K z, ∃ m : ℤ, (hermForm Hm v w).im = m) ∧
        ∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K z → w ∈ K z →
          Pair N z v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N))
            (Complex.exp_ne_zero _)) := by
    intro z hz hnz
    obtain ⟨-, Hm, hH, hpos, hspan, hint, hw⟩ := GlobalTheory.ShFam.Hor.LogCh.kernel_lattice_of_isUnf E H Dw l Xo c O β T.Z σ U hσ hU g (e.symm z) (ex (e.symm z))
      (hinner z hz hnz) (hExpAt _ (hsymm z hz)) (hslice z hz)
    exact ⟨Hm, hH, hpos, hspan, fun v hv w hw' => hint v w hv hw', fun N v w hN hv hw' => hw N v w _ hN hv hw' rfl⟩
  have hP4 : ∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧
      ∀ u u' : Fin r₀ → ℤ, (fun j => (u j : ZMod N)) ∈ S → Pair N 0 (∑ j, u j • ζ 0 j) (∑ j, u' j • ζ 0 j) 1 := by
    intro N hN
    have hsl : IsHolTo Set.univ (fun w => (ex x₀ w).left) := by
      have := hslice 0 hmem0
      rw [h0] at this
      exact this
    obtain ⟨Tt, hT1, hT2, hTc⟩ := GlobalTheory.T.exists_toricTorsion_cubicalWeil_one_complexPoint E H T.Z.X T.Z.t (x₀.1 ≫ genι T.Z) g N (ex x₀) hN (hExpAt x₀ hx₀) hsurj hsl
    obtain ⟨S, hSc, hS⟩ := GlobalTheory.T.torsion_count_through_exponential_lattice_kernel _ g r₀ N (ex x₀) (ζ 0) Tt hN (hadd x₀ hx₀) hsurj hζB hT1 hTc
    refine ⟨S, hSc, fun u u' hu => ?_⟩
    show GlobalTheory.UU.CubWeil T.Z.t.cub N (ex (e.symm 0) ((N : ℂ)⁻¹ • ∑ j, u j • ζ 0 j))
      (ex (e.symm 0) ((N : ℂ)⁻¹ • ∑ j, u' j • ζ 0 j)) (unitOn 1)
    rw [h0, unitOn_one]
    exact hT2 _ (hS u hu) _ (pow_eq_one_of_map _ (hadd x₀ hx₀) (hzero x₀ hx₀) hN ((hζB.2 _).2 ⟨u', rfl⟩))
  obtain ⟨r, lam, M, hc, hs, -, hMv, hrad⟩ :=
    GlobalTheory.ShFam.Hor.LogCh.ConstForm.constForm n a g r₀ K ζ Pair hLF hζan hζli hζK hB0 hζC hζstd hP1 hP2 hP3 hP4
  have hM' : ∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧
      (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧
      ∀ s' ∈ logDom n a, logExp a s' = logExp a s → ∀ i j, (hermForm Hm (lam s' i) (lam s' j)).im = M i j := by
    intro s hsD
    have hz1 : logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
      rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
      intro k
      have hk := hsD k
      by_cases h : (k : ℕ) < a
      · simp only [h, if_true] at hk
        simp only [logExp, h, if_true, Complex.norm_exp]
        exact Real.exp_lt_one_iff.2 hk
      · simp only [h, if_false] at hk
        simpa only [logExp, h, if_false] using hk
    have hnz : ∀ k : Fin n, (k : ℕ) < a → logExp a s k ≠ 0 := fun k hk => by
      simp only [logExp, hk, if_true]
      exact Complex.exp_ne_zero _
    obtain ⟨Hm, hH, hpos, -, hint, hw⟩ := hP3 _ hz1 hnz
    refine ⟨Hm, hH, hpos, fun s' hs' he => hMv s' hs' Hm ?_ ?_⟩
    · rw [he]; exact hint
    · rw [he]; exact hw
  obtain ⟨rk, τ₀, B, P, ρ, d, hρ, hρ1, hd, hPC, hPd, hPu, hrel⟩ :=
    GlobalTheory.T.exists_periodChart_holomorphicLatticeFamily n a g r₀ r ha K ζ lam M hLF hζan hζli hζK hB0 hζstd hc hs hM' hrad
  obtain ⟨ch, hch, hchs, hchρ⟩ := GlobalTheory.ShFam.Hor.LogCh.isExpChart_rescale E H Dw l Xo c O β T.Z σ n g e ex P ρ hEC hρ hρ1 hPd hPu
  have hρ0 : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ.ne'
  have hcard : Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) = g := by
    let z₁ : Fin n → ℂ := fun _ => (1 / 2 : ℂ)
    have hz₁ : z₁ ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
      rw [mem_ball_zero_iff]
      refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 fun k => ?_) (by norm_num)
      simp [z₁]
    exact (GlobalTheory.ShFam.Hor.LogCh.kernel_lattice_of_isUnf E H Dw l Xo c O β T.Z σ U hσ hU g (e.symm z₁) (ex (e.symm z₁))
      (hinner z₁ hz₁ fun k _ => by simp [z₁]) (hExpAt _ (hsymm z₁ hz₁)) (hslice z₁ hz₁)).1
  have hex : ∀ x ∈ ch.source, ∀ k, e x k = (ρ : ℂ) * ch x k := fun x hx k => by
    rw [hchρ x hx]
    simp [Complex.real_smul]
  have hx₀ch : x₀ ∈ ch.source := (hchs x₀).2 ⟨hx₀, by rw [he0]; exact Metric.mem_ball_self hρ⟩
  refine ⟨n, a, ha, g, rk, τ₀, B, ch, fun x v => ex x (P (e x) *ᵥ v), d, hPC, hch, hx₀ch, ?_, hcard, hd, ?_, ?_⟩
  · funext k
    have := hex x₀ hx₀ch k
    rw [he0] at this
    exact ((mul_eq_zero.1 this.symm).resolve_left hρ0)
  · intro x hx
    have hxe := ((hchs x).1 hx).1
    rw [hbd x hxe]
    constructor
    · intro h i hi
      apply h (Fin.castLE ha i) ((hka _).1 (by simp))
      rw [hex x hx, hi, mul_zero]
    · intro h k hk hk0
      apply h ⟨k, (hka k).2 hk⟩
      rw [hex x hx] at hk0
      exact (mul_eq_zero.1 hk0).resolve_left hρ0
  · intro x hx hin
    have hxe := ((hchs x).1 hx).1
    have hzb := ((hchs x).1 hx).2
    have hz1 : e x ∈ Metric.ball (0 : Fin n → ℂ) 1 := by rw [← htarget]; exact e.map_source hxe
    have hnz : ∀ k : Fin n, (k : ℕ) < a → e x k ≠ 0 := fun k hk =>
      (hbd x hxe).1 hin k ((hka k).1 hk)
    obtain ⟨s, hsD, hsz⟩ := exists_logExp_eq n a (e x) hz1 hnz
    have hsl : IsHolTo Set.univ (fun w => (ex x w).left) := by
      have := hslice (e x) hz1
      rw [e.left_inv hxe] at this
      exact this
    obtain ⟨-, Hm, hH, hpos, -, hint, hweil⟩ :=
      GlobalTheory.ShFam.Hor.LogCh.kernel_lattice_of_isUnf E H Dw l Xo c O β T.Z σ U hσ hU g x (ex x) hin (hExpAt x hxe) hsl
    have hKz : ∀ w, w ∈ K (logExp a s) ↔ ex x w = 1 := fun w => by
      rw [hsz]
      show ex (e.symm (e x)) w = 1 ↔ _
      rw [e.left_inv hxe]
    have hlamrel := hMv s hsD Hm (fun v hv w hw => hint v w ((hKz v).1 hv) ((hKz w).1 hw))
      (fun N v w hN hv hw => by
        show GlobalTheory.UU.CubWeil T.Z.t.cub N (ex (e.symm (logExp a s)) ((N : ℂ)⁻¹ • v))
          (ex (e.symm (logExp a s)) ((N : ℂ)⁻¹ • w)) _
        rw [hsz, e.left_inv hxe]
        exact hweil N v w _ hN ((hKz v).1 hv) ((hKz w).1 hw) rfl)
    have key := hrel s hsD (hsz ▸ hzb) Hm hlamrel
    have hchx : ρ⁻¹ • e x = ch x := by rw [hchρ x hx, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]
    rw [hsz, hchx] at key
    rw [← key]
    have hPinj : Function.Injective (P (e x)).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (hPu _ hzb))
    refine ⟨Matrix.isHermitian_mul_mul_conjTranspose _ hH, fun u hu => ?_, fun v w hv hw => ?_,
      fun k v w ζ' hk hv hw hζ' => ?_⟩
    · rw [hermForm_pull']
      exact hpos _ (fun h0' => hu (hPinj (by rw [h0', Matrix.mulVec_zero])))
    · rw [hermForm_pull']
      exact hint _ _ hv hw
    · rw [hermForm_pull'] at hζ'
      have e1 : ∀ u : Fin g → ℂ, P (e x) *ᵥ ((k : ℂ)⁻¹ • u) = (k : ℂ)⁻¹ • (P (e x) *ᵥ u) := fun u =>
        Matrix.mulVec_smul _ _ _
      show GlobalTheory.UU.CubWeil T.Z.t.cub k (ex x (P (e x) *ᵥ ((k : ℂ)⁻¹ • v))) (ex x (P (e x) *ᵥ ((k : ℂ)⁻¹ • w))) (unitOn ζ')
      rw [e1, e1]
      exact hweil k _ _ ζ' hk hv hw hζ'

end GlobalTheory.ShFam.Hor.LogCh.PerChart
end
end

section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_riemannForm_periodChart_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ x₀ : GlobalTheory.CxPts (genStr T.Z) σ, ∃ (n a : ℕ) (ha : a ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g) (d : ℝ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ IsExpChart ch₀ ex ∧ x₀ ∈ ch₀.source ∧ ch₀ x₀ = 0 ∧ Fintype.card ((Σ τ : E →+* ℂ, Fin (Dw.mult τ))) = g ∧ 0 < d ∧ (∀ x ∈ ch₀.source, Inner x ↔ ∀ i : Fin a, ch₀ x (Fin.castLE ha i) ≠ 0) ∧ ∀ x ∈ ch₀.source, Inner x → ((((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹).IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm (((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹) u u).re) ∧ (∀ v w : Fin g → ℂ, ex x v = 1 → ex x w = 1 → ∃ m : ℤ, (hermForm (((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹) v w).im = m) ∧ ∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex x v = 1 → ex x w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm (((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹) v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil T.Z.t.cub k (ex x ((k : ℂ)⁻¹ • v)) (ex x ((k : ℂ)⁻¹ • w)) (unitOn ζ)) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.PerChart.exists_riemann_period_chart | exact GlobalTheory.ShFam.Hor.LogCh.PerChart.exists_riemann_period_chart | (intros; apply GlobalTheory.ShFam.Hor.LogCh.PerChart.exists_riemann_period_chart <;> assumption)
end

section
section
open Set

namespace GlobalTheory

theorem punctured_unit_disc_eq_exp_image :
    Metric.ball (0:ℂ) 1 \ {0} = Complex.exp '' {z : ℂ | z.re < 0} := by
  ext w
  constructor
  · rintro ⟨hb, h0⟩
    have h0' : w ≠ 0 := h0
    refine ⟨Complex.log w, ?_, Complex.exp_log h0'⟩
    rw [Set.mem_setOf_eq, Complex.log_re]
    rw [Metric.mem_ball, dist_zero_right] at hb
    exact Real.log_neg (norm_pos_iff.mpr h0') hb
  · rintro ⟨z, hz, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_exp]
      exact Real.exp_lt_one_iff.mpr hz
    · exact Complex.exp_ne_zero z

theorem isPreconnected_punctured_unit_disc :
    IsPreconnected (Metric.ball (0:ℂ) 1 \ {0}) := by
  rw [punctured_unit_disc_eq_exp_image]
  exact (convex_halfSpace_re_lt 0).isPreconnected.image _ Complex.continuous_exp.continuousOn

theorem isPreconnected_polydisc_first_coords_ne_zero :
    ∀ (n a : ℕ) (ha : a ≤ n), _root_.IsPreconnected {z : Fin n → ℂ | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0} := by
  intro n a ha
  have hS : {z : Fin n → ℂ | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0}
      = Set.pi univ (fun k : Fin n => if (k:ℕ) < a then Metric.ball (0:ℂ) 1 \ {0} else Metric.ball (0:ℂ) 1) := by
    ext z
    rw [ball_pi _ one_pos]
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Pi.zero_apply]
    constructor
    · rintro ⟨hb, hne⟩ k
      split_ifs with hk
      · exact ⟨hb k, fun h => hne ⟨k, hk⟩ (by simpa using h)⟩
      · exact hb k
    · intro h
      refine ⟨fun k => ?_, fun i => ?_⟩
      · have := h k
        split_ifs at this
        · exact this.1
        · exact this
      · have := h (Fin.castLE ha i)
        rw [if_pos (by simp)] at this
        exact this.2
  rw [hS]
  apply isPreconnected_univ_pi
  intro k
  split_ifs
  · exact isPreconnected_punctured_unit_disc
  · exact (convex_ball (0:ℂ) 1).isPreconnected

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPreconnected_ball_inter_coords_ne_zero : ∀ (n a : ℕ) (ha : a ≤ n), _root_.IsPreconnected {z : Fin n → ℂ | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0} := by
  atlas_forward_decl GlobalTheory.isPreconnected_polydisc_first_coords_ne_zero
end

section
section
open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.HodgeSmooth.chart_comp_locconst : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ (n : ℕ) (ch : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr Z) σ) (Fin n → ℂ)), IsHolTo ch.target (fun z => (ch.symm z).1) → ∀ (k₀ : U.Comp) (x₀ : (U.X k₀).dom), cxPt Z (U.un k₀ x₀) ∈ ch.source → ∃ B : Set (Fin n → ℂ), IsOpen B ∧ ch (cxPt Z (U.un k₀ x₀)) ∈ B ∧ ∀ z ∈ B, ∀ (k : U.Comp) (x : (U.X k).dom), cxPt Z (U.un k x) = ch.symm z → k = k₀ := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ r U hσ hU h1 n ch hsy k₀ x₀ hy₀
  obtain ⟨W, hinj⟩ := GlobalTheory.HodgeSmooth.exists_unfWit_inj hσ hU h1
  have := Z.jQ_open
  have hB₀ := (hsy Z.jQ.opensRange 0).1
  set B₀ := {b ∈ ch.target | ⊤ ≤ (ch.symm b).1 ⁻¹ᵁ Z.jQ.opensRange} with hB₀def
  set y₀ := U.un k₀ x₀ with hy₀def
  have hb₀ : ch (cxPt Z y₀) ∈ B₀ := by
    refine ⟨ch.map_source hy₀, ?_⟩
    rw [ch.left_inv hy₀]
    intro s _
    exact ⟨GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) y₀ s, (Scheme.Hom.comp_apply (GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) y₀) Z.jQ s).symm⟩
  have : Nonempty (Sp ℂ ⟶ Xo.XF c) := ⟨GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) y₀⟩
  have hw : ∀ b ∈ B₀, ∃ w : Sp ℂ ⟶ Xo.XF c, w ≫ Z.jQ = (ch.symm b).1 := fun b hb =>
    ⟨IsOpenImmersion.lift Z.jQ _ (by rintro _ ⟨s, rfl⟩; exact hb.2 (Set.mem_univ s)), IsOpenImmersion.lift_fac _ _ _⟩
  choose! w hw using hw
  have hwh : IsHolTo B₀ w := GlobalTheory.TrueCx.TorHolo.isHolTo_of_openImmersion Z.jQ
    (GlobalTheory.LocLift.isHolTo_congr (GlobalTheory.LocLift.isHolTo_mono hsy hB₀ fun b hb => hb.1) hw)
  have hyh := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp hwh (pullback.fst _ _)
  have hsnd : ∀ b ∈ B₀, w b ≫ pullback.snd _ _ = spMap σ := fun b hb => by
    rw [← Z.jQ_over, ← Category.assoc, hw b hb]
    exact (ch.symm b).2
  obtain ⟨B, i, P, hB, hbB, hsub, hP, hu⟩ := W.F.lift n B₀ (fun x => w x ≫ pullback.fst _ _) hB₀
    (fun x hx => by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hsnd _ hx, ← Spec.map_comp]
      rfl) hyh _ hb₀
  have hik : ∀ z ∈ B, ∀ (k : U.Comp) (x : (U.X k).dom), cxPt Z (U.un k x) = ch.symm z → W.ik k = i := by
    intro z hz k x hkx
    have h1' : w z = GlobalTheory.AllWt.ptF (S := Formalism.L2.Pj.CAt σ) (U.un k x) :=
      (cancel_mono Z.jQ).1 ((hw z (hsub hz)).trans (congrArg Subtype.val hkx.symm))
    have h2 : W.F.u i (P z) = (U.un k x).x := by
      rw [hu z hz, h1']
      exact GlobalTheory.ShFam.ptF_fst _
    exact W.F.disj _ _ _ _ (W.period k x) (hP.1 z hz) ((W.lie k x).1.symm.trans h2.symm)
  have hk₀ : W.ik k₀ = i := hik _ hbB k₀ x₀ (by rw [ch.left_inv hy₀])
  exact ⟨B, hB, hbB, fun z hz k x hkx => hinj ((hik z hz k x hkx).trans hk₀.symm)⟩
end

open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormalFrames_same_component_near_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ (n : ℕ) (ch : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr Z) σ) (Fin n → ℂ)), IsHolTo ch.target (fun z => (ch.symm z).1) → ∀ (k₀ : U.Comp) (x₀ : (U.X k₀).dom), cxPt Z (U.un k₀ x₀) ∈ ch.source → ∃ B : Set (Fin n → ℂ), IsOpen B ∧ ch (cxPt Z (U.un k₀ x₀)) ∈ B ∧ ∀ z ∈ B, ∀ (k : U.Comp) (x : (U.X k).dom), cxPt Z (U.un k x) = ch.symm z → k = k₀ := by
  atlas_forward_decl GlobalTheory.HodgeSmooth.chart_comp_locconst
end

section
section
open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

section EigenvectorOrthogonality

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.ShFam
open scoped ComplexOrder

namespace GlobalTheory.HodgeSmooth.EigOrth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

open Classical in

def riemConst (U : Formalism.L2.PjFree.Unf Xo c σ r) (k : U.Comp) (τ : E →+* ℂ) : ℝ :=
  2 * ((if Formalism.L2.PjFree.relab c σ τ ∈ (U.X k).Ψ then Formalism.L2.PjFree.relab c σ τ
    else ComplexEmbedding.conjugate (Formalism.L2.PjFree.relab c σ τ)) (-(U.X k).ξ0)).im

theorem exists_diag_im {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (W : UnfWit U) (k : U.Comp) (x : (U.X k).dom) (hx : IsOrth (U.X k) x.1) :
    ∃ D : Fin W.g → ℂ, (∀ τ (j : Fin (Dw.mult τ)), D (W.e.symm ⟨τ, j⟩) = ((riemConst U k τ : ℝ) : ℂ)) ∧
      ∀ v w, (hermForm (diagonal D) (W.Pm k x v) (W.Pm k x w)).im = (W.F.Di (W.ik k)).EF v w := by
  classical
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨f, hf⟩ := FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hU.1
    (Formalism.L2.PjFree.relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  rw [← hp0] at hf
  have hper (v) : W.Pm k x v = perVec (U.X k) (W.e.trans f) x.1 (W.φ k v : Fin r → E) := funext fun j => by
    rw [W.Pm_eq, perVec, Equiv.trans_apply]
    have h := hf (W.e j)
    generalize f (W.e j) = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega), Formalism.L2.PjFree.perFr, dif_pos a, dif_pos hn]
    · rw [if_pos (by omega), Formalism.L2.PjFree.perFr, dif_neg a,
        dif_pos (show conjEmb (Formalism.L2.PjFree.relab c σ (W.e j).1) ∈ (U.X k).Ψ from hτ), dif_pos hn]
      rfl
  refine ⟨diagXi (U.X k) (W.e.trans f), fun τ j => ?_, fun v w => ?_⟩
  · rw [diagXi, Equiv.trans_apply, Equiv.apply_symm_apply]
    rcases hf ⟨τ, j⟩ with ⟨a, h1, -⟩ | ⟨a, h1, -, -⟩
    · rw [h1]
      simp only [riemConst, if_pos a]
    · rw [h1]
      simp only [riemConst, if_neg a]
  · rw [hper, hper, im_diag_ortho _ _ _ hx, ← W.iso]
    simp

theorem riemConst_pos {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (W : UnfWit U) (k : U.Comp) (x : (U.X k).dom) (hx : IsOrth (U.X k) x.1)
    (τ : E →+* ℂ) (hτ : 0 < Dw.mult τ) : 0 < riemConst U k τ := by
  classical
  obtain ⟨D, hD, him⟩ := exists_diag_im hσ hU W k x hx
  obtain ⟨-, -, -, hspan, Hm₀, -, hpos, hHm₀⟩ := W.period k x
  have e := UnitDet.eq_of_im_hermForm_eq _ hspan (diagonal D) Hm₀ (by
    rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
    rw [him, hHm₀])
  set j := W.e.symm ⟨τ, ⟨0, hτ⟩⟩
  have h := hpos (Pi.single j 1) (by simp)
  rw [← e] at h
  have h2 : hermForm (diagonal D) (Pi.single j 1) (Pi.single j 1) = D j := by
    simp [hermForm]
  rw [h2, hD] at h
  simpa using h

end GlobalTheory.HodgeSmooth.EigOrth

end EigenvectorOrthogonality

open GlobalTheory.HodgeSmooth.EigOrth in

theorem GlobalTheory.HodgeSmooth.exists_diag_riem_orth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (W : UnfWit U), ∃ d : U.Comp → (E →+* ℂ) → ℝ, (∀ (k : U.Comp) (x : (U.X k).dom), IsOrth (U.X k) x.1 → ∀ τ : E →+* ℂ, 0 < Dw.mult τ → 0 < d k τ) ∧ ∀ (k : U.Comp) (x : (U.X k).dom), IsOrth (U.X k) x.1 → ∀ (i : Fin W.F.n) (P : (W.F.Di i).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) P → ∀ (Hm : Matrix (Fin W.g) (Fin W.g) ℂ), (∀ v w, (hermForm Hm (P v) (P w)).im = (W.F.Di i).EF v w) → W.F.u i P = (U.un k x).x → ∀ (τ τ' : E →+* ℂ) (zz : Fin (Dw.mult τ) → (Fin W.g → ℂ)) (zz' : Fin (Dw.mult τ') → (Fin W.g → ℂ)) (uu : Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (uu' : Fin (Dw.mult τ') → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (T' : Matrix (Fin (Dw.mult τ')) (Fin (Dw.mult τ')) ℂ), (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz b) (uu b)) → (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz' b) (uu' b)) → (∀ b, IsCombAt (U.un k x).x ((U.un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) (uu b)) → (∀ b, IsCombAt (U.un k x).x ((U.un k x).u τ') (show Fin (Dw.mult τ') → CAt σ from fun b' => T' b' b) (uu' b)) → (of fun b b' => hermForm Hm (zz b') (zz b)) = ((d k τ : ℝ) : ℂ) • (Tᴴ * T) ∧ (τ' ≠ τ → ∀ b b', hermForm Hm (zz' b') (zz b) = 0) := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hσ hU W
  refine ⟨fun k τ => riemConst U k τ, fun k x hx τ hτ => riemConst_pos hσ hU W k x hx τ hτ, ?_⟩
  intro k x hx i P hP Hm hH hPu τ τ' zz zz' uu uu' T T' hder hder' hT hT'
  obtain ⟨D, hD, him⟩ := exists_diag_im hσ hU W k x hx
  have p := W.period k x
  obtain ⟨hPx, hv⟩ := W.lie k x
  obtain ⟨h, gam, hex, hh, hiso, -⟩ := familyUnif_exp_unique E H Dw l Xo _ _ _ W.F i (W.ik k) P _ hP p
    (by rw [← hPx]; exact hPu)
  set A := LinearMap.toMatrix' h.toLinearMap with hA
  have hAv : ∀ z, A *ᵥ z = h z := fun z => by rw [hA, LinearMap.toMatrix'_mulVec]; rfl
  have hcol : ∀ (τ : E →+* ℂ) (zz : Fin (Dw.mult τ) → (Fin W.g → ℂ))
      (uu : Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left))
      (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ),
      (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz b) (uu b)) →
      (∀ b, IsCombAt (U.un k x).x ((U.un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) (uu b)) →
      ∀ b, A *ᵥ zz b = ∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ) := by
    intro τ zz uu T hder hT b
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ _ _ W.F _ _ p _ ((U.un k x).u τ) _ (hv τ) _
      (uu b)).1 (hPx ▸ hT b)
    have d2 := (ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ _ _ W.F _ P hP _ _ h.toLinearMap p hex _ _).1 (hder b)
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ W.F _ _ p
    rw [hAv]
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  have key := UnitDet.eq_of_im_hermForm_eq _ hP.2.2.2.1
    (Aᵀ * (diagonal D * A.map (starRingEnd ℂ))) Hm (by
      rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
      rw [← UnitDet.hermForm_mulVec, hAv, hAv, ← hh, ← hh, him, hiso, hH])
  refine ⟨?_, fun hne b b' => ?_⟩
  · have hsupp : ∀ b, diagonal D *ᵥ star (∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ)) =
        (((riemConst U k τ : ℝ) : ℂ) • (1 : Matrix (Fin W.g) (Fin W.g) ℂ)) *ᵥ
          star (∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ)) := by
      intro b
      simp only [smul_mulVec, Matrix.one_mulVec]
      funext p'
      rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
      by_cases hp : ∃ j, W.e.symm ⟨τ, j⟩ = p'
      · obtain ⟨j, rfl⟩ := hp
        rw [hD τ j]
      · push_neg at hp
        have : (∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ)) p' = 0 := by
          rw [Finset.sum_apply]
          exact Finset.sum_eq_zero fun j _ => by rw [Pi.smul_apply, Pi.single_eq_of_ne (hp j).symm, smul_zero]
        simp [Pi.star_apply, this]
    ext b b'
    rw [of_apply, ← key, ← UnitDet.hermForm_mulVec, hcol τ zz uu T hder hT, hcol τ zz uu T hder hT, hermForm,
      hsupp, ← hermForm]
    beta_reduce
    generalize ((riemConst U k τ : ℝ) : ℂ) = dd
    clear hsupp key hcol hAv hiso hh hex him hD hT hder hH hPu hT' hder'
    have hi : ∀ j j' : Fin (Dw.mult τ), W.e.symm ⟨τ, j⟩ = W.e.symm ⟨τ, j'⟩ ↔ j = j' := fun j j' => by simp
    simp [hermForm, smul_mulVec, sum_dotProduct, dotProduct_sum, star_sum, Pi.single_apply, hi, mul_apply, mul_comm]
  · rw [← key, ← UnitDet.hermForm_mulVec, hcol τ' zz' uu' T' hder' hT', hcol τ zz uu T hder hT]
    simp only [hermForm, dotProduct, mulVec_diagonal, Pi.star_apply]
    refine Finset.sum_eq_zero fun q _ => ?_
    by_cases hq : ∃ j, W.e.symm ⟨τ', j⟩ = q
    · obtain ⟨j, rfl⟩ := hq
      have : (∑ j'', T j'' b • (Pi.single (W.e.symm ⟨τ, j''⟩) 1 : Fin W.g → ℂ)) (W.e.symm ⟨τ', j⟩) = 0 := by
        rw [Finset.sum_apply]
        refine Finset.sum_eq_zero fun j'' _ => ?_
        rw [Pi.smul_apply, Pi.single_eq_of_ne, smul_zero]
        intro he
        exact hne (congrArg Sigma.fst (W.e.symm.injective he))
      rw [this]
      simp
    · push_neg at hq
      have : (∑ j, T' j b' • (Pi.single (W.e.symm ⟨τ', j⟩) 1 : Fin W.g → ℂ)) q = 0 := by
        rw [Finset.sum_apply]
        exact Finset.sum_eq_zero fun j _ => by rw [Pi.smul_apply, Pi.single_eq_of_ne (hq j).symm, smul_zero]
      rw [this]
      simp
end
end

open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_diagonal_riemannForm_orthonormalFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (W : UnfWit U), ∃ d : U.Comp → (E →+* ℂ) → ℝ, (∀ (k : U.Comp) (x : (U.X k).dom), IsOrth (U.X k) x.1 → ∀ τ : E →+* ℂ, 0 < Dw.mult τ → 0 < d k τ) ∧ ∀ (k : U.Comp) (x : (U.X k).dom), IsOrth (U.X k) x.1 → ∀ (i : Fin W.F.n) (P : (W.F.Di i).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) P → ∀ (Hm : Matrix (Fin W.g) (Fin W.g) ℂ), (∀ v w, (hermForm Hm (P v) (P w)).im = (W.F.Di i).EF v w) → W.F.u i P = (U.un k x).x → ∀ (τ τ' : E →+* ℂ) (zz : Fin (Dw.mult τ) → (Fin W.g → ℂ)) (zz' : Fin (Dw.mult τ') → (Fin W.g → ℂ)) (uu : Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (uu' : Fin (Dw.mult τ') → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (T' : Matrix (Fin (Dw.mult τ')) (Fin (Dw.mult τ')) ℂ), (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz b) (uu b)) → (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz' b) (uu' b)) → (∀ b, IsCombAt (U.un k x).x ((U.un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) (uu b)) → (∀ b, IsCombAt (U.un k x).x ((U.un k x).u τ') (show Fin (Dw.mult τ') → CAt σ from fun b' => T' b' b) (uu' b)) → (of fun b b' => hermForm Hm (zz b') (zz b)) = ((d k τ : ℝ) : ℂ) • (Tᴴ * T) ∧ (τ' ≠ τ → ∀ b b', hermForm Hm (zz' b') (zz b) = 0) := by
  atlas_forward_decl GlobalTheory.HodgeSmooth.exists_diag_riem_orth
end

section
open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.HodgeInteriorGram

theorem isDerivAt0_comp_equiv {g g' : ℕ} {X : Scheme.{0}} (L : (Fin g' → ℂ) ≃L[ℂ] (Fin g → ℂ))
    (y : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (w : Fin g' → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) :
    IsDerivAt0 (fun z => y (L z)) w v ↔ IsDerivAt0 y (L w) v := by
  unfold IsDerivAt0
  simp only [map_zero]
  refine and_congr Iff.rfl (forall_congr' fun U => forall_congr' fun h => forall_congr' fun f => ?_)
  rw [show (fun z => valAt' (y (L z)) U f) = (fun z => valAt' (y z) U f) ∘ L from rfl, L.comp_right_fderiv,
    map_zero]
  rfl

theorem int_eq_of_exp_eq (m n : ℤ) (h : ∀ k : ℕ, 0 < k →
    Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) :
    m = n := by
  have hI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have key : ∀ K : ℕ, 0 < K → (K : ℤ) ∣ n - m := by
    intro K hK
    obtain ⟨N, hN⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h K hK)
    have hkC : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
    have e : ((n - m : ℤ) : ℂ) = ((K * N : ℤ) : ℂ) := by
      push_cast
      linear_combination (norm := skip) ((K : ℂ) / (2 * Real.pi * Complex.I)) * hN
      field_simp
      ring
    exact ⟨N, by exact_mod_cast e⟩
  have hz : n - m = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd (key ((n - m).natAbs + 1) (Nat.succ_pos _)) ?_
    rw [Int.abs_eq_natAbs]
    push_cast
    omega
  omega

theorem hermForm_pull' {g g' : ℕ} (M : Matrix (Fin g') (Fin g) ℂ) (Hm : Matrix (Fin g') (Fin g') ℂ)
    (z w : Fin g → ℂ) : hermForm (Mᵀ * Hm * Mᵀᴴ) z w = hermForm Hm (M *ᵥ z) (M *ᵥ w) := by
  have : Mᵀᴴ *ᵥ (star w) = star (M *ᵥ w) := by
    rw [Matrix.star_mulVec, ← Matrix.mulVec_transpose]
    rfl
  rw [hermForm, hermForm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, this, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

end GlobalTheory.HodgeInteriorGram

theorem GlobalTheory.HodgeInteriorGram.gram_eq_riem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (W : UnfWit (unfFam U σ)), Function.Injective W.ik → ∀ (d : (unfFam U σ).Comp → (E →+* ℂ) → ℝ), (∀ (k : (unfFam U σ).Comp) (x : ((unfFam U σ).X k).dom), IsOrth ((unfFam U σ).X k) x.1 → ∀ τ : E →+* ℂ, 0 < Dw.mult τ → 0 < d k τ) → (∀ (k : (unfFam U σ).Comp) (x : ((unfFam U σ).X k).dom), IsOrth ((unfFam U σ).X k) x.1 → ∀ (i : Fin W.F.n) (P : (W.F.Di i).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) P → ∀ (Hm : Matrix (Fin W.g) (Fin W.g) ℂ), (∀ v w, (hermForm Hm (P v) (P w)).im = (W.F.Di i).EF v w) → W.F.u i P = ((unfFam U σ).un k x).x → ∀ (τ τ' : E →+* ℂ) (zz : Fin (Dw.mult τ) → (Fin W.g → ℂ)) (zz' : Fin (Dw.mult τ') → (Fin W.g → ℂ)) (uu : Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (uu' : Fin (Dw.mult τ') → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (T' : Matrix (Fin (Dw.mult τ')) (Fin (Dw.mult τ')) ℂ), (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz b) (uu b)) → (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz' b) (uu' b)) → (∀ b, IsCombAt ((unfFam U σ).un k x).x (((unfFam U σ).un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) (uu b)) → (∀ b, IsCombAt ((unfFam U σ).un k x).x (((unfFam U σ).un k x).u τ') (show Fin (Dw.mult τ') → CAt σ from fun b' => T' b' b) (uu' b)) → (of fun b b' => hermForm Hm (zz b') (zz b)) = ((d k τ : ℝ) : ℂ) • (Tᴴ * T) ∧ (τ' ≠ τ → ∀ b b', hermForm Hm (zz' b') (zz b) = 0)) → ∀ (g : ℕ) (x : GlobalTheory.CxPts (genStr Z) σ) (exx : (Fin g → ℂ) → (Over.mk (x.1 ≫ genι Z) ⟶ Z.t.G)), Inner x → IsExpAt Z.t (x.1 ≫ genι Z) exx → IsHolTo Set.univ (fun w => (exx w).left) → ∀ (k : (unfFam U σ).Comp) (x' : ((unfFam U σ).X k).dom), IsOrth ((unfFam U σ).X k) x'.1 → cxPt Z ((unfFam U σ).un k x') = x → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ v w : Fin g → ℂ, exx v = 1 → exx w = 1 → ∃ m : ℤ, (hermForm Hm v w).im = m) → (∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → exx v = 1 → exx w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (exx ((k : ℂ)⁻¹ • v)) (exx ((k : ℂ)⁻¹ • w)) (unitOn ζ)) → ∀ (f : EigFrame Z σ (x.1 ≫ genι Z)) (Wd : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ), Dirs ⟨x, f⟩ (fun w => (exx w).left) Wd → (∀ τ, (hodgeMet Z U).gram x f τ = (((2 * Real.pi / d k τ : ℝ)) : ℂ) • Matrix.of fun b b' => hermForm Hm (Wd ⟨τ, b'⟩) (Wd ⟨τ, b⟩)) ∧ ∀ p q : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), p.1 ≠ q.1 → hermForm Hm (Wd p) (Wd q) = 0 := by
  classical
  intro E _ _ _ H Dw l Xo c O _ β Z σ U hσ hU W hinj d hdpos hd g x exx hin hex hhol k x' hx' hkx Hm hint hweil f Wd hdirs
  have hexf : ∃ g₀, IsHodgeFrame (unfFam U) x g₀ := by
    rw [← hkx]; exact ⟨_, isHodgeFrame_cxFrame (U := unfFam U) hσ hx'⟩
  have hg : ∀ τ, (hodgeMet Z U).gram x f τ =
      ((2 * Real.pi : ℝ) : ℂ) • ((hexf.choose.co f τ)ᴴ * hexf.choose.co f τ) := fun τ => dif_pos hexf
  obtain ⟨k'', x'', hx'', hkx'', hv⟩ := GlobalTheory.HodgeSmooth.hodgeFrame_comp hσ hexf.choose_spec
  have hk : k'' = k := by
    apply hinj
    have e := x_eq_of_cxPt (congrArg Subtype.val (hkx''.trans hkx.symm))
    exact W.F.disj _ _ _ _ (W.period k'' x'') (W.period k x')
      ((W.lie k'' x'').1.symm.trans (e.trans (W.lie k x').1))
  subst hk
  have hu : W.F.u (W.ik k'') (W.Pm k'' x'') =
      (GlobalTheory.AllWt.ptF (S := CAt σ) ((unfFam U σ).un k'' x'') : Sp ℂ ⟶ Xo.XF c) ≫
        pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) :=
    (W.lie k'' x'').1.symm.trans (ptF_fst _).symm
  have hp : (GlobalTheory.AllWt.ptF (S := CAt σ) ((unfFam U σ).un k'' x'') : Sp ℂ ⟶ Xo.XF c) ≫ Z.jQ ≫
      pullback.fst Z.s (spMap β) = x.1 ≫ genι Z := by
    rw [← hkx'']
    exact (Category.assoc _ _ _).symm
  have hper := W.period k'' x''
  have he' := isExpAt_pushEx E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper
  have hhol' := pushEx_hol E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper
  have hker := pushEx_eq_one_iff E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper
  have hcw := pushEx_cubWeil E H Dw l Xo c O β Z W.g _ _ W.F _ _ _ _ hu hp hper
  obtain ⟨L, hL⟩ := exp_eq_comp_linearEquiv E H Z.X Z.t (x.1 ≫ genι Z) g W.g exx _ hex hhol he' hhol'
  set A : Matrix (Fin g) (Fin W.g) ℂ := LinearMap.toMatrix' L.toLinearMap with hA
  have hAv : ∀ z, A *ᵥ z = L z := fun z => LinearMap.toMatrix'_mulVec _ z
  set Hm' : Matrix (Fin W.g) (Fin W.g) ℂ := Aᵀ * Hm * Aᵀᴴ with hHm'
  have hpull : ∀ z w, hermForm Hm' z w = hermForm Hm (L z) (L w) := fun z w => by
    rw [hHm', GlobalTheory.HodgeInteriorGram.hermForm_pull', hAv, hAv]
  have hIm : ∀ a b, (hermForm Hm' (W.Pm k'' x'' a) (W.Pm k'' x'' b)).im = (W.F.Di (W.ik k'')).EF a b := by
    intro a b
    rw [hpull]
    have h1 : exx (L (W.Pm k'' x'' a)) = 1 := by rw [← hL]; exact (hker _).2 ⟨a, rfl⟩
    have h2 : exx (L (W.Pm k'' x'' b)) = 1 := by rw [← hL]; exact (hker _).2 ⟨b, rfl⟩
    obtain ⟨m, hm⟩ := hint _ _ h1 h2
    rw [hm]
    congr 1
    refine GlobalTheory.HodgeInteriorGram.int_eq_of_exp_eq _ _ fun K hK => ?_
    have w1 := hweil K _ _ (Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (m : ℂ) / K))) hK h1 h2
      (by rw [hm, Complex.ofReal_intCast]; rfl)
    have w2 := hcw K a b (Units.mk0 _ (Complex.exp_ne_zero
      (-(2 * Real.pi * Complex.I) * ((W.F.Di (W.ik k'')).EF a b : ℂ) / K))) hK rfl
    rw [hL, hL, L.map_smul, L.map_smul] at w2
    exact congrArg Units.val (ReciprocityTheory.ChartRestriction.G.H1.unitOn_injective (w1.unique w2))
  set Lc := L.toContinuousLinearEquiv with hLc
  have hLc' : ∀ z, Lc z = L z := fun z => rfl
  choose w hwt hwm hwc using fun (τ : E →+* ℂ) (b : Fin (Dw.mult τ)) =>
    GlobalTheory.HodgeSmooth.exists_lift_comb ((unfFam U σ).un k'' x'') hkx'' hexf.choose f hv τ b
  have hder : ∀ τ (b : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (W.F.ex (W.ik k'') (W.Pm k'' x'') z).left)
      (Lc.symm (Wd ⟨τ, b⟩)) (w τ b ≫ Z.m0.toSABMap.φ) := by
    intro τ b
    refine isDerivAt0_ex_of_push Z W.F _ _ _ hper hu (hwt τ b).1 ?_
    rw [hwm τ b]
    have e1 : (fun z => liftEx Z W.F _ (W.ik k'') (W.Pm k'' x'') hu z ≫ Z.m.φ) =
        fun z => (exx (Lc z)).left := funext fun z => by
      rw [hLc', ← hL]
      rfl
    rw [e1]
    refine (GlobalTheory.HodgeInteriorGram.isDerivAt0_comp_equiv Lc (fun v => (exx v).left) _ _).2 ?_
    rw [Lc.apply_symm_apply]
    exact hdirs ⟨τ, b⟩
  have hmat := fun τ τ' => hd k'' x'' hx'' (W.ik k'') (W.Pm k'' x'') hper Hm' hIm (W.lie k'' x'').1.symm τ τ'
    (fun b => Lc.symm (Wd ⟨τ, b⟩)) (fun b => Lc.symm (Wd ⟨τ', b⟩)) (fun b => w τ b ≫ Z.m0.toSABMap.φ)
    (fun b => w τ' b ≫ Z.m0.toSABMap.φ) (hexf.choose.co f τ) (hexf.choose.co f τ') (hder τ) (hder τ') (hwc τ) (hwc τ')
  refine ⟨fun τ => ?_, fun p q hpq => ?_⟩
  · obtain ⟨h1, -⟩ := hmat τ τ
    rw [hg τ]
    have e2 : (of fun b b' : Fin (Dw.mult τ) => hermForm Hm (Wd ⟨τ, b'⟩) (Wd ⟨τ, b⟩)) =
        of fun b b' => hermForm Hm' (Lc.symm (Wd ⟨τ, b'⟩)) (Lc.symm (Wd ⟨τ, b⟩)) := by
      ext b b'
      simp only [of_apply, hpull, ← hLc', Lc.apply_symm_apply]
    rw [e2, h1]
    rcases Nat.eq_zero_or_pos (Dw.mult τ) with h0 | h0
    · ext b
      exact absurd b.2 (by omega)
    · have hdp := hdpos k'' x'' hx'' τ h0
      rw [smul_smul, ← Complex.ofReal_mul]
      congr 2
      field_simp
  · have h2 := (hmat q.1 p.1).2 hpq q.2 p.2
    rw [hpull, ← hLc', ← hLc', Lc.apply_symm_apply, Lc.apply_symm_apply] at h2
    exact h2
end

section
open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeMetric_frame_eq_riemannForm_at_interior_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (W : UnfWit (unfFam U σ)), Function.Injective W.ik → ∀ (d : (unfFam U σ).Comp → (E →+* ℂ) → ℝ), (∀ (k : (unfFam U σ).Comp) (x : ((unfFam U σ).X k).dom), IsOrth ((unfFam U σ).X k) x.1 → ∀ τ : E →+* ℂ, 0 < Dw.mult τ → 0 < d k τ) → (∀ (k : (unfFam U σ).Comp) (x : ((unfFam U σ).X k).dom), IsOrth ((unfFam U σ).X k) x.1 → ∀ (i : Fin W.F.n) (P : (W.F.Di i).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) P → ∀ (Hm : Matrix (Fin W.g) (Fin W.g) ℂ), (∀ v w, (hermForm Hm (P v) (P w)).im = (W.F.Di i).EF v w) → W.F.u i P = ((unfFam U σ).un k x).x → ∀ (τ τ' : E →+* ℂ) (zz : Fin (Dw.mult τ) → (Fin W.g → ℂ)) (zz' : Fin (Dw.mult τ') → (Fin W.g → ℂ)) (uu : Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (uu' : Fin (Dw.mult τ') → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (T' : Matrix (Fin (Dw.mult τ')) (Fin (Dw.mult τ')) ℂ), (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz b) (uu b)) → (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz' b) (uu' b)) → (∀ b, IsCombAt ((unfFam U σ).un k x).x (((unfFam U σ).un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) (uu b)) → (∀ b, IsCombAt ((unfFam U σ).un k x).x (((unfFam U σ).un k x).u τ') (show Fin (Dw.mult τ') → CAt σ from fun b' => T' b' b) (uu' b)) → (of fun b b' => hermForm Hm (zz b') (zz b)) = ((d k τ : ℝ) : ℂ) • (Tᴴ * T) ∧ (τ' ≠ τ → ∀ b b', hermForm Hm (zz' b') (zz b) = 0)) → ∀ (g : ℕ) (x : GlobalTheory.CxPts (genStr Z) σ) (exx : (Fin g → ℂ) → (Over.mk (x.1 ≫ genι Z) ⟶ Z.t.G)), Inner x → IsExpAt Z.t (x.1 ≫ genι Z) exx → IsHolTo Set.univ (fun w => (exx w).left) → ∀ (k : (unfFam U σ).Comp) (x' : ((unfFam U σ).X k).dom), IsOrth ((unfFam U σ).X k) x'.1 → cxPt Z ((unfFam U σ).un k x') = x → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ v w : Fin g → ℂ, exx v = 1 → exx w = 1 → ∃ m : ℤ, (hermForm Hm v w).im = m) → (∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → exx v = 1 → exx w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (exx ((k : ℂ)⁻¹ • v)) (exx ((k : ℂ)⁻¹ • w)) (unitOn ζ)) → ∀ (f : EigFrame Z σ (x.1 ≫ genι Z)) (Wd : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ), Dirs ⟨x, f⟩ (fun w => (exx w).left) Wd → (∀ τ, (hodgeMet Z U).gram x f τ = (((2 * Real.pi / d k τ : ℝ)) : ℂ) • Matrix.of fun b b' => hermForm Hm (Wd ⟨τ, b'⟩) (Wd ⟨τ, b⟩)) ∧ ∀ p q : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), p.1 ≠ q.1 → hermForm Hm (Wd p) (Wd q) = 0 := by
  first | exact @GlobalTheory.HodgeInteriorGram.gram_eq_riem | exact GlobalTheory.HodgeInteriorGram.gram_eq_riem | (intros; apply GlobalTheory.HodgeInteriorGram.gram_eq_riem <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HodgeChart

theorem hodgeMet_eq_riem_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (n a : ℕ) (ha : a ≤ n) (g : ℕ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g), IsExpChart ch₀ ex → Fintype.card ((Σ τ : E →+* ℂ, Fin (Dw.mult τ))) = g → (∀ x ∈ ch₀.source, Inner x ↔ ∀ i : Fin a, ch₀ x (Fin.castLE ha i) ≠ 0) → ∃ κ : (E →+* ℂ) → ℝ, (∀ τ, 0 < κ τ) ∧ ∀ x ∈ ch₀.source, Inner x → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, ((Hm).IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm (Hm) u u).re) ∧ (∀ v w : Fin g → ℂ, ex x v = 1 → ex x w = 1 → ∃ m : ℤ, (hermForm (Hm) v w).im = m) ∧ ∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex x v = 1 → ex x w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm (Hm) v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil T.Z.t.cub k (ex x ((k : ℂ)⁻¹ • v)) (ex x ((k : ℂ)⁻¹ • w)) (unitOn ζ)) → ∀ (f : EigFrame T.Z σ (x.1 ≫ genι T.Z)) (W : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ), Dirs ⟨x, f⟩ (fun w => (ex x w).left) W → (∀ τ, (hodgeMet T.Z U).gram x f τ = ((κ τ : ℝ) : ℂ) • Matrix.of fun b b' => hermForm Hm (W ⟨τ, b'⟩) (W ⟨τ, b⟩)) ∧ ∀ p q : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), p.1 ≠ q.1 → hermForm Hm (W p) (W q) = 0 := by
  intro E _ _ _ H Dw l Xo c O _ β Y T σ U hσ hU n a ha g ch₀ ex hEC _ hIn
  classical
  obtain ⟨htarget, -, hsymmHol, hadd, hjoint, htan⟩ := hEC
  have hsrc : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ch₀.symm z ∈ ch₀.source := fun z hz =>
    ch₀.map_target (by rw [htarget]; exact hz)
  set Ω : Set (Fin n → ℂ) := {z | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0} with hΩ
  have hinΩ : ∀ x ∈ ch₀.source, Inner x → ch₀ x ∈ Ω := fun x hx hI =>
    ⟨by rw [← htarget]; exact ch₀.map_source hx, (hIn x hx).1 hI⟩
  have hΩin : ∀ z ∈ Ω, Inner (ch₀.symm z) := fun z hz =>
    (hIn _ (hsrc z hz.1)).2 (by rw [ch₀.right_inv (by rw [htarget]; exact hz.1)]; exact hz.2)
  by_cases h1 : 1 ≤ Dw.p + Dw.q
  swap
  · have hm : ∀ τ : E →+* ℂ, Dw.mult τ = 0 := fun τ => by unfold Datum.mult; split_ifs <;> omega
    refine ⟨fun _ => 1, fun _ => one_pos, fun x _ _ Hm _ f Wd _ => ⟨fun τ => ?_, fun p q _ => ?_⟩⟩
    · ext i
      have h0 := hm τ
      have h2 := i.2
      omega
    · have h0 := hm p.1
      have h2 := p.2.2
      omega
  set U' := unfFam U σ with hU'def
  have hU' : Formalism.L2.PjFree.IsUnf U' := by rw [hU'def, unfFam_self]; exact hU
  obtain ⟨W, hinj⟩ := exists_unfWit_inj hσ hU' h1
  obtain ⟨d, hdpos, hd⟩ := GlobalTheory.T.exists_diagonal_riemannForm_orthonormalFrame E H Dw l Xo c σ _ U' hσ hU' W
  have hreach : ∀ z ∈ Ω, ∃ (k : U'.Comp) (x : (U'.X k).dom), IsOrth (U'.X k) x.1 ∧
      cxPt T.Z (U'.un k x) = ch₀.symm z :=
    fun z hz => exists_orth (Z := T.Z) hσ hU' (hΩin z hz)
  by_cases hne : Ω.Nonempty
  swap
  · exact ⟨fun _ => 1, fun _ => one_pos, fun x hx hI => absurd ⟨ch₀ x, hinΩ x hx hI⟩ hne⟩
  obtain ⟨z₁, hz₁⟩ := hne
  have hreach' : ∀ z, ∃ k : U'.Comp, z ∈ Ω → ∃ x : (U'.X k).dom, IsOrth (U'.X k) x.1 ∧
      cxPt T.Z (U'.un k x) = ch₀.symm z := fun z => by
    by_cases h : z ∈ Ω
    · obtain ⟨k, x, hx⟩ := hreach z h
      exact ⟨k, fun _ => ⟨x, hx⟩⟩
    · exact ⟨(hreach z₁ hz₁).choose, fun h' => absurd h' h⟩
  choose comp hcomp using hreach'
  letI : TopologicalSpace U'.Comp := ⊥
  haveI : DiscreteTopology U'.Comp := ⟨rfl⟩
  have hcont : ContinuousOn comp Ω := by
    intro z hz
    obtain ⟨x₀, -, hx₀⟩ := hcomp z hz
    have hs0 : cxPt T.Z (U'.un (comp z) x₀) ∈ ch₀.source := by rw [hx₀]; exact hsrc z hz.1
    obtain ⟨B, hBo, hzB, hB⟩ := GlobalTheory.T.orthonormalFrames_same_component_near_chart E H Dw l Xo c O β T.Z σ _ U' hσ hU' h1 n ch₀ hsymmHol (comp z) x₀ hs0
    rw [hx₀, ch₀.right_inv (by rw [htarget]; exact hz.1)] at hzB
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hBo.mem_nhds hzB)] with w hw hwB
    obtain ⟨x, -, hx⟩ := hcomp w hw
    exact hB w hwB _ x hx
  have hconst : ∀ z ∈ Ω, comp z = comp z₁ := fun z hz =>
    (GlobalTheory.T.isPreconnected_ball_inter_coords_ne_zero n a ha).constant hcont hz hz₁
  refine ⟨fun τ => if 0 < d (comp z₁) τ then 2 * Real.pi / d (comp z₁) τ else 1, fun τ => ?_, ?_⟩
  · dsimp only
    split_ifs with h
    · exact div_pos Real.two_pi_pos h
    · exact one_pos
  intro x hx hI Hm hHm f Wd hW
  have hz := hinΩ x hx hI
  obtain ⟨x', hx'o, hx'⟩ := hcomp _ hz
  rw [ch₀.left_inv hx] at hx'
  have hk := hconst _ hz
  have hExpAt : IsExpAt T.Z.t (x.1 ≫ genι T.Z) (ex x) := ⟨hadd x hx, (htan x hx).1, (htan x hx).2⟩
  have hslice : IsHolTo Set.univ (fun w => (ex x w).left) := by
    have hmem : ch₀ x ∈ ch₀.target := ch₀.map_source hx
    have := GlobalTheory.HolPeriods.isHolTo_comp (φ := fun w : Fin g → ℂ => (ch₀ x, w)) hjoint isOpen_univ
      ((differentiableOn_const (ch₀ x)).prodMk differentiableOn_id) fun w _ => Set.mk_mem_prod hmem (Set.mem_univ w)
    dsimp only at this
    rw [ch₀.left_inv hx] at this
    exact this
  obtain ⟨hg, ho⟩ := GlobalTheory.T.hodgeMetric_frame_eq_riemannForm_at_interior_point E H Dw l Xo c O β T.Z σ U hσ hU W hinj d hdpos hd g x (ex x) hI hExpAt hslice _ x' hx'o hx'
    Hm hHm.2.2.1 hHm.2.2.2 f Wd hW
  refine ⟨fun τ => ?_, ho⟩
  rw [hg τ]
  by_cases hm : Dw.mult τ = 0
  · ext i
    have h2 := i.2
    omega
  · have hpos := hdpos _ x' hx'o τ (Nat.pos_of_ne_zero hm)
    have e : d (comp (ch₀ x)) τ = d (comp z₁) τ := by rw [hk]
    rw [e] at hpos ⊢
    simp only [if_pos hpos]

end GlobalTheory.HodgeChart
end
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeMetric_eq_const_mul_riemannForm_on_expChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (n a : ℕ) (ha : a ≤ n) (g : ℕ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g), IsExpChart ch₀ ex → Fintype.card ((Σ τ : E →+* ℂ, Fin (Dw.mult τ))) = g → (∀ x ∈ ch₀.source, Inner x ↔ ∀ i : Fin a, ch₀ x (Fin.castLE ha i) ≠ 0) → ∃ κ : (E →+* ℂ) → ℝ, (∀ τ, 0 < κ τ) ∧ ∀ x ∈ ch₀.source, Inner x → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, ((Hm).IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm (Hm) u u).re) ∧ (∀ v w : Fin g → ℂ, ex x v = 1 → ex x w = 1 → ∃ m : ℤ, (hermForm (Hm) v w).im = m) ∧ ∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex x v = 1 → ex x w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm (Hm) v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil T.Z.t.cub k (ex x ((k : ℂ)⁻¹ • v)) (ex x ((k : ℂ)⁻¹ • w)) (unitOn ζ)) → ∀ (f : EigFrame T.Z σ (x.1 ≫ genι T.Z)) (W : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ), Dirs ⟨x, f⟩ (fun w => (ex x w).left) W → (∀ τ, (hodgeMet T.Z U).gram x f τ = ((κ τ : ℝ) : ℂ) • Matrix.of fun b b' => hermForm Hm (W ⟨τ, b'⟩) (W ⟨τ, b⟩)) ∧ ∀ p q : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), p.1 ≠ q.1 → hermForm Hm (W p) (W q) = 0 := by
  atlas_forward_decl GlobalTheory.HodgeChart.hodgeMet_eq_riem_chart
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.PerChart

theorem exists_periodChart_hodge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ x₀ : GlobalTheory.CxPts (genStr T.Z) σ, ∃ (n a : ℕ) (ha : a ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g) (κ : (E →+* ℂ) → ℝ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ IsExpChart ch₀ ex ∧ x₀ ∈ ch₀.source ∧ ch₀ x₀ = 0 ∧ Fintype.card ((Σ τ : E →+* ℂ, Fin (Dw.mult τ))) = g ∧ (∀ τ, 0 < κ τ) ∧ (∀ x ∈ ch₀.source, Inner x ↔ ∀ i : Fin a, ch₀ x (Fin.castLE ha i) ≠ 0) ∧ ∀ x ∈ ch₀.source, Inner x → ∀ (f : EigFrame T.Z σ (x.1 ≫ genι T.Z)) (W : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ), Dirs ⟨x, f⟩ (fun w => (ex x w).left) W → (∀ τ, (hodgeMet T.Z U).gram x f τ = ((κ τ : ℝ) : ℂ) • Matrix.of fun b b' => hermForm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹ (W ⟨τ, b'⟩) (W ⟨τ, b⟩)) ∧ ∀ p q : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), p.1 ≠ q.1 → hermForm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹ (W p) (W q) = 0 := by
  intro E _ _ _ H Dw l Xo c O _ β Y T σ U hσ hU x₀
  obtain ⟨n, a, ha, g, rk, τ₀, B, ch₀, ex, d, hP, hE, hx₀, h0, hcard, hd, hInner, hR⟩ :=
    GlobalTheory.T.exists_riemannForm_periodChart_genericFibre E H Dw l Xo c O β Y T σ U hσ hU x₀
  obtain ⟨κ, hκ, hM⟩ := GlobalTheory.T.hodgeMetric_eq_const_mul_riemannForm_on_expChart E H Dw l Xo c O β Y T σ U hσ hU n a ha g ch₀ ex hE hcard hInner
  refine ⟨n, a, ha, g, rk, τ₀, B, ch₀, ex, fun τ => κ τ * d, hP, hE, hx₀, h0, hcard,
    fun τ => mul_pos (hκ τ) hd, hInner, ?_⟩
  intro x hx hin f W hW
  obtain ⟨h1, h2⟩ := hM x hx hin _ (hR x hx hin) f W hW
  have hs : ∀ (M : Matrix (Fin g) (Fin g) ℂ) (v w : Fin g → ℂ),
      hermForm (((d : ℝ) : ℂ) • M) v w = ((d : ℝ) : ℂ) * hermForm M v w := by
    intro M v w
    simp [hermForm, Matrix.smul_mulVec, dotProduct_smul]
  refine ⟨fun τ => ?_, fun p q hpq => ?_⟩
  · rw [h1 τ]
    ext b b'
    simp only [Matrix.smul_apply, Matrix.of_apply, hs, smul_eq_mul]
    push_cast
    ring
  · have := h2 p q hpq
    rw [hs] at this
    exact (mul_eq_zero.1 this).resolve_left (by exact_mod_cast hd.ne')

end GlobalTheory.ShFam.Hor.PerChart
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodChart_hodgeMetric_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ x₀ : GlobalTheory.CxPts (genStr T.Z) σ, ∃ (n a : ℕ) (ha : a ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g) (κ : (E →+* ℂ) → ℝ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ IsExpChart ch₀ ex ∧ x₀ ∈ ch₀.source ∧ ch₀ x₀ = 0 ∧ Fintype.card ((Σ τ : E →+* ℂ, Fin (Dw.mult τ))) = g ∧ (∀ τ, 0 < κ τ) ∧ (∀ x ∈ ch₀.source, Inner x ↔ ∀ i : Fin a, ch₀ x (Fin.castLE ha i) ≠ 0) ∧ ∀ x ∈ ch₀.source, Inner x → ∀ (f : EigFrame T.Z σ (x.1 ≫ genι T.Z)) (W : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ), Dirs ⟨x, f⟩ (fun w => (ex x w).left) W → (∀ τ, (hodgeMet T.Z U).gram x f τ = ((κ τ : ℝ) : ℂ) • Matrix.of fun b b' => hermForm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹ (W ⟨τ, b'⟩) (W ⟨τ, b⟩)) ∧ ∀ p q : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), p.1 ≠ q.1 → hermForm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹ (W p) (W q) = 0 := by
  atlas_forward_decl GlobalTheory.ShFam.Hor.PerChart.exists_periodChart_hodge
end
