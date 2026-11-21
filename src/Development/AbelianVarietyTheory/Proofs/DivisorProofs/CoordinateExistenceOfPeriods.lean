import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFderivEqZero
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeSeparatesEmbeddings

section
open Module

theorem GlobalTheory.exists_zlattice_basis_realCoord_integral : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    ∃ (n : ℕ) (b : Fin n → Λ) (c : Fin n → (Fin g → ℂ) →ₗ[ℝ] ℝ),
      (∀ v, ∑ i, c i v • ((b i : Λ) : Fin g → ℂ) = v) ∧
      ∀ (φ : Λ →+ (Fin g → ℂ)) (x : Λ), ∑ i, c i (x : Fin g → ℂ) • φ (b i) = φ x := by
  intro g Λ hd hs
  haveI := hd
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  let bZ0 := Module.Free.chooseBasis ℤ Λ
  let bZ := bZ0.reindex (Fintype.equivFin _)
  let bR := bZ.ofZLatticeBasis ℝ Λ
  refine ⟨_, fun i => bZ i, fun i => bR.coord i, ?_, ?_⟩
  · intro v
    have h := bR.sum_repr v
    conv_rhs => rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [bR]
  · intro φ x
    have hx : ∀ i, bR.coord i (x : Fin g → ℂ) = ((bZ.repr x i : ℤ) : ℝ) := by
      intro i
      simp [bR, Module.Basis.ofZLatticeBasis_repr_apply]
    simp_rw [hx]
    conv_rhs => rw [← bZ.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul, map_zsmul]

alias _root_.GlobalTheory.T.lattice_real_coordinate_basis := _root_.GlobalTheory.exists_zlattice_basis_realCoord_integral
end

section
section
namespace GlobalTheory

theorem realDiag_conj_coordProj : ∀ (g : ℕ) (K : Type) (ρ : K → Fin g → ℝ), (∀ j k, j ≠ k → ∃ a, ρ a j ≠ ρ a k) →
    ∀ (T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)),
    (∀ a, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v, T (fun m ↦ (ρ a m : ℂ) * v m) = M (T v)) →
    ∀ j : Fin g, ∃ q : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v, q (T v) = T (Pi.single j (v j)) := by
  intro g K ρ hsep T hT j
  classical
  let P : (Fin g → ℝ) → Prop := fun c =>
    ∃ q : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v, T (fun m ↦ (c m : ℂ) * v m) = q (T v)
  have hconst : ∀ r : ℝ, P (fun _ => r) := by
    intro r
    refine ⟨(r : ℂ) • LinearMap.id, fun v => ?_⟩
    have h : (fun m ↦ ((r : ℝ) : ℂ) * v m) = r • v := by
      funext m; simp [Complex.real_smul]
    rw [h, map_smul]
    funext m
    simp [Complex.real_smul]
  have hadd : ∀ c d, P c → P d → P (c + d) := by
    rintro c d ⟨q1, h1⟩ ⟨q2, h2⟩
    refine ⟨q1 + q2, fun v => ?_⟩
    have h : (fun m ↦ (((c + d) m : ℝ) : ℂ) * v m)
        = (fun m ↦ (c m : ℂ) * v m) + (fun m ↦ (d m : ℂ) * v m) := by
      funext m; simp [add_mul]
    rw [h, map_add, h1, h2, LinearMap.add_apply]
  have hmul : ∀ c d, P c → P d → P (c * d) := by
    rintro c d ⟨q1, h1⟩ ⟨q2, h2⟩
    refine ⟨q1 ∘ₗ q2, fun v => ?_⟩
    calc T (fun m ↦ (((c * d) m : ℝ) : ℂ) * v m)
        = T (fun m ↦ (c m : ℂ) * ((d m : ℂ) * v m)) := by
          congr 1; funext m; simp [mul_assoc]
      _ = q1 (T (fun m ↦ (d m : ℂ) * v m)) := h1 _
      _ = (q1 ∘ₗ q2) (T v) := by rw [h2]; rfl
  have hρ : ∀ a, P (ρ a) := fun a => by
    obtain ⟨M, hM⟩ := hT a
    exact ⟨M, hM⟩
  have haff : ∀ c s t, P c → P (fun m => (c m - s) * t) := by
    intro c s t hc
    have h : (fun m => (c m - s) * t) = (c + (fun _ => -s)) * (fun _ => t) := by
      funext m; simp [sub_eq_add_neg]
    rw [h]; exact hmul _ _ (hadd _ _ hc (hconst _)) (hconst _)
  let f : Fin g → (Fin g → ℝ) := fun k =>
    if h : j ≠ k then
      (fun m => (ρ (Classical.choose (hsep j k h)) m - ρ (Classical.choose (hsep j k h)) k) *
        (ρ (Classical.choose (hsep j k h)) j - ρ (Classical.choose (hsep j k h)) k)⁻¹)
    else 1
  have hf : ∀ k, P (f k) := by
    intro k
    by_cases h : j ≠ k
    · simp only [f, dif_pos h]
      exact haff _ _ _ (hρ _)
    · simp only [f, dif_neg h]
      exact hconst 1
  let δ : Fin g → ℝ := ∏ k ∈ Finset.univ.erase j, f k
  have hδ : P δ := Finset.prod_induction _ P hmul (hconst 1) (fun k _ => hf k)
  have hδj : δ j = 1 := by
    simp only [δ, Finset.prod_apply]
    apply Finset.prod_eq_one
    intro k hk
    have hjk : j ≠ k := (Finset.ne_of_mem_erase hk).symm
    simp only [f, dif_pos hjk]
    exact mul_inv_cancel₀ (sub_ne_zero.mpr (Classical.choose_spec (hsep j k hjk)))
  have hδm : ∀ m, m ≠ j → δ m = 0 := by
    intro m hm
    simp only [δ, Finset.prod_apply]
    apply Finset.prod_eq_zero (i := m) (Finset.mem_erase.mpr ⟨hm, Finset.mem_univ _⟩)
    have hjm : j ≠ m := fun h => hm h.symm
    simp only [f, dif_pos hjm, sub_self, zero_mul]
  obtain ⟨q, hq⟩ := hδ
  refine ⟨q, fun v => ?_⟩
  rw [← hq]
  congr 1
  funext m
  by_cases hm : m = j
  · subst hm; simp [hδj]
  · simp [hδm m hm, Pi.single_apply, hm]

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coordinate_projection_complex : ∀ (g : ℕ) (K : Type) (ρ : K → Fin g → ℝ), (∀ j k, j ≠ k → ∃ a, ρ a j ≠ ρ a k) →
    ∀ (T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)),
    (∀ a, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v, T (fun m ↦ (ρ a m : ℂ) * v m) = M (T v)) →
    ∀ j : Fin g, ∃ q : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v, q (T v) = T (Pi.single j (v j)) := by
  atlas_forward_decl GlobalTheory.realDiag_conj_coordProj
end

section
section
namespace GlobalTheory

theorem coordsDiag_key (a b y : ℂ) (h : ‖b‖ < ‖a‖) (hy : a * y + b * starRingEnd ℂ y = 0) : y = 0 := by
  by_contra hne
  have h1 : ‖a * y‖ = ‖b * starRingEnd ℂ y‖ := by
    rw [eq_neg_of_add_eq_zero_left hy, norm_neg]
  rw [norm_mul, norm_mul, Complex.norm_conj] at h1
  have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hne
  have h2 := mul_right_cancel₀ hy'.ne' h1
  linarith

theorem coordsDiag : ∀ (g : ℕ) (T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)),
    (∀ j : Fin g, ∃ q : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v, q (T v) = T (Pi.single j (v j))) →
    ∀ (α β : Fin g → ℂ), (∀ j, ‖β j‖ < ‖α j‖) →
    (∀ j (y : ℂ), T (Pi.single j y) j = α j * y + β j * starRingEnd ℂ y) →
    ∃ D : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ),
      (∀ v, D (T v) = fun j ↦ v j + β j / α j * starRingEnd ℂ (v j)) ∧
      ∀ (c : Fin g → ℝ) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ v, T (fun m ↦ (c m : ℂ) * v m) = M (T v)) →
        ∀ w, D (M w) = fun j ↦ (c j : ℂ) * D w j := by
  intro g T hq α β hαβ hT
  choose q hq using hq
  have hα : ∀ j, α j ≠ 0 := fun j h => by
    have := hαβ j
    rw [h, norm_zero] at this
    exact (norm_nonneg _).not_gt this
  have hTinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    funext j
    have h1 := hq j v
    rw [hv, map_zero] at h1
    have h2 := congrFun h1.symm j
    rw [hT] at h2
    exact coordsDiag_key _ _ _ (hαβ j) h2
  have hTsurj : Function.Surjective T := LinearMap.injective_iff_surjective.mp hTinj
  let L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    LinearMap.pi (fun j => (α j)⁻¹ • (LinearMap.proj j ∘ₗ q j))
  have hL : ∀ v, L (T v) = fun j ↦ v j + β j / α j * starRingEnd ℂ (v j) := by
    intro v; funext j
    simp only [L, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, smul_eq_mul]
    rw [hq j v, hT]
    field_simp [hα j]
  have hLinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨v, rfl⟩ := hTsurj w
    have hv : v = 0 := by
      funext j
      have h3 := congrFun ((hL v).symm.trans hw) j
      have hz : ‖β j / α j‖ < ‖(1 : ℂ)‖ := by
        rw [norm_div, norm_one, div_lt_one (norm_pos_iff.mpr (hα j))]
        exact hαβ j
      apply coordsDiag_key 1 (β j / α j) (v j) hz
      simpa using h3
    rw [hv, map_zero]
  have hLsurj := LinearMap.injective_iff_surjective.mp hLinj
  refine ⟨LinearEquiv.ofBijective L ⟨hLinj, hLsurj⟩, hL, ?_⟩
  intro c M hM w
  obtain ⟨v, rfl⟩ := hTsurj w
  show L (M (T v)) = fun j => (c j : ℂ) * L (T v) j
  rw [← hM, hL, hL]
  funext j
  simp only [map_mul, Complex.conj_ofReal]
  ring

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_antilinear_normal_form : ∀ (g : ℕ) (T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)),
    (∀ j : Fin g, ∃ q : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v, q (T v) = T (Pi.single j (v j))) →
    ∀ (α β : Fin g → ℂ), (∀ j, ‖β j‖ < ‖α j‖) →
    (∀ j (y : ℂ), T (Pi.single j y) j = α j * y + β j * starRingEnd ℂ y) →
    ∃ D : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ),
      (∀ v, D (T v) = fun j ↦ v j + β j / α j * starRingEnd ℂ (v j)) ∧
      ∀ (c : Fin g → ℝ) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ v, T (fun m ↦ (c m : ℂ) * v m) = M (T v)) →
        ∀ w, D (M w) = fun j ↦ (c j : ℂ) * D w j := by
  atlas_forward_decl GlobalTheory.coordsDiag
end

section
section
namespace GlobalTheory

theorem diag_coords_of_holomorphic_lattice_family : ∀ (Ω : Type) [NormedAddCommGroup Ω] [NormedSpace ℂ Ω] (g : ℕ) (K : Type) (ρ : K → Fin g → ℂ),
    (∀ a j, starRingEnd ℂ (ρ a j) = ρ a j) → (∀ j k, j ≠ k → ∃ a, ρ a j ≠ ρ a k) →
    ∀ (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    (∀ a, ∀ x ∈ Λ, (fun j ↦ ρ a j * x j) ∈ Λ) →
    ∀ (V : Set Ω) (τ : Ω → Λ →+ (Fin g → ℂ)), IsOpen V → (0 : Ω) ∈ V → (∀ x, τ 0 x = x) →
    (∀ x, DifferentiableOn ℂ (fun z ↦ τ z x) V) →
    (∀ z ∈ V, ∀ a, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      ∀ x x' : Λ, (x' : Fin g → ℂ) = (fun j ↦ ρ a j * (x : Fin g → ℂ) j) → τ z x' = M (τ z x)) →
    ∃ (V' : Set Ω) (D : Ω → (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (ζ : Ω → Fin g → ℂ),
      IsOpen V' ∧ (0 : Ω) ∈ V' ∧ V' ⊆ V ∧ DifferentiableOn ℂ ζ V' ∧ ζ 0 = 0 ∧ (∀ z ∈ V', ∀ j, ‖ζ z j‖ < 1) ∧
      (∀ z ∈ V', ∀ x : Λ, D z (τ z x) = fun j ↦ (x : Fin g → ℂ) j + ζ z j * starRingEnd ℂ ((x : Fin g → ℂ) j)) ∧
      ∀ z ∈ V', ∀ a (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
        (∀ x x' : Λ, (x' : Fin g → ℂ) = (fun j ↦ ρ a j * (x : Fin g → ℂ) j) → τ z x' = M (τ z x)) →
        ∀ w, D z (M w) = fun j ↦ ρ a j * D z w j := by
  intro Ω _ _ g K ρ hreal hsep Λ hd hs hΛ V τ hV h0 hτ0 hτd hM
  obtain ⟨ρr, hρ⟩ : ∃ ρr : K → Fin g → ℝ, ∀ a j, ((ρr a j : ℝ) : ℂ) = ρ a j :=
    ⟨fun a j ↦ (ρ a j).re, fun a j ↦ Complex.conj_eq_iff_re.mp (hreal a j)⟩
  have hsepr : ∀ j k, j ≠ k → ∃ a, ρr a j ≠ ρr a k := by
    intro j k hjk
    obtain ⟨a, ha⟩ := hsep j k hjk
    exact ⟨a, fun h ↦ ha (by rw [← hρ, ← hρ, h])⟩
  obtain ⟨n, b, c, hbc, hφ⟩ := GlobalTheory.T.lattice_real_coordinate_basis g Λ hd hs
  obtain ⟨T, hTapp⟩ : ∃ T : Ω → (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ),
      ∀ z v, T z v = ∑ i, c i v • τ z (b i) :=
    ⟨fun z ↦ ∑ i, (c i).smulRight (τ z (b i)), fun z v ↦ by simp⟩
  have hTΛ : ∀ z (x : Λ), T z x = τ z x := fun z x ↦ by rw [hTapp]; exact hφ (τ z) x
  have hT0 : ∀ v, T 0 v = v := fun v ↦ by rw [hTapp]; simp only [hτ0]; exact hbc v
  have hTd : ∀ v, DifferentiableOn ℂ (fun z ↦ T z v) V := by
    intro v
    simp only [hTapp]
    have := DifferentiableOn.sum (u := Finset.univ) (A := fun i z ↦ c i v • τ z (b i))
      (fun i _ ↦ (hτd (b i)).const_smul (c i v))
    simpa [Finset.sum_fn] using this
  have hcomm : ∀ z a (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (∀ x x' : Λ, (x' : Fin g → ℂ) = (fun j ↦ ρ a j * (x : Fin g → ℂ) j) → τ z x' = M (τ z x)) →
      ∀ v, T z (fun m ↦ (ρr a m : ℂ) * v m) = M (T z v) := by
    intro z a M hMz
    let Dg : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
      { toFun := fun v m ↦ ρ a m * v m
        map_add' := by intro v w; ext m; simp [mul_add]
        map_smul' := by intro r v; ext m; simp; ring }
    have key := LinearMap.ext_on (f := (T z).comp Dg) (g := (M.restrictScalars ℝ).comp (T z)) hs (by
      intro x hx
      have hx' : (fun j ↦ ρ a j * x j) ∈ Λ := hΛ a x hx
      have e := hMz ⟨x, hx⟩ ⟨_, hx'⟩ rfl
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars]
      rw [← hTΛ, ← hTΛ] at e
      exact e)
    intro v
    have := LinearMap.congr_fun key v
    simpa [Dg, hρ] using this
  obtain ⟨α, hα⟩ : ∃ α : Ω → Fin g → ℂ, ∀ z j,
      α z j = (T z (Pi.single j 1) j - Complex.I * T z (Pi.single j Complex.I) j) / 2 := ⟨_, fun _ _ ↦ rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : Ω → Fin g → ℂ, ∀ z j,
      β z j = (T z (Pi.single j 1) j + Complex.I * T z (Pi.single j Complex.I) j) / 2 := ⟨_, fun _ _ ↦ rfl⟩
  have hTs : ∀ z j (y : ℂ), T z (Pi.single j y) j = α z j * y + β z j * starRingEnd ℂ y := by
    intro z j y
    have hy : (Pi.single j y : Fin g → ℂ) = y.re • (Pi.single j 1 : Fin g → ℂ) + y.im • (Pi.single j Complex.I : Fin g → ℂ) := by
      ext m
      rcases eq_or_ne m j with rfl | h
      · simp only [Pi.single_eq_same, Pi.add_apply, Pi.smul_apply, Complex.real_smul, mul_one]
        exact (Complex.re_add_im y).symm
      · simp [h]
    rw [hy, map_add, map_smul, map_smul, hα, hβ]
    simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul]
    have hc : starRingEnd ℂ y = (y.re : ℂ) - (y.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [hc]
    have hy2 : y = (y.re : ℂ) + (y.im : ℂ) * Complex.I := (Complex.re_add_im y).symm
    linear_combination (-(T z (Pi.single j 1) j - Complex.I * T z (Pi.single j Complex.I) j) / 2) * hy2
      + ((y.im : ℂ) * T z (Pi.single j Complex.I) j) * Complex.I_sq
  have hα0 : ∀ j, α 0 j = 1 := by
    intro j; rw [hα, hT0, hT0]; simp [Complex.I_mul_I]
  have hβ0 : ∀ j, β 0 j = 0 := by
    intro j; rw [hβ, hT0, hT0]; simp [Complex.I_mul_I]
  have hαd : ∀ j, DifferentiableOn ℂ (fun z ↦ α z j) V := by
    intro j; simp only [hα]
    have h3 : DifferentiableOn ℂ (fun z ↦ T z (Pi.single j 1) j - Complex.I * T z (Pi.single j Complex.I) j) V :=
      (differentiableOn_pi.1 (hTd _) j).sub ((differentiableOn_pi.1 (hTd _) j).const_mul Complex.I)
    simpa [div_eq_mul_inv] using h3.mul_const (2 : ℂ)⁻¹
  have hβd : ∀ j, DifferentiableOn ℂ (fun z ↦ β z j) V := by
    intro j; simp only [hβ]
    have h3 : DifferentiableOn ℂ (fun z ↦ T z (Pi.single j 1) j + Complex.I * T z (Pi.single j Complex.I) j) V :=
      (differentiableOn_pi.1 (hTd _) j).add ((differentiableOn_pi.1 (hTd _) j).const_mul Complex.I)
    simpa [div_eq_mul_inv] using h3.mul_const (2 : ℂ)⁻¹
  set V' : Set Ω := V ∩ ⋂ j, (V ∩ (fun z ↦ ‖α z j‖ - ‖β z j‖) ⁻¹' Set.Ioi 0) with hV'
  have hV'o : IsOpen V' := by
    refine hV.inter (isOpen_iInter_of_finite fun j ↦ ContinuousOn.isOpen_inter_preimage ?_ hV isOpen_Ioi)
    exact ((hαd j).continuousOn.norm).sub (hβd j).continuousOn.norm
  have hV'm : ∀ z ∈ V', z ∈ V ∧ ∀ j, ‖β z j‖ < ‖α z j‖ := by
    intro z hz
    simp only [hV', Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioi, sub_pos] at hz
    exact ⟨hz.1, fun j ↦ (hz.2 j).2⟩
  have h0' : (0 : Ω) ∈ V' := by
    simp only [hV', Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioi, sub_pos, hα0, hβ0]
    simp [h0]
  have hαne : ∀ z ∈ V', ∀ j, α z j ≠ 0 := fun z hz j ↦
    norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg _) ((hV'm z hz).2 j))
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω → Fin g → ℂ, ∀ z j, ζ z j = β z j / α z j := ⟨_, fun _ _ ↦ rfl⟩
  have hζd : DifferentiableOn ℂ ζ V' := by
    refine differentiableOn_pi.2 fun j ↦ ?_
    simp only [hζ]
    have hsub : V' ⊆ V := fun z hz ↦ (hV'm z hz).1
    simp only [div_eq_mul_inv]
    exact ((hβd j).mono hsub).mul (((hαd j).mono hsub).inv fun z hz ↦ hαne z hz j)
  have hpt : ∀ z ∈ V', ∃ Dz : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ),
      (∀ v, Dz (T z v) = fun j ↦ v j + β z j / α z j * starRingEnd ℂ (v j)) ∧
      ∀ a (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ v, T z (fun m ↦ (ρr a m : ℂ) * v m) = M (T z v)) →
        ∀ w, Dz (M w) = fun j ↦ (ρr a j : ℂ) * Dz w j := by
    intro z hz
    have hMex : ∀ a, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
        ∀ v, T z (fun m ↦ (ρr a m : ℂ) * v m) = M (T z v) := fun a ↦ by
      obtain ⟨M, hMz⟩ := hM z (hV'm z hz).1 a
      exact ⟨M, hcomm z a M hMz⟩
    obtain ⟨Dz, h1, h2⟩ := GlobalTheory.T.exists_antilinear_normal_form g (T z) (GlobalTheory.T.exists_coordinate_projection_complex g K ρr hsepr (T z) hMex) (α z) (β z) (hV'm z hz).2 (hTs z)
    exact ⟨Dz, h1, fun a M hMa w ↦ h2 (ρr a) M hMa w⟩
  classical
  let D : Ω → (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := fun z ↦
    if hz : z ∈ V' then Classical.choose (hpt z hz) else LinearEquiv.refl ℂ _
  refine ⟨V', D, ζ, hV'o, h0', fun z hz ↦ (hV'm z hz).1, hζd, ?_, ?_, ?_, ?_⟩
  · funext j; rw [hζ, hβ0]; simp
  · intro z hz j
    rw [hζ, norm_div, div_lt_one (norm_pos_iff.mpr (hαne z hz j))]
    exact (hV'm z hz).2 j
  · intro z hz x
    have := (Classical.choose_spec (hpt z hz)).1 x
    simp only [D, dif_pos hz]
    rw [← hTΛ, this]
    funext j; rw [hζ]
  · intro z hz a M hMz w
    have := (Classical.choose_spec (hpt z hz)).2 a M (hcomm z a M hMz) w
    simp only [D, dif_pos hz]
    rw [this]; simp only [hρ]

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_deformation_multiplication : ∀ (Ω : Type) [NormedAddCommGroup Ω] [NormedSpace ℂ Ω] (g : ℕ) (K : Type) (ρ : K → Fin g → ℂ),
    (∀ a j, starRingEnd ℂ (ρ a j) = ρ a j) → (∀ j k, j ≠ k → ∃ a, ρ a j ≠ ρ a k) →
    ∀ (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    (∀ a, ∀ x ∈ Λ, (fun j ↦ ρ a j * x j) ∈ Λ) →
    ∀ (V : Set Ω) (τ : Ω → Λ →+ (Fin g → ℂ)), IsOpen V → (0 : Ω) ∈ V → (∀ x, τ 0 x = x) →
    (∀ x, DifferentiableOn ℂ (fun z ↦ τ z x) V) →
    (∀ z ∈ V, ∀ a, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      ∀ x x' : Λ, (x' : Fin g → ℂ) = (fun j ↦ ρ a j * (x : Fin g → ℂ) j) → τ z x' = M (τ z x)) →
    ∃ (V' : Set Ω) (D : Ω → (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (ζ : Ω → Fin g → ℂ),
      IsOpen V' ∧ (0 : Ω) ∈ V' ∧ V' ⊆ V ∧ DifferentiableOn ℂ ζ V' ∧ ζ 0 = 0 ∧ (∀ z ∈ V', ∀ j, ‖ζ z j‖ < 1) ∧
      (∀ z ∈ V', ∀ x : Λ, D z (τ z x) = fun j ↦ (x : Fin g → ℂ) j + ζ z j * starRingEnd ℂ ((x : Fin g → ℂ) j)) ∧
      ∀ z ∈ V', ∀ a (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
        (∀ x x' : Λ, (x' : Fin g → ℂ) = (fun j ↦ ρ a j * (x : Fin g → ℂ) j) → τ z x' = M (τ z x)) →
        ∀ w, D z (M w) = fun j ↦ ρ a j * D z w j := by
  atlas_forward_decl GlobalTheory.diag_coords_of_holomorphic_lattice_family
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifDet

theorem detOmega_eq_const_mul_det :
    ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ)) (L : LB X.A.left)
    (u : HolUnif X.A L (Module.finrank ℚ F)) (δ : X.DetOmega), ∃ C : ℂ,
    ∀ (v : Fin (Module.finrank ℚ F) → X.Lie) (W : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ),
      (∀ j, u.IsDiff (W j) (v j).hom) → δ v = C * W.det := by
  intro F _ _ 𝔠 X L u δ
  obtain ⟨-, h2⟩ := UnifTangent.tangent_bijection u X.dim

  have he : ∀ k : Fin (Module.finrank ℚ F), ∃ t : X.Lie, u.IsDiff (Pi.single k 1) t.hom := fun k => by
    obtain ⟨t, ⟨ht, hd⟩, -⟩ := h2 (Pi.single k 1)
    exact ⟨Serre.Lie.mk X.rm t ht, hd⟩
  choose e he using he
  let T : (Fin (Module.finrank ℚ F) → ℂ) →ₗ[ℂ] X.Lie := Fintype.linearCombination ℂ e
  have hT : ∀ w : Fin (Module.finrank ℚ F) → ℂ, u.IsDiff w (T w).hom := fun w => by
    have hc : IsLieComb w (fun k => (e k).hom) (T w).hom := by
      rw [Serre.Lie.isLieComb_iff]
      simp [T, Fintype.linearCombination_apply]
    have := UnifDifferential.isDiff_of_isLieComb X.A L _ _ u (fun k => Pi.single k 1) (fun k => (e k).hom) w
      (T w).hom (fun k => (e k).isTangent) he hc
    convert this using 1
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  refine ⟨δ.compLinearMap T (Pi.basisFun ℂ (Fin (Module.finrank ℚ F))), fun v W hW => ?_⟩
  have hv : v = fun j => T (W j) := funext fun j =>
    Serre.Lie.ext ((h2 (W j)).unique ⟨(v j).isTangent, hW j⟩ ⟨(T (W j)).isTangent, hT (W j)⟩)
  have key := DFunLike.congr_fun
    (AlternatingMap.eq_smul_basis_det (Pi.basisFun ℂ (Fin (Module.finrank ℚ F))) (δ.compLinearMap T)) W
  rw [hv]
  refine key.trans ?_
  rw [Pi.basisFun_det]
  rfl

end GlobalTheory.UnifDet
end
end

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_omega_eq_const_mul_det : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ)) (L : LB X.A.left)
    (u : HolUnif X.A L (Module.finrank ℚ F)) (δ : X.DetOmega), ∃ C : ℂ,
    ∀ (v : Fin (Module.finrank ℚ F) → X.Lie) (W : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ),
      (∀ j, u.IsDiff (W j) (v j).hom) → δ v = C * W.det := by
  atlas_forward_decl GlobalTheory.UnifDet.detOmega_eq_const_mul_det
end

section
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_separates_embeddings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) (φ : I → E →+* ℂ), IsCMType φ →
    ∀ i k, i ≠ k → ∃ a : 𝓞 (FR E), φ i ((a : FR E) : E) ≠ φ k ((a : FR E) : E) := by
  first | exact @GlobalTheory.CMSep.exists_int_ne | exact GlobalTheory.CMSep.exists_int_ne | (intros; apply GlobalTheory.CMSep.exists_int_ne <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.PeriodFamily
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD defCoord polydisc)
open GlobalTheory.LatJet GlobalTheory.LatJet.An
open scoped Classical Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet.An

namespace CoordProof

theorem diag_coords : ∀ (Ω : Type) [NormedAddCommGroup Ω] [NormedSpace ℂ Ω] (g : ℕ) (K : Type) (ρ : K → Fin g → ℂ),
    (∀ a j, starRingEnd ℂ (ρ a j) = ρ a j) → (∀ j k, j ≠ k → ∃ a, ρ a j ≠ ρ a k) →
    ∀ (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    (∀ a, ∀ x ∈ Λ, (fun j ↦ ρ a j * x j) ∈ Λ) →
    ∀ (V : Set Ω) (τ : Ω → Λ →+ (Fin g → ℂ)), IsOpen V → (0 : Ω) ∈ V → (∀ x, τ 0 x = x) →
    (∀ x, DifferentiableOn ℂ (fun z ↦ τ z x) V) →
    (∀ z ∈ V, ∀ a, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      ∀ x x' : Λ, (x' : Fin g → ℂ) = (fun j ↦ ρ a j * (x : Fin g → ℂ) j) → τ z x' = M (τ z x)) →
    ∃ (V' : Set Ω) (D : Ω → (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (ζ : Ω → Fin g → ℂ),
      IsOpen V' ∧ (0 : Ω) ∈ V' ∧ V' ⊆ V ∧ DifferentiableOn ℂ ζ V' ∧ ζ 0 = 0 ∧ (∀ z ∈ V', ∀ j, ‖ζ z j‖ < 1) ∧
      (∀ z ∈ V', ∀ x : Λ, D z (τ z x) = fun j ↦ (x : Fin g → ℂ) j + ζ z j * starRingEnd ℂ ((x : Fin g → ℂ) j)) ∧
      ∀ z ∈ V', ∀ a (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
        (∀ x x' : Λ, (x' : Fin g → ℂ) = (fun j ↦ ρ a j * (x : Fin g → ℂ) j) → τ z x' = M (τ z x)) →
        ∀ w, D z (M w) = fun j ↦ ρ a j * D z w j := GlobalTheory.T.lattice_deformation_multiplication

theorem exists_isDet : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ)) (L : LB X.A.left)
    (u : HolUnif X.A L (Module.finrank ℚ F)) (δ : X.DetOmega), ∃ C : ℂ,
    ∀ (v : Fin (Module.finrank ℚ F) → X.Lie) (W : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ),
      (∀ j, u.IsDiff (W j) (v j).hom) → δ v = C * W.det := GlobalTheory.T.det_omega_eq_const_mul_det

theorem cmType_sep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) (φ : I → E →+* ℂ), IsCMType φ →
    ∀ i k, i ≠ k → ∃ a : 𝓞 (FR E), φ i ((a : FR E) : E) ≠ φ k ((a : FR E) : E) := GlobalTheory.T.cm_type_separates_embeddings

theorem pull_ext {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) {T : Over S'} {x y : T ⟶ G'} (e : x.left ≫ φ = y.left ≫ φ) : x = y := by
  apply Over.OverMorphism.ext
  exact h.1.hom_ext e (by rw [Over.w x, Over.w y])

theorem jetRing_π_algebraMap {I : Type} [Fintype I] {n : ℕ} (J : JetRing ℂ I n) (a : ℂ) : J.π (algebraMap ℂ J.B a) = a := by
  rw [J.π_eq, Algebra.algebraMap_eq_smul_one, ← J.one, map_smul]
  simp

theorem π_jet (hJ : JetCalc) {I : Type} [Fintype I] {n : ℕ} (J : JetRing ℂ I n) (f : (I → ℂ) → ℂ) : J.π (jet J f) = f 0 := by
  obtain ⟨-, -, -, -, -, ht, -⟩ := hJ I n J
  simp only [jet, taylor, map_sum]
  rw [Finset.sum_eq_single 0]
  · simp [Algebra.smul_def, jetRing_π_algebraMap]
  · intro k _ hk
    refine Finset.sum_eq_zero fun s _ ↦ ?_
    rw [Algebra.smul_def, map_mul, map_prod]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [Fin.prod_univ_succ, ht, zero_mul, mul_zero]
  · simp

end CoordProof

open CoordProof in

theorem coordEx (hGM : GlobalTheory.Published.GaussManinPeriods) (hJ : JetCalc) (hD : DiagFrame) : CoordEx := by
  obtain ⟨ε, GM⟩ := hGM
  refine ⟨ε, ?_⟩
  intro E _ _ _ I _ 𝔠 φ c y hφ hc n T J Y G
  haveI := G.smooth
  have hX : ∀ z, ∃ (X' : Obj (FR E) 𝔠 (Sp ℂ)) (q : X'.A.left ⟶ G.X.A.left),
      X'.IsPullBy G.X (spMap (G.y z : G.B →+* ℂ)) q := fun z ↦ Obj.exists_isPullBy G.X _
  choose X q hq using hX
  have hδ : ∀ z, ∃ δ : (X z).DetGen, Obj.DetCorr (G.y z : G.B →+* ℂ) (q z) G.δ.1 δ.1 :=
    fun z ↦ ((hq z).existsUnique_detGen _ G.δ).exists
  choose δ hδ using hδ
  let mor : ∀ z, GrpMor (dp0 G.B) (𝟙 _) G.X.A (dp0 ℂ) (𝟙 _) (X z).A (G.y z : G.B →+* ℂ)
      (spMap (G.y z : G.B →+* ℂ)) (q z) := fun z ↦
    GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) (hq z).grp
  have hπj : J.π.comp (G.j : G.B →+* J.B) = (G.y 0 : G.B →+* ℂ) := by
    ext b
    simp only [RingHom.comp_apply, RingHom.coe_coe, G.jet_eq, π_jet hJ]
  have h₀ : T.X.IsPullBy G.X (spMap (G.y 0 : G.B →+* ℂ)) (Y.i ≫ G.q) := by
    rw [← hπj, Cris.spMap_comp]
    exact Y.pull.comp G.pull
  obtain ⟨V, u, τ, P, P₀, hV, h0V, hVU, hper0, hper, -, hτ0, hτhol, hend, hPhol, hcrys⟩ :=
    GM G.B G.X.A _ G.X.ab G.X.dim I G.U G.y G.isOpen G.zero G.hol (fun z ↦ (X z).A) q (fun z ↦ (hq z).grp) mor
      (fun z ↦ (X z).diag T.U.c) (fun z ↦ LB.isLB_pull ((X z).isLB _) _) T.X.A (Y.i ≫ G.q) h₀.grp
      (T.X.diag T.U.c) (LB.isLB_pull (T.X.isLB _) _) T.U.u

  let ρ : 𝓞 (FR E) → Fin (Module.finrank ℚ (FR E)) → ℂ := fun a j ↦ φ (T.U.e j) ((a : FR E) : E)
  have hreal : ∀ a j, starRingEnd ℂ (ρ a j) = ρ a j := fun a j ↦ (a : FR E).2 (φ (T.U.e j))
  have hsep : ∀ j k, j ≠ k → ∃ a, ρ a j ≠ ρ a k := fun j k hjk ↦
    cmType_sep E I φ hφ _ _ (T.U.e.injective.ne hjk)
  let dg : 𝓞 (FR E) → (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) := fun a ↦
    { toFun := fun w j ↦ ρ a j * w j
      map_add' := fun w w' ↦ funext fun j ↦ mul_add _ _ _
      map_smul' := fun s w ↦ funext fun j ↦ by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hdg : ∀ a w, dg a w = fun j ↦ ρ a j * w j := fun _ _ ↦ rfl
  have hact0 : ∀ a w, T.U.u.ex (dg a w) = T.U.u.ex w ≫ T.X.rm.act a := fun a w ↦ T.U.act a w
  have hΛ : ∀ a, ∀ x ∈ T.U.u.Λ, (fun j ↦ ρ a j * x j) ∈ T.U.u.Λ := fun a x hx ↦ by
    haveI := T.X.rm.hom a
    rw [← T.U.u.ker, ← hdg, hact0, (T.U.u.ker x).2 hx]
    exact H1.ClosedPointWeilPower.one_comp_hom _ inferInstance
  have hM0 : ∀ a w, (T.U.u.ex (dg a w)).left ≫ (Y.i ≫ G.q) =
      (T.U.u.ex w).left ≫ (Y.i ≫ G.q) ≫ (G.X.rm.act a).left := fun a w ↦ by
    rw [hact0, Over.comp_left, Category.assoc, h₀.act a]
  have hend' : ∀ z ∈ V, ∀ a, ∃ M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ),
      (∀ w, ((u z).ex (M w)).left ≫ q z = ((u z).ex w).left ≫ q z ≫ (G.X.rm.act a).left) ∧
      ∀ x x' : T.U.u.Λ, (x' : Fin (Module.finrank ℚ (FR E)) → ℂ) = dg a x → (τ z x' : Fin (Module.finrank ℚ (FR E)) → ℂ) = M (τ z x) := fun z hz a ↦ by
    haveI := G.X.rm.hom a
    exact hend (G.X.rm.act a) (dg a) (hM0 a) z hz
  let τ' : (I → ℂ) → T.U.u.Λ →+ (Fin (Module.finrank ℚ (FR E)) → ℂ) := fun z ↦ ((u z).Λ.subtype.toAddMonoidHom).comp (τ z).toAddMonoidHom
  have hτ' : ∀ z x, τ' z x = (τ z x : Fin (Module.finrank ℚ (FR E)) → ℂ) := fun _ _ ↦ rfl
  obtain ⟨V', D, ζ, hV', h0V', hV'V, hζ, hζ0, hζ1, hDτ, hDM⟩ := diag_coords (I → ℂ) _ (𝓞 (FR E)) ρ hreal hsep T.U.u.Λ
    T.U.u.discrete T.U.u.full hΛ V τ' hV h0V (fun x ↦ hτ0 x) (fun x ↦ hτhol x)
    (fun z hz a ↦ (hend' z hz a).imp fun M hM ↦ fun x x' hx ↦ hM.2 x x' hx)

  let ζ' : (I → ℂ) → I → ℂ := fun z i ↦ ζ z (T.U.e.symm i)
  have hdiff_ex : ∀ {A : Over (Sp ℂ)} [GrpObj A] {L₁ L₂ : LB A.left} {g : ℕ} (u₁ : HolUnif A L₁ g) (u₂ : HolUnif A L₂ g),
      u₁.ex = u₂.ex → ∀ w v, u₂.IsDiff w v → u₁.IsDiff w v := by
    intro A _ L₁ L₂ g u₁ u₂ h w v hv
    simpa only [HolUnif.IsDiff, h] using hv
  have hU : ∀ z ∈ V', ∃ U : Unif φ (lattice c y) (ζ' z) (X z), U.e = T.U.e ∧ U.c = T.U.c ∧
      ∀ w v, (u z).IsDiff ((D z).symm w) v → U.u.IsDiff w v := by
    intro z hz
    have hzV := hV'V hz

    have hrm : ∀ a, ∃ M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ),
        (∀ w, (u z).ex (M w) = (u z).ex w ≫ (X z).rm.act a) ∧ ∀ w, D z (M w) = fun j ↦ ρ a j * D z w j := by
      intro a
      obtain ⟨M, hM1, hM2⟩ := hend' z hzV a
      refine ⟨M, fun w ↦ pull_ext (hq z).grp ?_, hDM z hz a M (fun x x' hx ↦ hM2 x x' hx)⟩
      rw [hM1, Over.comp_left, Category.assoc, (hq z).act a]
    obtain ⟨u1, hu1ex, hu1Λ, -, -, hu1d⟩ := GlobalTheory.exists_holUnif_reparam (X z).A _ _ (u z) (D z).symm (fun _ ↦ 1)
      (differentiable_const 1) (fun _ ↦ one_ne_zero) rfl
    have hact1 : ∀ (a : 𝓞 (FR E)) w, u1.ex (fun j ↦ φ (T.U.e j) ((a : FR E) : E) * w j) = u1.ex w ≫ (X z).rm.act a := by
      intro a w
      obtain ⟨M, hM1, hM2⟩ := hrm a
      have : (D z).symm (fun j ↦ φ (T.U.e j) ((a : FR E) : E) * w j) = M ((D z).symm w) := by
        apply (D z).injective
        rw [LinearEquiv.apply_symm_apply, hM2, LinearEquiv.apply_symm_apply]
      rw [hu1ex, hu1ex, this, hM1]
    obtain ⟨u2, hh, hex, χ, hAH⟩ := hD (FR E) 𝔠 (X z) T.U.c T.U.pos u1
      (fun j ↦ (φ (T.U.e j)).comp (algebraMap (FR E) E))
      (fun j k hjk ↦ by
        by_contra hne
        obtain ⟨a, ha⟩ := cmType_sep E I φ hφ _ _ (T.U.e.injective.ne hne)
        exact ha (RingHom.congr_fun hjk (a : FR E)))
      hact1
    refine ⟨⟨T.U.e, T.U.c, T.U.pos, u2, fun w ↦ ?_, fun a w ↦ ?_, fun i ↦ hh (T.U.e.symm i), ?_⟩, rfl, rfl, ?_⟩
    · have hmem : w ∈ u2.Λ ↔ (D z).symm w ∈ (u z).Λ := by
        rw [← u2.ker w, hex, u1.ker w, hu1Λ w]
      rw [hmem]
      constructor
      · intro hw
        obtain ⟨x₀, hx₀⟩ : ∃ x₀ : T.U.u.Λ, (τ z x₀ : Fin (Module.finrank ℚ (FR E)) → ℂ) = (D z).symm w :=
          ⟨(τ z).symm ⟨_, hw⟩, by simp⟩
        obtain ⟨x, hxL, hx⟩ := (T.U.lat x₀).1 x₀.2
        refine ⟨x, hxL, ?_⟩
        have h1 := hDτ z hz x₀
        rw [hτ', hx₀, LinearEquiv.apply_symm_apply] at h1
        rw [h1]; funext j; simp [hx, defCoord, ζ']
      · rintro ⟨x, hxL, rfl⟩
        have hx₀ : (fun j ↦ defCoord φ 0 x (T.U.e j)) ∈ T.U.u.Λ := (T.U.lat _).2 ⟨x, hxL, rfl⟩
        have h1 := hDτ z hz ⟨_, hx₀⟩
        rw [hτ'] at h1
        have h2 : (fun j ↦ defCoord φ (ζ' z) x (T.U.e j)) = D z (τ z ⟨_, hx₀⟩) := by
          rw [h1]; funext j; simp [defCoord, ζ']
        rw [h2, LinearEquiv.symm_apply_apply]; exact (τ z _).2
    · rw [hex]; exact hact1 a w
    · simp only [Equiv.symm_apply_apply]; exact ⟨χ, hAH⟩
    · intro w v hv
      exact hdiff_ex u2 u1 hex w v (hu1d w v hv)

  choose U hUe hUc hUd using hU
  have hC : ∀ z (hz : z ∈ V'), ∃ C, (U z hz).IsDet (δ z).1 C := fun z hz ↦ exists_isDet (X z) _ (U z hz).u (δ z).1
  obtain ⟨-, -, -, -, -, hJt, hJprod⟩ := hJ I n J
  refine ⟨{
    V := V'
    isOpen := hV'
    zero := h0V'
    sub := hV'V.trans hVU
    X := X
    q := q
    pull := hq
    mor := mor
    δ := δ
    corr := hδ
    ζ := ζ'
    ζ_hol := differentiableOn_pi.2 fun i ↦ differentiableOn_pi.1 hζ _
    ζ_zero := by funext i; simp [ζ', hζ0]
    ζ_mem := fun z hz i ↦ hζ1 z hz _
    U := U
    e_eq := hUe
    C := fun z ↦ if hz : z ∈ V' then Classical.choose (hC z hz) else 0
    det := fun z hz ↦ by simp only [dif_pos hz]; exact Classical.choose_spec (hC z hz)
    P₀ := P₀
    per := hper0
    P := fun z ↦ (P z).comp (τ z).toAddMonoidHom
    lie := fun z hz x ↦ by
      obtain ⟨v, hv1, hv2⟩ := (hper z (hV'V hz)).2.2.1 (τ z x)
      refine ⟨v, hv1, hUd z hz _ v ?_⟩
      have h1 : (fun a ↦ x.1 a + ζ' z (T.U.e a) * starRingEnd ℂ (x.1 a)) = D z (τ z x) := by
        rw [← hτ', hDτ z hz x]; funext a; simp [ζ']
      rw [h1, LinearEquiv.symm_apply_apply]; exact hv2
    P_hol := fun x c ↦ (hPhol x c).mono hV'V
    horiz := fun m' x d hd c ↦ hcrys J.B J.π J.κ J.nil (jetRing_π_algebraMap J) (n + 1) J.t hJt hJprod G.j G.jet_eq
      Y.X'.A G.q G.pull.grp m' Y.i Y.pull.grp rfl Y.mor x d hd c }⟩

end GlobalTheory.LatJet.An
end
end

open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinate_existence_of_periods : GlobalTheory.Published.GaussManinPeriods → JetCalc → DiagFrame → CoordEx := by
  atlas_forward_decl GlobalTheory.LatJet.An.coordEx
end
