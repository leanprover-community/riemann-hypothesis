import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ExistsPerpHermitianReduction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCombinations
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticCoefficientForms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.GramSchmidtEigenframe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PositiveSpanMatrices
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FinrankEqTwoMulHalfDegree

section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Matrix
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

private theorem jForm_swap_eq_conj (p : ℕ) {n : ℕ} (x y : Fin n → ℂ) :
    ReciprocityTheory.MultiplicativeHeights.jForm p y x = conj (ReciprocityTheory.MultiplicativeHeights.jForm p x y) := by
  unfold ReciprocityTheory.MultiplicativeHeights.jForm ReciprocityTheory.MultiplicativeHeights.sgn
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp [mul_comm]

private theorem linearIndependent_mulVec_embVec {K : Type} [Field K] [NumberField K] {n : ℕ} (σ : K →+* ℂ)
    (A : Matrix (Fin n) (Fin n) K) (Q : Matrix (Fin n) (Fin n) ℂ) (hA : LinearIndependent K A)
    (hQ : Q.det ≠ 0) : LinearIndependent ℂ (fun j => Q *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec σ (A j)) := by
  have hdet : Matrix.det A ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hA)).ne_zero
  have hMe : (Matrix.of fun j k => (Q *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec σ (A j)) k) =
      σ.mapMatrix A * Q.transpose := by
    ext j k
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.mulVec, dotProduct, ReciprocityTheory.MultiplicativeHeights.embVec]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hU : IsUnit (Matrix.of fun j k => (Q *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec σ (A j)) k) := by
    rw [hMe, Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, Matrix.det_transpose,
      ← RingHom.map_det]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero ((map_ne_zero σ).mpr hdet) hQ)
  exact Matrix.linearIndependent_rows_iff_isUnit.mpr hU

theorem reducedLattice_short_bound (hD5 : CoveringRadiusStatement) (r : ℕ) (X : DataX E r) (ξ : Fin r → E) (z0 : Frame X.Ψ r)
    (f : X.Ψ → Fin (r - 2) → Fin r → ℂ) (β : Fin (r - 2) → Fin r → E) (S : ReciprocityTheory.MultiplicativeHeights.HermForm E (r - 2))
    (LB : Submodule (𝓞 E) (Fin (r - 2) → E)) (Q : X.Ψ → Matrix (Fin (r - 2)) (Fin (r - 2)) ℂ) (ep rh : ℝ)
    (hξ : X.IsIso ξ) (hz : z0 ∈ X.dom) (hf : X.UBasis z0 ξ f)
    (hβ : ∀ k, herm X.Gm (β k) ξ = 0)
    (hβind : LinearIndependent E (Fin.cons ξ β : Fin (r - 2 + 1) → Fin r → E))
    (hβspan : ∀ x : Fin r → E, herm X.Gm x ξ = 0 → ∃ (c : Fin (r - 2) → E) (e : E), x = ∑ k, c k • β k + e • ξ)
    (hS : ∀ c c' : Fin (r - 2) → E, S.h c c' = herm X.Gm (∑ k, c' k • β k) (∑ k, c k • β k))
    (hLB : ∀ c : Fin (r - 2) → E, c ∈ LB ↔ ∃ e : E, ∑ k, c k • β k + e • ξ ∈ X.L')
    (hLat : ReciprocityTheory.MultiplicativeHeights.IsLattice LB) (hSD : ReciprocityTheory.MultiplicativeHeights.IsSelfDual S LB)
    (hQ : ∀ τ, (Q τ).det ≠ 0)
    (hSQ : ∀ τ (c c' : Fin (r - 2) → E), τ.1 (S.h c c') =
      ReciprocityTheory.MultiplicativeHeights.jForm (X.p0 - 1) (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c) (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c'))
    (hQf : ∀ τ (c : Fin (r - 2) → E), X.ucomp z0 ξ (X.embV (∑ k, c k • β k)) τ =
      ∑ k, (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c) k • f τ k)
    (hep : 0 < ep) (hep1 : ep ≤ 1) (hrh : 0 < rh) (hrh1 : rh ≤ 1)
    (hD4 : ∀ x ∈ X.L', herm X.Gm x ξ = 0 → (∀ e : E, x ≠ e • ξ) →
      ∃ τ : X.Ψ, ep ≤ X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)) :
    ∃ lam : Fin (r - 2) → Fin r → E,
      (∀ j, lam j ∈ X.L' ∧ herm X.Gm (lam j) ξ = 0) ∧
      LinearIndependent E (Fin.cons ξ lam : Fin (r - 2 + 1) → Fin r → E) ∧
      (∀ j k : Fin (r - 2), (j : ℕ) < X.p0 - 1 → X.p0 - 1 ≤ (k : ℕ) → herm X.Gm (lam j) (lam k) = 0) ∧
      (∀ j : Fin (r - 2), (j : ℕ) < X.p0 - 1 → ∀ τ : X.Ψ, 0 < (τ.1 (herm X.Gm (lam j) (lam j))).re) ∧
      (∀ j : Fin (r - 2), X.p0 - 1 ≤ (j : ℕ) → ∀ τ : X.Ψ, (τ.1 (herm X.Gm (lam j) (lam j))).re < 0) ∧
      (∀ j (τ : X.Ψ), ‖τ.1 (herm X.Gm (lam j) (lam j))‖ ≤ d6La r X.p0 (fdeg E) (dE E) ep rh ^ 2) ∧
      (∀ τ, LinearIndependent ℂ fun j => X.ucomp z0 ξ (X.embV (lam j)) τ) ∧
      (∀ τ j, X.ucomp z0 ξ (X.embV (lam j)) τ ∈ Submodule.span ℂ (Set.range (f τ))) ∧
      (∀ τ (j k : Fin (r - 2)), (j : ℕ) < X.p0 - 1 → X.p0 - 1 ≤ (k : ℕ) →
        hermC τ.1 X.Gm (X.ucomp z0 ξ (X.embV (lam j)) τ) (X.ucomp z0 ξ (X.embV (lam k)) τ) = 0) ∧
      (∀ τ (w : Fin (r - 2) → ℂ), (∀ j : Fin (r - 2), X.p0 - 1 ≤ (j : ℕ) → w j = 0) → w ≠ 0 →
        0 < (hermC τ.1 X.Gm (∑ j, w j • X.ucomp z0 ξ (X.embV (lam j)) τ)
          (∑ j, w j • X.ucomp z0 ξ (X.embV (lam j)) τ)).re) ∧
      (∀ τ (w : Fin (r - 2) → ℂ), (∀ j : Fin (r - 2), (j : ℕ) < X.p0 - 1 → w j = 0) → w ≠ 0 →
        (hermC τ.1 X.Gm (∑ j, w j • X.ucomp z0 ξ (X.embV (lam j)) τ)
          (∑ j, w j • X.ucomp z0 ξ (X.embV (lam j)) τ)).re < 0) ∧
      (∀ τ (c : Fin (r - 2) → ℂ), (∑ k, c k • f τ k) ∈ Submodule.span ℂ
          ((fun j => X.ucomp z0 ξ (X.embV (lam j)) τ) '' {j | (j : ℕ) < X.p0 - 1}) →
        (∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then 0 else ‖c k‖ ^ 2) ≤
          (rh / 120) ^ 2 * ∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then ‖c k‖ ^ 2 else 0) := by
  classical
  obtain ⟨hξΛ, hξξ, hξ0⟩ := hξ
  have hcardpos : 0 < Fintype.card X.Ψ := by
    apply QuadraticCoefficientForms.card_Psi_pos <;> assumption
  have hcard : Fintype.card X.Ψ = fdeg E := by
    apply QuadraticCoefficientForms.card_Psi <;> assumption
  haveI : Nonempty X.Ψ := Fintype.card_pos_iff.mp hcardpos
  obtain ⟨τ0⟩ := (inferInstance : Nonempty X.Ψ)
  have hpb : 1 ≤ X.p0 ∧ X.p0 < r := by
    apply IsotropicIndexSums.isotropicIndex_bounds (hξ := hξξ) (hne := hξ0) (τ := τ0) <;> assumption
  obtain ⟨hp1, hpr0⟩ := hpb
  have hON : ∀ τ : X.Ψ, ∀ k l, hermC τ.1 X.Gm (f τ k) (f τ l) =
      if k = l then (if (k : ℕ) < X.p0 - 1 then 1 else -1) else 0 := fun τ => (hf τ).2.2.1
  have hSsym : ∀ x y : Fin (r - 2) → E, S.h x y = 0 → S.h y x = 0 := by
    intro x y hxy
    apply (map_eq_zero τ0.1).mp
    rw [hSQ, jForm_swap_eq_conj, ← hSQ, hxy]
    simp
  rcases Nat.eq_zero_or_pos (r - 2) with hn | hn
  · haveI : IsEmpty (Fin (r - 2)) := by rw [hn]; infer_instance
    refine ⟨fun j => ∑ k, (0 : E) • β k + (0 : E) • ξ, fun j => isEmptyElim j, ?_,
      fun j => isEmptyElim j, fun j => isEmptyElim j, fun j => isEmptyElim j,
      fun j => isEmptyElim j, fun _ => linearIndependent_empty_type, fun _ j => isEmptyElim j,
      fun _ j => isEmptyElim j, fun _ w _ hw => absurd (Subsingleton.elim w 0) hw,
      fun _ w _ hw => absurd (Subsingleton.elim w 0) hw, fun _ c _ => by simp⟩
    apply IsotropicCombinations.cons_li (hli := hβind) (hla := linearIndependent_empty_type) <;> assumption
  have hlamξ : ∀ (c : Fin (r - 2) → E) (e : E), herm X.Gm (∑ k, c k • β k + e • ξ) ξ = 0 := by
    intro c e
    apply IsotropicCombinations.herm_lam_ξ <;> assumption
  have hpr : X.p0 - 1 ≤ r - 2 := by omega
  have h_inj : Function.Injective (fun τ : X.Ψ => τ.1) := Subtype.val_injective
  have h_cm : ∀ τ : E →+* ℂ, (∃ i : X.Ψ, (fun τ : X.Ψ => τ.1) i = τ) ↔
      ¬ ∃ i : X.Ψ, (fun τ : X.Ψ => τ.1) i = ComplexEmbedding.conjugate τ := by
    intro τ
    have h := X.cmType τ
    constructor
    · rintro ⟨i, hi⟩ ⟨j, hj⟩
      have hτ : τ ∈ X.Ψ := by rw [← hi]; exact i.2
      have hc : ComplexEmbedding.conjugate τ ∈ X.Ψ := by rw [← hj]; exact j.2
      exact (h.mp hτ) hc
    · intro hn'
      exact ⟨⟨τ, h.mpr fun hc => hn' ⟨⟨_, hc⟩, rfl⟩⟩, rfl⟩
  have h_short : ∀ v ∈ LB, v ≠ 0 → ∃ i : X.Ψ, Real.sqrt ep ^ 2 ≤
      ReciprocityTheory.MultiplicativeHeights.normSq (Q i *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec i.1 v) := by
    intro v hv hv0
    obtain ⟨e, he⟩ := (hLB v).mp hv
    have hne : ∀ e' : E, ∑ k, v k • β k + e • ξ ≠ e' • ξ := by
      intro e'
      apply IsotropicCombinations.ne_smul_ξ (hli := hβind) (hc := hv0) <;> assumption
    obtain ⟨τ, hτ⟩ := hD4 _ he (hlamξ v e) hne
    refine ⟨τ, ?_⟩
    rw [IsotropicIndexSums.ucomp_drop (hx := hz) (hne := hξ0), hQf, (hf τ).2.2.2.1] at hτ
    rw [Real.sq_sqrt hep.le]
    exact hτ
  have hD := hD5 E X.Ψ (r - 2) (X.p0 - 1) S (fun τ : X.Ψ => τ.1) Q LB (Real.sqrt ep) h_inj h_cm
    hpr (Real.sqrt_pos.mpr hep) hQ hSQ hLat hSD h_short
  obtain ⟨hcov, v, hvL, hvli, hvmaj⟩ := hD
  rw [hcard] at hcov hvmaj
  have hf1 : (1 : ℝ) ≤ (fdeg E : ℝ) := by
    rw [← hcard]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr hcardpos.ne'
  have hnR : (1 : ℝ) ≤ ((r - 2 : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn.ne'
  have hd1 : (1 : ℝ) ≤ dE E := by
    unfold dE
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero (K := E))
  have hs : 0 < Real.sqrt ep := Real.sqrt_pos.mpr hep
  have hs1 : Real.sqrt ep ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hep1
  have hX : 1 ≤ ((fdeg E : ℝ) * ((r - 2 : ℕ) : ℝ)) ^ 3 :=
    one_le_pow₀ (one_le_mul_of_one_le_of_one_le hf1 hnR)
  have hXd : 1 ≤ ((fdeg E : ℝ) * ((r - 2 : ℕ) : ℝ)) ^ 3 * dE E := by
    have h := mul_le_mul hX hd1 zero_le_one (by linarith)
    linarith
  have hμpos : 0 < (d5mu (fdeg E) (r - 2) (dE E) (Real.sqrt ep)) := by
    unfold d5mu
    apply div_pos _ hs
    linarith
  have hμ4 : 4 ≤ (d5mu (fdeg E) (r - 2) (dE E) (Real.sqrt ep)) := by
    unfold d5mu
    rw [le_div_iff₀ hs]
    linarith
  have hA : 1 ≤ Real.sqrt ((r - 2 : ℕ) : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hnR
  have e1 : 2 * ReciprocityTheory.MultiplicativeHeights.approxR (r - 2) ((d5mu (fdeg E) (r - 2) (dE E) (Real.sqrt ep))) (rh / 40) =
      320 * (Real.sqrt ((r - 2 : ℕ) : ℝ) * (d5mu (fdeg E) (r - 2) (dE E) (Real.sqrt ep))) / rh := by
    unfold ReciprocityTheory.MultiplicativeHeights.approxR
    rw [div_div_eq_mul_div]
    ring
  have hT320 : 320 * (d5mu (fdeg E) (r - 2) (dE E) (Real.sqrt ep)) ≤ 2 * ReciprocityTheory.MultiplicativeHeights.approxR (r - 2) ((d5mu (fdeg E) (r - 2) (dE E) (Real.sqrt ep))) (rh / 40) := by
    rw [e1, le_div_iff₀ hrh]
    nlinarith [mul_le_mul_of_nonneg_left hrh1 hμpos.le, mul_le_mul_of_nonneg_right hA hμpos.le]
  have hT1 : 1 ≤ 2 * ReciprocityTheory.MultiplicativeHeights.approxR (r - 2) ((d5mu (fdeg E) (r - 2) (dE E) (Real.sqrt ep))) (rh / 40) := by linarith
  have hTμ : 2 * (d5mu (fdeg E) (r - 2) (dE E) (Real.sqrt ep)) ^ 2 ≤ (2 * ReciprocityTheory.MultiplicativeHeights.approxR (r - 2) ((d5mu (fdeg E) (r - 2) (dE E) (Real.sqrt ep))) (rh / 40)) ^ 2 := by
    nlinarith [mul_le_mul hT320 hT320 (by linarith) (by linarith), sq_nonneg (d5mu (fdeg E) (r - 2) (dE E) (Real.sqrt ep))]
  obtain ⟨la, hlaL, hlali, hlaorth, hlapos, hlaneg, hlab1, hlab2⟩ :=
    ReciprocityTheory.MultiplicativeHeights.Closed.approx E X.Ψ (r - 2) (X.p0 - 1) S (fun τ : X.Ψ => τ.1) Q LB v
      ((d5mu (fdeg E) (r - 2) (dE E) (Real.sqrt ep))) (rh / 40) hpr hμpos (div_pos hrh (by norm_num)) (by linarith) hQ hSQ hSD.1
      hcov hvL hvli hvmaj
  choose ec hec using fun j => (hLB (la j)).mp (hlaL j)
  have hu : ∀ (τ : X.Ψ) (j : Fin (r - 2)), X.ucomp z0 ξ (X.embV (∑ i, la j i • β i + ec j • ξ)) τ =
      ∑ k, (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 (la j)) k • f τ k := by
    intro τ j
    rw [IsotropicIndexSums.ucomp_drop (hx := hz) (hne := hξ0), hQf]
  have hcomb : ∀ (τ : X.Ψ) (w : Fin (r - 2) → ℂ),
      ∑ j, w j • X.ucomp z0 ξ (X.embV (∑ i, la j i • β i + ec j • ξ)) τ =
        ∑ k, (Q τ *ᵥ ∑ j, w j • ReciprocityTheory.MultiplicativeHeights.embVec τ.1 (la j)) k • f τ k := by
    intro τ w
    simp_rw [hu τ]
    rw [IsotropicCombinations.comb_swap]
    simp_rw [IsotropicCombinations.qcomb]
  have hone : ∀ (τ : X.Ψ) (j : Fin (r - 2)),
      Q τ *ᵥ ∑ i, (Pi.single j (1 : ℂ) : Fin (r - 2) → ℂ) i • ReciprocityTheory.MultiplicativeHeights.embVec τ.1 (la i) =
        Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 (la j) := by
    intro τ j
    congr 1
    simp [Pi.single_apply]
  have hsn : ∀ j : Fin (r - 2), (Pi.single j (1 : ℂ) : Fin (r - 2) → ℂ) ≠ 0 :=
    fun j h => by simpa using congrFun h j
  have hll : ∀ j1 j2 : Fin (r - 2), herm X.Gm (∑ i, la j1 i • β i + ec j1 • ξ) (∑ i, la j2 i • β i + ec j2 • ξ) = S.h (la j2) (la j1) := by
    intro j1 j2
    rw [hS (la j2) (la j1)]
    apply IsotropicCombinations.herm_lam_lam <;> first | assumption | exact X.Gm_herm
  have hM : ∀ τ : X.Ψ, LinearIndependent ℂ (fun j => Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 (la j)) :=
    fun τ => linearIndependent_mulVec_embVec τ.1 la (Q τ) hlali (hQ τ)
  have F2 : LinearIndependent E (Fin.cons ξ (fun j => (∑ i, la j i • β i + ec j • ξ)) : Fin (r - 2 + 1) → Fin r → E) := by
    apply IsotropicCombinations.cons_li (hli := hβind) (hla := hlali) <;> assumption
  have F3 : ∀ j k : Fin (r - 2), (j : ℕ) < X.p0 - 1 → X.p0 - 1 ≤ (k : ℕ) →
      herm X.Gm (∑ i, la j i • β i + ec j • ξ) (∑ i, la k i • β i + ec k • ξ) = 0 := by
    intro j k hj hk
    rw [hll, hSsym _ _ (hlaorth j k hj hk)]
  have F4 : ∀ j : Fin (r - 2), (j : ℕ) < X.p0 - 1 → ∀ τ : X.Ψ,
      0 < (τ.1 (herm X.Gm (∑ i, la j i • β i + ec j • ξ) (∑ i, la j i • β i + ec j • ξ))).re := by
    intro j hj τ
    rw [hll, hSQ, ← hone τ j]
    exact (hlapos τ (Pi.single j (1 : ℂ))
      (fun i hi => by rw [Pi.single_apply, if_neg]; rintro rfl; omega)).2 (hsn j)
  have F5 : ∀ j : Fin (r - 2), X.p0 - 1 ≤ (j : ℕ) → ∀ τ : X.Ψ,
      (τ.1 (herm X.Gm (∑ i, la j i • β i + ec j • ξ) (∑ i, la j i • β i + ec j • ξ))).re < 0 := by
    intro j hj τ
    rw [hll, hSQ, ← hone τ j]
    exact hlaneg τ (Pi.single j (1 : ℂ))
      (fun i hi => by rw [Pi.single_apply, if_neg]; rintro rfl; omega) (hsn j)
  have F6 : ∀ (j : Fin (r - 2)) (τ : X.Ψ),
      ‖τ.1 (herm X.Gm (∑ i, la j i • β i + ec j • ξ) (∑ i, la j i • β i + ec j • ξ))‖ ≤ d6La r X.p0 (fdeg E) (dE E) ep rh ^ 2 := by
    intro j τ
    rw [hll]
    apply IsotropicCombinations.la_bound (hT := hT1) (hμ := hTμ) (hp0 := hp1)
    by_cases hj : (j : ℕ) < X.p0 - 1
    · exact Or.inl (hlab1 τ j hj)
    · exact Or.inr (hlab2 τ j (not_lt.mp hj))
  have F7 : ∀ τ : X.Ψ, LinearIndependent ℂ fun j => X.ucomp z0 ξ (X.embV (∑ i, la j i • β i + ec j • ξ)) τ := by
    intro τ
    rw [Fintype.linearIndependent_iff]
    intro w hw
    rw [hcomb τ w] at hw
    have h0 : Q τ *ᵥ ∑ j, w j • ReciprocityTheory.MultiplicativeHeights.embVec τ.1 (la j) = 0 :=
      IsotropicIndexSums.coeff_unique (f := f τ) (hf := hON τ)
        (h := hw.trans (by simp : (0 : Fin r → ℂ) = ∑ k, (0 : Fin (r - 2) → ℂ) k • f τ k))
    have h1 : ∑ j, w j • (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 (la j)) = 0 := by
      funext k
      have h2 := congrFun h0 k
      rw [IsotropicCombinations.qcomb] at h2
      simpa [Finset.sum_apply] using h2
    exact Fintype.linearIndependent_iff.mp (hM τ) w h1
  have F8 : ∀ (τ : X.Ψ) (j : Fin (r - 2)),
      X.ucomp z0 ξ (X.embV (∑ i, la j i • β i + ec j • ξ)) τ ∈ Submodule.span ℂ (Set.range (f τ)) := by
    intro τ j
    rw [hu τ j]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have F9 : ∀ (τ : X.Ψ) (j k : Fin (r - 2)), (j : ℕ) < X.p0 - 1 → X.p0 - 1 ≤ (k : ℕ) →
      hermC τ.1 X.Gm (X.ucomp z0 ξ (X.embV (∑ i, la j i • β i + ec j • ξ)) τ) (X.ucomp z0 ξ (X.embV (∑ i, la k i • β i + ec k • ξ)) τ) = 0 := by
    intro τ j k hj hk
    rw [hu τ j, hu τ k, IsotropicCombinations.hC_comb2_ortho (hf := hON τ), ← hSQ,
      hSsym _ _ (hlaorth j k hj hk), map_zero]
  have WorkedExample : ∀ (τ : X.Ψ) (w : Fin (r - 2) → ℂ), (∀ j : Fin (r - 2), X.p0 - 1 ≤ (j : ℕ) → w j = 0) →
      w ≠ 0 → 0 < (hermC τ.1 X.Gm (∑ j, w j • X.ucomp z0 ξ (X.embV (∑ i, la j i • β i + ec j • ξ)) τ)
        (∑ j, w j • X.ucomp z0 ξ (X.embV (∑ i, la j i • β i + ec j • ξ)) τ)).re := by
    intro τ w hw hw0
    rw [hcomb τ w, IsotropicIndexSums.hC_comb_ortho (hf := hON τ)]
    exact (hlapos τ w hw).2 hw0
  have LargeParameterEstimates : ∀ (τ : X.Ψ) (w : Fin (r - 2) → ℂ), (∀ j : Fin (r - 2), (j : ℕ) < X.p0 - 1 → w j = 0) →
      w ≠ 0 → (hermC τ.1 X.Gm (∑ j, w j • X.ucomp z0 ξ (X.embV (∑ i, la j i • β i + ec j • ξ)) τ)
        (∑ j, w j • X.ucomp z0 ξ (X.embV (∑ i, la j i • β i + ec j • ξ)) τ)).re < 0 := by
    intro τ w hw hw0
    rw [hcomb τ w, IsotropicIndexSums.hC_comb_ortho (hf := hON τ)]
    exact hlaneg τ w hw hw0
  have F12 : ∀ (τ : X.Ψ) (c : Fin (r - 2) → ℂ), (∑ k, c k • f τ k) ∈ Submodule.span ℂ
      ((fun j => X.ucomp z0 ξ (X.embV (∑ i, la j i • β i + ec j • ξ)) τ) '' {j | (j : ℕ) < X.p0 - 1}) →
      (∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then 0 else ‖c k‖ ^ 2) ≤
        (rh / 120) ^ 2 * ∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then ‖c k‖ ^ 2 else 0 := by
    intro τ c hc
    rw [Finsupp.mem_span_image_iff_linearCombination] at hc
    obtain ⟨l, hl, hlc⟩ := hc
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype l
      (fun i a => a • X.ucomp z0 ξ (X.embV (∑ k, la i k • β k + ec i • ξ)) τ) (fun _ => zero_smul ℂ _)] at hlc
    rw [hcomb τ l] at hlc
    have hcq := IsotropicIndexSums.coeff_unique (f := f τ) (hf := hON τ) (h := hlc)
    have hws : ∀ j : Fin (r - 2), X.p0 - 1 ≤ (j : ℕ) → l j = 0 := by
      intro j hj
      rw [Finsupp.mem_supported'] at hl
      exact hl j (by simp only [Set.mem_setOf_eq, not_lt]; exact hj)
    have h3 := (hlapos τ l hws).1
    simp only [hcq] at h3
    rw [show rh / 40 / 3 = rh / 120 by ring] at h3
    exact h3
  exact ⟨fun j => (∑ i, la j i • β i + ec j • ξ), fun j => ⟨hec j, hlamξ _ _⟩, F2, F3, F4, F5, F6, F7, F8, F9, WorkedExample, LargeParameterEstimates, F12⟩

end

end ReciprocityTheory.ChartRestriction.G.FD
end

section
namespace ReciprocityTheory.ChartRestriction.G.FD.BlockIdentityExpansion

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

private lemma hermC_sum_left_lemma (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {m : ℕ} (c : Fin m → ℂ)
    (q : Fin m → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ k, c k • q k) v = ∑ k, c k * hermC τ G (q k) v := by
  unfold hermC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ a, ∑ k, ∑ b, c k * q k a * τ (G a b) * conj (v b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ b, c k * q k a * τ (G a b) * conj (v b) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring

private lemma hermC_sum_right_lemma_2 (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {m : ℕ} (u : Fin r → ℂ)
    (d : Fin m → ℂ) (q : Fin m → Fin r → ℂ) :
    hermC τ G u (∑ l, d l • q l) = ∑ l, conj (d l) * hermC τ G u (q l) := by
  unfold hermC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
  calc _ = ∑ a, ∑ l, ∑ b, u a * τ (G a b) * (conj (d l) * conj (q l b)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ l, ∑ a, ∑ b, u a * τ (G a b) * (conj (d l) * conj (q l b)) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring

lemma f_gram_re (X : Data E r) (ξ : Fin r → E) (z0 : Frame X.Ψ r) (f : X.Ψ → Fin (r - 2) → Fin r → ℂ)
    (hf : X.UBasis z0 ξ f) (τ : X.Ψ) (a : Fin (r - 2) → ℂ) :
    (hermC τ.1 X.Gm (∑ k, a k • f τ k) (∑ k, a k • f τ k)).re =
      ∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then ‖a k‖ ^ 2 else -‖a k‖ ^ 2 := by
  obtain ⟨-, -, hgr, -, -⟩ := hf τ
  rw [hermC_sum_left_lemma]
  simp only [hermC_sum_right_lemma_2, hgr, mul_ite, mul_zero, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp [Complex.mul_conj, Complex.normSq_eq_norm_sq] <;>
    rw [← Complex.ofReal_pow, Complex.ofReal_re]

private lemma hermC_add_left_fundamental_domains (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u u' v : Fin r → ℂ) :
    hermC τ G (u + u') v = hermC τ G u v + hermC τ G u' v := by
  unfold hermC
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma hermC_sub_left' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u u' v : Fin r → ℂ) :
    hermC τ G (u - u') v = hermC τ G u v - hermC τ G u' v := by
  unfold hermC
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private lemma hermC_sub_right' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v v' : Fin r → ℂ) :
    hermC τ G u (v - v') = hermC τ G u v - hermC τ G u v' := by
  unfold hermC
  simp only [Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

private lemma hermC_smul_left_fundamental_domains (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : ℂ) (u v : Fin r → ℂ) :
    hermC τ G (c • u) v = c * hermC τ G u v := by
  unfold hermC
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private lemma hermC_smul_right_fundamental_domains (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : ℂ) (u v : Fin r → ℂ) :
    hermC τ G u (c • v) = conj c * hermC τ G u v := by
  unfold hermC
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

private lemma hermC_zero_left' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (v : Fin r → ℂ) :
    hermC τ G 0 v = 0 := by
  unfold hermC
  simp

private lemma hermC_zero_right' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u : Fin r → ℂ) :
    hermC τ G u 0 = 0 := by
  unfold hermC
  simp

private lemma ppos_smul_fundamental_domains (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (u : Fin r → ℂ) :
    X.ppos x τ (c • u) = c • X.ppos x τ u := by
  rw [Data.ppos_eq, Data.ppos_eq, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hermC_smul_left_fundamental_domains]
  ring

private lemma hermC_add_right_fundamental_domains (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v v' : Fin r → ℂ) :
    hermC τ G u (v + v') = hermC τ G u v + hermC τ G u v' := by
  unfold hermC
  simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem key (X : DataX E r) (ξ : Fin r → E) (z0 x0 : Frame X.Ψ r)
    (f : X.Ψ → Fin (r - 2) → Fin r → ℂ) (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (δ : ℝ)
    (hz : z0 ∈ X.dom) (hx0 : x0 ∈ X.dom) (hortho : X.IsOrtho x0)
    (hflag : X.SameFlag z0 x0) (hf : X.UBasis z0 ξ f)
    (hI : ∀ s t : X.Ψ → ℂ, X.applyV h1 (X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) =
      X.lineV ξ s + X.Jz z0 (X.lineV ξ t))
    (hUz : ∀ u ∈ X.Uz z0 ξ, X.applyV h1 u ∈ X.Uz z0 ξ)
    (hgraph : ∀ τ (v : Fin r → ℂ), v ∈ Submodule.span ℂ (f τ '' {k | (k : ℕ) < X.p0 - 1}) →
      ∀ c : Fin (r - 2) → ℂ, (h1 τ) *ᵥ v = ∑ k, c k • f τ k →
        (∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then 0 else ‖c k‖ ^ 2) ≤
          δ ^ 2 * ∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then ‖c k‖ ^ 2 else 0)
    (τ : X.Ψ) (v : Fin r → ℂ) (hv : v ∈ Spos X.toData z0 τ) :
    Neg X.toData x0 τ (h1 τ *ᵥ v) ≤ δ ^ 2 * Pos X.toData x0 τ (h1 τ *ᵥ v) := by
  classical
  obtain ⟨hperp, hJ, hgr, -, hspan⟩ := hf τ
  have hdet0 : (mat x0 τ).det ≠ 0 := (hx0 τ).1
  have hS : Spos X.toData z0 τ = Spos X.toData x0 τ := hflag τ
  have hJt : ∀ u, X.Jt z0 τ u = I • ((2 : ℂ) • X.ppos z0 τ u - u) := fun u => rfl

  have hPpos : ∀ k : Fin (r - 2), (k : ℕ) < X.p0 - 1 → X.ppos z0 τ (f τ k) = f τ k := by
    intro k hk
    have h := hJ k
    rw [if_pos hk, hJt] at h
    have h2 := smul_right_injective (Fin r → ℂ) Complex.I_ne_zero h
    have h3 : (2 : ℂ) • X.ppos z0 τ (f τ k) = (2 : ℂ) • f τ k := by
      rw [sub_eq_iff_eq_add.mp h2, two_smul]
    exact smul_right_injective (Fin r → ℂ) two_ne_zero h3
  have hPneg : ∀ k : Fin (r - 2), ¬ (k : ℕ) < X.p0 - 1 → X.ppos z0 τ (f τ k) = 0 := by
    intro k hk
    have h := hJ k
    rw [if_neg hk, hJt, neg_smul, ← smul_neg] at h
    have h2 := smul_right_injective (Fin r → ℂ) Complex.I_ne_zero h
    have h3 : (2 : ℂ) • X.ppos z0 τ (f τ k) = 0 := by
      have h4 := congrArg (· + f τ k) h2
      simpa using h4
    exact (smul_eq_zero.mp h3).resolve_left two_ne_zero
  have hfS : ∀ k : Fin (r - 2), (k : ℕ) < X.p0 - 1 → f τ k ∈ Spos X.toData z0 τ := by
    intro k hk
    rw [← hPpos k hk]
    exact ppos_mem (X := X.toData) z0 τ _
  have hvP : X.ppos z0 τ v = v := ppos_of_mem (X := X.toData) hz τ v hv
  have hvneg : ∀ k : Fin (r - 2), ¬ (k : ℕ) < X.p0 - 1 → hermC τ.1 X.Gm v (f τ k) = 0 := by
    intro k hk
    rw [← hvP, Data.ppos_selfadj (X := X.toData) hz τ v (f τ k), hPneg k hk, hermC_zero_right']

  obtain ⟨a, ha⟩ : ∃ a : Fin (r - 2) → ℂ,
      a = fun k : Fin (r - 2) => if (k : ℕ) < X.p0 - 1 then hermC τ.1 X.Gm v (f τ k) else 0 := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Fin r → ℂ, w = ∑ k, a k • f τ k := ⟨_, rfl⟩
  have hwspan : w ∈ Submodule.span ℂ (f τ '' {k | (k : ℕ) < X.p0 - 1}) := by
    rw [hw]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : (k : ℕ) < X.p0 - 1
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
    · simp [ha, hk]
  have hwS : w ∈ Spos X.toData z0 τ := by
    rw [hw]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : (k : ℕ) < X.p0 - 1
    · exact Submodule.smul_mem _ _ (hfS k hk)
    · simp [ha, hk]
  have hfw : ∀ k, hermC τ.1 X.Gm (f τ k) w =
      conj (a k) * (if (k : ℕ) < X.p0 - 1 then 1 else -1) := by
    intro k
    rw [hw, hermC_sum_right_lemma_2]
    simp only [hgr, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hfp : ∀ k, hermC τ.1 X.Gm (f τ k) (v - w) = 0 := by
    intro k
    rw [hermC_sub_right', hfw]
    by_cases hk : (k : ℕ) < X.p0 - 1
    · rw [if_pos hk, mul_one, ha]
      simp only [if_pos hk]
      rw [hermC_conj τ.1 X.Gm_herm, sub_self]
    · rw [if_neg hk, ha]
      simp only [if_neg hk, map_zero, zero_mul, sub_zero]
      rw [← hermC_conj τ.1 X.Gm_herm, hvneg k hk, map_zero]
  have hskew : ∀ u q, hermC τ.1 X.Gm (X.Jt z0 τ u) q = -hermC τ.1 X.Gm u (X.Jt z0 τ q) := by
    intro u q
    rw [hJt, hJt, hermC_smul_left_fundamental_domains, hermC_smul_right_fundamental_domains, hermC_sub_left', hermC_sub_right',
      hermC_smul_left_fundamental_domains, hermC_smul_right_fundamental_domains, Data.ppos_selfadj (X := X.toData) hz τ u q, Complex.conj_I]
    first
      | (simp only [map_ofNat]; ring)
      | (simp; ring)

  let Lq : (Fin r → ℂ) → (Fin r → ℂ) →ₗ[ℂ] ℂ := fun q =>
    { toFun := fun u => hermC τ.1 X.Gm u q
      map_add' := fun u u' => hermC_add_left_fundamental_domains _ _ u u' q
      map_smul' := fun c u => hermC_smul_left_fundamental_domains _ _ c u q }
  have hK : ⨅ i, LinearMap.ker (![Lq (Data.emb τ.1 ξ), Lq (X.Jt z0 τ (Data.emb τ.1 ξ))] i) ≤
      LinearMap.ker (Lq (v - w)) := by
    intro u hu
    rw [Submodule.mem_iInf] at hu
    have h0 : hermC τ.1 X.Gm u (Data.emb τ.1 ξ) = 0 := hu 0
    have h1' : hermC τ.1 X.Gm u (X.Jt z0 τ (Data.emb τ.1 ξ)) = 0 := hu 1
    have hJu : hermC τ.1 X.Gm (X.Jt z0 τ u) (Data.emb τ.1 ξ) = 0 := by rw [hskew, h1', neg_zero]
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hspan u h0 hJu)
    show hermC τ.1 X.Gm u (v - w) = 0
    rw [← hc, hermC_sum_left_lemma]
    exact Finset.sum_eq_zero fun k _ => by rw [hfp k, mul_zero]
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (mem_span_of_iInf_ker_le_ker hK)
  have hc' : ∀ u, hermC τ.1 X.Gm u (v - w) =
      hermC τ.1 X.Gm u (conj (c 0) • Data.emb τ.1 ξ + conj (c 1) • X.Jt z0 τ (Data.emb τ.1 ξ)) := by
    intro u
    have h := LinearMap.congr_fun hc u
    simp only [Fin.sum_univ_two, LinearMap.add_apply, LinearMap.smul_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, smul_eq_mul] at h
    rw [hermC_add_right_fundamental_domains, hermC_smul_right_fundamental_domains, hermC_smul_right_fundamental_domains, Complex.conj_conj,
      Complex.conj_conj]
    exact h.symm
  have hnd : ∀ z : Fin r → ℂ, (∀ u, hermC τ.1 X.Gm u z = 0) → z = 0 := by
    intro z hz'
    rw [expand (X := X.toData) hortho τ hdet0 z]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [← hermC_conj τ.1 X.Gm_herm, hz', map_zero, mul_zero, zero_smul]
  have hpq : v - w = conj (c 0) • Data.emb τ.1 ξ + conj (c 1) • X.Jt z0 τ (Data.emb τ.1 ξ) := by
    refine sub_eq_zero.mp (hnd _ fun u => ?_)
    rw [hermC_sub_right', hc' u, sub_self]
  have hfix : h1 τ *ᵥ (v - w) = v - w := by
    have h := congrFun (hI (fun _ => conj (c 0)) (fun _ => conj (c 1))) τ
    simp only [Data.applyV, Data.lineV, Data.Jz, Pi.add_apply] at h
    have he : conj (c 0) • Data.emb τ.1 ξ + conj (c 1) • X.Jt z0 τ (Data.emb τ.1 ξ) =
        conj (c 0) • Data.emb τ.1 ξ + I • ((2 : ℂ) • X.ppos z0 τ (conj (c 1) • Data.emb τ.1 ξ) -
          conj (c 1) • Data.emb τ.1 ξ) := by
      rw [hJt, ppos_smul_fundamental_domains]
      first
        | module
        | (simp only [smul_sub, smul_smul]; ring_nf)
    rw [hpq, he]
    first
      | exact h
      | simpa using h

  have hwe : hermC τ.1 X.Gm w (Data.emb τ.1 ξ) = 0 := by
    rw [hw, hermC_sum_left_lemma]
    exact Finset.sum_eq_zero fun k _ => by rw [(hperp k).1, mul_zero]
  have hwP : X.ppos z0 τ w = w := ppos_of_mem (X := X.toData) hz τ w hwS
  have hp0 : ∀ τ' : X.Ψ, X.ppos z0 τ' 0 = 0 := fun τ' => by
    simpa using ppos_smul_fundamental_domains X.toData z0 τ' 0 0
  have hU : (fun τ' => if τ' = τ then w else 0) ∈ X.Uz z0 ξ := by
    refine ⟨fun τ' => ?_, fun τ' => ?_⟩
    · by_cases h : τ' = τ
      · simp only [if_pos h]
        rw [h]
        exact hwe
      · simp only [if_neg h]
        exact hermC_zero_left' _ _ _
    · by_cases h : τ' = τ
      · simp only [Data.Jz, if_pos h]
        rw [h, hwP, hermC_smul_left_fundamental_domains, hermC_sub_left', hermC_smul_left_fundamental_domains, hwe]
        ring
      · simp only [Data.Jz, if_neg h, hp0, smul_zero, sub_zero]
        exact hermC_zero_left' _ _ _
  have hA := hUz _ hU
  have hA1 : hermC τ.1 X.Gm (h1 τ *ᵥ w) (Data.emb τ.1 ξ) = 0 := by
    have h := hA.1 τ
    simpa [Data.applyV] using h
  have hA2 : hermC τ.1 X.Gm (X.Jt z0 τ (h1 τ *ᵥ w)) (Data.emb τ.1 ξ) = 0 := by
    have h := hA.2 τ
    simpa [Data.applyV, Data.Jz, Data.Jt] using h
  obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hspan _ hA1 hA2)
  have hg := hgraph τ w hwspan cc hcc.symm
  have hy : h1 τ *ᵥ v = (v - w) + ∑ k, cc k • f τ k := by
    rw [hcc]
    conv_rhs => rw [← hfix]
    rw [← Matrix.mulVec_add, sub_add_cancel]
  rw [hy]

  have hpS0 : v - w ∈ Spos X.toData x0 τ := hS ▸ Submodule.sub_mem _ hv hwS
  obtain ⟨b, hb⟩ : ∃ b : Fin (r - 2) → ℂ,
      b = fun k : Fin (r - 2) => if (k : ℕ) < X.p0 - 1 then 0 else cc k := ⟨_, rfl⟩
  have hNeq : PositiveSpanMatrices.Neg X.toData x0 τ ((v - w) + ∑ k, cc k • f τ k) =
      PositiveSpanMatrices.Neg X.toData x0 τ (∑ k, b k • f τ k) := by
    unfold PositiveSpanMatrices.Neg
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [hermC_add_left_fundamental_domains, perp_kap (X := X.toData) hortho τ _ hpS0 a', zero_add,
      hermC_sum_left_lemma, hermC_sum_left_lemma]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hb]
    by_cases hk : (k : ℕ) < X.p0 - 1
    · simp only [if_pos hk, zero_mul]
      rw [perp_kap (X := X.toData) hortho τ _ (hS ▸ hfS k hk) a', mul_zero]
    · simp only [if_neg hk]
  have hnegperp : ∀ b' : Fin X.p0,
      hermC τ.1 X.Gm (∑ k, b k • f τ k) (col (mat x0 τ) (Fin.castLE X.p0_le b')) = 0 := by
    intro b'
    rw [hermC_sum_left_lemma]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hb]
    by_cases hk : (k : ℕ) < X.p0 - 1
    · simp only [if_pos hk, zero_mul]
    · simp only [if_neg hk]
      rw [perp_of_ppos_zero (X := X.toData) hx0 τ (f τ k) ?_ b', mul_zero]
      rw [← FrameDegreeData.ppos_sameFlag (X := X.toData) hz hx0 hflag τ]
      exact hPneg k hk
  have hN : PositiveSpanMatrices.Neg X.toData x0 τ ((v - w) + ∑ k, cc k • f τ k) =
      ∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then 0 else ‖cc k‖ ^ 2 := by
    rw [hNeq]
    have h1' := re_self_of_perp (X := X.toData) hortho τ hdet0 _ hnegperp
    have h2' := f_gram_re X.toData ξ z0 f hf τ b
    have h3' : PositiveSpanMatrices.Neg X.toData x0 τ (∑ k, b k • f τ k) =
        -∑ k : Fin (r - 2), (if (k : ℕ) < X.p0 - 1 then ‖b k‖ ^ 2 else -‖b k‖ ^ 2) := by
      linarith
    rw [h3', ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hb]
    by_cases hk : (k : ℕ) < X.p0 - 1 <;> simp [hk]

  have hre := re_self_split (X := X.toData) hortho τ hdet0 ((v - w) + ∑ k, cc k • f τ k)
  have hpf : ∀ k, hermC τ.1 X.Gm (v - w) (f τ k) = 0 := fun k => by
    rw [← hermC_conj τ.1 X.Gm_herm, hfp k, map_zero]
  have hexp : (hermC τ.1 X.Gm ((v - w) + ∑ k, cc k • f τ k) ((v - w) + ∑ k, cc k • f τ k)).re =
      (hermC τ.1 X.Gm (v - w) (v - w)).re +
        (hermC τ.1 X.Gm (∑ k, cc k • f τ k) (∑ k, cc k • f τ k)).re := by
    rw [hermC_add_left_fundamental_domains, hermC_add_right_fundamental_domains, hermC_add_right_fundamental_domains,
      hermC_sum_right_lemma_2 τ.1 X.Gm (v - w), hermC_sum_left_lemma τ.1 X.Gm cc (f τ) (v - w)]
    simp only [hpf, hfp, mul_zero, Finset.sum_const_zero, add_zero, zero_add, Complex.add_re]
  have hSS := f_gram_re X.toData ξ z0 f hf τ cc
  have hPp := re_self_of_mem (X := X.toData) hortho τ hdet0 _ hpS0
  have hP0 := Pos_nonneg (X := X.toData) x0 τ (v - w)
  have hsplit : (∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then ‖cc k‖ ^ 2 else -‖cc k‖ ^ 2) =
      (∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then ‖cc k‖ ^ 2 else 0) -
        ∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then 0 else ‖cc k‖ ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  rw [hN] at hre ⊢
  have hmono : ∀ A B C : ℝ, C ≤ δ ^ 2 * A → A ≤ B → C ≤ δ ^ 2 * B := fun A B C h1 h2 =>
    h1.trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg δ))
  refine hmono _ _ _ hg ?_
  linarith [hre, hexp, hSS, hPp, hP0, hsplit]

end

end ReciprocityTheory.ChartRestriction.G.FD.BlockIdentityExpansion
end

section
namespace ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def Amat (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (z0 x0 : Frame X.Ψ r) (τ : X.Ψ) :
    Matrix (Fin X.p0) (Fin X.p0) ℂ :=
  Matrix.of fun b' b => hermC τ.1 X.Gm (col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b))
    (col (mat x0 τ) (Fin.castLE X.p0_le b'))

def Bmat (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (z0 x0 : Frame X.Ψ r) (τ : X.Ψ) :
    Matrix (Fin (r - X.p0)) (Fin X.p0) ℂ :=
  Matrix.of fun a b => -hermC τ.1 X.Gm (col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b))
    (col (mat x0 τ) (kap X.p0_le a))

lemma col_mul' (A B : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) : col (A * B) a = A *ᵥ col B a := by
  funext k
  simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

lemma mulVec_eq_sum_col (M : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) : M *ᵥ w = ∑ c, w c • col M c := by
  funext k
  simp only [Matrix.mulVec, dotProduct, col, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun c _ ↦ mul_comm _ _

lemma yvec_eq (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (z0 : Frame X.Ψ r) (τ : X.Ψ) (u : Fin X.p0 → ℂ) :
    ∑ b, u b • col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b) =
      h1 τ *ᵥ ∑ b, u b • col (mat z0 τ) (Fin.castLE X.p0_le b) := by
  simp only [col_mul', Matrix.mulVec_sum, Matrix.mulVec_smul]

private lemma hermC_sum_smul_left' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {m : ℕ}
    (c : Fin m → ℂ) (y : Fin m → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ b, c b • y b) v = ∑ b, c b * hermC τ G (y b) v := by
  simp only [hermC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b' _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring

lemma Pos_eq (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (z0 x0 : Frame X.Ψ r) (τ : X.Ψ) (u : Fin X.p0 → ℂ) :
    Pos X x0 τ (∑ b, u b • col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b)) =
      ∑ b', ‖(Amat X h1 z0 x0 τ *ᵥ u) b'‖ ^ 2 := by
  unfold Pos
  refine Finset.sum_congr rfl fun b' _ ↦ ?_
  have h : (Amat X h1 z0 x0 τ *ᵥ u) b' = ∑ b, u b * hermC τ.1 X.Gm
      (col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b)) (col (mat x0 τ) (Fin.castLE X.p0_le b')) := by
    simp only [Matrix.mulVec, dotProduct, Amat, Matrix.of_apply]
    exact Finset.sum_congr rfl fun b _ ↦ mul_comm _ _
  rw [hermC_sum_smul_left', h]

lemma Neg_eq (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (z0 x0 : Frame X.Ψ r) (τ : X.Ψ) (u : Fin X.p0 → ℂ) :
    Neg X x0 τ (∑ b, u b • col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b)) =
      ∑ a, ‖(Bmat X h1 z0 x0 τ *ᵥ u) a‖ ^ 2 := by
  unfold PositiveSpanMatrices.Neg
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  have h : (Bmat X h1 z0 x0 τ *ᵥ u) a = -∑ b, u b * hermC τ.1 X.Gm
      (col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b)) (col (mat x0 τ) (kap X.p0_le a)) := by
    simp only [Matrix.mulVec, dotProduct, Bmat, Matrix.of_apply, neg_mul, Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun b _ ↦ mul_comm _ _
  rw [hermC_sum_smul_left', h, norm_neg]

lemma colW_expand (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (z0 : Frame X.Ψ r) {x0 : Frame X.Ψ r}
    (hortho : X.IsOrtho x0) (τ : X.Ψ) (hdet0 : (mat x0 τ).det ≠ 0) (b : Fin X.p0) :
    col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b) =
      ∑ b', Amat X h1 z0 x0 τ b' b • col (mat x0 τ) (Fin.castLE X.p0_le b') +
        ∑ a, Bmat X h1 z0 x0 τ a b • col (mat x0 τ) (kap X.p0_le a) := by
  classical
  set y := col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b) with hy
  set α := (mat x0 τ)⁻¹ *ᵥ y with hα
  have hyα : y = ∑ c, α c • col (mat x0 τ) c := by
    rw [← mulVec_eq_sum_col, hα, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet0), Matrix.one_mulVec]
  have hcd : ∀ c d, hermC τ.1 X.Gm (col (mat x0 τ) c) (col (mat x0 τ) d) =
      if c = d then ((sgn X.p0 (c : ℕ) : ℝ) : ℂ) else 0 := by
    intro c d
    have := congrFun (congrFun (hortho τ) c) d
    simpa [gram, Matrix.diagonal_apply] using this
  have hh : ∀ d, hermC τ.1 X.Gm y (col (mat x0 τ) d) = α d * ((sgn X.p0 (d : ℕ) : ℝ) : ℂ) := by
    intro d
    rw [hyα, hermC_sum_smul_left']
    simp only [hcd, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  rw [hyα, sum_split X.p0_le]
  congr 1
  · refine Finset.sum_congr rfl fun b' _ ↦ ?_
    congr 1
    simp only [Amat, Matrix.of_apply]
    rw [← hy, hh]
    have hb' := b'.isLt
    simp [sgn, hb']
  · refine Finset.sum_congr rfl fun a _ ↦ ?_
    congr 1
    simp only [Bmat, Matrix.of_apply]
    rw [← hy, hh, show sgn X.p0 (kap X.p0_le a : ℕ) = -1 by simp [sgn, kap]]
    push_cast
    ring

lemma lowBlock_castLE (Z : X.Coord) (τ : X.Ψ) (b' b : Fin X.p0) :
    X.lowBlock Z τ (Fin.castLE X.p0_le b') (Fin.castLE X.p0_le b) = if b' = b then 1 else 0 := by
  have hb' := b'.isLt
  simp only [Data.lowBlock, Matrix.of_apply, Fin.castLE_inj, Fin.coe_castLE]
  rw [dif_neg (by omega)]
  simp

lemma lowBlock_kap (Z : X.Coord) (τ : X.Ψ) (a : Fin (r - X.p0)) (b : Fin X.p0) :
    X.lowBlock Z τ (kap X.p0_le a) (Fin.castLE X.p0_le b) = Z τ a b := by
  simp only [Data.lowBlock, Matrix.of_apply, if_neg (kap_ne_castLE X.p0_le a b), zero_add]
  rw [dif_pos ⟨by simp [kap], by simp [b.isLt]⟩]
  exact congrArg₂ (Z τ) (Fin.ext (by simp [kap])) (Fin.ext (by simp))

lemma colZ (x0 : Frame X.Ψ r) (Z : X.Coord) (τ : X.Ψ) (b : Fin X.p0) :
    col (mat (X.xZ x0 Z) τ) (Fin.castLE X.p0_le b) =
      col (mat x0 τ) (Fin.castLE X.p0_le b) + ∑ a, Z τ a b • col (mat x0 τ) (kap X.p0_le a) := by
  classical
  have hm : mat (X.xZ x0 Z) τ = mat x0 τ * X.lowBlock Z τ := rfl
  have hc : ∀ c k, col (X.lowBlock Z τ) c k = X.lowBlock Z τ k c := fun _ _ ↦ rfl
  rw [hm, col_mul', mulVec_eq_sum_col, sum_split X.p0_le]
  simp only [hc, lowBlock_castLE, lowBlock_kap, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

end

end ReciprocityTheory.ChartRestriction.G.FD.LowerBlockMatrices
end

section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Matrix
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem unitary_fixing_isotropic_plane (r : ℕ) (X : DataX E r) (ξ : Fin r → E) (z0 x0 : Frame X.Ψ r)
    (f : X.Ψ → Fin (r - 2) → Fin r → ℂ) (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (δ : ℝ)
    (hξ : X.IsIso ξ) (hz : z0 ∈ X.dom) (hx0 : x0 ∈ X.dom) (hortho : X.IsOrtho x0)
    (hflag : X.SameFlag z0 x0) (hf : X.UBasis z0 ξ f) (hδ : 0 ≤ δ) (hU : X.IsUnitaryC h1)
    (hI : ∀ s t : X.Ψ → ℂ, X.applyV h1 (X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) =
      X.lineV ξ s + X.Jz z0 (X.lineV ξ t))
    (hUz : ∀ u ∈ X.Uz z0 ξ, X.applyV h1 u ∈ X.Uz z0 ξ)
    (hgraph : ∀ τ (v : Fin r → ℂ), v ∈ Submodule.span ℂ (f τ '' {k | (k : ℕ) < X.p0 - 1}) →
      ∀ c : Fin (r - 2) → ℂ, (h1 τ) *ᵥ v = ∑ k, c k • f τ k →
        (∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then 0 else ‖c k‖ ^ 2) ≤
          δ ^ 2 * ∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then ‖c k‖ ^ 2 else 0) :
    ∃ Z1 : X.Coord, X.SameFlag (X.lmulC h1 z0) (X.xZ x0 Z1) ∧ X.zN Z1 ≤ δ := by
  classical
  have hdetOf : ∀ x ∈ X.dom, ∀ τ, (mat x τ).det ≠ 0 := by
    intro x hx τ
    simp only [Data.dom, GG, Set.mem_setOf_eq] at hx
    exact (hx τ).1
  have hcolLI : ∀ x ∈ X.dom, ∀ τ,
      LinearIndependent ℂ (fun b : Fin X.p0 => col (mat x τ) (Fin.castLE X.p0_le b)) := by
    intro x hx τ
    have hu : IsUnit (mat x τ) := (Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit (hdetOf x hx τ))
    exact (Matrix.linearIndependent_cols_iff_isUnit.mpr hu).comp (Fin.castLE X.p0_le)
      (Fin.castLE_injective _)
  have hineq : ∀ τ (u : Fin X.p0 → ℂ),
      ∑ a, ‖(LowerBlockMatrices.Bmat X.toData h1 z0 x0 τ *ᵥ u) a‖ ^ 2 ≤
        δ ^ 2 * ∑ b', ‖(LowerBlockMatrices.Amat X.toData h1 z0 x0 τ *ᵥ u) b'‖ ^ 2 := by
    intro τ u
    have hv : (∑ b, u b • col (mat z0 τ) (Fin.castLE X.p0_le b)) ∈ PositiveSpanMatrices.Spos X.toData z0 τ :=
      Submodule.sum_mem _ (fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))
    have k := BlockIdentityExpansion.key X ξ z0 x0 f h1 δ hz hx0 hortho hflag hf hI hUz hgraph τ _ hv
    rw [← LowerBlockMatrices.yvec_eq (X := X.toData), LowerBlockMatrices.Neg_eq (X := X.toData),
      LowerBlockMatrices.Pos_eq (X := X.toData)] at k
    exact k
  have hAdet : ∀ τ, (LowerBlockMatrices.Amat X.toData h1 z0 x0 τ).det ≠ 0 := by
    intro τ
    rw [Ne, ← Matrix.exists_mulVec_eq_zero_iff]
    rintro ⟨u, hu0, hAu⟩
    set v : Fin r → ℂ := ∑ b, u b • col (mat z0 τ) (Fin.castLE X.p0_le b) with hvdef
    set y : Fin r → ℂ := ∑ b, u b • col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b) with hydef
    have hP : PositiveSpanMatrices.Pos X.toData x0 τ y = 0 := by
      rw [hydef, LowerBlockMatrices.Pos_eq (X := X.toData), hAu]
      simp
    have hNle : PositiveSpanMatrices.Neg X.toData x0 τ y ≤ 0 := by
      have k := hineq τ u
      rw [hAu] at k
      rw [hydef, LowerBlockMatrices.Neg_eq (X := X.toData)]
      simpa using k
    have hN : PositiveSpanMatrices.Neg X.toData x0 τ y = 0 :=
      le_antisymm hNle (PositiveSpanMatrices.Neg_nonneg (X := X.toData) x0 τ y)
    have hy0 : y = 0 :=
      PositiveSpanMatrices.eq_zero_of_Pos_Neg (X := X.toData) hortho τ (hdetOf x0 hx0 τ) y hP hN
    have hyv : y = h1 τ *ᵥ v := by
      rw [hydef, hvdef, LowerBlockMatrices.yvec_eq (X := X.toData)]
    have hvv : hermC τ.1 X.Gm v v = 0 := by
      rw [← hU τ v v, ← hyv, hy0, hermC_zero_left]
    have hvx0 : v ∈ PositiveSpanMatrices.Spos X.toData x0 τ := by
      have hv : v ∈ PositiveSpanMatrices.Spos X.toData z0 τ :=
        Submodule.sum_mem _ (fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))
      unfold PositiveSpanMatrices.Spos at hv ⊢
      rw [← hflag τ]
      exact hv
    have hv0 : v = 0 :=
      PositiveSpanMatrices.zero_of_mem_self (X := X.toData) hortho τ (hdetOf x0 hx0 τ) v hvx0 hvv
    apply hu0
    funext b
    exact Fintype.linearIndependent_iff.mp (hcolLI z0 hz τ) u hv0 b
  let Z1 : X.Coord := fun τ =>
    (LowerBlockMatrices.Bmat X.toData h1 z0 x0 τ * (LowerBlockMatrices.Amat X.toData h1 z0 x0 τ)⁻¹ :
      Matrix (Fin (r - X.p0)) (Fin X.p0) ℂ)
  refine ⟨Z1, ?_, ?_⟩
  · intro τ
    have hA := hAdet τ
    refine PositiveSpanMatrices.span_eq_of_mat _ _ (LowerBlockMatrices.Amat X.toData h1 z0 x0 τ) hA (fun b => ?_)
    have hZA : ∀ a, ∑ b', Z1 τ a b' * LowerBlockMatrices.Amat X.toData h1 z0 x0 τ b' b =
        LowerBlockMatrices.Bmat X.toData h1 z0 x0 τ a b := by
      intro a
      have h := congrFun (congrFun (Matrix.nonsing_inv_mul_cancel_right
        (LowerBlockMatrices.Amat X.toData h1 z0 x0 τ) (LowerBlockMatrices.Bmat X.toData h1 z0 x0 τ)
        ((Matrix.isUnit_iff_isUnit_det _).mp ((Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hA)))) a) b
      rw [Matrix.mul_apply] at h
      exact h
    show col (h1 τ * mat z0 τ) (Fin.castLE X.p0_le b) = _
    rw [LowerBlockMatrices.colW_expand (X := X.toData) h1 z0 hortho τ (hdetOf x0 hx0 τ) b]
    simp only [LowerBlockMatrices.colZ (X := X.toData), smul_add, Finset.sum_add_distrib, Finset.smul_sum,
      smul_smul]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_smul, ← hZA a]
    congr 1
    refine Finset.sum_congr rfl (fun b' _ => ?_)
    ring
  · refine Real.iSup_le (fun τ => ?_) hδ
    unfold Data.opN
    refine Real.sSup_le (fun t ht => ?_) hδ
    obtain ⟨v, hv, rfl⟩ := ht
    set A := LowerBlockMatrices.Amat X.toData h1 z0 x0 τ with hAdef
    set B := LowerBlockMatrices.Bmat X.toData h1 z0 x0 τ with hBdef
    have hA := hAdet τ
    set u := A⁻¹ *ᵥ v with hudef
    have hAu : A *ᵥ u = v := by
      rw [hudef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hA), Matrix.one_mulVec]
    have hZv : Matrix.of (Z1 τ) *ᵥ v = B *ᵥ u := by
      rw [hudef, Matrix.mulVec_mulVec]
      rfl
    rw [hZv]
    have k := hineq τ u
    rw [hAu] at k
    have hpos : 0 < ∑ j, ‖v j‖ ^ 2 := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
      exact Finset.sum_pos' (fun _ _ => by positivity) ⟨j, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hj) 2⟩
    rw [div_le_iff₀ (Real.sqrt_pos.mpr hpos)]
    calc Real.sqrt (∑ i, ‖(B *ᵥ u) i‖ ^ 2) ≤ Real.sqrt (δ ^ 2 * ∑ j, ‖v j‖ ^ 2) := Real.sqrt_le_sqrt k
      _ = δ * Real.sqrt (∑ j, ‖v j‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq hδ]

end

end ReciprocityTheory.ChartRestriction.G.FD
end

section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Matrix
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

theorem complexStructure_add (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.Jt x τ (u + v) = X.Jt x τ u + X.Jt x τ v := by
  have hh : ∀ w, hermC τ.1 X.Gm (u + v) w = hermC τ.1 X.Gm u w + hermC τ.1 X.Gm v w := by
    intro w
    simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hp : X.ppos x τ (u + v) = X.ppos x τ u + X.ppos x τ v := by
    simp only [ReciprocityTheory.ChartRestriction.G.FD.Data.ppos, hh, add_mul, Finset.sum_add_distrib, add_smul]
  simp only [ReciprocityTheory.ChartRestriction.G.FD.Data.Jt, hp, smul_add, smul_sub]
  abel

theorem complexStructure_smul (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (u : Fin r → ℂ) :
    X.Jt x τ (c • u) = c • X.Jt x τ u := by
  have hh : ∀ w, hermC τ.1 X.Gm (c • u) w = c * hermC τ.1 X.Gm u w := by
    intro w
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hp : X.ppos x τ (c • u) = c • X.ppos x τ u := by
    simp only [ReciprocityTheory.ChartRestriction.G.FD.Data.ppos, hh, Finset.smul_sum, smul_smul, Finset.mul_sum, mul_assoc]
  simp only [ReciprocityTheory.ChartRestriction.G.FD.Data.Jt, hp]
  module

theorem eigenspan_perp_isotropic {z0 : Frame X.Ψ r} {ξ : Fin r → E} {f : X.Ψ → Fin (r - 2) → Fin r → ℂ}
    (hf : X.UBasis z0 ξ f) (τ : X.Ψ) (s : Set (Fin (r - 2))) (σ : ℂ)
    (hs : ∀ k ∈ s, (if (k : ℕ) < X.p0 - 1 then I else -I) = σ) (v : Fin r → ℂ)
    (hv : v ∈ Submodule.span ℂ (f τ '' s)) :
    hermC τ.1 X.Gm v (emb τ.1 ξ) = 0 ∧ hermC τ.1 X.Gm (X.Jt z0 τ v) (emb τ.1 ξ) = 0 ∧
      X.Jt z0 τ v = σ • v := by
  have hadd : ∀ a b w, hermC τ.1 X.Gm (a + b) w = hermC τ.1 X.Gm a w + hermC τ.1 X.Gm b w := by
    intro a b w
    simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hsm : ∀ (c : ℂ) a w, hermC τ.1 X.Gm (c • a) w = c * hermC τ.1 X.Gm a w := by
    intro c a w
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hJ0 : X.Jt z0 τ 0 = 0 := by simpa using complexStructure_smul X z0 τ 0 0
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.UBasis at hf
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨k, hk, rfl⟩ := hw
    exact ⟨((hf τ).1 k).1, ((hf τ).1 k).2, by rw [(hf τ).2.1 k, hs k hk]⟩
  | zero => exact ⟨by simp [hermC], by rw [hJ0]; simp [hermC], by rw [hJ0, smul_zero]⟩
  | add a b _ _ ha hb =>
    exact ⟨by rw [hadd, ha.1, hb.1, add_zero], by rw [complexStructure_add, hadd, ha.2.1, hb.2.1, add_zero],
      by rw [complexStructure_add, ha.2.2, hb.2.2, smul_add]⟩
  | smul c a _ ha =>
    exact ⟨by rw [hsm, ha.1, mul_zero], by rw [complexStructure_smul, hsm, ha.2.1, mul_zero],
      by rw [complexStructure_smul, ha.2.2, smul_comm]⟩

end Data

private lemma d4ep0_pos_and_le_one (g d f NA NC c1 w : ℝ) (hg : 0 < g) (hd : 0 < d) (hf : 1 ≤ f) (hNC : 0 < NC)
    (hNA : 0 ≤ NA) (hc1 : 0 < c1) (hw : 1 ≤ w) :
    0 < flowEpsilonBound g d f NA NC c1 w ∧ flowEpsilonBound g d f NA NC c1 w ≤ 1 := by
  unfold flowEpsilonBound
  dsimp only
  refine ⟨lt_min one_pos ?_, min_le_left _ _⟩
  have hH : 0 ≤ NC ^ 2 * (2 + 4 * f ^ 4 * (d ^ (1 / (2 * f))) ^ 2 * NA ^ 2) := by positivity
  have hK : 1 ≤ 1 + g * d ^ 2 * (NC ^ 2 * (2 + 4 * f ^ 4 * (d ^ (1 / (2 * f))) ^ 2 * NA ^ 2)) *
      (2 * c1 + 1) := by
    have : 0 ≤ g * d ^ 2 * (NC ^ 2 * (2 + 4 * f ^ 4 * (d ^ (1 / (2 * f))) ^ 2 * NA ^ 2)) * (2 * c1 + 1) := by
      apply mul_nonneg (mul_nonneg (mul_pos hg (pow_pos hd 2)).le hH)
      linarith
    linarith
  have hL : 0 ≤ Real.log (2 * (1 + g * d ^ 2 * (NC ^ 2 * (2 + 4 * f ^ 4 * (d ^ (1 / (2 * f))) ^ 2 * NA ^ 2)) *
      (2 * c1 + 1)) * (4 * f)) := Real.log_nonneg (by nlinarith)
  have h4 : 0 ≤ 4 * f * Real.log (2 * (1 + g * d ^ 2 * (NC ^ 2 * (2 + 4 * f ^ 4 * (d ^ (1 / (2 * f))) ^ 2 * NA ^ 2)) *
      (2 * c1 + 1)) * (4 * f)) := mul_nonneg (by linarith) hL
  apply div_pos (pow_pos (by linarith) 2)
  apply mul_pos (mul_pos (mul_pos (pow_pos (mul_pos hg (pow_pos hd 2)) 2) (pow_pos hNC 2)) hc1)
  linarith

theorem epsilonZero_pos_le_one {r : ℕ} (X : DataX E r) (c1 w : ℝ) (hc1 : 0 < c1) (hw1 : 1 ≤ w) :
    0 < flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w ∧ flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w ≤ 1 := by
  have hd : 0 < dE E := by
    unfold dE
    exact abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero E))
  have hf : (1 : ℝ) ≤ (fdeg E : ℝ) := by
    have h1 : Module.finrank ℚ E = 2 * NumberField.InfinitePlace.nrComplexPlaces E :=
      NumberField.IsTotallyComplex.finrank E
    have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
    have h3 : 1 ≤ fdeg E := by
      unfold fdeg
      omega
    exact_mod_cast h3
  exact d4ep0_pos_and_le_one _ _ _ _ _ _ _ (Nat.cast_pos.mpr X.g_pos) hd hf (Nat.cast_pos.mpr X.NC_pos) (Nat.cast_nonneg _) hc1 hw1

theorem orthonormalShortVectorBound_of (hD4 : ShortVectorBound (E := E)) (hD5 : CoveringRadiusStatement) : OrthonormalShortVectorBound (E := E) := by
  intro r X la P ξ ν c1 w z0 hH x0 hx0 hortho hflag
  have hξ : X.IsIso ξ := hH.2.2.1
  have hc1 : 0 < c1 := hH.2.2.2.1
  have hw1 : 1 ≤ w := hH.2.2.2.2.2.2.1
  have hz : z0 ∈ X.dom := hH.2.2.2.2.2.2.2.2.2.1.1
  obtain ⟨hep, hep1⟩ := epsilonZero_pos_le_one X c1 w hc1 hw1
  have hrh : 0 < d6rh c1 w := by unfold d6rh; positivity
  have hrh1 : d6rh c1 w ≤ 1 := by
    unfold d6rh
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hD4' := hD4 r X la P ξ ν c1 w z0 hH
  obtain ⟨f, hf⟩ := exists_unitary_basis_same_flag r X ξ z0 x0 hξ hz hx0 hortho hflag
  obtain ⟨β, S, LB, Q, hβ, hβind, hβspan, hS, hLB, hLat, hSD, hQ, hSQ, hQf⟩ := exists_perp_hermitian_reduction r X ξ z0 f hξ hz hf
  obtain ⟨lam, hl1, hl2, hl3, hl4, hl5, hl6, hYind, hYU, hYorth, hYpos, hYneg, hYgraph⟩ :=
    reducedLattice_short_bound hD5 r X ξ z0 f β S LB Q _ _ hξ hz hf hβ hβind hβspan hS hLB hLat hSD hQ hSQ hQf hep hep1 hrh
      hrh1 hD4'
  obtain ⟨h1, hU, hI, hUz, hmap, hpre⟩ := gramSchmidt_eigenframe r X ξ z0 f (fun τ j => X.ucomp z0 ξ (X.embV (lam j)) τ) hξ hz hf
    hYind hYU hYorth hYpos hYneg
  obtain ⟨Z1, hfl, hZ⟩ := unitary_fixing_isotropic_plane r X ξ z0 x0 f h1 (d6rh c1 w / 120) hξ hz hx0 hortho hflag hf (by positivity) hU hI
    hUz (fun τ v hv c hc => hYgraph τ c (hc ▸ hmap τ v hv))
  obtain ⟨hdom1, haproj, -, hJ⟩ := unitaryComplementMove r X.toData ξ hξ z0 hz h1 hU hI hUz

  have hJsplit : ∀ j : Fin (r - 2),
      X.Jz (X.lmulC h1 z0) (X.ucomp (X.lmulC h1 z0) ξ (X.embV (lam j))) =
        (if (j : ℕ) < X.p0 - 1 then I else -I) • X.ucomp (X.lmulC h1 z0) ξ (X.embV (lam j)) := by
    intro j
    choose u hu hhu using hpre
    have hmem : ∀ τ, X.toData.Jt z0 τ (u τ j) = (if (j : ℕ) < X.p0 - 1 then I else -I) • u τ j ∧
        hermC τ.1 X.Gm (u τ j) (Data.emb τ.1 ξ) = 0 ∧
        hermC τ.1 X.Gm (X.toData.Jt z0 τ (u τ j)) (Data.emb τ.1 ξ) = 0 := by
      intro τ
      have := X.toData.eigenspan_perp_isotropic hf τ _ (if (j : ℕ) < X.p0 - 1 then I else -I) (fun k hk => by
        simp only [Set.mem_setOf_eq] at hk
        by_cases hj : (j : ℕ) < X.p0 - 1
        · rw [if_pos (hk.2 hj), if_pos hj]
        · rw [if_neg (fun h => hj (hk.1 h)), if_neg hj]) (u τ j) (hu τ j)
      exact ⟨this.2.2, this.1, this.2.1⟩
    have huU : (fun τ => u τ j) ∈ X.Uz z0 ξ := ⟨fun τ => (hmem τ).2.1, fun τ => (hmem τ).2.2⟩
    have hIp : X.embV (lam j) ∈ X.Iperp ξ := fun τ => by
      rw [Data.embV, ← emb_herm, (hl1 j).2, map_zero]
    have hY : X.ucomp (X.lmulC h1 z0) ξ (X.embV (lam j)) = X.applyV h1 (fun τ => u τ j) := by
      funext τ
      show (X.embV (lam j) - X.aproj (X.lmulC h1 z0) ξ (X.embV (lam j))) τ = (h1 τ) *ᵥ (u τ j)
      rw [haproj _ hIp, hhu τ j]
      rfl
    rw [hY, hJ _ huU]
    funext τ
    simp only [Data.applyV, Data.Jz, Pi.smul_apply]
    have h2 := (hmem τ).1
    simp only [Data.Jt] at h2
    rw [h2, Matrix.mulVec_smul]
  refine ⟨lam, h1, Z1, hU, hI, hUz, ⟨hl1, hl2, hl3, fun j hj => ⟨hl4 j hj, ?_⟩, fun j hj => ⟨hl5 j hj, ?_⟩, hl6⟩,
    hfl, ?_⟩
  · rw [hJsplit j, if_pos hj]
  · rw [hJsplit j, if_neg (by omega), neg_smul]
  · have : d6rh c1 w / 120 ≤ d6rh c1 w / 100 := by
      apply div_le_div_of_nonneg_left hrh.le (by norm_num) (by norm_num)
    linarith

end

end ReciprocityTheory.ChartRestriction.G.FD
end
