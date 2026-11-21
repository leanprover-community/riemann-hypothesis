import Formalism.NormUnitaryBounds.Statement
import Formalism.LatticeSlopes.CovolAntiSameRank
import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolPos
import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqCovolume
import Formalism.LatticeSlopes.LatticeSlopesProofs.ShortVector
import Formalism.LatticeSlopes.LatticeSlopesProofs.SaturationProperties
import Formalism.LatticeSlopes.LatticeSlopesProofs.DegQuot

section
open Module Submodule

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem discreteTopology_of_norm_ge (L : Submodule ℤ E) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ x ∈ L, x ≠ 0 → ε ≤ ‖x‖) : DiscreteTopology L := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have hball : ({0} : Set L) = Metric.ball (0 : L) ε := by
    ext x
    simp only [Set.mem_singleton_iff, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro rfl
      simpa using hε
    · intro hx
      by_contra hne
      have hx0 : (x : E) ≠ 0 := fun h0 => hne (Subtype.ext h0)
      have := h x x.2 hx0
      rw [Submodule.coe_norm] at hx
      linarith
  rw [hball]
  exact Metric.isOpen_ball

theorem exists_ne_zero_norm_le_rank_div_of_dualMinimum (Q : Submodule ℤ E) [hQd : DiscreteTopology Q] (hQ : Q ≠ ⊥) {l : ℝ}
    (hl : 0 < l)
    (hdual : ∀ y ∈ span ℝ (Q : Set E), y ≠ 0 →
      (∀ x ∈ Q, ∃ z : ℤ, inner ℝ x y = (z : ℝ)) → l ≤ ‖y‖) :
    ∃ q ∈ Q, q ≠ 0 ∧ ‖q‖ ≤ (Formalism.F.rk Q : ℝ) / l := by
  classical
  set k := Module.finrank ℤ Q with hk
  let b := Module.finBasis ℤ Q
  let v : Fin k → E := fun i => (b i : E)
  let G := Matrix.gram ℝ v
  have hcovQ : Formalism.F.covol Q = Real.sqrt G.det := Formalism.F.covol_eq_gram E Q (Fin k) b
  have hpos : 0 < Formalism.F.covol Q := Formalism.F.covol_pos' E Q hQd
  have hdet : 0 < G.det := Real.sqrt_pos.mp (hcovQ ▸ hpos)
  have hdetu : IsUnit G.det := hdet.ne'.isUnit
  let P := G⁻¹
  let w : Fin k → E := fun j => ∑ i, P i j • v i
  have hGP : G * P = 1 := Matrix.mul_nonsing_inv G hdetu
  have hbi : ∀ l j, inner ℝ (v l) (w j) = if l = j then 1 else 0 := by
    intro l j
    have h1 : inner ℝ (v l) (w j) = (G * P) l j := by
      simp only [w, inner_sum, real_inner_smul_right, Matrix.mul_apply, G, Matrix.gram_apply]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [h1, hGP, Matrix.one_apply]
  have hQv : ∀ x ∈ Q, ∃ a : Fin k → ℤ, x = ∑ i, (a i : ℝ) • v i := by
    intro x hx
    refine ⟨fun i => b.repr ⟨x, hx⟩ i, ?_⟩
    have h1 := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    have h2 : ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : E) = x := h1
    calc x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : E) := h2.symm
      _ = _ := by
        simp only [Int.cast_smul_eq_zsmul, v]
        try rfl
  let D := Submodule.span ℤ (Set.range w)
  have hint : ∀ y ∈ D, ∀ x ∈ Q, ∃ z : ℤ, inner ℝ x y = (z : ℝ) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      intro x hx
      obtain ⟨a, rfl⟩ := hQv x hx
      refine ⟨a j, ?_⟩
      simp only [sum_inner, real_inner_smul_left, hbi]
      simp
    | zero => exact fun x _ => ⟨0, by simp⟩
    | add y y' _ _ h1 h2 =>
      intro x hx
      obtain ⟨z1, e1⟩ := h1 x hx
      obtain ⟨z2, e2⟩ := h2 x hx
      exact ⟨z1 + z2, by rw [inner_add_right, e1, e2]; push_cast; ring⟩
    | smul c y _ h1 =>
      intro x hx
      obtain ⟨z1, e1⟩ := h1 x hx
      exact ⟨c * z1, by rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, e1]; push_cast; ring⟩
  have hDV : ∀ y ∈ D, y ∈ span ℝ (Q : Set E) := by
    intro y hy
    have hle : D ≤ (span ℝ (Q : Set E)).restrictScalars ℤ := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (b i).2))
    exact hle hy
  have hDl : ∀ y ∈ D, y ≠ 0 → l ≤ ‖y‖ := fun y hy hy0 => hdual y (hDV y hy) hy0 (hint y hy)
  have hDd : DiscreteTopology D := discreteTopology_of_norm_ge D hl hDl
  have hli : LinearIndependent ℤ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg l
    have h1 := congrArg (fun y => inner ℝ (v l) y) hg
    simp only [inner_sum, inner_zero_right] at h1
    simp only [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hbi, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
    exact_mod_cast h1
  let bw := Basis.span hli
  have hcovD : Formalism.F.covol D = Real.sqrt (Matrix.gram ℝ w).det := by
    rw [Formalism.F.covol_eq_gram E D (Fin k) bw]
    congr 3
    funext i
    exact congrArg Subtype.val (Basis.span_apply hli i)
  have hgw : Matrix.gram ℝ w = P.transpose * G * P := Formalism.F.gram_sum_smul_eq_transpose_mul v P
  have hdetw : (Matrix.gram ℝ w).det = G.det⁻¹ := by
    rw [hgw, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_nonsing_inv,
      Ring.inverse_eq_inv']
    field_simp
  have hrkD : Formalism.F.rk D = k := by
    simp only [Formalism.F.rk]
    rw [Module.finrank_eq_card_basis bw, Fintype.card_fin]
  have hrkQ : Formalism.F.rk Q = k := rfl
  have hkpos : 0 < k := by
    have : Nontrivial Q := Submodule.nontrivial_iff_ne_bot.mpr hQ
    exact Module.finrank_pos
  have hD0 : D ≠ ⊥ := by
    intro h
    have hw0 : w ⟨0, hkpos⟩ ∈ D := Submodule.subset_span ⟨_, rfl⟩
    rw [h, Submodule.mem_bot] at hw0
    have h2 := hbi ⟨0, hkpos⟩ ⟨0, hkpos⟩
    rw [hw0, inner_zero_right] at h2
    simp at h2
  obtain ⟨q, hqQ, hq0, hqn⟩ := Formalism.F.shortVector_of Formalism.F.covol_eq_covolume' E Q hQd hQ
  obtain ⟨y, hyD, hy0, hyn⟩ := Formalism.F.shortVector_of Formalism.F.covol_eq_covolume' E D hDd hD0
  refine ⟨q, hqQ, hq0, ?_⟩
  have hly := hDl y hyD hy0
  rw [hrkD, hcovD, hdetw, Real.sqrt_inv, ← hcovQ] at hyn
  rw [hrkQ] at hqn ⊢
  have ht : 0 < Formalism.F.covol Q ^ ((1 : ℝ) / k) := Real.rpow_pos_of_pos hpos _
  rw [Real.inv_rpow hpos.le] at hyn
  have hsk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt (Nat.cast_nonneg k)
  have h1 : l * Formalism.F.covol Q ^ ((1 : ℝ) / k) ≤ Real.sqrt k := by
    have h2 := hly.trans hyn
    calc l * Formalism.F.covol Q ^ ((1 : ℝ) / k)
        ≤ Real.sqrt k * (Formalism.F.covol Q ^ ((1 : ℝ) / k))⁻¹ * Formalism.F.covol Q ^ ((1 : ℝ) / k) :=
          mul_le_mul_of_nonneg_right h2 ht.le
      _ = Real.sqrt k := by field_simp
  rw [le_div_iff₀ hl]
  calc ‖q‖ * l ≤ Real.sqrt k * Formalism.F.covol Q ^ ((1 : ℝ) / k) * l :=
        mul_le_mul_of_nonneg_right hqn hl.le
    _ = Real.sqrt k * (l * Formalism.F.covol Q ^ ((1 : ℝ) / k)) := by ring
    _ ≤ Real.sqrt k * Real.sqrt k := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
    _ = k := hsk

end Formalism.NormUnitaryCountingLemmas
end
end

section
open Module Submodule

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_starProjection_ne_zero_norm_le_of_dualMinimum (M : Submodule ℤ E) [hMd : DiscreteTopology M]
    (hspan : span ℝ (M : Set E) = ⊤) {l : ℝ} (hl : 0 < l)
    (hdual : ∀ y : E, y ≠ 0 → (∀ x ∈ M, ∃ z : ℤ, inner ℝ x y = (z : ℝ)) → l ≤ ‖y‖)
    (W : Submodule ℝ E) (N : Submodule ℤ E) (hNM : N ≤ M) (hNW : span ℝ (N : Set E) = W)
    (hW : W ≠ ⊤) :
    ∃ m ∈ M, Wᗮ.starProjection m ≠ 0 ∧
      ‖Wᗮ.starProjection m‖ ≤ (finrank ℝ E : ℝ) / l := by
  classical
  obtain ⟨hSat, hNS, -⟩ := Formalism.F.saturation_properties E M N hMd hNM
  obtain ⟨hQd, hrk, -⟩ := Formalism.F.degree_quotient E M (Formalism.F.satur M N) hMd hSat
  have hSW : span ℝ ((Formalism.F.satur M N : Submodule ℤ E) : Set E) = W := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      rw [← hNW]
      exact (Submodule.mem_inf.mp hx).2
    · rw [← hNW]
      exact Submodule.span_mono (show (N : Set E) ⊆ Formalism.F.satur M N from hNS)
  have hQeq : ∀ q, q ∈ Formalism.F.quot M (Formalism.F.satur M N) ↔ ∃ m ∈ M, Wᗮ.starProjection m = q := by
    intro q
    simp [Formalism.F.quot, hSW, Submodule.mem_map]
  haveI := hQd
  have hPzero : ∀ x ∈ W, Wᗮ.starProjection x = 0 := by
    intro x hx
    have h1 := Submodule.starProjection_add_starProjection_orthogonal (K := W) x
    rw [Submodule.starProjection_eq_self_iff.mpr hx] at h1
    simpa using h1
  have hsubW : ∀ m : E, m - Wᗮ.starProjection m ∈ W := by
    intro m
    have h1 := Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) m
    rwa [Submodule.orthogonal_orthogonal] at h1
  have hQne : Formalism.F.quot M (Formalism.F.satur M N) ≠ ⊥ := by
    intro hQ0
    apply hW
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    intro m hm
    have hq : Wᗮ.starProjection m ∈ Formalism.F.quot M (Formalism.F.satur M N) := (hQeq _).mpr ⟨m, hm, rfl⟩
    rw [hQ0, Submodule.mem_bot] at hq
    have h1 := hsubW m
    rw [hq, sub_zero] at h1
    exact h1
  have hdual' : ∀ y ∈ span ℝ ((Formalism.F.quot M (Formalism.F.satur M N) : Submodule ℤ E) : Set E), y ≠ 0 →
      (∀ x ∈ Formalism.F.quot M (Formalism.F.satur M N), ∃ z : ℤ, inner ℝ x y = (z : ℝ)) → l ≤ ‖y‖ := by
    intro y hy hy0 hint
    apply hdual y hy0
    intro x hx
    obtain ⟨z, hz⟩ := hint _ ((hQeq _).mpr ⟨x, hx, rfl⟩)
    refine ⟨z, ?_⟩
    have hyW : y ∈ Wᗮ := by
      refine (Submodule.span_le.mpr ?_) hy
      intro q hq
      obtain ⟨m, -, rfl⟩ := (hQeq q).mp hq
      exact Submodule.starProjection_apply_mem _ _
    rw [← hz, Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hyW]
  obtain ⟨q, hqQ, hq0, hqle⟩ := exists_ne_zero_norm_le_rank_div_of_dualMinimum (Formalism.F.quot M (Formalism.F.satur M N)) hQne hl hdual'
  obtain ⟨m, hm, rfl⟩ := (hQeq q).mp hqQ
  refine ⟨m, hm, hq0, le_trans hqle ?_⟩
  have hMrk : Formalism.F.rk M = finrank ℝ E := by
    haveI : IsZLattice ℝ M := ⟨hspan⟩
    exact ZLattice.rank ℝ M
  have hle : Formalism.F.rk (Formalism.F.quot M (Formalism.F.satur M N)) ≤ finrank ℝ E := by
    rw [← hMrk, hrk]
    exact Nat.le_add_left _ _
  exact div_le_div_of_nonneg_right (by exact_mod_cast hle) hl.le

theorem norm_add_sq_eq_of_inner_eq_zero {x y : E} (h : inner ℝ x y = 0) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [norm_add_sq_real, h]
  ring

theorem exists_short_linearIndependent_of_dualMinimum (M : Submodule ℤ E) [hMd : DiscreteTopology M]
    (hspan : span ℝ (M : Set E) = ⊤) {l : ℝ} (hl : 0 < l)
    (hdual : ∀ y : E, y ≠ 0 → (∀ x ∈ M, ∃ z : ℤ, inner ℝ x y = (z : ℝ)) → l ≤ ‖y‖) :
    ∀ k, k ≤ finrank ℝ E → ∃ b : Fin k → E, (∀ i, b i ∈ M) ∧ LinearIndependent ℝ b ∧
      (∀ i, ‖b i‖ ^ 2 ≤ (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) / l) ^ 2) ∧
      (∀ w ∈ span ℝ (Set.range b), ∃ z ∈ span ℤ (Set.range b),
        ‖w - z‖ ^ 2 ≤ (k : ℝ) * ((finrank ℝ E : ℝ) / l) ^ 2 / 4) := by
  classical
  have hPzero : ∀ (W : Submodule ℝ E), ∀ x ∈ W, Wᗮ.starProjection x = 0 := by
    intro W x hx
    have h1 := Submodule.starProjection_add_starProjection_orthogonal (K := W) x
    rw [Submodule.starProjection_eq_self_iff.mpr hx] at h1
    simpa using h1
  have hsubW : ∀ (W : Submodule ℝ E) (m : E), m - Wᗮ.starProjection m ∈ W := by
    intro W m
    have h1 := Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) m
    rwa [Submodule.orthogonal_orthogonal] at h1
  have horth : ∀ (W : Submodule ℝ E) (u : E) (m : E), u ∈ W →
      inner ℝ u (Wᗮ.starProjection m) = 0 := by
    intro W u m hu
    exact Submodule.inner_right_of_mem_orthogonal hu (Submodule.starProjection_apply_mem _ _)
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨Fin.elim0, fun i => i.elim0, linearIndependent_empty_type, fun i => i.elim0, ?_⟩
    intro w hw
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    have hw0 : w = 0 := by simpa [Set.range_eq_empty] using hw
    subst hw0
    simp
  | succ k ih =>
    intro hk
    obtain ⟨b, hbM, hbli, hbn, hbd⟩ := ih (by omega)
    have hNM : span ℤ (Set.range b) ≤ M := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbM i)
    have hNW : span ℝ ((span ℤ (Set.range b) : Submodule ℤ E) : Set E) = span ℝ (Set.range b) :=
      Submodule.span_span_of_tower ℤ ℝ (Set.range b)
    have hWtop : span ℝ (Set.range b) ≠ ⊤ := by
      intro hW
      have h1 : finrank ℝ (span ℝ (Set.range b)) = k := by
        rw [finrank_span_eq_card hbli, Fintype.card_fin]
      rw [hW, finrank_top] at h1
      omega
    obtain ⟨m, hm, hp0, hple⟩ :=
      exists_starProjection_ne_zero_norm_le_of_dualMinimum M hspan hl hdual (span ℝ (Set.range b)) (span ℤ (Set.range b)) hNM hNW hWtop
    obtain ⟨z, hz, hzd⟩ := hbd (m - (span ℝ (Set.range b))ᗮ.starProjection m) (hsubW _ m)
    have hzW : z ∈ span ℝ (Set.range b) := by
      rw [← hNW]
      exact Submodule.subset_span hz
    have hcnn : 0 ≤ (finrank ℝ E : ℝ) / l := div_nonneg (Nat.cast_nonneg _) hl.le
    have hk1 : ((k : ℝ) + 1) ≤ (finrank ℝ E : ℝ) := by exact_mod_cast hk
    refine ⟨Fin.snoc b (m - z), ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last]
        exact M.sub_mem hm (hNM hz)
      · simp only [Fin.snoc_castSucc]
        exact hbM j
    · rw [linearIndependent_fin_snoc]
      refine ⟨hbli, fun hmem => hp0 ?_⟩
      have e : m = (m - z) + z := by abel
      rw [e, map_add, hPzero _ _ hmem, hPzero _ _ hzW, add_zero]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last]
        have e : m - z = (span ℝ (Set.range b))ᗮ.starProjection m +
            ((m - (span ℝ (Set.range b))ᗮ.starProjection m) - z) := by abel
        have hin : ((m - (span ℝ (Set.range b))ᗮ.starProjection m) - z) ∈ span ℝ (Set.range b) :=
          Submodule.sub_mem _ (hsubW _ m) hzW
        have hi : inner ℝ ((span ℝ (Set.range b))ᗮ.starProjection m)
            ((m - (span ℝ (Set.range b))ᗮ.starProjection m) - z) = 0 := by
          rw [real_inner_comm]
          exact horth _ _ m hin
        rw [e, norm_add_sq_eq_of_inner_eq_zero hi]
        have h2 : ‖(span ℝ (Set.range b))ᗮ.starProjection m‖ ^ 2 ≤ ((finrank ℝ E : ℝ) / l) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hple 2
        have hc2 : 0 ≤ ((finrank ℝ E : ℝ) / l) ^ 2 := sq_nonneg _
        nlinarith
      · simp only [Fin.snoc_castSucc]
        exact hbn j
    · intro w hw
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hw
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      have hu : ∑ j : Fin k, c j.castSucc • b j ∈ span ℝ (Set.range b) :=
        Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
      have hδ := abs_sub_round (c (Fin.last k))
      have hv : ∑ j : Fin k, c j.castSucc • b j +
          (c (Fin.last k) - (round (c (Fin.last k)) : ℝ)) •
            ((m - (span ℝ (Set.range b))ᗮ.starProjection m) - z) ∈ span ℝ (Set.range b) :=
        Submodule.add_mem _ hu (Submodule.smul_mem _ _ (Submodule.sub_mem _ (hsubW _ m) hzW))
      obtain ⟨z'', hz'', hz''d⟩ := hbd _ hv
      have hmem_last : m - z ∈ span ℤ (Set.range (Fin.snoc b (m - z) : Fin (k + 1) → E)) :=
        Submodule.subset_span ⟨Fin.last k, by simp⟩
      have hspan_le : span ℤ (Set.range b) ≤ span ℤ (Set.range (Fin.snoc b (m - z) : Fin (k + 1) → E)) :=
        Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact Submodule.subset_span ⟨j.castSucc, by simp⟩)
      refine ⟨(round (c (Fin.last k))) • (m - z) + z'', Submodule.add_mem _
        (Submodule.smul_mem _ _ hmem_last) (hspan_le hz''), ?_⟩
      have hdecomp : ∑ j : Fin k, c j.castSucc • b j + c (Fin.last k) • (m - z) -
          ((round (c (Fin.last k))) • (m - z) + z'') =
          (∑ j : Fin k, c j.castSucc • b j +
            (c (Fin.last k) - (round (c (Fin.last k)) : ℝ)) •
              ((m - (span ℝ (Set.range b))ᗮ.starProjection m) - z) - z'') +
          (c (Fin.last k) - (round (c (Fin.last k)) : ℝ)) • (span ℝ (Set.range b))ᗮ.starProjection m := by
        rw [← Int.cast_smul_eq_zsmul ℝ]
        simp only [sub_smul, smul_sub]
        abel
      have hz''W : z'' ∈ span ℝ (Set.range b) := by
        rw [← hNW]
        exact Submodule.subset_span hz''
      have hi : inner ℝ (∑ j : Fin k, c j.castSucc • b j +
            (c (Fin.last k) - (round (c (Fin.last k)) : ℝ)) •
              ((m - (span ℝ (Set.range b))ᗮ.starProjection m) - z) - z'')
          ((c (Fin.last k) - (round (c (Fin.last k)) : ℝ)) • (span ℝ (Set.range b))ᗮ.starProjection m) = 0 := by
        rw [real_inner_smul_right, horth _ _ m (Submodule.sub_mem _ hv hz''W), mul_zero]
      rw [hdecomp, norm_add_sq_eq_of_inner_eq_zero hi, norm_smul, mul_pow, Real.norm_eq_abs]
      have hδ2 : |c (Fin.last k) - (round (c (Fin.last k)) : ℝ)| ^ 2 ≤ 1 / 4 := by
        have h0 := abs_nonneg (c (Fin.last k) - (round (c (Fin.last k)) : ℝ))
        nlinarith
      have h2 : ‖(span ℝ (Set.range b))ᗮ.starProjection m‖ ^ 2 ≤ ((finrank ℝ E : ℝ) / l) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hple 2
      have hc2 : 0 ≤ ((finrank ℝ E : ℝ) / l) ^ 2 := sq_nonneg _
      have hp2 : 0 ≤ ‖(span ℝ (Set.range b))ᗮ.starProjection m‖ ^ 2 := sq_nonneg _
      push_cast
      nlinarith [mul_le_mul hδ2 h2 hp2 (by norm_num : (0 : ℝ) ≤ 1 / 4)]

theorem shortIndependentVectorsOfDualMinimum : ShortIndependentVectorsOfDualMinimum := by
  intro E _ _ _ M hMd hspan l hl hdual
  haveI := hMd
  obtain ⟨b, hbM, hbli, hbn, -⟩ := exists_short_linearIndependent_of_dualMinimum M hspan hl hdual (finrank ℝ E) le_rfl
  refine ⟨b, hbM, hbli, fun i => ?_⟩
  have hn0 : (0 : ℝ) < (finrank ℝ E : ℝ) := by exact_mod_cast Fin.pos i
  have h1 : ‖b i‖ ≤ Real.sqrt (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) / l) := by
    have h2 := hbn i
    have h3 : 0 ≤ Real.sqrt (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) / l) := by positivity
    have h4 : (Real.sqrt (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) / l)) ^ 2 =
        (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) / l) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hn0.le]
    nlinarith [norm_nonneg (b i)]
  have h5 : (finrank ℝ E : ℝ) ^ ((3 : ℝ) / 2) = (finrank ℝ E : ℝ) * Real.sqrt (finrank ℝ E : ℝ) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hn0, Real.rpow_one, Real.sqrt_eq_rpow]
  rw [h5]
  calc ‖b i‖ ≤ Real.sqrt (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) / l) := h1
    _ = (finrank ℝ E : ℝ) * Real.sqrt (finrank ℝ E : ℝ) / l := by ring

end Formalism.NormUnitaryCountingLemmas
end
end
