import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearBarGoodPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedCharacterGood
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemNsp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroMinorOfRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatPartitionOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatReindexRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartStackDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartBoundedCoefficients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartShearInvariance
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedLinearBarDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankCoinvariantInducedIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedScalarIrreducible

section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_minor_of_rank : ∀ (k : Type) [Field k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ρ : ℕ) (Y : Matrix A D k), ρ ≤ Y.rank → ∃ S : Fin ρ → A, ∃ τ : Fin ρ → D, (Y.submatrix S τ).det ≠ 0 := by
  first | exact @GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank | exact GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank | (intros; apply GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank <;> assumption)
end

section
open GlobalTheory.WeilM Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_partition_of_unity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ι : Type) [Finite ι] (U : ι → Set (Matrix A D k)), (∀ i, IsOpen (U i)) → ∀ f ∈ SB (Matrix A D k), (∀ Y, f Y ≠ 0 → ∃ i, Y ∈ U i) → f ∈ Submodule.span ℂ {g | g ∈ SB (Matrix A D k) ∧ ∃ i, ∀ Y, g Y ≠ 0 → Y ∈ U i} := by
  first | exact @GlobalTheory.CoverSB.mem_span_of_cover | exact GlobalTheory.CoverSB.mem_span_of_cover | (intros; apply GlobalTheory.CoverSB.mem_span_of_cover <;> assumption)
end

section
open GlobalTheory.WeilM Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_reindex_rows : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A A' D : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] (ν : kˣ →* ℂˣ) (e : A ≃ A'), (∀ f ∈ SB (Matrix A' D k), (fun Y : Matrix A D k => f (Y.submatrix e.symm id)) ∈ SB (Matrix A D k)) ∧ (∀ f ∈ GlobalTheory.RankStrata.Nsp k A' D ν, (fun Y : Matrix A D k => f (Y.submatrix e.symm id)) ∈ GlobalTheory.RankStrata.Nsp k A D ν) := by
  first | exact @GlobalTheory.RankStrata.rowRenum_SB_Nsp | exact GlobalTheory.RankStrata.rowRenum_SB_Nsp | (intros; apply GlobalTheory.RankStrata.rowRenum_SB_Nsp <;> assumption)
end

section
open GlobalTheory.WeilM Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_chart_stack_decomposition : ∀ (k : Type) [Field k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D] (τ : R → D) (Y : Matrix (R ⊕ T) D k), Y.rank ≤ Fintype.card R → (Y.submatrix Sum.inl τ).det ≠ 0 → ∃ C : Matrix T R k, Y = GlobalTheory.RankChart.stack Y.toRows₁ C := by
  first | exact @GlobalTheory.RankChart.exists_eq_stack | exact GlobalTheory.RankChart.exists_eq_stack | (intros; apply GlobalTheory.RankChart.exists_eq_stack <;> assumption)
end

section
open GlobalTheory.WeilM Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_chart_bounded_coefficients : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D] (τ : R → D), ∀ f ∈ SB (Matrix (R ⊕ T) D k), (∀ Y : Matrix (R ⊕ T) D k, f Y ≠ 0 → (Y.submatrix Sum.inl τ).det ≠ 0) → ∃ a : kˣ, ∀ (Y₁ : Matrix R D k) (C : Matrix T R k), f (GlobalTheory.RankChart.stack Y₁ C) ≠ 0 → C ∈ GlobalTheory.LocMod.Inhab.box T R a := by
  first | exact @GlobalTheory.RankChart.bounded_coeff_of_SB | exact GlobalTheory.RankChart.bounded_coeff_of_SB | (intros; apply GlobalTheory.RankChart.bounded_coeff_of_SB <;> assumption)
end

section
open GlobalTheory.WeilM Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_chart_shear_invariance : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D], ∀ f ∈ SB (Matrix (R ⊕ T) D k), ∃ b : kˣ, ∀ (Y : Matrix (R ⊕ T) D k), ∀ c ∈ GlobalTheory.LocMod.Inhab.box T R b, f (GlobalTheory.RankChart.shear c Y) = f Y := by
  first | exact @GlobalTheory.RankChart.sb_shear_invariant | exact GlobalTheory.RankChart.sb_shear_invariant | (intros; apply GlobalTheory.RankChart.sb_shear_invariant <;> assumption)
end

section
section
open GlobalTheory.WeilM Matrix

namespace GlobalTheory.RankChart
open GlobalTheory.SplitFlip GlobalTheory.LocMod.Inhab ValuativeRel

theorem exists_mem_nsp_eq_of_rank_le : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D] [Nonempty T] (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν ϖ : ℂ)) ^ m ≠ (r : ℂ)) → ∀ (τ : R → D), ∀ f ∈ SB (Matrix (R ⊕ T) D k), (∀ Y : Matrix (R ⊕ T) D k, f Y ≠ 0 → (Y.submatrix Sum.inl τ).det ≠ 0) → ∃ Φ ∈ GlobalTheory.RankStrata.Nsp k (R ⊕ T) D ν, ∀ Y : Matrix (R ⊕ T) D k, Y.rank ≤ Fintype.card R → Φ Y = f Y := by
  intro k _ _ _ _ R T D _ _ _ _ _ _ _ ν ϖ hϖ hν τ f hf hsupp
  classical
  obtain ⟨a, ha⟩ := GlobalTheory.T.rank_chart_bounded_coefficients k R T D τ f hf hsupp
  obtain ⟨b, hb⟩ := GlobalTheory.T.rank_chart_shear_invariance k R T D f hf
  have hv0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  have hv1 : valuation k (ϖ : k) ≤ 1 := hϖ ▸ uniformizer_lt_one.le
  have hva : ∀ x : k, (valuation k (x : k) ≤ valuation k (((ϖ⁻¹ * a : kˣ)) : k) ↔
      valuation k ((ϖ : k) * x) ≤ valuation k (a : k)) := by
    intro x
    rw [Units.val_mul, map_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, le_inv_mul_iff₀ hv0]
  have hHH' : box T R a ≤ box T R (ϖ⁻¹ * a) := by
    intro C hC r q
    rw [hva, map_mul]
    exact (mul_le_of_le_one_left' hv1).trans (hC r q)
  have hdilmem : ∀ C : Matrix T R k, ((ϖ : k) • C ∈ box T R a ↔ C ∈ box T R (ϖ⁻¹ * a)) := fun C =>
    forall_congr' fun r => forall_congr' fun q => by rw [hva]; rfl
  generalize hH : box T R a = H at ha hHH' hdilmem
  generalize hH' : box T R (ϖ⁻¹ * a) = H' at hHH' hdilmem
  generalize hL : box T R b = L at hb
  haveI : Finite (H ⧸ L.addSubgroupOf H) := hH ▸ hL ▸ finite_box (Y := T) (Y' := R) (k := k) a b
  haveI : Finite (H' ⧸ H.addSubgroupOf H') := hH ▸ hH' ▸ finite_box (Y := T) (Y' := R) (k := k) (ϖ⁻¹ * a) a
  letI : Fintype (H ⧸ L.addSubgroupOf H) := Fintype.ofFinite _
  letI : Fintype (H' ⧸ H.addSubgroupOf H') := Fintype.ofFinite _

  have hinvL : ∀ (Y₁ : Matrix R D k) (C C' : Matrix T R k), C' - C ∈ L →
      f (stack Y₁ C') = f (stack Y₁ C) := by
    intro Y₁ C C' h
    have := hb (stack Y₁ C) (C' - C) h
    rwa [shear_stack, add_sub_cancel] at this
  obtain ⟨Ψ₁, hΨ₁, hSB⟩ : ∃ Ψ₁ : Matrix (R ⊕ T) D k → ℂ,
      (∀ Y, Ψ₁ Y = ∑ q : H ⧸ L.addSubgroupOf H, f (shear ((q.out : H) : Matrix T R k) Y)) ∧
      Ψ₁ ∈ SB (Matrix (R ⊕ T) D k) :=
    ⟨∑ q : H ⧸ L.addSubgroupOf H, omB ν ν (shearGL ((q.out : H) : Matrix T R k)) 1 f,
      fun Y => by simp [Finset.sum_apply, omB_shearGL],
      Submodule.sum_mem _ fun q _ => omB_mem_SB ν ν _ _ hf⟩
  have hzero : ∀ Y : Matrix (R ⊕ T) D k, (Y.submatrix Sum.inl τ).det = 0 → Ψ₁ Y = 0 := by
    intro Y hY
    rw [hΨ₁]
    refine Finset.sum_eq_zero fun q _ => ?_
    by_contra h
    exact hsupp _ h (by rwa [submatrix_inl_eq, toRows₁_shear, ← submatrix_inl_eq])
  have hA1 : ∀ (Y₁ : Matrix R D k) (C : Matrix T R k),
      Ψ₁ (stack Y₁ C) = if C ∈ H then Ψ₁ (stack Y₁ 0) else 0 := by
    intro Y₁ C
    have h := sum_shift_out (fun C => f (stack Y₁ C)) H L (fun x y h => hinvL Y₁ x y h) (ha Y₁) C
    simp only [hΨ₁, shear_stack, zero_add]
    exact h
  have hA2 : ∀ (Y₁ : Matrix R D k) (C : Matrix T R k),
      ∑ q' : H' ⧸ H.addSubgroupOf H', Ψ₁ (stack Y₁ (C + ((q'.out : H') : Matrix T R k))) =
        if C ∈ H' then Ψ₁ (stack Y₁ 0) else 0 := by
    intro Y₁ C
    rw [Finset.sum_congr rfl fun q' _ => hA1 Y₁ _]
    exact sum_ite_out H H' hHH' _ C

  obtain ⟨lam, hlam⟩ : ∃ lam : ℂ, lam = (ν ϖ : ℂ) ^ Fintype.card T * apow (ϖ ^ Fintype.card T) ((Fintype.card D : ℂ) / 2) :=
    ⟨_, rfl⟩
  obtain ⟨n₁, hn₁, hexp⟩ : ∃ n₁ ∈ GlobalTheory.RankStrata.Nsp k (R ⊕ T) D ν, ∀ Y, n₁ Y = Ψ₁ Y - lam * Ψ₁ (dil (ϖ : k) Y) +
      lam * (∑ q' : H' ⧸ H.addSubgroupOf H', Ψ₁ (shear ((q'.out : H') : Matrix T R k) Y) -
        (Fintype.card (H' ⧸ H.addSubgroupOf H') : ℂ) * Ψ₁ Y) := by
    refine ⟨(Ψ₁ - omB ν ν (dilGL ϖ : GL (R ⊕ T) k) 1 Ψ₁) +
      lam • ∑ q' : H' ⧸ H.addSubgroupOf H', (omB ν ν (shearGL ((q'.out : H') : Matrix T R k)) 1 Ψ₁ - Ψ₁), ?_, ?_⟩
    · refine add_mem ?_ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q' _ =>
        GlobalTheory.RankStrata.sub_mem_Nsp ν _ hSB))
      rw [← neg_sub]
      exact Submodule.neg_mem _ (GlobalTheory.RankStrata.sub_mem_Nsp ν _ hSB)
    · intro Y
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, omB_dilGL,
        omB_shearGL, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hlam,
        Pi.mul_apply, Pi.natCast_apply]
  have hn₁val : ∀ Y : Matrix (R ⊕ T) D k, Y.rank ≤ Fintype.card R →
      n₁ Y = (1 - lam * Fintype.card (H' ⧸ H.addSubgroupOf H')) * Ψ₁ Y := by
    intro Y hY
    rw [hexp]
    by_cases hd : (Y.submatrix Sum.inl τ).det = 0
    · rw [hzero Y hd, hzero _ (by rwa [submatrix_inl_eq, toRows₁_dil, ← submatrix_inl_eq]),
        Finset.sum_eq_zero fun q' _ => hzero _ (by rwa [submatrix_inl_eq, toRows₁_shear, ← submatrix_inl_eq])]
      ring
    · obtain ⟨C, hC⟩ := GlobalTheory.T.rank_chart_stack_decomposition k R T D τ Y hY hd
      rw [hC, dil_stack]
      simp only [shear_stack]
      rw [hA2, hA1 _ ((ϖ : k) • C), hdilmem]
      ring

  obtain ⟨n₀, hn₀, hn₀val⟩ : ∃ n₀ ∈ GlobalTheory.RankStrata.Nsp k (R ⊕ T) D ν,
      ∀ Y, n₀ Y = Ψ₁ Y - (Fintype.card (H ⧸ L.addSubgroupOf H) : ℂ) * f Y := by
    refine ⟨∑ q : H ⧸ L.addSubgroupOf H, (omB ν ν (shearGL ((q.out : H) : Matrix T R k)) 1 f - f),
      Submodule.sum_mem _ fun q _ => GlobalTheory.RankStrata.sub_mem_Nsp ν _ hf, fun Y => ?_⟩
    simp only [hΨ₁, Finset.sum_apply, Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, omB_shearGL]

  have hQ : (Fintype.card (H ⧸ L.addSubgroupOf H) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hlamne : 1 - lam * (Fintype.card (H' ⧸ H.addSubgroupOf H') : ℂ) ≠ 0 := by
    obtain ⟨r, hr, hr'⟩ := exists_apow_eq (ϖ ^ Fintype.card T) (Fintype.card D)
    have hc : (0 : ℝ) < r * Fintype.card (H' ⧸ H.addSubgroupOf H') :=
      mul_pos hr (Nat.cast_pos.2 Fintype.card_pos)
    intro h
    refine hν (Fintype.card T) Fintype.card_pos (r * Fintype.card (H' ⧸ H.addSubgroupOf H'))⁻¹ ?_
    have h1 : (ν ϖ : ℂ) ^ Fintype.card T * ((r * Fintype.card (H' ⧸ H.addSubgroupOf H') : ℝ) : ℂ) = 1 := by
      rw [hlam, hr'] at h
      push_cast
      linear_combination -h
    rw [eq_inv_of_mul_eq_one_left h1, Complex.ofReal_inv]
  refine ⟨(Fintype.card (H ⧸ L.addSubgroupOf H) : ℂ)⁻¹ •
      ((1 - lam * Fintype.card (H' ⧸ H.addSubgroupOf H'))⁻¹ • n₁ - n₀),
    Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hn₁) hn₀), fun Y hY => ?_⟩
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hn₁val Y hY, hn₀val]
  field_simp
  ring

end GlobalTheory.RankChart
end

open GlobalTheory.WeilM Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_minor_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D] [Nonempty T] (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν ϖ : ℂ)) ^ m ≠ (r : ℂ)) → ∀ (τ : R → D), ∀ f ∈ SB (Matrix (R ⊕ T) D k), (∀ Y : Matrix (R ⊕ T) D k, f Y ≠ 0 → (Y.submatrix Sum.inl τ).det ≠ 0) → ∃ Φ ∈ GlobalTheory.RankStrata.Nsp k (R ⊕ T) D ν, ∀ Y : Matrix (R ⊕ T) D k, Y.rank ≤ Fintype.card R → Φ Y = f Y := by
  atlas_forward_decl GlobalTheory.RankChart.exists_mem_nsp_eq_of_rank_le
end

section
open GlobalTheory.WeilM Matrix

noncomputable section
namespace GlobalTheory.RankStrata

theorem exists_fullRank_sub_mem_span : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν ϖ : ℂ)) ^ m ≠ (r : ℂ)) →
    ∀ Ψ ∈ SB (Matrix (Fin n) (Fin d) k), ∃ Ψ₀ ∈ SB (Matrix (Fin n) (Fin d) k), (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≠ n → Ψ₀ Y = 0) ∧
      Ψ - Ψ₀ ∈ Submodule.span ℂ {Z | ∃ g : GL (Fin n) k, ∃ Ψ' ∈ SB (Matrix (Fin n) (Fin d) k), Z = GlobalTheory.SplitFlip.omB ν ν g 1 Ψ' - Ψ'} := by
  intro k _ _ _ _ n d ν ϖ hϖ hν Ψ hΨ
  classical
  have piece : ∀ ρ < n, ∀ f : Matrix (Fin n) (Fin d) k → ℂ, f ∈ SB (Matrix (Fin n) (Fin d) k) →
      ∀ (S : Fin ρ → Fin n) (τ : Fin ρ → Fin d), (∀ Y, f Y ≠ 0 → (Y.submatrix S τ).det ≠ 0) →
      ∃ Φ ∈ Nsp k (Fin n) (Fin d) ν, ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≤ ρ → Φ Y = f Y := by
    intro ρ hρ f hf S τ hS
    by_cases h0 : ∀ Y, f Y = 0
    · exact ⟨0, Submodule.zero_mem _, fun Y _ => by simp [h0 Y]⟩
    push_neg at h0
    obtain ⟨Y0, hY0⟩ := h0
    have hinj : Function.Injective S := by
      intro i j hij
      by_contra hne
      exact hS Y0 hY0 (Matrix.det_zero_of_row_eq hne (by ext l; simp [hij]))
    let e' : Fin ρ ⊕ ↥(Set.range S)ᶜ ≃ Fin n :=
      (Equiv.sumCongr (Equiv.ofInjective S hinj) (Equiv.refl _)).trans (Equiv.Set.sumCompl _)
    have he' : ∀ i, e'.symm (S i) = Sum.inl i := fun i => by
      rw [Equiv.symm_apply_eq]; simp [e']
    haveI : Nonempty ↥(Set.range S)ᶜ := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      have := Fintype.card_congr e'
      simp at this
      omega
    have hT := GlobalTheory.T.schwartzBruhat_reindex_rows k (Fin ρ ⊕ ↥(Set.range S)ᶜ) (Fin n) (Fin d) ν e'
    obtain ⟨Φ', hΦ', hΦ'f⟩ := GlobalTheory.T.schwartzBruhat_minor_support k (Fin ρ) (↥(Set.range S)ᶜ) (Fin d) ν ϖ hϖ hν τ
      (fun Z => f (Z.submatrix e'.symm id)) (hT.1 f hf) (fun Z hZ => by
        have := hS _ hZ
        rwa [Matrix.submatrix_submatrix, show (e'.symm ∘ S) = Sum.inl from funext he'] at this)
    have hT2 := GlobalTheory.T.schwartzBruhat_reindex_rows k (Fin n) (Fin ρ ⊕ ↥(Set.range S)ᶜ) (Fin d) ν e'.symm
    refine ⟨_, hT2.2 Φ' hΦ', fun Y hY => ?_⟩
    simp only [Equiv.symm_symm]
    rw [hΦ'f _ (by rw [show (id : Fin d → Fin d) = ⇑(Equiv.refl (Fin d)) from rfl, Matrix.rank_submatrix]; simpa using hY)]
    simp [Matrix.submatrix_submatrix]
  have step : ∀ ρ < n, ∀ g ∈ SB (Matrix (Fin n) (Fin d) k),
      (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank < ρ → g Y = 0) →
      ∃ Φ ∈ Nsp k (Fin n) (Fin d) ν, ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≤ ρ → Φ Y = g Y := by
    intro ρ hρ g hg hg0
    haveI : T2Space k := by
      letI := IsTopologicalAddGroup.rightUniformSpace k
      haveI := isUniformAddGroup_of_addCommGroup (G := k)
      infer_instance
    have hsp := GlobalTheory.T.schwartzBruhat_partition_of_unity k (Fin n) (Fin d) ((Fin ρ → Fin n) × (Fin ρ → Fin d))
      (fun i => {Y : Matrix (Fin n) (Fin d) k | (Y.submatrix i.1 i.2).det ≠ 0})
      (fun i => isOpen_ne_fun ((continuous_id.matrix_submatrix i.1 i.2).matrix_det) continuous_const) g hg
      (fun Y hY => by
        have : ρ ≤ Y.rank := by
          by_contra h
          exact hY (hg0 Y (by omega))
        obtain ⟨S, τ, h⟩ := GlobalTheory.T.exists_nonzero_minor_of_rank k _ _ ρ Y this
        exact ⟨(S, τ), h⟩)
    refine Submodule.span_induction
      (p := fun g _ => ∃ Φ ∈ Nsp k (Fin n) (Fin d) ν, ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≤ ρ → Φ Y = g Y)
      ?_ ?_ ?_ ?_ hsp
    · rintro f ⟨hf, i, hi⟩
      exact piece ρ hρ f hf i.1 i.2 hi
    · exact ⟨0, Submodule.zero_mem _, fun _ _ => rfl⟩
    · rintro x y _ _ ⟨Φ, hΦ, h⟩ ⟨Φ', hΦ', h'⟩
      exact ⟨Φ + Φ', Submodule.add_mem _ hΦ hΦ', fun Y hY => by simp [h Y hY, h' Y hY]⟩
    · rintro c x _ ⟨Φ, hΦ, h⟩
      exact ⟨c • Φ, Submodule.smul_mem _ c hΦ, fun Y hY => by simp [h Y hY]⟩
  have ind : ∀ ρ ≤ n, ∃ Ψρ ∈ SB (Matrix (Fin n) (Fin d) k),
      (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank < ρ → Ψρ Y = 0) ∧ Ψ - Ψρ ∈ Nsp k (Fin n) (Fin d) ν := by
    intro ρ
    induction ρ with
    | zero => intro _; exact ⟨Ψ, hΨ, fun Y h => absurd h (Nat.not_lt_zero _), by simp⟩
    | succ ρ ih =>
      intro hρ
      obtain ⟨Ψρ, hSB, h0, hN⟩ := ih (by omega)
      obtain ⟨Φ, hΦ, hΦe⟩ := step ρ (by omega) Ψρ hSB h0
      refine ⟨Ψρ - Φ, Submodule.sub_mem _ hSB (Nsp_le_SB _ _ ν hΦ), fun Y hY => ?_, ?_⟩
      · simp [hΦe Y (by omega)]
      · have : Ψ - (Ψρ - Φ) = (Ψ - Ψρ) + Φ := by abel
        rw [this]; exact Submodule.add_mem _ hN hΦ
  obtain ⟨Ψ₀, h1, h2, h3⟩ := ind n le_rfl
  refine ⟨Ψ₀, h1, fun Y hY => h2 Y (lt_of_le_of_ne ?_ hY), h3⟩
  simpa using Matrix.rank_le_card_height Y

end GlobalTheory.RankStrata
end
end

section
open GlobalTheory.WeilM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_full_rank_modulo_translates : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν ϖ : ℂ)) ^ m ≠ (r : ℂ)) →
    ∀ Ψ ∈ SB (Matrix (Fin n) (Fin d) k), ∃ Ψ₀ ∈ SB (Matrix (Fin n) (Fin d) k), (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≠ n → Ψ₀ Y = 0) ∧
      Ψ - Ψ₀ ∈ Submodule.span ℂ {Z | ∃ g : GL (Fin n) k, ∃ Ψ' ∈ SB (Matrix (Fin n) (Fin d) k), Z = GlobalTheory.SplitFlip.omB ν ν g 1 Ψ' - Ψ'} := by
  first | exact @GlobalTheory.RankStrata.exists_fullRank_sub_mem_span | exact GlobalTheory.RankStrata.exists_fullRank_sub_mem_span | (intros; apply GlobalTheory.RankStrata.exists_fullRank_sub_mem_span <;> assumption)
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RankCoinv

open GlobalTheory.SplitFlip in

theorem exists_soLoc_sub_mem_augAt : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v,
    X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) →
    ∀ t : E →ₐ[F] Fv F v, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₀ ∈ G.M'.SoLoc B.ψ t, φ - φ₀ ∈ augAt om' v := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv hν t φ hφ
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_linear_bar_good_place hP F E σ B a a' G X om om' hT v hv t
  obtain ⟨ν₀, hν₀, hf⟩ := GlobalTheory.T.exists_unramified_character_good hP F E σ B a a' G X om om' hT v hv hν t
  have hspan : Submodule.span ℂ {Z | ∃ g : GL (Fin a') (Fv F v), ∃ Ψ' ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)),
      Z = omB ν₀ ν₀ g 1 Ψ' - Ψ'} ≤ (augAt om' v ⊓ SB _).map ι := by
    rw [Submodule.span_le]
    rintro Z ⟨g₀, Ψ', hΨ', rfl⟩
    obtain ⟨φ', hφ', rfl⟩ := hι.bij.surjOn hΨ'
    obtain ⟨g, hg, hact⟩ := hf ι hι g₀
    obtain ⟨φ₁, hφ₁, hA, hE⟩ := hact φ' hφ'
    refine ⟨φ₁ - φ', ⟨Submodule.subset_span ⟨g, hg, φ', hφ', φ₁, hφ₁, hA, rfl⟩, Submodule.sub_mem _ hφ₁ hφ'⟩, ?_⟩
    simp [map_sub, hE]
  obtain ⟨Ψ₀, -, hrk, hmem⟩ := GlobalTheory.T.schwartzBruhat_full_rank_modulo_translates (Fv F v) a' (a + a') ν₀ (unifAt v)
    (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec hν₀ (ι φ) (hι.bij.mapsTo hφ)
  obtain ⟨n, ⟨hnA, hnSB⟩, hn⟩ := hspan hmem
  refine ⟨φ - n, ⟨Submodule.sub_mem _ hφ hnSB, ι, hι, fun Y hY => ?_⟩, by simpa using hnA⟩
  have : ι (φ - n) = Ψ₀ := by rw [map_sub, hn]; abel
  rw [this]; exact hrk Y hY

end GlobalTheory.RankCoinv
end

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_local_approximation : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) →
    ∀ t : E →ₐ[F] Fv F v, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₀ ∈ G.M'.SoLoc B.ψ t, φ - φ₀ ∈ augAt om' v := by
  atlas_forward_decl GlobalTheory.RankCoinv.exists_soLoc_sub_mem_augAt
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitFlip
open scoped Matrix

namespace GlobalTheory.FullRankCoinv.IndTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem Y0_mul_apply {a n : ℕ} (M : Matrix (Fin (a + n)) (Fin (a + n)) k) (i : Fin n) (j : Fin (a + n)) :
    (Y0 k n (a + n) * M) i j = M (Fin.natAdd a i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.natAdd a i)]
  · simp [Y0]
  · intro l _ hl
    have : ¬ ((l : ℕ) = a + i) := fun h => hl (Fin.ext (by simp; omega))
    simp [Y0, this]
  · simp

theorem mul_Y0_apply {a n : ℕ} (D : Matrix (Fin n) (Fin n) k) (i : Fin n) (j : Fin (a + n)) :
    (D * Y0 k n (a + n)) i j = if h : a ≤ (j : ℕ) then D i ⟨j - a, by omega⟩ else 0 := by
  split_ifs with h
  · rw [Matrix.mul_apply, Finset.sum_eq_single (⟨j - a, by omega⟩ : Fin n)]
    · simp [Y0]; omega
    · intro l _ hl
      have : ¬ ((j : ℕ) = a + l) := fun h' => hl (Fin.ext (by simp; omega))
      simp [Y0, this]
    · simp
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    have : ¬ ((j : ℕ) = a + l) := by omega
    simp [Y0, this]

theorem Y0_mul_parab {a n : ℕ} (p : parab k (GlobalTheory.RankFibre.blocks a n)) :
    Y0 k n (a + n) * (p : GL (Fin (a + n)) k).1 =
      (leviProj k (GlobalTheory.RankFibre.blocks a n) p true : GL (Fin n) k).1 * Y0 k n (a + n) := by
  ext i j
  rw [Y0_mul_apply, mul_Y0_apply]
  have hp := (mem_parab_two k).1 p.2
  split_ifs with h
  · rw [leviProj_apply]
    have e1 : GlobalTheory.RankFibre.blocks a n ⟨true, i⟩ = Fin.natAdd a i := Fin.ext (by simp [stdSum])
    have e2 : GlobalTheory.RankFibre.blocks a n ⟨true, (⟨j - a, by omega⟩ : Fin n)⟩ = j := Fin.ext (by simp [stdSum]; omega)
    rw [e1, e2]
  · have := hp i ⟨j, by omega⟩
    simpa [stdSum] using this

end GlobalTheory.FullRankCoinv.IndTwist

namespace GlobalTheory.FullRankCoinv.IndTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem parChar_eq {a n : ℕ} (ν : kˣ →* ℂˣ) (p : parab k (GlobalTheory.RankFibre.blocks a n)) :
    ((GlobalTheory.RankFibre.parChar ν ν⁻¹ a n p : ℂˣ) : ℂ) =
      apow (gdet (p : GL (Fin (a + n)) k)) ((n : ℂ) / 2) *
        ((((ν (gdet (leviProj k (GlobalTheory.RankFibre.blocks a n) p true)))⁻¹ : ℂˣ) : ℂ) *
          apow (gdet (leviProj k (GlobalTheory.RankFibre.blocks a n) p true)) (-((a + n : ℕ) : ℂ) / 2)) := by
  set A := leviProj k (GlobalTheory.RankFibre.blocks a n) p false
  set D := leviProj k (GlobalTheory.RankFibre.blocks a n) p true
  have hδ : deltaHalf k (Two (Fin a) (Fin n)) (leviProj k (GlobalTheory.RankFibre.blocks a n) p) =
      absPow k ((n : ℂ) / 2) (gdet A) * absPow k (-(a : ℂ) / 2) (gdet D) := by
    rw [← (leviTwo k (Fin a) (Fin n)).apply_symm_apply (leviProj k (GlobalTheory.RankFibre.blocks a n) p), deltaHalf_two]
    simp [A, D]
    rfl
  have hdet : gdet (p : GL (Fin (a + n)) k) = gdet A * gdet D := by
    rw [gdet, det_parab, Fintype.prod_bool, mul_comm]
  simp only [GlobalTheory.RankFibre.parChar, MonoidHom.comp_apply, MonoidHom.mul_apply, Units.val_mul, hδ]
  rw [hdet, apow_mul]
  have e : apow (gdet D) (-(a : ℂ) / 2) =
      apow (gdet D) ((n : ℂ) / 2) * apow (gdet D) (-((a + n : ℕ) : ℂ) / 2) := by
    rw [← apow_add]; congr 1; push_cast; ring
  show apow (gdet A) ((n : ℂ) / 2) * apow (gdet D) (-(a : ℂ) / 2) * (((ν * ν⁻¹) (gdet A) : ℂˣ) : ℂ) *
    ((ν⁻¹ (gdet D) : ℂˣ) : ℂ) = _
  rw [e, mul_inv_cancel]
  simp only [MonoidHom.one_apply, Units.val_one, mul_one, MonoidHom.inv_apply]
  ring

end GlobalTheory.FullRankCoinv.IndTwist

namespace GlobalTheory.FullRankCoinv.IndTwist

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def detTw (d : ℕ) (s : ℂ) : (GL (Fin d) k → ℂ) →ₗ[ℂ] (GL (Fin d) k → ℂ) where
  toFun f x := apow (gdet x) s * f x
  map_add' f g := by funext x; simp [mul_add]
  map_smul' c f := by funext x; simp; ring

theorem detTw_apply (d : ℕ) (s : ℂ) (f : GL (Fin d) k → ℂ) (x : GL (Fin d) k) :
    detTw d s f x = apow (gdet x) s * f x := rfl

theorem detTw_neg_detTw (d : ℕ) (s : ℂ) (f : GL (Fin d) k → ℂ) : detTw d (-s) (detTw d s f) = f := by
  funext x; rw [detTw_apply, detTw_apply, ← mul_assoc, ← apow_add]; simp

theorem detTw_detTw_neg (d : ℕ) (s : ℂ) (f : GL (Fin d) k → ℂ) : detTw d s (detTw d (-s) f) = f := by
  simpa using detTw_neg_detTw d (-s) f

theorem detTw_translate (d : ℕ) (s : ℂ) (f : GL (Fin d) k → ℂ) (h : GL (Fin d) k) :
    (fun x => detTw d s f (x * h)) = apow (gdet h) s • detTw d s (fun x => f (x * h)) := by
  funext x
  simp only [detTw_apply, Pi.smul_apply, smul_eq_mul, gdet_mul, apow_mul]
  ring

theorem detTw_mem_indScal {a n : ℕ} (ν : kˣ →* ℂˣ) {f : GL (Fin (a + n)) k → ℂ} (hf : f ∈ indSp k n (a + n) ν) :
    detTw (a + n) ((n : ℂ) / 2) f ∈ GlobalTheory.RankFibre.indScal ν ν⁻¹ a n := by
  obtain ⟨⟨U, hU, hfU⟩, hfl⟩ := hf
  have hK : IsSmoothChar (detChar (Fin (a + n)) (absPow k ((n : ℂ) / 2))) :=
    (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar
  have hK1 : ((detChar (Fin (a + n)) (absPow k ((n : ℂ) / 2))).ker : Set (GL (Fin (a + n)) k)) ∈ nhds 1 :=
    hK.mem_nhds (by simp)
  refine ⟨mem_smoothPart_of_nhds (Filter.mem_of_superset (Filter.inter_mem hU hK1) fun g hg => ?_), ?_⟩
  · have hg2 : apow (gdet g) ((n : ℂ) / 2) = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.1 hg.2)
      exact this
    show (fun x => detTw (a + n) ((n : ℂ) / 2) f (x * g)) = detTw (a + n) ((n : ℂ) / 2) f
    funext x
    simp only [detTw_apply, gdet_mul, apow_mul, hg2, mul_one, hfU x g hg.1]
  · intro p x
    have h := hfl p x (leviProj k (GlobalTheory.RankFibre.blocks a n) p true) (Y0_mul_parab p)
    simp only [ofChar_apply, detTw_apply, gdet_mul, apow_mul, h, parChar_eq]
    ring

end GlobalTheory.FullRankCoinv.IndTwist

namespace GlobalTheory.FullRankCoinv

open IndTwist

theorem indSp_irreducible : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
    ∀ N : Submodule ℂ (GL (Fin d) k → ℂ), N ≤ GlobalTheory.FullRankCoinv.indSp k n d ν →
      (∀ f ∈ N, ∀ h₀ : GL (Fin d) k, (fun h => f (h * h₀)) ∈ N) → N = ⊥ ∨ N = GlobalTheory.FullRankCoinv.indSp k n d ν := by
  intro P k _ _ _ _ n d ν hn hνs hνu N hN hinv
  obtain ⟨a, rfl⟩ : ∃ a, d = a + n := ⟨d - n, by omega⟩
  have hu : IsUnitaryChar ν⁻¹ := fun g => by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hνu g, inv_one]
  set s : ℂ := (n : ℂ) / 2
  let M : Submodule ℂ (GL (Fin (a + n)) k → ℂ) := N.comap (detTw (a + n) (-s))
  have hMle : M ≤ GlobalTheory.RankFibre.indScal ν ν⁻¹ a n := fun g hg => by
    have := detTw_mem_indScal ν (hN hg)
    rwa [detTw_detTw_neg] at this
  have hMinv : ∀ g ∈ M, ∀ h : GL (Fin (a + n)) k, (fun x => g (x * h)) ∈ M := fun g hg h => by
    show detTw (a + n) (-s) (fun x => g (x * h)) ∈ N
    have e : detTw (a + n) (-s) (fun x => g (x * h)) =
        apow (gdet h) s • (fun x => detTw (a + n) (-s) g (x * h)) := by
      rw [detTw_translate, smul_smul, ← apow_add]; simp
    rw [e]
    exact N.smul_mem _ (hinv _ hg h)
  have hmemM : ∀ f ∈ N, detTw (a + n) s f ∈ M := fun f hf => by
    show detTw (a + n) (-s) (detTw (a + n) s f) ∈ N
    rwa [detTw_neg_detTw]
  rcases GlobalTheory.RankFibre.indScal_irreducible P.bernsteinUnitaryProductIrreducible k a n ν ν⁻¹ hνs hνu hνs.inv hu
    M hMle hMinv with h | h
  · left
    refine (Submodule.eq_bot_iff N).2 fun f hf => ?_
    have h0 : detTw (a + n) s f = 0 := by
      have := hmemM f hf
      rw [h] at this
      exact (Submodule.mem_bot ℂ).1 this
    rw [← detTw_neg_detTw (a + n) s f, h0, map_zero]
  · right
    refine le_antisymm hN fun f hf => ?_
    have := h (detTw_mem_indScal ν hf)
    have h' : detTw (a + n) (-s) (detTw (a + n) s f) ∈ N := this
    rwa [detTw_neg_detTw] at h'

end GlobalTheory.FullRankCoinv
end
end

section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_full_rank_irreducible : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
    ∀ N : Submodule ℂ (GL (Fin d) k → ℂ), N ≤ GlobalTheory.FullRankCoinv.indSp k n d ν →
      (∀ f ∈ N, ∀ h₀ : GL (Fin d) k, (fun h => f (h * h₀)) ∈ N) → N = ⊥ ∨ N = GlobalTheory.FullRankCoinv.indSp k n d ν := by
  first | exact @GlobalTheory.FullRankCoinv.indSp_irreducible | exact GlobalTheory.FullRankCoinv.indSp_irreducible | (intros; apply GlobalTheory.FullRankCoinv.indSp_irreducible <;> assumption)
end

section
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IrrCoinvSmall

theorem fullRk_irred : GlobalTheory.FunPr.Hypotheses₂ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν →
    ∀ N : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ), GlobalTheory.FullRankCoinv.augRk n d ν ≤ N →
      N ≤ GlobalTheory.FullRankCoinv.fullRk k n d → (∀ h : GL (Fin d) k, ∀ Ψ ∈ N, (fun Y => Ψ (Y * h.1)) ∈ N) →
      N = GlobalTheory.FullRankCoinv.augRk n d ν ∨ N = GlobalTheory.FullRankCoinv.fullRk k n d := by
  intro hP k _ _ _ _ n d ν hnd hs hu N hA hNF hN
  obtain ⟨Z, hZ1, hZ2, hZ3, hZ4⟩ := GlobalTheory.T.full_rank_coinvariant_induced_iso k n d ν hnd hs
  rcases GlobalTheory.T.induced_full_rank_irreducible hP k n d ν hnd hs hu (N.map Z) (by rintro _ ⟨Ψ, hΨ, rfl⟩; exact hZ1 Ψ (hNF hΨ)) (by
    rintro _ ⟨Ψ, hΨ, rfl⟩ h₀; exact ⟨_, hN h₀ Ψ hΨ, hZ4 Ψ (hNF hΨ) h₀⟩) with hE | hE
  · left
    refine le_antisymm (fun Ψ hΨ => hZ3 Ψ (hNF hΨ) ?_) hA
    have : Z Ψ ∈ N.map Z := ⟨Ψ, hΨ, rfl⟩
    rw [hE] at this
    exact (Submodule.mem_bot ℂ).1 this
  · right
    refine le_antisymm hNF (fun Ψ hΨ => ?_)
    have : Z Ψ ∈ N.map Z := hE ▸ hZ1 Ψ hΨ
    obtain ⟨Ψ', hΨ', he⟩ := this
    have h1 : Ψ - Ψ' ∈ GlobalTheory.FullRankCoinv.augRk n d ν :=
      hZ3 _ (Submodule.sub_mem _ hΨ (hNF hΨ')) (by simp [map_sub, he])
    have := N.add_mem hΨ' (hA h1)
    rwa [add_sub_cancel] at this

theorem irr_small : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) →
    ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → Fv F v) → ℂ), augAt om' v ≤ N → N ≤ SB _ →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om' (1, h)) φ φ₁ → φ₁ ∈ N) →
      N = augAt om' v ∨ N = SB _ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv hν N hAN hNS hN
  obtain ⟨t, ι, ν₀, hs, hu, hbij, hso, hg, hh⟩ := GlobalTheory.T.exists_unramified_linear_bar_dual hP F E σ B a a' G X om om' hT v hv
  have hR := GlobalTheory.T.schwartz_bruhat_local_approximation hP F E σ B a a' G X om om' hT v hv hν t
  have haugSB : augAt om' v ≤ SB _ := Submodule.span_le.2 (by
    rintro _ ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact Submodule.sub_mem _ hφ₁ hφ)

  have hgen : GlobalTheory.FullRankCoinv.augRk a' (a + a') ν₀ ≤
      (augAt om' v).map ι ⊓ GlobalTheory.FullRankCoinv.fullRk (Fv F v) a' (a + a') := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g₀, Ψ, hΨ, rfl⟩
    obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hΨ.1
    obtain ⟨g, hgU, hg'⟩ := hg g₀
    obtain ⟨φ₁, hφ₁, hA, he⟩ := hg' φ hφ
    refine ⟨⟨φ₁ - φ, Submodule.subset_span ⟨g, hgU, φ, hφ, φ₁, hφ₁, hA, rfl⟩, by simp [map_sub, he]⟩, ?_, ?_⟩
    · rw [← he]
      exact Submodule.sub_mem _ (hbij.mapsTo hφ₁) hΨ.1
    · intro Y hY
      rw [← he]
      show ι φ₁ Y - ι φ Y = 0
      rw [he, hΨ.2 Y hY]
      simp only [GlobalTheory.FullRankCoinv.lact, sub_zero]
      rw [hΨ.2 _ (by rwa [Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by
        rw [Matrix.det_transpose]; exact (Matrix.GeneralLinearGroup.det g₀).isUnit)]), mul_zero]
  set N' := N.map ι ⊓ GlobalTheory.FullRankCoinv.fullRk (Fv F v) a' (a + a') with hN'
  have hA' : GlobalTheory.FullRankCoinv.augRk a' (a + a') ν₀ ≤ N' :=
    hgen.trans (inf_le_inf_right _ (Submodule.map_mono hAN))
  have hst : ∀ h₀ : GL (Fin (a + a')) (Fv F v), ∀ Ψ ∈ N', (fun Y => Ψ (Y * h₀.1)) ∈ N' := by
    rintro h₀ _ ⟨⟨φ, hφN, rfl⟩, hΨ⟩
    obtain ⟨h, hhU, c, hc, hh'⟩ := hh h₀
    obtain ⟨φ₁, hφ₁, hA, he⟩ := hh' φ (hNS hφN)
    have h1 : (fun Y => ι φ (Y * h₀.1)) = c⁻¹ • ι φ₁ := by
      rw [he]; funext Y; simp [hc]
    refine ⟨⟨c⁻¹ • φ₁, N.smul_mem _ (hN h hhU φ hφN φ₁ hφ₁ hA), by rw [map_smul, h1]⟩, ?_, ?_⟩
    · rw [h1]; exact Submodule.smul_mem _ _ (hbij.mapsTo hφ₁)
    · intro Y hY
      exact hΨ.2 _ (by rwa [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.GeneralLinearGroup.det h₀).isUnit])
  have hinj : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ι φ = ι φ' → φ = φ' := fun φ hφ φ' hφ' e => hbij.injOn hφ hφ' e
  have hloc : ∀ φ₀ ∈ G.M'.SoLoc B.ψ t, ι φ₀ ∈ GlobalTheory.FullRankCoinv.fullRk (Fv F v) a' (a + a') :=
    fun φ₀ h0 => ⟨hbij.mapsTo h0.1, (hso φ₀ h0.1).1 h0⟩
  rcases fullRk_irred hP (Fv F v) a' (a + a') ν₀ (by omega) hs hu N' hA' inf_le_right hst with hE | hE
  · left
    refine le_antisymm (fun φ hφN => ?_) hAN
    obtain ⟨φ₀, h0, hd⟩ := hR φ (hNS hφN)
    have h0N : φ₀ ∈ N := by
      have := N.sub_mem hφN (hAN hd); rwa [sub_sub_cancel] at this
    have h1 : ι φ₀ ∈ GlobalTheory.FullRankCoinv.augRk a' (a + a') ν₀ := hE ▸ ⟨⟨φ₀, h0N, rfl⟩, hloc φ₀ h0⟩
    obtain ⟨⟨w, hw, hwe⟩, -⟩ := hgen h1
    have : w = φ₀ := hinj w (haugSB hw) φ₀ h0.1 hwe
    subst this
    have := (augAt om' v).add_mem hw hd
    rwa [add_sub_cancel] at this
  · right
    refine le_antisymm hNS (fun φ hφ => ?_)
    obtain ⟨φ₀, h0, hd⟩ := hR φ hφ
    have h1 : ι φ₀ ∈ N' := hE ▸ hloc φ₀ h0
    obtain ⟨⟨φ', hφ'N, he⟩, -⟩ := h1
    have : φ' = φ₀ := hinj φ' (hNS hφ'N) φ₀ h0.1 he
    subst this
    have := N.add_mem hφ'N (hAN hd)
    rwa [add_sub_cancel] at this

end GlobalTheory.IrrCoinvSmall
end

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.augmentation_submodule_second_factor : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) →
    ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → Fv F v) → ℂ), augAt om' v ≤ N → N ≤ SB _ →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om' (1, h)) φ φ₁ → φ₁ ∈ N) →
      N = augAt om' v ∨ N = SB _ := by
  atlas_forward_decl GlobalTheory.IrrCoinvSmall.irr_small
end
