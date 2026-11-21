import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityFiniteOfUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearGLTransposeMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartStackDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartBoundedCoefficients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartShearInvariance
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroMinorOfRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatPartitionOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatReindexRows
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanCharacterTranslatesCoinvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearWittModelLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWittModelUnitaryActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryMatrixSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConductStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieDerivativePolynomialFockArchimedeanUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryPreservesPolynomialFockStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianKernel

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_maps_gaussian_identity : GlobalTheory.Published.HoweDualityFinite →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, IsEmpty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSub om' v (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), GlobalTheory.Published.ThetaSub om' v N →
        N ≠ GlobalTheory.WeilM.SB _ → ∀ φ ∈ N, Rf.p' v φ = 0 := by
  first | exact @GlobalTheory.HoweNonsplitKerSmall.howe_nonsplit_ker_small | exact GlobalTheory.HoweNonsplitKerSmall.howe_nonsplit_ker_small | (intros; apply GlobalTheory.HoweNonsplitKerSmall.howe_nonsplit_ker_small <;> assumption)
end

section
open GlobalTheory.WeilM Matrix

noncomputable section

namespace GlobalTheory.SmallRankCoinv
open GlobalTheory.SplitFlip GlobalTheory.LocMod.Inhab ValuativeRel GlobalTheory.RankChart GlobalTheory.RankStrata

theorem card_box_quot_le {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (T R : Type) [Fintype T] [DecidableEq T] [Fintype R] [DecidableEq R] {ϖ : kˣ} (hϖ : IsUnif ϖ) (a : kˣ) :
    Nat.card (box T R (ϖ⁻¹ * a) ⧸ (box T R a).addSubgroupOf (box T R (ϖ⁻¹ * a))) ≤
      GlobalTheory.SplitWeil.resCard k ^ (Fintype.card T * Fintype.card R) := by
  have hb : 0 < valuation k ((ϖ⁻¹ * a : kˣ) : k) := zero_lt_iff.2 (by simp)
  have hv0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  have ha0 : 0 < valuation k (a : k) := zero_lt_iff.2 (by simp)
  have hint : ∀ (x : box T R (ϖ⁻¹ * a)) r q, x.1 r q / ((ϖ⁻¹ * a : kˣ) : k) ∈ 𝒪[k] := fun x r q => by
    rw [Valuation.mem_integer_iff, map_div₀, div_le_one₀ hb]
    exact x.2 r q
  let φ : box T R (ϖ⁻¹ * a) →+ (T → R → 𝓀[k]) :=
    { toFun := fun x r q => IsLocalRing.residue 𝒪[k] ⟨_, hint x r q⟩
      map_zero' := by
        funext r q
        rw [Pi.zero_apply, Pi.zero_apply, ← map_zero (IsLocalRing.residue 𝒪[k])]
        congr 1
        exact Subtype.ext (by simp)
      map_add' := fun x y => by
        funext r q
        rw [Pi.add_apply, Pi.add_apply, ← map_add]
        congr 1
        exact Subtype.ext (by simp [add_div]) }
  have hker : φ.ker ≤ (box T R a).addSubgroupOf (box T R (ϖ⁻¹ * a)) := by
    intro x hx
    rw [AddSubgroup.mem_addSubgroupOf]
    intro r q
    have h1 : IsLocalRing.residue 𝒪[k] ⟨_, hint x r q⟩ = 0 := congrFun (congrFun hx r) q
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one] at h1
    have h2 : valuation k (x.1 r q / ((ϖ⁻¹ * a : kˣ) : k)) ≤ valuation k (ϖ : k) := by
      rw [hϖ, le_uniformizer_iff]; exact h1
    rw [map_div₀, div_le_iff₀ hb, ← map_mul, ← Units.val_mul, mul_inv_cancel_left] at h2
    exact h2
  have h1 : Nat.card (box T R (ϖ⁻¹ * a) ⧸ φ.ker) ≤ Nat.card (T → R → 𝓀[k]) :=
    Nat.card_le_card_of_injective _ (QuotientAddGroup.kerLift_injective φ)
  haveI : Finite (box T R (ϖ⁻¹ * a) ⧸ φ.ker) := Finite.of_injective _ (QuotientAddGroup.kerLift_injective φ)
  have h2 := Nat.le_of_dvd Nat.card_pos (AddSubgroup.index_dvd_of_le hker)
  refine h2.trans (h1.trans_eq ?_)
  simp only [Nat.card_fun, Nat.card_eq_fintype_card, GlobalTheory.SplitWeil.resCard, ← pow_mul, mul_comm]

theorem norm_scalar_lt_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ϖ : kˣ} (hϖ : IsUnif ϖ) {z : ℂ} (hz : ‖z‖ = 1) {t r d c : ℕ} (ht : 0 < t) (hrd : 2 * r < d)
    (hc : c ≤ GlobalTheory.SplitWeil.resCard k ^ (t * r)) : ‖z ^ t * apow (ϖ ^ t) ((d : ℂ) / 2) * (c : ℂ)‖ < 1 := by
  have hq : (1 : ℝ) < GlobalTheory.SplitWeil.resCard k := by exact_mod_cast (Finite.one_lt_card : 1 < Nat.card 𝓀[k])
  have hn : GlobalTheory.SplitWeil.nabs k (ϖ ^ t) = ((GlobalTheory.SplitWeil.resCard k : ℝ)⁻¹) ^ t := by
    rw [← GlobalTheory.GLDoubling.nabs_unif hϖ]
    simp [GlobalTheory.SplitWeil.nabs]
  set q : ℝ := (GlobalTheory.SplitWeil.resCard k : ℝ) with hqd
  have hq0 : 0 < q := by linarith
  have e : ‖apow (ϖ ^ t) ((d : ℂ) / 2)‖ = q ^ (-((t : ℝ) * (d / 2))) := by
    rw [apow, Complex.norm_cpow_eq_rpow_re_of_pos (GlobalTheory.SplitWeil.Model.nabs_pos _), hn, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity), Real.inv_rpow hq0.le, ← Real.rpow_neg hq0.le]
    simp
  rw [norm_mul, norm_mul, norm_pow, hz, one_pow, one_mul, e, Complex.norm_natCast]
  have hc' : (c : ℝ) ≤ q ^ ((t : ℝ) * r) := by
    rw [← Nat.cast_mul, Real.rpow_natCast, hqd]; exact_mod_cast hc
  calc _ ≤ q ^ (-((t : ℝ) * (d / 2))) * q ^ ((t : ℝ) * r) := by gcongr
    _ = q ^ (-((t : ℝ) * (d / 2)) + t * r) := (Real.rpow_add hq0 _ _).symm
    _ < 1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg hq
      have h1 : (2 * r : ℝ) < d := by exact_mod_cast hrd
      have h2 : (0 : ℝ) < t := by exact_mod_cast ht
      nlinarith

theorem chart_eq_of_rank_le : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D] [Nonempty T] (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ‖(ν ϖ : ℂ)‖ = 1 → 2 * Fintype.card R < Fintype.card D → ∀ (τ : R → D), ∀ f ∈ SB (Matrix (R ⊕ T) D k), (∀ Y : Matrix (R ⊕ T) D k, f Y ≠ 0 → (Y.submatrix Sum.inl τ).det ≠ 0) → ∃ Φ ∈ GlobalTheory.RankStrata.Nsp k (R ⊕ T) D ν, ∀ Y : Matrix (R ⊕ T) D k, Y.rank ≤ Fintype.card R → Φ Y = f Y := by
  intro k _ _ _ _ R T D _ _ _ _ _ _ _ ν ϖ hϖ hν hRD τ f hf hsupp
  classical
  obtain ⟨a, ha⟩ := GlobalTheory.RankChart.bounded_coeff_of_SB k R T D τ f hf hsupp
  obtain ⟨b, hb⟩ := GlobalTheory.RankChart.sb_shear_invariant k R T D f hf
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
  have hcard := card_box_quot_le T R hϖ a
  generalize hH : box T R a = H at ha hHH' hdilmem hcard
  generalize hH' : box T R (ϖ⁻¹ * a) = H' at hHH' hdilmem hcard
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
    · obtain ⟨C, hC⟩ := GlobalTheory.RankChart.exists_eq_stack k R T D τ Y hY hd
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
    rw [Nat.card_eq_fintype_card] at hcard
    have hlt := norm_scalar_lt_one hϖ hν (Fintype.card_pos (α := T)) hRD hcard
    rw [← hlam] at hlt
    intro h
    rw [← sub_eq_zero.1 h, norm_one] at hlt
    exact lt_irrefl _ hlt
  refine ⟨(Fintype.card (H ⧸ L.addSubgroupOf H) : ℂ)⁻¹ •
      ((1 - lam * Fintype.card (H' ⧸ H.addSubgroupOf H'))⁻¹ • n₁ - n₀),
    Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hn₁) hn₀), fun Y hY => ?_⟩
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hn₁val Y hY, hn₀val]
  field_simp
  ring

theorem exists_fullRank_sub_mem : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ‖(ν ϖ : ℂ)‖ = 1 → 2 * n ≤ d + 1 →
    ∀ Ψ ∈ SB (Matrix (Fin n) (Fin d) k), ∃ Ψ₀ ∈ SB (Matrix (Fin n) (Fin d) k), (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≠ n → Ψ₀ Y = 0) ∧
      Ψ - Ψ₀ ∈ Submodule.span ℂ {Z | ∃ g : GL (Fin n) k, ∃ Ψ' ∈ SB (Matrix (Fin n) (Fin d) k), Z = GlobalTheory.SplitFlip.omB ν ν g 1 Ψ' - Ψ'} := by
  intro k _ _ _ _ n d ν ϖ hϖ hν hnd Ψ hΨ
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
    have hT := GlobalTheory.RankStrata.rowRenum_SB_Nsp k (Fin ρ ⊕ ↥(Set.range S)ᶜ) (Fin n) (Fin d) ν e'
    obtain ⟨Φ', hΦ', hΦ'f⟩ := chart_eq_of_rank_le k (Fin ρ) (↥(Set.range S)ᶜ) (Fin d) ν ϖ hϖ hν (by simp only [Fintype.card_fin]; omega) τ
      (fun Z => f (Z.submatrix e'.symm id)) (hT.1 f hf) (fun Z hZ => by
        have := hS _ hZ
        rwa [Matrix.submatrix_submatrix, show (e'.symm ∘ S) = Sum.inl from funext he'] at this)
    have hT2 := GlobalTheory.RankStrata.rowRenum_SB_Nsp k (Fin n) (Fin ρ ⊕ ↥(Set.range S)ᶜ) (Fin d) ν e'.symm
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
    have hsp := GlobalTheory.CoverSB.mem_span_of_cover k (Fin n) (Fin d) ((Fin ρ → Fin n) × (Fin ρ → Fin d))
      (fun i => {Y : Matrix (Fin n) (Fin d) k | (Y.submatrix i.1 i.2).det ≠ 0})
      (fun i => isOpen_ne_fun ((continuous_id.matrix_submatrix i.1 i.2).matrix_det) continuous_const) g hg
      (fun Y hY => by
        have : ρ ≤ Y.rank := by
          by_contra h
          exact hY (hg0 Y (by omega))
        obtain ⟨S, τ, h⟩ := GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank k _ _ ρ Y this
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

end GlobalTheory.SmallRankCoinv

end
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweSplitSmall

section Local

open GlobalTheory.SplitFlip

theorem eq_coinv_or_eq_top (HB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible)
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}
    (hnd : 2 * n ≤ d + 1) {ν β : kˣ →* ℂˣ} (hν : IsSmU ν) (hβ : IsSmU β)
    (C N : Submodule ℂ (Matrix (Fin n) (Fin d) k → ℂ))
    (hC : C = Submodule.span ℂ {z | ∃ (g : GL (Fin n) k) (Ψ : Matrix (Fin n) (Fin d) k → ℂ),
        Ψ ∈ SB (Matrix (Fin n) (Fin d) k) ∧ z = omA ν β g 1 Ψ - Ψ})
    (hCN : C ≤ N) (hN : N ≤ SB (Matrix (Fin n) (Fin d) k))
    (hst : ∀ (h : GL (Fin d) k), ∀ Ψ ∈ N, omA ν β 1 h Ψ ∈ N) :
    N ≤ C ∨ SB (Matrix (Fin n) (Fin d) k) ≤ N := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (k := k)
  have dec : ∀ Ψ ∈ SB (Matrix (Fin n) (Fin d) k), ∃ Ψ₀ ∈ SB (Matrix (Fin n) (Fin d) k),
      (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≠ n → Ψ₀ Y = 0) ∧ Ψ - Ψ₀ ∈ C := by
    intro Ψ hΨ
    obtain ⟨Ψ₀, h1, h2, h3⟩ := GlobalTheory.SmallRankCoinv.exists_fullRank_sub_mem k n d ν ϖ hϖ (hν.2 ϖ) hnd Ψ hΨ
    refine ⟨Ψ₀, h1, h2, ?_⟩
    rw [hC]
    refine Submodule.span_mono ?_ h3
    rintro _ ⟨g, Ψ', hΨ', rfl⟩
    refine ⟨invT g, Ψ', hΨ', ?_⟩
    congr 1
    funext Y
    simp only [omA, omB, map_one, Units.val_one, Matrix.mul_one, mul_one, apow_one, invT_inv_val, gdet_invT, map_inv,
      inv_inv, apow_inv, neg_div, neg_neg]
  rcases GlobalTheory.T.span_character_translates_coinvariant HB k n d (by omega) ν β hν.1 hν.2 hβ.1 hβ.2 N (hC ▸ hCN) hN hst with h | h
  · left
    intro Ψ hΨ
    obtain ⟨Ψ₀, -, h2, h3⟩ := dec Ψ (hN hΨ)
    have h4 : Ψ₀ ∈ N := by simpa using N.sub_mem hΨ (hCN h3)
    have h5 : Ψ₀ ∈ C := hC ▸ h Ψ₀ h4 h2
    simpa using C.add_mem h3 h5
  · right
    intro Ψ hΨ
    obtain ⟨Ψ₀, h1, h2, h3⟩ := dec Ψ hΨ
    simpa using N.add_mem (hCN h3) (h Ψ₀ h1 h2)

theorem isSmU_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ν : kˣ →* ℂˣ} (h : IsSmU ν) : IsSmU ν⁻¹ := by
  refine ⟨Subgroup.isOpen_mono (H₁ := ν.ker) (fun x hx => ?_) h.1, fun x => ?_⟩
  · rw [MonoidHom.mem_ker, MonoidHom.inv_apply, hx, inv_one]
  · rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, h.2, inv_one]

end Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

omit [NumberField E] in

theorem one_mem_UAt {n : ℕ} (Y : Spc F E n) (v : Pl F) : (1 : UA σ Y.J) ∈ UAt σ Y (evFin F v) := fun u _ => by
  rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero]

theorem surj_herm {B : Base F E} {n r s : ℕ} {X : Spc F E n} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) {v : Pl F}
    (t : E →ₐ[F] Fv F v) (g : GL (Fin n) (Fv F v)) : ∃ x ∈ UAt σ X (evFin F v), locMat t 1 x = g := by
  have hJ : IsUnit (X.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := GlobalTheory.LeviAtPlace.det_ne_zero_of_sig (hX.sig (InfinitePlace.mk φ))
    have h1 : X.J.det ≠ 0 := fun e => h0 (by
      rw [show X.J.map _ = RingHom.mapMatrix _ X.J from rfl, ← RingHom.map_det, e, map_zero])
    rw [show X.J.map t = (t : E →+* Fv F v).mapMatrix X.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  refine ⟨GlobalTheory.LeviAtPlace.leviHom hB.cm t X.J hJ hX.herm g, GlobalTheory.LeviAtPlace.lift_sub_one_at v _, Units.ext ?_⟩
  rw [locMat_val, GlobalTheory.LeviAtPlace.leviHom_map_piW, GlobalTheory.LeviAtPlace.locMat, GlobalTheory.LeviAtPlace.pairMat_fst]
  simp

theorem thetaSub_eq (hP : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (P : IsPair B M χX χW om r s r' s') (hnd : 2 * n ≤ d + 1)
    {v : Pl F} (t : E →ₐ[F] Fv F v) {N : Submodule ℂ ((Fin n × Fin d → Fv F v) → ℂ)} (hN : GlobalTheory.Published.ThetaSub om v N) :
    N = augAt om v ∨ N = SB _ := by
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_linear_witt_model_local hP F E σ B n d X W M χX χW om r s r' s' P v t 1 1
  have act := GlobalTheory.T.linear_witt_model_unitary_action hP F E σ B n d X W M χX χW om r s r' s' P v t 1 1 ι hι
  have hex := (GlobalTheory.T.theta_action_exists hP F E σ B n d X W M χX χW om r s r' s' P v).1
  have hb := Model.IsLin.bij hι
  have hν := isSmU_inv (GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E χW P.hW v t).1
  have hβ := (GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E χX P.hX v t).1
  have haug : augAt om v ≤ SB _ := hN.1.trans hN.2.1
  have pull : ∀ Q : Submodule ℂ ((Fin n × Fin d → Fv F v) → ℂ), Q ≤ SB _ → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ι φ ∈ Q.map ι → φ ∈ Q := by
    rintro Q hQ φ hφ ⟨ψ, hψ, e⟩
    rw [← hb.injOn (hQ hψ) hφ e]
    exact hψ
  have hC : Submodule.span ℂ {z | ∃ (g : GL (Fin n) (Fv F v)) (Ψ : Matrix (Fin n) (Fin d) (Fv F v) → ℂ),
      Ψ ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)) ∧
        z = GlobalTheory.SplitFlip.omA (chrW χW t)⁻¹ (chrW χX t) g 1 Ψ - Ψ} ≤ (augAt om v).map ι := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, Ψ, hΨ, rfl⟩
    obtain ⟨φ, hφ, rfl⟩ := hb.surjOn hΨ
    obtain ⟨x, hx, rfl⟩ := surj_herm P.base P.herm t g
    obtain ⟨φ₁, ⟨h1, H⟩, -⟩ := hex x hx 1 (one_mem_UAt _ v) φ hφ
    refine ⟨φ₁ - φ, Submodule.subset_span ⟨x, hx, φ, hφ, φ₁, h1, H, rfl⟩, ?_⟩
    rw [map_sub, act x hx 1 (one_mem_UAt _ v) φ hφ φ₁ h1 H, map_one]
  rcases eq_coinv_or_eq_top hP.bernsteinUnitaryProductIrreducible hnd hν hβ _ (N.map ι) rfl
    (hC.trans (Submodule.map_mono hN.1)) (by rintro _ ⟨φ, hφ, rfl⟩; exact hb.mapsTo (hN.2.1 hφ)) (by
      rintro h _ ⟨φ, hφ, rfl⟩
      obtain ⟨x, hx, rfl⟩ := GlobalTheory.T.local_unitary_matrix_surjective F E σ B d W r' s' P.base P.skew v t 1 h
      obtain ⟨φ₁, ⟨h1, H⟩, -⟩ := hex 1 (one_mem_UAt _ v) x hx φ (hN.2.1 hφ)
      refine ⟨φ₁, hN.2.2 x hx φ hφ φ₁ h1 H, ?_⟩
      rw [act 1 (one_mem_UAt _ v) x hx φ (hN.2.1 hφ) φ₁ h1 H, map_one]) with h | h
  · exact Or.inl (le_antisymm (fun φ hφ => pull _ haug φ (hN.2.1 hφ) (hC (h ⟨φ, hφ, rfl⟩))) hN.1)
  · exact Or.inr (le_antisymm hN.2.1 fun φ hφ => pull _ hN.2.1 φ hφ (h (hb.mapsTo hφ)))

theorem isHecke_div {χ₁ χ₂ : Chr F E} (h₁ : IsHecke F E χ₁) (h₂ : IsHecke F E χ₂) : IsHecke F E (χ₁ / χ₂) := by
  refine ⟨?_, fun x => ?_⟩
  · show Continuous fun x => χ₁ x / χ₂ x
    exact h₁.1.div' h₂.1
  · rw [MonoidHom.div_apply, h₁.2 x, h₂.2 x, div_one]

theorem resEtaPow_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E}
    {m m' : ℕ} (h : ResEtaPow K χ m) (h' : ResEtaPow K χ' m') : ResEtaPow K (χ / χ') (m + m') := by
  intro u
  rw [MonoidHom.div_apply, Circle.coe_div, h u, h' u]
  split_ifs
  · simp
  · rw [div_eq_mul_inv, ← inv_pow, inv_neg_one, ← pow_add]

theorem isPair_small {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, isHecke_div h.chars.heckeα h.chars.heckeβ, h.chars.resα,
    add_comm a' a ▸ resEtaPow_div h.chars.resα h.chars.resβ, h.weil'⟩

theorem howe_split_ker_small : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.MinguezThetaGL →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, Nonempty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSub om' v (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), GlobalTheory.Published.ThetaSub om' v N →
        N ≠ GlobalTheory.WeilM.SB _ → ∀ φ ∈ N, Rf.p' v φ = 0 := by
  intro hP _ F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM v ⟨t⟩
  have hlt := hM.triple.geo.lt
  have key := fun N hN => thetaSub_eq (N := N) hP (isPair_small hM.triple) (by omega) t hN
  refine ⟨⟨2, fun m N hmono hN => ?_⟩, fun N hN hne φ hφ => ?_⟩
  · by_contra hm
    have h01 : N ⟨0, by omega⟩ < N ⟨1, by omega⟩ := hmono (by simp [Fin.lt_def])
    have h12 : N ⟨1, by omega⟩ < N ⟨2, by omega⟩ := hmono (by simp [Fin.lt_def])
    rcases key _ (hN ⟨1, by omega⟩) with h | h
    · exact absurd (h ▸ (hN _).1.trans_lt h01 : augAt om' v < augAt om' v) (lt_irrefl _)
    · exact absurd (h12.trans_le (hN _).2.1) (h ▸ lt_irrefl _)
  · rcases key N hN with h | h
    · exact hM.fin.inv' v (h ▸ hφ)
    · exact absurd h hne

end GlobalTheory.HoweSplitSmall

end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_maps_gaussian_sum : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.MinguezThetaGL →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, Nonempty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSub om' v (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), GlobalTheory.Published.ThetaSub om' v N →
        N ≠ GlobalTheory.WeilM.SB _ → ∀ φ ∈ N, Rf.p' v φ = 0 := by
  atlas_forward_decl GlobalTheory.HoweSplitSmall.howe_split_ker_small
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

noncomputable section

namespace GlobalTheory.HoweRealSmall

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

private theorem det_ne_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
  have h2 : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro h0
  apply h2
  rw [Matrix.det_mul, Matrix.det_mul, h0]; simp

private theorem det_ne_sig_map {E : Type} [Field E] {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (τ : E →+* ℂ) (c : ℂ)
    (h : HasSig (c • J.map τ) r s) : J.det ≠ 0 := by
  intro h0
  apply det_ne_hasSig h
  have e := RingHom.map_det τ J
  rw [RingHom.mapMatrix_apply] at e
  rw [Matrix.det_smul, ← e, h0, map_zero, mul_zero]

private theorem hecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

private theorem resEta_div {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

private theorem acts_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : Module.End ℂ ((κ → AF F) → ℂ)) :
    Acts (evI F) ⇑T ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  rw [e, map_zero]

private theorem actsD_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (T : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) :
    ActsD (evI F) (fun t => ⇑(T t)) ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _ x
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  simp only [e, map_zero, Pi.zero_apply]
  exact hasDerivAt_const _ _

theorem howe_real_ker' : GlobalTheory.Published.HoweDualityReal →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' N →
        N ≠ G.M'.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p' f = 0 := by
  intro hHD F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM
  have hT := hM.triple
  have hg := hT.geo
  have hc := hT.chars
  have hR := hM.real
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have dV' : G.V'.J.det ≠ 0 := det_ne_sig_map (Bs.emb w₀).1 1 (by rw [one_smul]; exact hg.hV'.sig w₀)
  have dW : G.W.J.det ≠ 0 := det_ne_sig_map (Bs.emb w₀).1 Complex.I (hg.hW.sig w₀)
  have hres := resEta_div hc.resα hc.resβ (Nat.add_comm a a')
  have hhk := hecke_div hc.heckeα hc.heckeβ
  obtain ⟨hbdd, hsum⟩ := hHD F E σ hT.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hT.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hT.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  have hLie := GlobalTheory.T.lieDerivative_polynomialFock_archimedeanUnitary F E σ hT.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hT.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hT.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  have hCpt := GlobalTheory.T.compactUnitary_preserves_polynomialFock F E σ hT.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hT.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hT.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  refine ⟨hbdd, ?_⟩
  intro N hN hNe φ hφ
  set K : Submodule ℂ (SInf F (Fin a' × Fin (a + a'))) := LinearMap.ker R.p' ⊓ G.M'.Pol Bs.ψ Bs.emb with hKdef
  have hK : GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' K := by
    refine ⟨inf_le_right, ?_, ?_, ?_, ?_⟩
    · intro γ hγ f hf f₁ hact
      exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (hR.quot'.lie γ hγ f hf f₁ hact), hN.1 (hN.2.1 γ hγ f hf f₁ hact)⟩
    · intro k hk f hf f₁ hact
      refine Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 ?_, hN.1 (hN.2.2.1 k hk f hf f₁ hact)⟩
      rw [map_sub, hR.quot'.cpt k hk f hf f₁ hact, sub_self]
    · intro γ hγ f hf f₁ hact
      have hf' := Submodule.mem_inf.1 hf
      have hp := hR.lie γ hγ 0 (zero_mem _) f hf'.2 0 f₁
        (actsD_zero (fun t => om (1, γ (Multiplicative.ofAdd t)))) hact
        (by rw [map_zero]; exact (LinearMap.mem_ker.1 hf'.1).symm)
      rw [map_zero] at hp
      exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 hp.symm, (hLie γ hγ f hf'.2).2 f₁ hact⟩
    · intro k hk f hf f₁ hact
      have hf' := Submodule.mem_inf.1 hf
      have hp := hR.cpt k hk 0 (zero_mem _) f hf'.2 0 f₁ (acts_zero _) hact
        (by rw [map_zero]; exact (LinearMap.mem_ker.1 hf'.1).symm)
      rw [map_zero] at hp
      exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 hp.symm, (hCpt k hk f hf'.2).2 f₁ hact⟩
  have hKne : K ≠ G.M'.Pol Bs.ψ Bs.emb := by
    intro hKe
    have hbot : (G.M'.Pol Bs.ψ Bs.emb).map R.p' = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro _ ⟨f, hf, rfl⟩
      rw [← hKe] at hf
      exact LinearMap.mem_ker.1 (Submodule.mem_inf.1 hf).1
    rw [hR.quot'.onto] at hbot
    haveI := hR.nontriv
    exact top_ne_bot hbot
  have hNK : N ⊔ K ≠ G.M'.Pol Bs.ψ Bs.emb := hsum N K hN hK hNe hKne
  rcases hR.irred (N.map R.p') (by
    intro γ hγ f hf f₁ hact hpm
    obtain ⟨n, hn, hpn⟩ := Submodule.mem_map.1 hpm
    obtain ⟨n₁, hactn⟩ := (hLie γ hγ n (hN.1 hn)).1
    rw [hR.lie γ hγ f hf n (hN.1 hn) f₁ n₁ hact hactn hpn.symm]
    exact Submodule.mem_map_of_mem (hN.2.2.2.1 γ hγ n hn n₁ hactn)) (by
    intro k hk f hf f₁ hact hpm
    obtain ⟨n, hn, hpn⟩ := Submodule.mem_map.1 hpm
    obtain ⟨n₁, hactn⟩ := (hCpt k hk n (hN.1 hn)).1
    rw [hR.cpt k hk f hf n (hN.1 hn) f₁ n₁ hact hactn hpn.symm]
    exact Submodule.mem_map_of_mem (hN.2.2.2.2 k hk n hn n₁ hactn)) with h0 | htop
  · have hmem : R.p' φ ∈ N.map R.p' := Submodule.mem_map_of_mem hφ
    rw [h0] at hmem
    exact (Submodule.mem_bot ℂ).1 hmem
  · exfalso
    apply hNK
    refine le_antisymm (sup_le hN.1 inf_le_right) ?_
    intro f hf
    have hm : R.p' f ∈ N.map R.p' := by rw [htop]; exact Submodule.mem_top
    obtain ⟨n, hn, hpn⟩ := Submodule.mem_map.1 hm
    have hk : f - n ∈ K :=
      Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (by rw [map_sub, hpn, sub_self]), sub_mem hf (hN.1 hn)⟩
    have := Submodule.add_mem_sup hn hk
    rwa [add_sub_cancel] at this

end GlobalTheory.HoweRealSmall

end
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeDuality_realPlaces_trivialChar_fockLift_smallPair : GlobalTheory.Published.HoweDualityReal →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' N →
        N ≠ G.M'.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p' f = 0 := by
  atlas_forward_decl GlobalTheory.HoweRealSmall.howe_real_ker'
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_maps_gaussian_kernel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    (∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSub om' v (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), GlobalTheory.Published.ThetaSub om' v N →
        N ≠ GlobalTheory.WeilM.SB _ → ∀ φ ∈ N, Rf.p' v φ = 0) →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' N →
        N ≠ G.M'.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p' f = 0) →
    ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ), GlobalTheory.SquareAgree.IsThetaSubG G.M' Bs.ψ Bs.emb om' N →
      N ≠ GlobalTheory.SquareAgree.algD G.M' Bs.ψ Bs.emb → ∀ Φ ∈ N, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf 0 Φ := by
  first | exact @GlobalTheory.HoweGlobalPair.allInKer | exact GlobalTheory.HoweGlobalPair.allInKer | (intros; apply GlobalTheory.HoweGlobalPair.allInKer <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree

theorem polMatch_zero_of_thetaSubG : GlobalTheory.Published.HoweDualityUnitary → GlobalTheory.Published.HoweDualityReal → GlobalTheory.Published.MinguezThetaGL → GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ), IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N →
      N ≠ algD Γ.M' Bs.ψ Bs.emb → ∀ Φ ∈ N, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ := by
  intro hU hR hMg hP F E _ _ _ _ _ σ a a' Bs Γ Xc om om' R Rf hM N hN hne Φ hΦ
  have hFin := GlobalTheory.T.howe_duality_finite_of_unitary hP hU
  refine GlobalTheory.T.matched_maps_gaussian_kernel F E σ Bs a a' Γ Xc om om' R Rf hM (fun v => ?_)
    (GlobalTheory.T.howeDuality_realPlaces_trivialChar_fockLift_smallPair hR F E σ Bs a a' Γ Xc om om' R Rf hM) N hN hne Φ hΦ
  rcases isEmpty_or_nonempty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) with h | h
  · exact GlobalTheory.T.matched_maps_gaussian_identity hFin F E σ Bs a a' Γ Xc om om' R Rf hM v h
  · exact GlobalTheory.T.matched_maps_gaussian_sum hP hMg F E σ Bs a a' Γ Xc om om' R Rf hM v h

end GlobalTheory.SquareAgree
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_maps_real_finite : GlobalTheory.Published.HoweDualityUnitary → GlobalTheory.Published.HoweDualityReal → GlobalTheory.Published.MinguezThetaGL → GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ), IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N →
      N ≠ algD Γ.M' Bs.ψ Bs.emb → ∀ Φ ∈ N, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf 0 Φ := by
  atlas_forward_decl GlobalTheory.SquareAgree.polMatch_zero_of_thetaSubG
end
