import Development.WeilBound.CoreStatements.ThetaDilations.SqPosOfNe
import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureLinearChange
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilRepresentationQuadraticDatumStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IwasawaDecompositionAdelicSL2
import Development.WeilBound.CoreStatements.ThetaDilations.ProdRho
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ReductionToSiegelDomain
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionModularity
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionAutomorphy
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionCuspExpansion
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaAverageIntegralFormula
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionGrowthBound
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RealQuadraticFormLemmaStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchurFunctionSmoothRightInvariantStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SchurFunctionWhittakerEquivariant
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.QuadraticLevelSetDensity

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]

theorem oh_mul {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x * y ∈ Oh F := fun v => mul_mem (hx v) (hy v)

theorem oh_nat (N : ℕ) : (N : A F) ∈ Oh F := by
  induction N with
  | zero => exact fun v => by rw [Nat.cast_zero]; exact zero_mem _
  | succ n ih => exact fun v => by rw [Nat.cast_succ]; exact add_mem (ih v) (one_mem _)

def LN (F ι : Type) [Field F] [NumberField F] (N : ℕ) : AddSubgroup (ι → A F) where
  carrier := {x | ∀ i, ∃ y ∈ Oh F, x i = (N : A F) * y}
  zero_mem' := fun _ => ⟨0, fun _ => zero_mem _, (mul_zero _).symm⟩
  add_mem' := fun ha hb i => by
    obtain ⟨y, hy, e⟩ := ha i
    obtain ⟨y', hy', e'⟩ := hb i
    exact ⟨y + y', fun v => add_mem (hy v) (hy' v), by rw [Pi.add_apply, e, e', mul_add]⟩
  neg_mem' := fun ha i => by
    obtain ⟨y, hy, e⟩ := ha i
    exact ⟨-y, fun v => neg_mem (hy v), by rw [Pi.neg_apply, e, mul_neg]⟩

theorem co_LN {N : ℕ} (hN : 0 < N) : CO (LN F ι N) := by
  obtain ⟨-, -, -, h1, -, -, -, -, -, h2⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have e : (LN F ι N : Set (ι → A F)) = Set.univ.pi fun _ => (fun y => (N : A F) * y) '' Oh F := by
    ext x
    exact ⟨fun h i _ => (h i).imp fun y hy => ⟨hy.1, hy.2.symm⟩, fun h i => (h i trivial).imp fun y hy => ⟨hy.1, hy.2.symm⟩⟩
  refine ⟨e ▸ isCompact_univ_pi fun _ => h1.image (continuous_const.mul continuous_id), ?_⟩
  have e' : (LN F ι N : Set (ι → A F)) = ⋂ i, (fun x => x i) ⁻¹' {x : A F | ∃ y ∈ Oh F, x = (N : A F) * y} := by
    ext x; rw [Set.mem_iInter]; rfl
  exact e' ▸ isOpen_iInter_of_finite fun i => (h2 N hN).preimage (continuous_apply i)

theorem LN_small {U : Set (ι → A F)} (hU : U ∈ 𝓝 (0 : ι → A F)) : ∃ N : ℕ, 0 < N ∧ (LN F ι N : Set (ι → A F)) ⊆ U := by
  obtain ⟨-, -, -, -, -, -, -, h1, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, t, ht, hsub⟩ := hU
  obtain ⟨N, hN, h⟩ := h1 (⋂ i, t i) (Filter.iInter_mem.2 ht)
  refine ⟨N, hN, fun x hx => hsub fun i _ => ?_⟩
  obtain ⟨y, hy, e⟩ := hx i
  exact e ▸ Set.mem_iInter.1 (h y hy) i

theorem orbit_adelic [MeasurableSpace (A F)] {ψ : AddChar (A F) ℂ} {h : A F} {B : Matrix ι ι (A F)}
    {μ : Measure (ι → A F)} (H : NAQuad ψ h B μ) {φ : (ι → A F) → ℂ} (hφ : SB φ) :
    ∃ (L' : AddSubgroup (ι → A F)) (s : Finset (ι → A F)) (C : ℝ), CO L' ∧ ∀ k : SL(2, A F), (∀ i j, k i j ∈ Oh F) →
      ∀ T, Impl ψ h B μ k T → (∀ u, ‖T φ u‖ ≤ C) ∧
        ∃ c : (ι → A F) → ℂ, (∀ a, ‖c a‖ ≤ C) ∧ T φ = ∑ a ∈ s, c a • ind a L' := by
  have hD := H.2.2.2.2.2
  obtain ⟨L, L', hL, hL', -, h0, hinv⟩ := sb_level hD hφ
  obtain ⟨L₂, hL₂, hK⟩ := co_cpt hD ((co_LN (F := F) (ι := ι) one_pos).1.image (continuous_const_smul h))
  obtain ⟨N, hN, hsub⟩ := LN_small (((hL'.2.inter (co_perp hD hL).2).inter (co_perp hD hL₂).2).mem_nhds
    ⟨⟨L'.zero_mem, (perpG hD L).zero_mem⟩, (perpG hD L₂).zero_mem⟩)
  refine orbit_bd H (Oh F) (co_LN hN) (fun a ha x hx i => ?_) hφ fun x hx y hy => funext fun u => ?_
  · obtain ⟨y, hy, e⟩ := hx i
    exact ⟨a * y, oh_mul ha hy, by rw [Pi.smul_apply, e, smul_eq_mul, mul_left_comm]⟩
  · have h1 : chiB ψ B (h • x) y = 1 := (hsub hy).2 _ (hK ⟨x, fun i => by
      obtain ⟨z, hz, e⟩ := hx i
      exact ⟨N * z, oh_mul (oh_nat N) hz, by rw [e, Nat.cast_one, one_mul]⟩, rfl⟩)
    rw [chiB, smul_dotProduct, smul_eq_mul] at h1
    rw [Heisenberg₂, hinv u x (hsub hx).1.1, AddChar.map_add_eq_mul, h1, mul_one]
    by_cases hu : u ∈ L
    · rw [show ψ (u ⬝ᵥ (B *ᵥ y)) = 1 from (hsub hy).1.2 u hu, one_mul]
    · rw [h0 u hu, mul_zero]

end PositivityTheory.PlacePermOperatorBicommutantSpan
end
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

set_option maxHeartbeats 400000 in
theorem bounded : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F)) (gi : Ω → InfinitePlace F → Matrix ι ι ℝ), CountData M B ρ Pr gf gi → ∀ φ : (ι → A F) → ℂ, SB φ → ∃ C : ℝ, ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → wt M τ * ‖((∫ ω, theta B ρ P (gf ω) (gi ω) φ τ ∂Pr) - eis ψ lf B ρ P φ τ)‖ ≤ C := by
  intro F _ _ _ _ lf hlf h1 ψ hψ ι _ _ M B ρ P hQ hM Ω _ Pr gf gi hC φ hφ
  have H := GlobalTheory.T.weil_representation_quadratic_datum F lf hlf h1 ψ hψ ι B hQ.2.2.1 hQ.2.2.2.1
  have hO := hC.2.2.2.1
  obtain ⟨𝒟, h𝒟⟩ : ∃ 𝒟 : ((ι → A F) → ℂ) → (InfinitePlace F → ℂ) → ℂ, ∀ φ τ,
    𝒟 φ τ = (∫ ω, theta B ρ P (gf ω) (gi ω) φ τ ∂Pr) - eis ψ lf B ρ P φ τ := ⟨_, fun _ _ => rfl⟩
  have hUD := fun ω => GlobalTheory.T.theta_function_modularity F ψ hψ ι M B ρ P hQ _ _ (hO ω)
  have hei := GlobalTheory.T.theta_function_cusp_expansion F lf hlf h1 ψ hψ ι M B ρ P hQ hM
  have heb := GlobalTheory.T.summable_norm_eiTerm_and_wt_mul_tsum_le F lf hlf h1 ψ hψ ι M B ρ P hQ hM
  have hti := GlobalTheory.T.theta_average_integral_formula F lf hlf h1 ψ hψ ι M B ρ P hQ Ω Pr gf gi hC
  have hsm : ∀ φ τ, SB φ → (∀ w, 0 < (τ w).im) → ∀ c : ℂ, 𝒟 (c • φ) τ = c * 𝒟 φ τ := fun φ τ hφ hτ c => by
    simp only [h𝒟, fun ω => (hUD ω φ τ).2.2 c, (hei φ hφ τ hτ).2.2.2 c, integral_const_mul, mul_sub]
  have good := good_ex hlf h1 hψ hQ (𝒟 := 𝒟) fun φ τ hφ hτ =>
    ⟨fun b => by simp only [h𝒟, fun ω => (hUD ω φ τ).1 b, (hei φ hφ τ hτ).1 b],
      fun a ha => by simp only [h𝒟, fun ω => (hUD ω φ τ).2.1 a ha, (hei φ hφ τ hτ).2.1 a ha],
      by simp only [h𝒟, mul_sub, ← integral_const_mul, (hei φ hφ τ hτ).2.2.1,
        fun ω => GlobalTheory.T.theta_function_automorphy F lf hlf h1 ψ hψ ι M B ρ P hQ _ _ (hO ω) φ hφ τ hτ], hsm φ τ hφ hτ⟩
  have hadd : ∀ τ, (∀ w, 0 < (τ w).im) → ∀ φ φ', SB φ → SB φ' → 𝒟 (φ + φ') τ = 𝒟 φ τ + 𝒟 φ' τ := by
    intro τ hτ φ φ' hφ hφ'
    obtain ⟨w₀, hw₀⟩ := Finite.exists_min fun w => (τ w).im
    have e1 : ∀ ω, theta B ρ P (gf ω) (gi ω) (φ + φ') τ =
        theta B ρ P (gf ω) (gi ω) φ τ + theta B ρ P (gf ω) (gi ω) φ' τ := fun ω => by
      have hs := (GlobalTheory.T.theta_series_summable F ι M B ρ P hQ _ _ (hO ω) τ hτ).1
      rw [theta, theta, theta, ← (hs φ hφ).of_norm.tsum_add (hs φ' hφ').of_norm]
      simp only [thTerm, Pi.add_apply, add_mul]
    have e2 : ∀ b, eiTerm ψ lf B ρ P (φ + φ') τ b = eiTerm ψ lf B ρ P φ τ b + eiTerm ψ lf B ρ P φ' τ b := fun b => by
      rw [eiTerm, eiTerm, eiTerm, ← add_mul, fstar, fstar, fstar,
        ← integral_add (sb_int H.2.2.2.2.2 (sb_opU H _ hφ)) (sb_int H.2.2.2.2.2 (sb_opU H _ hφ'))]
      simp only [opU, Pi.add_apply, mul_add]
    obtain ⟨_, s1⟩ := heb φ hφ _ (hτ w₀)
    obtain ⟨_, s2⟩ := heb φ' hφ' _ (hτ w₀)
    simp only [h𝒟, e1, eis, e2, Pi.add_apply, integral_add (hti φ τ hφ hτ).1 (hti φ' τ hφ' hτ).1,
      (s1 τ hw₀).1.of_norm.tsum_add (s2 τ hw₀).1.of_norm]
    ring
  obtain ⟨S, κ, t, hκ, ht, hred⟩ := GlobalTheory.T.reduction_to_siegel_domain F hQ.1 ρ hQ.2.2.2.2.1
  have hwt : ∀ τ : InfinitePlace F → ℂ, 0 ≤ wt M τ := fun τ => Finset.prod_nonneg fun _ _ => by positivity
  have hS : ∀ φ, SB φ → ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : InfinitePlace F → ℂ, (∀ w, t ≤ (τ w).im) →
      (∀ v w, κ * (τ w).im ≤ (τ v).im) → wt M τ * ‖𝒟 φ τ‖ ≤ C := fun φ hφ => by
    obtain ⟨C₁, b1⟩ := GlobalTheory.T.weighted_theta_average_le_of_countData F ι M B ρ P hQ Ω Pr gf gi hC φ hφ κ t hκ ht
    obtain ⟨C₂, b2⟩ := heb φ hφ t ht
    refine ⟨|C₁| + |C₂|, by positivity, fun τ h2 h3 => ?_⟩
    have hτ : ∀ w, 0 < (τ w).im := fun w => ht.trans_le (h2 w)
    have h4 := (mul_le_mul_right (hti φ τ hφ hτ).2 _).trans (b1 τ h2 h3).2
    rw [← ENNReal.ofReal_mul (hwt τ)] at h4
    have h5 := (ENNReal.ofReal_le_ofReal_iff (abs_nonneg C₁)).1 (h4.trans (ENNReal.ofReal_le_ofReal (le_abs_self _)))
    have h6 : ‖𝒟 φ τ‖ ≤ ‖(∫ ω, theta B ρ P (gf ω) (gi ω) φ τ ∂Pr) - φ 0‖ + ∑' b, ‖eiTerm ψ lf B ρ P φ τ b‖ := by
      simp only [h𝒟, eis, ← sub_sub]
      exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_tsum_le_tsum_norm (b2 τ h2).1))
    refine (mul_le_mul_of_nonneg_left h6 (hwt τ)).trans ?_
    rw [mul_add]
    exact add_le_add h5 ((b2 τ h2).2.trans (le_abs_self _))
  choose T hT1 hT2 using good
  obtain ⟨L, s, C₀, hL, horb⟩ := orbit_adelic H hφ
  have := H.2.2.2.2.2.1
  have := H.2.2.2.2.2.2.1
  choose C hC0 hCb using fun (r : SL(2, F)) (a : ι → A F) => hS _ ((hT1 r).1 _ (sb_ind a hL))
  refine ⟨∑ r ∈ S, ∑ a ∈ s, |C₀| * C r a, fun τ hτ => ?_⟩
  rw [← h𝒟]
  obtain ⟨r, hr, k, hk, h2, h3⟩ := hred τ hτ
  have hmob := GlobalTheory.T.mobius_action_upper_half_plane F ρ τ hτ
  obtain ⟨-, c, hc, e⟩ := horb (Matrix.SpecialLinearGroup.map (algebraMap F (A F)) k) (fun i j => ((GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.1 (k i j)).2 (hk i j)) _ (hT1 k)
  have hτ' : ∀ w, 0 < (mob ρ (r * k) τ w).im := fun w => (hmob.1 _ w).2
  rw [← hT2 k φ τ hφ hτ, ← hT2 r _ _ ((hT1 k).1 φ hφ) fun w => (hmob.1 k w).2, ← hmob.2.1, e,
    map_sum_sb (hT1 r).2.2.1 (hT1 r).2.2.2.1 s c fun a => sb_ind a hL]
  have e2 := congrFun (map_sum_sb (T := fun φ _ => 𝒟 φ (mob ρ (r * k) τ))
    (fun φ φ' h h' => funext fun _ => hadd _ hτ' φ φ' h h') (fun c φ h => funext fun _ => hsm φ _ h hτ' c) s c
    fun a => (hT1 r).1 _ (sb_ind a hL)) 0
  rw [e2, Finset.sum_apply]
  refine le_trans ?_ (Finset.single_le_sum (f := fun r => ∑ a ∈ s, |C₀| * C r a)
    (fun r _ => Finset.sum_nonneg fun a _ => mul_nonneg (abs_nonneg _) (hC0 r a)) hr)
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hwt _)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Pi.smul_apply, norm_smul, mul_left_comm]
  exact mul_le_mul ((hc a).trans (le_abs_self _)) (hCb r a _ h2 h3) (mul_nonneg (hwt _) (norm_nonneg _)) (abs_nonneg _)

end PositivityTheory.PlacePermOperatorBicommutantSpan
end
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

theorem int_fou {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] {χ : V → V → ℂ} {μ : Measure V}
    (h : NADual V χ μ) {f : V → ℂ} (hf : SB f) : ∫ y, fou χ μ f y ∂μ = f 0 := by
  have := (fou_sb h hf).2 0
  simpa only [fou, neg_zero, chi_sym h _ 0, chi_zero h, mul_one] using this

theorem recip : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ φ : (ι → A F) → ℂ, SB φ → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∀ b : F, b ≠ 0 → cG B ρ P τ * eiTerm ψ lf B ρ P (fou (chiB ψ (Bf B)) (muF B lf) φ) (fun w => -(τ w)⁻¹) b = eiTerm ψ lf B ρ P φ τ (-b⁻¹) := by
  intro F _ _ _ _ lf hlf h1 ψ hψ ι _ _ M B ρ P hQ φ hφ τ hτ b hb
  have H := GlobalTheory.T.weil_representation_quadratic_datum F lf hlf h1 ψ hψ ι B hQ.2.2.1 hQ.2.2.2.1
  have hD := H.2.2.2.2.2
  set m : ℝ := |((Algebra.norm ℚ (b⁻¹ : F) : ℚ) : ℝ)|⁻¹ ^ M with hm
  have hm0 : 0 < m := pow_pos (inv_pos.2 (abs_pos.2 (by exact_mod_cast Algebra.norm_ne_zero_iff.2 (inv_ne_zero hb)))) M
  obtain ⟨γ, -, hγ⟩ := weil_id H (uA (Units.mk0 b hb)) hm0 (mod_rat hlf h1 hQ.2.1 B (Units.mk0 b hb)⁻¹)
  set c : A F := algebraMap F (A F) b⁻¹ with hc
  have hγ' : ∀ φ, SB φ → opU ψ (hf F) (Bf B) (algebraMap F (A F) b) (fou (chiB ψ (Bf B)) (muF B lf) φ) =
      (γ * m) • fou (chiB ψ (Bf B)) (muF B lf) (opU ψ (hf F) (Bf B) (algebraMap F (A F) (-b⁻¹))
        (opD 1 c (fou (chiB ψ (Bf B)) (muF B lf) (opU ψ (hf F) (Bf B) (algebraMap F (A F) (-b⁻¹)) φ)))) := by
    intro φ hφ
    refine (hγ φ hφ).trans ?_
    rw [mul_smul, ← fou_smul (m : ℂ), map_neg]
    congr 2
    funext u
    simp only [opU, opD, Pi.smul_apply, smul_eq_mul, Complex.ofReal_one, one_mul, mul_left_comm (m : ℂ)]
    rfl
  have hO : IsOrth B ρ 1 fun _ => 1 := ⟨by simp, fun _ => by simp⟩
  have hU := fun φ τ => (GlobalTheory.T.theta_function_modularity F ψ hψ ι M B ρ P hQ _ _ hO φ τ)
  have hW := GlobalTheory.T.theta_function_automorphy F lf hlf h1 ψ hψ ι M B ρ P hQ _ _ hO
  have hG := GlobalTheory.T.archimedean_gaussian_fourier F ι M B ρ P hQ
  obtain ⟨φ₀, hφ₀, hne⟩ := (GlobalTheory.T.theta_series_summable F ι M B ρ P hQ _ _ hO τ hτ).2
  have hρ : ∀ w, ((ρ w b : ℝ) : ℂ) ≠ 0 := fun w => by exact_mod_cast (map_ne_zero (ρ w)).2 hb
  have him : ∀ {σ : InfinitePlace F → ℂ}, (∀ w, 0 < (σ w).im) → ∀ w, 0 < (-(σ w)⁻¹).im := fun h w => by
    rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_pos (h w) (Complex.normSq_pos.2 fun h0 => by simpa [h0] using h w)
  set τ₁ : InfinitePlace F → ℂ := fun w => τ w + (ρ w (-b⁻¹) : ℝ) with hτ₁
  have p1 : ∀ w, 0 < (τ₁ w).im := fun w => by simpa [hτ₁] using hτ w
  set τ₄ : InfinitePlace F → ℂ := fun w => ((ρ w b⁻¹ : ℝ) : ℂ) ^ 2 * -(τ₁ w)⁻¹ + (ρ w (-b⁻¹) : ℝ) with hτ₄
  have p4 : ∀ w, 0 < (τ₄ w).im := fun w => by
    simp only [hτ₄, Complex.add_im, Complex.ofReal_im, add_zero, ← Complex.ofReal_pow, Complex.im_ofReal_mul]
    exact mul_pos (sq_pos_of_ne_zero ((map_ne_zero (ρ w)).2 (inv_ne_zero hb))) (him p1 w)
  have e4 : (fun w => -(τ₄ w)⁻¹) = fun w => -(τ w)⁻¹ + (ρ w b : ℝ) := by
    funext w
    have h0 : τ w ≠ 0 := fun h => by simpa [h] using hτ w
    have h2 : τ₁ w ≠ 0 := fun h => by simpa [h] using p1 w
    have h3 : τ w * (ρ w b : ℝ) - 1 ≠ 0 := fun h => h2 (by
      simp only [hτ₁, map_neg, map_inv₀, Complex.ofReal_neg, Complex.ofReal_inv]
      field_simp [hρ w]
      linear_combination h)
    have h5 : τ₄ w = -(τ w / (τ w * (ρ w b : ℝ) - 1)) := by
      have h6 : τ₁ w = (τ w * (ρ w b : ℝ) - 1) / (ρ w b : ℝ) := by
        simp only [hτ₁, map_neg, map_inv₀, Complex.ofReal_neg, Complex.ofReal_inv]
        field_simp [hρ w]
        ring
      have h7 := hρ w
      simp only [hτ₄, h6, map_neg, map_inv₀, Complex.ofReal_neg, Complex.ofReal_inv]
      generalize ((ρ w b : ℝ) : ℂ) = r at h3 h7 ⊢
      rw [inv_div, div_eq_mul_inv, div_eq_mul_inv]
      have h8 := mul_inv_cancel₀ h3
      have h9 := mul_inv_cancel₀ h7
      linear_combination (-(r⁻¹ * (τ w * r - 1)⁻¹) - τ w * (τ w * r - 1)⁻¹) * h9 + r⁻¹ * h8
    rw [h5]
    field_simp
    ring
  have s1 := sb_opU H (algebraMap F (A F) (-b⁻¹)) hφ₀
  have s3 : SB (opD 1 c (fou (chiB ψ (Bf B)) (muF B lf) (opU ψ (hf F) (Bf B) (algebraMap F (A F) (-b⁻¹)) φ₀))) :=
    sb_opD H 1 (uA (Units.mk0 b hb)⁻¹) (fou_sb hD s1).1
  have t1 := (hW _ s1 τ₁ p1).trans ((hU φ₀ τ).1 (-b⁻¹))
  have t4 := (hW _ (sb_opU H (algebraMap F (A F) (-b⁻¹)) s3) τ₄ p4).trans
    (((hU _ _).1 (-b⁻¹)).trans ((hU _ fun w => -(τ₁ w)⁻¹).2.1 b⁻¹ (inv_ne_zero hb)))
  have t0 := hW φ₀ hφ₀ τ hτ
  rw [← (hU _ fun w => -(τ w)⁻¹).1 b, hγ' φ₀ hφ₀, (hU _ _).2.2, ← e4] at t0
  have t5 := (hG τ₄ p4).2.2.1
  have key : cG B ρ P τ * (γ * m) * cG B ρ P (fun w => -(τ₄ w)⁻¹) = cG B ρ P τ₁ := by
    refine mul_right_cancel₀ hne ?_
    conv_rhs => rw [← t0]
    conv_lhs => rw [← t1, ← t4]
    linear_combination (cG B ρ P τ * (γ * m) * cG B ρ P τ₁ * theta B ρ P 1 (fun _ => 1)
      (fou (chiB ψ (Bf B)) (muF B lf) (opU ψ (hf F) (Bf B) (algebraMap F (A F) (-b⁻¹)) (opD 1 c
        (fou (chiB ψ (Bf B)) (muF B lf) (opU ψ (hf F) (Bf B) (algebraMap F (A F) (-b⁻¹)) φ₀)))))
      fun w => -(τ₄ w)⁻¹) * t5
  have s1' := sb_opU H (algebraMap F (A F) (-b⁻¹)) hφ
  have s3' : SB (opD 1 c (fou (chiB ψ (Bf B)) (muF B lf) (opU ψ (hf F) (Bf B) (algebraMap F (A F) (-b⁻¹)) φ))) :=
    sb_opD H 1 (uA (Units.mk0 b hb)⁻¹) (fou_sb hD s1').1
  have f1 : fstar ψ (hf F) (Bf B) (muF B lf) (fou (chiB ψ (Bf B)) (muF B lf) φ) (algebraMap F (A F) b) =
      γ * m * fstar ψ (hf F) (Bf B) (muF B lf) φ (algebraMap F (A F) (-b⁻¹)) := by
    rw [fstar, hγ' φ hφ]
    simp only [Pi.smul_apply, smul_eq_mul, integral_const_mul, int_fou hD (sb_opU H _ s3')]
    simp [opU, opD, qf, fou, chiB, fstar]
  rw [eiTerm, eiTerm, f1, ← e4, ← key]
  ring

end PositivityTheory.PlacePermOperatorBicommutantSpan
end
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

theorem cG_dil {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι] {M : ℕ} {B : Matrix ι ι F}
    {ρ : InfinitePlace F → (F →+* ℝ)} {P : InfinitePlace F → Matrix ι ι ℝ} (hQ : QSetup M B ρ P) {a : F} (ha : a ≠ 0)
    (τ : InfinitePlace F → ℂ) : cG B ρ P (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) =
      ((|((Algebra.norm ℚ a : ℚ) : ℝ)|⁻¹ ^ M) ^ 2 : ℝ) * cG B ρ P τ := by
  let L : (InfinitePlace F → ι → ℝ) →ₗ[ℝ] (InfinitePlace F → ι → ℝ) :=
    LinearMap.pi fun w => (ρ w a • LinearMap.id) ∘ₗ LinearMap.proj w
  have hdet : |LinearMap.det L| = |((Algebra.norm ℚ a : ℚ) : ℝ)| ^ (2 * M) := by
    rw [LinearMap.det_pi, ← prod_rho hQ.1 hQ.2.2.2.2.1, Finset.abs_prod, ← Finset.prod_pow]
    simp [hQ.2.1]
  have hn : (0 : ℝ) < |((Algebra.norm ℚ a : ℚ) : ℝ)| := abs_pos.2 (by exact_mod_cast Algebra.norm_ne_zero_iff.2 ha)
  have hd : LinearMap.det L ≠ 0 := abs_pos.1 (by rw [hdet]; positivity)
  have e : gauss B ρ P (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) = fun x => gauss B ρ P τ (L x) := by
    funext x
    simp only [gauss, L, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.smul_apply,
      LinearMap.id_apply, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, ← Complex.ofReal_pow,
      Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    push_cast
    ring
  have hm := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (InfinitePlace F → ι → ℝ)) hd
  have e2 : ∫ x, gauss B ρ P τ (L x) = ∫ x, gauss B ρ P τ x ∂(Measure.map L volume) :=
    (integral_map_equiv (L.equivOfDetNeZero hd).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv _).symm
  rw [cG, cG, e, e2, hm, integral_smul_measure, abs_inv, hdet, ENNReal.toReal_ofReal (by positivity),
    Complex.real_smul, ← pow_mul, mul_comm M 2, inv_pow]
  ring

theorem fstar_dil {R : Type} [CommRing R] {ι : Type} [Fintype ι] [TopologicalSpace R] [MeasurableSpace R]
    {ψ : AddChar R ℂ} {h : R} {B : Matrix ι ι R} {μ : Measure (ι → R)} (H : NAQuad ψ h B μ) (a : Rˣ) {m : ℝ}
    (hm : 0 ≤ m) (hμ : ∀ s : Set (ι → R), MeasurableSet s → μ ((fun u => (a : R) • u) '' s) = ENNReal.ofReal m * μ s)
    (φ : (ι → R) → ℂ) (b : R) : m * fstar ψ h B μ (opD 1 (a : R) φ) ((a : R) ^ 2 * b) = fstar ψ h B μ φ b := by
  have := H.1
  have := H.2.2.2.2.2.2.2.2.2.1
  let e : (ι → R) ≃ᵐ (ι → R) := (Homeomorph.smul a).toMeasurableEquiv
  have he : μ = ENNReal.ofReal m • μ.map e := by
    ext s hs
    rw [Measure.smul_apply, e.map_apply, smul_eq_mul, ← hμ _ (e.measurable hs)]
    exact congrArg μ (e.surjective.image_preimage s).symm
  rw [fstar, fstar]
  conv_rhs => rw [he]
  rw [integral_smul_measure, integral_map_equiv, ENNReal.toReal_ofReal hm, Complex.real_smul]
  congr 2
  funext u
  show _ = opU ψ h B b φ ((a : R) • u)
  simp only [opU, opD, qf, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, Complex.ofReal_one, one_mul]
  congr 2
  ring

theorem ei_inv : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M → ∀ φ : (ι → A F) → ℂ, SB φ → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → (∀ b : F, eis ψ lf B ρ P (opU ψ (hf F) (Bf B) (algebraMap F (A F) b) φ) (fun w => τ w + (ρ w b : ℝ)) = eis ψ lf B ρ P φ τ) ∧ (∀ a : F, a ≠ 0 → eis ψ lf B ρ P (opD 1 (algebraMap F (A F) a) φ) (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) = eis ψ lf B ρ P φ τ) ∧ (cG B ρ P τ * eis ψ lf B ρ P (fou (chiB ψ (Bf B)) (muF B lf) φ) (fun w => -(τ w)⁻¹) = eis ψ lf B ρ P φ τ) ∧ ∀ c : ℂ, eis ψ lf B ρ P (c • φ) τ = c * eis ψ lf B ρ P φ τ := by
  intro F _ _ _ _ lf hlf h1 ψ hψ ι _ _ M B ρ P hQ hM φ hφ τ hτ
  have H := GlobalTheory.T.weil_representation_quadratic_datum F lf hlf h1 ψ hψ ι B hQ.2.2.1 hQ.2.2.2.1
  have hD := H.2.2.2.2.2
  have hsum : ∀ φ, SB φ → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → Summable (eiTerm ψ lf B ρ P φ τ) := by
    intro φ hφ τ hτ
    obtain ⟨w₀, hw₀⟩ := Finite.exists_min fun w => (τ w).im
    obtain ⟨_, s⟩ := GlobalTheory.T.summable_norm_eiTerm_and_wt_mul_tsum_le F lf hlf h1 ψ hψ ι M B ρ P hQ hM φ hφ _ (hτ w₀)
    exact (s τ hw₀).1.of_norm
  refine ⟨fun b => ?_, fun a ha => ?_, ?_, fun c => ?_⟩
  · rw [eis, eis, ← (Equiv.addLeft b).tsum_eq (eiTerm ψ lf B ρ P φ τ)]
    congr 1
    · simp [opU, qf]
    · refine tsum_congr fun b' => ?_
      simp only [eiTerm, fstar, opU, Equiv.coe_addLeft, map_add, Complex.ofReal_add, add_assoc, ← mul_assoc,
        ← AddChar.map_add_eq_mul, add_mul, add_comm (algebraMap F (A F) b * _)]
  · rw [eis, eis, ← (Equiv.mulLeft₀ (a ^ 2) (pow_ne_zero 2 ha)).tsum_eq]
    congr 1
    · simp [opD]
    · refine tsum_congr fun b' => ?_
      have e := fstar_dil H (uA (Units.mk0 a ha)) (by positivity) (mod_rat hlf h1 hQ.2.1 B (Units.mk0 a ha)) φ
        (algebraMap F (A F) b')
      have e2 := cG_dil hQ ha fun w => τ w + (ρ w b' : ℝ)
      simp only [eiTerm, Equiv.mulLeft₀_apply, map_mul, map_pow, Complex.ofReal_mul, Complex.ofReal_pow, ← mul_add]
      rw [e2, ← e, mul_left_comm, ← mul_assoc]
      rfl
  · have hτ' : ∀ w, 0 < (-(τ w)⁻¹).im := fun w => by
      rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
      exact div_pos (hτ w) (Complex.normSq_pos.2 fun h0 => by simpa [h0] using hτ w)
    classical
    have hF := (fou_sb hD hφ).1
    have e1 : cG B ρ P τ * fou (chiB ψ (Bf B)) (muF B lf) φ 0 = eiTerm ψ lf B ρ P φ τ 0 := by
      simp [eiTerm, fstar, opU, fou, chiB, mul_comm]
    have e2 : cG B ρ P τ * eiTerm ψ lf B ρ P (fou (chiB ψ (Bf B)) (muF B lf) φ) (fun w => -(τ w)⁻¹) 0 = φ 0 := by
      have := (GlobalTheory.T.archimedean_gaussian_fourier F ι M B ρ P hQ τ hτ).2.2.1
      simp only [eiTerm, fstar, opU, map_zero, zero_mul, AddChar.map_zero_eq_one, one_mul, Complex.ofReal_zero, add_zero,
        int_fou hD hφ]
      rw [mul_left_comm, this, mul_one]
    rw [eis, eis, (hsum _ hF _ hτ').tsum_eq_add_tsum_ite 0, (hsum _ hφ _ hτ).tsum_eq_add_tsum_ite 0, mul_add, mul_add,
      e1, e2, ← tsum_mul_left, add_left_comm, ← ((Equiv.inv F).trans (Equiv.neg F)).tsum_eq
        fun b => if b = 0 then 0 else eiTerm ψ lf B ρ P φ τ b]
    congr 2
    refine tsum_congr fun b => ?_
    by_cases hb : b = 0
    · simp [hb]
    · rw [if_neg hb, recip F lf hlf h1 ψ hψ ι M B ρ P hQ φ hφ τ hτ b hb]
      exact (if_neg (by simpa using hb)).symm
  · simp only [eis, eiTerm, fstar, opU, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul, mul_assoc,
      tsum_mul_left, mul_add]

end PositivityTheory.PlacePermOperatorBicommutantSpan
end
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

theorem sb_indL {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] {a : ℕ} (ha : 0 < a) :
    SB (indL (F := F) (ι := ι) a) := by
  have := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.1
  have ha' : (a : F) ≠ 0 := by exact_mod_cast ha.ne'
  have e : indL (F := F) (ι := ι) a = ind 0 (LN F ι 1) ∘ Homeomorph.smul (uA (Units.mk0 (a : F) ha')) := by
    funext u
    have h : (∀ i, (a : A F) * u i ∈ Oh F) ↔ uA (Units.mk0 (a : F) ha') • u - 0 ∈ LN F ι 1 := by
      rw [sub_zero]
      refine forall_congr' fun i => ?_
      have : (uA (Units.mk0 (a : F) ha') • u) i = (a : A F) * u i := by simp [uA, Units.smul_def]
      simp [this]
    by_cases hu : ∀ i, (a : A F) * u i ∈ Oh F
    · exact (Set.indicator_of_mem (s := {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}) hu _).trans
        (ind_of_mem (h.1 hu)).symm
    · exact (Set.indicator_of_notMem (s := {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}) hu _).trans
        (ind_of_not (mt h.2 hu)).symm
  exact e ▸ sb_homeo (sb_ind 0 (co_LN one_pos)) _

theorem bounded_a : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F)) (gi : Ω → InfinitePlace F → Matrix ι ι ℝ), CountData M B ρ Pr gf gi → ∃ C : ℝ, ∀ a : ℕ, 0 < a → ∀ x : InfinitePlace F → ℝ, SB (indL (F := F) (ι := ι) a) ∧ ‖((∫ ω, theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) ∂Pr) - eis ψ lf B ρ P (indL a) (fun w => (x w : ℂ) + Complex.I))‖ ≤ C * (a : ℝ) ^ (Module.finrank ℚ F * M) := by
  intro F _ _ _ _ lf hlf h1 ψ hψ ι _ _ M B ρ P hQ hM Ω _ Pr gf gi hC
  obtain ⟨C, hb⟩ := bounded F lf hlf h1 ψ hψ ι M B ρ P hQ hM Ω Pr gf gi hC _ (sb_indL one_pos)
  refine ⟨C, fun a ha x => ⟨sb_indL ha, ?_⟩⟩
  have ha' : (a : F) ≠ 0 := by exact_mod_cast ha.ne'
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  set τ : InfinitePlace F → ℂ := fun w => ((((a : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) * ((x w : ℂ) + Complex.I) with hτ
  have him : ∀ w, (τ w).im = ((a : ℝ) ^ 2)⁻¹ := fun w => by simp only [hτ, Complex.im_ofReal_mul]; simp
  have hp : ∀ w, 0 < (τ w).im := fun w => by rw [him]; positivity
  have e1 : opD 1 (algebraMap F (A F) a) (indL (F := F) (ι := ι) 1) = indL a := by
    funext u
    have h : (∀ i, ((1 : ℕ) : A F) * (algebraMap F (A F) a • u) i ∈ Oh F) ↔ ∀ i, (a : A F) * u i ∈ Oh F := by
      simp only [Nat.cast_one, one_mul, Pi.smul_apply, smul_eq_mul, map_natCast]
    simp only [opD, indL, Set.indicator, Complex.ofReal_one, one_mul]
    classical
    convert if_congr h (rfl : (1 : ℂ) = 1) (rfl : (0 : ℂ) = 0) <;> rfl
  have e2 : (fun w => ((ρ w (a : F) : ℝ) : ℂ) ^ 2 * τ w) = fun w => (x w : ℂ) + Complex.I := by
    funext w; simp only [hτ, map_natCast]; push_cast; field_simp
  have e3 := fun ω => (GlobalTheory.T.theta_function_modularity F ψ hψ ι M B ρ P hQ _ _ (hC.2.2.2.1 ω) (indL 1) τ).2.1 a ha'
  have e4 := (ei_inv F lf hlf h1 ψ hψ ι M B ρ P hQ hM _ (sb_indL one_pos) τ hp).2.1 a ha'
  rw [e1, e2] at e4
  simp only [e1, e2] at e3
  have h2 := hb τ hp
  have hcard : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
    have := hQ.1
    rw [IsTotallyReal.finrank F, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
  have hw : wt M τ = ((a : ℝ) ^ (Module.finrank ℚ F * M))⁻¹ := by
    simp only [wt, him, Real.sqrt_inv, Real.sqrt_sq haR.le, Finset.prod_const, Finset.card_univ, hcard, ← pow_mul,
      inv_pow, mul_comm M]
  simp only [e3, e4]
  rwa [hw, inv_mul_le_iff₀ (by positivity), mul_comm] at h2

theorem core : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ), Fintype.card ι = 2 * M → 3 ≤ M → ∀ (B : Matrix ι ι F), B.IsSymm → B.det ≠ 0 → ∀ (ρ : InfinitePlace F → (F →+* ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∀ (Pm : InfinitePlace F → Matrix ι ι ℝ), (∀ w, (Pm w).PosDef) → (∀ w, Pm w * (B.map (ρ w))⁻¹ * Pm w = B.map (ρ w)) → ∀ [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] (lf : Measure (FiniteAdeleRing (𝓞 F) F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (ginf : Ω → InfinitePlace F → Matrix ι ι ℝ) (gf : Ω → Matrix ι ι (FiniteAdeleRing (𝓞 F) F)), (∀ w i j, Measurable fun ω => ginf ω w i j) → (∀ i j, Measurable fun ω => gf ω i j) → (∀ ω w, (ginf ω w)ᵀ * B.map (ρ w) * ginf ω w = B.map (ρ w)) → (∀ ω, (gf ω)ᵀ * B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) * gf ω = B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F))) → (∀ N : ℕ, 0 < N → ∃ C : ℝ, ∀ R : ℝ, 0 < R → ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, Set.indicator {x : ι → F | (∀ i v, ((N : FiniteAdeleRing (𝓞 F) F) * (gf ω *ᵥ fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x j)) i) v ∈ v.adicCompletionIntegers F) ∧ ∀ w, ‖ginf ω w *ᵥ fun j => ρ w (x j)‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) x.1 ∂Pr ≤ ENNReal.ofReal (C * (R ^ (Module.finrank ℚ F * M) + R ^ (2 * Module.finrank ℚ F * M)))) → ∃ (C : ℝ) (Df : ℕ → FiniteAdeleRing (𝓞 F) F → ℝ) (Dinf : (InfinitePlace F → ℝ) → ℝ), (∀ a : ℕ, 0 < a → Continuous (Df a) ∧ (∀ y, 0 ≤ Df a y) ∧ ∀ U : Set (FiniteAdeleRing (𝓞 F) F), MeasurableSet U → (Measure.pi fun _ : ι => lf) {x | (∀ i v, ((a : FiniteAdeleRing (𝓞 F) F) * x i) v ∈ v.adicCompletionIntegers F) ∧ algebraMap F (FiniteAdeleRing (𝓞 F) F) (1 / 2) * (x ⬝ᵥ (B.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ x)) ∈ U} = ∫⁻ y in U, ENNReal.ofReal (Df a y) ∂lf) ∧ (Continuous Dinf ∧ (∀ y, 0 ≤ Dinf y) ∧ ∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in {x : InfinitePlace F → ι → ℝ | (fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (B.map (ρ w) *ᵥ x w))) ∈ U}, ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w))) = ∫⁻ y in U, ENNReal.ofReal (Dinf y)) ∧ ∀ a : ℕ, 0 < a → ∀ β : F, β ≠ 0 → ∃ I : ℝ≥0, ∫⁻ ω, ∑' x : {x : ι → F // (1 / 2 : F) * (x ⬝ᵥ (B *ᵥ x)) = β}, Set.indicator {x : ι → F | ∀ i v, ((a : FiniteAdeleRing (𝓞 F) F) * (gf ω *ᵥ fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x j)) i) v ∈ v.adicCompletionIntegers F} (fun x => ENNReal.ofReal (Real.exp (-Real.pi * ∑ w, (ginf ω w *ᵥ fun j => ρ w (x j)) ⬝ᵥ (Pm w *ᵥ (ginf ω w *ᵥ fun j => ρ w (x j)))))) x.1 ∂Pr = (I : ℝ≥0∞) ∧ |(I : ℝ) - (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (2 * M - 1) * Df a (algebraMap F (FiniteAdeleRing (𝓞 F) F) β) * Dinf (fun w => ρ w β)| ≤ C * (a : ℝ) ^ (Module.finrank ℚ F * M) := by
  intro F _ _ hF ι _ _ M hc hM B hB hdet ρ hρ P hP hPP _ _ lf hlf h1 Ω _ Pr _ gi gf m1 m2 o1 o2 hcnt
  have hQ : QSetup M B ρ P := ⟨hF, hc, hB, hdet, hρ, hP, hPP⟩
  have hC : CountData M B ρ Pr gf gi := ⟨inferInstance, m1, m2, fun ω => ⟨o2 ω, o1 ω⟩, hcnt⟩
  obtain ⟨ψ, hψ⟩ := (GlobalTheory.T.standard_adelic_character F).1
  obtain ⟨C, hb⟩ := bounded_a F lf hlf h1 ψ hψ ι M B ρ P hQ hM Ω Pr gf gi hC
  choose! Df d1 d2 d3 d4 d5 using GlobalTheory.T.schur_function_whittaker_equivariant F lf hlf h1 ψ hψ ι M B ρ P hQ hM
  obtain ⟨Di, i1, i2, i3, i4, i5⟩ := GlobalTheory.T.quadratic_level_set_density F ι M B ρ P hQ hM
  refine ⟨C, Df, Di, fun a ha => ⟨d1 a ha, d2 a ha, d3 a ha⟩, ⟨i1, i2, i3⟩, fun a ha β hβ => ?_⟩
  obtain ⟨-, -, -, -, -, -, hint, -, hK, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hs := sb_indL (F := F) (ι := ι) ha
  obtain ⟨N₁, p1, n1⟩ := GlobalTheory.T.weil_operator_integral_invariance F lf hlf h1 ψ hψ ι M B ρ P hQ _ hs
  have hq : Continuous (qf (hf F) (Bf B) : (ι → A F) → A F) := by unfold qf; fun_prop
  obtain ⟨N₂, p2, n2⟩ := hK _ ((hs.2.isCompact.image hq).insert (algebraMap F (A F) β))
  have hN : 0 < N₁ * N₂ := Nat.mul_pos p1 p2
  have hβN : ∃ r : 𝓞 F, (r : F) = ((N₁ * N₂ : ℕ) : F) * β := (hint _).1 (by
    rw [map_mul, map_natCast, Nat.cast_mul, mul_assoc]
    exact oh_mul (oh_nat N₁) (n2 _ (Set.mem_insert _ _)))
  obtain ⟨⟨D, hD⟩, -, -, hvol⟩ := GlobalTheory.T.lattice_fundamental_domain_volume F hF ρ hρ _ hN
  obtain ⟨I, e1, j1, e2⟩ := GlobalTheory.T.real_quadratic_form_lemma F ι M B ρ P hQ Ω Pr gf gi hC a ha β hβ _ hN hβN (fun y hy => by
    rw [Nat.cast_mul, mul_assoc]
    refine oh_mul (oh_nat N₁) (n2 _ (Set.mem_insert_of_mem _ ⟨y, subset_tsupport _ ?_, rfl⟩))
    rw [Function.mem_support, indL, Set.indicator_of_mem (s := {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}) hy]
    exact one_ne_zero) D hD
  obtain ⟨j2, e3⟩ := GlobalTheory.T.schur_function_smooth_right_invariant F lf hlf h1 ψ hψ ι M B ρ P hQ hM _ hs (d4 a ha) i4 β hβ _ hN hβN
    (fun x hx y => by
      rw [Nat.cast_mul, mul_assoc]
      exact (n1 _ (oh_mul (oh_nat N₂) hx)).2 y) D hD
  refine ⟨I, Eq.trans (lintegral_congr fun ω => tsum_congr fun x => ?_) e1, ?_⟩
  · by_cases hx : ∀ i, (a : A F) * (gf ω *ᵥ fun j => algebraMap F (A F) (x.1 j)) i ∈ Oh F
    · rw [Set.indicator_of_mem (by exact hx), thTerm, indL,
        Set.indicator_of_mem (s := {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}) hx, one_mul, ← ofReal_norm, gauss,
        Complex.norm_exp]
      congr 2
      simp [Finset.mul_sum]
    · rw [Set.indicator_of_notMem (by exact hx), thTerm, indL,
        Set.indicator_of_notMem (s := {x : ι → A F | ∀ i, (a : A F) * x i ∈ Oh F}) hx, zero_mul, enorm_zero]
  · have hk : 0 < kap F := inv_pos.2 (Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast discr_ne_zero F)))
    have hsq : 0 < Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| :=
      Real.sqrt_pos.2 (abs_pos.2 (by exact_mod_cast Algebra.norm_ne_zero_iff.2 hdet))
    set v : ℝ := ((N₁ * N₂ : ℕ) : ℝ) ^ Module.finrank ℚ F * (kap F)⁻¹ with hv
    have hv0 : 0 < v := by positivity
    have hvD : volume.real D = v := by rw [Measure.real, (hvol D hD).1, ENNReal.toReal_ofReal hv0.le]
    have h2 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := D)
      (f := fun x : InfinitePlace F → ℝ => (∫ ω, theta B ρ P (gf ω) (gi ω) (indL a) (fun w => (x w : ℂ) + Complex.I) ∂Pr) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) -
        eis ψ lf B ρ P (indL a) (fun w => (x w : ℂ) + Complex.I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)))
      (C := C * (a : ℝ) ^ (Module.finrank ℚ F * M)) (by rw [(hvol D hD).1]; exact ENNReal.ofReal_lt_top) fun x _ => by
        rw [← sub_mul, norm_mul, Complex.norm_exp]
        simpa using (hb a ha x).2
    rw [integral_sub j1 j2, e2, e3, d5 a ha, i5, hvD, show (volume D).toReal = v from hvD] at h2
    have e4 : ((v : ℝ) : ℂ) * ((I : ℝ) : ℂ) - ((N₁ * N₂ : ℕ) : ℂ) ^ Module.finrank ℚ F *
        ((kap F ^ (2 * M - 2) * (Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)|)⁻¹ * Df a (algebraMap F (A F) β) : ℝ) : ℂ) *
        ((Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)| * Di (fun w => ρ w β) : ℝ) : ℂ) =
        ((v * ((I : ℝ) - kap F ^ (2 * M - 1) * Df a (algebraMap F (A F) β) * Di fun w => ρ w β) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
        ← Complex.ofReal_mul, ← Complex.ofReal_sub, show 2 * M - 1 = 2 * M - 2 + 1 by omega, pow_succ, hv]
      congr 1
      field_simp
    rw [e4, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hv0, mul_comm v] at h2
    exact le_of_mul_le_mul_right h2 hv0

end PositivityTheory.PlacePermOperatorBicommutantSpan
end
end
