import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalMatchingOfHoweDualityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockOperatorActsByNoncompactQuadraticOps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualDirectionDerivativeMixedCoordinateBound
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaDoubleAbsoluteSumSobolevBound
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightTranslate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralFundamentalDomainLeOfMeetsOrbitsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianWittIndexLeNegativeSignature
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralSiegelConeInvModulusLtTopWeilStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilThetaLevelPolynomialInHeight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevSeminormWeilThetaPolynomialInHeightStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittFrameTorusEqLeviElementStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviThetaValueLeDetMulRationalSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfPowerDetAbsRealDiagonalTorusStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionHeisenbergWordSupLeLevelPowStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedThetaSeriesRapidDecay
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedCoordinateSupportIntegralAtLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SiegelConeIntegralMatrixLatticeCountStatement
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCI
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.Expand

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid

noncomputable section

namespace GlobalTheory.TorusMixedDecay

theorem one_le_sum_tauE (D : D7) (y : D.host.E) (hy : IsIntegral ℤ y) (h0 : y ≠ 0) :
    1 ≤ ∑ τ, ‖tauE D τ y‖ := by
  obtain ⟨φ, hφ⟩ : ∃ σ : D.host.E →+* ℂ, 1 ≤ ‖σ y‖ := by
    apply NumberField.exists_conjugate_one_le_norm (K := D.host.E) (α := ⟨y, hy⟩)
    intro h; exact h0 (congrArg Subtype.val h)
  obtain ⟨τ, hτ⟩ := (GlobalTheory.CMTypePlaces.mk_tauE_bijective D).2 (InfinitePlace.mk φ)
  have : ‖φ y‖ = ‖tauE D τ y‖ := by
    rw [← InfinitePlace.apply, ← InfinitePlace.apply]
    simp only at hτ
    rw [hτ]
  rw [this] at hφ
  exact hφ.trans (Finset.single_le_sum (f := fun τ => ‖tauE D τ y‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ τ))

theorem coord_le {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {m r : ℕ} (ξ : Matrix (Fin m) (Fin r) D.host.E)
    (L : ℕ) (hL : 0 < L) (hint : ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)) (t : Fin r → ℝ) (ht : ∀ i, 0 < t i)
    (i : Fin r) (j : Fin m) (hj : ξ j i ≠ 0) :
    t i ≤ (L : ℝ) * (1 + ∑ τ, ∑ a, ∑ b,
      ‖(compAt θ τ (ξ.map (incA D) : Mx D m r) * diagonal (fun k => (t k : ℂ))) a b‖) := by
  have hcomp : ∀ τ, compAt θ τ (ξ.map (incA D) : Mx D m r) = ξ.map (tauE D τ) := by
    intro τ; ext i j; exact (hθ τ).1 (ξ i j)
  have hentry : ∀ τ a b, ‖(compAt θ τ (ξ.map (incA D) : Mx D m r) *
      diagonal (fun k => (t k : ℂ))) a b‖ = ‖tauE D τ (ξ a b)‖ * t b := by
    intro τ a b
    rw [hcomp, Matrix.mul_diagonal, norm_mul, Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (ht b)]
  simp only [hentry]
  have hL0 : (L : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hL.ne'
  have h1 := one_le_sum_tauE D _ (hint j i) (mul_ne_zero hL0 hj)
  simp only [map_mul, map_natCast, norm_mul, Complex.norm_natCast] at h1
  rw [← Finset.mul_sum] at h1
  have hn : ∀ τ a b, 0 ≤ ‖tauE D τ (ξ a b)‖ * t b := fun τ a b => mul_nonneg (norm_nonneg _) (ht b).le
  have h2 : (∑ τ, ‖tauE D τ (ξ j i)‖) * t i ≤ ∑ τ, ∑ a, ∑ b, ‖tauE D τ (ξ a b)‖ * t b := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun τ _ => ?_
    calc ‖tauE D τ (ξ j i)‖ * t i ≤ ∑ b, ‖tauE D τ (ξ j b)‖ * t b :=
          Finset.single_le_sum (f := fun b => ‖tauE D τ (ξ j b)‖ * t b) (fun b _ => hn τ j b) (Finset.mem_univ i)
      _ ≤ _ := Finset.single_le_sum (f := fun a => ∑ b, ‖tauE D τ (ξ a b)‖ * t b)
          (fun a _ => Finset.sum_nonneg fun b _ => hn τ a b) (Finset.mem_univ j)
  have hLr : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  calc t i = 1 * t i := (one_mul _).symm
    _ ≤ ((L : ℝ) * ∑ τ, ‖tauE D τ (ξ j i)‖) * t i := mul_le_mul_of_nonneg_right h1 (ht i).le
    _ = (L : ℝ) * ((∑ τ, ‖tauE D τ (ξ j i)‖) * t i) := mul_assoc _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hLr

set_option maxHeartbeats 1000000 in
theorem prod_mul_sum_mixS_le : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (V X S₀ : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec V S₀ r) (μ' : Measure (Mx D X.rank r))
    (𝓕' : Set (Mx D X.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D X.rank r) μ' 𝓕' → ∀ (c : ℝ), 0 < c →
    ∀ (K₀ : Set (WO V X)), K₀ ∈ nhds (0 : WO V X) → IsCompact K₀ →
    ∀ (μ : Measure (WO V X)) (𝓕 : Set (WO V X)), IsCovolOne (ratL X V) μ 𝓕 → ∀ (τ₀ : D.what₂.Tau) (e : ℕ),
    ∃ (k A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ Ψ : WO V X → ℂ, IsThetaFunO ψ V X Ψ →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ V X (n • u) Ψ = Ψ) →
      (∀ (x : Mx D X.rank r) (i : Fin r), (∀ j, compAt θ τ₀ x j i = 0) → d.mixS X ψ μ' 𝓕' Ψ x 0 = 0) →
      ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ α : Mx D r r, α.map (finPart D) = 1 →
        (∀ τ, compAt θ τ α = diagonal (fun i => (t i : ℂ))) →
        ENNReal.ofReal (∏ i, t i ^ e) *
          ∑' ξ : Matrix (Fin X.rank) (Fin r) D.host.E, ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ ≤
          ENNReal.ofReal (C * (n : ℝ) ^ A * (GlobalTheory.Size.sobO (V := V) (W := X) ψ θ μ 𝓕 k Ψ).toReal) := by
  intro D ψ hψ θ hθ V X S₀ r d μ' 𝓕' hμ' c hc K₀ hK₀ hK₀c μ 𝓕 hμ τ₀ e
  obtain ⟨N, A₄, C₄, hC₄, h4⟩ := GlobalTheory.T.siegelCone_integral_matrix_lattice_count θ hθ X.rank r c hc
  obtain ⟨k₂, C₂, hC₂, h2⟩ := GlobalTheory.T.mixed_theta_series_rapid_decay ψ hψ θ hθ V X S₀ r d μ' 𝓕' hμ' (N + r * e)
  obtain ⟨k₁, B, C₁, hC₁, h1⟩ := GlobalTheory.T.thetaFunction_heisenbergWord_sup_le_level_pow ψ hψ θ hθ V X K₀ hK₀ hK₀c μ 𝓕 hμ
  obtain ⟨M, hM, h3⟩ := GlobalTheory.T.mixedCoordinate_support_integral_at_level ψ hψ V X S₀ r d μ' 𝓕' hμ' K₀ hK₀ hK₀c
  set Wc : ℝ := ∑ k ∈ Finset.range (k₂ + 1),
    (Fintype.card (D.what₂.Tau × Fin X.rank × Fin V.rank × Bool) : ℝ) ^ k with hWc
  have hWc0 : 0 ≤ Wc := Finset.sum_nonneg fun _ _ => by positivity
  refine ⟨k₁ + k₂, B + A₄ + r * e, C₂ * Wc * C₁ * C₄ * (M : ℝ) ^ (A₄ + r * e), by positivity, ?_⟩
  intro n hn Ψ hΨ hlev hvan t ht α hα hαc
  set sob := GlobalTheory.Size.sobO (V := V) (W := X) ψ θ μ 𝓕 (k₁ + k₂) Ψ with hsob
  have hsob_ne : sob ≠ ⊤ := GlobalTheory.Size.sobO_ne_top hψ hθ hμ.1 hμ.2.1 hΨ _

  have hw : GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) GlobalTheory.HeisTaylor.supN k₂ Ψ ≤
      ENNReal.ofReal (Wc * (C₁ * (n : ℝ) ^ B)) * sob := by
    unfold GlobalTheory.Size.wordSum
    have hk : ∀ k ∈ Finset.range (k₂ + 1), ∀ a : Fin k → D.what₂.Tau × Fin X.rank × Fin V.rank × Bool,
        GlobalTheory.HeisTaylor.supN (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) (List.ofFn a) Ψ) ≤
          ENNReal.ofReal (C₁ * (n : ℝ) ^ B) * sob := by
      intro k hk a
      refine (h1 n hn Ψ hΨ hlev (List.ofFn a)).trans ?_
      rw [List.length_ofFn]
      gcongr
      exact GlobalTheory.Size.wordSum_mono (by have := Finset.mem_range.1 hk; omega) Ψ
    calc ∑ k ∈ Finset.range (k₂ + 1), ∑ a : Fin k → D.what₂.Tau × Fin X.rank × Fin V.rank × Bool,
          GlobalTheory.HeisTaylor.supN (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) (List.ofFn a) Ψ)
        ≤ ∑ k ∈ Finset.range (k₂ + 1), ∑ _a : Fin k → D.what₂.Tau × Fin X.rank × Fin V.rank × Bool,
          ENNReal.ofReal (C₁ * (n : ℝ) ^ B) * sob :=
          Finset.sum_le_sum fun k hk' => Finset.sum_le_sum fun a _ => hk k hk' a
      _ = ENNReal.ofReal (Wc * (C₁ * (n : ℝ) ^ B)) * sob := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
          rw [← Finset.sum_mul, hWc, ENNReal.ofReal_mul hWc0, ← mul_assoc]
          congr 2
          rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
          push_cast; rfl
  set L : ℕ := M * n with hL
  set K₁ := ENNReal.ofReal C₂ * (ENNReal.ofReal (Wc * (C₁ * (n : ℝ) ^ B)) * sob) with hK₁
  set K := ENNReal.ofReal ((L : ℝ) ^ (r * e)) * K₁ with hK
  have hLpos : 0 < L := Nat.mul_pos hM hn

  have hpt : ∀ ξ : Matrix (Fin X.rank) (Fin r) D.host.E,
      ENNReal.ofReal (∏ i, t i ^ e) * ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ ≤
        {ξ : Matrix (Fin X.rank) (Fin r) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator
          (fun ξ => ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j,
            ‖(compAt θ τ (ξ.map (incA D) : Mx D X.rank r) * diagonal (fun k => (t k : ℂ))) i j‖) ^ N)⁻¹) ξ * K := by
    intro ξ
    by_cases h0 : d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0 = 0
    · rw [h0, enorm_zero, mul_zero]; exact bot_le
    have hfin : (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α).map (finPart D) =
        (ξ.map (incA D) : Mx D X.rank r).map (finPart D) := by
      rw [Matrix.map_mul, hα, Matrix.mul_one]
    have hint := h3 n hn Ψ hΨ hlev ξ _ hfin h0
    rw [Set.indicator_of_mem (show ξ ∈ {ξ : Matrix (Fin X.rank) (Fin r) D.host.E |
      ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)} from hint)]
    have hc' : ∀ τ, compAt θ τ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) =
        compAt θ τ (ξ.map (incA D) : Mx D X.rank r) * diagonal (fun k => (t k : ℂ)) := by
      intro τ
      rw [← hαc τ]
      exact Matrix.map_mul (f := ((θ τ).comp (infPart D)))
    have hb := h2 Ψ hΨ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α)
    simp only [hc'] at hb
    have hcol : ∀ i, ∃ j, ξ j i ≠ 0 := by
      intro i
      by_contra hcon
      push_neg at hcon
      refine h0 (hvan _ i fun j => ?_)
      rw [hc', Matrix.mul_diagonal]
      have : compAt θ τ₀ (ξ.map (incA D) : Mx D X.rank r) j i = 0 := by
        simp only [compAt, Matrix.map_apply, hcon j, map_zero]
      rw [this, zero_mul]
    have hti : ∀ i, t i ≤ (L : ℝ) * (1 + ∑ τ, ∑ a, ∑ b,
        ‖(compAt θ τ (ξ.map (incA D) : Mx D X.rank r) * diagonal (fun k => (t k : ℂ))) a b‖) := fun i => by
      obtain ⟨j, hj⟩ := hcol i
      exact coord_le hθ ξ L hLpos hint t ht.1 i j hj
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 1 + ∑ τ, ∑ a, ∑ b,
        ‖(compAt θ τ (ξ.map (incA D) : Mx D X.rank r) * diagonal (fun k => (t k : ℂ))) a b‖ := ⟨_, rfl⟩
    have hs0 : 0 < s := by rw [hs]; positivity
    rw [← hs] at hb hti ⊢
    have hprod : ∏ i, t i ^ e ≤ (L : ℝ) ^ (r * e) * s ^ (r * e) := by
      calc ∏ i, t i ^ e ≤ ∏ _i : Fin r, ((L : ℝ) * s) ^ e :=
            Finset.prod_le_prod (fun i _ => pow_nonneg (ht.1 i).le _)
              (fun i _ => pow_le_pow_left₀ (ht.1 i).le (hti i) _)
        _ = _ := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_pow, mul_comm e r]
    set P := ENNReal.ofReal (s ^ N) with hP
    have hP0 : P ≠ 0 := by
      rw [hP, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact pow_pos hs0 _
    have hPt : P ≠ ⊤ := ENNReal.ofReal_ne_top
    have hb1 : ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ *
        ENNReal.ofReal (s ^ (N + r * e)) ≤ K₁ :=
      hb.trans (by rw [hK₁]; gcongr)
    have hb' : ENNReal.ofReal (∏ i, t i ^ e) *
        ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ * P ≤ K := by
      generalize ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ = z at hb1 ⊢
      calc ENNReal.ofReal (∏ i, t i ^ e) * z * P
          ≤ ENNReal.ofReal ((L : ℝ) ^ (r * e) * s ^ (r * e)) * z * P := by
            gcongr
        _ = ENNReal.ofReal ((L : ℝ) ^ (r * e)) * (z * ENNReal.ofReal (s ^ (N + r * e))) := by
            rw [hP, pow_add, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
            ring
        _ ≤ K := by rw [hK]; gcongr
    rw [ENNReal.ofReal_inv_of_pos (pow_pos hs0 _), ← hP, ← ENNReal.div_eq_inv_mul]
    exact (ENNReal.le_div_iff_mul_le (Or.inl hP0) (Or.inl hPt)).2 hb'
  have es : sob = ENNReal.ofReal sob.toReal := (ENNReal.ofReal_toReal hsob_ne).symm
  rw [← ENNReal.tsum_mul_left]
  calc ∑' ξ : Matrix (Fin X.rank) (Fin r) D.host.E,
        ENNReal.ofReal (∏ i, t i ^ e) * ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ
      ≤ ∑' ξ : Matrix (Fin X.rank) (Fin r) D.host.E,
        {ξ : Matrix (Fin X.rank) (Fin r) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator
          (fun ξ => ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j,
            ‖(compAt θ τ (ξ.map (incA D) : Mx D X.rank r) * diagonal (fun k => (t k : ℂ))) i j‖) ^ N)⁻¹) ξ * K :=
        ENNReal.tsum_le_tsum hpt
    _ = (∑' ξ : Matrix (Fin X.rank) (Fin r) D.host.E,
        {ξ : Matrix (Fin X.rank) (Fin r) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator
          (fun ξ => ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j,
            ‖(compAt θ τ (ξ.map (incA D) : Mx D X.rank r) * diagonal (fun k => (t k : ℂ))) i j‖) ^ N)⁻¹) ξ) * K :=
        ENNReal.tsum_mul_right
    _ ≤ ENNReal.ofReal (C₄ * (L : ℝ) ^ A₄) * K := by gcongr; exact h4 L hLpos t ht
    _ = ENNReal.ofReal (C₄ * (L : ℝ) ^ A₄) * (ENNReal.ofReal ((L : ℝ) ^ (r * e)) * (ENNReal.ofReal C₂ *
          (ENNReal.ofReal (Wc * (C₁ * (n : ℝ) ^ B)) * ENNReal.ofReal sob.toReal))) := by rw [hK, hK₁, ← es]
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC₂, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [hL]
      push_cast
      ring

end GlobalTheory.TorusMixedDecay

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_mixedCoordinate_sum_rapid_decay : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (V X S₀ : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec V S₀ r) (μ' : Measure (Mx D X.rank r))
    (𝓕' : Set (Mx D X.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D X.rank r) μ' 𝓕' → ∀ (c : ℝ), 0 < c →
    ∀ (K₀ : Set (WO V X)), K₀ ∈ nhds (0 : WO V X) → IsCompact K₀ →
    ∀ (μ : Measure (WO V X)) (𝓕 : Set (WO V X)), IsCovolOne (ratL X V) μ 𝓕 → ∀ (τ₀ : D.what₂.Tau) (e : ℕ),
    ∃ (k A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ Ψ : WO V X → ℂ, IsThetaFunO ψ V X Ψ →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ V X (n • u) Ψ = Ψ) →
      (∀ (x : Mx D X.rank r) (i : Fin r), (∀ j, compAt θ τ₀ x j i = 0) → d.mixS X ψ μ' 𝓕' Ψ x 0 = 0) →
      ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ α : Mx D r r, α.map (finPart D) = 1 →
        (∀ τ, compAt θ τ α = diagonal (fun i => (t i : ℂ))) →
        ENNReal.ofReal (∏ i, t i ^ e) *
          ∑' ξ : Matrix (Fin X.rank) (Fin r) D.host.E, ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ ≤
          ENNReal.ofReal (C * (n : ℝ) ^ A * (GlobalTheory.Size.sobO (V := V) (W := X) ψ θ μ 𝓕 k Ψ).toReal) := by
  atlas_forward_decl GlobalTheory.TorusMixedDecay.prod_mul_sum_mixS_le
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

open scoped Pointwise

noncomputable section

namespace GlobalTheory.ThetaCuspInteg

theorem theta_le_height {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (M X : HSp D)
    (χ χ' : (Formalism.L2.Theta.AE D)ˣ →* Circle) (ω : WRep M X) (hω : IsWeil ψ ε M X χ χ' ω) (Φ : WO M X → ℂ)
    (hΦ : IsThetaFunO ψ (sgn ε M) X Φ) (τ₀ : D.what₂.Tau)
    (hvan : ∀ (g : GA D M) (h : GA D X) (S₀ : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec (sgn ε M) S₀ r)
      (μ' : Measure (Mx D X.rank r)) (𝓕' : Set (Mx D X.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D X.rank r) μ' 𝓕' →
      ∀ (x : Mx D X.rank r) (i : Fin r), (∀ j, compAt θ τ₀ x j i = 0) → d.mixS X ψ μ' 𝓕' (ω (g, h) Φ) x 0 = 0)
    (r : ℕ) (Xf Yf : Matrix (Fin M.rank) (Fin r) D.host.E) (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig M.gram Xf Yf)
    (Ω C₀ : Set (GA D M)) (K : Subgroup (GA D M)) (c : ℝ) (hC₀ : IsCompact C₀) (hK : IsCompact (K : Set (GA D M)))
    (hc : 0 < c)
    (hsub : ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig M.gram Xf Yf t a →
      a⁻¹ * p * a ∈ C₀) (h : GA D X) :
    ∃ B : ℝ, ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig M.gram Xf Yf t a →
      ∀ k ∈ K, ‖thetaKO ω (p * a * k) h Φ‖ₑ ≤ ENNReal.ofReal B := by
  have hC₁ : IsCompact (C₀ * (K : Set (GA D M))) := hC₀.mul hK
  obtain ⟨K₀, hK₀n, hK₀c, m, e, hlev⟩ := GlobalTheory.T.weilTheta_level_polynomial_in_height ψ θ hθ ε M X χ χ' ω hω Φ hΦ _ hC₁
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (sgn ε M) X
  obtain ⟨S₀, d, hA1⟩ := GlobalTheory.T.wittFrame_torus_eq_levi_element θ hθ ε M r Xf Yf hW
  obtain ⟨μ', 𝓕', hcov, hA2⟩ := GlobalTheory.T.leviThetaValue_le_det_mul_rational_sum ψ (sgn ε M) S₀ X r d χ χ' (ω.toSgn ε) hω
  obtain ⟨k, A, C, hC, hB⟩ := GlobalTheory.T.torus_mixedCoordinate_sum_rapid_decay ψ (IsWeilDatumO.std hω) θ hθ (sgn ε M) X S₀ r d μ' 𝓕' hcov c hc K₀ hK₀n hK₀c
    μ 𝓕 hμ τ₀ (Module.finrank ℚ D.host.F * X.rank)
  obtain ⟨N₂, C₂, hC₂, hU⟩ := GlobalTheory.T.sobolevSeminorm_weilTheta_polynomial_in_height ψ θ hθ ε M X χ χ' ω hω Φ hΦ _ hC₁ μ 𝓕 hμ k
  set H : ℝ := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) with hHdef
  refine ⟨C * (m * H ^ e) ^ A * (C₂ * H ^ N₂), fun p hp t ht a ha k' hk' => ?_⟩
  have hy : a⁻¹ * p * a * k' ∈ C₀ * (K : Set (GA D M)) := Set.mul_mem_mul (hsub p hp t ht a ha) hk'
  have hΨ : IsThetaFunO ψ (sgn ε M) X (ω (a⁻¹ * p * a * k', h) Φ) := by
    have := hω.om_pres ((GlobalTheory.Grid.ofSgn ε M).symm (a⁻¹ * p * a * k'), h) Φ hΦ
    simpa [GlobalTheory.Grid.WRep.toSgn] using this
  obtain ⟨n, hn, hnle, hnlev⟩ := hlev _ hy h
  have hs := hU _ hy h
  have hsplit : thetaKO ω (p * a * k') h Φ = ω (a, 1) (ω (a⁻¹ * p * a * k', h) Φ) 0 := by
    have e1 : ((p * a * k', h) : GA D M × GA D X) = (a, 1) * (a⁻¹ * p * a * k', h) := by
      ext <;> simp [mul_assoc]
    unfold thetaKO
    rw [e1, map_mul]
    rfl
  rw [hsplit]
  obtain ⟨α, hα1, hα2, hlevi⟩ := hA1 t ht.1 a ha
  have h2 := hB n hn _ hΨ hnlev (hvan _ h S₀ r d μ' 𝓕' hcov) t ht α.1 hα1 hα2
  have hle := hA2 _ hΨ α
  generalize ω (a⁻¹ * p * a * k', h) Φ = Ψ at *
  have e' : ω (a, 1) Ψ 0 = ω.toSgn ε (d.levi α, 1) Ψ 0 := by
    rw [← hlevi]
    show ω (a, 1) Ψ 0 = ω ((ofSgn ε M) ((ofSgn ε M).symm a), 1) Ψ 0
    rw [MulEquiv.apply_symm_apply]
  rw [← e', GlobalTheory.T.halfPowerDetAbs_realDiagonal_torus θ hθ r X.rank t ht.1 α hα1 hα2] at hle
  refine hle.trans (h2.trans (ENNReal.ofReal_le_ofReal ?_))
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm0 : 0 ≤ m * H ^ e := hn0.trans hnle
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn0 hnle A) hC) hs ENNReal.toReal_nonneg
    (mul_nonneg hC (pow_nonneg hm0 A))

theorem integrableOn_thetaKO : GlobalTheory.Published.SiegelSetUnitary → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (M X : HSp D) (χ χ' : (Formalism.L2.Theta.AE D)ˣ →* Circle) (ω : WRep M X), IsWeil ψ ε M X χ χ' ω →
    ∀ p : ℕ, (∃ τ, Formalism.UG.HasSignature (gramAt D M τ) (M.rank - p) p) → p < M.rank →
    ∀ ν 𝓕, IsHaarFD M ν 𝓕 → ∀ Φ, IsThetaFunO ψ (sgn ε M) X Φ → ∀ τ₀ : D.what₂.Tau,
    (∀ (g : GA D M) (h : GA D X) (S₀ : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec (sgn ε M) S₀ r) (μ' : Measure (Mx D X.rank r))
      (𝓕' : Set (Mx D X.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D X.rank r) μ' 𝓕' →
      ∀ (x : Mx D X.rank r) (i : Fin r), (∀ j, compAt θ τ₀ x j i = 0) → d.mixS X ψ μ' 𝓕' (ω (g, h) Φ) x 0 = 0) →
    ∀ h, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν := by
  intro hRT D ψ θ hθ ε M X χ χ' ω hω p hsig hd ν 𝓕 hν Φ hΦ τ₀ hvan h
  obtain ⟨τ, hτ⟩ := hsig
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D M
  have hν1 := hν.1
  obtain ⟨r, Xf, Yf, hW⟩ := GlobalTheory.SiegelSet.exists_isWittFrame (GlobalTheory.AdelicU.isCMExt_host D) (isHermND_gram M)
  have hr : r ≤ p := GlobalTheory.T.hermitianWittIndex_le_negative_signature M hτ hW
  obtain ⟨K, Ω, c, hK, hΩ, -, hc, -, hcl, hcov, ⟨C₀, hC₀, hconj⟩, hmeas, -, -⟩ :=
    hRT D.host.F D.host.E D.sp.cm.sig (GlobalTheory.AdelicU.isCMExt_host D) M.rank M.gram (isHermND_gram M) r Xf Yf hW
  obtain ⟨-, C₁, hC₁⟩ := hmeas ν hν1
  obtain ⟨B, hB⟩ := theta_le_height ψ θ hθ ε M X χ χ' ω hω Φ hΦ τ₀ hvan r Xf Yf hW Ω C₀ K c hC₀ hK hc hconj h
  have hω' : IsWeilDatumO ψ (sgn ε M) X χ χ' (ω.toSgn ε) := hω
  have hcont : Continuous fun g => thetaKO ω g h Φ :=
    (hω'.om_cont Φ hΦ 0).comp ((continuous_ofSgn_symm ε M).prodMk continuous_const)
  have hinv : ∀ γ ∈ GQ M, ∀ g, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ := fun γ hγ g => by
    have e1 : (((ofSgn ε M).symm (γ * g), h) : GA D (sgn ε M) × GA D X) =
        ((ofSgn ε M).symm γ, 1) * ((ofSgn ε M).symm g, h) := by simp
    show (ω.toSgn ε) ((ofSgn ε M).symm (γ * g), h) Φ 0 = (ω.toSgn ε) ((ofSgn ε M).symm g, h) Φ 0
    rw [e1, map_mul, Module.End.mul_apply]
    exact hω'.om_aut _ (ofSgn_symm_mem_GQ ε hγ) 1 (one_mem _) _ (hω'.om_pres _ _ hΦ)
  set S := GlobalTheory.SiegelSet.siegelSet D.sp.cm.sig M.gram Xf Yf Ω c K with hSdef
  have hSm : MeasurableSet S := hcl.measurableSet
  have hScov : ∀ g, ∃ γ ∈ GQ M, γ * g ∈ S := fun g => by
    obtain ⟨γ, hγ, s, hs, e⟩ := hcov g
    refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
    rw [e, inv_mul_cancel_left]
    exact hs
  have hI := GlobalTheory.T.lintegral_siegelCone_inv_modulus_lt_top_weil D.host.F M.rank r 0 hc (by omega)
  simp only [mul_zero, pow_zero, Finset.prod_const_one, ENNReal.ofReal_one, one_mul] at hI
  have key : ∫⁻ g in 𝓕, ‖thetaKO ω g h Φ‖ₑ ∂ν ≤
      C₁ * (ENNReal.ofReal B * ∫⁻ t in GlobalTheory.SiegelSet.cone r c,
        ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F M.rank t * ∏ i, t i)⁻¹)) := by
    calc ∫⁻ g in 𝓕, ‖thetaKO ω g h Φ‖ₑ ∂ν ≤ ∫⁻ g in S, ‖thetaKO ω g h Φ‖ₑ ∂ν :=
          GlobalTheory.T.lintegral_fundamentalDomain_le_of_meets_all_orbits (GQ M) ν hν.2 hSm hScov hcont.enorm.measurable
            (fun γ hγ g => by rw [hinv γ hγ g])
      _ ≤ C₁ * ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal B *
            ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F M.rank t * ∏ i, t i)⁻¹) :=
          hC₁ (fun g => ‖thetaKO ω g h Φ‖ₑ) (fun _ => ENNReal.ofReal B) measurable_const
            fun q hq t ht a ha k hk => hB q hq t ht a ha k hk
      _ = _ := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ⟨hcont.aestronglyMeasurable, key.trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI))⟩

end GlobalTheory.ThetaCuspInteg

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_integrableOn_fundamentalDomain : GlobalTheory.Published.SiegelSetUnitary → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (M X : HSp D) (χ χ' : (Formalism.L2.Theta.AE D)ˣ →* Circle) (ω : WRep M X), IsWeil ψ ε M X χ χ' ω →
    ∀ p : ℕ, (∃ τ, Formalism.UG.HasSignature (gramAt D M τ) (M.rank - p) p) → p < M.rank →
    ∀ ν 𝓕, IsHaarFD M ν 𝓕 → ∀ Φ, IsThetaFunO ψ (sgn ε M) X Φ → ∀ τ₀ : D.what₂.Tau,
    (∀ (g : GA D M) (h : GA D X) (S₀ : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec (sgn ε M) S₀ r) (μ' : Measure (Mx D X.rank r))
      (𝓕' : Set (Mx D X.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D X.rank r) μ' 𝓕' →
      ∀ (x : Mx D X.rank r) (i : Fin r), (∀ j, compAt θ τ₀ x j i = 0) → d.mixS X ψ μ' 𝓕' (ω (g, h) Φ) x 0 = 0) →
    ∀ h, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν := by
  atlas_forward_decl GlobalTheory.ThetaCuspInteg.integrableOn_thetaKO
end

section
noncomputable section

namespace GlobalTheory.GoodFock

section Ring

open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli Finset

variable {U : Type} [Ring U] [Algebra ℂ U] {n b : ℕ}

def quad (R L : Fin b → Fin n → U) (j k : Fin n) : U := ∑ i, R i j * L i k

theorem glRel_quad (R L : Fin b → Fin n → U) (hR : ∀ i j l k, R i j * R l k = R l k * R i j)
    (hL : ∀ i j l k, L i j * L l k = L l k * L i j)
    (hLR : ∀ i j l k, L i j * R l k = R l k * L i j + if i = l ∧ j = k then 1 else 0) : GlRelR (quad R L) := by
  intro a c e d
  have key : ∀ i l, R i a * L i c * (R l e * L l d) - R l e * L l d * (R i a * L i c) =
      (if i = l ∧ c = e then R i a * L l d else 0) - (if l = i ∧ d = a then R l e * L i c else 0) := by
    intro i l
    have h1 : R i a * L i c * (R l e * L l d) =
        R i a * R l e * (L i c * L l d) + (if i = l ∧ c = e then R i a * L l d else 0) := by
      rw [mul_assoc, ← mul_assoc (L i c), hLR]
      split_ifs <;> simp [mul_add, add_mul, mul_assoc]
    have h2 : R l e * L l d * (R i a * L i c) =
        R l e * R i a * (L l d * L i c) + (if l = i ∧ d = a then R l e * L i c else 0) := by
      rw [mul_assoc, ← mul_assoc (L l d), hLR]
      split_ifs <;> simp [mul_add, add_mul, mul_assoc]
    rw [h1, h2, hR i a l e, hL i c l d]
    abel
  unfold quad
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (f := fun l i => R l e * L l d * (R i a * L i c)),
    ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib, key]
  simp only [Finset.sum_sub_distrib]
  congr 1
  · by_cases h : c = e <;> simp [h]
  · by_cases h : d = a <;> simp [h]

theorem capelli_mem (R L : Fin b → Fin n → U) (hE : GlRelR (quad R L)) (x : Fin n → ℂ) (hx : x ≠ 0) :
    ∃ Q : Fin b → U, capelliC (quad R L) ((n : ℂ) - 1) = ∑ i, (∑ a, x a • R i a) * Q i := by
  obtain ⟨c, hc⟩ := Function.ne_iff.1 hx
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := c.2; omega⟩
  have e : ((m + 1 : ℕ) : ℂ) - 1 = m := by push_cast; ring
  rw [e]
  have h := fun a => capelli_expand_minus (quad R L) hE (m : ℂ) a c
  simp only [sub_self, capEntry, map_zero, ite_self, add_zero] at h
  refine ⟨fun i => (x c)⁻¹ • ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
    (L i d * cminor (quad R L) c.succAbove d.succAbove m), ?_⟩
  have h2 : x c • capelliC (quad R L) m = ∑ a, x a • (if a = c then capelliC (quad R L) m else 0) := by simp
  have h3 : capelliC (quad R L) m = (x c)⁻¹ • (x c • capelliC (quad R L) m) := by
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [h3, h2]
  simp only [← h, mul_smul_comm, ← Finset.smul_sum]
  congr 1
  simp only [quad, Finset.sum_mul, Finset.mul_sum, Finset.smul_sum, mul_smul_comm, smul_mul_assoc, mul_assoc]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => smul_comm _ _ _

theorem comp_prod {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (q : M →ₗ[ℂ] N) :
    ∀ {p : ℕ} (f : Fin p → Module.End ℂ M) (c : Fin p → ℂ), (∀ j, q ∘ₗ f j = c j • q) →
      q ∘ₗ (List.ofFn f).prod = (∏ j, c j) • q
  | 0, f, c, _ => by ext; simp
  | p + 1, f, c, h => by
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, h, LinearMap.smul_comp,
      comp_prod q _ (fun j => c j.succ) (fun j => h j.succ), smul_smul, Fin.prod_univ_succ]

theorem comp_capelli {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (q : M →ₗ[ℂ] N)
    (E : Fin n → Fin n → Module.End ℂ M) (y x : ℂ) (h : ∀ j k, q ∘ₗ E j k = (if j = k then y else 0) • q) :
    q ∘ₗ capelliC E x = (∏ j : Fin n, (y + (x - (j : ℕ)))) • q := by
  have h1 : ∀ z j k, q ∘ₗ capEntry E z j k = (if j = k then y + z else 0) • q := by
    intro z j k
    rw [capEntry, LinearMap.comp_add, h]
    split_ifs
    · ext; simp [Algebra.algebraMap_eq_smul_one, add_smul]
    · simp
  rw [← Matrix.det_diagonal, Matrix.det_apply, Finset.sum_smul]
  unfold capelliC cminor
  ext v
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_zsmul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have := LinearMap.congr_fun (comp_prod q (fun j : Fin n => capEntry E (x - ((j : ℕ) : ℂ)) (id (σ j)) (id j))
    (fun j => if σ j = j then y + (x - (j : ℕ)) else 0) (fun j => h1 _ _ _)) v
  rw [LinearMap.comp_apply] at this
  rw [this, LinearMap.smul_apply, Units.smul_def, smul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · rw [h]
  · rfl

end Ring

section Poly

open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators MvPolynomial

variable {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)

open Classical in
theorem pd_X (v w : Formalism.IndefR.Datum.FVar D b a) (P : PolF D b a) :
    pderiv v (X w * P) = X w * pderiv v P + if v = w then P else 0 := by
  rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
  by_cases h : v = w
  · subst h; simp
  · simp [h, Pi.single_apply, Ne.symm h]

theorem pd_pd (v w : Formalism.IndefR.Datum.FVar D b a) (P : PolF D b a) :
    pderiv v (pderiv w P) = pderiv w (pderiv v P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    rw [mul_comm, pd_X, pd_X, map_add, map_add, pd_X, pd_X, hp]
    split_ifs <;> simp [add_assoc, add_comm, add_left_comm]

theorem rai_rai (i l : Fin b) (j k : Fin a) :
    raiO τ ε ε' i j * raiO τ ε ε' l k = raiO τ ε ε' l k * raiO τ ε ε' i j := by
  refine LinearMap.ext fun P => ?_
  unfold raiO
  by_cases h1 : ε' i = ε j <;> by_cases h2 : ε' l = ε k
  · simp [h1, h2, smul_smul, mul_comm, mul_left_comm, mul_assoc]
  · have : ¬ ((τ, l, k) : Formalism.IndefR.Datum.FVar D b a) = (τ, i, j) := fun e => by
      simp only [Prod.mk.injEq, true_and] at e; exact h2 (e.1 ▸ e.2 ▸ h1)
    simp only [h1, h2, if_true, if_false, Module.End.mul_apply, LinearMap.smul_apply, map_smul, LinearMap.neg_apply,
      map_neg, LinearMap.mulLeft_apply, Derivation.coeFn_coe, pd_X, this, add_zero, smul_smul, mul_comm (sgn (ε k)), smul_neg]
  · have : ¬ ((τ, i, j) : Formalism.IndefR.Datum.FVar D b a) = (τ, l, k) := fun e => by
      simp only [Prod.mk.injEq, true_and] at e; exact h1 (e.1 ▸ e.2 ▸ h2)
    simp only [h1, h2, if_true, if_false, Module.End.mul_apply, LinearMap.smul_apply, map_smul, LinearMap.neg_apply,
      map_neg, LinearMap.mulLeft_apply, Derivation.coeFn_coe, pd_X, this, add_zero, smul_smul, mul_comm (sgn (ε k)), smul_neg]
  · simp only [h1, h2, if_false, Module.End.mul_apply, LinearMap.smul_apply, map_smul, LinearMap.neg_apply,
      map_neg, Derivation.coeFn_coe, smul_smul, mul_comm (sgn (ε k)), smul_neg, pd_pd (τ, i, j)]

theorem low_low (i l : Fin b) (j k : Fin a) :
    lowO τ ε ε' i j * lowO τ ε ε' l k = lowO τ ε ε' l k * lowO τ ε ε' i j := by
  refine LinearMap.ext fun P => ?_
  unfold lowO
  by_cases h1 : ε' i = ε j <;> by_cases h2 : ε' l = ε k
  · simp only [h1, h2, if_true, Module.End.mul_apply, LinearMap.smul_apply, map_smul,
      Derivation.coeFn_coe, smul_smul, mul_comm (sgn (ε k)), pd_pd (τ, i, j)]
  · have : ¬ ((τ, i, j) : Formalism.IndefR.Datum.FVar D b a) = (τ, l, k) := fun e => by
      simp only [Prod.mk.injEq, true_and] at e; exact h2 (e.1 ▸ e.2 ▸ h1)
    simp only [h1, h2, if_true, if_false, Module.End.mul_apply, LinearMap.smul_apply, map_smul,
      LinearMap.mulLeft_apply, Derivation.coeFn_coe, pd_X, this, add_zero, smul_smul, mul_comm (sgn (ε k))]
  · have : ¬ ((τ, l, k) : Formalism.IndefR.Datum.FVar D b a) = (τ, i, j) := fun e => by
      simp only [Prod.mk.injEq, true_and] at e; exact h1 (e.1 ▸ e.2 ▸ h2)
    simp only [h1, h2, if_true, if_false, Module.End.mul_apply, LinearMap.smul_apply, map_smul,
      LinearMap.mulLeft_apply, Derivation.coeFn_coe, pd_X, this, add_zero, smul_smul, mul_comm (sgn (ε k))]
  · simp [h1, h2, smul_smul, mul_comm, mul_left_comm, mul_assoc]

theorem low_rai (i : Fin b) (j : Fin a) (l : Fin b) (k : Fin a) :
    lowO τ ε ε' i j * raiO τ ε ε' l k = raiO τ ε ε' l k * lowO τ ε ε' i j + if i = l ∧ j = k then 1 else 0 := by
  refine LinearMap.ext fun P => ?_
  unfold lowO raiO
  by_cases e : i = l ∧ j = k
  · obtain ⟨rfl, rfl⟩ := e
    by_cases h1 : ε' i = ε j
    · simp only [h1, if_true, Module.End.mul_apply, LinearMap.smul_apply, map_smul, LinearMap.add_apply, and_self,
        LinearMap.mulLeft_apply, Derivation.coeFn_coe, pd_X, smul_smul, GlobalTheory.LieFock.sgn_mul_self, one_smul,
        Module.End.one_apply]
    · simp only [h1, if_true, if_false, Module.End.mul_apply, LinearMap.smul_apply, map_smul, LinearMap.add_apply, and_self,
        LinearMap.mulLeft_apply, Derivation.coeFn_coe, pd_X, smul_smul, GlobalTheory.LieFock.sgn_mul_self, one_smul,
        Module.End.one_apply, LinearMap.neg_apply, map_neg, smul_neg]
      ring
  · have t1 : ¬ ((τ, i, j) : Formalism.IndefR.Datum.FVar D b a) = (τ, l, k) := fun h => e (by simpa using h)
    have t2 : ¬ ((τ, l, k) : Formalism.IndefR.Datum.FVar D b a) = (τ, i, j) := fun h => t1 h.symm
    by_cases h1 : ε' i = ε j <;> by_cases h2 : ε' l = ε k <;>
    simp only [e, h1, h2, if_true, if_false, Module.End.mul_apply, LinearMap.smul_apply, map_smul, LinearMap.neg_apply,
      map_neg, LinearMap.mulLeft_apply, Derivation.coeFn_coe, pd_X, t1, t2, add_zero, smul_smul, mul_comm (sgn (ε k)),
      smul_neg, pd_pd (τ, i, j), mul_left_comm (X (τ, i, j))]

theorem fockS_single (j k : Fin a) : fockS τ ε ε' (Matrix.single j k 1) =
    quad (raiO τ ε ε') (lowO τ ε ε') j k + (if j = k then (b : ℂ) / 2 else 0) • 1 := by
  unfold fockS quad
  rw [Finset.sum_eq_single j, Finset.sum_eq_single k]
  · rw [Matrix.single_apply_same, one_smul, Finset.sum_add_distrib]
    split_ifs
    · rw [← Finset.sum_smul]; simp [div_eq_mul_inv]
    · simp
  · intro c _ hc; simp [Ne.symm hc]
  · simp
  · intro c _ hc; simp [Ne.symm hc]
  · simp

theorem fockS_add_smul (c : ℂ) (N N' : Matrix (Fin a) (Fin a) ℂ) :
    fockS τ ε ε' (N + c • N') = fockS τ ε ε' N + c • fockS τ ε ε' N' := by
  simp only [fockS, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib, Finset.smul_sum,
    mul_smul]

end Poly

section Theta

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.ChainFr GlobalTheory.FockIndep GlobalTheory.OrientedHeis GlobalTheory.MixModel Complex
open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators (raiO lowO fockS)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}

open Classical in

theorem ccr (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr V) (B : Fr W) (k l : FVar D W.rank V.rank)
    {g : WO V W → ℂ} (hg : IsThetaFunO ψ V W g) :
    annih (heisO ψ V W) θ k.1 (cplxO (A.cart k.1) (B.cart k.1)) (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2)
      (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l g) =
    aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l
      (annih (heisO ψ V W) θ k.1 (cplxO (A.cart k.1) (B.cart k.1)) (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2) g) +
      (if k = l then -(fockScale D k.1 : ℂ) else 0) • g := by
  have hS := GlobalTheory.ChainFr.Model.isCartanInv_cart A
  have hT := GlobalTheory.ChainFr.Model.isCartanInv_cart B
  obtain ⟨τ, a, b⟩ := k
  obtain ⟨τ', c, d⟩ := l
  refine (GlobalTheory.FockIndep.annih_aPlus hψ hθ τ _ hS hT τ' _ hg).trans ?_
  refine congrArg₂ (· + ·) rfl (congrArg (· • g) ?_)
  unfold omDir
  by_cases h : τ = τ'
  · subst h
    have gA : (A.onb τ)ᴴ * gramAt D V τ * A.onb τ = diagonal fun a => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (A.ε τ a) :=
      GlobalTheory.LieFock.gram_onb (GlobalTheory.LieFock.fr_det A τ) (A.fr_gram τ)
    have gB : (B.onb τ)ᴴ * gramAt D W τ * B.onb τ = diagonal fun a => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (B.ε τ a) :=
      GlobalTheory.LieFock.gram_onb (GlobalTheory.LieFock.fr_det B τ) (B.fr_gram τ)
    simp only [if_true, GlobalTheory.FockVecInj.cplxO_unitMap (B := A.onb τ) (isUnit_nonsing_inv_det _ (GlobalTheory.LieFock.fr_det A τ))
      (GlobalTheory.LieFock.cart_onb A τ) (GlobalTheory.LieFock.cart_onb B τ),
      Matrix.mul_smul, Matrix.trace_smul, GlobalTheory.FockVecInj.trace_unitMap (fun a => GlobalTheory.LieFock.sgn_mul_self _) gA gB,
      Prod.mk.injEq, true_and]
    have hre := GlobalTheory.RealSymplForm.realPlace_imaginaryGenerator_re_eq_zero D τ
    have h1 := GlobalTheory.VacuumFockLaws.fockScale_sq (D := D) τ
    have h2 := GlobalTheory.VacuumFockLaws.fockScale_ne (D := D) τ
    by_cases e : a = c ∧ b = d
    · rw [if_pos e, if_pos e, inv_mul_eq_iff_eq_mul₀ h2, mul_neg, h1]
      unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn
      split_ifs <;> simp [hre] <;> ring_nf <;> simp only [I_sq] <;> ring1
    · simp [e]
  · simp [h]

theorem annih_ptF (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr V) (B : Fr W) {f : WO V W → ℂ}
    (hf : IsVacF ψ θ A B f) (k : FVar D W.rank V.rank) (P : PolF D W.rank V.rank) :
    annih (heisO ψ V W) θ k.1 (cplxO (A.cart k.1) (B.cart k.1)) (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2)
      (ptF ψ θ A B f P) = (-(fockScale D k.1 : ℂ)) • ptF ψ θ A B f (MvPolynomial.pderiv k P) := by
  classical
  have hS := GlobalTheory.ChainFr.Model.isCartanInv_cart A
  have hT := GlobalTheory.ChainFr.Model.isCartanInv_cart B
  have h := GlobalTheory.ArchRec.DerFock.pure_deriv (P := IsThetaFunO ψ V W)
    (A := aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb)
    (B := annih (heisO ψ V W) θ k.1 (cplxO (A.cart k.1) (B.cart k.1)) (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2))
    (fun _ _ => theta_add) (fun a _ => theta_smul a) (fun _ _ h => aPlus_theta hψ hθ _ _ _ h)
    (fun i j _ h => aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h)
    (fun _ _ _ h h' => aPlus_add hψ hθ _ _ _ h h') (fun _ a _ h => aPlus_smul hψ hθ _ _ _ a h)
    (fun _ _ h h' => annih_add hψ hθ _ _ _ h h') (fun a _ h => annih_smul hψ hθ _ _ _ a h)
    (fun j g h => ccr hψ hθ A B k j h) hf.1 (hf.2 k.1 _) P
  refine h.trans ?_
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_smul]
  rfl

theorem ptF_raiO (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr V) (B : Fr W) {f : WO V W → ℂ}
    (hf : IsVacF ψ θ A B f) (τ : D.what₂.Tau) (i : Fin W.rank) (j : Fin V.rank) (P : PolF D W.rank V.rank) :
    ptF ψ θ A B f (raiO τ (A.ε τ) (B.ε τ) i j P) = GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (A.ε τ j) •
      aPlus (heisO ψ V W) θ τ (cplxO 1 1) (unitMap (A.onb τ) (B.onb τ) i j) (ptF ψ θ A B f P) := by
  have hu := GlobalTheory.LieFock.cplxO_unit A B τ i j
  have lin : ∀ (c : ℂ) Q, ptF ψ θ A B f (c • Q) = c • ptF ψ θ A B f Q := fun c Q => by
    unfold ptF; exact map_smul _ _ _
  unfold raiO
  by_cases hp : B.ε τ i = A.ε τ j
  · rw [if_pos hp, one_smul] at hu
    rw [if_pos hp, LinearMap.smul_apply, LinearMap.mulLeft_apply, lin, GlobalTheory.FockAdjoint.ptF_X_mul hψ hθ A B hf.1]
    simp only [aPlus, crea, hu, GlobalTheory.FockBaseChange.cplxO_one]
  · rw [if_neg hp, neg_one_smul, ← neg_smul] at hu
    have h := annih_ptF hψ hθ A B hf (τ, i, j) P
    have hg := GlobalTheory.FockAdjoint.ptF_theta hψ hθ A B hf.1 P
    have h2 := GlobalTheory.VacuumFockLaws.fockScale_ne (D := D) τ
    have hn : Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ ((-I) • unitMap (A.onb τ) (B.onb τ) i j) (ptF ψ θ A B f P) =
        -Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (I • unitMap (A.onb τ) (B.onb τ) i j) (ptF ψ θ A B f P) := by
      have := GlobalTheory.FockBaseChange.dRho_dir_smul hψ hθ τ (-1) (I • unitMap (A.onb τ) (B.onb τ) i j) hg
      simpa only [ofReal_neg, ofReal_one, neg_smul, one_smul] using this
    simp only [annih, hu, hn] at h
    rw [if_neg hp, LinearMap.smul_apply, LinearMap.neg_apply, lin, ← neg_one_smul ℂ, lin]
    simp only [aPlus, crea, GlobalTheory.FockBaseChange.cplxO_one, Derivation.coeFn_coe]
    congr 1
    rw [sub_eq_add_neg, ← smul_neg, h, smul_smul, mul_neg, inv_mul_cancel₀ h2]

def Killed (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (τ : D.what₂.Tau) (V W : HSp D) (Φ : WO V W → ℂ) : Prop :=
  ∀ v : Fin V.rank → ℂ, v ≠ 0 → Φ ∈ Submodule.span ℂ
    {F | ∃ w Ψ, IsThetaFunO ψ V W Ψ ∧ F = Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (vecMulVec w v) Ψ}

theorem killed_capelli (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr V) (B : Fr W) {f : WO V W → ℂ}
    (hf : IsVacF ψ θ A B f) (τ : D.what₂.Tau) (P : PolF D W.rank V.rank) :
    Killed ψ θ τ V W (ptF ψ θ A B f (capelliC (quad (raiO τ (A.ε τ) (B.ε τ)) (lowO τ (A.ε τ) (B.ε τ)))
      ((V.rank : ℂ) - 1) P)) := by
  intro v hv
  have hd : IsUnit (A.onb τ).det := isUnit_nonsing_inv_det _ (GlobalTheory.LieFock.fr_det A τ)
  have hy : v ᵥ* A.onb τ ᵥ* (A.onb τ)⁻¹ = v := by rw [vecMul_vecMul, mul_nonsing_inv _ hd, vecMul_one]
  obtain ⟨Q, hQ⟩ := capelli_mem (raiO τ (A.ε τ) (B.ε τ)) (lowO τ (A.ε τ) (B.ε τ))
    (glRel_quad _ _ (fun i j l k => rai_rai τ _ _ i l j k) (fun i j l k => low_low τ _ _ i l j k) (low_rai τ _ _))
    (fun a => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (A.ε τ a) * (v ᵥ* A.onb τ) a) (fun h => hv (by
      have : v ᵥ* A.onb τ = 0 := funext fun a => by
        have := congrArg (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (A.ε τ a) * ·) (congrFun h a)
        simpa [← mul_assoc, GlobalTheory.LieFock.sgn_mul_self] using this
      rw [← hy, this, zero_vecMul]))
  rw [hQ]
  have e : ptF ψ θ A B f ((∑ i, (∑ a, (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (A.ε τ a) * (v ᵥ* A.onb τ) a) • raiO τ (A.ε τ) (B.ε τ) i a) *
      Q i) P) = ∑ i, ∑ a, (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (A.ε τ a) * (v ᵥ* A.onb τ) a) •
        ptF ψ θ A B f (raiO τ (A.ε τ) (B.ε τ) i a (Q i P)) := by
    unfold ptF
    simp only [LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply, map_sum, map_smul]
  rw [e]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hg := GlobalTheory.FockAdjoint.ptF_theta hψ hθ A B hf.1 (Q i P)
  have e2 : ∑ a, (v ᵥ* A.onb τ) a • unitMap (A.onb τ) (B.onb τ) i a = vecMulVec (fun r => B.onb τ r i) v := by
    have : ∑ a, (v ᵥ* A.onb τ) a • Matrix.single i a (1 : ℂ) = vecMulVec (Pi.single i 1) (v ᵥ* A.onb τ) := by
      ext r s
      by_cases h : i = r
      · subst h; simp [Matrix.sum_apply, vecMulVec_apply, Matrix.single_apply]
      · simp [Matrix.sum_apply, vecMulVec_apply, h, Pi.single_apply, Ne.symm h]
    have e4 : ∑ a, (v ᵥ* A.onb τ) a • unitMap (A.onb τ) (B.onb τ) i a =
        B.onb τ * (∑ a, (v ᵥ* A.onb τ) a • Matrix.single i a (1 : ℂ)) * (A.onb τ)⁻¹ := by
      simp only [unitMap, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [e4, this, mul_vecMulVec, vecMulVec_mul, hy, mulVec_single_one]
    rfl
  have e3 : ∑ a, (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (A.ε τ a) * (v ᵥ* A.onb τ) a) •
      ptF ψ θ A B f (raiO τ (A.ε τ) (B.ε τ) i a (Q i P)) =
      aPlus (heisO ψ V W) θ τ (cplxO 1 1) (vecMulVec (fun r => B.onb τ r i) v) (ptF ψ θ A B f (Q i P)) := by
    rw [← e2, GlobalTheory.FockBaseChange.aPlus_dir_sum hψ hθ τ _ _ hg]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [GlobalTheory.FockBaseChange.aPlus_dir_smul hψ hθ τ _ _ hg, ptF_raiO hψ hθ A B hf, smul_smul, mul_right_comm,
      GlobalTheory.LieFock.sgn_mul_self, one_mul]
  rw [e3, aPlus, crea, GlobalTheory.FockBaseChange.cplxO_one, ← smul_vecMulVec]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨_, _, hg, rfl⟩)
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, hg, rfl⟩)))

theorem Killed.om {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    (hom : IsWeilDatumO ψ V W χS χT om) (hθ : IsInfFam θ) {τ : D.what₂.Tau} {Φ : WO V W → ℂ} (h : Killed ψ θ τ V W Φ)
    (g : GA D V) (k : GA D W) : Killed ψ θ τ V W (om (g, k) Φ) := by
  intro v hv
  have e : compAt θ τ (mt V g) * compAt θ τ (mt V g⁻¹) = 1 := by
    rw [← GlobalTheory.OrientedHeis.compAt_mul]
    have : HMul.hMul (mt V g) (mt V g⁻¹) = (1 : Matrix _ _ (Formalism.L2.Theta.AE D)) := g.1.mul_inv
    rw [this]
    exact Matrix.map_one _ (by simp) (by simp)
  have hy : v ᵥ* compAt θ τ (mt V g) ᵥ* compAt θ τ (mt V g⁻¹) = v := by rw [vecMul_vecMul, e, vecMul_one]
  have h1 := Submodule.mem_map_of_mem (f := om (g, k)) (h (v ᵥ* compAt θ τ (mt V g)) fun h0 => hv (by
    rw [← hy, h0, zero_vecMul]))
  rw [Submodule.map_span] at h1
  refine Submodule.span_mono ?_ h1
  rintro _ ⟨_, ⟨w, Ψ, hΨ, rfl⟩, rfl⟩
  refine ⟨compAt θ τ (mt W k) *ᵥ w, om (g, k) Ψ, hom.om_pres _ _ hΨ, ?_⟩
  rw [GlobalTheory.OrientedHeis.om_dRho hom hθ g k τ _ hΨ, mul_vecMulVec, vecMulVec_mul, hy]

theorem mixS_dRho (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ)
    (v : GlobalTheory.Unf.VolM D W.rank ρ) (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin ρ) ℂ) {f : WO V W → ℂ}
    (hf : IsThetaFunO ψ V W f) (x : Mx D W.rank ρ) (hx : ((compAt θ τ x)ᴴ * gramAt D W τ * z).trace = 0) :
    d.mixS W ψ v.μ v.𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (z * compAt θ τ d.pY) f) x 0 = 0 := by
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt (m := W.rank) (n := ρ) hθ τ z
  have hL' : IsLineAt θ τ (z * compAt θ τ d.pY) ((d.extY W).comp (lineAt θ τ z)) := by
    refine ⟨?_, fun t => ?_, fun t τ' => ?_⟩
    · exact hL.1.matrix_mul continuous_const
    · show ((lineAt θ τ z t) * d.pY).map (finPart D) = 0
      rw [Matrix.map_mul, hL.2.1 t, Matrix.zero_mul]
    · show compAt θ τ' ((lineAt θ τ z t) * d.pY) = _
      rw [GlobalTheory.OrientedHeis.compAt_mul, hL.2.2 t τ']
      split_ifs with h
      · subst h
        rw [Matrix.smul_mul]
      · rw [Matrix.zero_mul]
  have hline := GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ hL' (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ _)
  have hline' : ∀ t, d.extY W (lineAt θ τ z t) = lineAt θ τ (z * compAt θ τ d.pY) t := fun t => by
    rw [← hline]; rfl
  have hder := GlobalTheory.T.hasDerivAt_mixedModelSource_dualLine_linearForm D ψ hψ θ hθ V V₀ W ρ d v f hf (lineAt θ τ z) hL.1 hL.2.1 x 0
  have hfun : (fun p => deriv (fun t : ℝ => heisO ψ V W (d.extY W (lineAt θ τ z t)) f p) 0) =
      Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (z * compAt θ τ d.pY) f := by
    funext p
    simp only [hline']
    rfl
  rw [hfun] at hder
  have hphase : ∀ t : ℝ, ψ (symplO V W (d.extX W x) (d.extY W (lineAt θ τ z t))) = 1 := by
    intro t
    have e := GlobalTheory.ThetaDecay.psi_symplOH_lineAt hψ hθ (GlobalTheory.Size.posSp D ρ) W x τ z t
    have e2 : symplOH V W (d.extX W x) (d.extY W (lineAt θ τ z t)) =
        symplOH (GlobalTheory.Size.posSp D ρ) W x (lineAt θ τ z t) := by
      rw [d.symplOH_extX_extY]
      exact (congrArg (trHalf D) (GlobalTheory.Unf.hO_posSp D W ρ x _)).symm
    have e3 : ψ (symplOH V W (d.extX W x) (d.extY W (lineAt θ τ z t))) =
        Complex.exp ((Real.pi * Complex.I) *
          ((t * GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D ρ) W τ z (compAt θ τ x) : ℝ) : ℂ)) := by
      rw [e2]; exact e
    have hs : GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt (GlobalTheory.Size.posSp D ρ) W τ z (compAt θ τ x) = 0 :=
      (GlobalTheory.Unf.symplAt_posSp D W ρ τ z (compAt θ τ x)).trans (by rw [hx]; simp)
    rw [GlobalTheory.Unf.symplO_eq_two_half, AddChar.map_add_eq_mul, e3, hs]
    simp
  simp only [hphase] at hder
  exact hder.unique (hasDerivAt_const _ _)

theorem Killed.mixS_eq_zero (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {τ : D.what₂.Tau} {Φ : WO V W → ℂ}
    (h : Killed ψ θ τ V W Φ) {V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {μ : Measure (Mx D W.rank ρ)}
    {𝓕 : Set (Mx D W.rank ρ)} (hμ : IsCovolOne (ratMx D W.rank ρ) μ 𝓕) (x : Mx D W.rank ρ) (i : Fin ρ)
    (hx : ∀ j, compAt θ τ x j i = 0) : d.mixS W ψ μ 𝓕 Φ x 0 = 0 := by
  have e : compAt θ τ d.pY * compAt θ τ d.jY = 1 := by
    rw [← GlobalTheory.OrientedHeis.compAt_mul]
    have : HMul.hMul d.pY d.jY = (1 : Matrix _ _ (Formalism.L2.Theta.AE D)) := d.pY_jY
    rw [this]
    exact Matrix.map_one _ (by simp) (by simp)
  have hv : Pi.single i 1 ᵥ* compAt θ τ d.pY ≠ 0 := fun h0 => by
    have := congrArg (· ᵥ* compAt θ τ d.jY) h0
    simp only [vecMul_vecMul, e, vecMul_one, zero_vecMul] at this
    simpa using congrFun this i
  let v : GlobalTheory.Unf.VolM D W.rank ρ := ⟨μ, 𝓕, hμ⟩
  suffices H : IsThetaFunO ψ V W Φ ∧ d.mixS W ψ v.μ v.𝓕 Φ x 0 = 0 from H.2
  refine Submodule.span_induction (p := fun F _ => IsThetaFunO ψ V W F ∧ d.mixS W ψ v.μ v.𝓕 F x 0 = 0)
    ?_ ?_ ?_ ?_ (h _ hv)
  · rintro _ ⟨w, Ψ, hΨ, rfl⟩
    refine ⟨theta_dRho hθ hψ τ _ hΨ, ?_⟩
    rw [← vecMulVec_mul]
    refine mixS_dRho hψ hθ d v τ _ hΨ x ?_
    rw [mul_vecMulVec, trace_vecMulVec, dotProduct_single_one, ← mulVec_mulVec]
    simp [mulVec, dotProduct, hx]
  · exact ⟨theta_zero, by simp [HypDec.mixS, heisO]⟩
  · intro F G _ _ hF hG
    exact ⟨theta_add hF.1 hG.1, by rw [GlobalTheory.Unf.DoubleSum.mixS_add d v hψ hF.1 hG.1, Pi.add_apply, hF.2, hG.2, add_zero]⟩
  · intro c F _ hF
    exact ⟨theta_smul c hF.1, by rw [GlobalTheory.Unf.DoubleSum.mixS_smul d v, Pi.smul_apply, hF.2, smul_zero]⟩

end Theta

section Quot

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Matrix GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.RealQuot Complex
open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators (raiO lowO fockS)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_lie_parts {n : ℕ} (ε : Fin n → Bool) (N : Matrix (Fin n) (Fin n) ℂ) :
    ∃ Y₁ Y₂ : Matrix (Fin n) (Fin n) ℂ, Y₁ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * Y₁ = 0 ∧
      Y₂ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * Y₂ = 0 ∧
      N = Y₁.map (starRingEnd ℂ) + I • Y₂.map (starRingEnd ℂ) ∧ Y₁.trace + I * Y₂.trace = -N.trace := by
  let s : Fin n → ℂ := fun a => GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε a)
  have hs : ∀ a, s a * s a = 1 := fun a => GlobalTheory.LieFock.sgn_mul_self _
  have hc : ∀ a, starRingEnd ℂ (s a) = s a := fun a => GlobalTheory.LieFock.conj_sgn _
  have h2 : starRingEnd ℂ 2 = 2 := map_ofNat _ 2
  refine ⟨Matrix.of fun i j => (starRingEnd ℂ (N i j) - s i * N j i * s j) / 2,
    Matrix.of fun i j => I * (starRingEnd ℂ (N i j) + s i * N j i * s j) / 2, ?_, ?_, ?_, ?_⟩
  · ext i j
    simp only [GlobalTheory.LieFock.Jm_eq, Matrix.add_apply, mul_diagonal, diagonal_mul, conjTranspose_apply, of_apply,
      Matrix.zero_apply, ← starRingEnd_apply, map_div₀, map_sub, map_mul, conj_conj, hc, h2]
    linear_combination (-(s i) * starRingEnd ℂ (N i j) / 2) * hs j - (N j i * s j / 2) * hs i
  · ext i j
    simp only [GlobalTheory.LieFock.Jm_eq, Matrix.add_apply, mul_diagonal, diagonal_mul, conjTranspose_apply, of_apply,
      Matrix.zero_apply, ← starRingEnd_apply, map_div₀, map_add, map_mul, conj_conj, hc, h2, conj_I]
    linear_combination (-I * (s i) * starRingEnd ℂ (N i j) / 2) * hs j + (I * N j i * s j / 2) * hs i
  · ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, map_apply, of_apply, smul_eq_mul, map_div₀, map_add, map_sub, map_mul,
      conj_conj, hc, h2, conj_I]
    linear_combination ((N i j + s i * starRingEnd ℂ (N j i) * s j) / 2) * I_mul_I
  · simp only [Matrix.trace, diag_apply, of_apply, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    linear_combination ((starRingEnd ℂ (N i i) + s i * N i i * s i) / 2) * I_mul_I - N i i * hs i

variable {D : D7} {M X : HSp D}

def sgA (A : Fr M) (τ : D.what₂.Tau) : Fin M.rank → Bool := (frSgn false A).ε τ

theorem comp_quad (A : Fr M) (B : Fr X) (eT : D.what₂.Tau → ℚ) (τ : D.what₂.Tau) {N : Type} [AddCommGroup N] [Module ℂ N]
    (q : PolF D X.rank M.rank →ₗ[ℂ] N) (hq : ∀ P ∈ coinv false A B eT, q P = 0) (j k : Fin M.rank) :
    q ∘ₗ quad (raiO τ (sgA A τ) (B.ε τ)) (lowO τ (sgA A τ) (B.ε τ)) j k =
      (if j = k then -((X.rank : ℂ) / 2 + eT τ) else 0) • q := by
  have hd := GlobalTheory.LieFock.fr_det A τ
  have key : ∀ Y : Matrix (Fin M.rank) (Fin M.rank) ℂ, Yᴴ * Formalism.REAL.Jm (A.ε τ) + Formalism.REAL.Jm (A.ε τ) * Y = 0 →
      ∀ P, q (fockS τ (sgA A τ) (B.ε τ) (Y.map (starRingEnd ℂ)) P) = ((eT τ : ℂ) * Y.trace) • q P := by
    intro Y hY P
    have hZ : (A.fr τ)⁻¹ * Y * A.fr τ ∈ lieAt M τ := by
      show _ * gramAt D M τ + gramAt D M τ * _ = 0
      rw [← A.fr_gram τ]
      have h1 : ((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ = 1 := by rw [← conjTranspose_mul, mul_nonsing_inv _ hd, conjTranspose_one]
      calc _ = (A.fr τ)ᴴ * (Yᴴ * (((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ) * Formalism.REAL.Jm (A.ε τ) +
            Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) * Y) * A.fr τ := by
            simp only [conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        _ = 0 := by rw [h1, mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_one, hY, Matrix.mul_zero, Matrix.zero_mul]
    have h := hq _ (Submodule.subset_span ⟨τ, _, hZ, P, rfl⟩)
    have e1 : A.fr τ * ((A.fr τ)⁻¹ * Y * A.fr τ) * (A.fr τ)⁻¹ = Y := by
      rw [Matrix.mul_assoc _ Y, mul_nonsing_inv_cancel_left _ _ hd, mul_nonsing_inv_cancel_right _ _ hd]
    have e2 : ((A.fr τ)⁻¹ * Y * A.fr τ).trace = Y.trace := by
      rw [trace_mul_cycle, mul_nonsing_inv _ hd, Matrix.one_mul]
    rw [actS, e1, e2, LinearMap.sub_apply, map_sub, LinearMap.smul_apply, Module.End.one_apply, map_smul] at h
    exact sub_eq_zero.1 h
  obtain ⟨Y₁, Y₂, h1, h2, h3, h4⟩ := exists_lie_parts (A.ε τ) (Matrix.single j k 1)
  refine LinearMap.ext fun P => ?_
  have h5 : q (fockS τ (sgA A τ) (B.ε τ) (Matrix.single j k 1) P) =
      (-((eT τ : ℂ) * (Matrix.single j k (1 : ℂ)).trace)) • q P := by
    conv_lhs => rw [h3, fockS_add_smul]
    rw [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, key _ h1, key _ h2, smul_smul, ← add_smul,
      ← mul_neg, ← h4]
    congr 1
    ring
  rw [fockS_single, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul,
    ← eq_sub_iff_add_eq, ← sub_smul] at h5
  rw [LinearMap.comp_apply, LinearMap.smul_apply, h5]
  congr 1
  split_ifs with h
  · subst h; rw [trace_single_eq_same]; ring
  · rw [trace_single_eq_of_ne _ _ _ h]; ring

end Quot

section Main

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.ChainFr MeasureTheory

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators (raiO lowO)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

theorem exists_good_polynomial : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (a b : D.what₂.Tau → ℚ),
  ∃ P' : PolF D X.rank W₁.rank, ∀ α β : (AE D)ˣ →* Circle, IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
    ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' → ∀ f, IsFinF ψ θ false A₁ B f →
      (∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), IsHaarFD W₁ ν₁ 𝓕₁ → ∀ h, IntegrableOn (fun g => thetaKO ωB g h (fockF ψ θ false A₁ B f P')) 𝓕₁ ν₁) ∧
      (p' (fockF ψ θ false A₁ B f P') = 0 → ∀ P'', p' (fockF ψ θ false A₁ B f P'') = 0) := by
  intro hP hK hM D ψ θ hψ hθ W W₁ X A A₁ B a b
  obtain ⟨Pr, q, q', -, hq', hLM⟩ := GlobalTheory.T.local_matching_of_howe_duality hP.howeDualityReal hP hK hM D ψ θ hψ hθ W W₁ X A A₁ B a b
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  obtain ⟨P₀, hP₀⟩ : ∃ P₀, q' P₀ = 0 → ∀ P, q' P = 0 := by
    by_cases h : ∃ P₀, q' P₀ ≠ 0
    · exact h.imp fun _ h h' => absurd h' h
    · push_neg at h
      exact ⟨0, fun _ => h⟩
  refine ⟨capelliC (quad (raiO τ (sgA A₁ τ) (B.ε τ)) (lowO τ (sgA A₁ τ) (B.ε τ)))
    ((W₁.rank : ℂ) - 1) P₀, fun α β htr hexp ωA ωB Pi rf rl p p' hm f hf => ⟨fun ν₁ 𝓕₁ hν => ?_, fun h0 P'' => ?_⟩⟩
  · obtain ⟨p₀, q₀, hsig, -, hlt⟩ := htr.sig
    have hW : IsWeilDatumO ψ (GlobalTheory.Grid.sgn false W₁) X α (α / β) (ωB.toSgn false) := hm.weilB
    have hk := killed_capelli hψ hθ (frSgn false A₁) B hf τ P₀
    refine GlobalTheory.T.thetaKernel_integrableOn_fundamentalDomain hP.siegelSetUnitary D ψ θ hθ false W₁ X _ _ ωB hm.weilB q₀ ⟨τ, (hsig τ).2.1⟩ (by omega) ν₁ 𝓕₁ hν _
      (GlobalTheory.FockAdjoint.ptF_theta hψ hθ (frSgn false A₁) B hf.1 _) τ fun g h S₀ r d μ' 𝓕' hμ x i hx => ?_
    have := (hk.om hW hθ ((GlobalTheory.Grid.ofSgn false W₁).symm g) h).mixS_eq_zero hψ hθ d hμ x i hx
    exact this
  · have hexpB : ∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D (α / β) τ (a τ - b τ) :=
      fun τ => ⟨(hexp τ).1, GlobalTheory.RealQuot.hasInfExp_div D β α τ _ _ (hexp τ).2 (hexp τ).1⟩
    obtain ⟨-, hco, -⟩ := GlobalTheory.RealQuot.oriented_maps D ψ θ hθ false W₁ X A₁ B α (α / β) ωB a (fun τ => a τ - b τ)
      hm.weilB hexpB Pi rf rl p' hm.mapB
    have hc := LinearMap.congr_fun (comp_capelli (p' ∘ₗ fockF ψ θ false A₁ B f) _ _ ((W₁.rank : ℂ) - 1)
      (comp_quad A₁ B (fun τ => a τ - b τ) τ _ (hco f hf))) P₀
    obtain ⟨a', b', ha', hb', hgap⟩ := htr.gap τ
    rw [Formalism.L2.Fam.ThC.expU D α τ _ _ ha' (hexp τ).1, Formalism.L2.Fam.ThC.expU D β τ _ _ hb' (hexp τ).2] at hgap
    have hne : (∏ j : Fin W₁.rank, (-((X.rank : ℂ) / 2 + ((a τ - b τ : ℚ) : ℂ)) + ((W₁.rank : ℂ) - 1 - (j : ℕ)))) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun j _ h => ?_
      have hj : ((j : ℕ) : ℚ) + 1 ≤ W₁.rank := by exact_mod_cast j.2
      have h' : (-((X.rank : ℚ) / 2 + (a τ - b τ)) + ((W₁.rank : ℚ) - 1 - (j : ℕ))) = 0 := by
        refine Rat.cast_injective (α := ℂ) ?_
        push_cast at h ⊢
        exact h
      linarith
    have h1 : p' (fockF ψ θ false A₁ B f P₀) = 0 := (smul_eq_zero.1 (hc.symm.trans h0)).resolve_left hne
    obtain ⟨Pf, r, r', e, -, -, -, he⟩ := (hLM α β htr hexp).2 ωA ωB Pi rf rl p p' hm
    rw [he f hf] at h1 ⊢
    by_cases hz : q' P₀ = 0
    · rw [hP₀ hz, TensorProduct.zero_tmul, map_zero]
    · have h2 : q' P₀ ⊗ₜ[ℂ] r' f = 0 := e.injective (h1.trans (map_zero e).symm)
      obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hz
      have h3 := congrArg (fun x => TensorProduct.lid ℂ Pf (LinearMap.rTensor Pf l x)) h2
      have h4 : r' f = 0 := by simpa [hl] using h3
      rw [h4, TensorProduct.tmul_zero, map_zero]

end Main

end GlobalTheory.GoodFock

end
end
