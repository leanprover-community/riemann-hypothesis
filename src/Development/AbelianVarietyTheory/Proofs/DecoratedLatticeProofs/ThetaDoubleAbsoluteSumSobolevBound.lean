import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateDecayRealEntriesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TsumAdelicMatrixSchwartzMajorantRationalNeTopStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctionsStatement
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelHeisenbergPhaseEqCexpRealPoints
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupNormWordSumSubLeAndDerivativeCost
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactAnnihilatorFiniteAdelesStdChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartEqSumTraceTraceDualBasis

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.CharDecay

open GlobalTheory.OrientedHeis Filter Topology

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem line_move (hθ : IsInfFam θ) {k l m n : ℕ} (P : Mx D k m) (Q : Mx D n l) (τ : D.what₂.Tau)
    (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    lineAt θ τ (compAt θ τ P ⬝ z ⬝ compAt θ τ Q) t = (P ⬝ lineAt θ τ z t ⬝ Q : Mx D k l) := by
  have hL := isLineAt_lineAt hθ τ z
  let L : ℝ →+ Mx D k l :=
    { toFun := fun t => P ⬝ lineAt θ τ z t ⬝ Q
      map_zero' := by rw [AddMonoidHom.map_zero, Matrix.mul_zero, Matrix.zero_mul]
      map_add' := fun s t => by rw [AddMonoidHom.map_add, Matrix.mul_add, Matrix.add_mul] }
  have hL' : IsLineAt θ τ (compAt θ τ P ⬝ z ⬝ compAt θ τ Q) L := by
    refine ⟨(continuous_const.matrix_mul hL.1).matrix_mul continuous_const, fun t => ?_, fun t τ' => ?_⟩
    · show (P ⬝ lineAt θ τ z t ⬝ Q : Mx D k l).map (finPart D) = 0
      rw [Matrix.map_mul, Matrix.map_mul, hL.2.1, Matrix.mul_zero, Matrix.zero_mul]
    · show compAt θ τ' (P ⬝ lineAt θ τ z t ⬝ Q : Mx D k l) = _
      rw [compAt_mul, compAt_mul, hL.2.2]
      split_ifs with e
      · rw [e, Matrix.mul_smul, Matrix.smul_mul]
      · rw [Matrix.mul_zero, Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (isLineAt_lineAt hθ τ _) hL']
  rfl

theorem phase_real (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {m n : ℕ} (y : Mx D n m) (κ : Mx D m n)
    (hκ : κ.map (finPart D) = 0) :
    ψ (-(Algebra.trace (AF D.host.F) (AE D) (y ⬝ κ).trace)) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((∑ τ, 2 * (Matrix.trace (compAt θ τ y ⬝ compAt θ τ κ)).re : ℝ) : ℂ)) := by
  set t := Matrix.trace (y ⬝ κ) with ht
  have hfin : finPart D t = 0 := GlobalTheory.PhaseReal.finPart_trace _ κ hκ
  have hT := GlobalTheory.PhaseReal.trace_real hfin
  set R := Algebra.trace (AF D.host.F) (AE D) t with hR
  have h1 : ψ (-R) = psiInf D.host.F ψ (-(fstA D.host.F R)) := by
    unfold psiInf
    congr 1
    rw [hT]
    refine Prod.ext rfl ?_
    exact neg_zero
  have h2 := hψ.2.2 θ hθ (-(fstA D.host.F R))
  have h4 : ∀ ρ, θ ρ (infPart D t) = Matrix.trace (compAt θ ρ y ⬝ compAt θ ρ κ) := fun ρ => by
    simp only [ht, Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply, compAt]
  have h3 : ∀ ρ, θ ρ ((-(fstA D.host.F R)) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      -((2 * (Matrix.trace (compAt θ ρ y ⬝ compAt θ ρ κ)).re : ℝ) : ℂ) := by
    intro ρ
    rw [TensorProduct.neg_tmul, map_neg, hR, GlobalTheory.PhaseReal.theta_trace θ hθ ρ t, h4]
  rw [h1, h2]
  congr 1
  simp only [h3, Finset.sum_neg_distrib]
  push_cast
  ring

theorem phase_line (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {m n : ℕ} (y : Mx D n m) (τ : D.what₂.Tau)
    (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    ψ (-(Algebra.trace (AF D.host.F) (AE D) (y ⬝ lineAt θ τ z t).trace)) =
      Complex.exp (((4 * Real.pi * (Matrix.trace (compAt θ τ y ⬝ z)).re * t : ℝ) : ℂ) * Complex.I) := by
  have hL := isLineAt_lineAt hθ τ z
  rw [phase_real hψ hθ y _ (hL.2.1 t), Finset.sum_eq_single τ (fun τ' _ e => by
    rw [hL.2.2, if_neg e, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re, mul_zero]) (by simp), hL.2.2, if_pos rfl,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  congr 1
  push_cast
  ring

theorem deriv_char (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (ℓ : (WO S T → ℂ) → ℂ)
    (hadd : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ℓ (f + g) = ℓ f + ℓ g)
    (hsmul : ∀ (c : ℂ) f, IsThetaFunO ψ S T f → ℓ (c • f) = c * ℓ f)
    (hb : ∀ f, IsThetaFunO ψ S T f → ‖ℓ f‖ₑ ≤ ⨆ w, ‖f w‖ₑ) {L : ℝ →+ WO S T} (hL : IsRealDir T S L) (a : ℝ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (h : ∀ t : ℝ, ℓ (heisO ψ S T (L t) f) = Complex.exp (((a * t : ℝ) : ℂ) * Complex.I) * ℓ f) :
    ℓ (dLine ψ S T L f) = (a : ℂ) * Complex.I * ℓ f := by
  have hsub : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ℓ (f - g) = ℓ f - ℓ g := fun f g hf hg => by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ g, hadd _ _ hf (theta_smul _ hg), hsmul _ _ hg]
    ring
  obtain ⟨C, hC⟩ := quotient_bound hθ hψ hL hf
  have hd : HasDerivAt (fun t : ℝ => Complex.exp (((a * t : ℝ) : ℂ) * Complex.I)) ((a : ℂ) * Complex.I) 0 := by
    have := ((((hasDerivAt_id (0 : ℝ)).const_mul a).ofReal_comp).mul_const Complex.I).cexp
    simpa using this
  have h1 := (hd.tendsto_slope_zero_right.mul_const (ℓ f)).sub_const (ℓ (dLine ψ S T L f))
  have h0 : Tendsto (fun t : ℝ => C * t) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => C * t) (𝓝 0) (𝓝 (C * 0)) := tendsto_id.const_mul C
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine (sub_eq_zero.1 (tendsto_nhds_unique h1 (squeeze_zero_norm' ?_ h0))).symm
  refine eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => ?_
  have hH := theta_heisO_real hθ hψ (hL.2 t) hf
  have hq := theta_smul (t : ℂ)⁻¹ (theta_sub hH hf)
  have hD := theta_dLine hθ hψ hL hf
  have h2 := (hb _ (theta_sub hq hD)).trans (iSup_le fun w =>
    (ofReal_norm _).symm.trans_le (ENNReal.ofReal_le_ofReal (hC t ht w)))
  rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff ((norm_nonneg _).trans (hC t ht 0)), hsub _ _ hq hD,
    hsmul _ _ (theta_sub hH hf), hsub _ _ hH hf, h] at h2
  refine le_of_eq_of_le ?_ h2
  congr 2
  simp only [zero_add, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, Complex.real_smul, Complex.ofReal_inv]
  ring

theorem entry_le (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {m n : ℕ} (P : Mx D T.rank m) (Q : Mx D n S.rank)
    (ℓ : (WO S T → ℂ) → ℂ) (y : Mx D n m)
    (hadd : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ℓ (f + g) = ℓ f + ℓ g)
    (hsmul : ∀ (c : ℂ) f, IsThetaFunO ψ S T f → ℓ (c • f) = c * ℓ f)
    (hb : ∀ f, IsThetaFunO ψ S T f → ‖ℓ f‖ₑ ≤ ⨆ w, ‖f w‖ₑ)
    (hchar : ∀ (ξ : Mx D m n) f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T (P ⬝ ξ ⬝ Q) f) =
      ψ (-(Algebra.trace (AF D.host.F) (AE D) (y ⬝ ξ).trace)) * ℓ f)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (τ : D.what₂.Tau) (i : Fin n) (j : Fin m) :
    ‖ℓ f‖ₑ * ENNReal.ofReal ‖compAt θ τ y i j‖ ≤
      ‖ℓ (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (compAt θ τ P ⬝ single j i (1 : ℂ) ⬝ compAt θ τ Q) f)‖ₑ +
      ‖ℓ (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (compAt θ τ P ⬝ single j i Complex.I ⬝ compAt θ τ Q) f)‖ₑ := by
  have key : ∀ b : ℂ, ‖ℓ f‖ * |(compAt θ τ y i j * b).re| ≤
      ‖ℓ (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (compAt θ τ P ⬝ single j i b ⬝ compAt θ τ Q) f)‖ := fun b => by
    rw [dRho_eq_dLine, deriv_char hψ hθ ℓ hadd hsmul hb (isRealDir_lineAt hθ τ _)
      (4 * Real.pi * (Matrix.trace (compAt θ τ y ⬝ single j i b)).re) hf fun t => by
        rw [line_move hθ, hchar _ f hf, phase_line hψ hθ], Matrix.trace_mul_single, op_smul_eq_mul, norm_mul, norm_mul,
      Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < 4 * Real.pi),
      mul_comm]
    refine mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (abs_nonneg _) ?_) (norm_nonneg _)
    linarith [Real.pi_gt_three]
  have k1 := key 1
  have k2 := key Complex.I
  rw [mul_one] at k1
  rw [Complex.mul_I_re, abs_neg] at k2
  simp only [← ofReal_norm]
  rw [← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal (le_trans ?_ (add_le_add k1 k2))
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (Complex.norm_le_abs_re_add_abs_im _) (norm_nonneg _)

end GlobalTheory.CharDecay

theorem GlobalTheory.CharDecay.decay : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (m n : ℕ) (P : Mx D T.rank m) (Q : Mx D n S.rank) (N : ℕ), ∃ C : ℝ≥0, ∀ (ℓ : (WO S T → ℂ) → ℂ) (y : Mx D n m), (∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ℓ (f + g) = ℓ f + ℓ g) → (∀ (c : ℂ) f, IsThetaFunO ψ S T f → ℓ (c • f) = c * ℓ f) → (∀ f, IsThetaFunO ψ S T f → ‖ℓ f‖ₑ ≤ ⨆ w, ‖f w‖ₑ) → (∀ (ξ : Mx D m n) f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T (P ⬝ ξ ⬝ Q) f) = ψ (-(Algebra.trace (AF D.host.F) (AE D) (y ⬝ ξ).trace)) * ℓ f) → ∀ f, IsThetaFunO ψ S T f → ‖ℓ f‖ₑ * ENNReal.ofReal ((1 + realSize θ y) ^ N) ≤ C * supSob ψ θ N f := by
  intro D ψ hψ θ hθ S T m n P Q N
  have hc : ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), ∃ c : ℝ≥0, ∀ k (f : WO S T → ℂ),
      IsThetaFunO ψ S T f →
        supSob ψ θ k (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) ≤ c * supSob ψ θ (k + 1) f := fun τ z =>
    ⟨Real.toNNReal (∑ i, ∑ j, (|(z i j).re| + |(z i j).im|)), fun k f hf =>
      GlobalTheory.Size.SupWord.ws_dRho_le (p := fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) hψ hθ GlobalTheory.Size.SupWord.supN_add_le
        GlobalTheory.Size.SupWord.supN_smul hf τ z k⟩
  choose c hc using hc
  induction N with
  | zero =>
    refine ⟨1, fun ℓ y _ _ hb _ f hf => ?_⟩
    rw [pow_zero, ENNReal.ofReal_one, mul_one, ENNReal.coe_one, one_mul]
    unfold supSob
    rw [GlobalTheory.Size.wordSum_zero]
    exact hb f hf
  | succ N ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨C + ∑ τ, ∑ i : Fin n, ∑ j : Fin m, (C * c τ (compAt θ τ P ⬝ single j i (1 : ℂ) ⬝ compAt θ τ Q) +
      C * c τ (compAt θ τ P ⬝ single j i Complex.I ⬝ compAt θ τ Q)), fun ℓ y hadd hsmul hb hchar f hf => ?_⟩
    have hs := realSize_nonneg θ y
    have hd : ∀ τ z, ‖ℓ (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f)‖ₑ * ENNReal.ofReal ((1 + realSize θ y) ^ N) ≤
        (C * c τ z : ℝ≥0) * supSob ψ θ (N + 1) f := fun τ z => by
      refine (hC ℓ y hadd hsmul hb hchar _ (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ z hf)).trans ?_
      rw [ENNReal.coe_mul, mul_assoc]
      exact mul_le_mul_right (hc τ z N f hf) _
    have he : ENNReal.ofReal (realSize θ y) = ∑ τ, ∑ i, ∑ j, ENNReal.ofReal ‖compAt θ τ y i j‖ := by
      unfold realSize
      rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
    rw [pow_succ, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add zero_le_one hs, ENNReal.ofReal_one, he,
      ← mul_assoc, mul_add, mul_one, ENNReal.coe_add, add_mul]
    refine add_le_add ((hC ℓ y hadd hsmul hb hchar f hf).trans
      (mul_le_mul_right (GlobalTheory.Size.wordSum_mono (Nat.le_succ N) f) _)) ?_
    simp only [ENNReal.ofNNReal_finsetSum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    rw [mul_right_comm, ENNReal.coe_add, add_mul]
    refine (mul_le_mul_left (GlobalTheory.CharDecay.entry_le hψ hθ P Q ℓ y hadd hsmul hb hchar hf τ i j) _).trans ?_
    rw [add_mul]
    exact add_le_add (hd τ _) (hd τ _)

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_functional_theta_estimate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (m n : ℕ) (P : Mx D T.rank m) (Q : Mx D n S.rank) (N : ℕ), ∃ C : ℝ≥0, ∀ (ℓ : (WO S T → ℂ) → ℂ) (y : Mx D n m), (∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ℓ (f + g) = ℓ f + ℓ g) → (∀ (c : ℂ) f, IsThetaFunO ψ S T f → ℓ (c • f) = c * ℓ f) → (∀ f, IsThetaFunO ψ S T f → ‖ℓ f‖ₑ ≤ ⨆ w, ‖f w‖ₑ) → (∀ (ξ : Mx D m n) f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T (P ⬝ ξ ⬝ Q) f) = ψ (-(Algebra.trace (AF D.host.F) (AE D) (y ⬝ ξ).trace)) * ℓ f) → ∀ f, IsThetaFunO ψ S T f → ‖ℓ f‖ₑ * ENNReal.ofReal ((1 + realSize θ y) ^ N) ≤ C * supSob ψ θ N f := by
  atlas_forward_decl GlobalTheory.CharDecay.decay
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.MatAnnih

theorem trace_mul_smul_single (D : D7) {m n : ℕ} (y : Mx D n m) (r : AF D.host.F) (i : Fin n) (j : Fin m)
    (a : D.host.E) :
    Algebra.trace (AF D.host.F) (AE D) (y ⬝ (r • Matrix.single j i (incA D a) : Mx D m n)).trace =
      r * Algebra.trace (AF D.host.F) (AE D) (incA D a * y i j) := by
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_mul_single, map_smul, smul_eq_mul, op_smul_eq_mul, mul_comm (y i j)]

theorem finPart_sum_tmul (D : D7) {d : ℕ} (x : Fin d → Af D.host.F) (e : Fin d → D.host.E) :
    finPart D (∑ l, pairA D.host.F 0 (x l) ⊗ₜ[D.host.F] e l) = ∑ l, x l ⊗ₜ[D.host.F] e l := by
  unfold finPart
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum]
  rfl

theorem annih_mem_box : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (m n : ℕ), ∀ V ∈ nhds (0 : Mx D m n), ∃ K : Set (Mx D n m), IsCompact K ∧ ∀ y : Mx D n m, (∀ ξ ∈ V, ξ.map (infPart D) = 0 → ψ (Algebra.trace (AF D.host.F) (AE D) (y ⬝ ξ).trace) = 1) → InBox K y := by
  intro D ψ hψ m n V hV
  obtain ⟨d, c, e, hce⟩ := GlobalTheory.TwistCoords.finPart_eq_sum_trace D
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _

  let M : (Fin n × Fin m × Fin d) → Mx D m n := fun p => Matrix.single p.2.1 p.1 (incA D (c p.2.2))
  let φ : (Fin n × Fin m × Fin d) → Af D.host.F → Mx D m n := fun p t => (pairA D.host.F 0 t) • M p
  have hpair : Continuous fun t : Af D.host.F => pairA D.host.F 0 t := continuous_const.prodMk continuous_id
  have hφ : ∀ p, Continuous (φ p) := fun p =>
    Continuous.smul (f := fun t : Af D.host.F => pairA D.host.F 0 t) (g := fun _ => M p) hpair continuous_const
  have hφ0 : ∀ p, φ p 0 = 0 := fun p => by
    have : pairA D.host.F 0 (0 : Af D.host.F) = 0 := rfl
    simp only [φ, this, zero_smul]
  have hO : (⋂ p, φ p ⁻¹' V) ∈ nhds (0 : Af D.host.F) :=
    Filter.iInter_mem.2 fun p => (hφ p).continuousAt.preimage_mem_nhds (by rw [hφ0]; exact hV)
  obtain ⟨K₀, hK₀, hmem⟩ := GlobalTheory.ScalarAnnih.exists_compact_of_annih D ψ hψ _ hO
  let g : (Fin n × Fin m × Fin d → Af D.host.F) → Mx D n m :=
    fun z => Matrix.of fun i j => ∑ l, pairA D.host.F 0 (z (i, j, l)) ⊗ₜ[D.host.F] e l
  have hg : Continuous g := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun z : Fin n × Fin m × Fin d → Af D.host.F => ∑ l, pairA D.host.F 0 (z (i, j, l)) ⊗ₜ[D.host.F] e l
    refine continuous_finset_sum _ fun l _ => ?_
    have : (fun z : Fin n × Fin m × Fin d → Af D.host.F => (pairA D.host.F 0 (z (i, j, l)) ⊗ₜ[D.host.F] e l : AE D)) =
        fun z => pairA D.host.F 0 (z (i, j, l)) • ((1 : AF D.host.F) ⊗ₜ[D.host.F] e l : AE D) := by
      funext z; rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact (hpair.comp (continuous_apply (A := fun _ : Fin n × Fin m × Fin d => Af D.host.F) (i, j, l))).smul
      (continuous_const (y := ((1 : AF D.host.F) ⊗ₜ[D.host.F] e l : AE D)))
  refine ⟨g '' Set.pi Set.univ (fun _ => K₀), (isCompact_univ_pi fun _ => hK₀).image hg, fun y hy => ?_⟩
  let z : Fin n × Fin m × Fin d → Af D.host.F :=
    fun p => sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) (incA D (c p.2.2) * y p.1 p.2.1))
  refine ⟨g z, ⟨z, fun p _ => hmem _ fun t ht => ?_, rfl⟩, ?_⟩
  · have hu : (pairA D.host.F 0 t • Matrix.single p.2.1 p.1 (incA D (c p.2.2)) : Mx D m n) ∈ V :=
      Set.mem_iInter.1 ht p
    have hinf : (pairA D.host.F 0 t • Matrix.single p.2.1 p.1 (incA D (c p.2.2)) : Mx D m n).map (infPart D) = 0 := by
      ext k l
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply, Matrix.single_apply]
      split_ifs
      · change infPart D (pairA D.host.F 0 t • ((1 : AF D.host.F) ⊗ₜ[D.host.F] c p.2.2)) = 0
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        change (fstA D.host.F (pairA D.host.F 0 t)) ⊗ₜ[D.host.F] (c p.2.2) = 0
        exact TensorProduct.zero_tmul _ _
      · rw [smul_zero, map_zero]
    have h1 := hy _ hu hinf
    have e2 := trace_mul_smul_single D y (pairA D.host.F 0 t) p.1 p.2.1 (c p.2.2)
    have e1 : pairA D.host.F 0 (t * z p) = pairA D.host.F 0 t *
        Algebra.trace (AF D.host.F) (AE D) (incA D (c p.2.2) * y p.1 p.2.1) :=
      Prod.ext (zero_mul _).symm rfl
    exact (congrArg ψ (e1.trans e2.symm)).trans h1
  · refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply, Matrix.sub_apply, Matrix.zero_apply, (finPart D).map_sub, sub_eq_zero, hce]
    exact (finPart_sum_tmul D (fun l => z (i, j, l)) e).symm

end GlobalTheory.MatAnnih
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_annihilator_compact_box : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (m n : ℕ), ∀ V ∈ nhds (0 : Mx D m n), ∃ K : Set (Mx D n m), IsCompact K ∧ ∀ y : Mx D n m, (∀ ξ ∈ V, ξ.map (infPart D) = 0 → ψ (Algebra.trace (AF D.host.F) (AE D) (y ⬝ ξ).trace) = 1) → InBox K y := by
  atlas_forward_decl GlobalTheory.MatAnnih.annih_mem_box
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
noncomputable section
variable {D : D7}

namespace GlobalTheory.Unf.DoubleSum

theorem realSize_nsmul (θ : InfFam D) {m k : ℕ} (n : ℕ) (x : Mx D m k) :
    realSize θ (n • x) = n * realSize θ x := by
  unfold realSize
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
  have : compAt θ τ (n • x) i j = (n : ℂ) * compAt θ τ x i j := by
    simp only [compAt, Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
  rw [this, norm_mul, Complex.norm_natCast]

theorem pointwise (θ : InfFam D) {a b c e : ℕ} (K : Set (Mx D a b)) (K' : Set (Mx D c e)) (N N' n : ℕ) (hn : 0 < n)
    (B : ℝ≥0∞) (F : ratMx D a b → ratMx D c e → ℝ≥0∞)
    (hF : ∀ x y, F x y ≠ 0 → InBox K (n • (x : Mx D a b)) ∧ InBox K' (n • (y : Mx D c e)))
    (h1 : ∀ x y, F x y * ENNReal.ofReal ((1 + realSize θ (x : Mx D a b)) ^ (N + N')) ≤ B)
    (h2 : ∀ x y, F x y * ENNReal.ofReal ((1 + realSize θ (y : Mx D c e)) ^ (N + N')) ≤ B) (x : ratMx D a b) (y : ratMx D c e) :
    F x y ≤ (n : ℝ≥0∞) ^ (N + N') * B * (ENNReal.ofReal (maj θ K N (n • (x : Mx D a b))) *
      ENNReal.ofReal (maj θ K' N' (n • (y : Mx D c e)))) := by
  by_cases h0 : F x y = 0
  · rw [h0]; exact bot_le
  obtain ⟨hx, hy⟩ := hF x y h0
  set s := 1 + realSize θ (x : Mx D a b) with hs
  set t := 1 + realSize θ (y : Mx D c e) with ht
  have s1 : 1 ≤ s := by have := realSize_nonneg θ (x : Mx D a b); linarith
  have t1 : 1 ≤ t := by have := realSize_nonneg θ (y : Mx D c e); linarith
  set M := max s t with hM
  have M1 : 1 ≤ M := le_trans s1 (le_max_left _ _)
  have Mpos : 0 < M := by linarith
  have hFM : F x y * ENNReal.ofReal (M ^ (N + N')) ≤ B := by
    rcases le_total s t with h | h
    · rw [hM, max_eq_right h]; exact h2 x y
    · rw [hM, max_eq_left h]; exact h1 x y
  have hMp : 0 < M ^ (N + N') := pow_pos Mpos _
  have hF' : F x y ≤ B * ENNReal.ofReal ((M ^ (N + N'))⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hMp, ← div_eq_mul_inv]
    exact ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hMp)) (Or.inl ENNReal.ofReal_ne_top) |>.2 hFM
  refine hF'.trans ?_
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnx : 1 + realSize θ (n • (x : Mx D a b)) ≤ n * M := by
    rw [realSize_nsmul]
    have := realSize_nonneg θ (x : Mx D a b)
    calc 1 + n * realSize θ (x : Mx D a b) ≤ n * s := by rw [hs]; nlinarith
      _ ≤ n * M := by gcongr; exact le_max_left _ _
  have hny : 1 + realSize θ (n • (y : Mx D c e)) ≤ n * M := by
    rw [realSize_nsmul]
    have := realSize_nonneg θ (y : Mx D c e)
    calc 1 + n * realSize θ (y : Mx D c e) ≤ n * t := by rw [ht]; nlinarith
      _ ≤ n * M := by gcongr; exact le_max_right _ _
  have px : 0 < 1 + realSize θ (n • (x : Mx D a b)) := by have := realSize_nonneg θ (n • (x : Mx D a b)); linarith
  have py : 0 < 1 + realSize θ (n • (y : Mx D c e)) := by have := realSize_nonneg θ (n • (y : Mx D c e)); linarith
  have key : (M ^ (N + N'))⁻¹ ≤ (n : ℝ) ^ (N + N') * (((1 + realSize θ (n • (x : Mx D a b))) ^ N)⁻¹ *
      ((1 + realSize θ (n • (y : Mx D c e))) ^ N')⁻¹) := by
    have e1 : ((n * M) ^ N)⁻¹ ≤ ((1 + realSize θ (n • (x : Mx D a b))) ^ N)⁻¹ :=
      inv_anti₀ (pow_pos px _) (pow_le_pow_left₀ px.le hnx _)
    have e2 : ((n * M) ^ N')⁻¹ ≤ ((1 + realSize θ (n • (y : Mx D c e))) ^ N')⁻¹ :=
      inv_anti₀ (pow_pos py _) (pow_le_pow_left₀ py.le hny _)
    have npos : (0 : ℝ) < n := by linarith
    calc (M ^ (N + N'))⁻¹ = (n : ℝ) ^ (N + N') * (((n * M) ^ N)⁻¹ * ((n * M) ^ N')⁻¹) := by
          rw [mul_pow, mul_pow, pow_add, pow_add]; field_simp
      _ ≤ _ := by gcongr
  unfold maj
  rw [if_pos hx, if_pos hy, mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    show (n : ℝ≥0∞) ^ (N + N') = ENNReal.ofReal ((n : ℝ) ^ (N + N')) by
      rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast],
    mul_left_comm, ← ENNReal.ofReal_mul (by positivity)]
  gcongr

end GlobalTheory.Unf.DoubleSum

end

theorem GlobalTheory.Unf.doubleSum_le_maj : ∀ (D : D7) (θ : InfFam D) (a b c e : ℕ) (K : Set (Mx D a b)) (K' : Set (Mx D c e)) (N N' n : ℕ), 0 < n → ∀ (B : ℝ≥0∞) (F : ratMx D a b → ratMx D c e → ℝ≥0∞), (∀ x y, F x y ≠ 0 → InBox K (n • (x : Mx D a b)) ∧ InBox K' (n • (y : Mx D c e))) → (∀ x y, F x y * ENNReal.ofReal ((1 + realSize θ (x : Mx D a b)) ^ (N + N')) ≤ B) → (∀ x y, F x y * ENNReal.ofReal ((1 + realSize θ (y : Mx D c e)) ^ (N + N')) ≤ B) → ∑' x, ∑' y, F x y ≤ (n : ℝ≥0∞) ^ (N + N') * B * ((∑' x : ratMx D a b, ENNReal.ofReal (maj θ K N x)) * ∑' y : ratMx D c e, ENNReal.ofReal (maj θ K' N' y)) := by
  intro D θ a b c e K K' N N' n hn B F hF h1 h2
  have hinj : Function.Injective (fun x : ratMx D a b => n • x) := by
    intro u v huv
    obtain ⟨γ, hγ⟩ := u.2; obtain ⟨δ, hδ⟩ := v.2
    have e1 : ((n • u : ratMx D a b) : Mx D a b) = n • (u : Mx D a b) := AddSubgroup.coe_nsmul _ _ _
    have e2 : ((n • v : ratMx D a b) : Mx D a b) = n • (v : Mx D a b) := AddSubgroup.coe_nsmul _ _ _
    have h := congrArg Subtype.val huv
    simp only at h
    rw [e1, e2] at h
    apply Subtype.ext
    have hr : rat (n • γ) = rat (n • δ) := by
      have r1 : rat (n • γ) = n • rat γ := by
        funext i j; simp [rat, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
      have r2 : rat (n • δ) = n • rat δ := by
        funext i j; simp [rat, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
      rw [r1, r2]
      have hγ' : rat γ = (u : Mx D a b) := hγ
      have hδ' : rat δ = (v : Mx D a b) := hδ
      rw [hγ', hδ']; exact h
    have hγδ : γ = δ := by
      have := rat_injective hr
      funext i j
      have hij := congrFun (congrFun this i) j
      simp only [Matrix.smul_apply, nsmul_eq_mul] at hij
      exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)) hij
    have hγ' : rat γ = (u : Mx D a b) := hγ
    have hδ' : rat δ = (v : Mx D a b) := hδ
    rw [← hγ', ← hδ', hγδ]
  have hinj' : Function.Injective (fun y : ratMx D c e => n • y) := by
    intro u v huv
    obtain ⟨γ, hγ⟩ := u.2; obtain ⟨δ, hδ⟩ := v.2
    have e1 : ((n • u : ratMx D c e) : Mx D c e) = n • (u : Mx D c e) := AddSubgroup.coe_nsmul _ _ _
    have e2 : ((n • v : ratMx D c e) : Mx D c e) = n • (v : Mx D c e) := AddSubgroup.coe_nsmul _ _ _
    have h := congrArg Subtype.val huv
    simp only at h
    rw [e1, e2] at h
    apply Subtype.ext
    have hr : rat (n • γ) = rat (n • δ) := by
      have r1 : rat (n • γ) = n • rat γ := by
        funext i j; simp [rat, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
      have r2 : rat (n • δ) = n • rat δ := by
        funext i j; simp [rat, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
      rw [r1, r2]
      have hγ' : rat γ = (u : Mx D c e) := hγ
      have hδ' : rat δ = (v : Mx D c e) := hδ
      rw [hγ', hδ']; exact h
    have hγδ : γ = δ := by
      have := rat_injective hr
      funext i j
      have hij := congrFun (congrFun this i) j
      simp only [Matrix.smul_apply, nsmul_eq_mul] at hij
      exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)) hij
    have hγ' : rat γ = (u : Mx D c e) := hγ
    have hδ' : rat δ = (v : Mx D c e) := hδ
    rw [← hγ', ← hδ', hγδ]
  have hx : ∑' x : ratMx D a b, ENNReal.ofReal (maj θ K N (n • (x : Mx D a b))) ≤
      ∑' x : ratMx D a b, ENNReal.ofReal (maj θ K N x) := by
    have := ENNReal.tsum_comp_le_tsum_of_injective hinj (fun x : ratMx D a b => ENNReal.ofReal (maj θ K N x))
    simpa only [AddSubgroup.coe_nsmul] using this
  have hy : ∑' y : ratMx D c e, ENNReal.ofReal (maj θ K' N' (n • (y : Mx D c e))) ≤
      ∑' y : ratMx D c e, ENNReal.ofReal (maj θ K' N' y) := by
    have := ENNReal.tsum_comp_le_tsum_of_injective hinj' (fun y : ratMx D c e => ENNReal.ofReal (maj θ K' N' y))
    simpa only [AddSubgroup.coe_nsmul] using this
  calc ∑' x, ∑' y, F x y ≤ ∑' (x : ratMx D a b), ∑' (y : ratMx D c e), (n : ℝ≥0∞) ^ (N + N') * B * (ENNReal.ofReal (maj θ K N (n • (x : Mx D a b))) *
        ENNReal.ofReal (maj θ K' N' (n • (y : Mx D c e)))) :=
        ENNReal.tsum_le_tsum fun x => ENNReal.tsum_le_tsum fun y =>
          GlobalTheory.Unf.DoubleSum.pointwise θ K K' N N' n hn B F hF h1 h2 x y
    _ = (n : ℝ≥0∞) ^ (N + N') * B * ((∑' x : ratMx D a b, ENNReal.ofReal (maj θ K N (n • (x : Mx D a b)))) *
        ∑' y : ratMx D c e, ENNReal.ofReal (maj θ K' N' (n • (y : Mx D c e)))) := by
        simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    _ ≤ _ := by gcongr
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_sum_weighted_bound : ∀ (D : D7) (θ : InfFam D) (a b c e : ℕ) (K : Set (Mx D a b)) (K' : Set (Mx D c e)) (N N' n : ℕ), 0 < n → ∀ (B : ℝ≥0∞) (F : ratMx D a b → ratMx D c e → ℝ≥0∞), (∀ x y, F x y ≠ 0 → InBox K (n • (x : Mx D a b)) ∧ InBox K' (n • (y : Mx D c e))) → (∀ x y, F x y * ENNReal.ofReal ((1 + realSize θ (x : Mx D a b)) ^ (N + N')) ≤ B) → (∀ x y, F x y * ENNReal.ofReal ((1 + realSize θ (y : Mx D c e)) ^ (N + N')) ≤ B) → ∑' x, ∑' y, F x y ≤ (n : ℝ≥0∞) ^ (N + N') * B * ((∑' x : ratMx D a b, ENNReal.ofReal (maj θ K N x)) * ∑' y : ratMx D c e, ENNReal.ofReal (maj θ K' N' y)) := by
  atlas_forward_decl GlobalTheory.Unf.doubleSum_le_maj
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section

namespace GlobalTheory.Unf.DoubleSum

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem enorm_integral_le {α β : Type} [MeasurableSpace α] {μ : Measure α} {𝓕 : Set α} (h : μ 𝓕 = 1) (u : α → ℂ)
    (hu : ∀ a, ‖u a‖ = 1) (p : α → β) (f : β → ℂ) : ‖∫ a in 𝓕, u a * f (p a) ∂μ‖ₑ ≤ ⨆ w, ‖f w‖ₑ := by
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine (lintegral_mono (g := fun _ => ⨆ w, ‖f w‖ₑ) fun a => ?_).trans ?_
  · beta_reduce
    rw [enorm_mul, ← ofReal_norm (u a), hu, ENNReal.ofReal_one, one_mul]
    exact le_iSup (fun w => ‖f w‖ₑ) _
  · rw [setLIntegral_const, h, mul_one]

theorem rearrange (C₁ C₂ : ℝ≥0) (p s M : ℝ≥0∞) (hM : M ≠ ⊤) :
    p * ((C₁ + C₂) * s) * M = ((C₁ + C₂) * M.toNNReal : ℝ≥0) * p * s := by
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hM, ENNReal.coe_add]
  ring

section Source

variable {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ)

theorem enorm_mixS_le (hψ : IsStdChar D ψ (-1)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) (w : WO S₀ T) :
    ‖d.mixS T ψ v.μ v.𝓕 f x w‖ₑ ≤ ⨆ w, ‖f w‖ₑ := by
  simp only [HypDec.mixS, HypDec.integrandS_eq]
  exact enorm_integral_le v.covol.2.2 _ (fun _ => hψ.1.2.1 _) _ f

theorem mixS_add (hψ : IsStdChar D ψ (-1)) {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g)
    (x : Mx D T.rank ρ) : d.mixS T ψ v.μ v.𝓕 (f + g) x = d.mixS T ψ v.μ v.𝓕 f x + d.mixS T ψ v.μ v.𝓕 g x := by
  funext w
  have h1 := d.integrableOn_mixS hψ.1.1 v.covol hf x w
  have h2 := d.integrableOn_mixS hψ.1.1 v.covol hg x w
  simp only [HypDec.mixS, HypDec.integrandS_eq, Pi.add_apply, mul_add] at h1 h2 ⊢
  exact integral_add h1 h2

theorem mixS_smul (c : ℂ) (f : WO S T → ℂ) (x : Mx D T.rank ρ) :
    d.mixS T ψ v.μ v.𝓕 (c • f) x = c • d.mixS T ψ v.μ v.𝓕 f x := by
  funext w
  simp only [HypDec.mixS, HypDec.integrandS_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]

variable (T) in

def dualPt (ρ : ℕ) : Mx D ρ T.rank →+ Mx D T.rank ρ where
  toFun b := adj (incA D D.host.xi0⁻¹ • (b ⬝ giA T))
  map_zero' := by rw [Matrix.zero_mul, smul_zero, adj_zero]
  map_add' _ _ := by rw [Matrix.add_mul, smul_add, adj_add]

theorem continuous_dualPt : Continuous (dualPt T ρ) := by
  have h : Continuous fun b : Mx D ρ T.rank => (b ⬝ giA T : Mx D ρ T.rank) := continuous_id.matrix_mul continuous_const
  exact continuous_adj.comp (f := fun b : Mx D ρ T.rank => incA D D.host.xi0⁻¹ • (b ⬝ giA T : Mx D ρ T.rank))
    (continuous_matrix fun i j => continuous_const.mul (h.matrix_elem i j))

theorem infPart_cA {a : AE D} (h : infPart D a = 0) : infPart D (cA D a) = 0 := by
  have e : ∀ z : AE D, infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x => rfl
    | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, ha, hb]
  rw [e, h, map_zero]

theorem dualPt_fin {b : Mx D ρ T.rank} (hb : b.map (infPart D) = 0) : (dualPt T ρ b).map (infPart D) = 0 := by
  have h : (b ⬝ giA T).map (infPart D) = 0 := by rw [Matrix.map_mul, hb, Matrix.zero_mul]
  funext i j
  refine infPart_cA (a := incA D D.host.xi0⁻¹ * (b ⬝ giA T) j i) ?_
  rw [map_mul, show infPart D ((b ⬝ giA T) j i) = 0 from congrFun (congrFun h j) i, mul_zero]

theorem symplO_dualPt (x : Mx D T.rank ρ) (b : Mx D ρ T.rank) :
    symplO S T (d.extX T x) (d.extY T (dualPt T ρ b)) = Algebra.trace (AF D.host.F) (AE D) (x ⬝ b).trace := by
  have h := d.hO_ext T x 0 0 (dualPt T ρ b) 0 0
  simp only [map_zero, zero_add, add_zero, hO_eq_trace S₀, Matrix.mul_zero, trace_zero] at h
  rw [symplO_eq, h, show pairS T (0 : Mx D T.rank ρ) 0 = 0 by simp [pairS], add_zero, pairS]
  congr 1
  rw [show dualPt T ρ b = adj (incA D D.host.xi0⁻¹ • (b ⬝ giA T)) from rfl, adj_adj, Matrix.smul_mul, trace_smul, smul_eq_mul, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_mul, Matrix.mul_assoc, giA_gA_cancel, trace_mul_comm]

end Source

section Target

variable {S T T₀ : HSp D} {σ : ℕ} (d : HypDec T T₀ σ) (v : VolM D σ S.rank)

theorem enorm_mixT_le (hψ : IsStdChar D ψ (-1)) (f : WO S T → ℂ) (y : Mx D S.rank σ) (w : WO S T₀) :
    ‖d.mixT S ψ v.μ v.𝓕 f y w‖ₑ ≤ ⨆ w, ‖f w‖ₑ := by
  simp only [HypDec.mixT, HypDec.integrandT_eq]
  exact enorm_integral_le v.covol.2.2 _ (fun _ => hψ.1.2.1 _) _ f

theorem mixT_add (hψ : IsStdChar D ψ (-1)) {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g)
    (y : Mx D S.rank σ) : d.mixT S ψ v.μ v.𝓕 (f + g) y = d.mixT S ψ v.μ v.𝓕 f y + d.mixT S ψ v.μ v.𝓕 g y := by
  funext w
  have h1 := d.integrableOn_mixT hψ.1.1 v.covol hf y w
  have h2 := d.integrableOn_mixT hψ.1.1 v.covol hg y w
  simp only [HypDec.mixT, HypDec.integrandT_eq, Pi.add_apply, mul_add] at h1 h2 ⊢
  exact integral_add h1 h2

theorem mixT_smul (c : ℂ) (f : WO S T → ℂ) (y : Mx D S.rank σ) :
    d.mixT S ψ v.μ v.𝓕 (c • f) y = c • d.mixT S ψ v.μ v.𝓕 f y := by
  funext w
  simp only [HypDec.mixT, HypDec.integrandT_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]

end Target

section Double

variable {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (d : HypDec S S₀ ρ) (d' : HypDec T T₀ σ) (v : VolM D T.rank ρ)
  (v' : VolM D σ S₀.rank)

variable (ψ) in

def val (x : Mx D T.rank ρ) (y : Mx D S₀.rank σ) (f : WO S T → ℂ) : ℂ :=
  d'.mixT S₀ ψ v'.μ v'.𝓕 (d.mixS T ψ v.μ v.𝓕 f x) y 0

theorem val_extY (hψ : IsStdChar D ψ (-1)) (x : Mx D T.rank ρ) (y : Mx D S₀.rank σ) (b : Mx D ρ T.rank)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    val ψ d d' v v' x y (heisO ψ S T (d.extY T (dualPt T ρ b)) f) =
      ψ (Algebra.trace (AF D.host.F) (AE D) (x ⬝ b).trace) * val ψ d d' v v' x y f := by
  rw [val, (GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ S S₀ T ρ d v f hf).2.1, mixT_smul, symplO_dualPt]
  rfl

theorem val_incX (hψ : IsStdChar D ψ (-1)) (x : Mx D T.rank ρ) (y : Mx D S₀.rank σ) (ξ : Mx D σ S₀.rank)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    val ψ d d' v v' x y (heisO ψ S T (d.ext0 T (d'.incX S₀ ξ)) f) =
      ψ (-(Algebra.trace (AF D.host.F) (AE D) (y ⬝ ξ).trace)) * val ψ d d' v v' x y f := by
  rw [val, (GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ S S₀ T ρ d v f hf).2.2.1,
    (GlobalTheory.T.heisenbergThetaMixedModelTarget_of_mixedModel D ψ hψ S₀ T T₀ σ d' v'.μ v'.𝓕 v'.covol _
      ((GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hψ).1 S S₀ T ρ d v.μ v.𝓕 v.covol f hf x)).1,
    GlobalTheory.OrientedHeis.symplO_skew, d'.symplO_incX_incAdj]
  rfl

theorem ext_zero_incX_finite_part_zero {ξ : Mx D σ S₀.rank} (h : ξ.map (infPart D) = 0) :
    (d.ext0 T (d'.incX S₀ ξ)).map (infPart D) = 0 := by
  have h1 : (d'.incX S₀ ξ).map (infPart D) = 0 := by rw [HypDec.incX_apply, Matrix.map_mul, h, Matrix.mul_zero]
  rw [HypDec.matrixExtendByZero_apply, Matrix.map_mul, h1, Matrix.zero_mul]

theorem trace_nsmul {a b : ℕ} (n : ℕ) (x : Mx D a b) (z : Mx D b a) : (x ⬝ (n • z)).trace = ((n • x) ⬝ z).trace := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, Matrix.mul_zero, Matrix.zero_mul]
  | succ n ih => rw [succ_nsmul, succ_nsmul, Matrix.mul_add, Matrix.add_mul, trace_add, trace_add, ih]

end Double

theorem absSum₂_le : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (ρ σ : ℕ), ∃ k : ℕ, ∀ (S₀ T₀ : HSp D) (d : HypDec S S₀ ρ) (d' : HypDec T T₀ σ) (v : VolM D T.rank ρ) (v' : VolM D σ S₀.rank), ∀ K₀ ∈ nhds (0 : WO S T), ∃ C : ℝ≥0, ∀ n : ℕ, 0 < n → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ S T (n • u) f = f) → GlobalTheory.IndefiniteRowSideFullHecke.WordMatrixSeminorms.absSum₂ ψ d d' v.μ v.𝓕 v'.μ v'.𝓕 f ≤ C * (n : ℝ≥0∞) ^ k * supSob ψ θ k f := by
  intro D ψ hψ θ hθ S T ρ σ
  choose N hN using GlobalTheory.T.tsum_adelicMatrixSchwartzMajorant_rational_ne_top D θ hθ
  refine ⟨N T.rank ρ + N (S.rank - 2 * ρ) σ, fun S₀ T₀ d d' v v' K₀ hK₀ => ?_⟩
  have hr : S.rank - 2 * ρ = S₀.rank := by have := d.rank_add; omega
  rw [hr]
  set k := N T.rank ρ + N S₀.rank σ with hk
  have hmv := fun f hf => (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hψ).1 S S₀ T ρ d v.μ v.𝓕 v.covol f hf
  have c1 : Continuous fun b => d.extY T (dualPt T ρ b) := continuous_dualPt.matrix_mul continuous_const
  have c2 : Continuous fun ξ => d.ext0 T (d'.incX S₀ ξ) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  obtain ⟨K, hK, hbox⟩ := GlobalTheory.T.character_annihilator_compact_box D ψ hψ ρ T.rank _
    (c1.continuousAt.preimage_mem_nhds (by rwa [map_zero, map_zero]))
  obtain ⟨K', hK', hbox'⟩ := GlobalTheory.T.character_annihilator_compact_box D ψ hψ σ S₀.rank _
    (c2.continuousAt.preimage_mem_nhds (by rwa [map_zero, map_zero]))
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.T.mixedCoordinate_decay_realEntries D ψ hψ θ hθ S S₀ T ρ d v k
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.T.bounded_functional_theta_estimate D ψ hψ θ hθ S T σ S₀.rank d'.jX d.p0 k
  have hM := ENNReal.mul_ne_top (hN T.rank ρ K hK) (hN S₀.rank σ K' hK')
  refine ⟨(C₁ + C₂) * ENNReal.toNNReal ((∑' x : ratMx D T.rank ρ, ENNReal.ofReal (maj θ K (N T.rank ρ) x)) *
    ∑' y : ratMx D S₀.rank σ, ENNReal.ofReal (maj θ K' (N S₀.rank σ) y)), fun n hn f hf hlev => ?_⟩
  refine (GlobalTheory.T.double_sum_weighted_bound D θ _ _ _ _ K K' (N T.rank ρ) (N S₀.rank σ) n hn ((C₁ + C₂) * supSob ψ θ k f)
    (fun x y => ‖val ψ d d' v v' x y f‖ₑ) (fun x y hne => ⟨hbox _ fun b hb hfin => ?_, hbox' _ fun ξ hξ hfin => ?_⟩)
    (fun x y => ?_) (fun x y => ?_)).trans (le_of_eq ?_)
  · have h := val_extY d d' v v' hψ x y (n • b) hf
    rw [map_nsmul, map_nsmul, hlev (d.extY T (dualPt T ρ b)) hb
      (by rw [HypDec.extY_apply, Matrix.map_mul, dualPt_fin hfin, Matrix.zero_mul]),
      trace_nsmul] at h
    exact (mul_eq_right₀ (enorm_ne_zero.1 hne)).1 h.symm
  · have h := val_incX d d' v v' hψ x y (n • ξ) hf
    rw [map_nsmul, map_nsmul, hlev (d.ext0 T (d'.incX S₀ ξ)) hξ (ext_zero_incX_finite_part_zero d d' hfin),
      trace_nsmul, AddChar.map_neg_eq_inv] at h
    exact inv_eq_one.1 ((mul_eq_right₀ (enorm_ne_zero.1 hne)).1 h.symm)
  · refine (mul_le_mul_left (enorm_mixT_le d' v' hψ _ _ _) _).trans ?_
    rw [ENNReal.iSup_mul]
    exact iSup_le fun w => (hC₁ f hf x w).trans (mul_le_mul_left le_self_add _)
  · refine (hC₂ (val ψ d d' v v' x y) y (fun f g hf hg => ?_) (fun c f _ => ?_) (fun f _ => ?_)
      (fun ξ f hf => val_incX d d' v v' hψ x y ξ hf) f hf).trans (mul_le_mul_left le_add_self _)
    · rw [val, mixS_add d v hψ hf hg, mixT_add d' v' hψ (hmv f hf x) (hmv g hg x)]
      rfl
    · rw [val, mixS_smul, mixT_smul]
      rfl
    · exact (enorm_mixT_le d' v' hψ _ _ _).trans (iSup_le fun w => enorm_mixS_le d v hψ f x w)
  · exact rearrange _ _ _ _ _ hM

end GlobalTheory.Unf.DoubleSum

end
end
