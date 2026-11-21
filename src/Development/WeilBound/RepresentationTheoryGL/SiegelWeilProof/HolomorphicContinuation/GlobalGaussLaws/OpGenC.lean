import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2IsometryAlt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellSt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveRationalInvariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentAtTauMemStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockMatrixTwoByTwoFinStandardSkewMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixRealSizeBoundsAlongRealParametrisati

section
noncomputable section

open scoped Matrix

namespace PositivityTheory.Rg.Sw.Glob

def SchOps : Prop :=
  ∀ (m n : ℕ), (∀ f g : (Fin m → Fin n → ℂ) → ℂ, IsSch f → IsSch g → IsSch (fun u => f u + g u)) ∧
    (∀ (c : ℂ) (f : (Fin m → Fin n → ℂ) → ℂ), IsSch f → IsSch (fun u => c * f u)) ∧
    (∀ (a : Matrix (Fin n) (Fin n) ℂ) (f : (Fin m → Fin n → ℂ) → ℂ), IsUnit a.det → IsSch f →
      IsSch (fun u => f (Matrix.of u * a))) ∧
    (∀ (ε : Fin m → Bool) (t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (f : (Fin m → Fin n → ℂ) → ℂ), bᴴ = b → IsSch f →
      IsSch (fun u => Complex.exp (Complex.I * (t : ℂ) * (b * gramX ε u).trace) * f u)) ∧
    ∃ f : (Fin m → Fin n → ℂ) → ℂ, IsSch f ∧ f 0 = 1

end PositivityTheory.Rg.Sw.Glob
end
end

section
noncomputable section

open scoped Matrix ContDiff
open MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob.OpGenAH

section Local

variable {m n : ℕ}

local notation "EE" => (Fin m → Fin n → ℂ)

theorem isSch_add' {f g : EE → ℂ} (hf : IsSch f) (hg : IsSch g) : IsSch (fun u => f u + g u) := by
  obtain ⟨S, rfl⟩ := hf
  obtain ⟨T, rfl⟩ := hg
  exact ⟨S + T, by ext u; simp⟩

theorem isSch_cmul (c : ℂ) {f : EE → ℂ} (hf : IsSch f) : IsSch (fun u => c * f u) := by
  obtain ⟨S, rfl⟩ := hf
  exact ⟨c • S, by ext u; simp⟩

def rmulEquiv (a : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) : EE ≃L[ℝ] EE :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u => (Matrix.of u * a : Matrix (Fin m) (Fin n) ℂ)
      invFun := fun u => (Matrix.of u * a⁻¹ : Matrix (Fin m) (Fin n) ℂ)
      map_add' := fun u v => by
        show Matrix.of (u + v) * a = Matrix.of u * a + Matrix.of v * a
        rw [← Matrix.add_mul]; rfl
      map_smul' := fun c u => by
        show Matrix.of (c • u) * a = c • (Matrix.of u * a)
        ext i j
        simp [Matrix.mul_apply, Finset.smul_sum, mul_assoc]
      left_inv := fun u => by
        show Matrix.of u * a * a⁻¹ = u
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.mul_one]; rfl
      right_inv := fun u => by
        show Matrix.of u * a⁻¹ * a = u
        rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.mul_one]; rfl }

theorem isSch_rmul (a : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) {f : EE → ℂ} (hf : IsSch f) :
    IsSch (fun u => f (Matrix.of u * a)) := by
  obtain ⟨S, rfl⟩ := hf
  exact ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rmulEquiv a ha) S, by ext u; rfl⟩

theorem hasTemperateGrowth_expI : (fun t : ℝ => Complex.exp (Complex.I * t)).HasTemperateGrowth := by
  have key : ∀ k : ℕ, iteratedDeriv k (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ))) =
      fun t : ℝ => Complex.I ^ k * Complex.exp (Complex.I * (t : ℂ)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      have h1 : HasDerivAt (fun s : ℝ => Complex.I * (s : ℂ)) (Complex.I * 1) t :=
        ((hasDerivAt_id t).ofReal_comp).const_mul Complex.I
      have h2 := (h1.cexp).const_mul (Complex.I ^ k)
      rw [h2.deriv]
      ring
  refine ⟨ContDiff.cexp (contDiff_const.mul Complex.ofRealCLM.contDiff), fun k => ⟨0, 1, fun x => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, key]
  simp only [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, pow_zero]
  rw [mul_comm Complex.I (x : ℂ), Complex.norm_exp_ofReal_mul_I]

def coordL (a : Fin m) (i : Fin n) : EE →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a)

theorem hasTemperateGrowth_evX (P : PX m n) : (fun u : EE => evX P u).HasTemperateGrowth := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    have e : (fun u : EE => evX (C c) u) = fun _ => c := by ext u; simp [evX]
    rw [e]
    exact Function.HasTemperateGrowth.const c
  | add p q hp hq =>
    have e : (fun u : EE => evX (p + q) u) = (fun u : EE => evX p u) + (fun u : EE => evX q u) := by
      ext u; simp [evX]
    rw [e]
    exact hp.add hq
  | mul_X p k hp =>
    have hk : (fun u : EE => if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1).HasTemperateGrowth := by
      by_cases h : k.2.2
      · simp only [h, if_true]
        exact ((Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ).comp (coordL k.1 k.2.1)).hasTemperateGrowth
      · simp only [h]
        exact (coordL k.1 k.2.1).hasTemperateGrowth
    have e : (fun u : EE => evX (p * X k) u) =
        (fun u : EE => evX p u) * (fun u : EE => if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1) := by
      ext u; simp [evX]
    rw [e]
    exact hp.mul hk

theorem gramX_herm (ε : Fin m → Bool) (u : EE) : (gramX ε u)ᴴ = gramX ε u := by
  ext i j
  simp [Matrix.conjTranspose_apply, gramX, Qp, Qb, evX, map_sum, mul_comm]

theorem trace_real (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) (u : EE) :
    (((b * gramX ε u).trace.re : ℝ) : ℂ) = (b * gramX ε u).trace := by
  have h : star (b * gramX ε u).trace = (b * gramX ε u).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, gramX_herm, hb, Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_re.1 h

theorem hasTemperateGrowth_phase (ε : Fin m → Bool) (t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) :
    (fun u : EE => Complex.exp (Complex.I * (t : ℂ) * (b * gramX ε u).trace)).HasTemperateGrowth := by
  have hP : (fun u : EE => (b * gramX ε u).trace) =
      fun u => evX (∑ i, ∑ j, MvPolynomial.C (b i j) * Qp ε j i) u := by
    funext u
    simp [evX, gramX, Matrix.trace, Matrix.mul_apply, map_sum]
  have hT : (fun u : EE => (b * gramX ε u).trace).HasTemperateGrowth := by
    rw [hP]
    exact hasTemperateGrowth_evX _
  have hR : (fun u : EE => t * (b * gramX ε u).trace.re).HasTemperateGrowth := by
    have h1 := ((t • Complex.reCLM : ℂ →L[ℝ] ℝ).hasTemperateGrowth).comp hT
    convert h1 using 1
    funext u
    simp
  have h3 := hasTemperateGrowth_expI.comp hR
  convert h3 using 1
  funext u
  simp only [Function.comp]
  rw [Complex.ofReal_mul, trace_real ε b hb u]
  ring_nf

theorem isSch_phase (ε : Fin m → Bool) (t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) {f : EE → ℂ}
    (hf : IsSch f) : IsSch (fun u => Complex.exp (Complex.I * (t : ℂ) * (b * gramX ε u).trace) * f u) := by
  obtain ⟨S, rfl⟩ := hf
  refine ⟨SchwartzMap.smulLeftCLM ℂ
    (fun u : EE => Complex.exp (Complex.I * (t : ℂ) * (b * gramX ε u).trace)) S, ?_⟩
  ext u
  simp [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_phase ε t b hb)]

theorem exists_isSch_one : ∃ f : EE → ℂ, IsSch f ∧ f 0 = 1 := by
  let β : ContDiffBump (0 : EE) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun u : EE => ((β u : ℝ) : ℂ)) := β.hasCompactSupport.comp_left Complex.ofReal_zero
  have h2 : ContDiff ℝ ∞ (fun u : EE => ((β u : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp β.contDiff
  refine ⟨_, ⟨h1.toSchwartzMap h2, rfl⟩, ?_⟩
  simp [β.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]

end Local

theorem _root_.PositivityTheory.Rg.Sw.Glob.schOps : SchOps := fun _ _ =>
  ⟨fun _ _ hf hg => isSch_add' hf hg, fun c _ hf => isSch_cmul c hf, fun a _ ha hf => isSch_rmul a ha hf,
    fun ε t b _ hb hf => isSch_phase ε t b hb hf, exists_isSch_one⟩

end PositivityTheory.Rg.Sw.Glob.OpGenAH
end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.OG

variable {D : D7}

theorem g_ext {n : ℕ} {g h : G D n} (e : mat g = mat h) : g = h := by
  unfold mat at e
  exact Subtype.ext (Units.ext e)

theorem exists_slice {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (x0 : Mx D m n)
    (z : Matrix (Fin m) (Fin n) ℂ) : ∃ x : Mx D m n, compAt θ τ x = z ∧
      (∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x0) ∧ x.map (finPart D) = x0.map (finPart D) := by
  classical
  obtain ⟨h1, h2⟩ := GlobalTheory.AdForm.RatMove.realPt_spec hθ (fun τ' => if τ' = τ then z - compAt θ τ x0 else 0)
  refine ⟨x0 + GlobalTheory.AdForm.realPt θ (fun τ' => if τ' = τ then z - compAt θ τ x0 else 0), ?_, ?_, ?_⟩
  · rw [GlobalTheory.RealParamSize.compAt_add, h2]
    simp
  · intro τ' h
    rw [GlobalTheory.RealParamSize.compAt_add, h2]
    simp [h]
  · rw [Matrix.map_add _ (map_add (finPart D)), h1, add_zero]

theorem tens_at {θ : InfFam D} {m n : ℕ} (τ : D.what₂.Tau) {fr : Matrix (Fin m) (Fin m) ℂ} (hfr : IsUnit fr.det)
    (f : (Fin m → Fin n → ℂ) → ℂ) (Ψ : Mx D m n → ℂ) (x : Mx D m n) (u : Matrix (Fin m) (Fin n) ℂ)
    (hx : compAt θ τ x = fr * u) : tens θ τ fr f Ψ x = f u * Ψ x := by
  simp only [tens, hx, Matrix.nonsing_inv_mul_cancel_left _ _ hfr]

theorem awayCls_zero {θ : InfFam D} {m n : ℕ} (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) :
    AwayCls θ τ fr (0 : Mx D m n → ℂ) := by
  refine ⟨fun _ _ _ _ => rfl, fun f _ => ?_⟩
  have : tens θ τ fr f (0 : Mx D m n → ℂ) = 0 := by
    funext x
    simp [tens]
  rw [this]
  exact zero_mem _

theorem exists_nU (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) : ∃ y : GR n, mR y = nU b := by
  let u : GL (Fin n ⊕ Fin n) ℂ :=
    ⟨nU b, nU (-b), by simp [nU, Matrix.fromBlocks_multiply], by simp [nU, Matrix.fromBlocks_multiply]⟩
  have hu : u ∈ GR n := by
    show InG (nU b)
    simp only [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hb]
    simp
  exact ⟨⟨u, hu⟩, rfl⟩

theorem component_block_matrix (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (a b c d : Mx D n n) :
    compAt θ τ (blk4 a b c d) = blk4 (compAt θ τ a) (compAt θ τ b) (compAt θ τ c) (compAt θ τ d) := by
  exact GlobalTheory.StdUnn.Frame.block_matrix_map _ a b c d

theorem finite_part_block_matrix {n : ℕ} (a b c d : Mx D n n) :
    (blk4 a b c d).map (finPart D) = blk4 (a.map (finPart D)) (b.map (finPart D)) (c.map (finPart D)) (d.map (finPart D)) := by
  exact GlobalTheory.StdUnn.Frame.block_matrix_map _ a b c d

theorem neg_block_matrix {R : Type} [CommRing R] {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) :
    -blk4 a b c d = blk4 (-a) (-b) (-c) (-d) := by
  unfold blk4
  rw [← Matrix.fromBlocks_neg]
  rfl

theorem jsq {R : Type} [CommRing R] {n : ℕ} :
    (blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0) * blk4 0 1 (-1) 0 = -1 := by
  rw [GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul, ← GlobalTheory.StdUnn.Frame.block_matrix_one, neg_block_matrix]
  simp

theorem mat_inv_w {n : ℕ} (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) : mat w⁻¹ = -blk4 0 1 (-1) 0 := by
  have h1 : mat w⁻¹ * mat w = 1 := by
    show mat (w⁻¹ * w) = 1
    rw [inv_mul_cancel]
    rfl
  have h2 : mat w * (-mat w) = 1 := by rw [mul_neg, hw, jsq, neg_neg]
  calc mat w⁻¹ = mat w⁻¹ * (mat w * (-mat w)) := by rw [h2, mul_one]
    _ = -mat w := by rw [← mul_assoc, h1, one_mul]
    _ = _ := by rw [hw]

end PositivityTheory.Rg.Sw.Glob.OG
end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.OG

variable {D : D7}

theorem compAt_zero' (θ : InfFam D) (τ : D.what₂.Tau) {m n : ℕ} : compAt θ τ (0 : Mx D m n) = 0 := by
  ext i j
  simp [compAt]

theorem compAt_one' (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} : compAt θ τ (1 : Mx D n n) = 1 := by
  ext i j
  simp only [compAt, Matrix.map_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem compAt_J (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} :
    compAt θ τ (blk4 (0 : Mx D n n) 1 (-1) 0) = blk4 0 1 (-1) 0 := by
  rw [component_block_matrix, GlobalTheory.RealParamSize.compAt_neg, compAt_zero', compAt_one']

theorem fin_J {n : ℕ} : (blk4 (0 : Mx D n n) 1 (-1) 0).map (finPart D) = blk4 0 1 (-1) 0 := by
  rw [finite_part_block_matrix, Matrix.map_neg _ (map_neg (finPart D)), Matrix.map_zero _ (map_zero (finPart D)),
    Matrix.map_one _ (map_zero (finPart D)) (map_one (finPart D))]

theorem iota_conj {θ : InfFam D} {τ : D.what₂.Tau} {n : ℕ} {ι : GR n →* G D n} (hθ : IsInfFam θ)
    (hι : IsPlaceEmb θ τ ι) (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) (y yn : GR n) (c : Matrix (Fin n) (Fin n) ℂ)
    (hyc : mR y = nbar c) (hyn : mR yn = nU (-c)) : ι yn = w⁻¹ * ι y * w := by
  apply g_ext
  have hm : mat (w⁻¹ * ι y * w) = mat w⁻¹ * mat (ι y) * mat w := rfl
  rw [hm, mat_inv_w w hw, hw]
  apply GlobalTheory.StabAtPlace.mx_ext hθ
  · rw [Matrix.map_mul, Matrix.map_mul, (hι.2 yn).2.2, (hι.2 y).2.2, Matrix.map_neg _ (map_neg (finPart D)), fin_J, mul_one,
      neg_mul, jsq, neg_neg]
  · intro τ'
    rw [GlobalTheory.AdForm.RatMove.compAt_mul, GlobalTheory.AdForm.RatMove.compAt_mul, GlobalTheory.RealParamSize.compAt_neg, compAt_J]
    by_cases h : τ' = τ
    · subst h
      rw [(hι.2 yn).1, (hι.2 y).1, hyn, hyc]
      change blk4 1 (-c) 0 1 = -blk4 0 1 (-1) 0 * blk4 1 0 c 1 * blk4 0 1 (-1) 0
      rw [neg_block_matrix, GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul, GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul]
      simp
    · rw [(hι.2 yn).2.1 τ' h, (hι.2 y).2.1 τ' h, mul_one, neg_mul, jsq, neg_neg]

end PositivityTheory.Rg.Sw.Glob.OG
end
end
