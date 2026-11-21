import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeVolumeGlTwoTranslate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeCharacterIntegralZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeCharacterIntegralValue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInnerProductSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInnerProductLeftIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRightCosetDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralMatrixRowRepExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowRepsDistinctCosets
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DigitCharacterSumValues
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusRowRepFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerUnipotentEquivariantHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTorusValueFormulaHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharacterUniformizerPower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetTorusPower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetRowRep
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerZpowMemIntegersIff

noncomputable section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFUDom
open Ad3 Ad3.LFS

section Main

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

local notation "ϖ" => (GLnLocal.uniformizer F : F)

theorem mp_mul' (a b : Fˣ) (s : ℂ) : mp (a * b) s = mp a s * mp b s := by
  simpa [mp, GodementSectionLocal.modPow] using GodementSectionLocal.modPow_mul (a : F) (b : F) s


def f1 (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) (l : Fin 3 → ℤ) (k : GL (Fin 2) F) : ℂ :=
  s2 ψ ν (k * (torusPow F 2 ![l 0, l 1])⁻¹)⁻¹ *
    mp (GeneralLinearGroup.det (k * (torusPow F 2 ![l 0, l 1])⁻¹)) (3 / 2) *
    inn ψ (Φ0 F) (k * (torusPow F 2 ![l 0, l 1])⁻¹) (torusPow F 3 l)



abbrev V2 (ψ : AddChar F Circle) : ℝ := (vol2 ψ).real {x : Fin 2 → F | ∀ i, x i ∈ 𝒪[F]}


theorem det_kd (l : Fin 3 → ℤ) (i j : ℕ) (c : Fin j → 𝓀[F]) :
    GeneralLinearGroup.det (rowRep i j c * (torusPow F 2 ![l 0, l 1])⁻¹) =
      uniformizerUnit F ^ ((i : ℤ) + j - l 0 - l 1) := by
  rw [map_mul, map_inv, GlobalTheory.T.det_row_rep, GlobalTheory.T.det_torus_power, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← _root_.zpow_neg, ← _root_.zpow_add]
  congr 1
  ring

theorem inv_kd (l : Fin 3 → ℤ) (i j : ℕ) (c : Fin j → 𝓀[F]) :
    (rowRep i j c * (torusPow F 2 ![l 0, l 1])⁻¹)⁻¹ =
      uni2 (-(digitSum F j c) * ϖ ^ (l 0 - l 1 - i)) * torusPow F 2 ![l 0 - i, l 1 - j] := by
  rw [_root_.mul_inv_rev, inv_inv, GlobalTheory.T.torus_row_rep_factorization]

theorem row_A (l : Fin 3 → ℤ) (i j : ℕ) (c : Fin j → 𝓀[F]) (b : Fin 2) :
    (((torusPow F 2 ![l 2, l 2] * (rowRep i j c * (torusPow F 2 ![l 0, l 1])⁻¹))⁻¹ : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 1 b = if b = 1 then ϖ ^ (l 1 - j - l 2) else 0 := by
  rw [_root_.mul_inv_rev, inv_kd, mul_assoc, ← torusPow_neg, ← torusPow_add]
  have e : (![l 0 - i, l 1 - j] + -![l 2, l 2] : Fin 2 → ℤ) = ![l 0 - i - l 2, l 1 - j - l 2] := by
    ext t; fin_cases t <;> simp <;> ring
  rw [e, Units.val_mul, coe_torusPow]
  simp only [uni2]
  fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

theorem inn_rep {ψ : AddChar F Circle} (hψ : IsStd ψ) (l : Fin 3 → ℤ) (i j : ℕ) (c : Fin j → 𝓀[F]) :
    inn ψ (Φ0 F) (rowRep i j c * (torusPow F 2 ![l 0, l 1])⁻¹) (torusPow F 3 l) =
      if (j : ℤ) ≤ l 1 - l 2 then
        sqrtQ F ^ (2 * (2 * l 2 + i + j - l 0 - l 1)) * ((V2 ψ : ℝ) : ℂ) else 0 := by
  set k := rowRep i j c with hk
  set d := torusPow F 2 ![l 0, l 1] with hd
  set A := torusPow F 2 ![l 2, l 2] * (k * d⁻¹) with hA
  have hint : ∀ a b, (((k * d⁻¹ * d : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F] := by
    intro a b
    rw [inv_mul_cancel_right, hk, coe_rowRep]
    have h0 := (GLnLocal.uniformizer F).2
    fin_cases a <;> fin_cases b <;> simp
    · exact pow_mem h0 _
    · exact digitSum_mem _ _
    · exact pow_mem h0 _
  rw [(GlobalTheory.T.local_inner_product_support F ψ (k * d⁻¹) l).2 hint]
  have hrow : (∀ b, ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 b ∈ 𝒪[F]) ↔ (j : ℤ) ≤ l 1 - l 2 := by
    rw [Fin.forall_fin_two, hA, hk, hd, row_A, row_A]
    simp only [zero_ne_one, if_false, if_true, Subring.zero_mem, true_and, GlobalTheory.T.uniformizer_zpow_mem_integers_iff']
    constructor <;> intro h <;> linarith
  split_ifs with hj
  · rw [GlobalTheory.T.lattice_character_integral_value F ψ hψ A (hrow.2 hj), GlobalTheory.T.lattice_volume_gl_two_translate F ψ hψ A]
    have hdet : GeneralLinearGroup.det A = uniformizerUnit F ^ (2 * l 2 + i + j - l 0 - l 1) := by
      rw [hA, map_mul, GlobalTheory.T.det_torus_power, det_kd, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← _root_.zpow_add]
      congr 1
      ring
    have hm := GlobalTheory.T.unramified_character_uniformizer_power F (2 * l 2 + i + j - l 0 - l 1) (-2)
    rw [← hdet] at hm
    have hm' : mp (GeneralLinearGroup.det A) (-1) = ((modulus ((GeneralLinearGroup.det A : Fˣ) : F) : ℝ) : ℂ)⁻¹ := by
      simp [mp, Complex.cpow_neg_one]
    have e1 : (((-2 : ℤ) : ℂ) / 2) = -1 := by norm_num
    rw [e1, hm'] at hm
    push_cast
    rw [hm]
    congr 2
    ring
  · exact GlobalTheory.T.lattice_character_integral_zero F ψ hψ A (fun h => hj (hrow.1 h))

def Cc (ψ : AddChar F Circle) (l : Fin 3 → ℤ) (i j : ℕ) : ℂ :=
  sqrtQ F ^ (-(3 * ((i : ℤ) + j - l 0 - l 1))) * sqrtQ F ^ (2 * (2 * l 2 + i + j - l 0 - l 1)) *
    ((V2 ψ : ℝ) : ℂ)

theorem unramified_vector_rep_formula {ψ : AddChar F Circle} (hψ : IsStd ψ) (ν : Fˣ →* ℂˣ) (l : Fin 3 → ℤ) (i j : ℕ)
    (c : Fin j → 𝓀[F]) :
    f1 ψ ν l (rowRep i j c) = if (j : ℤ) ≤ l 1 - l 2 then
      ((ψ (-(digitSum F j c) * ϖ ^ (l 0 - l 1 - i)) : Circle) : ℂ) *
        s2 ψ ν (torusPow F 2 ![l 0 - i, l 1 - j]) * Cc ψ l i j else 0 := by
  unfold f1
  rw [inv_kd, GlobalTheory.T.whittaker_unipotent_equivariant_holds F ψ hψ, det_kd, inn_rep hψ]
  have hm := GlobalTheory.T.unramified_character_uniformizer_power F ((i : ℤ) + j - l 0 - l 1) 3
  have e : (((3 : ℤ) : ℂ) / 2) = 3 / 2 := by norm_num
  rw [e] at hm
  rw [hm]
  split_ifs
  · simp only [Cc]
    ring
  · simp


theorem sum_rep {ψ : AddChar F Circle} (hψ : IsStd ψ) (ν : Fˣ →* ℂˣ) (l : Fin 3 → ℤ) (i j : ℕ)
    (hj : (j : ℤ) ≤ l 1 - l 2) :
    ∑ c : Fin j → 𝓀[F], f1 ψ ν l (rowRep i j c) = if (i : ℤ) ≤ l 0 - l 1 then
      (qF F : ℂ) ^ j * s2 ψ ν (torusPow F 2 ![l 0 - i, l 1 - j]) * Cc ψ l i j else 0 := by
  simp_rw [unramified_vector_rep_formula hψ, if_pos hj]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  split_ifs with hi
  · rw [(GlobalTheory.T.digit_character_sum_values F ψ hψ j _).1 (by linarith)]
  · by_cases h2 : l 1 - j ≤ l 0 - i
    · rw [(GlobalTheory.T.digit_character_sum_values F ψ hψ j _).2 (by linarith) (by linarith)]
      simp
    · rw [(GlobalTheory.T.whittaker_torus_value_formula_holds F ψ hψ ν _ _).2 (not_le.1 h2)]
      simp


end Main


end GlobalTheory.CompanionTheory.LFUDom
