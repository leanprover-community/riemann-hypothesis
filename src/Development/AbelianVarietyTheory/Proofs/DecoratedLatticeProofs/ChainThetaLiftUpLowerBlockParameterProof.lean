import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerDiagonalBlockAsGLMemIntegralGeneralLinear
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeIdentityIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeEsymmScaledMultisetAddSegment
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsParahoricAndIntegralGLDoubleCosetReps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricDatumEigenvectorTwoBlockParahoric
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepChainStepMatrixCoefficientTwisted
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientIntegrationFormulaDiscreteSubgroupLeft
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenIsCompactTwoBlockParahoricSubgroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsParahoricAndIntegralGLDoubleCosetRepsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwoBlockParahoricLowerBlockDetTameCharacterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricDatumEigenvectorTwoBlockParahoricStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearModelSplitPlaceTwistSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralConjCuspFormParameterTransfer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainUpwardLiftHeckeParamTransferred
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitProjectionUnderEqResidueCardEqAbsNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftsCharOfResidueCharAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainSplittingCharactersResidueUnramifi

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ParHeckeTarget

open GlobalTheory.ParHeckeSource

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D D' : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

theorem inSupp_mul_left {y : Matrix (A ⊕ D') (A ⊕ D) k} (hy : InSupp y) {u : GL (A ⊕ D') k}
    (hu : u ∈ parahoric k A D') : InSupp (u.val * y) ∧
      valuation k ((u.val * y).toBlocks₁₁.det - u.val.toBlocks₁₁.det * y.toBlocks₁₁.det) < 1 := by
  have hJ := GlobalTheory.DatumEigen.int_of_mem hu
  have hl := (mem_parahoric.1 hu).2
  obtain ⟨hyi, hyd, hyl⟩ := hy
  have hprod : ∀ i l, (u.val * y) i l ∈ 𝒪[k] := fun i l => by
    rw [mul_apply]; exact sum_mem fun m _ => mul_mem (hJ i m) (hyi m l)
  have hcong : valuation k ((u.val * y).toBlocks₁₁.det - u.val.toBlocks₁₁.det * y.toBlocks₁₁.det) < 1 := by
    rw [← det_mul]
    refine GlobalTheory.DatumEigen.val_det_sub_lt (fun i l => hprod _ _) (fun i l => ?_) (fun i l => ?_)
    · rw [mul_apply]; exact sum_mem fun m _ => mul_mem (hJ _ _) (hyi _ _)
    · simp only [toBlocks₁₁, of_apply, mul_apply, Fintype.sum_sum_type, add_sub_cancel_left]
      exact Valuation.map_sum_lt _ one_ne_zero fun m _ => GlobalTheory.DatumEigen.val_mul_lt (hJ _ _) (hyl _ _)
  have hd1 : valuation k (u.val.toBlocks₁₁.det * y.toBlocks₁₁.det) = 1 := by
    rw [map_mul, hyd, mul_one, (GlobalTheory.DatumEigen.val_det_blocks hu).1]
  refine ⟨⟨hprod, ?_, ?_⟩, hcong⟩
  · rw [← hd1]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [hd1]; exact hcong
  · intro e a
    rw [mul_apply, Fintype.sum_sum_type]
    refine Valuation.map_add_lt _ (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)
      (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)
    · rw [mul_comm]; exact GlobalTheory.DatumEigen.val_mul_lt (hyi _ _) (hl _ _)
    · exact GlobalTheory.DatumEigen.val_mul_lt (hJ _ _) (hyl _ _)

omit [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] in
theorem torusElt_indic_int {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset D') :
    IsIntM (torusElt k D' ϖ (indic s)).val := by
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  rw [val_torusElt]
  intro i j
  rw [diagonal_apply]; split_ifs
  · show valuation k _ ≤ 1
    rw [map_zpow₀]
    exact zpow_le_one₀ (zero_lt_iff.2 (by simp)) hlt.le (by unfold indic; split_ifs <;> norm_num)
  · exact zero_mem _

theorem inSupp_diag_mul {y : Matrix (A ⊕ D') (A ⊕ D) k} (hy : InSupp y) {t : Matrix D' D' k} (ht : IsIntM t) :
    InSupp ((fromBlocks (1 : Matrix A A k) 0 0 t : Matrix (A ⊕ D') (A ⊕ D') k) * y) ∧
      ((fromBlocks (1 : Matrix A A k) 0 0 t : Matrix (A ⊕ D') (A ⊕ D') k) * y).toBlocks₁₁ = y.toBlocks₁₁ := by
  obtain ⟨h1, h2, h3⟩ := hy
  obtain ⟨a, b, c, e⟩ := isIntM_toBlocks (show IsIntM y from h1)
  rw [fromBlocks_diag_mul]
  refine ⟨⟨isIntM_fromBlocks_iff.2 ⟨a, b, isIntM_mul ht c, isIntM_mul ht e⟩, by simpa using h2, fun i j => ?_⟩,
    toBlocks_fromBlocks₁₁ _ _ _ _⟩
  rw [fromBlocks_apply₂₁]
  exact val_lt_mul ht (fun a b => h3 a b) i j

open Classical in

theorem coset_term : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ : kˣ →* ℂˣ), IsTame ξ → ∀ (s : Finset D') (j : GL (A ⊕ D') k), j ∈ parahoric k A D' → ∀ d : kˣ, (d : k) = j.1.toBlocks₂₂.det → ∀ x : Matrix (A ⊕ D') (A ⊕ D) k, (InSupp (((j * mtor ϖ (indic s))⁻¹).1 * x) → ((ξ d * (ξ (GeneralLinearGroup.det j))⁻¹ : ℂˣ) : ℂ) * datum ξ (((j * mtor ϖ (indic s))⁻¹).1 * x) = datum ξ x) ∧ (¬ InSupp (((j * mtor ϖ (indic s))⁻¹).1 * x) → datum ξ (((j * mtor ϖ (indic s))⁻¹).1 * x) = 0) := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ ξ hξ s j hj d hd x
  set y := ((j * mtor ϖ (indic s))⁻¹).1 * x with hydef
  refine ⟨fun hW => ?_, fun hW => by simp only [datum, dif_neg hW]⟩
  set T := torusElt k D' ϖ (indic s) with hT
  have hg0 : (mtor (A := A) ϖ (indic s)).val = fromBlocks (1 : Matrix A A k) 0 0 T.val := by
    rw [mtor_eq_dg, val_dg]
  have hx : x = j.val * ((mtor (A := A) ϖ (indic s)).val * y) := by
    rw [hydef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mul]
  obtain ⟨hg, hg11⟩ := inSupp_diag_mul hW (torusElt_indic_int hϖ s)
  rw [← hg0] at hg hg11
  obtain ⟨hs, hc⟩ := inSupp_mul_left hg hj
  rw [← hx, hg11] at hc
  rw [← hx] at hs
  obtain ⟨h11, h22⟩ := GlobalTheory.DatumEigen.val_det_blocks hj
  have n11 : j.val.toBlocks₁₁.det ≠ 0 := fun h0 => by rw [h0, map_zero] at h11; exact zero_ne_one h11
  set u₁ : kˣ := Units.mk0 _ n11 with hu₁
  have hdv : valuation k (d : k) = 1 := by rw [hd]; exact h22
  have t1 : ξ (GeneralLinearGroup.det j) = ξ (u₁ * d) := by
    refine GlobalTheory.DatumEigen.tame_eq hξ (by rw [Units.val_mul, map_mul, hdv, mul_one]; exact h11) ?_
    rw [Units.val_mul, hd, GeneralLinearGroup.val_det_apply]
    exact GlobalTheory.DatumEigen.det_cong hj
  have t2 : ξ (Units.mk0 _ hs.det_ne) = ξ (Units.mk0 _ hW.det_ne * u₁) := by
    refine GlobalTheory.DatumEigen.tame_eq hξ (by rw [Units.val_mul, map_mul, Units.val_mk0, hW.2.1, one_mul]; exact h11) ?_
    show valuation k (x.toBlocks₁₁.det - y.toBlocks₁₁.det * j.val.toBlocks₁₁.det) < 1
    rw [mul_comm (y.toBlocks₁₁.det)]
    exact hc
  simp only [datum, dif_pos hs, dif_pos hW]
  rw [t1, t2, ← Units.val_mul]
  congr 1
  simp only [map_mul]
  group

end GlobalTheory.ParHeckeTarget
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoric_hecke_sum_term_at_coset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ : kˣ →* ℂˣ), IsTame ξ → ∀ (s : Finset D') (j : GL (A ⊕ D') k), j ∈ parahoric k A D' → ∀ d : kˣ, (d : k) = j.1.toBlocks₂₂.det → ∀ x : Matrix (A ⊕ D') (A ⊕ D) k, (InSupp (((j * mtor ϖ (indic s))⁻¹).1 * x) → ((ξ d * (ξ (GeneralLinearGroup.det j))⁻¹ : ℂˣ) : ℂ) * datum ξ (((j * mtor ϖ (indic s))⁻¹).1 * x) = datum ξ x) ∧ (¬ InSupp (((j * mtor ϖ (indic s))⁻¹).1 * x) → datum ξ (((j * mtor ϖ (indic s))⁻¹).1 * x) = 0) := by
  atlas_forward_decl GlobalTheory.ParHeckeTarget.coset_term
end

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ParHeckeTarget

open GlobalTheory.ParHeckeSource

variable {k : Type} [Field k] [ValuativeRel k]

theorem val_lt_mul_right {l m n : Type} [Fintype m] {c : Matrix l m k} {P : Matrix m n k}
    (hc : ∀ i j, valuation k (c i j) < 1) (hP : IsIntM P) (i j) : valuation k ((c * P) i j) < 1 := by
  rw [mul_apply]
  exact Valuation.map_sum_lt _ one_ne_zero fun m _ => by
    rw [mul_comm]; exact GlobalTheory.DatumEigen.val_mul_lt (hP _ _) (hc _ _)

theorem isIntM_of_lt {m n : Type} {M : Matrix m n k} (h : ∀ i j, valuation k (M i j) < 1) : IsIntM M :=
  fun i j => (show valuation k (M i j) ≤ 1 from (h i j).le)

section Alg
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

def nlow (v : Matrix D A k) : GL (A ⊕ D) k :=
  ⟨fromBlocks 1 0 v 1, fromBlocks 1 0 (-v) 1, by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩

theorem val_nlow (v : Matrix D A k) : (nlow v).val = fromBlocks 1 0 v 1 := rfl

end Alg

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D D' : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

theorem nlow_mem {v : Matrix D' A k} (hv : ∀ i j, valuation k (v i j) < 1) : nlow v ∈ parahoric k A D' := by
  refine mem_parahoric_of ?_ ?_ fun i j => by simpa [val_nlow] using hv i j
  · rw [val_nlow]; exact isIntM_fromBlocks_iff.2 ⟨isIntM_one, isIntM_zero, isIntM_of_lt hv, isIntM_one⟩
  · rw [val_nlow, det_fromBlocks_zero₁₂, det_one, det_one, one_mul, map_one]

theorem torus_int {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset D) :
    IsIntM (torusElt k D ϖ (indic s)).val := by
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  rw [val_torusElt]
  intro i j
  rw [diagonal_apply]; split_ifs
  · show valuation k _ ≤ 1
    rw [map_zpow₀]
    exact zpow_le_one₀ (zero_lt_iff.2 (by simp)) hlt.le (by unfold indic; split_ifs <;> norm_num)
  · exact zero_mem _

theorem nlow_mul_eq {x : Matrix (A ⊕ D') (A ⊕ D) k} (hx : InSupp x) :
    (nlow (-(x.toBlocks₂₁ * x.toBlocks₁₁⁻¹))).val * x = fromBlocks x.toBlocks₁₁ x.toBlocks₁₂ 0 (schur x) := by
  have hu : IsUnit x.toBlocks₁₁.det := isUnit_iff_ne_zero.2 hx.det_ne
  have hxe := fromBlocks_toBlocks x
  set a := x.toBlocks₁₁
  set b := x.toBlocks₁₂
  set c := x.toBlocks₂₁
  set e := x.toBlocks₂₂
  rw [schur, ← hxe, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
  rw [val_nlow, fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  · rw [Matrix.neg_mul, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one, neg_add_cancel]
  · rw [Matrix.neg_mul]; abel

theorem inSupp_mul_iff {x : Matrix (A ⊕ D') (A ⊕ D) k} (hx : InSupp x) (V : Matrix (A ⊕ D') (A ⊕ D') k)
    (h11 : IsIntM V.toBlocks₁₁) (hd : valuation k V.toBlocks₁₁.det = 1) (h12 : IsIntM V.toBlocks₁₂) :
    InSupp (V * fromBlocks x.toBlocks₁₁ x.toBlocks₁₂ 0 (schur x)) ↔
      (∀ i l, valuation k (V.toBlocks₂₁ i l) < 1) ∧ IsIntM (V.toBlocks₂₂ * schur x) := by
  have hxI : IsIntM x := hx.1
  obtain ⟨i11, i12, -, -⟩ := isIntM_toBlocks hxI
  have inv11 : IsIntM x.toBlocks₁₁⁻¹ := isIntM_inv i11 hx.2.1
  have hu : IsUnit x.toBlocks₁₁.det := isUnit_iff_ne_zero.2 hx.det_ne
  have hS := schur_int hx
  have e : V * fromBlocks x.toBlocks₁₁ x.toBlocks₁₂ 0 (schur x) = fromBlocks (V.toBlocks₁₁ * x.toBlocks₁₁)
      (V.toBlocks₁₁ * x.toBlocks₁₂ + V.toBlocks₁₂ * schur x) (V.toBlocks₂₁ * x.toBlocks₁₁)
      (V.toBlocks₂₁ * x.toBlocks₁₂ + V.toBlocks₂₂ * schur x) := by
    conv_lhs => rw [← fromBlocks_toBlocks V]
    rw [fromBlocks_multiply]; simp
  rw [e]
  constructor
  · rintro ⟨hI, -, hl⟩
    obtain ⟨-, -, -, d⟩ := isIntM_fromBlocks_iff.1 (show IsIntM _ from hI)
    have hR : ∀ i l, valuation k (V.toBlocks₂₁ i l) < 1 := by
      have e2 : V.toBlocks₂₁ = V.toBlocks₂₁ * x.toBlocks₁₁ * x.toBlocks₁₁⁻¹ := by
        rw [Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
      intro i l; rw [e2]
      exact val_lt_mul_right (fun a b => by simpa using hl a b) inv11 i l
    refine ⟨hR, ?_⟩
    have e3 : V.toBlocks₂₂ * schur x =
        (V.toBlocks₂₁ * x.toBlocks₁₂ + V.toBlocks₂₂ * schur x) - V.toBlocks₂₁ * x.toBlocks₁₂ := by abel
    rw [e3]; exact isIntM_sub d (isIntM_mul (isIntM_of_lt hR) i12)
  · rintro ⟨hR, hUS⟩
    have iR := isIntM_of_lt hR
    refine ⟨isIntM_fromBlocks_iff.2 ⟨isIntM_mul h11 i11, ?_, isIntM_mul iR i11, ?_⟩, ?_, ?_⟩
    · exact fun a b => add_mem (isIntM_mul h11 i12 a b) (isIntM_mul h12 hS a b)
    · exact fun a b => add_mem (isIntM_mul iR i12 a b) (hUS a b)
    · rw [toBlocks_fromBlocks₁₁, det_mul, map_mul, hd, hx.2.1, one_mul]
    · intro i l; rw [fromBlocks_apply₂₁]; exact val_lt_mul_right hR i11 i l

theorem key_mem {Y : GL (A ⊕ D') k} (hY : Y ∈ parahoric k A D') {E T : GL D' k} (hE : E ∈ KO k D')
    (hEY : E.val = Y.val.toBlocks₂₂) (hT : IsIntM T.val)
    (hl : ∀ i l, valuation k (((T⁻¹).val * Y.val.toBlocks₂₁) i l) < 1) :
    dg A T⁻¹ * Y * dg A (E⁻¹ * T) ∈ parahoric k A D' := by
  obtain ⟨y11, y12, -, -⟩ := isIntM_toBlocks (isIntM_of_mem_parahoric hY)
  have hv : (dg A T⁻¹ * Y * dg A (E⁻¹ * T)).val =
      fromBlocks Y.val.toBlocks₁₁ (Y.val.toBlocks₁₂ * (E⁻¹ * T).val) ((T⁻¹).val * Y.val.toBlocks₂₁) 1 := by
    rw [Units.val_mul, Units.val_mul, val_dg, val_dg, fromBlocks_diag_mul, mul_fromBlocks_diag]
    simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
    congr 1
    rw [← hEY, ← Units.val_mul, ← Units.val_mul, show T⁻¹ * E * (E⁻¹ * T) = 1 by group, Units.val_one]
  refine mem_parahoric_of ?_ ?_ ?_
  · rw [hv]
    have hq : IsIntM (E⁻¹ * T).val := by
      rw [Units.val_mul]; exact isIntM_mul (isIntM_of_mem_KO (inv_mem hE)) hT
    exact isIntM_fromBlocks_iff.2 ⟨y11, isIntM_mul y12 hq, isIntM_of_lt hl, isIntM_one⟩
  · have h1 : (T⁻¹).val.det * T.val.det = 1 := by
      rw [← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]
    have e : (dg A T⁻¹ * Y * dg A (E⁻¹ * T)).val.det = ((T⁻¹).val.det * T.val.det) * Y.val.det * (E⁻¹).val.det := by
      rw [Units.val_mul, Units.val_mul, det_mul, det_mul, det_dg, det_dg, Units.val_mul, det_mul]; ring
    rw [e, h1, one_mul, map_mul, val_det_of_mem_KO (mem_parahoric.1 hY).1, val_det_of_mem_KO (inv_mem hE), one_mul]
  · intro i l
    rw [hv]; simpa using hl i l

end GlobalTheory.ParHeckeTarget

namespace GlobalTheory.ParHeckeTarget

open GlobalTheory.ParHeckeSource
open Classical

theorem card_filter_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D') (R : Finset (GL (A ⊕ D') k)) d, IsReps (mtor ϖ (indic s)) R d → ∀ RK, IsRepsK (torusElt k D' ϖ (indic s)) RK → ∀ x : Matrix (A ⊕ D') (A ⊕ D) k, InSupp x → (R.filter fun j => InSupp (((j * mtor ϖ (indic s))⁻¹).1 * x)).card = (RK.filter fun g => ∀ i l, ((g⁻¹).1 * schur x) i l ∈ 𝒪[k]).card := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ s R d hR RK hRK x hx
  rw [mtor_eq_dg] at hR ⊢
  set T := torusElt k D' ϖ (indic s) with hTdef
  have hT : IsIntM T.val := torus_int hϖ s
  set S := schur x with hSdef
  have hν : ∀ i l, valuation k ((-(x.toBlocks₂₁ * x.toBlocks₁₁⁻¹)) i l) < 1 := by
    obtain ⟨i11, -, -, -⟩ := isIntM_toBlocks (show IsIntM x from hx.1)
    intro i l
    rw [Matrix.neg_apply, Valuation.map_neg]
    exact val_lt_mul_right (fun a b => hx.2.2 a b) (isIntM_inv i11 hx.2.1) i l
  set c := nlow (-(x.toBlocks₂₁ * x.toBlocks₁₁⁻¹)) with hcdef
  have hc : c ∈ parahoric k A D' := nlow_mem hν
  have hcx : c.val * x = fromBlocks x.toBlocks₁₁ x.toBlocks₁₂ 0 S := nlow_mul_eq hx
  have hJR : ∀ j ∈ R, j ∈ parahoric k A D' := fun j hj => (hR.1 j hj).1
  have hcond : ∀ j ∈ parahoric k A D', InSupp (((j * dg A T)⁻¹).val * x) ↔
      (∀ i l, valuation k (((T⁻¹).val * ((c * j)⁻¹).val.toBlocks₂₁) i l) < 1) ∧
        IsIntM ((T⁻¹).val * ((c * j)⁻¹).val.toBlocks₂₂ * S) := by
    intro j hj
    have hY : (c * j)⁻¹ ∈ parahoric k A D' := inv_mem (mul_mem hc hj)
    have e1 : (j * dg A T)⁻¹ = dg A T⁻¹ * (c * j)⁻¹ * c := by rw [map_inv]; group
    have e2 : (dg A T⁻¹ * (c * j)⁻¹).val = fromBlocks ((c * j)⁻¹).val.toBlocks₁₁ ((c * j)⁻¹).val.toBlocks₁₂
        ((T⁻¹).val * ((c * j)⁻¹).val.toBlocks₂₁) ((T⁻¹).val * ((c * j)⁻¹).val.toBlocks₂₂) := by
      rw [Units.val_mul, val_dg, fromBlocks_diag_mul]
    obtain ⟨y11, y12, -, -⟩ := isIntM_toBlocks (isIntM_of_mem_parahoric hY)
    rw [e1, Units.val_mul (dg A T⁻¹ * (c * j)⁻¹) c, Matrix.mul_assoc, hcx,
      inSupp_mul_iff hx _ (by rw [e2, toBlocks_fromBlocks₁₁]; exact y11)
        (by rw [e2, toBlocks_fromBlocks₁₁]; exact (GlobalTheory.DatumEigen.val_det_blocks hY).1)
        (by rw [e2, toBlocks_fromBlocks₁₂]; exact y12),
      e2, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
  have hkey : ∀ j ∈ parahoric k A D', (∀ i l, valuation k (((T⁻¹).val * ((c * j)⁻¹).val.toBlocks₂₁) i l) < 1) →
      (c * j * dg A T)⁻¹ * dg A ((lowerDiagonalBlockAsGL ((c * j)⁻¹))⁻¹ * T) ∈ parahoric k A D' := fun j hj hl => by
    have hY : (c * j)⁻¹ ∈ parahoric k A D' := inv_mem (mul_mem hc hj)
    have := key_mem hY (lowerDiagonalBlockAsGL_mem_integralGeneralLinear hY) (lowerDiagonalBlockAsGL_val_eq_toBlocks_two_two hY) hT hl
    rw [show (c * j * dg A T)⁻¹ = dg A T⁻¹ * (c * j)⁻¹ by rw [map_inv]; group]
    exact this
  let pick : GL (A ⊕ D') k → GL D' k := fun j =>
    if h : ∃ g, g ∈ RK ∧ g⁻¹ * ((lowerDiagonalBlockAsGL ((c * j)⁻¹))⁻¹ * T) ∈ KO k D' then h.choose else 1
  have spec : ∀ j ∈ parahoric k A D', pick j ∈ RK ∧ (pick j)⁻¹ * ((lowerDiagonalBlockAsGL ((c * j)⁻¹))⁻¹ * T) ∈ KO k D' :=
    fun j hj => by
      have hY : (c * j)⁻¹ ∈ parahoric k A D' := inv_mem (mul_mem hc hj)
      have h := (hRK.2 _ (inv_mem (lowerDiagonalBlockAsGL_mem_integralGeneralLinear hY))).exists
      simp only [pick, dif_pos h]; exact h.choose_spec
  have uniq : ∀ j ∈ parahoric k A D', ∀ g ∈ RK, g⁻¹ * ((lowerDiagonalBlockAsGL ((c * j)⁻¹))⁻¹ * T) ∈ KO k D' → pick j = g :=
    fun j hj g hg h => (hRK.2 _ (inv_mem (lowerDiagonalBlockAsGL_mem_integralGeneralLinear (inv_mem (mul_mem hc hj))))).unique (spec j hj) ⟨hg, h⟩
  apply Finset.card_nbij pick
  · intro j hj
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter] at hj ⊢
    obtain ⟨hjR, hin⟩ := hj
    have hJ := hJR j hjR
    have hY : (c * j)⁻¹ ∈ parahoric k A D' := inv_mem (mul_mem hc hJ)
    obtain ⟨-, h22⟩ := (hcond j hJ).1 hin
    obtain ⟨hg, hK⟩ := spec j hJ
    refine ⟨hg, ?_⟩
    have e : ((pick j)⁻¹).val = ((pick j)⁻¹ * ((lowerDiagonalBlockAsGL ((c * j)⁻¹))⁻¹ * T)).val *
        ((T⁻¹).val * (lowerDiagonalBlockAsGL ((c * j)⁻¹)).val) := by
      rw [← Units.val_mul, ← Units.val_mul]; congr 1; group
    have : IsIntM (((pick j)⁻¹).val * S) := by
      rw [e, Matrix.mul_assoc, lowerDiagonalBlockAsGL_val_eq_toBlocks_two_two hY]
      exact isIntM_mul (isIntM_of_mem_KO hK) h22
    exact this
  · intro j₁ hj₁ j₂ hj₂ he
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hj₁ hj₂
    obtain ⟨h1R, h1⟩ := hj₁
    obtain ⟨h2R, h2⟩ := hj₂
    have hJ1 := hJR _ h1R
    have hJ2 := hJR _ h2R
    have m1 := hkey j₁ hJ1 ((hcond j₁ hJ1).1 h1).1
    have m2 := hkey j₂ hJ2 ((hcond j₂ hJ2).1 h2).1
    obtain ⟨-, hK1⟩ := spec j₁ hJ1
    obtain ⟨-, hK2⟩ := spec j₂ hJ2
    rw [he] at hK1
    have hm : (j₁ * dg A T)⁻¹ * (j₂ * dg A T) ∈ parahoric k A D' := by
      have := mul_mem (mul_mem (mul_mem m1 (dg_mem (inv_mem hK1))) (dg_mem hK2)) (inv_mem m2)
      convert this using 1
      simp only [map_mul, map_inv]; group
    exact (hR.2 j₂ hJ2).unique ⟨h1R, hm⟩ ⟨h2R, by simp⟩
  · intro g hg
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter] at hg
    obtain ⟨hgR, hSg⟩ := hg
    obtain ⟨κ, hκ, κ', hκ', hgdef⟩ := hRK.1 g hgR
    have hj₀ : c⁻¹ * dg A κ ∈ parahoric k A D' := mul_mem (inv_mem hc) (dg_mem hκ)
    obtain ⟨j, ⟨hjR, hm⟩, -⟩ := hR.2 _ hj₀
    set n := (j * dg A T)⁻¹ * (c⁻¹ * dg A κ * dg A T) with hndef
    have hJ := hJR j hjR
    have hY : (c * j)⁻¹ ∈ parahoric k A D' := inv_mem (mul_mem hc hJ)
    have eV : dg A T⁻¹ * (c * j)⁻¹ = n * dg A (κ * T)⁻¹ := by
      rw [hndef]; simp only [map_mul, map_inv]; group
    have hb : ∀ (P : Matrix (A ⊕ D') (A ⊕ D') k), P = (dg A T⁻¹ * (c * j)⁻¹).val →
        P.toBlocks₂₁ = (T⁻¹).val * ((c * j)⁻¹).val.toBlocks₂₁ ∧
          P.toBlocks₂₂ = (T⁻¹).val * ((c * j)⁻¹).val.toBlocks₂₂ := by
      rintro P rfl
      rw [Units.val_mul, val_dg, fromBlocks_diag_mul, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
      exact ⟨rfl, rfl⟩
    obtain ⟨h21, h22⟩ := hb _ (by rw [eV])
    rw [Units.val_mul, val_dg, mul_fromBlocks_diag, toBlocks_fromBlocks₂₁] at h21
    rw [Units.val_mul, val_dg, mul_fromBlocks_diag, toBlocks_fromBlocks₂₂] at h22
    have hE : lowerDiagonalBlockAsGL ((c * j)⁻¹) = T * lowerDiagonalBlockAsGL n * (κ * T)⁻¹ := by
      ext1
      rw [lowerDiagonalBlockAsGL_val_eq_toBlocks_two_two hY, Units.val_mul, Units.val_mul, lowerDiagonalBlockAsGL_val_eq_toBlocks_two_two hm, Matrix.mul_assoc, h22, ← Matrix.mul_assoc,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    have hpick : pick j = g := by
      refine uniq j hJ g hgR ?_
      rw [hE, hgdef, show (κ * T * κ')⁻¹ * ((T * lowerDiagonalBlockAsGL n * (κ * T)⁻¹)⁻¹ * T) = κ'⁻¹ * (lowerDiagonalBlockAsGL n)⁻¹ by group]
      exact mul_mem (inv_mem hκ') (inv_mem (lowerDiagonalBlockAsGL_mem_integralGeneralLinear hm))
    refine ⟨j, ?_, hpick⟩
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter]
    refine ⟨hjR, (hcond j hJ).2 ⟨fun i l => ?_, ?_⟩⟩
    · rw [← h21]; exact (mem_parahoric.1 hm).2 i l
    · rw [← h22, show (κ * T)⁻¹ = κ' * g⁻¹ by rw [hgdef]; group, Units.val_mul κ' g⁻¹, ← Matrix.mul_assoc,
        Matrix.mul_assoc]
      exact isIntM_mul (isIntM_mul (isIntM_toBlocks (isIntM_of_mem_parahoric hm)).2.2.2 (isIntM_of_mem_KO hκ')) hSg

end GlobalTheory.ParHeckeTarget
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_filter_parahoric_cosets_eq_schur_count : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D') (R : Finset (GL (A ⊕ D') k)) d, IsReps (mtor ϖ (indic s)) R d → ∀ RK, IsRepsK (torusElt k D' ϖ (indic s)) RK → ∀ x : Matrix (A ⊕ D') (A ⊕ D) k, InSupp x → (R.filter fun j => InSupp (((j * mtor ϖ (indic s))⁻¹).1 * x)).card = (RK.filter fun g => ∀ i l, ((g⁻¹).1 * schur x) i l ∈ 𝒪[k]).card := by
  atlas_forward_decl GlobalTheory.ParHeckeTarget.card_filter_eq
end

section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

open Classical

namespace GlobalTheory.ParHeckeTarget

theorem sum_reps_datum_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ : kˣ →* ℂˣ), IsTame ξ → ∀ (s : Finset D') (R : Finset (GL (A ⊕ D') k)) d, IsReps (mtor ϖ (indic s)) R d → ∀ RK, IsRepsK (torusElt k D' ϖ (indic s)) RK → ∀ x : Matrix (A ⊕ D') (A ⊕ D) k, ∑ j ∈ R, ((ξ (d j) * (ξ (GeneralLinearGroup.det j))⁻¹ : ℂˣ) : ℂ) * datum ξ (((j * mtor ϖ (indic s))⁻¹).1 * x) = ∑ g ∈ RK, liftS ξ (fun y => intInd ((g⁻¹).1 * y)) x := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ ξ hξ s R d hR RK hRK x
  have hL : ∀ j ∈ R, ((ξ (d j) * (ξ (GeneralLinearGroup.det j))⁻¹ : ℂˣ) : ℂ) * datum ξ (((j * mtor ϖ (indic s))⁻¹).1 * x) =
      if InSupp (((j * mtor ϖ (indic s))⁻¹).1 * x) then datum ξ x else 0 := by
    intro j hj
    have h := GlobalTheory.T.parahoric_hecke_sum_term_at_coset k A D D' ϖ hϖ ξ hξ s j (hR.1 j hj).1 (d j) (hR.1 j hj).2 x
    split_ifs with hs
    · exact h.1 hs
    · rw [h.2 hs, mul_zero]
  have hRt : ∀ g ∈ RK, liftS ξ (fun y => intInd ((g⁻¹).1 * y)) x =
      if (∀ i l, ((g⁻¹).1 * schur x) i l ∈ 𝒪[k]) then datum ξ x else 0 := by
    intro g _
    simp only [liftS, intInd]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hRt, ← Finset.sum_filter, ← Finset.sum_filter,
    Finset.sum_const, Finset.sum_const]
  by_cases hx : InSupp x
  · rw [GlobalTheory.T.card_filter_parahoric_cosets_eq_schur_count k A D D' ϖ hϖ s R d hR RK hRK x hx]
  · have h0 : datum ξ x = 0 := by simp only [datum, dif_neg hx]
    simp [h0]

end GlobalTheory.ParHeckeTarget
end
end

section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ParHecke.StringEig

open GlobalTheory.ChainOnto (esymm_add_C esymm_map_mul_C esymm_string esymm_eq_zero_of_lt sqrt_sq_C natCast_cpow_half)

theorem map_coe_segL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) (z : ℂˣ) (t : ℕ) :
    (segL ϖ z t).map (fun b : ℂˣ => (b : ℂ)) =
      (Finset.range t).val.map fun i : ℕ => (z : ℂ) * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ ((t : ℤ) - 1 - 2 * i) := by
  rw [segL, Multiset.map_map, Finset.range_val]
  refine Multiset.map_congr rfl fun i _ => ?_
  simp only [Function.comp_apply, Units.val_mul]
  congr 1
  rw [GlobalTheory.MellinPoly.absPow_eq_zpow, ord_eq_one hϖ, zpow_one, ← natCast_cpow_half]
  congr 1
  push_cast
  ring

theorem genVal_add_segL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (r N t n₀ : ℕ) (B : Multiset ℂˣ) (zS zT : ℂˣ), B.card = N → n₀ ≤ N + t → genVal (resCard k) r (N + t) (B.map (· * (zS * zT⁻¹)) + segL ϖ zS t) n₀ = (zS : ℂ) ^ n₀ * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (n₀ * (r + N)) * ∑ n ∈ Finset.range (N + 1), (if n ≤ n₀ then ((resCard k ^ (n * (t - (n₀ - n))) * Formalism.L2.Col.gaussBin (resCard k) t (n₀ - n) : ℕ) : ℂ) else 0) * (((zT : ℂ) ^ n * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (n * (r + N + t)))⁻¹ * genVal (resCard k) r N B n) := by
  intro k _ _ _ _ ϖ hϖ r N t n₀ B zS zT hB hn₀
  set Q := resCard k with hQdef
  have hsQ := sqrt_sq_C Q
  have hs : ((Real.sqrt Q : ℝ) : ℂ) ≠ 0 := by
    intro h0
    rw [h0] at hsQ
    have h1 : 1 < Q := one_lt_resCard k
    have : ((Q : ℕ) : ℂ) = 0 := by rw [← hsQ]; ring
    exact (by omega : Q ≠ 0) (by exact_mod_cast this)
  set s : ℂ := ((Real.sqrt Q : ℝ) : ℂ) with hsdef
  have hA : (B.map (· * (zS * zT⁻¹))).map (fun b : ℂˣ => (b : ℂ)) =
      (B.map fun b : ℂˣ => (b : ℂ)).map fun x => ((zS : ℂ) * (zT : ℂ)⁻¹) * x := by
    simp [Multiset.map_map, Function.comp_def, mul_comm]
  have hBc : (B.map fun b : ℂˣ => (b : ℂ)).card = N := by simp [hB]
  set F : ℕ → ℂ := fun n => (if n ≤ n₀ then ((Q ^ (n * (t - (n₀ - n))) * Formalism.L2.Col.gaussBin Q t (n₀ - n) : ℕ) : ℂ) else 0) *
    (((zT : ℂ) ^ n * s ^ (n * (r + N + t)))⁻¹ * genVal Q r N B n) with hF
  have hFa : ∀ j, N < j → F j = 0 := by
    intro j hj
    simp only [hF, genVal, esymm_eq_zero_of_lt _ (hBc ▸ hj), mul_zero]
  have hFk : ∀ j, n₀ < j → F j = 0 := by
    intro j hj
    simp only [hF, if_neg (show ¬ j ≤ n₀ by omega), zero_mul]
  have hR : ∑ j ∈ Finset.range (N + 1), F j = ∑ j ∈ Finset.range (n₀ + 1), F j := by
    rw [Finset.sum_subset (Finset.range_mono (show N + 1 ≤ N + n₀ + 1 by omega))
        (fun j _ hn => hFa j (by simp at hn; omega)),
      Finset.sum_subset (Finset.range_mono (show n₀ + 1 ≤ N + n₀ + 1 by omega))
        (fun j _ hn => hFk j (by simp at hn; omega))]
  rw [hR, genVal, Multiset.map_add, esymm_add_C, Finset.mul_sum, Finset.mul_sum, hA, map_coe_segL k ϖ hϖ]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ n₀ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [esymm_map_mul_C, esymm_string Q s zS hs hsQ t]
  simp only [hF, if_pos hjk, genVal]
  by_cases hjN : j ≤ N
  · by_cases hat : n₀ - j ≤ t
    · have hsI : s ^ (r * n₀ + n₀ * (N + t - n₀)) * s ^ (-(((n₀ - j : ℕ) : ℤ) * ((t : ℤ) - ((n₀ - j : ℕ) : ℤ)))) =
          s ^ (n₀ * (r + N)) * (s ^ 2) ^ (j * (t - (n₀ - j))) * (s ^ (j * (r + N + t)))⁻¹ * s ^ (r * j + j * (N - j)) := by
        rw [← pow_mul]
        simp only [← zpow_natCast, ← _root_.zpow_neg, ← zpow_add₀ hs]
        congr 1
        push_cast [Nat.cast_sub hjN, Nat.cast_sub hjk, Nat.cast_sub hat, Nat.cast_sub hn₀]
        ring
      have hz : ((zS : ℂ) * (zT : ℂ)⁻¹) ^ j * (zS : ℂ) ^ (n₀ - j) = (zS : ℂ) ^ n₀ * ((zT : ℂ) ^ j)⁻¹ := by
        rw [mul_pow, mul_right_comm, ← pow_add, Nat.add_sub_cancel' hjk, inv_pow]
      calc _ = (s ^ (r * n₀ + n₀ * (N + t - n₀)) * s ^ (-(((n₀ - j : ℕ) : ℤ) * ((t : ℤ) - ((n₀ - j : ℕ) : ℤ))))) *
            (((zS : ℂ) * (zT : ℂ)⁻¹) ^ j * (zS : ℂ) ^ (n₀ - j)) *
            ((Formalism.L2.Col.gaussBin Q t (n₀ - j) : ℂ) * (B.map fun b : ℂˣ => (b : ℂ)).esymm j) := by ring
        _ = (s ^ (n₀ * (r + N)) * (s ^ 2) ^ (j * (t - (n₀ - j))) * (s ^ (j * (r + N + t)))⁻¹ * s ^ (r * j + j * (N - j))) *
            ((zS : ℂ) ^ n₀ * ((zT : ℂ) ^ j)⁻¹) *
            ((Formalism.L2.Col.gaussBin Q t (n₀ - j) : ℂ) * (B.map fun b : ℂˣ => (b : ℂ)).esymm j) := by rw [hsI, hz]
        _ = _ := by rw [hsQ]; push_cast; rw [mul_inv]; ring
    · rw [Formalism.L2.Col.gaussBin_eq_zero Q (show t < n₀ - j by omega)]
      simp
  · rw [esymm_eq_zero_of_lt _ (by omega)]
    simp

end GlobalTheory.ParHecke.StringEig

end
end

section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.DatumEigenLeft

open GlobalTheory.DatumEigen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D D' : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

omit [Fintype D] [DecidableEq D] in

theorem inSupp_mul_left {x : Matrix (A ⊕ D') (A ⊕ D) k} (hx : InSupp x) {j : GL (A ⊕ D') k}
    (hj : j ∈ parahoric k A D') : InSupp (j.val * x) ∧
      valuation k ((j.val * x).toBlocks₁₁.det - j.val.toBlocks₁₁.det * x.toBlocks₁₁.det) < 1 := by
  have hJ := int_of_mem hj
  have hl := (mem_parahoric.1 hj).2
  obtain ⟨hxi, hxd, hxl⟩ := hx
  have hprod : ∀ i l, (j.val * x) i l ∈ 𝒪[k] := fun i l => by
    rw [mul_apply]; exact sum_mem fun m _ => mul_mem (hJ i m) (hxi m l)
  have hcong : valuation k ((j.val * x).toBlocks₁₁.det - j.val.toBlocks₁₁.det * x.toBlocks₁₁.det) < 1 := by
    rw [← det_mul]
    refine val_det_sub_lt (fun i l => hprod _ _) (fun i l => ?_) (fun i l => ?_)
    · rw [mul_apply]; exact sum_mem fun m _ => mul_mem (hJ _ _) (hxi _ _)
    · simp only [toBlocks₁₁, of_apply, mul_apply, Fintype.sum_sum_type, add_sub_cancel_left]
      exact Valuation.map_sum_lt _ one_ne_zero fun m _ => val_mul_lt (hJ _ _) (hxl _ _)
  have hd1 : valuation k (j.val.toBlocks₁₁.det * x.toBlocks₁₁.det) = 1 := by
    rw [map_mul, hxd, mul_one, (val_det_blocks hj).1]
  refine ⟨⟨hprod, ?_, ?_⟩, hcong⟩
  · rw [← hd1]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [hd1]; exact hcong
  · intro e a
    rw [mul_apply, Fintype.sum_sum_type]
    refine Valuation.map_add_lt _ (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)
      (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)
    · rw [mul_comm]; exact val_mul_lt (hxi _ _) (hl _ _)
    · exact val_mul_lt (hJ _ _) (hxl _ _)

end GlobalTheory.DatumEigenLeft

namespace GlobalTheory.DatumEigenLeft
open GlobalTheory.DatumEigen

theorem omTwo_datum_inv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ξ μS μT : kˣ →* ℂˣ), IsTame ξ → IsUnram (μS * ξ⁻¹) → ∀ j ∈ parahoric k A D', ∀ d : kˣ, (d : k) = (j : Matrix (A ⊕ D') (A ⊕ D') k).toBlocks₂₂.det → omTwo μS μT (1 : GL (A ⊕ D) k) j (datum ξ⁻¹ : Matrix (A ⊕ D') (A ⊕ D) k → ℂ) = (ξ d : ℂ) • (datum ξ⁻¹ : Matrix (A ⊕ D') (A ⊕ D) k → ℂ) := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ξ μS μT hξ hμ j hj d hd
  funext x
  have hK := (mem_parahoric.1 hj).1
  have hdetv : valuation k (GeneralLinearGroup.det j : k) = 1 := (nabs_eq_one_iff _).1 (nabs_det_of_mem_KO hK)
  have hμj : μS (GeneralLinearGroup.det j) = ξ (GeneralLinearGroup.det j) := by
    have := hμ _ hdetv
    rwa [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one] at this
  simp only [omTwo, om, Pi.smul_apply, smul_eq_mul, nabs_det_of_mem_KO hK, MonoidHom.mul_apply, MonoidHom.inv_apply,
    map_one, inv_one, Units.val_one, one_mul, Real.one_rpow, Complex.ofReal_one, mul_one, inv_inv]
  rw [show nabs k 1 = 1 by simp [nabs], Real.one_rpow, Complex.ofReal_one, mul_one, Matrix.mul_one, Units.val_mul,
    hμj]
  have hT : (μT (GeneralLinearGroup.det j) : ℂ) ≠ 0 := Units.ne_zero _
  have e1 : ((ξ (GeneralLinearGroup.det j) : ℂ) * (((μT (GeneralLinearGroup.det j))⁻¹ : ℂˣ) : ℂ)) *
      ((μT (GeneralLinearGroup.det j) : ℂ) * datum ξ⁻¹ ((j⁻¹ : GL (A ⊕ D') k).val * x)) =
      (ξ (GeneralLinearGroup.det j) : ℂ) * datum ξ⁻¹ ((j⁻¹ : GL (A ⊕ D') k).val * x) := by
    rw [Units.val_inv_eq_inv_val]; field_simp
  rw [e1]
  have hx : x = j.val * ((j⁻¹ : GL (A ⊕ D') k).val * x) := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  generalize (j⁻¹ : GL (A ⊕ D') k).val * x = y at hx ⊢
  subst hx
  unfold datum
  obtain ⟨h11, h22⟩ := val_det_blocks hj
  by_cases hy : InSupp y
  · obtain ⟨hs, hc⟩ := inSupp_mul_left hy hj
    have n11 : j.val.toBlocks₁₁.det ≠ 0 := fun h0 => by rw [h0, map_zero] at h11; exact zero_ne_one h11
    set u : kˣ := Units.mk0 _ n11 with hu
    have hdv : valuation k (d : k) = 1 := by rw [hd]; exact h22
    have t1 : ξ (GeneralLinearGroup.det j) = ξ (u * d) := by
      refine tame_eq hξ (by rw [Units.val_mul, map_mul, hdv, mul_one]; exact h11) ?_
      rw [Units.val_mul, hd, GeneralLinearGroup.val_det_apply]
      exact det_cong hj
    have t2 : ξ (Units.mk0 _ hs.det_ne) = ξ (u * Units.mk0 _ hy.det_ne) := by
      refine tame_eq hξ (by rw [Units.val_mul, map_mul, hu, Units.val_mk0, Units.val_mk0, hy.2.1, h11, mul_one]) ?_
      rw [Units.val_mul, Units.val_mk0, Units.val_mk0]
      exact hc
    rw [dif_pos hs, dif_pos hy, MonoidHom.inv_apply, MonoidHom.inv_apply, inv_inv, inv_inv, t1, t2, map_mul, map_mul]
    simp only [Units.val_mul]
    ring
  · have hs : ¬ InSupp (j.val * y) := fun hs => by
      have := (inSupp_mul_left hs (inv_mem hj)).1
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this
      exact hy this
    rw [dif_neg hs, dif_neg hy, mul_zero, mul_zero]

end GlobalTheory.DatumEigenLeft
end
end

section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.TorusLeft

theorem sum_indic {D' : Type} [Fintype D'] [DecidableEq D'] (s : Finset D') : ∑ i, indic s i = (s.card : ℤ) := by
  simp [indic]

theorem zpow_rpow_half (q : ℝ) (hq : 0 ≤ q) (n m : ℕ) :
    ((q ^ (-(n : ℤ)) : ℝ) ^ (-(m : ℝ) / 2)) = (Real.sqrt q) ^ (n * m) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq, ← Real.rpow_intCast, ← Real.rpow_mul hq]
  congr 1
  push_cast; ring

theorem omTwo_torusLeft : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ μS μT : kˣ →* ℂˣ), IsUnram (μS * ξ⁻¹) → ∀ (s : Finset D') (j : GL (A ⊕ D') k), j ∈ parahoric k A D' → ∀ (u : Matrix (A ⊕ D') (A ⊕ D) k → ℂ) (y : Matrix (A ⊕ D') (A ⊕ D) k), omTwo μS μT (1 : GL (A ⊕ D) k) (j * mtor ϖ (indic s)) u y = (μS ϖ : ℂ) ^ s.card * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (s.card * (Fintype.card A + Fintype.card D)) * (ξ (GeneralLinearGroup.det j) : ℂ) * u (((j * mtor ϖ (indic s))⁻¹ : GL (A ⊕ D') k).1 * y) := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ ξ μS μT hu s j hj u y
  have hKO : j ∈ KO k (A ⊕ D') := (mem_parahoric.1 hj).1
  have hnj : nabs k (GeneralLinearGroup.det j) = 1 := nabs_det_of_mem_KO hKO
  have hvj : valuation k ((GeneralLinearGroup.det j : kˣ) : k) = 1 := (nabs_eq_one_iff _).1 hnj
  have hξ : μS (GeneralLinearGroup.det j) = ξ (GeneralLinearGroup.det j) := by
    have := hu _ hvj
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one] at this
    exact this
  have hdm : GeneralLinearGroup.det (mtor ϖ (indic s) : GL (A ⊕ D') k) = ϖ ^ (s.card : ℤ) := by
    rw [GlobalTheory.ChainStepCoef.det_mtor, sum_indic]
  have hnm : nabs k (GeneralLinearGroup.det (mtor ϖ (indic s) : GL (A ⊕ D') k)) = (resCard k : ℝ) ^ (-(s.card : ℤ)) := by
    rw [GlobalTheory.ChainStepCoef.nabs_det_mtor hϖ, sum_indic]
  have hnh : nabs k (GeneralLinearGroup.det (j * mtor ϖ (indic s))) = (resCard k : ℝ) ^ (-(s.card : ℤ)) := by
    rw [map_mul, nabs_mul, hnj, hnm, one_mul]
  have hμh : μS (GeneralLinearGroup.det (j * mtor ϖ (indic s))) = ξ (GeneralLinearGroup.det j) * μS ϖ ^ s.card := by
    rw [map_mul, map_mul, hξ, hdm, zpow_natCast, map_pow]
  have hq : ((nabs k (GeneralLinearGroup.det (j * mtor ϖ (indic s))) ^ (-(Fintype.card (A ⊕ D) : ℝ) / 2) : ℝ) : ℂ)
      = ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (s.card * (Fintype.card A + Fintype.card D)) := by
    rw [hnh, ← Fintype.card_sum, zpow_rpow_half _ (Nat.cast_nonneg _)]
    push_cast; rfl
  have key : (((μS * μT⁻¹) (GeneralLinearGroup.det (j * mtor ϖ (indic s))) : ℂˣ) : ℂ) *
      (((μT⁻¹ (GeneralLinearGroup.det (j * mtor ϖ (indic s))))⁻¹ : ℂˣ) : ℂ) =
      (μS (GeneralLinearGroup.det (j * mtor ϖ (indic s))) : ℂ) := by
    rw [← Units.val_mul, MonoidHom.mul_apply, MonoidHom.inv_apply, inv_inv, inv_mul_cancel_right]
  simp only [omTwo, om, Pi.smul_apply, smul_eq_mul, map_one, Units.val_one, one_mul, nabs_one, Real.one_rpow, Complex.ofReal_one, mul_one, Matrix.mul_one]
  rw [hq, ← mul_assoc, ← mul_assoc, key, hμh, Units.val_mul, Units.val_pow_eq_pow_val]
  ring

end GlobalTheory.TorusLeft
end

section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section
namespace GlobalTheory.TorusRightScalar

theorem det_mtor' {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ) :
    GeneralLinearGroup.det (mtor ϖ e : GL (A ⊕ D) k) = ϖ ^ ∑ i, e i := by
  ext
  rw [GeneralLinearGroup.val_det_apply, mtor, val_torusElt, det_diagonal, Units.val_zpow_eq_zpow_val,
    Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul]
  induction (Finset.univ : Finset D) using Finset.induction_on with
  | empty => simp
  | insert i t hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ (Units.ne_zero ϖ), ih]

theorem sum_neg_indic {D : Type} [Fintype D] [DecidableEq D] (s : Finset D) :
    ∑ i, (-indic s) i = -(s.card : ℤ) := by
  simp [indic, Finset.sum_neg_distrib, Finset.sum_ite_mem]

theorem torusRight : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ μS μT : kˣ →* ℂˣ), IsUnram (μT * ξ⁻¹) → ∀ (s : Finset D) (j : GL (A ⊕ D) k), j ∈ parahoric k A D → ∀ (u : Matrix (A ⊕ D') (A ⊕ D) k → ℂ) (y : Matrix (A ⊕ D') (A ⊕ D) k), omTwo μS μT (j * mtor ϖ (-indic s)) (1 : GL (A ⊕ D') k) u y = (((ξ (GeneralLinearGroup.det j))⁻¹ : ℂˣ) : ℂ) * (μT ϖ : ℂ) ^ s.card * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (s.card * (Fintype.card A + Fintype.card D')) * u (y * (j * mtor ϖ (-indic s)).1) := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ ξ μS μT hun s j hj u y
  have hjK : j ∈ KO k (A ⊕ D) := (mem_parahoric.1 hj).1
  have hn1 : nabs k (GeneralLinearGroup.det j) = 1 := nabs_det_of_mem_KO hjK
  have hv1 : valuation k ((GeneralLinearGroup.det j : kˣ) : k) = 1 := (nabs_eq_one_iff _).1 hn1
  have hxi : μT (GeneralLinearGroup.det j) = ξ (GeneralLinearGroup.det j) := by
    have := hun _ hv1
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one] at this
    exact this
  have hdet : GeneralLinearGroup.det (j * mtor ϖ (-indic s)) =
      GeneralLinearGroup.det j * ϖ ^ (-(s.card : ℤ)) := by
    rw [map_mul, det_mtor', sum_neg_indic]
  have hq0 : (0 : ℝ) < resCard k := by
    have q1 : 1 < Nat.card 𝓀[k] := Finite.one_lt_card
    unfold resCard; exact_mod_cast (lt_trans one_pos q1)
  have hnabs : nabs k (GeneralLinearGroup.det (j * mtor ϖ (-indic s))) = (resCard k : ℝ) ^ s.card := by
    rw [map_mul, show nabs k (GeneralLinearGroup.det j * GeneralLinearGroup.det (mtor ϖ (-indic s) : GL (A ⊕ D) k)) =
      nabs k (GeneralLinearGroup.det j) * nabs k (GeneralLinearGroup.det (mtor ϖ (-indic s) : GL (A ⊕ D) k)) by
        simp [nabs, map_mul], hn1, one_mul, mtor, nabs_det_torusElt hϖ, Fintype.sum_sum_type]
    simp [indic, Finset.sum_ite_mem]
  have hpow : ((resCard k : ℝ) ^ s.card) ^ ((Fintype.card (A ⊕ D') : ℝ) / 2) =
      (Real.sqrt (resCard k)) ^ (s.card * (Fintype.card A + Fintype.card D')) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le,
      ← Real.rpow_mul hq0.le, Fintype.card_sum]
    congr 1
    push_cast
    ring
  simp only [omTwo, om, map_one, inv_one, Units.val_one, one_smul, Matrix.one_mul, hnabs, hpow]
  have h1 : nabs k 1 = 1 := by simp [nabs]
  rw [h1, Real.one_rpow, hdet, map_mul, map_zpow, MonoidHom.inv_apply, MonoidHom.inv_apply, hxi]
  push_cast
  simp only [_root_.zpow_neg, zpow_natCast]
  rw [inv_pow, inv_inv]
  ring

end GlobalTheory.TorusRightScalar
end
end

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section
namespace GlobalTheory.ParHeckeCard

section general
variable {G : Type} [Group G]

def dcos (J : Subgroup G) (g : G) : Set G := {x | ∃ a ∈ J, ∃ b ∈ J, x = a * g * b}

theorem dcos_eq_iUnion (J : Subgroup G) (g : G) (R : Finset G) (h1 : ∀ j ∈ R, j ∈ J)
    (h2 : ∀ j ∈ J, ∃! j', j' ∈ R ∧ (j' * g)⁻¹ * (j * g) ∈ J) :
    dcos J g = ⋃ j ∈ R, (fun x => (j * g)⁻¹ * x) ⁻¹' (J : Set G) := by
  ext x
  simp only [dcos, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨j', ⟨hj'R, hj'⟩, -⟩ := h2 a ha
    refine ⟨j', hj'R, ?_⟩
    have e : (j' * g)⁻¹ * (a * g * b) = ((j' * g)⁻¹ * (a * g)) * b := by group
    rw [e]; exact J.mul_mem hj' hb
  · rintro ⟨j, hjR, hj⟩
    exact ⟨j, h1 j hjR, (j * g)⁻¹ * x, hj, by group⟩

theorem pairwiseDisjoint_cosets (J : Subgroup G) (g : G) (R : Finset G) (h1 : ∀ j ∈ R, j ∈ J)
    (h2 : ∀ j ∈ J, ∃! j', j' ∈ R ∧ (j' * g)⁻¹ * (j * g) ∈ J) :
    (R : Set G).PairwiseDisjoint (fun j => (fun x => (j * g)⁻¹ * x) ⁻¹' (J : Set G)) := by
  intro j₁ hj₁ j₂ hj₂ hne
  refine Set.disjoint_left.2 fun x hx₁ hx₂ => hne ?_
  simp only [Set.mem_preimage, SetLike.mem_coe] at hx₁ hx₂
  have hm : (j₁ * g)⁻¹ * (j₂ * g) ∈ J := by
    have e : (j₁ * g)⁻¹ * (j₂ * g) = ((j₁ * g)⁻¹ * x) * ((j₂ * g)⁻¹ * x)⁻¹ := by group
    rw [e]; exact J.mul_mem hx₁ (J.inv_mem hx₂)
  have hself : (j₂ * g)⁻¹ * (j₂ * g) ∈ J := by simp
  exact (h2 j₂ (h1 j₂ (Finset.mem_coe.1 hj₂))).unique ⟨Finset.mem_coe.1 hj₁, hm⟩ ⟨Finset.mem_coe.1 hj₂, hself⟩

theorem dcos_inv (J : Subgroup G) (g : G) : dcos J g⁻¹ = Inv.inv ⁻¹' dcos J g := by
  ext x
  simp only [dcos, Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨b⁻¹, J.inv_mem hb, a⁻¹, J.inv_mem ha, by group⟩
  · rintro ⟨a, ha, b, hb, h⟩
    refine ⟨b⁻¹, J.inv_mem hb, a⁻¹, J.inv_mem ha, ?_⟩
    rw [← inv_inv x, h]; group

theorem measure_dcos [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (J : Subgroup G) (hJ : MeasurableSet (J : Set G)) (g : G) (R : Finset G) (h1 : ∀ j ∈ R, j ∈ J)
    (h2 : ∀ j ∈ J, ∃! j', j' ∈ R ∧ (j' * g)⁻¹ * (j * g) ∈ J) :
    μ (dcos J g) = R.card * μ J := by
  rw [dcos_eq_iUnion J g R h1 h2, measure_biUnion_finset (pairwiseDisjoint_cosets J g R h1 h2)
    (fun j _ => measurable_const_mul _ hJ)]
  simp only [measure_preimage_mul, Finset.sum_const, nsmul_eq_mul]

theorem card_eq_of_unimodular [MeasurableSpace G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (J : Subgroup G) (hJo : IsOpen (J : Set G)) (hJt : μ J ≠ ⊤) (g : G) (R R' : Finset G)
    (h1 : ∀ j ∈ R, j ∈ J) (h2 : ∀ j ∈ J, ∃! j', j' ∈ R ∧ (j' * g)⁻¹ * (j * g) ∈ J)
    (h1' : ∀ j ∈ R', j ∈ J) (h2' : ∀ j ∈ J, ∃! j', j' ∈ R' ∧ (j' * g⁻¹)⁻¹ * (j * g⁻¹) ∈ J) :
    R.card = R'.card := by
  haveI : μ.IsInvInvariant := GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant μ
  have h0 : μ J ≠ 0 := (hJo.measure_pos μ ⟨1, J.one_mem⟩).ne'
  have e1 := measure_dcos μ J hJo.measurableSet g R h1 h2
  have e2 := measure_dcos μ J hJo.measurableSet g⁻¹ R' h1' h2'
  rw [dcos_inv, Measure.measure_preimage_inv, e1] at e2
  have h := (ENNReal.mul_left_inj h0 hJt).1 e2
  exact_mod_cast h

end general

theorem card_isReps_inv (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (g : GL (A ⊕ D) k)
    (R R' : Finset (GL (A ⊕ D) k)) (d d' : GL (A ⊕ D) k → kˣ) :
    IsReps g R d → IsReps g⁻¹ R' d' → R.card = R'.card ∧ R.Nonempty := by
  intro hR hR'
  letI : MeasurableSpace (GL (A ⊕ D) k) := borel _
  haveI : BorelSpace (GL (A ⊕ D) k) := ⟨rfl⟩
  haveI : IsTopologicalGroup (GL (A ⊕ D) k) := inferInstance
  haveI : LocallyCompactSpace (GL (A ⊕ D) k) := inferInstance
  haveI : SecondCountableTopology (GL (A ⊕ D) k) := inferInstance
  obtain ⟨hJo, hJc⟩ := GlobalTheory.ParahoricOpenCompact.isOpen_isCompact_parahoric k A D

  have hRI : ∀ (μ : Measure (GL (A ⊕ D) k)) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
    intro μ _
    refine ⟨fun g => ?_⟩
    have h : Measure.modularCharacter g = 1 := by
      refine GlobalTheory.SplitFlip.hom_eq_one_of_center Measure.modularCharacter (fun z hz => ?_) g
      have h1 := Measure.map_right_mul_eq_modularCharacterFun_smul μ z
      rw [show (fun x => x * z) = fun x => z * x from funext fun x => (hz x).symm,
        Measure.IsMulLeftInvariant.map_mul_left_eq_self] at h1
      have h2 := congrArg (fun m : Measure (GL (A ⊕ D) k) => m (KO k (A ⊕ D))) h1
      have hne : μ (KO k (A ⊕ D)) ≠ 0 := (GlobalTheory.SplitFlip.isOpen_KO.measure_pos μ ⟨1, one_mem _⟩).ne'
      have hnt : μ (KO k (A ⊕ D)) ≠ ⊤ := GlobalTheory.SplitFlip.isCompact_KO.measure_lt_top.ne
      simp only [Measure.coe_nnreal_smul_apply] at h2
      have h3 : (Measure.modularCharacterFun z : ENNReal) = 1 :=
        (ENNReal.mul_left_inj hne hnt).1 (by rw [one_mul]; exact h2.symm)
      exact_mod_cast h3
    rw [Measure.map_right_mul_eq_modularCharacterFun_smul μ g, show Measure.modularCharacterFun g = 1 from h, one_smul]
  haveI := hRI (Measure.haar : Measure (GL (A ⊕ D) k))
  refine ⟨card_eq_of_unimodular (Measure.haar : Measure (GL (A ⊕ D) k)) (parahoric k A D) hJo
    hJc.measure_lt_top.ne g R R' (fun j hj => (hR.1 j hj).1) hR.2
    (fun j hj => (hR'.1 j hj).1) hR'.2, ?_⟩
  obtain ⟨j', ⟨hj', -⟩, -⟩ := hR.2 1 (one_mem _)
  exact ⟨j', hj'⟩

end GlobalTheory.ParHeckeCard
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_parahoricDoubleCosetReps_inv_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (g : GL (A ⊕ D) k) (R R' : Finset (GL (A ⊕ D) k)) (d d' : GL (A ⊕ D) k → kˣ), IsReps g R d → IsReps g⁻¹ R' d' → R.card = R'.card ∧ R.Nonempty := by
  atlas_forward_decl GlobalTheory.ParHeckeCard.card_isReps_inv
end

section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ParHeckeTransfer

theorem mtor_neg {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ) :
    (mtor ϖ (-e) : GL (A ⊕ D) k) = (mtor ϖ e)⁻¹ := by
  unfold mtor torusElt
  rw [← map_inv]
  congr 1
  funext i
  rcases i with i | i <;> simp [_root_.zpow_neg]

theorem sum_eq_genVal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ) (ξ μS μT : kˣ →* ℂˣ), IsTame ξ → IsUnram (μT * ξ⁻¹) → ∀ (W : Submodule ℂ (Matrix (A ⊕ D') (A ⊕ D) k → ℂ)) (hW : ∀ g h, ∀ u ∈ W, omTwo μS μT g h u ∈ W) (hΦ : datum ξ⁻¹ ∈ W) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GL (A ⊕ D) k) X) (x : X) (B : Multiset ℂˣ), IsGen ρ ξ ϖ B x → ∀ (X' : Type) [AddCommGroup X'] [Module ℂ X'] (ρ' : Representation ℂ (GL (A ⊕ D') k) X') (b : W →ₗ[ℂ] X →ₗ[ℂ] X'), (∀ g h (u : W) y, b ⟨omTwo μS μT g h u, hW g h u u.2⟩ (ρ g y) = ρ' h (b u y)) → ∀ (s : Finset D) (R : Finset (GL (A ⊕ D) k)) (d : GL (A ⊕ D) k → kˣ), IsReps (mtor ϖ (-indic s)) R d → ∑ j ∈ R, (ξ (d j) : ℂ) • b ⟨omTwo μS μT (j * mtor ϖ (-indic s)) 1 (datum ξ⁻¹), hW _ _ _ hΦ⟩ x = genVal (resCard k) (Fintype.card A) (Fintype.card D) B s.card • b ⟨datum ξ⁻¹, hΦ⟩ x := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ ξ μS μT hξ hμ W hW hΦ X _ _ ρ x B hx X' _ _ ρ' b hb s R d hR
  set g : GL (A ⊕ D) k := mtor ϖ (indic s) with hg
  have hginv : (mtor ϖ (-indic s) : GL (A ⊕ D) k) = g⁻¹ := mtor_neg ϖ (indic s)
  rw [hginv] at hR ⊢
  set Φ : W := ⟨datum ξ⁻¹, hΦ⟩ with hΦdef

  have h1 : ∀ j ∈ R, (ξ (d j) : ℂ) • b ⟨omTwo μS μT (j * g⁻¹) 1 (datum ξ⁻¹), hW _ _ _ hΦ⟩ x = b Φ (ρ g x) := by
    intro j hj
    obtain ⟨hjJ, hdj⟩ := hR.1 j hj
    have hjiJ : j⁻¹ ∈ parahoric k A D := inv_mem hjJ
    have hne := (GlobalTheory.T.twoBlockParahoric_lowerBlock_det_tameCharacter k A D ξ hξ j⁻¹ hjiJ).1
    have hprod := (GlobalTheory.T.twoBlockParahoric_lowerBlock_det_tameCharacter k A D ξ hξ j hjJ).2 (d j) (Units.mk0 _ hne) hdj rfl
    have hx1 : ρ j⁻¹ x = (ξ (Units.mk0 _ hne) : ℂ) • x := hx.1 j⁻¹ hjiJ (Units.mk0 _ hne) rfl
    have he := hb (j * g⁻¹) 1 Φ (ρ (g * j⁻¹) x)
    have hone : (j * g⁻¹) * (g * j⁻¹) = 1 := by group
    rw [← Module.End.mul_apply, ← map_mul, hone, map_one, Module.End.one_apply, map_one, Module.End.one_apply,
      map_mul, Module.End.mul_apply, hx1, map_smul, map_smul] at he
    rw [show (⟨omTwo μS μT (j * g⁻¹) 1 (datum ξ⁻¹), hW _ _ _ hΦ⟩ : W) = ⟨omTwo μS μT (j * g⁻¹) 1 Φ, hW _ _ Φ Φ.2⟩ from rfl,
      he, smul_smul, hprod, one_smul]

  have htame : IsTame ξ⁻¹ := fun y hy => by simp [hξ y hy]
  have hunr : IsUnram (μT⁻¹ * ξ) := fun y hy => by
    have := hμ y hy
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply] at this ⊢
    rw [← inv_inv (ξ y), ← mul_inv, this, inv_one]
  have h2 : ∀ j ∈ parahoric k A D, ∀ dd : kˣ, (dd : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det →
      ∀ z, b Φ (ρ j z) = (ξ dd : ℂ) • b Φ z := by
    intro j hj dd hdd z
    have hom : omTwo μS μT j (1 : GL (A ⊕ D') k) (datum ξ⁻¹) = ((ξ⁻¹ dd : ℂˣ) : ℂ) • datum ξ⁻¹ := by
      have := GlobalTheory.T.parahoricDatum_eigenvector_twoBlockParahoric k A D D' ξ⁻¹ (μT⁻¹ * ξ) htame hunr j hj dd hdd
      rw [show μT⁻¹ * ξ * ξ⁻¹ = μT⁻¹ by rw [mul_assoc, mul_inv_cancel, mul_one]] at this
      unfold omTwo
      rw [this]
      funext y
      simp
    have he := hb j 1 Φ z
    have hsub : (⟨omTwo μS μT j 1 Φ, hW j 1 Φ Φ.2⟩ : W) = ((ξ⁻¹ dd : ℂˣ) : ℂ) • Φ := Subtype.ext hom
    rw [hsub, map_smul, LinearMap.smul_apply, map_one, Module.End.one_apply] at he
    rw [← he, smul_smul]
    simp

  obtain ⟨R'', d'', hR''⟩ := (GlobalTheory.T.exists_parahoric_and_integralGL_doubleCosetReps k A D).1 g
  have hcard := (GlobalTheory.T.card_parahoricDoubleCosetReps_inv_eq k A D g R'' R d'' d hR'' hR).1
  have hT := hx.2.2 s R'' d'' hR''
  have hsum2 : genVal (resCard k) (Fintype.card A) (Fintype.card D) B s.card • b Φ x = R''.card • b Φ (ρ g x) := by
    rw [← map_smul, hT, map_sum, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨hjJ, hdj⟩ := hR''.1 j hj
    rw [map_smul, show (mtor ϖ (indic s) : GL (A ⊕ D) k) = g from rfl, map_mul, Module.End.mul_apply,
      h2 j hjJ (d'' j) hdj, smul_smul]
    simp
  rw [Finset.sum_congr rfl h1, Finset.sum_const, hsum2, hcard]

end GlobalTheory.ParHeckeTransfer
end
end

section
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ParHeckeTransfer

theorem transfer : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ t : ℕ, Fintype.card D' = Fintype.card D + t → ∀ (ξ μS μT : kˣ →* ℂˣ), IsTame ξ → IsUnram (μS * ξ⁻¹) → IsUnram (μT * ξ⁻¹) → ∀ (W : Submodule ℂ (Matrix (A ⊕ D') (A ⊕ D) k → ℂ)) (hW : ∀ g h, ∀ u ∈ W, omTwo μS μT g h u ∈ W) (hΦ : datum ξ⁻¹ ∈ W) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GL (A ⊕ D) k) X) (x : X) (B : Multiset ℂˣ), IsGen ρ ξ ϖ B x → ∀ (X' : Type) [AddCommGroup X'] [Module ℂ X'] (ρ' : Representation ℂ (GL (A ⊕ D') k) X') (b : W →ₗ[ℂ] X →ₗ[ℂ] X'), (∀ g h (u : W) y, b ⟨omTwo μS μT g h u, hW g h u u.2⟩ (ρ g y) = ρ' h (b u y)) → IsGen ρ' ξ ϖ (B.map (· * (μS ϖ * (μT ϖ)⁻¹)) + segL ϖ (μS ϖ) t) (b ⟨datum ξ⁻¹, hΦ⟩ x) := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ t hD' ξ μS μT hξ hS hT W hW hΦ X _ _ ρ x B hx X' _ _ ρ' b hb
  have hξi : IsTame ξ⁻¹ := fun y hy => by rw [MonoidHom.inv_apply, hξ y hy, inv_one]
  have hρ1 : ∀ y : X, ρ 1 y = y := fun y => by rw [map_one, Module.End.one_apply]
  obtain ⟨hx1, hx2, hx3⟩ := hx
  refine ⟨?_, ?_, fun s => ?_⟩
  · intro j hj d hd
    have h1 := hb 1 j ⟨datum ξ⁻¹, hΦ⟩ x
    rw [hρ1] at h1
    rw [← h1]
    have e : (⟨omTwo μS μT 1 j (datum ξ⁻¹), hW 1 j _ hΦ⟩ : W) = (ξ d : ℂ) • (⟨datum ξ⁻¹, hΦ⟩ : W) :=
      Subtype.ext (GlobalTheory.DatumEigenLeft.omTwo_datum_inv k A D D' ξ μS μT hξ hS j hj d hd)
    rw [e, map_smul, LinearMap.smul_apply]
  · simp [segL, hx2, hD']

  · intro R' d' hR'
    obtain ⟨hr1, hr2⟩ := GlobalTheory.ParHeckeReps.exists_reps_both k A D
    obtain ⟨-, hr2'⟩ := GlobalTheory.ParHeckeReps.exists_reps_both k A D'
    choose RR dd hRR using hr1
    choose RK hRK using hr2
    obtain ⟨RK', hRK'⟩ := hr2' (torusElt k D' ϖ (indic s))
    have hsn : ∀ n : ℕ, ∃ s : Finset D, n ≤ Fintype.card D → s.card = n := fun n => by
      by_cases h : n ≤ Fintype.card D
      · obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset D)) (by simpa using h)
        exact ⟨s, fun _ => hs⟩
      · exact ⟨∅, fun h' => absurd h' h⟩
    choose sn hsn using hsn
    have hq : (0 : ℝ) < (resCard k : ℝ) := by
      have : 0 < Nat.card 𝓀[k] := Nat.card_pos
      unfold resCard; exact_mod_cast this
    have hsq : ((Real.sqrt (resCard k) : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.2 hq).ne'
    set Φw : W := ⟨datum ξ⁻¹, hΦ⟩ with hΦw
    set C : ℂ := (μS ϖ : ℂ) ^ s.card * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (s.card * (Fintype.card A + Fintype.card D)) with hC
    set cn : ℕ → ℂ := fun n => if n ≤ s.card then ((resCard k ^ (n * (t - (s.card - n))) * Formalism.L2.Col.gaussBin (resCard k) t (s.card - n) : ℕ) : ℂ) else 0 with hcn
    set den : ℕ → ℂ := fun n => (μT ϖ : ℂ) ^ n * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (n * (Fintype.card A + Fintype.card D')) with hden
    have hden0 : ∀ n, den n ≠ 0 := fun n => mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) (pow_ne_zero _ hsq)
    have key : ∑ j ∈ R', (((ξ (d' j))⁻¹ : ℂˣ) : ℂ) • (⟨omTwo μS μT 1 (j * mtor ϖ (indic s)) (datum ξ⁻¹), hW _ _ _ hΦ⟩ : W) =
        C • ∑ n ∈ Finset.range (Fintype.card D + 1), (cn n * (den n)⁻¹) •
            ∑ j ∈ RR (mtor ϖ (-indic (sn n))), (ξ (dd (mtor ϖ (-indic (sn n))) j) : ℂ) •
              (⟨omTwo μS μT (j * mtor ϖ (-indic (sn n))) 1 (datum ξ⁻¹), hW _ _ _ hΦ⟩ : W) := by
      apply Subtype.ext
      funext y
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hT1 := GlobalTheory.ParHeckeTarget.sum_reps_datum_eq k A D D' ϖ hϖ ξ⁻¹ hξi s R' d' hR' RK' hRK' y
      have hU := GlobalTheory.ParHecke.heckeIdentity_integral k D D' ϖ hϖ t hD' s RK' hRK' sn (fun n => RK (torusElt k D ϖ (-indic (sn n))))
        (fun n hn => ⟨hsn n hn, hRK _⟩) (schur y)
      have hL : ∑ j ∈ R', (((ξ (d' j))⁻¹ : ℂˣ) : ℂ) * omTwo μS μT 1 (j * mtor ϖ (indic s)) (datum ξ⁻¹) y =
          C * (datum ξ⁻¹ y * ∑ g ∈ RK', intInd (((g⁻¹ : GL D' k)).1 * schur y)) := by
        have e2 : datum ξ⁻¹ y * ∑ g ∈ RK', intInd (((g⁻¹ : GL D' k)).1 * schur y) =
            ∑ g ∈ RK', liftS ξ⁻¹ (fun z => intInd ((g⁻¹).1 * z)) y := by
          rw [Finset.mul_sum]; rfl
        rw [e2, ← hT1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [GlobalTheory.TorusLeft.omTwo_torusLeft k A D D' ϖ hϖ ξ μS μT hS s j (hR'.1 j hj).1]
        simp only [MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, hC]
        field_simp
      have hR : ∀ n ∈ Finset.range (Fintype.card D + 1),
          (cn n * (den n)⁻¹) * ∑ j ∈ RR (mtor ϖ (-indic (sn n))), (ξ (dd (mtor ϖ (-indic (sn n))) j) : ℂ) *
              omTwo μS μT (j * mtor ϖ (-indic (sn n))) 1 (datum ξ⁻¹) y =
            cn n * (datum ξ⁻¹ y * ∑ g ∈ RK (torusElt k D ϖ (-indic (sn n))), intInd (schur y * g.1)) := by
        intro n hn
        have hc := hsn n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))
        have e2 : datum ξ⁻¹ y * ∑ g ∈ RK (torusElt k D ϖ (-indic (sn n))), intInd (schur y * g.1) =
            ∑ g ∈ RK (torusElt k D ϖ (-indic (sn n))), liftS ξ⁻¹ (fun z => intInd (z * g.1)) y := by
          rw [Finset.mul_sum]; rfl
        rw [e2, ← GlobalTheory.ParHeckeSource.sum_reps_datum_eq k A D D' ϖ hϖ ξ⁻¹ hξi (sn n) _ _ (hRR _) _ (hRK _) y, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [GlobalTheory.TorusRightScalar.torusRight k A D D' ϖ hϖ ξ μS μT hT (sn n) j ((hRR _).1 j hj).1, hc]
        have := hden0 n
        simp only [MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, hden] at this ⊢
        field_simp
      rw [hL, hU, Finset.sum_congr rfl hR]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    have lhs : ∑ j ∈ R', (((ξ (d' j))⁻¹ : ℂˣ) : ℂ) • ρ' (j * mtor ϖ (indic s)) (b Φw x) =
        b (∑ j ∈ R', (((ξ (d' j))⁻¹ : ℂˣ) : ℂ) • (⟨omTwo μS μT 1 (j * mtor ϖ (indic s)) (datum ξ⁻¹), hW _ _ _ hΦ⟩ : W)) x := by
      rw [map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, LinearMap.smul_apply, ← hb 1 _ Φw x, hρ1]
    have e4 : ∀ n ∈ Finset.range (Fintype.card D + 1),
        b ((cn n * (den n)⁻¹) • ∑ j ∈ RR (mtor ϖ (-indic (sn n))), (ξ (dd (mtor ϖ (-indic (sn n))) j) : ℂ) •
              (⟨omTwo μS μT (j * mtor ϖ (-indic (sn n))) 1 (datum ξ⁻¹), hW _ _ _ hΦ⟩ : W)) x =
          (cn n * (den n)⁻¹ * genVal (resCard k) (Fintype.card A) (Fintype.card D) B n) • b Φw x := by
      intro n hn
      have hc := hsn n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))
      rw [map_smul, LinearMap.smul_apply, map_sum, LinearMap.sum_apply]
      simp_rw [map_smul, LinearMap.smul_apply]
      rw [GlobalTheory.ParHeckeTransfer.sum_eq_genVal k A D D' ϖ ξ μS μT hξ hT W hW hΦ X ρ x B ⟨hx1, hx2, hx3⟩ X' ρ' b hb (sn n) _ _ (hRR _), hc, smul_smul]
    rw [lhs, key, map_smul, LinearMap.smul_apply, map_sum, LinearMap.sum_apply, Finset.sum_congr rfl e4,
      ← Finset.sum_smul, smul_smul]
    congr 1
    have hN := GlobalTheory.ParHecke.StringEig.genVal_add_segL k ϖ hϖ (Fintype.card A) (Fintype.card D) t s.card B (μS ϖ) (μT ϖ) hx2
      (by rw [← hD']; exact Finset.card_le_univ s)
    rw [show Fintype.card D' = Fintype.card D + t from hD']
    rw [hN, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hC, hcn, hden, hD']
    ring

end GlobalTheory.ParHeckeTransfer
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerBlockParameter_transfer_invariantPairing : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ t : ℕ, Fintype.card D' = Fintype.card D + t → ∀ (ξ μS μT : kˣ →* ℂˣ), IsTame ξ → IsUnram (μS * ξ⁻¹) → IsUnram (μT * ξ⁻¹) → ∀ (W : Submodule ℂ (Matrix (A ⊕ D') (A ⊕ D) k → ℂ)) (hW : ∀ g h, ∀ u ∈ W, omTwo μS μT g h u ∈ W) (hΦ : datum ξ⁻¹ ∈ W) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GL (A ⊕ D) k) X) (x : X) (B : Multiset ℂˣ), IsGen ρ ξ ϖ B x → ∀ (X' : Type) [AddCommGroup X'] [Module ℂ X'] (ρ' : Representation ℂ (GL (A ⊕ D') k) X') (b : W →ₗ[ℂ] X →ₗ[ℂ] X'), (∀ g h (u : W) y, b ⟨omTwo μS μT g h u, hW g h u u.2⟩ (ρ g y) = ρ' h (b u y)) → IsGen ρ' ξ ϖ (B.map (· * (μS ϖ * (μT ϖ)⁻¹)) + segL ϖ (μS ϖ) t) (b ⟨datum ξ⁻¹, hΦ⟩ x) := by
  atlas_forward_decl GlobalTheory.ParHeckeTransfer.transfer
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.ChainTw.linModel_theta : ∀ D : D7, ForStepQ D fun c w k s s' p => ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι ι', IsChart s k φ ι → IsChart s' (k + 1) φ ι' → ∀ μS μT ξl : (Fv D.host.F v)ˣ →* ℂˣ, (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μS y = Circle.toUnits (c.chS (k + 1) x)) → (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μT y = Circle.toUnits (c.chT (k + 1) x)) → LiftsChar φ PP ξl (w.ξ PP) → ∀ P, ∃ (W : Submodule ℂ (Matrix (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → ℂ)) (hW : ∀ g h, ∀ u ∈ W, GlobalTheory.ParHecke.omTwo μS μT g h u ∈ W) (hΦ : datum ξl⁻¹ ∈ W) (T : W →ₗ[ℂ] (WO s.V s'.V → ℂ)), T ⟨_, hΦ⟩ = p.pt P ∧ (∀ u, IsThetaFunO c.ψ s.V s'.V (T u)) ∧ ∀ g h (u : W), p.ω (ι g, ι' h) (T u) = T ⟨_, hW g h u u.2⟩ := by
  intro D hG c w hw k hk s s' hs hs' p hp PP hPP v φ hφ ι ι' hι hι' μS μT ξl hS hT hξ P
  obtain ⟨m, X, hX⟩ := GlobalTheory.Size.exists_isCovolOne s.V s'.V
  obtain ⟨hW, hΦ, T, h1, h2, h3, h4⟩ :=
    GlobalTheory.T.linearModel_splitPlace_twist_schwartzBruhat D hG c w hw k hk s s' hs hs' p hp PP hPP v φ hφ ι ι' hι hι' μS μT ξl hS hT hξ P m X hX
  exact ⟨_, hW, hΦ, T, h1, h2, h3⟩
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearModel_twistPlace_in_thetaFunctions : ∀ D : D7, ForStepQ D fun c w k s s' p => ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι ι', IsChart s k φ ι → IsChart s' (k + 1) φ ι' → ∀ μS μT ξl : (Fv D.host.F v)ˣ →* ℂˣ, (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μS y = Circle.toUnits (c.chS (k + 1) x)) → (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μT y = Circle.toUnits (c.chT (k + 1) x)) → LiftsChar φ PP ξl (w.ξ PP) → ∀ P, ∃ (W : Submodule ℂ (Matrix (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → ℂ)) (hW : ∀ g h, ∀ u ∈ W, GlobalTheory.ParHecke.omTwo μS μT g h u ∈ W) (hΦ : datum ξl⁻¹ ∈ W) (T : W →ₗ[ℂ] (WO s.V s'.V → ℂ)), T ⟨_, hΦ⟩ = p.pt P ∧ (∀ u, IsThetaFunO c.ψ s.V s'.V (T u)) ∧ ∀ g h (u : W), p.ω (ι g, ι' h) (T u) = T ⟨_, hW g h u u.2⟩ := by
  atlas_forward_decl GlobalTheory.ChainTw.linModel_theta
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.ChainTw.UpQProof

theorem isGen_of_injective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A B₀ : Type} [Fintype A] [DecidableEq A] [Fintype B₀] [DecidableEq B₀]
    {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (GL (A ⊕ B₀) k) X} {ρ' : Representation ℂ (GL (A ⊕ B₀) k) Y} (f : X →ₗ[ℂ] Y)
    (hf : ∀ g y, f (ρ g y) = ρ' g (f y)) (hi : Function.Injective f) {ξ : kˣ →* ℂˣ} {ϖ : kˣ} {B : Multiset ℂˣ} {x : X}
    (h : GlobalTheory.ParHecke.IsGen ρ' ξ ϖ B (f x)) : GlobalTheory.ParHecke.IsGen ρ ξ ϖ B x := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, h2, fun s R d hR => hi ?_⟩
  · intro g hg d hd
    apply hi
    rw [hf, h1 g hg d hd, map_smul]
  · rw [map_smul, map_sum, h3 s R d hR]
    simp only [map_smul, hf]

open ValuativeRel in

theorem seg_eq_segL {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) (PP : Pl D.host.E) (hP : IsProjAt φ PP)
    {ϖ : (Fv D.host.F v)ˣ} (hϖ : valuation (Fv D.host.F v) (ϖ : Fv D.host.F v) = uniformizer (Fv D.host.F v))
    (z : ℂˣ) (t : ℕ) : GlobalTheory.LFun.seg PP z t = GlobalTheory.ParHecke.segL ϖ z t := by
  have hq := (GlobalTheory.PlaceProjAt.under_resCard D v φ PP hP).2
  have hn := GlobalTheory.GLDoubling.nabs_unif hϖ
  unfold GlobalTheory.LFun.seg GlobalTheory.ParHecke.segL
  rw [Finset.range_val]
  refine Multiset.map_congr rfl fun n _ => ?_
  ext
  simp only [Units.val_mul, GlobalTheory.SmGL.val_absPow, hn, hq, GlobalTheory.LFun.npowU, Units.val_mk0, GlobalTheory.LFun.npow]
  congr 1
  rw [Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm), ← Complex.cpow_neg]
  congr 1
  ring

theorem isUnram_of_lifts {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) (PP : Pl D.host.E) (hP : IsProjAt φ PP)
    (a : (kP PP)ˣ →* ℂˣ) (μ μ' : (Fv D.host.F v)ˣ →* ℂˣ) (h : LiftsChar φ PP μ a) (h' : LiftsChar φ PP μ' a) :
    GlobalTheory.SplitWeil.IsUnram (μ * μ'⁻¹) := by
  intro y hy
  have hy1 : Valued.v (y : Fv D.host.F v) = 1 := (GlobalTheory.TameLiftChar.val_eq_one_iff _).1 hy
  obtain ⟨a0, ha0⟩ := ReciprocityTheory.Aut.adic_exists_approx v (y : Fv D.host.F v) hy1.le
  let x0 : 𝓞 D.host.E := algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a0
  have hx0 : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E) = algebraMap (𝓞 D.host.F) (Fv D.host.F v) a0 := by
    have h1 : ((x0 : 𝓞 D.host.E) : D.host.E) = algebraMap D.host.F D.host.E (algebraMap (𝓞 D.host.F) D.host.F a0) := by
      show algebraMap (𝓞 D.host.E) D.host.E _ = _
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    rw [h1, GlobalTheory.PlaceRed.rdQ_alg]
    rfl
  have hr1 : Valued.v ((y : Fv D.host.F v) - GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E)) < 1 := by rw [hx0]; exact ha0
  have hnot : x0 ∉ PP.asIdeal := by
    intro hm
    have h2 := (hP x0).1 hm
    have : Valued.v (y : Fv D.host.F v) < 1 := by
      have := Valuation.map_add_lt Valued.v hr1 h2
      simpa using this
    rw [hy1] at this
    exact lt_irrefl _ this
  have hne : (Ideal.Quotient.mk PP.asIdeal x0 : kP PP) ≠ 0 := fun h0 => hnot (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  let κ : (kP PP)ˣ := Units.mk0 _ hne
  have hR : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.RedRel φ PP (y : Fv D.host.F v) (κ : kP PP) := ⟨x0, rfl, hr1⟩
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h y κ hR, h' y κ hR, mul_inv_cancel]

end GlobalTheory.ChainTw.UpQProof

open GlobalTheory.ChainTw.UpQProof in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.ChainTw.upQ_holds : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, UpQ D := by
  classical
  intro hP D hN c w hw k hk s s' hs hs' p hp u φ hu v₀ _
  intro PP hPP v φv hφv x ϖ hx ξl hξl ι' hι'
  obtain ⟨-, hch⟩ := GlobalTheory.TwistChart.charts_at_twist D c w hw k hk.le s hs PP hPP
  obtain ⟨-, -, ⟨ι, hι⟩, hμ⟩ := hch v φv hφv
  obtain ⟨μS, -, hμS⟩ := hμ (c.chS (k + 1))
  obtain ⟨μT, -, hμT⟩ := hμ (c.chT (k + 1))
  obtain ⟨W, hW, hΦ, T, hT0, hTθ, hTω⟩ :=
    GlobalTheory.T.linearModel_twistPlace_in_thetaFunctions D hN c w hw k hk s s' hs hs' p hp PP hPP v φv hφv ι ι' hι hι' μS μT ξl hμS hμT hξl φ
  have hsrc := hu v₀ PP hPP v φv hφv x ϖ hx ξl hξl ι hι
  obtain ⟨e, he, hx1, hx2, hϖ⟩ := hx
  have hSϖ : μS ϖ = Circle.toUnits (c.chS (k + 1) x) := hμS x ϖ ⟨e, he, hx1, hx2⟩
  have hTϖ : μT ϖ = Circle.toUnits (c.chT (k + 1) x) := hμT x ϖ ⟨e, he, hx1, hx2⟩
  have htame := (GlobalTheory.tameLift_isTame_not_isUnram D v φv PP (w.ξ PP) hφv (hw.ne PP hPP) ξl hξl).1
  obtain ⟨hres, -, -⟩ := GlobalTheory.ChainOnto.levRes_step D c hw.com k hk
  have hQ := hres PP (hw.union ▸ Finset.mem_union_right _ hPP)
  rw [hw.chiQ (k + 1) PP hPP, inv_inv] at hQ
  have hunS : GlobalTheory.SplitWeil.IsUnram (μS * ξl⁻¹) :=
    isUnram_of_lifts φv PP hφv (w.ξ PP) μS ξl (GlobalTheory.T.liftsChar_of_residueChar_at_splitPlace D _ PP _ hQ.1 v φv hφv μS hμS) hξl
  have hunT : GlobalTheory.SplitWeil.IsUnram (μT * ξl⁻¹) :=
    isUnram_of_lifts φv PP hφv (w.ξ PP) μT ξl (GlobalTheory.T.liftsChar_of_residueChar_at_splitPlace D _ PP _ hQ.2 v φv hφv μT hμT) hξl
  have hcard : Fintype.card (Blocks (k + 1) D.R.t) = Fintype.card (Blocks k D.R.t) + D.R.t := by
    simp [Blocks, Fintype.card_sigma]
    ring
  obtain ⟨hr, -, hfl⟩ := hs
  have hHaar : s.ν.IsHaarMeasure := hfl.haar
  have hFund : IsFundamentalDomain (GQ s.V) s.fd s.ν := hfl.fund
  have hθ : IsInfFam c.θ := hw.com.inf
  set F : GA D s.V → ℂ := PiLocalization₂.val u v₀ with hF
  have hFa := PiLocalization₂.val_autCusp c s u v₀
  let ρ0 : Representation ℂ (GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v)) (GA D s.V → ℂ) :=
    (GlobalTheory.PRep.rightReg ℂ (GA D s.V) ℂ).comp ι
  let cy : GA D s.V → ℂ := fun g => conj (F g)
  let X : Submodule ℂ (GA D s.V → ℂ) := Submodule.span ℂ (Set.range fun a => ρ0 a cy)
  have hX : ∀ a, ∀ z ∈ X, ρ0 a z ∈ X := by
    intro a z hz
    have hle : Submodule.map (ρ0 a) X ≤ X := by
      rw [Submodule.map_span_le]
      rintro _ ⟨b, rfl⟩
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨a * b, rfl⟩
    exact hle ⟨z, hz, rfl⟩
  let ρ : Representation ℂ (GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v)) X := GlobalTheory.PRep.sub ρ0 X hX
  have hcy : cy ∈ X := Submodule.subset_span ⟨1, by simp⟩
  have hXp : ∀ z ∈ X, (∀ u', IsThetaFunO c.ψ s.V s'.V u' → ∀ y, IntegrableOn (fun g => thetaKO p.ω g y u' * z g) s.fd s.ν) ∧
      (∀ γ ∈ GQ s.V, ∀ g, z (γ * g) = z g) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, rfl⟩ := hz
      refine ⟨fun u' hu' y => GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_mul_conj_integrableOn hP D c.ψ s.V s'.V (c.chS (k + 1))
        (c.chT (k + 1)) p.ω hp.weil c.θ hθ s.ν s.fd hHaar hFund u' F hu' hFa.1 hFa.2 (ι a) y, fun γ hγ g => ?_⟩
      show conj (F (γ * g * ι a)) = conj (F (g * ι a))
      rw [mul_assoc]
      exact congrArg conj (hFa.1.left γ hγ _)
    | zero => exact ⟨fun u' _ y => by simp, fun _ _ _ => rfl⟩
    | add z z' _ _ h1 h2 =>
      refine ⟨fun u' hu' y => ?_, fun γ hγ g => by simp [h1.2 γ hγ, h2.2 γ hγ]⟩
      rw [show (fun g => thetaKO p.ω g y u' * (z + z') g) = fun g => thetaKO p.ω g y u' * z g + thetaKO p.ω g y u' * z' g from
        funext fun g => by simp [mul_add]]
      exact (h1.1 u' hu' y).add (h2.1 u' hu' y)
    | smul a z _ h1 =>
      refine ⟨fun u' hu' y => ?_, fun γ hγ g => by simp [h1.2 γ hγ]⟩
      rw [show (fun g => thetaKO p.ω g y u' * (a • z) g) = fun g => a * (thetaKO p.ω g y u' * z g) from
        funext fun g => by simp [mul_left_comm]]
      exact (h1.1 u' hu' y).const_mul a
  let bf : W → X → GA D s'.V → ℂ := fun u' z y => ∫ g in s.fd, thetaKO p.ω g y (T u') * (z : GA D s.V → ℂ) g ∂s.ν
  let b : W →ₗ[ℂ] X →ₗ[ℂ] (GA D s'.V → ℂ) := LinearMap.mk₂ ℂ bf
    (fun u₁ u₂ z => by
      funext y
      show _ = bf u₁ z y + bf u₂ z y
      simp only [bf, ← integral_add ((hXp z z.2).1 _ (hTθ u₁) y) ((hXp z z.2).1 _ (hTθ u₂) y)]
      congr 1; funext g
      simp [thetaKO, add_mul])
    (fun a u₁ z => by
      funext y
      show _ = a * bf u₁ z y
      simp only [bf, ← integral_const_mul]
      congr 1; funext g
      simp [thetaKO, mul_assoc])
    (fun u₁ z z' => by
      funext y
      show _ = bf u₁ z y + bf u₁ z' y
      simp only [bf, ← integral_add ((hXp z z.2).1 _ (hTθ u₁) y) ((hXp z' z'.2).1 _ (hTθ u₁) y)]
      congr 1; funext g
      simp [mul_add])
    (fun a u₁ z => by
      funext y
      show _ = a * bf u₁ z y
      simp only [bf, ← integral_const_mul]
      congr 1; funext g
      simp [mul_left_comm])
  have hb : ∀ g h (u₁ : W) (z : X), b ⟨GlobalTheory.ParHecke.omTwo μS μT g h u₁, hW g h u₁ u₁.2⟩ (ρ g z) =
      (GlobalTheory.PRep.rightReg ℂ (GA D s'.V) ℂ).comp ι' h (b u₁ z) := by
    intro a a' u₁ z
    funext y
    show ∫ g in s.fd, thetaKO p.ω g y (T ⟨GlobalTheory.ParHecke.omTwo μS μT a a' u₁, hW a a' u₁ u₁.2⟩) * (z : GA D s.V → ℂ) (g * ι a) ∂s.ν =
      ∫ g in s.fd, thetaKO p.ω g (y * ι' a') (T u₁) * (z : GA D s.V → ℂ) g ∂s.ν
    rw [← hTω a a' u₁]
    simp_rw [thetaKO_om_apply]
    exact GlobalTheory.ChainOnto.setIntegral_fd_mul_right D s.V s.ν s.fd hHaar hFund
      (fun g => thetaKO p.ω g (y * ι' a') (T u₁) * (z : GA D s.V → ℂ) g)
      (fun γ hγ g => by simp only [thetaKO_left hp.weil (hTθ u₁) γ hγ, (hXp z z.2).2 γ hγ]) (ι a)
  have hx0 : GlobalTheory.ParHecke.IsGen ρ ξl ϖ (qPar c PP x k) ⟨cy, hcy⟩ :=
    isGen_of_injective X.subtype (fun _ _ => rfl) Subtype.val_injective hsrc
  have key := GlobalTheory.T.lowerBlockParameter_transfer_invariantPairing (Fv D.host.F v) (Fin D.R.r) (Blocks k D.R.t) (Blocks (k + 1) D.R.t) ϖ hϖ D.R.t hcard ξl μS μT
    htame hunS hunT W hW hΦ X ρ ⟨cy, hcy⟩ (qPar c PP x k) hx0 (GA D s'.V → ℂ) ((GlobalTheory.PRep.rightReg ℂ (GA D s'.V) ℂ).comp ι') b hb
  have hval : b ⟨GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.datum ξl⁻¹, hΦ⟩ ⟨cy, hcy⟩ = fun y => conj (p.up φ F y) := by
    funext y
    show ∫ g in s.fd, thetaKO p.ω g y (T ⟨GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.datum ξl⁻¹, hΦ⟩) * conj (F g) ∂s.ν =
      conj (∫ g in s.fd, conj (thetaKO p.ω g y (p.pt φ)) * F g ∂s.ν)
    rw [hT0, ← integral_conj]
    congr 1; funext g; simp
  rw [hval, hSϖ, hTϖ, ← seg_eq_segL φv PP hφv hϖ] at key
  exact key

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainThetaLiftUpLowerBlockParameter_proof : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, UpQ D := by
  atlas_forward_decl GlobalTheory.ChainTw.upQ_holds
end
