import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cut_BPEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqNF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqShift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormaliserAcrossPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemLevelZeroOfMemGroup
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimET
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PosAtOfCptCoefOfThmPActualCpt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LimitOfModuleForms
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaFinsetSumSmulOfXiExists
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WaveIsometryOfRadial
import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.HerGenC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimE
import Development.AbelianVarietyTheory.Definitions.Jets.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HsInnerSelfEqNormSq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliWordProductDecayBoundUniform
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AestronglyMeasurableTopVectorSmoothCoefficientStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaIntegrandIntegrableOfXiExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_PtwCut
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingEqIntegralInnerTopVectors
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopVectorCutoffEqAndVanish
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroEnergyBoundDecayingCasimirEigenfunction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeSumOfCompactCoefficientPositivity

section
namespace GlobalTheory.JetConstSq

theorem main : ∀ C₃ CΛ C₀ C₂ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 0 ≤ C₀ → 0 < C₂ → ∃ C₄ : ℝ, ∀ (b Λ : ℝ) (r n₀ p₀ : ℕ), 3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * r + 2 : ℕ) : ℝ)) → n₀ ≤ 30 * (r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((r : ℝ) + 1) ^ 2 → 2 * (3 * b) ^ (2 * n₀) * (1 * (C₂ * Λ ^ 2) ^ (r + 1)) * b ^ (2 * C₃ * ((2 * r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ)) ≤ b ^ (C₄ * ((2 * r + 2 : ℕ) : ℝ) ^ 4) := by
  intro C₃ CΛ C₀ C₂ h3 hΛ h0 h2
  refine ⟨40 + CΛ + C₂ + 2 * C₃ * (C₀ + 9), ?_⟩
  intro b Λ r n₀ p₀ hb hΛ1 hΛb hn hp
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  have hnR : (n₀ : ℝ) ≤ 30 * ((r : ℝ) + 1) ^ 2 + 6 := by exact_mod_cast hn
  have hm : ((2 * r + 2 : ℕ) : ℝ) = 2 * ((r : ℝ) + 1) := by push_cast; ring
  have hq : ((2 * p₀ + n₀ : ℕ) : ℝ) = 2 * (p₀ : ℝ) + n₀ := by push_cast; ring
  have hr : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by push_cast; ring
  rw [hm] at hΛb
  rw [hm, hq]
  have hs : (1 : ℝ) ≤ (r : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) r; linarith

  have hC2 : C₂ ≤ b ^ C₂ := by
    have h1 : (1 : ℝ) ≤ Real.log b := by
      rw [Real.le_log_iff_exp_le hb0]
      have := Real.exp_one_lt_d9
      linarith
    rw [Real.rpow_def_of_pos hb0]
    have h4 : C₂ ≤ Real.log b * C₂ := by nlinarith
    have := Real.add_one_le_exp (Real.log b * C₂)
    linarith
  have e1 : (2 : ℝ) ≤ b ^ (1 : ℝ) := by rw [Real.rpow_one]; linarith
  have e2 : (3 * b) ^ (2 * n₀) ≤ b ^ (4 * (n₀ : ℝ)) := by
    have : (3 * b) ^ (2 * n₀) ≤ (b * b) ^ (2 * n₀) :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) _
    refine this.trans (le_of_eq ?_)
    rw [show (4 * (n₀ : ℝ)) = ((4 * n₀ : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    ring
  have e3 : 1 * (C₂ * Λ ^ 2) ^ (r + 1) ≤
      b ^ ((C₂ + 2 * (CΛ * (2 * ((r : ℝ) + 1)))) * ((r : ℝ) + 1)) := by
    rw [one_mul, Real.rpow_mul hb0.le, ← hr, Real.rpow_natCast]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    rw [Real.rpow_add hb0, mul_comm (2 : ℝ) (CΛ * _), Real.rpow_mul hb0.le, Real.rpow_two, hr]
    exact mul_le_mul hC2 (pow_le_pow_left₀ (by linarith) hΛb 2) (by positivity) (by positivity)
  generalize ((r : ℝ) + 1) = s at *
  have hn0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  have hs2 : 1 ≤ s ^ 2 := one_le_pow₀ hs
  have hs12 : s ≤ s ^ 2 := by nlinarith
  have hs4 : s ^ 2 ≤ s ^ 4 := pow_le_pow_right₀ hs (by norm_num)
  calc _ ≤ b ^ (1 : ℝ) * b ^ (4 * (n₀ : ℝ)) * b ^ ((C₂ + 2 * (CΛ * (2 * s))) * s) *
        b ^ (2 * C₃ * (2 * s) ^ 2 * (2 * (p₀ : ℝ) + n₀)) := by
        gcongr
    _ = b ^ (1 + 4 * (n₀ : ℝ) + (C₂ + 2 * (CΛ * (2 * s))) * s +
        2 * C₃ * (2 * s) ^ 2 * (2 * (p₀ : ℝ) + n₀)) := by
        rw [Real.rpow_add hb0, Real.rpow_add hb0, Real.rpow_add hb0]
    _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hb1
        have a1 : 1 + 4 * (n₀ : ℝ) ≤ 40 * (2 * s) ^ 4 := by nlinarith
        have a2 : C₂ * s ≤ C₂ * (2 * s) ^ 4 := by
          apply mul_le_mul_of_nonneg_left _ h2.le; nlinarith
        have a3 : CΛ * (4 * s ^ 2) ≤ CΛ * (2 * s) ^ 4 := by
          apply mul_le_mul_of_nonneg_left _ hΛ; nlinarith
        have a4 : 2 * (p₀ : ℝ) + n₀ ≤ (C₀ + 9) * (2 * s) ^ 2 := by
          have : 0 ≤ C₀ * s ^ 2 := by positivity
          nlinarith
        have a5 : 2 * C₃ * (2 * s) ^ 2 * (2 * (p₀ : ℝ) + n₀) ≤
            2 * C₃ * (2 * s) ^ 2 * ((C₀ + 9) * (2 * s) ^ 2) :=
          mul_le_mul_of_nonneg_left a4 (by positivity)
        nlinarith

end GlobalTheory.JetConstSq
end

section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP2 Formalism.QuantumDeterminants

namespace GlobalTheory.JetBoundShifted

open Formalism.FourierDecayAlt.TBB MeasureTheory
open scoped ENNReal

theorem bigCellJetBound_shiftedTypePlace {P : M.Par} {Wp Wq Wq' : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] {up up' : ℕ → ℝ}
    (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P up up') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (F : B.Mat P.k P.r → (Wq' →L[ℂ] Wp)) (n₀ p₀ : ℕ) (hT : 0 < Tq p)
    (h : ∀ c : Fin (P.r + 1) → ℂ, Ew q (fun _ => 1) F (P.r + 1) [] (bigPt P.r c) ≤
      ‖(D.ptMatN (bigPt P.r c) (P.r + 1)).det‖ ^ (2 * (2 * p₀ + n₀)) * (Tq p)⁻¹ ^ n₀ *
        Ew p (fun _ => 1) f (P.r + 1) [] (bigPt P.r c)) :
    jN2 q F ≤ ENNReal.ofReal ((Tq p)⁻¹ ^ n₀) * bigCellDetWeightedEnergyIntegral p f (2 * p₀ + n₀) := by
  have hT0 : 0 ≤ (Tq p)⁻¹ ^ n₀ := by positivity
  unfold jN2 bigCellDetWeightedEnergyIntegral
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun c => ?_
  rw [← ENNReal.ofReal_mul hT0]
  refine ENNReal.ofReal_le_ofReal ((h c).trans (le_of_eq ?_))
  ring

end GlobalTheory.JetBoundShifted

namespace GlobalTheory.JetBoundShifted

open MeasureTheory
open scoped ENNReal

theorem main : ∀ C₃ CΛ C₀ C₂ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 0 ≤ C₀ → 0 < C₂ → ∃ C₄ : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp) (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Fp : B.Mat P.k P.r → (Wqp →L[ℂ] Wp)) (Fm : B.Mat P.k P.r → (Wqm →L[ℂ] Wp)) (b Λ : ℝ) (n₀ p₀ : ℕ), 3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → TBB.TTp pp = TBB.TTp p → TBB.TTp pm = TBB.TTp p → NormAtSh p pp pm f Fp Fm b n₀ p₀ → TBB.PtBound pp Fp (1 * (C₂ * Λ ^ 2) ^ (P.r + 1)) → TBB.PtBound pm Fm (1 * (C₂ * Λ ^ 2) ^ (P.r + 1)) → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  intro C₃ CΛ C₀ C₂ hC₃ hCΛ hC₀ hC₂
  obtain ⟨C₄, hC₄⟩ := GlobalTheory.JetConstSq.main C₃ CΛ C₀ C₂ hC₃ hCΛ hC₀ hC₂
  refine ⟨C₄, ?_⟩
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm f Fp Fm b Λ n₀ p₀ hb hΛ hΛb
    hn₀ hp₀ htp htm hNorm hPp hPm hReg γ hγ hG
  have hGp : 0 < TBB.Gp pp γ := by rw [gp_eq p pp htp]; exact hG
  have hGm : 0 < TBB.Gp pm γ := by rw [gp_eq p pm htm]; exact hG
  have hK := hC₄ b Λ P.r n₀ p₀ hb hΛ hΛb hn₀ hp₀
  set G := TBB.Gp p γ with hGdef
  set m : ℝ := ((2 * P.r + 2 : ℕ) : ℝ) with hm
  have hb0 : 0 < b := by linarith
  have hT0 : 0 < TBB.Tq p := p.T.base.T'_pos
  set c : ℝ := 1 * (C₂ * Λ ^ 2) ^ (P.r + 1) with hc
  have hc0 : 0 ≤ c := by positivity
  set T : ℝ := (TBB.Tq p)⁻¹ ^ n₀ with hTdef
  have hT0' : 0 ≤ T := by positivity
  set B3 : ℝ := b ^ (2 * C₃ * m ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ)) with hB3
  have hB30 : 0 ≤ B3 := by positivity
  set A : ℝ := (3 * b) ^ (2 * n₀) * (TBB.Tq p / G) ^ n₀ * G⁻¹ ^ (2 * p₀) with hA
  have hA0 : 0 ≤ A := by positivity
  set J := TBB.jN2 p f
  have hReg' : TBB.bigCellDetWeightedEnergyIntegral p f (2 * p₀ + n₀) ≤ ENNReal.ofReal B3 * J := hReg _ le_rfl
  have hEp : ENNReal.ofReal (TBB.Ew pp (fun _ => 1) Fp (P.r + 1) [] γ) ≤
      ENNReal.ofReal c * (ENNReal.ofReal T * (ENNReal.ofReal B3 * J)) := by
    refine (hPp γ hγ hGp).trans ?_
    gcongr
    exact (bigCellJetBound_shiftedTypePlace p pp f Fp n₀ p₀ hT0 fun c => hNorm.2.1 c).trans (by gcongr)
  have hEm : ENNReal.ofReal (TBB.Ew pm (fun _ => 1) Fm (P.r + 1) [] γ) ≤
      ENNReal.ofReal c * (ENNReal.ofReal T * (ENNReal.ofReal B3 * J)) := by
    refine (hPm γ hγ hGm).trans ?_
    gcongr
    exact (bigCellJetBound_shiftedTypePlace p pm f Fm n₀ p₀ hT0 fun c => hNorm.2.2 c).trans (by gcongr)
  set X := ENNReal.ofReal c * (ENNReal.ofReal T * (ENNReal.ofReal B3 * J))
  have hE : ENNReal.ofReal (TBB.Ew p (fun _ => 1) f (P.r + 1) [] γ) ≤ ENNReal.ofReal A * (2 * X) := by
    refine (ENNReal.ofReal_le_ofReal (hNorm.1 γ hγ hG)).trans ?_
    rw [ENNReal.ofReal_mul hA0]
    gcongr
    refine ENNReal.ofReal_add_le.trans ?_
    rw [two_mul]; exact add_le_add hEp hEm
  refine hE.trans ?_
  clear_value A c T B3 J G m
  have hX : ENNReal.ofReal A * (2 * X) = ENNReal.ofReal (A * 2 * c * T * B3) * J := by
    simp only [X]
    rw [show A * 2 * c * T * B3 = A * (2 * (c * (T * B3))) by ring, ENNReal.ofReal_mul hA0,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul hc0, ENNReal.ofReal_mul hT0', ENNReal.ofReal_ofNat]
    ring
  rw [hX]
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) (by simp)
  have hGne : G ≠ 0 := hG.ne'
  have heq : A * 2 * c * T * B3 = (2 * (3 * b) ^ (2 * n₀) * c * B3) * G⁻¹ ^ (2 * p₀ + n₀) := by
    simp only [hA, hTdef]
    rw [pow_add, div_eq_mul_inv]
    have : (TBB.Tq p * G⁻¹) ^ n₀ * (TBB.Tq p)⁻¹ ^ n₀ = G⁻¹ ^ n₀ := by
      rw [← mul_pow]; congr 1; field_simp
    linear_combination (2 * (3 * b) ^ (2 * n₀) * G⁻¹ ^ (2 * p₀) * c * B3) * this
  rw [heq]
  exact mul_le_mul_of_nonneg_right hK (by positivity)

end GlobalTheory.JetBoundShifted
end

section
noncomputable section

namespace GlobalTheory.GivenXi

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section sesq

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JCx2 Formalism.FourierDecayAlt.P.JCx4
open scoped ComplexConjugate

theorem formLev_sesquilinear (hΞ : B.XiExists) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (A : ℝ) (mm : ℕ)
    (hA : P5.Auser P0 w.length + 1 ≤ A) (hmm : P5.mmUser P0 w.length ≤ mm)
    (x x' y : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : ∀ a, InCC A mm (x a)) (hx' : ∀ a, InCC A mm (x' a)) (hy : ∀ a, InCC A mm (y a)) :
    D.formLev T s j w (x + c • x') y = D.formLev T s j w x y + c * D.formLev T s j w x' y ∧
      D.formLev T s j w y (x + c • x') = D.formLev T s j w y x + starRingEnd ℂ c * D.formLev T s j w y x' := by
  have hS := ma_hS P0 T s j w

  have hAB : AB P0.k (P0.r - ↑j) ≤ A - 2 * (w.length : ℝ) := by
    have h1 := pd_thr_AB P0 j w.length A hA
    linarith
  have hm5 : 5 + (2 * (P0.r - ↑j) + P0.k + 1) * w.length ≤ mm := pd_thr_mm P0 j w.length mm hmm
  have hN0 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _

  have hin : ∀ {F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)}, InCC A mm F →
      InCC (A - 2 * (w.length : ℝ) + ((2 * w.length : ℕ) : ℝ)) (5 + (2 * (P0.r - ↑j) + P0.k + 1) * w.length) F :=
    fun h => sq_inCC_mono (by push_cast; linarith) hm5 h

  have hvec : ∀ v : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp),
      (∀ a, InCC A mm (v a)) → ∀ a,
        InCC (A - 2 * (w.length : ℝ)) 5 (D.actOp (D.RRlev T s j w) v a) := by
    intro v hv a
    rw [ma_actOp_eq]
    exact sq_inCC_sum Finset.univ (fun b => (D.RRlev T s j w a b) (v b)) (fun b _ => ma_inCC (hS a b) (hin (hv b)))
  have hlow : ∀ {F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)}, InCC A mm F →
      InCC (A - 2 * (w.length : ℝ)) 5 F := fun h =>
    sq_inCC_mono (by linarith) (by omega) h
  refine ⟨?_, ?_⟩
  · show ∑ a, beta (T.bs j) (D.actOp (D.RRlev T s j w) (x + c • x') a) (y a) =
      ∑ a, beta (T.bs j) (D.actOp (D.RRlev T s j w) x a) (y a) +
        c * ∑ a, beta (T.bs j) (D.actOp (D.RRlev T s j w) x' a) (y a)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hGV : ∀ g ∈ GV P0.k (P0.r - j), D.actOp (D.RRlev T s j w) (x + c • x') a g =
        (D.actOp (D.RRlev T s j w) x a + c • D.actOp (D.RRlev T s j w) x' a) g := by
      intro g hg
      show (∑ b, D.ap (D.RRlev T s j w a b) ((x + c • x') b)) g =
        (∑ b, D.ap (D.RRlev T s j w a b) (x b) + c • ∑ b, D.ap (D.RRlev T s j w a b) (x' b)) g
      rw [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, Finset.sum_apply, Finset.smul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      exact (hS a b).2.1 _ _ (x b) (x' b) c (hin (hx b)) (hin (hx' b)) g hg
    rw [sq_beta_congr (T.bs j) hGV]
    exact (GlobalTheory.BetaSum.beta_sesq hΞ (T.bs j) hAB (hvec x hx a) (hvec x' hx' a) (hlow (hy a)) c).1
  · show ∑ a, beta (T.bs j) (D.actOp (D.RRlev T s j w) y a) ((x + c • x') a) =
      ∑ a, beta (T.bs j) (D.actOp (D.RRlev T s j w) y a) (x a) +
        conj c * ∑ a, beta (T.bs j) (D.actOp (D.RRlev T s j w) y a) (x' a)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact (GlobalTheory.BetaSum.beta_sesq hΞ (T.bs j) hAB (hlow (hx a)) (hlow (hx' a)) (hvec y hy a) c).2

theorem formLev_norm_le (hΞ : B.XiExists) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (A : ℝ)
    (hA : P5.Auser P0 w.length + 1 ≤ A) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ (u v : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (cu cv : ℝ),
      (∀ b, CCle (A - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (u b) cu) →
      (∀ a, CCle (A - 1 - 2 * (w.length : ℝ)) 5 (v a) cv) →
      ‖D.formLev T s j w u v‖ ≤ Cf * cu * cv := by
  have hR := ma_hS P0 T s j w
  set A'' : ℝ := A - 1 - 2 * (w.length : ℝ) with hA''
  have hop : ∀ a b, ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (c : ℝ),
      CCle (A'' + ((2 * w.length : ℕ) : ℝ)) (5 + (2 * (P0.r - j) + P0.k + 1) * w.length) F c →
      CCle A'' 5 (D.RRlev T s j w a b F) (K * c) := fun a b => (hR a b).1 A'' 5
  choose K hK0 hK using hop
  set KK : ℝ := ∑ a, ∑ b, K a b with hKK
  have hKK0 : 0 ≤ KK := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hK0 a b
  have hKab : ∀ a, ∑ b, K a b ≤ KK := fun a =>
    Finset.single_le_sum (f := fun a => ∑ b, K a b) (fun a _ => Finset.sum_nonneg fun b _ => hK0 a b)
      (Finset.mem_univ a)
  have hAB : AB P0.k (P0.r - j) ≤ A'' := pd_thr_AB P0 j w.length A hA
  obtain ⟨_, _, _, hB1, _, _, _⟩ := (BXiAsm.any_of hΞ) P0.k (P0.r - j) Wp Wq (T.bs j) A'' hAB
  obtain ⟨Cβ, hCβ⟩ := hB1
  have hA2 : A'' + ((2 * w.length : ℕ) : ℝ) = A - 1 := by rw [hA'']; push_cast; ring
  set card : ℝ := (Fintype.card (Wd.Ix (Fin w.length)) : ℝ)
  have hcard : 0 ≤ card := Nat.cast_nonneg _
  refine ⟨card * (|Cβ| * KK), mul_nonneg hcard (mul_nonneg (abs_nonneg _) hKK0), ?_⟩
  intro u v cu cv hcu hcv
  have hcu0 : 0 ≤ cu := pd_ccle_nonneg (hcu (Classical.arbitrary _))
  have hcv0 : 0 ≤ cv := pd_ccle_nonneg (hcv (Classical.arbitrary _))
  have hu' : ∀ b, CCle (A'' + ((2 * w.length : ℕ) : ℝ)) (5 + (2 * (P0.r - j) + P0.k + 1) * w.length) (u b) cu :=
    fun b => pd_ccle_mono (le_of_eq hA2) le_rfl (hcu b)
  have hRu : ∀ a, CCle A'' 5 (D.actOp (D.RRlev T s j w) u a) (KK * cu) := by
    intro a
    rw [ma_actOp_eq]
    refine pd_ccle_mono_c (pd_ccle_sum Finset.univ (fun b => D.RRlev T s j w a b (u b)) (fun b => K a b * cu)
      fun b _ => hK a b (u b) cu (hu' b)) ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hKab a) hcu0
  unfold D.formLev
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ a, ‖B.beta (T.bs j) (D.actOp (D.RRlev T s j w) u a) (v a)‖ ≤ |Cβ| * (KK * cu) * cv := by
    intro a
    have h := (hCβ _ _ _ _ ⟨_, hRu a⟩ ⟨_, hcv a⟩ (pd_ccle_mono le_rfl (by norm_num) (hRu a))
      (pd_ccle_mono le_rfl (by norm_num) (hcv a))).2.2
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg hKK0 hcu0)) hcv0
  refine (Finset.sum_le_sum fun a _ => hterm a).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  apply le_of_eq
  ring

theorem formLev_sesquilinear_finiteReg (hΞ : B.XiExists) : Formalism.FourierDecayAlt.JC.FormLevSesqMM := by
  intro Wp Wq _ _ _ _ _ _ P0 T s j w A mm ε _ hA hmm x x' y c hx hx' hy
  exact formLev_sesquilinear hΞ P0 T s j w A mm hA hmm x x' y c (fun a => (hx a).2.1) (fun a => (hx' a).2.1)
    (fun a => (hy a).2.1)

end sesq

section limit

open Matrix MeasureTheory Filter Topology
open scoped ContDiff
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBE Formalism.FourierDecayAlt.P.JCTx6.Lev0

theorem formLev_tendsto (hΞ : B.XiExists) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (N : ℕ) (hw : w.length ≤ N)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (x y : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (xn yn : ℕ → Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (Bd : ℝ) (dn : ℕ → ℝ)
    (hdn : Tendsto dn atTop (𝓝 0))
    (hx : ∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (x e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (x e) Bd)
    (hy : ∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (y e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (y e) Bd)
    (hxn : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (xn n e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (xn n e) Bd)
    (hyn : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (yn n e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (yn n e) Bd)
    (hdx : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (xn n e - x e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (xn n e - x e) (dn n))
    (hdy : ∀ n e, JC.CCCoefM (T.bs j) (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ (yn n e - y e) ∧
      B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (yn n e - y e) (dn n)) :
    Tendsto (fun n => D.formLev T s j w (xn n) (yn n)) atTop (𝓝 (D.formLev T s j w x y)) := by
  have hAu : P5.Auser P0 w.length + 1 ≤ P5.Auser P0 N + 1 := by linarith [auser_mono P0 hw]
  have hmu : P5.mmUser P0 w.length ≤ P5.mmUser P0 N := mmUser_mono P0 hw
  have hS := formLev_sesquilinear_finiteReg hΞ Wp Wq P0 T s j w (P5.Auser P0 N + 1) (P5.mmUser P0 N) ε₀ hε₀ hAu hmu
  obtain ⟨Cf, hCf0, hCf⟩ := formLev_norm_le hΞ P0 T s j w (P5.Auser P0 N + 1 + 1) (by linarith)
  have hmm5 : 5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ P5.mmUser P0 N := by
    have := Formalism.FourierDecayAlt.P.JCx2.pd_thr_mm P0 j N (P5.mmUser P0 N) le_rfl
    have h2 : (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ (2 * (P0.r - (j : ℕ)) + P0.k + 1) * N :=
      Nat.mul_le_mul_left _ hw
    omega
  have h5 : 5 ≤ P5.mmUser P0 N := by unfold P5.mmUser; omega
  have hu : ∀ (u : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (cu : ℝ),
      (∀ e, B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (u e) cu) →
      ∀ e, B.CCle (P5.Auser P0 N + 1 + 1 - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (u e) cu := by
    intro u cu h e
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m hmm5 (h e))
  have hv : ∀ (u : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (cu : ℝ),
      (∀ e, B.CCle (P5.Auser P0 N + 1) (P5.mmUser P0 N) (u e) cu) →
      ∀ e, B.CCle (P5.Auser P0 N + 1 + 1 - 1 - 2 * (w.length : ℝ)) 5 (u e) cu := by
    intro u cu h e
    have hw0 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m h5 (h e))
  have key : ∀ n, D.formLev T s j w (xn n) (yn n) - D.formLev T s j w x y =
      D.formLev T s j w (xn n - x) (yn n) + D.formLev T s j w x (yn n - y) := by
    intro n
    have e1 : xn n = x + (1 : ℂ) • (xn n - x) := by simp
    have e2 : yn n = y + (1 : ℂ) • (yn n - y) := by simp
    have s1 := (hS x (xn n - x) (yn n) 1 (fun e => (hx e).1) (fun e => (hdx n e).1) (fun e => (hyn n e).1)).1
    have s2 := (hS y (yn n - y) x 1 (fun e => (hy e).1) (fun e => (hdy n e).1) (fun e => (hx e).1)).2
    rw [← e1] at s1
    rw [← e2] at s2
    rw [s1, s2]
    simp
    ring
  have hbd : ∀ n, ‖D.formLev T s j w (xn n) (yn n) - D.formLev T s j w x y‖ ≤ 2 * Cf * Bd * dn n := by
    intro n
    rw [key n]
    have b1 := hCf (xn n - x) (yn n) (dn n) Bd (hu _ _ fun e => (hdx n e).2) (hv _ _ fun e => (hyn n e).2)
    have b2 := hCf x (yn n - y) Bd (dn n) (hu _ _ fun e => (hx e).2) (hv _ _ fun e => (hdy n e).2)
    calc _ ≤ ‖D.formLev T s j w (xn n - x) (yn n)‖ + ‖D.formLev T s j w x (yn n - y)‖ := norm_add_le _ _
      _ ≤ Cf * dn n * Bd + Cf * Bd * dn n := add_le_add b1 b2
      _ = 2 * Cf * Bd * dn n := by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n => 2 * Cf * Bd * dn n) atTop (𝓝 0) := by
    simpa using hdn.const_mul (2 * Cf * Bd)
  exact squeeze_zero (fun n => norm_nonneg _) hbd hlim

theorem levelForm_cutoff_tendsto_below (hΞ : B.XiExists) : ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ Cc : ℝ, Cl ≤ Cc →
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ) (cut : ℕ → B.Mat P.k P.r → ℂ),
    C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    (∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) →
    ∀ i, i ≤ P.r → ∀ w : List C.Letter, w.length ≤ N → ∀ a b,
      Tendsto (fun n => p.RR (fun g => cut n g • D.cutF p.T.base χ f ε g) i w a b) atTop
        (𝓝 (p.RR (D.cutF p.T.base χ f ε) i w a b)) := by
  obtain ⟨Cs, hCs0, hSQ⟩ := sliceQ
  refine ⟨Cs + 1, by positivity, ?_⟩
  intro Cc hCc Wp Wq _ _ _ _ _ _ P p f χ ε A N cut hχ hε hf hfA hA hcut i hi w hw a b
  have hk2 : 2 ≤ P.k := p.hl.2.2
  set X : ℝ := (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3 with hX
  have hX1 : 1 ≤ X := by
    have h1 : (1 : ℝ) ≤ 2 * (P.r : ℝ) + P.k + 1 := by
      have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
      linarith
    have : 1 ≤ (2 * (P.r : ℝ) + P.k + 1) ^ 3 := one_le_pow₀ h1
    have : 0 ≤ (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 := by positivity
    linarith
  have hR4 : 1 ≤ ((P.r : ℝ) + 1) ^ 4 := one_le_pow₀ (by have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _; linarith)
  have hA' : Cs * ((P.r : ℝ) + 1) ^ 4 * X ≤ A - 1 := by
    have h1 : (Cs + 1) * ((P.r : ℝ) + 1) ^ 4 * X ≤ A :=
      le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCc (by positivity)) (by positivity)) hA
    have h2 : 1 ≤ ((P.r : ℝ) + 1) ^ 4 * X := by nlinarith
    nlinarith
  set M := 3 * (11 * (N * (2 * P.r + P.k + 1) ^ 2 + (2 * P.r + P.k + 1) ^ 3) + 5) with hM
  obtain ⟨bf, hbf⟩ := hfA M
  have hbf0 : 0 ≤ bf := JCx2.pd_ccle_nonneg hbf
  have hbf' : B.CCle (A - 1) M f bf := BetaSesquilinearity.CCle_mono_A (by linarith) hbf
  obtain ⟨Kp, hKp0, hKp⟩ := JCx2.pd_cut_ccle (k := P.k) (r := P.r) (E := Wq →L[ℂ] Wp) M
  have hψ : ∀ n : ℕ, B.CCle (A - 1) M (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) (Kp * bf / ((n : ℝ) + 1)) :=
    fun n => hKp _ (by positivity) A f bf hbf
  have hψs : ∀ n : ℕ, B.CkOn ⊤ (B.GV P.k P.r) (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) :=
    fun n => JCx2.pd_smooth_smul (JCx2.pd_psi_cd _) hf
  set hn : ℕ → B.Mat P.k P.r → (Wq →L[ℂ] Wp) := fun n g => cut n g • f g with hhn
  have hneq : ∀ n, hn n = fun g => f g + (-1 : ℂ) • (JCx2.pdPsi ((n : ℝ) + 1) g • f g) := by
    intro n; funext g
    simp only [hhn, cut_eq cut hcut n g, sub_smul, one_smul]
    simp [sub_eq_add_neg]
  have hnC : ∀ n, B.CCle (A - 1) M (hn n) (bf + Kp * bf) := by
    intro n
    rw [hneq n]
    refine JCx2.pd_ccle_mono_c (BetaSesquilinearity.CCle_add hbf' (BetaSesquilinearity.CCle_smul (-1) (hψ n))) ?_
    have h1 : Kp * bf / ((n : ℝ) + 1) ≤ Kp * bf := div_le_self (by positivity) (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    simp only [norm_neg, norm_one, one_mul]
    linarith
  have hns : ∀ n, B.CkOn ⊤ (B.GV P.k P.r) (hn n) := by
    intro n
    rw [hneq n]
    exact BetaSesquilinearity.CkOn_add hf (BetaSesquilinearity.CkOn_smul (-1) (hψs n))
  have hsub : ∀ n, (fun g => f g - hn n g) = fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g := by
    intro n; funext g
    rw [hneq n]; simp
  have hFn : ∀ n, (fun g => cut n g • D.cutF p.T.base χ f ε g) = D.cutF p.T.base χ (hn n) ε := by
    intro n; funext g
    simp only [D.cutF, hhn]
    rw [smul_comm]
  simp only [KB.Pl.RR, hFn]
  unfold D.RRplace
  by_cases hab : D.IsLocPt a i ∧ D.IsLocPt b i
  swap
  · simp only [dif_neg hab]; exact tendsto_const_nhds
  simp only [dif_pos hab, dif_pos hi]
  have hca : P.r - i = P.r - D.ptSize a := by simp [hab.1.2]
  have hcb : P.r - i = P.r - D.ptSize b := by simp [hab.2.2]
  have hQa := fun e => hSQ Cs le_rfl P.k P.r Wp Wq p.T χ (A - 1) N P rfl rfl hk2 hχ hA' ε hε i hi w hw a hca hab.1 e
  have hQb := fun e => hSQ Cs le_rfl P.k P.r Wp Wq p.T χ (A - 1) N P rfl rfl hk2 hχ hA' ε hε i hi w hw b hcb hab.2 e
  choose εa Ka hεa hKa hQ1a hQ2a using hQa
  choose εb Kb hεb hKb hQ1b hQ2b using hQb
  set S : ℝ := ∑ e, (εa e)⁻¹ + ∑ e, (εb e)⁻¹ with hS
  have hSa : ∀ e, (εa e)⁻¹ ≤ S := by
    intro e
    have h1 : (εa e)⁻¹ ≤ ∑ e, (εa e)⁻¹ :=
      Finset.single_le_sum (f := fun e => (εa e)⁻¹) (fun e _ => (inv_pos.2 (hεa e)).le) (Finset.mem_univ e)
    have h2 : 0 ≤ ∑ e, (εb e)⁻¹ := Finset.sum_nonneg fun e _ => (inv_pos.2 (hεb e)).le
    linarith
  have hSb : ∀ e, (εb e)⁻¹ ≤ S := by
    intro e
    have h1 : (εb e)⁻¹ ≤ ∑ e, (εb e)⁻¹ :=
      Finset.single_le_sum (f := fun e => (εb e)⁻¹) (fun e _ => (inv_pos.2 (hεb e)).le) (Finset.mem_univ e)
    have h2 : 0 ≤ ∑ e, (εa e)⁻¹ := Finset.sum_nonneg fun e _ => (inv_pos.2 (hεa e)).le
    linarith
  have hS0 : 0 < S := lt_of_lt_of_le (inv_pos.2 (hεa Wd.e1)) (hSa Wd.e1)
  have hε₀a : ∀ e, S⁻¹ ≤ εa e := fun e => by
    have := inv_anti₀ (inv_pos.2 (hεa e)) (hSa e); rwa [inv_inv] at this
  have hε₀b : ∀ e, S⁻¹ ≤ εb e := fun e => by
    have := inv_anti₀ (inv_pos.2 (hεb e)) (hSb e); rwa [inv_inv] at this
  set KK : ℝ := ∑ e, Ka e + ∑ e, Kb e with hKK
  have hKa' : ∀ e, Ka e ≤ KK := by
    intro e
    have h1 : Ka e ≤ ∑ e, Ka e := Finset.single_le_sum (f := Ka) (fun e _ => hKa e) (Finset.mem_univ e)
    have h2 : 0 ≤ ∑ e, Kb e := Finset.sum_nonneg fun e _ => hKb e
    linarith
  have hKb' : ∀ e, Kb e ≤ KK := by
    intro e
    have h1 : Kb e ≤ ∑ e, Kb e := Finset.single_le_sum (f := Kb) (fun e _ => hKb e) (Finset.mem_univ e)
    have h2 : 0 ≤ ∑ e, Ka e := Finset.sum_nonneg fun e _ => hKa e
    linarith
  have hKK0 : 0 ≤ KK := le_trans (hKa Wd.e1) (hKa' Wd.e1)
  have hB1 : bf ≤ bf + Kp * bf := by nlinarith

  have main : ∀ (q : C.LPt) (hcq : P.r - i = P.r - D.ptSize q) (εq Kq : Wd.Ix (Fin w.length) → ℝ),
      (∀ e, S⁻¹ ≤ εq e) → (∀ e, 0 ≤ Kq e) → (∀ e, Kq e ≤ KK) →
      (∀ e (h : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : ℝ), B.CkOn ⊤ (B.GV P.k P.r) h → B.CCle (A - 1) M h c →
        JC.CCCoefM (p.T.bs i) (P5.Auser P N + 1) (P5.mmUser P N) (εq e) (xs p.T χ ε i hi w q hcq h e) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N) (xs p.T χ ε i hi w q hcq h e) (Kq e * c)) →
      (∀ e (h₁ h₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c₁ c₂ : ℝ), B.CkOn ⊤ (B.GV P.k P.r) h₁ →
        B.CkOn ⊤ (B.GV P.k P.r) h₂ → B.CCle (A - 1) M h₁ c₁ → B.CCle (A - 1) M h₂ c₂ →
        ∀ γ ∈ B.GV P.k (P.r - i), xs p.T χ ε i hi w q hcq h₁ e γ - xs p.T χ ε i hi w q hcq h₂ e γ =
          xs p.T χ ε i hi w q hcq (fun g => h₁ g - h₂ g) e γ) →
      (∀ e, JC.CCCoefM (p.T.bs i) (P5.Auser P N + 1) (P5.mmUser P N) S⁻¹ (xs p.T χ ε i hi w q hcq f e) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N) (xs p.T χ ε i hi w q hcq f e) (KK * (bf + Kp * bf))) ∧
      (∀ n e, JC.CCCoefM (p.T.bs i) (P5.Auser P N + 1) (P5.mmUser P N) S⁻¹ (xs p.T χ ε i hi w q hcq (hn n) e) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N) (xs p.T χ ε i hi w q hcq (hn n) e) (KK * (bf + Kp * bf))) ∧
      (∀ n e, JC.CCCoefM (p.T.bs i) (P5.Auser P N + 1) (P5.mmUser P N) S⁻¹
          (xs p.T χ ε i hi w q hcq (hn n) e - xs p.T χ ε i hi w q hcq f e) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N)
          (xs p.T χ ε i hi w q hcq (hn n) e - xs p.T χ ε i hi w q hcq f e) (KK * (Kp * bf / ((n : ℝ) + 1)))) := by
    intro q hcq εq Kq hεq hKq hKq' hQ1 hQ2
    refine ⟨fun e => ?_, fun n e => ?_, fun n e => ?_⟩
    · obtain ⟨h1, h2⟩ := hQ1 e f bf hf hbf'
      exact ⟨cccoef_mono h1 (hεq e), JCx2.pd_ccle_mono_c h2 (mul_le_mul (hKq' e) hB1 hbf0 hKK0)⟩
    · obtain ⟨h1, h2⟩ := hQ1 e (hn n) _ (hns n) (hnC n)
      exact ⟨cccoef_mono h1 (hεq e), JCx2.pd_ccle_mono_c h2 (mul_le_mul_of_nonneg_right (hKq' e) (by positivity))⟩
    · obtain ⟨h1, h2⟩ := hQ1 e _ _ (hψs n) (hψ n)
      have hd : ∀ γ ∈ B.GV P.k (P.r - i), (fun γ => (-1 : ℂ) • xs p.T χ ε i hi w q hcq
          (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) e γ) γ =
          (xs p.T χ ε i hi w q hcq (hn n) e - xs p.T χ ε i hi w q hcq f e) γ := by
        intro γ hγ
        have := hQ2 e f (hn n) bf _ hf (hns n) hbf' (hnC n) γ hγ
        rw [hsub n] at this
        simp only [Pi.sub_apply, ← this]
        simp
      have hC2 := Formalism.FourierDecayAlt.P.Ux1.cc_congr hd (BetaSesquilinearity.CCle_smul (-1) h2)
      simp only [norm_neg, norm_one, one_mul] at hC2
      have hC3 := JCx2.pd_ccle_mono_c hC2 (mul_le_mul_of_nonneg_right (hKq' e) (by positivity))
      refine ⟨⟨hC3.1, ⟨_, hC3⟩, fun γ hγ hne => ?_⟩, hC3⟩
      rw [← hd γ hγ] at hne
      have hne' : xs p.T χ ε i hi w q hcq (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) e γ ≠ 0 := by
        intro h0; apply hne; simp [h0]
      exact (hεq e).trans (h1.2.2 γ hγ hne')
  obtain ⟨ma1, ma2, ma3⟩ := main a hca εa Ka hε₀a hKa hKa' hQ1a hQ2a
  obtain ⟨mb1, mb2, mb3⟩ := main b hcb εb Kb hε₀b hKb hKb' hQ1b hQ2b
  have hdn : Tendsto (fun n : ℕ => KK * (Kp * bf / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat.congr
      (fun n => by simp)
    have := (h1.const_mul (Kp * bf)).const_mul KK
    simpa [div_eq_mul_inv, mul_assoc] using this
  exact formLev_tendsto hΞ P p.T _ ⟨i, by omega⟩ w N hw S⁻¹ (inv_pos.2 hS0)
    (xs p.T χ ε i hi w a hca f) (xs p.T χ ε i hi w b hcb f)
    (fun n => xs p.T χ ε i hi w a hca (hn n)) (fun n => xs p.T χ ε i hi w b hcb (hn n))
    (KK * (bf + Kp * bf)) (fun n => KK * (Kp * bf / ((n : ℝ) + 1))) hdn ma1 mb1 ma2 mb2 ma3 mb3

theorem levelForm_cutoff_tendsto (hΞ : B.XiExists) : Formalism.FourierDecayAlt.KB.FormLimit := by
  intro Cb
  obtain ⟨Cl, _, hL⟩ := levelForm_cutoff_tendsto_below hΞ
  obtain ⟨Ct, hT⟩ := PBE.formLimit_top Cb
  refine ⟨max Cl Ct, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P0 p f χ ε A N cut hDD hχ hε hf hfA hA hcut
  refine ⟨fun n => PBE.cutCpt P0 p.T.base f χ ε cut hχ hε hf hcut n, ?_⟩
  intro i w hwc hw a b
  have hX : 0 ≤ ((P0.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P0.r : ℝ) + P0.k + 1) ^ 2 + (2 * (P0.r : ℝ) + P0.k + 1) ^ 3) := by
    positivity
  rcases lt_trichotomy i (P0.r + 1) with hlt | heq | hgt
  · exact hL (max Cl Ct) (le_max_left _ _) Wp Wq P0 p f χ ε A N cut hχ hε hf hfA hA hcut i (by omega) w hw a b
  · subst heq
    refine hT Wp Wq P0 p f χ ε A N cut hDD hχ hε hf hfA ?_ hcut w hwc hw a b
    refine le_trans ?_ hA
    have := mul_le_mul_of_nonneg_right (le_max_right Cl Ct) hX
    nlinarith
  · have h0 : ∀ F, p.RR F i w a b = 0 := by
      intro F
      unfold KB.Pl.RR D.RRplace
      split_ifs <;> first | rfl | (exfalso; omega)
    simp only [h0]
    exact tendsto_const_nhds

end limit

end GlobalTheory.GivenXi

end
end

section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.QuantumDeterminants NumberField MeasureTheory Filter Topology
open scoped ComplexOrder

namespace GlobalTheory.LevelZeroLimit

noncomputable section

theorem limPos_of_compactPositivity (hΞ : B.XiExists) (hA : P5.ThmPActualCpt) {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF : KB.CptCoef p.T.base F) (Y : Finset ℝ) (N : ℕ) : LimPos p F Y N := by
  intro w hw _
  have hh : D.IsLocPt ([] : C.LPt) 0 := ⟨by simp, rfl⟩
  rw [PBL.rr_eq_form p F 0 (Nat.zero_le _) w [] [] hh hh]
  have h := GlobalTheory.WeightedFormPos.formPosCpt_of_xiExists hΞ hA Wp Wq P p 0 (Nat.zero_le _) w hw.1 _
    (fun e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F 0 (Nat.zero_le _) w [] hh hF e)
  simpa using (Complex.le_def.1 h).1

theorem limPos_of_limEvT_of_compactPositivity (hΞ : B.XiExists) (hA : P5.ThmPActualCpt) (Cb : ℝ) :
    ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ)
    (A : ℝ) (N : ℕ) (Y : Finset ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    LimEvT p χ F Y N → LimPos p F Y N := by
  obtain ⟨Cc, hCc⟩ := GlobalTheory.GivenXi.levelForm_cutoff_tendsto hΞ Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p F χ A N Y hDD hχ hF hFA hth hEv w hw hN
  have hcut : ∀ ε : ℝ, 0 < ε → 0 ≤ (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re := by
    intro ε hε
    obtain ⟨hcpt, hlim⟩ := hCc Wp Wq P p F χ ε A N (cutN P.k P.r) hDD hχ hε hF hFA hth (fun _ _ => rfl)
    have hT := (Complex.continuous_re.tendsto _).comp (hlim 0 w hw.1 hN [] [])
    exact ge_of_tendsto hT
      (Eventually.of_forall fun n => limPos_of_compactPositivity hΞ hA p (hcpt n) Y N w hw hN)
  exact ge_of_tendsto (hEv w hw hN) (eventually_nhdsWithin_of_forall fun ε hε => hcut ε hε)

theorem limE_of_limEvT_of_xiExists (hΞ : B.XiExists) :
    P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ nn : ℝ → ℝ) (A : ℝ) (N : ℕ) (Y : Finset ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → (∀ y, 0 ≤ nn y) → B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → LimEvT p χ F Y N → LimBd p nn F Y N → LimE p nn χ F Y N := by
  intro hA Cb
  obtain ⟨Cc, hCc⟩ := limPos_of_limEvT_of_compactPositivity hΞ hA Cb
  exact ⟨Cc, fun Wp Wq _ _ _ _ _ _ P p F χ nn A N Y hDD hχ hnn hF hFA hth hEv hBd =>
    limE_of_partsT p nn χ F Y N hnn hEv (hCc Wp Wq P p F χ A N Y hDD hχ hF hFA hth hEv) hBd⟩

end

end GlobalTheory.LevelZeroLimit
end

section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants
open Filter Topology

namespace GlobalTheory.PointwiseBoundDecay

theorem levelZero_limit_of_xiExists (hΞ : B.XiExists) (Cb : ℝ) : ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ)
    (ε A : ℝ) (N : ℕ) (nn : ℝ → ℝ) (Y : Finset ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f →
    (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    LimZeroN p nn (D.cutF p.T.base χ f ε) Y N := by
  obtain ⟨Cc, hCc⟩ := GlobalTheory.GivenXi.levelForm_cutoff_tendsto hΞ Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ ε A N nn Y hDD hχ hε hf hfA hA
  have hFL := (hCc Wp Wq P p f χ ε A N (cutN P.k P.r) hDD hχ hε hf hfA hA (fun _ _ => rfl)).2
  intro w hw hN
  have hT := hFL 0 w hw.1 hN [] []
  have hre := (Complex.continuous_re.tendsto _).comp hT
  have e1 : ∀ n : ℕ, TBB.Ew p nn (apx (D.cutF p.T.base χ f ε) n) 0 w [] =
      (p.RR (fun g => cutN P.k P.r n g • D.cutF p.T.base χ f ε g) 0 w [] []).re / TBB.normC nn w :=
    fun n => Formalism.FourierDecayAlt.P.TBBx3.ew_zero_nil p nn _ w
  have e2 : TBB.Ew p nn (D.cutF p.T.base χ f ε) 0 w [] =
      (p.RR (D.cutF p.T.base χ f ε) 0 w [] []).re / TBB.normC nn w :=
    Formalism.FourierDecayAlt.P.TBBx3.ew_zero_nil p nn _ w
  simp only [e1, e2]
  exact hre.div_const _

theorem top_threshold_le (r k N : ℕ) :
    ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤
      ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  push_cast
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn
  have h1 : 1 ≤ n := by linarith
  have h3 : n ≤ n ^ 3 := le_self_pow₀ h1 (by norm_num)
  have h4 : (r : ℝ) * n + 1 ≤ ((r : ℝ) + 1) * n := by nlinarith
  have h5 : ((r : ℝ) + 1) ≤ ((r : ℝ) + 1) ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  have h6 : n ≤ (N : ℝ) * n ^ 2 + n ^ 3 := by
    have : 0 ≤ (N : ℝ) * n ^ 2 := by positivity
    linarith
  have h7 : ((r : ℝ) + 1) * n ≤ ((r : ℝ) + 1) ^ 2 * ((N : ℝ) * n ^ 2 + n ^ 3) :=
    mul_le_mul h5 h6 (by linarith) (by positivity)
  calc ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * n + 1)
      ≤ ((r : ℝ) + 1) ^ 2 * (((r : ℝ) + 1) ^ 2 * ((N : ℝ) * n ^ 2 + n ^ 3)) :=
        mul_le_mul_of_nonneg_left (h4.trans h7) (by positivity)
    _ = _ := by ring

open GlobalTheory.PointwiseBound in

theorem ptBound_of_xiExists (hXi : B.XiExists) (hA : P5.ThmPActualCpt) : ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Λ κ₀ : ℝ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ), 1 ≤ Λ → 0 < κ₀ → 3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) → KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) F → TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn (apx (D.cutF p.T.base χ F ε) n) Y K N) → (∀ ε : ℝ, 0 < ε → LimTopN p nn (D.cutF p.T.base χ F ε)) → (∀ ε : ℝ, 0 < ε → LimZeroN p nn (D.cutF p.T.base χ F ε) Y N) → LimE p nn χ F Y N → LemB p F κ₀ → TBB.PtBound p F (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)) := by
  have hRad := GlobalTheory.WeightedFormPos.radialModuleForm_of_xiExists hXi
  have hSS := GlobalTheory.ListDuality.listDuality_cpt hRad
  have hVI := waveIsometry_of_radial hRad
  have hFP := GlobalTheory.WeightedFormPos.formPosCpt_of_xiExists hXi
  have hI4 := GlobalTheory.LiftBoundCpt.liftBound_of_xiExists hXi hA hSS hFP
  obtain ⟨C₂, hC₂, hLS⟩ := Formalism.FourierDecayAlt.P.lemma_s_of_parts Formalism.FourierDecayAlt.P.lemma_s_induction_base
    Formalism.FourierDecayAlt.P.lemma_s_induction_up
  refine ⟨C₂, hC₂, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p F Λ κ₀ χ nn Y K N Cb hΛ hκ hK hKN hχ hnn hCb hF hWG hLG hI5 hTN hZN hE hB
  refine Formalism.FourierDecayAlt.P.point_bound_of_corollary_s Wp Wq P p nn χ F Y Λ K N C₂ κ₀ hC₂.le hκ hnn
    ⟨1, one_pos, fun ε hε _ => ?_⟩ (Formalism.FourierDecayAlt.P.vector_truncation_at_place p χ F hχ.2.2)
    (Formalism.FourierDecayAlt.P.limit_zero_at_place p nn χ F Y N κ₀ hE hB)
  refine corS_of_apx p nn _ Y Λ K N C₂ (fun n => ?_) (hTN ε hε) (hZN ε hε)
  have hG := cptCoef_apx P p.T.base hχ hF hε n
  have hPos := GlobalTheory.WeightedFormPos.posAt_of_cptCoef_of_xiExists hXi hA Wp Wq P p nn _ Y N (fun y => (hnn y).le) hG
  exact Formalism.FourierDecayAlt.P.corSOfLemmaS_statement Wp Wq P p nn _ Y Λ K N C₂ hKN hC₂.le hPos
    (hLS Wp Wq P p nn _ Y Λ K N hK hΛ hPos (extension_at_zero hXi hA p nn _ Y N Cb hCb hG)
      (GlobalTheory.planeWave_bound_of_xiExists hXi hA hVI hSS hFP Wp Wq P p nn _ Y Λ K N Cb hCb hG hnn hWG)
      (hI4 Wp Wq P p nn _ Y Λ K N hG hnn hLG) (hI5 ε hε n))

theorem main : P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ C₂ Cc : ℝ, 0 < C₂ ∧ ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Λ A : ℝ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ), 1 ≤ Λ → 3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) → KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn (apx (D.cutF p.T.base χ F ε) n) Y K N) → LimEvT p χ F Y N → LimBd p nn F Y N → TBB.PtBound p F (1 * (C₂ * Λ ^ 2) ^ (P.r + 1)) := by
  intro hA Cb
  have hXi : B.XiExists := Formalism.FourierDecayAlt.P.exists_auxiliary_xi
  obtain ⟨C₂, hC₂, hPt⟩ := ptBound_of_xiExists hXi hA
  obtain ⟨c₃, hc₃⟩ := limTopN_cut_of_inCC
  obtain ⟨Ca, hCa⟩ := levelZero_limit_of_xiExists hXi Cb
  obtain ⟨Ce, hE⟩ := GlobalTheory.LevelZeroLimit.limE_of_limEvT_of_xiExists hXi hA Cb
  refine ⟨C₂, max (max 0 c₃) (max Ca Ce), hC₂, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P q F Λ A χ nn Y K N hΛ hK hKN hχ hnn hCb hF hFA hth hWG hLG hI5 hLim hBd
  set C : ℝ := max (max 0 c₃) (max Ca Ce) with hC
  have hC0 : 0 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hC3 : c₃ ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hCa' : Ca ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCe' : Ce ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hmono : ∀ c : ℝ, c ≤ C → c * ((P.r : ℝ) + 1) ^ 4 *
      ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A := fun c hc =>
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)).trans hth
  have hth1 : c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A := by
    refine le_trans ?_ hth
    rw [mul_assoc, mul_assoc]
    exact (mul_le_mul_of_nonneg_right hC3 (by positivity)).trans
      (mul_le_mul_of_nonneg_left (top_threshold_le P.r P.k N) hC0)
  exact hPt Wp Wq P q F Λ 1 χ nn Y K N Cb hΛ one_pos hK hKN hχ hnn hCb hF hWG hLG hI5
    (hc₃ Wp Wq P q nn χ F A hth1 hχ hFA hF)
    (fun ε hε => hCa Wp Wq P q F χ ε A N nn Y hCb hχ hε hF hFA (hmono _ hCa'))
    (hE Wp Wq P q F χ nn A N Y hCb hχ (fun y => (hnn y).le) hF hFA (hmono _ hCe') hLim hBd)
    (lemB_one q F)

end GlobalTheory.PointwiseBoundDecay
end

section
section
open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants

namespace GlobalTheory.JetBoundEqualTypesReg

theorem of_compact : P5.ThmPActualCpt → ∀ Cb C₃ CΛ C₀ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp) (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)) (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq)) (b Λ A₀ : ℝ) (n₀ p₀ d : ℕ) (χ nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ), 3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → pp.T.base.z = p.T.base.z → pp.T.base.z' = p.T.base.z' → pm.T.base.z = p.T.base.z → pm.T.base.z' = p.T.base.z' → 3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) → KB.InDDplus2 (shP P up up') pp.l0 pp.T.base Cb pp.Θ → KB.InDDplus2 (shP P um um') pm.l0 pm.T.base Cb pm.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → CutBPEq.PolyOp d Ap → CutBPEq.PolyOp d Am → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d → AmapsSh p pp pm f Ap Am ApPt AmPt b n₀ → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBBx5.WaveGrid pp nnp Yp Λ K N → TBBx5.LiftGrid pp nnp Yp Λ K N → TBBx5.WaveGrid pm nnm Ym Λ K N → TBBx5.LiftGrid pm nnm Ym Λ K N → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pp nnp (apx (D.cutF pp.T.base χ (fpmSh pp f Ap p₀) ε) n) Yp K N) → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pm nnm (apx (D.cutF pm.T.base χ (fpmSh pm f Am p₀) ε) n) Ym K N) → LimEvT pp χ (fpmSh pp f Ap p₀) Yp N → LimEvT pm χ (fpmSh pm f Am p₀) Ym N → LimBd pp nnp (fpmSh pp f Ap p₀) Yp N → LimBd pm nnm (fpmSh pm f Am p₀) Ym N → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  intro hA Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨C₂, Cc, hC₂, hPt⟩ := GlobalTheory.PointwiseBoundDecay.main hA Cb
  obtain ⟨C₄, hC₄⟩ := GlobalTheory.JetBoundShifted.main C₃ CΛ C₀ C₂ hC₃ hCΛ hC₀ hC₂
  refine ⟨C₄, Cc, ?_⟩
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm f Ap Am ApPt AmPt b Λ A₀ n₀ p₀ d χ nnp nnm
    Yp Ym K N hb hΛ hΛb hn₀ hp₀ hzp hzp' hzm hzm' hK hKN hχ hnnp hnnm hDDp hDDm hf hfA hAp hAm hth
    hAms hReg hWGp hLGp hWGm hLGm hI5p hI5m hDp hDm hBdp hBdm
  have hNorm := normaliser_across_places P Wp Wq Wqp Wqm up up' um um' p pp pm f Ap Am ApPt AmPt b n₀ p₀
    hzp hzp' hzm hzm' hAms
  have hdp := shifted_decay P Wp Wq Wqp up up' pp f Ap A₀ d p₀ hfA hAp
  have hdm := shifted_decay P Wp Wq Wqm um um' pm f Am A₀ d p₀ hfA hAm
  have hPp := hPt Wp Wqp (shP P up up') pp (fpmSh pp f Ap p₀) Λ _ χ nnp Yp K N hΛ hK hKN hχ hnnp hDDp
    (ckOn_fpmSh pp p₀ hf (ckOn_of_polyOp hAp)) hdp hth hWGp hLGp hI5p hDp hBdp
  have hPm := hPt Wp Wqm (shP P um um') pm (fpmSh pm f Am p₀) Λ _ χ nnm Ym K N hΛ hK hKN hχ hnnm hDDm
    (ckOn_fpmSh pm p₀ hf (ckOn_of_polyOp hAm)) hdm hth hWGm hLGm hI5m hDm hBdm
  exact hC₄ P Wp Wq Wqp Wqm up up' um um' p pp pm f _ _ b Λ n₀ p₀ hb hΛ hΛb hn₀ hp₀
    (ttp_eq p pp hzp hzp') (ttp_eq p pm hzm hzm') hNorm hPp hPm hReg

theorem main : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → ∀ Cb C₃ CΛ C₀ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp) (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)) (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq)) (b Λ A₀ : ℝ) (n₀ p₀ d : ℕ) (χ nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ), 3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → pp.T.base.z = p.T.base.z → pp.T.base.z' = p.T.base.z' → pm.T.base.z = p.T.base.z → pm.T.base.z' = p.T.base.z' → 3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) → KB.InDDplus2 (shP P up up') pp.l0 pp.T.base Cb pp.Θ → KB.InDDplus2 (shP P um um') pm.l0 pm.T.base Cb pm.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → CutBPEq.PolyOp d Ap → CutBPEq.PolyOp d Am → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d → AmapsSh p pp pm f Ap Am ApPt AmPt b n₀ → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBBx5.WaveGrid pp nnp Yp Λ K N → TBBx5.LiftGrid pp nnp Yp Λ K N → TBBx5.WaveGrid pm nnm Ym Λ K N → TBBx5.LiftGrid pm nnm Ym Λ K N → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pp nnp (apx (D.cutF pp.T.base χ (fpmSh pp f Ap p₀) ε) n) Yp K N) → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pm nnm (apx (D.cutF pm.T.base χ (fpmSh pm f Am p₀) ε) n) Ym K N) → LimEvT pp χ (fpmSh pp f Ap p₀) Yp N → LimEvT pm χ (fpmSh pm f Am p₀) Ym N → LimBd pp nnp (fpmSh pp f Ap p₀) Yp N → LimBd pm nnm (fpmSh pm f Am p₀) Ym N → TBB.ThmBpAt p f b C₄ n₀ p₀ :=
  fun _ => of_compact

end GlobalTheory.JetBoundEqualTypesReg
end

open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetBound_equalTypes_threePlaces_of_xiIntegrable : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → ∀ Cb C₃ CΛ C₀ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp) (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)) (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq)) (b Λ A₀ : ℝ) (n₀ p₀ d : ℕ) (χ nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ), 3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → pp.T.base.z = p.T.base.z → pp.T.base.z' = p.T.base.z' → pm.T.base.z = p.T.base.z → pm.T.base.z' = p.T.base.z' → 3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) → KB.InDDplus2 (shP P up up') pp.l0 pp.T.base Cb pp.Θ → KB.InDDplus2 (shP P um um') pm.l0 pm.T.base Cb pm.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → CutBPEq.PolyOp d Ap → CutBPEq.PolyOp d Am → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d → AmapsSh p pp pm f Ap Am ApPt AmPt b n₀ → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBBx5.WaveGrid pp nnp Yp Λ K N → TBBx5.LiftGrid pp nnp Yp Λ K N → TBBx5.WaveGrid pm nnm Ym Λ K N → TBBx5.LiftGrid pm nnm Ym Λ K N → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pp nnp (apx (D.cutF pp.T.base χ (fpmSh pp f Ap p₀) ε) n) Yp K N) → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pm nnm (apx (D.cutF pm.T.base χ (fpmSh pm f Am p₀) ε) n) Ym K N) → LimEvT pp χ (fpmSh pp f Ap p₀) Yp N → LimEvT pm χ (fpmSh pm f Am p₀) Ym N → LimBd pp nnp (fpmSh pp f Ap p₀) Yp N → LimBd pm nnm (fpmSh pm f Am p₀) Ym N → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  atlas_forward_decl GlobalTheory.JetBoundEqualTypesReg.main
end

section
open MeasureTheory Filter Topology

namespace GlobalTheory

theorem memLp_and_tendsto_integral_inner_of_eventually_eq : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (a : ℝ → X → E) (u : X → E) (h : X → ℝ), Integrable h μ → (∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (a ε) μ) → (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ x ∂μ, ‖a ε x‖ ^ 2 ≤ h x) → (∀ᵐ x ∂μ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), a ε x = u x) → MemLp u 2 μ ∧ Tendsto (fun ε : ℝ => ∫ x, inner ℂ (a ε x) (u x) ∂μ) (𝓝[>] 0) (𝓝 (((∫ x, ‖u x‖ ^ 2 ∂μ : ℝ) : ℂ))) := by
  intro X _ μ E _ _ a u h hh hm hb he

  obtain ⟨s, hs⟩ := (𝓝[>] (0 : ℝ)).exists_seq_tendsto
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hs.eventually (hm.and hb))
  have hs' : Tendsto (fun n => s (n + N)) atTop (𝓝[>] (0 : ℝ)) :=
    hs.comp (tendsto_add_atTop_nat N)
  have hev : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, a (s (n + N)) x = u x := by
    filter_upwards [he] with x hx
    exact hs'.eventually hx
  have hu : AEStronglyMeasurable u μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun n => a (s (n + N)))
      (fun n => (hN (n + N) (Nat.le_add_left _ _)).1) ?_
    filter_upwards [hev] with x hx
    exact tendsto_const_nhds.congr' (hx.mono fun n hn => hn.symm)
  have hub : ∀ᵐ x ∂μ, ‖u x‖ ^ 2 ≤ h x := by
    have h1 : ∀ᵐ x ∂μ, ∀ n, ‖a (s (n + N)) x‖ ^ 2 ≤ h x :=
      ae_all_iff.2 fun n => (hN (n + N) (Nat.le_add_left _ _)).2
    filter_upwards [hev, h1] with x hx h1x
    obtain ⟨n, hn⟩ := hx.exists
    rw [← hn]; exact h1x n
  refine ⟨?_, ?_⟩
  · rw [memLp_two_iff_integrable_sq_norm hu]
    refine hh.mono' (hu.norm.pow 2) ?_
    filter_upwards [hub] with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    exact hx
  · have key : (((∫ x, ‖u x‖ ^ 2 ∂μ : ℝ) : ℂ)) = ∫ x, inner ℂ (u x) (u x) ∂μ := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    rw [key]
    refine tendsto_integral_filter_of_dominated_convergence h ?_ ?_ hh ?_
    · filter_upwards [hm] with ε hε
      exact hε.inner hu
    · filter_upwards [hb] with ε hε
      filter_upwards [hε, hub] with x h1 h2
      have := norm_inner_le_norm (𝕜 := ℂ) (a ε x) (u x)
      nlinarith [sq_nonneg (‖a ε x‖ - ‖u x‖)]
    · filter_upwards [he] with x hx
      exact tendsto_const_nhds.congr' (hx.mono fun ε hε => by simp only [hε])

end GlobalTheory
end

section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

namespace GlobalTheory.BetaCutLimit

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end GlobalTheory.BetaCutLimit

namespace GlobalTheory

open Filter Topology MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
private theorem exists_CCle_four_of_inCC_five {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ}
    {G : _root_.Formalism.FourierDecayAlt.B.Mat k r → E} (hG : _root_.Formalism.FourierDecayAlt.B.InCC A 5 G) : ∃ c, _root_.Formalism.FourierDecayAlt.B.CCle A 4 G c := by
  unfold _root_.Formalism.FourierDecayAlt.B.InCC _root_.Formalism.FourierDecayAlt.B.CCle at hG
  obtain ⟨c, h1, h2⟩ := hG
  exact ⟨c, _root_.Formalism.FourierDecayAlt.P.B5.ckOn_mono (by norm_num) h1, fun u v hu hv hl g hg => h2 u v hu hv (by omega) g hg⟩

open Filter Topology MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
private theorem measurableSet_Qset' (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) : MeasurableSet (_root_.Formalism.FourierDecayAlt.B.Qset Bs) :=
  measurableSet_lt measurable_const (_root_.Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _)

open Filter Topology MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
private theorem aestronglyMeasurable_Qset_indicator_hsVec (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    {G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp} (hG : ContinuousOn G (_root_.Formalism.FourierDecayAlt.B.GV k r)) :
    AEStronglyMeasurable ((_root_.Formalism.FourierDecayAlt.B.Qset Bs).indicator fun q => _root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs G (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))
      volume := by
  refine (aestronglyMeasurable_indicator_iff (measurableSet_Qset' Bs)).2 ?_
  have h := _root_.Formalism.FourierDecayAlt.P.B7.jc_aesm_J Bs hG (1, 1)
  simp only [_root_.Formalism.FourierDecayAlt.P.bessel_function_trivial_index k r Wp Wq Bs G] at h
  exact _root_.Formalism.FourierDecayAlt.P.JCTx2.hsVec_cont'.comp_aestronglyMeasurable h

open Filter Topology MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
private theorem mem_Qset_iff_bcWeight_pos (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (q : (Fin r → ℂ) × ℂ) :
    q ∈ _root_.Formalism.FourierDecayAlt.B.Qset Bs ↔ 0 < _root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q := Iff.rfl

open Filter Topology MeasureTheory in
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in
private theorem aestronglyMeasurable_weighted_pairing_lemma_2 (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    {G G' : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp} (hG : ContinuousOn G (_root_.Formalism.FourierDecayAlt.B.GV k r))
    (hG' : ContinuousOn G' (_root_.Formalism.FourierDecayAlt.B.GV k r)) :
    AEStronglyMeasurable (fun q : (Fin r → ℂ) × ℂ =>
      (_root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q : ℂ) *
        inner ℂ (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs G (_root_.Formalism.FourierDecayAlt.B.gq Bs q))) (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs G' (_root_.Formalism.FourierDecayAlt.B.gq Bs q))))
      volume := by
  have h := (Complex.continuous_ofReal.measurable.comp (_root_.Formalism.FourierDecayAlt.P.B7.measurable_bcWeight (k := k) (r := r)
    (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z'))).aestronglyMeasurable.mul
    ((aestronglyMeasurable_Qset_indicator_hsVec Bs hG).inner (aestronglyMeasurable_Qset_indicator_hsVec Bs hG'))
  refine h.congr (Eventually.of_forall fun q => ?_)
  by_cases hq : q ∈ _root_.Formalism.FourierDecayAlt.B.Qset Bs
  · simp only [Pi.mul_apply, Function.comp_apply, Set.indicator_of_mem hq]
  · have hw : _root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q = 0 :=
      le_antisymm (not_lt.1 ((mem_Qset_iff_bcWeight_pos Bs q).not.1 hq)) (_root_.Formalism.FourierDecayAlt.P.JCTx2.bcWeight_nonneg' _ _ q)
    simp only [Pi.mul_apply, Function.comp_apply, hw, Complex.ofReal_zero, zero_mul]

open Filter Topology MeasureTheory in

theorem _root_.GlobalTheory.beta_cutF_tendsto : _root_.GlobalTheory.HCXi.BesselXiIntegrable → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (χ : ℝ → ℝ) (A : ℝ) (X F : _root_.Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)), _root_.Formalism.FourierDecayAlt.C6.IsCut0 χ → _root_.Formalism.FourierDecayAlt.B.AB k r ≤ A → _root_.Formalism.FourierDecayAlt.B.InCC A 5 X → _root_.Formalism.FourierDecayAlt.B.InCC A 5 F → Tendsto (fun ε : ℝ => _root_.Formalism.FourierDecayAlt.B.beta Bs X (_root_.Formalism.FourierDecayAlt.D.cutF Bs χ F ε)) (𝓝[>] 0) (𝓝 (_root_.Formalism.FourierDecayAlt.B.beta Bs X F)) := by
  intro hHC k r Wp Wq _ _ _ _ _ _ Bs χ A X F hχ hA hX hF
  have hint := _root_.GlobalTheory.betaIntegrand_integrable_of_xiExists
    (_root_.GlobalTheory.HCXi.xiExists_of_besselXiIntegrable hHC) k r Wp Wq Bs A X F hA hX hF
  obtain ⟨M, -, hM⟩ := _root_.Formalism.FourierDecayAlt.P.JCTx2.cut_bound hχ
  have hχ' := hχ
  unfold _root_.Formalism.FourierDecayAlt.C6.IsCut0 at hχ'
  obtain ⟨hχc, -, hχ1⟩ := hχ'
  obtain ⟨cF, hcF⟩ := exists_CCle_four_of_inCC_five hF
  obtain ⟨cX, hcX⟩ := exists_CCle_four_of_inCC_five hX
  have hFc : ContinuousOn F (_root_.Formalism.FourierDecayAlt.B.GV k r) := _root_.Formalism.FourierDecayAlt.P.B7.jc_cont (A := A) (by unfold _root_.Formalism.FourierDecayAlt.B.InCC; exact ⟨cF, hcF⟩)
  have hXc : ContinuousOn X (_root_.Formalism.FourierDecayAlt.B.GV k r) := _root_.Formalism.FourierDecayAlt.P.B7.jc_cont (A := A) (by unfold _root_.Formalism.FourierDecayAlt.B.InCC; exact ⟨cX, hcX⟩)
  have hcut : ∀ ε q, (_root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q : ℂ) *
      inner ℂ (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs (_root_.Formalism.FourierDecayAlt.D.cutF Bs χ F ε) (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))
        (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs X (_root_.Formalism.FourierDecayAlt.B.gq Bs q))) =
      (χ (_root_.Formalism.QuantumDeterminants.Gf k r Bs.z Bs.z' (_root_.Formalism.FourierDecayAlt.B.gq Bs q) / ε) : ℂ) *
        ((_root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q : ℂ) *
          inner ℂ (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs F (_root_.Formalism.FourierDecayAlt.B.gq Bs q))) (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs X (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))) := by
    intro ε q
    rw [_root_.Formalism.FourierDecayAlt.P.JCTx2.JF_cutF, _root_.Formalism.FourierDecayAlt.P.JCTx2.hsVec_smul', inner_smul_left, Complex.conj_ofReal]
    ring
  refine tendsto_integral_filter_of_dominated_convergence
    (F := fun ε q => (_root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q : ℂ) *
      inner ℂ (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs (_root_.Formalism.FourierDecayAlt.D.cutF Bs χ F ε) (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))
        (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs X (_root_.Formalism.FourierDecayAlt.B.gq Bs q))))
    (fun q => M * ‖(_root_.Formalism.QuantumDeterminants.bcWeight k r (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z) (_root_.Formalism.QuantumDeterminants.Tz k r Bs.z') q : ℂ) *
      inner ℂ (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs F (_root_.Formalism.FourierDecayAlt.B.gq Bs q))) (_root_.Formalism.FourierDecayAlt.B.hsVec (_root_.Formalism.FourierDecayAlt.B.JF Bs X (_root_.Formalism.FourierDecayAlt.B.gq Bs q)))‖)
    (Eventually.of_forall fun ε => ?_) (Eventually.of_forall fun ε => Eventually.of_forall fun q => ?_)
    (hint.norm.const_mul M) ?_
  · refine aestronglyMeasurable_weighted_pairing_lemma_2 Bs ?_ hXc
    have hcont : ContinuousOn (fun g => ((χ (_root_.Formalism.QuantumDeterminants.Gf k r Bs.z Bs.z' g / ε) : ℝ) : ℂ) • F g)
        (_root_.Formalism.FourierDecayAlt.B.GV k r) :=
      ((Complex.continuous_ofReal.comp (hχc.continuous.comp
        ((_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.Gf_cont Bs.z Bs.z').div_const ε))).continuousOn).smul hFc
    exact hcont
  · rw [hcut, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
  · filter_upwards [_root_.Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_or_weight_zero Bs] with q hq
    simp_rw [hcut]
    rcases hq with hq | hq
    · have hG : 0 < _root_.Formalism.QuantumDeterminants.Gf k r Bs.z Bs.z' (_root_.Formalism.FourierDecayAlt.B.gq Bs q) := (_root_.Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom Bs (by exact hq)).2.2
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioc_mem_nhdsGT hG] with ε hε
      rw [hχ1 _ ((one_le_div hε.1).2 hε.2), Complex.ofReal_one, one_mul]
      rfl
    · simp only [hq, Complex.ofReal_zero, zero_mul, mul_zero]
      exact tendsto_const_nhds

end GlobalTheory
end
end

section
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem beta_fold_cut_eq_beta_fold_of_cut : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (χ : ℝ → ℝ) (δ ε ε₁ : ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), C6.IsCut0 χ → (∀ x, x < δ → χ x = 0) → 0 < ε → 0 < ε₁ → ε₁ < δ * ε → B.CkOn ⊤ (B.GV P.k P.r) F → B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV P.k P.r (a.2 : ℂ) G) ((D.cutF p.T.base χ F ε₁)) w) (D.cutF p.T.base χ F ε) = B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV P.k P.r (a.2 : ℂ) G) (F) w) (D.cutF p.T.base χ F ε) := by
  intro Wp Wq _ _ _ _ _ _ P p s w χ δ ε ε₁ F hχ hδ hε hε₁ hlt hF
  unfold B.beta betaBig
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  by_cases hq : bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q = 0
  · simp only [hq, Complex.ofReal_zero, zero_mul]
  obtain ⟨hgG, -⟩ := Formalism.FourierDecayAlt.P.CutBP.bigCell_pos p q hq
  by_cases hG : Gf P.k P.r p.T.base.z p.T.base.z' (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) < δ * ε
  · have h0 : B.JF p.T.base (D.cutF p.T.base χ F ε) (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) = 0 := by
      rw [Formalism.FourierDecayAlt.P.CutBP.jf_congr_level p.T.base (Y := fun _ => 0) hgG (fun x _ hGx => by
        unfold D.cutF
        rw [hGx, hδ _ ((div_lt_iff₀ hε).2 hG)]
        simp)]
      unfold B.JF besselJ
      simp
    have h1 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
      unfold B.hsVec
      ext i
      simp
    simp only [h0, h1, inner_zero_left]
  · have hge : ε₁ < Gf P.k P.r p.T.base.z p.T.base.z' (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) :=
      lt_of_lt_of_le hlt (not_lt.1 hG)
    have hU : IsOpen {x : B.Mat P.k P.r | ε₁ < Gf P.k P.r p.T.base.z p.T.base.z' x} :=
      isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf p.T.base.z p.T.base.z').continuous
    have he : ∀ x ∈ {x : B.Mat P.k P.r | ε₁ < Gf P.k P.r p.T.base.z p.T.base.z' x} ∩ B.GV P.k P.r,
        D.cutF p.T.base χ F ε₁ x = F x := by
      intro x hx
      unfold D.cutF
      rw [hχ.2.2 _ ((one_le_div hε₁).2 (le_of_lt hx.1))]
      simp
    have hcut := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hF ε₁
    have hlev : ∀ x ∈ B.GV P.k P.r, Gf P.k P.r p.T.base.z p.T.base.z' x =
        Gf P.k P.r p.T.base.z p.T.base.z' (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) →
        x ∈ {x : B.Mat P.k P.r | ε₁ < Gf P.k P.r p.T.base.z p.T.base.z' x} ∩ B.GV P.k P.r :=
      fun x hx hGx => ⟨by show ε₁ < _; rw [hGx]; exact hge, hx⟩
    have key := Formalism.FourierDecayAlt.P.CutBP.jf_congr_level p.T.base hgG (fun x hx hGx =>
      Formalism.FourierDecayAlt.P.CutBP.fold_congr_open s hU hcut hF he w x (hlev x hx hGx))
    exact congrArg (fun A => (bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF p.T.base (D.cutF p.T.base χ F ε) (bigCell P.k P.r q.1 (p.T.base.μsec q.2))))
        (B.hsVec A)) key

end GlobalTheory
end

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelZeroPairing_cutoff_locality : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (χ : ℝ → ℝ) (δ ε ε₁ : ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), C6.IsCut0 χ → (∀ x, x < δ → χ x = 0) → 0 < ε → 0 < ε₁ → ε₁ < δ * ε → B.CkOn ⊤ (B.GV P.k P.r) F → B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV P.k P.r (a.2 : ℂ) G) ((D.cutF p.T.base χ F ε₁)) w) (D.cutF p.T.base χ F ε) = B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV P.k P.r (a.2 : ℂ) G) (F) w) (D.cutF p.T.base χ F ε) := by
  atlas_forward_decl GlobalTheory.beta_fold_cut_eq_beta_fold_of_cut
end

section
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

theorem threshold_le_cut (k r N : ℕ) :
    B.AB k r ≤ 3 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) := by
  unfold B.AB
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set D : ℝ := 2 * (r : ℝ) + k + 1 with hD
  have hD1 : 1 ≤ D := by rw [hD]; linarith
  have h1 : ((k : ℝ) + r) * ((r : ℝ) + 1) ≤ D * D :=
    mul_le_mul (by rw [hD]; linarith) (by rw [hD]; linarith) (by linarith) (by linarith)
  have h2 : D * D ≤ D ^ 3 := by nlinarith [mul_nonneg (mul_self_nonneg D) (sub_nonneg.2 hD1)]
  have h3 : 1 ≤ D ^ 3 := one_le_pow₀ hD1
  have h4 : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 4 := one_le_pow₀ (by linarith)
  have h5 : 0 ≤ (N : ℝ) * D ^ 2 := by positivity
  have h6 : (N : ℝ) * D ^ 2 + D ^ 3 ≤ ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * D ^ 2 + D ^ 3) :=
    le_mul_of_one_le_left (by linarith) h4
  nlinarith

theorem integral_topDensity_eq_levelZero : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ((∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c)) volume) ∧ ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ c : Fin (P.r + 1) → ℂ, ‖TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c)‖ ≤ h c) → ∫ c : Fin (P.r + 1) → ℂ, TBB.Ew p (fun _ => 1) f (P.r + 1) w (TBB.bigPt P.r c) = (p.RR f 0 w [] []).re := by
  intro hXi hA Cb
  obtain ⟨Cc, hCc⟩ := GlobalTheory.T.levelZeroPairing_eq_integral_inner_topVectors hA Cb
  refine ⟨max Cc 3, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ A N w hDD hχ hf hCC hthr hw hN hdom
  obtain ⟨-, h, hint, hb⟩ := hdom
  have hX : (0 : ℝ) ≤ ((P.r : ℝ) + 1) ^ 4 *
      ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) := by positivity
  have hthr1 : Cc * ((P.r : ℝ) + 1) ^ 4 *
      ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A := by
    refine le_trans ?_ hthr
    rw [mul_assoc Cc, mul_assoc (max Cc 3)]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX
  have hAB : B.AB P.k P.r ≤ A := by
    refine le_trans (threshold_le_cut P.k P.r N) (le_trans ?_ hthr)
    rw [mul_assoc (3 : ℝ), mul_assoc (max Cc 3)]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hX
  have hpol := hCc Wp Wq P p f χ A N w hDD hχ hf hCC hthr1 hw hN
  obtain ⟨δ, hδ, hδχ⟩ := hχ.2.1
  have hcut := fun (ε : ℝ) (hε : 0 < ε) (c : Fin (P.r + 1) → ℂ) =>
    GlobalTheory.T.topVector_cutoff_eq_and_vanish Wp Wq P p Cb χ δ ε f w c hDD hw hχ hδχ hε hf
  set X := List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) f w with hXdef
  have hXCC : B.InCC A 5 X := by
    obtain ⟨K, -, hK⟩ := GlobalTheory.capelli_fold_ccle P.k P.r Wp Wq (M.sgn P p.l0) w 5
    obtain ⟨c, hc⟩ := hCC (5 + List.length w * (2 * P.r + P.k + 1))
    exact ⟨K * c, hK A c f hf hc⟩
  have hlimL := GlobalTheory.beta_cutF_tendsto hXi P.k P.r Wp Wq p.T.base χ A X f hχ hAB hXCC (hCC 5)
  have hlimR := (GlobalTheory.memLp_and_tendsto_integral_inner_of_eventually_eq (Fin (P.r + 1) → ℂ) volume _
    (fun ε => tv p (D.cutF p.T.base χ f ε) w) (tv p f w) h hint
    (Eventually.of_forall fun ε => GlobalTheory.T.aestronglyMeasurable_topVector_smoothCoefficient Wp Wq P p Cb _ w hDD hw
      (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hf ε))
    (by
      filter_upwards [hb] with ε hε
      filter_upwards [hε] with c hc
      rw [Ew_eq_norm_tv_sq] at hc
      exact le_trans (le_abs_self _) hc)
    (Eventually.of_forall fun c => by
      by_cases hG : 0 < TBB.Gp p (TBB.bigPt P.r c)
      · filter_upwards [Ioo_mem_nhdsGT hG] with ε hε
        exact (hcut ε hε.1 c).1 hε.2
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        have hε' : 0 < ε := hε
        have hG' := not_lt.1 hG
        rw [(hcut ε hε' c).2.2 hG', (hcut ε hε' c).2.1 (lt_of_le_of_lt hG' (mul_pos hδ hε'))])).2
  have heq : (fun ε : ℝ => B.beta p.T.base X (D.cutF p.T.base χ f ε)) =ᶠ[𝓝[>] 0]
      fun ε : ℝ => ∫ c, inner ℂ (tv p (D.cutF p.T.base χ f ε) w c) (tv p f w c) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    have hδε : 0 < δ * ε := mul_pos hδ hε'
    have h1 : 0 < δ * ε / 2 := by linarith
    have h2 : δ * ε / 2 < δ * ε := by linarith
    rw [hXdef, ← GlobalTheory.T.levelZeroPairing_cutoff_locality Wp Wq P p (M.sgn P p.l0) w χ δ ε (δ * ε / 2) f hχ hδχ hε' h1 h2 hf,
      hpol _ _ h1 hε']
    refine integral_congr_ae (Eventually.of_forall fun c => ?_)
    by_cases hG : TBB.Gp p (TBB.bigPt P.r c) < δ * ε
    · simp only [(hcut ε hε' c).2.1 hG, inner_zero_left]
    · simp only [(hcut _ h1 c).1 (lt_of_lt_of_le h2 (not_lt.1 hG))]
  have hfin := tendsto_nhds_unique (hlimL.congr' heq) hlimR
  have hRR : p.RR f 0 w [] [] = B.beta p.T.base X f := by
    unfold KB.Pl.RR
    rw [Formalism.FourierDecayAlt.P.level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hf (Formalism.FourierDecayAlt.P.CutBP.good_positioned_of_cut hw)]
    rfl
  rw [hRR, hfin, Complex.ofReal_re]
  exact integral_congr_ae (Eventually.of_forall fun c => Ew_eq_norm_tv_sq Wp Wq P p f w c)

end GlobalTheory.TopVec
end

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigCell_integral_topDensity_eq_levelZero : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ((∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c)) volume) ∧ ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ c : Fin (P.r + 1) → ℂ, ‖TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c)‖ ≤ h c) → ∫ c : Fin (P.r + 1) → ℂ, TBB.Ew p (fun _ => 1) f (P.r + 1) w (TBB.bigPt P.r c) = (p.RR f 0 w [] []).re := by
  atlas_forward_decl GlobalTheory.TopVec.integral_topDensity_eq_levelZero
end

section
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

theorem levelZero_cut_eq_integral_Ew : P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ∀ ε : ℝ, 0 < ε → (p.RR (D.cutF p.T.base χ f ε) 0 w [] []).re = ∫ c : Fin (P.r + 1) → ℂ, TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c) := by
  intro hA Cb
  obtain ⟨Cc, hCc⟩ := GlobalTheory.T.levelZeroPairing_eq_integral_inner_topVectors hA Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ A N w hD hχ hf hdec hAle hw hN ε hε
  have h := hCc Wp Wq P p f χ A N w hD hχ hf hdec hAle hw hN ε ε hε hε
  have hF := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hf ε
  have h0 : p.RR (D.cutF p.T.base χ f ε) 0 w [] [] =
      ∫ c, inner ℂ (tv p (D.cutF p.T.base χ f ε) w c) (tv p (D.cutF p.T.base χ f ε) w c) := by
    unfold KB.Pl.RR
    rw [Formalism.FourierDecayAlt.P.level_zero_holds _ _ _ _ _ _ _ _ _ _ _ hF (Formalism.FourierDecayAlt.P.CutBP.good_positioned_of_cut hw)]
    exact h
  have h1 : ∀ c, inner ℂ (tv p (D.cutF p.T.base χ f ε) w c) (tv p (D.cutF p.T.base χ f ε) w c) =
      ((‖tv p (D.cutF p.T.base χ f ε) w c‖ ^ 2 : ℝ) : ℂ) := fun c => by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  rw [h0]
  simp only [h1, Ew_eq_norm_tv_sq]
  rw [integral_complex_ofReal, Complex.ofReal_re]

end GlobalTheory.TopVec
end

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelZero_cutoff_eq_bigCell_integral : P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ∀ ε : ℝ, 0 < ε → (p.RR (D.cutF p.T.base χ f ε) 0 w [] []).re = ∫ c : Fin (P.r + 1) → ℂ, TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c) := by
  atlas_forward_decl GlobalTheory.TopVec.levelZero_cut_eq_integral_Ew
end

section
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

theorem Ew_cutF_eventually_eq : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → KB.CutWord P p.l0 w → ∀ᵐ c : Fin (P.r + 1) → ℂ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c) = TBB.Ew p (fun _ => 1) f (P.r + 1) w (TBB.bigPt P.r c) := by
  intro Wp Wq _ _ _ _ _ _ P p Cb f χ w hΘ hχ hf hw
  obtain ⟨δ, hδ, hδχ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x, x < δ → χ x = 0 := by
    have h := hχ
    unfold C6.IsCut0 at h
    tauto
  refine Filter.Eventually.of_forall fun c => ?_
  simp only [Ew_eq_norm_tv_sq]
  by_cases hG : 0 < TBB.Gp p (TBB.bigPt P.r c)
  · filter_upwards [Ioo_mem_nhdsGT hG] with ε hε
    rw [(GlobalTheory.T.topVector_cutoff_eq_and_vanish Wp Wq P p Cb χ δ ε f w c hΘ hw hχ hδχ hε.1 hf).1 hε.2]
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    have h := GlobalTheory.T.topVector_cutoff_eq_and_vanish Wp Wq P p Cb χ δ ε f w c hΘ hw hχ hδχ hε' hf
    rw [h.2.1 ((not_lt.1 hG).trans_lt (mul_pos hδ hε')), h.2.2 (not_lt.1 hG)]

end GlobalTheory.TopVec
end

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDensity_cutoff_eventually_eq_smoothCoefficient : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → KB.CutWord P p.l0 w → ∀ᵐ c : Fin (P.r + 1) → ℂ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c) = TBB.Ew p (fun _ => 1) f (P.r + 1) w (TBB.bigPt P.r c) := by
  atlas_forward_decl GlobalTheory.TopVec.Ew_cutF_eventually_eq
end

section
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem levelZeroForm_cutoff_tendsto_of_domination : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (Y : Finset ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → (∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ((∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c)) volume) ∧ ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ c : Fin (P.r + 1) → ℂ, ‖TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c)‖ ≤ h c)) → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → Tendsto (fun ε : ℝ => (p.RR (D.cutF p.T.base χ f ε) 0 w [] []).re) (𝓝[>] 0) (𝓝 (p.RR f 0 w [] []).re) := by
  intro hX hP Cb
  obtain ⟨C1, h1⟩ := GlobalTheory.T.levelZero_cutoff_eq_bigCell_integral hP Cb
  obtain ⟨C2, h2⟩ := GlobalTheory.T.bigCell_integral_topDensity_eq_levelZero hX hP Cb
  refine ⟨max C1 C2, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ A N Y hD hχ hf hA hC hdom w hw hN
  have hpos : (0 : ℝ) ≤ ((P.r : ℝ) + 1) ^ 4 := by positivity
  have hpos' : (0 : ℝ) ≤ (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3 := by
    positivity
  have hC1 := le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left C1 C2) hpos) hpos') hC
  have hC2 := le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right C1 C2) hpos) hpos') hC
  have hd := hdom w hw hN
  have hid := h2 Wp Wq P p f χ A N w hD hχ hf hA hC2 hw.1 hN hd
  have hform := h1 Wp Wq P p f χ A N w hD hχ hf hA hC1 hw.1 hN
  have hptw := GlobalTheory.T.topDensity_cutoff_eventually_eq_smoothCoefficient Wp Wq P p Cb f χ w hD hχ hf hw.1
  obtain ⟨hm, h, hi, hb⟩ := hd
  have key := tendsto_integral_filter_of_dominated_convergence h hm hb hi
    (hptw.mono fun c hc => tendsto_const_nhds.congr' (hc.mono fun _ e => e.symm))
  rw [hid] at key
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hform ε hε).symm

end GlobalTheory
end

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelZeroForm_cutoff_tendsto_of_density_domination : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (Y : Finset ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → (∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ((∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c)) volume) ∧ ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ c : Fin (P.r + 1) → ℂ, ‖TBB.Ew p (fun _ => 1) (D.cutF p.T.base χ f ε) (P.r + 1) w (TBB.bigPt P.r c)‖ ≤ h c)) → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → Tendsto (fun ε : ℝ => (p.RR (D.cutF p.T.base χ f ε) 0 w [] []).re) (𝓝[>] 0) (𝓝 (p.RR f 0 w [] []).re) := by
  atlas_forward_decl GlobalTheory.levelZeroForm_cutoff_tendsto_of_domination
end

section
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Filter Topology MeasureTheory

namespace GlobalTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem limEvT_pow_mul_of_topDomination : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → NFTopDomAll → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ), NFHyp Cb Cc p f A₀ p₀ χ N → LimEvT p χ (Formalism.FourierDecayAlt.P.TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N := by
  intro hX hP hDom Cb
  obtain ⟨C1, h1⟩ := GlobalTheory.T.levelZeroForm_cutoff_tendsto_of_density_domination hX hP Cb
  obtain ⟨C2, h2⟩ := hDom Cb
  refine ⟨max C1 C2, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hH
  have hpos : (0 : ℝ) ≤ ((P.r : ℝ) + 1) ^ 4 := by positivity
  have hpos' : (0 : ℝ) ≤ (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3 := by
    positivity
  have hC1 := le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left C1 C2) hpos) hpos') a5
  have hC2 := le_trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right C1 C2) hpos) hpos') a5
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) :=
    fun g₀ _ => ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial,
      contDiffOn_const, fun _ _ _ => rfl⟩
  exact h1 Wp Wq P p _ χ _ N Y a2 a1 (ckOn_fpm p p₀ a3 hid) (inCC_fpm_id p p₀ a4) hC1
    (fun w hw hN => h2 Wp Wq P p f A₀ p₀ χ Y N ⟨a1, a2, a3, a4, hC2, a6⟩ w hw hN)

end GlobalTheory
end

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_levelZero_form_cutoff_pow_mul_of_domination : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → NFTopDomAll → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ), NFHyp Cb Cc p f A₀ p₀ χ N → LimEvT p χ (Formalism.FourierDecayAlt.P.TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N := by
  atlas_forward_decl GlobalTheory.limEvT_pow_mul_of_topDomination
end

section
section
open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants

namespace GlobalTheory.EigenThreePlaces

theorem exists_isCut0 : ∃ χ : ℝ → ℝ, C6.IsCut0 χ := by
  refine ⟨fun x => Real.smoothTransition (2 * x - 1), ?_, ⟨1 / 2, by norm_num, fun x hx => ?_⟩, fun x hx => ?_⟩
  · exact Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  · exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · exact Real.smoothTransition.one_of_one_le (by linarith)

theorem decay_split (c c' x : ℝ) (k r N : ℕ)
    (h : max 3 (max c c') * ((r : ℝ) + 1) ^ 4 *
      ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ x) :
    c * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ x ∧
      c' * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ x ∧
      B.AB k r ≤ x := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn
  have hn1 : 1 ≤ n := by linarith
  have hX : 0 ≤ (N : ℝ) * n ^ 2 + n ^ 3 := by positivity
  have hR : 0 ≤ ((r : ℝ) + 1) ^ 4 := by positivity
  refine ⟨le_trans ?_ h, le_trans ?_ h, le_trans ?_ h⟩
  · gcongr
    exact (le_max_left _ _).trans (le_max_right _ _)
  · gcongr
    exact (le_max_right _ _).trans (le_max_right _ _)
  · have h1 : (r : ℝ) + 1 ≤ ((r : ℝ) + 1) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
    have h2 : n ≤ n ^ 3 := le_self_pow₀ hn1 (by norm_num)
    have h3 : n ≤ (N : ℝ) * n ^ 2 + n ^ 3 := by
      have : 0 ≤ (N : ℝ) * n ^ 2 := by positivity
      linarith
    calc B.AB k r ≤ 3 * ((r : ℝ) + 1) * n := by
          unfold B.AB
          rw [hn]
          nlinarith [mul_nonneg hr hk, mul_nonneg hr hr]
      _ ≤ _ := by
          gcongr
          exact le_max_left _ _

theorem main : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → NFTopDomAll → ∀ Cb C₃ CΛ C₀ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp) (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)) (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq)) (b Λ A₀ : ℝ) (n₀ p₀ d : ℕ) (nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ), 3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → pp.T.base.z = p.T.base.z → pp.T.base.z' = p.T.base.z' → pm.T.base.z = p.T.base.z → pm.T.base.z' = p.T.base.z' → 3 ≤ K → (P.r + 1) * K ≤ N → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) → KB.InDDplus2 (shP P up up') pp.l0 pp.T.base Cb pp.Θ → KB.InDDplus2 (shP P um um') pm.l0 pm.T.base Cb pm.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → CutBPEq.PolyOp d Ap → CutBPEq.PolyOp d Am → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d → AmapsSh p pp pm f Ap Am ApPt AmPt b n₀ → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBBx5.WaveGrid pp nnp Yp Λ K N → TBBx5.LiftGrid pp nnp Yp Λ K N → TBBx5.WaveGrid pm nnm Ym Λ K N → TBBx5.LiftGrid pm nnm Ym Λ K N → N ≤ 2 * p₀ → ∀ (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs : ℝ), (∀ y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (y : ℂ) f g = ((∏ s, (y + lam' s) : ℝ) : ℂ) • f g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + d : ℕ) : ℝ) ≤ cs - 1) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nnp y) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nnm y) → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  intro hX hP hDom Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨C₄, Cc, h⟩ := GlobalTheory.T.jetBound_equalTypes_threePlaces_of_xiIntegrable hX hP Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨Cn, hn⟩ := GlobalTheory.T.tendsto_levelZero_form_cutoff_pow_mul_of_domination hX hP hDom Cb
  obtain ⟨-, L2⟩ := GlobalTheory.T.levelZeroEnergyBound_decayingCasimirEigenfunction hX
  obtain ⟨χ, hχ⟩ := exists_isCut0
  refine ⟨C₄, max 3 (max Cc Cn), ?_⟩
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm f Ap Am ApPt AmPt b Λ A₀ n₀ p₀ d
    nnp nnm Yp Ym K N hb hΛ hΛb hn₀ hp₀ hzp hzp' hzm hzm' hK hKN hnnp hnnm hDDp hDDm hf hfA hAp hAm
    hth hAms hreg hWGp hLGp hWGm hLGm hN2 lam lam' cs he hs hc hnp hnm
  obtain ⟨hth1, hth4, hth3⟩ := decay_split Cc Cn _ P.k P.r N hth
  have hth4' : Cn * ((P.r : ℝ) + 1) ^ 4 *
      ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
      (A₀ - d) - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := by linarith
  have hA3 : B.AB P.k P.r ≤ A₀ - (((2 * P.r + 2) * p₀ + d : ℕ) : ℝ) := by
    rw [Nat.cast_add]; linarith
  have hLp : LimEvT pp χ (fpmSh pp f Ap p₀) Yp N := by
    have e := fpmSh_eq_fpm pp f Ap p₀
    have k := hn Wp Wqp (shP P up up') pp (fun g => (f g).comp (Ap g)) (A₀ - d) p₀ χ Yp N
      ⟨hχ, hDDp, ckOn_compSh hf (ckOn_of_polyOp hAp), inCC_compSh pp hfA hAp, hth4', hN2⟩
    exact Eq.mpr (congrArg (fun F => LimEvT pp χ F Yp N) e) k
  have hLm : LimEvT pm χ (fpmSh pm f Am p₀) Ym N := by
    have e := fpmSh_eq_fpm pm f Am p₀
    have k := hn Wp Wqm (shP P um um') pm (fun g => (f g).comp (Am g)) (A₀ - d) p₀ χ Ym N
      ⟨hχ, hDDm, ckOn_compSh hf (ckOn_of_polyOp hAm), inCC_compSh pm hfA hAm, hth4', hN2⟩
    exact Eq.mpr (congrArg (fun F => LimEvT pm χ F Ym N) e) k
  have hI5p : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
      TBB.BlockGrowthBound pp nnp (apx (D.cutF pp.T.base χ (fpmSh pp f Ap p₀) ε) n) Yp K N := fun ε hε n =>
    GlobalTheory.T.latticeSum_of_compactCoefficient_positivity hP Wp Wqp (shP P up up') pp nnp _ Yp K N Cb hDDp
      (cptCoef_apx (shP P up up') pp.T.base hχ (ckOn_fpmSh pp p₀ hf (ckOn_of_polyOp hAp)) hε n) hnnp
  have hI5m : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
      TBB.BlockGrowthBound pm nnm (apx (D.cutF pm.T.base χ (fpmSh pm f Am p₀) ε) n) Ym K N := fun ε hε n =>
    GlobalTheory.T.latticeSum_of_compactCoefficient_positivity hP Wp Wqm (shP P um um') pm nnm _ Ym K N Cb hDDm
      (cptCoef_apx (shP P um um') pm.T.base hχ (ckOn_fpmSh pm p₀ hf (ckOn_of_polyOp hAm)) hε n) hnnm
  exact h P Wp Wq Wqp Wqm up up' um um' p pp pm f Ap Am ApPt AmPt b Λ A₀ n₀ p₀ d
    χ nnp nnm Yp Ym K N hb hΛ hΛb hn₀ hp₀ hzp hzp' hzm hzm' hK hKN hχ hnnp hnnm hDDp hDDm hf hfA hAp hAm
    hth1 hAms hreg hWGp hLGp hWGm hLGm hI5p hI5m hLp hLm
    (L2 Wp Wq Wqp P up up' pp lam lam' cs A₀ p₀ d nnp f Ap Yp N hAp hf hfA he hs hc hA3 hnp)
    (L2 Wp Wq Wqm P um um' pm lam lam' cs A₀ p₀ d nnm f Am Ym N hAm hf hfA he hs hc hA3 hnm)

end GlobalTheory.EigenThreePlaces
end

open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_eigenfunction_bound_three_places : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → NFTopDomAll → ∀ Cb C₃ CΛ C₀ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp] [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm] (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp) (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)) (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq)) (b Λ A₀ : ℝ) (n₀ p₀ d : ℕ) (nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ), 3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → pp.T.base.z = p.T.base.z → pp.T.base.z' = p.T.base.z' → pm.T.base.z = p.T.base.z → pm.T.base.z' = p.T.base.z' → 3 ≤ K → (P.r + 1) * K ≤ N → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) → KB.InDDplus2 (shP P up up') pp.l0 pp.T.base Cb pp.Θ → KB.InDDplus2 (shP P um um') pm.l0 pm.T.base Cb pm.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → CutBPEq.PolyOp d Ap → CutBPEq.PolyOp d Am → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d → AmapsSh p pp pm f Ap Am ApPt AmPt b n₀ → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBBx5.WaveGrid pp nnp Yp Λ K N → TBBx5.LiftGrid pp nnp Yp Λ K N → TBBx5.WaveGrid pm nnm Ym Λ K N → TBBx5.LiftGrid pm nnm Ym Λ K N → N ≤ 2 * p₀ → ∀ (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs : ℝ), (∀ y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (y : ℂ) f g = ((∏ s, (y + lam' s) : ℝ) : ℂ) • f g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + d : ℕ) : ℝ) ≤ cs - 1) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nnp y) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nnm y) → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  atlas_forward_decl GlobalTheory.EigenThreePlaces.main
end
