module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GamAtOfLawsCore
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaNetDimensionAndPointCountBound
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProofStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmFamilyFunctionalsDetectLowCoefficients
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExtendEmbedding
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPolynomialBoundRunConstantsDegreeFourStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.QuotientBoundOfKillDetectConstantRoom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

set_option autoImplicit false

namespace GlobalTheory.RunJoin




theorem qAt_run : ∃ Cq : ℝ → ℝ → ℝ, ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → j < D.R.m → LatAt (recB h.toLawsCore) j ka → QAt large₂ (recB h.toLawsCore) j ka 7 H.CK 1 4 (Cq H.CA H.CK) 4 Tn (cc D large₂ C2 A2 7 wL) := by
  obtain ⟨C₀, hC₀, hroom⟩ := GlobalTheory.T.exists_polynomial_bound_runConstants_degree_four
  refine ⟨fun a b => 1 + 3 * C₀ a 7 b + 1041, ?_⟩
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hP hjm hL hCR hO hn hlast hsz hT hc hTc
  have h3 : 3 ≤ D.R.r := le_trans (by norm_num) hP.r8
  have hcc : Real.log (Ideal.absNorm D.host.ccK) ≤ large₂.sc.L := by
    obtain ⟨Q, -, -⟩ := hP.page
    exact Q.ccK_log
  obtain ⟨hZ, hR⟩ := hroom D large₂ j ka H.CA 7 H.CK Tn (cc D large₂ C2 A2 7 wL) hP.hyp.1 hcc hj hjm h3 hCR hsz hT hc hTc
  obtain ⟨-, -, -, -, -, -, -, -, hdim, -⟩ := GlobalTheory.RunJoin.net_at_run D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hP
  have hG := GlobalTheory.RunIn.gamAt_of_lawsCore D T.toCore h.toLawsCore
  have hK := GlobalTheory.T.arithmeticCMKnownTheorems_proof
  have hpp : 1041 * Zb D large₂ ^ 3 ≤ WeightFamilies.PPv D large₂ 1041 3 * ka.size := by
    have e : WeightFamilies.PPv D large₂ 1041 3 = 1041 * Zb D large₂ ^ 3 := by
      unfold WeightFamilies.PPv
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rfl
    rw [e]
    have hZ' : (1 : ℝ) ≤ Zb D large₂ := hZ
    exact le_mul_of_one_le_right (by positivity) ka.one_le_size
  have key := GlobalTheory.ArcCM.qat_of_kill_detect hK D T.toCore h.toLawsCore j ka 7 Tn
    (cc D large₂ C2 A2 7 wL) large₂ H.CK 1 4 (C₀ H.CA 7 H.CK) 4 1041 3
    hG hj hjm hL (GlobalTheory.ArcCM.killQ_of_gamAt hK D T.toCore h.toLawsCore j ka 7 Tn _ hG hj hjm)
    (GlobalTheory.ArcCM.detectQ_of_known hK D T.toCore h.toLawsCore j ka 7 Tn _ hG hj hjm h3 hT hc)
    hZ (hC₀ _ _ _) (by norm_num) hR
    (le_trans hdim hpp)
  have e4 : max (4 : ℝ) (max 4 3) = 4 := by norm_num
  rw [e4] at key
  exact key hCR hO hn hlast hsz hT hc hTc

end GlobalTheory.RunJoin
