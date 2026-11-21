import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaNetDimensionAndPointCountBoundStatement
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsBoundedByPowerOfAtLeastTwoInvD4ep0
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridgeAlt
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.InnerEuclideanEmbeddingEqAverage
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
import Formalism.LocalToGlobal.ProjectiveLattices.CombAlgOfCombBound
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Formalism.LocalToGlobal.ProjectiveLattices.AxHLAM
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmFamilyFunctionalsDetectLowCoefficientsStatement
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumSectionValueCoeffEqFourierJacobiStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TraceFormIndependence
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemFormsLowCoeffsVanishIffFourierJacobi
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TransvInOfHasPrinc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProofStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.QuotientBoundOfKillDetectConstantRoom

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM.Room

theorem assemble (K M P z s lc lL lr lR lo ld ln : ℝ) (hz : 1 ≤ z) (hP : z ≤ P) (hK : 1 ≤ K) (hM : 0 ≤ M)
    (hs : 1 ≤ s) (hc : lc ≤ K * z) (hL : lL ≤ M * P) (hr : lr ≤ K * z) (hR : lR ≤ z) (ho : lo ≤ K * z)
    (hd : ld ≤ K * z) (hn : ln ≤ M * P) :
    4 * Real.pi + (lc / 2 + lL + lr + lR) * s ≤ (17 + 2 * K + M) * P * s ∧
    ((1 + lo) / 2 + (1 / 2) * lL) * s ≤ (17 + 2 * K + M) * P * s ∧
    ld + ln ≤ (17 + 2 * K + M) * P := by
  have hKz : K * z ≤ K * P := mul_le_mul_of_nonneg_left hP (by linarith)
  have hKP : 0 ≤ K * P := by nlinarith
  have hMP : 0 ≤ M * P := mul_nonneg hM (by linarith)
  have hpi := Real.pi_le_four
  refine ⟨?_, ?_, ?_⟩
  · have h1 : lc / 2 + lL + lr + lR ≤ (1 + 2 * K + M) * P := by nlinarith
    have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ s)
    have h3 : 1 ≤ P * s := by nlinarith
    nlinarith
  · refine mul_le_mul_of_nonneg_right ?_ (by linarith)
    nlinarith
  · nlinarith

theorem log_le_self' {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ x := Real.log_le_self hx

end GlobalTheory.ArcCM.Room
end

section
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.SplitConst

theorem constants_bounded_sq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 g NA NC : ℕ) (c₁ w Z : ℝ), 3 ≤ r → 1 ≤ p0 → p0 ≤ r → 1 ≤ g → 1 ≤ NA → 1 ≤ NC → 0 < c₁ → 1 ≤ w → 1 ≤ Z → (fdeg E : ℝ) ≤ Z → (r : ℝ) ≤ Z → Real.log (dE E) ≤ Z → Real.log g ≤ Z → Real.log NA ≤ Z → Real.log NC ≤ Z → Real.log c₁ ≤ Z → Real.log w ≤ Z → Real.log (nQ E r g NA NC c₁ w) ≤ 200 * Z ^ 2 ∧ Real.log (LaQ E r p0 g NA NC c₁ w) ≤ 200 * Z ^ 2 := by
  intro E _ _ _ r p0 g NA NC c w Z hr hp hpr hg hNA hNC hc hw hZ hfZ hrZ hdZ hgZ hNAZ hNCZ hcZ hwZ
  have hZX : Z + 1 ≤ Real.exp Z := Real.add_one_le_exp Z
  set X := Real.exp Z with hXdef
  have hX : 2 ≤ X := by linarith
  have le_of_log : ∀ a : ℝ, 0 < a → Real.log a ≤ Z → a ≤ X := fun a ha h => (Real.log_le_iff_le_exp ha).1 h
  have hd : 1 ≤ dE E := by
    unfold dE
    have := NumberField.discr_ne_zero E
    have h2 : (1 : ℤ) ≤ |NumberField.discr E| := Int.one_le_abs this
    exact_mod_cast h2
  have hn : 2 ≤ Module.finrank ℚ E := by
    have h1 := Module.finrank_mul_finrank ℚ (NumberField.maximalRealSubfield E) E
    have h2 : Module.finrank (NumberField.maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
    have h3 : 0 < Module.finrank ℚ (NumberField.maximalRealSubfield E) := Module.finrank_pos
    rw [h2] at h1
    omega
  have hf : (1 : ℝ) ≤ fdeg E := by
    have : 1 ≤ fdeg E := by unfold fdeg; omega
    exact_mod_cast this
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hNA1 : (1 : ℝ) ≤ NA := by exact_mod_cast hNA
  have hNC1 : (1 : ℝ) ≤ NC := by exact_mod_cast hNC
  have hd' := le_of_log _ (by linarith) hdZ
  have hg' := le_of_log _ (by linarith) hgZ
  have hNA' := le_of_log _ (by linarith) hNAZ
  have hNC' := le_of_log _ (by linarith) hNCZ
  have hc' := le_of_log _ hc hcZ
  have hw' := le_of_log _ (by linarith) hwZ
  have hf' : (fdeg E : ℝ) ≤ X := by linarith
  have pe := isBoundedByPowerOfAtLeastTwo_inv_d4ep0 hX hg1 hd hf hNA1 hNC1 hc hw hg' hd' hf' hNA' hNC' hc' hw'
  have ph := rh_inv hX hc hw hc' hw'
  have pd := PB.base hX (by linarith) hd'
  have pf := PB.base hX (by linarith) hf'
  have pNA := PB.base hX (by linarith) hNA'
  have pNC := PB.base hX (by linarith) hNC'
  have pr : PB X 1 ((r - 2 : ℕ) : ℝ) := by
    refine PB.base hX (by positivity) ?_
    have : ((r - 2 : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.sub_le r 2
    linarith
  have prd : PB X 1 (rdE E) :=
    pd.of_le (Real.rpow_nonneg (by linarith) _) (rpow_le_self hd (by
      have : 1 ≤ Module.finrank ℚ E := by omega
      exact_mod_cast this))
  have p1 : PB X 0 1 := PB.const hX 0 (by norm_num) (by norm_num)
  have p2 : PB X 1 2 := PB.const hX 1 (by norm_num) (by norm_num)
  have p4 : PB X 2 4 := PB.const hX 2 (by norm_num) (by norm_num)
  have p40 : PB X 6 40 := PB.const hX 6 (by norm_num) (by norm_num)
  have p1000 : PB X 10 1000 := PB.const hX 10 (by norm_num) (by norm_num)
  set ep := flowEpsilonBound g (dE E) (fdeg E) NA NC c w
  set rh := d6rh c w
  have hZ2 : Z ≤ Z ^ 2 := by nlinarith
  constructor
  · have pm := (((pf.mul (((p2.mul pf).mul pr).pow 3)).mul pd).mul pNA).mul ((pNC.pow 2).mul prd |>.mul pe).sqrt
    have py := (p1000.mul pm).mul ph
    have hy : 1000 * frameIndexBound r (fdeg E) (dE E) (rdE E) NA NC ep / rh =
        1000 * ((fdeg E : ℝ) * (2 * (fdeg E : ℝ) * ((r - 2 : ℕ) : ℝ)) ^ 3 * dE E * NA * √((NC : ℝ) ^ 2 * rdE E * ep⁻¹)) * rh⁻¹ := by
      unfold frameIndexBound
      rw [div_eq_mul_inv, div_eq_mul_inv, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat]
    rw [← hy] at py
    have pn : PB X 100 (nQ E r g NA NC c w : ℝ) := by
      refine (((py.add p1).add p1).mono (by norm_num)).of_le (by positivity) ?_
      unfold nQ
      push_cast
      have := Nat.ceil_lt_add_one py.2.1
      linarith
    have := pn.log_le (by unfold nQ; positivity)
    push_cast at this
    nlinarith
  · have pmu := ((p4.mul ((pf.mul pr).pow 3)).mul pd).mul pe.sqrt
    have pb := ((p2.mul (((p4.mul pr.sqrt).mul pmu).mul (p40.mul ph))).mono (j := 100) (by norm_num)).pow (2 * p0 - 1)
    have hy : d6La r p0 (fdeg E) (dE E) ep rh =
        (2 * (4 * √((r - 2 : ℕ) : ℝ) * (4 * ((fdeg E : ℝ) * ((r - 2 : ℕ) : ℝ)) ^ 3 * dE E * √(ep⁻¹)) * (40 * rh⁻¹))) ^
          (2 * p0 - 1) := by
      unfold d6La ReciprocityTheory.MultiplicativeHeights.approxR d5mu
      rw [div_eq_mul_inv _ (rh / 40), inv_div, div_eq_mul_inv 40, div_eq_mul_inv, ← Real.sqrt_inv]
    rw [← hy] at pb
    have pL : PB X (100 * (2 * p0 - 1)) (LaQ E r p0 g NA NC c w) := by
      unfold LaQ
      rcases max_choice (1 : ℝ) _ with h | h <;> rw [h]
      · exact p1.mono (Nat.zero_le _)
      · exact pb
    have h1 := pL.log_le (lt_of_lt_of_le one_pos (le_max_left _ _))
    have h2 : ((100 * (2 * p0 - 1) : ℕ) : ℝ) ≤ 200 * r := by
      have : 100 * (2 * p0 - 1) ≤ 200 * r := by omega
      exact_mod_cast this
    have h3 : ((100 * (2 * p0 - 1) : ℕ) : ℝ) * Z ≤ (200 * Z) * Z :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith

theorem constants_bounded_four : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 g NA NC : ℕ) (c₁ w Z : ℝ), 3 ≤ r → 1 ≤ p0 → p0 ≤ r → 1 ≤ g → 1 ≤ NA → 1 ≤ NC → 0 < c₁ → 1 ≤ w → 1 ≤ Z → (fdeg E : ℝ) ≤ Z → (r : ℝ) ≤ Z → Real.log (dE E) ≤ Z → Real.log g ≤ Z → Real.log NA ≤ Z → Real.log NC ≤ Z → Real.log c₁ ≤ Z → Real.log w ≤ Z → Real.log (nQ E r g NA NC c₁ w) ≤ 200 * Z ^ (4 : ℝ) ∧ Real.log (LaQ E r p0 g NA NC c₁ w) ≤ 200 * Z ^ (4 : ℝ) := by
  intro E _ _ _ r p0 g NA NC c w Z hr hp hpr hg hNA hNC hc hw hZ hfZ hrZ hdZ hgZ hNAZ hNCZ hcZ hwZ
  obtain ⟨h1, h2⟩ := constants_bounded_sq E r p0 g NA NC c w Z hr hp hpr hg hNA hNC hc hw hZ hfZ hrZ hdZ hgZ
    hNAZ hNCZ hcZ hwZ
  have h3 : Z ^ 2 ≤ Z ^ (4 : ℝ) := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)
  constructor <;> linarith

end GlobalTheory.SplitConst

end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM.Room

set_option maxHeartbeats 1000000 in

theorem room_four : ∃ C₀ : ℝ → ℝ → ℝ → ℝ, (∀ a b c, 0 ≤ C₀ a b c) ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CA CR Ck Tt cc : ℝ), WeightAlgebra.ParA large₂ CA → Real.log (Ideal.absNorm D.host.ccK) ≤ large₂.sc.L → InR D j → j < D.R.m → 3 ≤ D.R.r → 0 ≤ CR → ka.size ≤ Ck * (D.R.k : ℝ) * (D.R.f : ℝ) * large₂.sc.b → 0 < Tt → 0 < cc → Tt * cc ≤ 1 → 1 ≤ zBase large₂ ∧ RoomAt large₂ j ka CR Tt cc (C₀ CA CR Ck) 4 := by
  set C : ℝ := 200 with hCdef
  set A : ℝ := 4 with hAdef
  have hC : 0 ≤ C := by norm_num [hCdef]
  have hA : 1 ≤ A := by norm_num [hAdef]
  have H := GlobalTheory.SplitConst.constants_bounded_four
  rw [← hCdef, ← hAdef] at H
  refine ⟨fun a b c => 17 + 2 * (20 + |a| + |b| * |a| + |c|) + C * (20 + |a| + |b| * |a| + |c|) ^ A,
    fun a b c => by positivity, ?_⟩
  intro D large₂ j ka CA CR Ck Tt cc hpar hNC hj hjm hr3 hCR hka hT hcc hTc
  obtain ⟨-, -, hdE, -, hg, -, hOm, -, -, -⟩ := hpar
  have : IsCMField D.host.E := D.host.isCMField_hostE
  set K : ℝ := 20 + |CA| + |CR| * |CA| + |Ck| with hKdef
  have ha0 := abs_nonneg CA
  have hb0 := abs_nonneg CR
  have hc0 := abs_nonneg Ck
  have hab0 : 0 ≤ |CR| * |CA| := mul_nonneg hb0 ha0
  have hK : 20 ≤ K := by rw [hKdef]; linarith
  have hL1 : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hfN : 1 ≤ D.R.f := by
    unfold Ranks.f Ranks.n
    have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity)
    omega
  have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hfN
  have hr1 : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : 1 ≤ D.R.r)
  have hm2 := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hkr : (D.R.k : ℝ) ≤ D.R.r := by
    have : D.R.k ≤ D.R.r := by unfold Ranks.r; omega
    exact_mod_cast this
  have hp1 : 1 ≤ (D.R.sigW j).2 := by unfold Ranks.sigW; simp only; omega
  have hpr : (D.R.sigW j).2 ≤ D.R.r := by unfold Ranks.sigW Ranks.r; simp only; omega
  set z : ℝ := zBase large₂ with hz
  have hzdef : z = (D.R.f : ℝ) * D.R.r * large₂.sc.L := rfl
  have hfr1 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := one_le_mul_of_one_le_of_one_le hf1 hr1
  have hfrz : (D.R.f : ℝ) * D.R.r ≤ z := le_mul_of_one_le_right (by linarith) hL1
  have hLz : large₂.sc.L ≤ z := le_mul_of_one_le_left (by linarith) hfr1
  have hz1 : 1 ≤ z := by linarith
  have hfz : (D.R.f : ℝ) ≤ z := (le_mul_of_one_le_right (by linarith) hr1).trans hfrz
  have hrz : (D.R.r : ℝ) ≤ z := (le_mul_of_one_le_left (by linarith) hf1).trans hfrz
  have hzK : 20 * z ≤ K * z := mul_le_mul_of_nonneg_right hK (by linarith)
  have hKz : K * z = 20 * z + |CA| * z + |CR| * |CA| * z + |Ck| * z := by rw [hKdef]; ring
  have haz : 0 ≤ |CA| * z := by positivity
  have habz : 0 ≤ |CR| * |CA| * z := by positivity
  have hcz : 0 ≤ |Ck| * z := by positivity
  have hd : Real.log |((discr D.host.E : ℤ) : ℝ)| ≤ |CA| * z := by
    refine hdE.trans ?_
    rw [← hzdef]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
  have hd1 : (1 : ℝ) ≤ |((discr D.host.E : ℤ) : ℝ)| := by
    have := Int.one_le_abs (discr_ne_zero D.host.E)
    exact_mod_cast this
  have hd0 : 0 ≤ Real.log |((discr D.host.E : ℤ) : ℝ)| := Real.log_nonneg hd1
  have hrd0 : 0 < D.host.rdE := (rdE_pos_le D).1
  have hrd : Real.log D.host.rdE ≤ |CA| * z := by
    have h1 := logdE_eq_rd D
    have h2 : logdE D = Real.log |((discr D.host.E : ℤ) : ℝ)| := rfl
    rw [h2] at h1
    have h3 : 0 ≤ Real.log D.host.rdE := by
      exact nonneg_of_mul_nonneg_right (h1 ▸ hd0) (by linarith)
    exact (le_mul_of_one_le_left h3 (by linarith)).trans (h1 ▸ hd)
  have hfdeg : fdeg D.host.E = D.R.f := by
    unfold fdeg
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    omega
  have hg0 := (D.host.g_prime 0).one_le
  have hg1 := (D.host.g_prime 1).one_le
  have hlg : Real.log ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) ≤ K * z := by
    have e0 : ((D.host.g 0 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : D.host.g 0 ≠ 0)
    have e1 : ((D.host.g 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : D.host.g 1 ≠ 0)
    rw [Nat.cast_mul, Real.log_mul e0 e1]
    have := hg 0
    have := hg 1
    linarith
  have hNA : (((discr D.host.E).natAbs : ℕ) : ℝ) = |((discr D.host.E : ℤ) : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hNA1 : 1 ≤ (discr D.host.E).natAbs := Int.natAbs_pos.2 (discr_ne_zero D.host.E)
  have hNC1 : 1 ≤ Ideal.absNorm D.host.ccK :=
    Nat.one_le_iff_ne_zero.2 (fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h))
  have hρ1 : (1 : ℝ) ≤ WeightFamilies.rho D j := by exact_mod_cast hp1
  have hρr : (WeightFamilies.rho D j : ℝ) ≤ D.R.r := by exact_mod_cast hpr
  have hdP : (WeightFamilies.dP D j : ℝ) = 2 * D.R.f * WeightFamilies.rho D j := by unfold WeightFamilies.dP; push_cast; ring
  have hdP1 : (1 : ℝ) ≤ WeightFamilies.dP D j := by
    rw [hdP]; exact one_le_mul_of_one_le_of_one_le (by linarith) hρ1
  have hdPz : (WeightFamilies.dP D j : ℝ) ≤ 2 * z := by
    have := mul_le_mul_of_nonneg_left hρr (by linarith : (0 : ℝ) ≤ D.R.f)
    rw [hdP]; linarith
  have hRR : 0 < WeightFamilies.RRv D CR := Real.rpow_pos_of_pos hrd0 _
  have hc1 : 0 < WeightFamilies.c1 D CR Tt cc j := by unfold WeightFamilies.c1; positivity
  have hlc : Real.log (WeightFamilies.c1 D CR Tt cc j) ≤ K * z := by
    have h1 : WeightFamilies.c1 D CR Tt cc j ≤ WeightFamilies.RRv D CR * (WeightFamilies.dP D j : ℝ) ^ 2 * (WeightFamilies.rho D j : ℝ) := by
      have h0 : 0 < WeightFamilies.RRv D CR * (WeightFamilies.dP D j : ℝ) ^ 2 * (WeightFamilies.rho D j : ℝ) := by positivity
      have : WeightFamilies.c1 D CR Tt cc j =
          (WeightFamilies.RRv D CR * (WeightFamilies.dP D j : ℝ) ^ 2 * (WeightFamilies.rho D j : ℝ)) * (Tt * cc) / 2 := by
        unfold WeightFamilies.c1; ring
      rw [this]
      have := mul_le_of_le_one_right h0.le hTc
      linarith
    refine (Real.log_le_log hc1 h1).trans ?_
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have h2 : Real.log (WeightFamilies.RRv D CR) = CR * Real.log D.host.rdE := Real.log_rpow hrd0 _
    have h3 : CR * Real.log D.host.rdE ≤ |CR| * |CA| * z := by
      rw [abs_of_nonneg hCR, mul_assoc]
      exact mul_le_mul_of_nonneg_left hrd hCR
    have h4 := log_le_self' (by linarith : (0 : ℝ) ≤ WeightFamilies.dP D j)
    have h5 := log_le_self' (by linarith : (0 : ℝ) ≤ WeightFamilies.rho D j)
    push_cast
    linarith
  have hs1 := ka.one_le_size
  have hlw : Real.log (ka.size + D.R.r) ≤ K * z := by
    have hb1 : 1 ≤ large₂.sc.b := Real.one_le_exp (by linarith)
    have h1 : Ck * (D.R.k : ℝ) * (D.R.f : ℝ) ≤ |Ck| * z := by
      rw [mul_assoc]
      refine mul_le_mul (le_abs_self _) ?_ (by positivity) hc0
      have := mul_le_mul_of_nonneg_right hkr (by linarith : (0 : ℝ) ≤ D.R.f)
      linarith
    have h2 : ka.size ≤ |Ck| * z * large₂.sc.b := hka.trans (mul_le_mul_of_nonneg_right h1 (by linarith))
    have h3 : ka.size + D.R.r ≤ (|Ck| * z + z) * large₂.sc.b := by
      have := le_mul_of_one_le_right (by linarith : (0 : ℝ) ≤ z) hb1
      linarith
    refine (Real.log_le_log (by linarith) h3).trans ?_
    rw [Real.log_mul (by positivity) (by positivity)]
    have h4 : Real.log large₂.sc.b = large₂.sc.L := Real.log_exp _
    have h5 := log_le_self' (by linarith : (0 : ℝ) ≤ |Ck| * z + z)
    linarith
  obtain ⟨hn, hLa⟩ := H D.host.E D.R.r (D.R.sigW j).2 (D.host.g 0 * D.host.g 1) (discr D.host.E).natAbs
    (Ideal.absNorm D.host.ccK) (WeightFamilies.c1 D CR Tt cc j) (ka.size + D.R.r) (K * z) hr3 hp1 hpr
    (Nat.mul_pos hg0 hg1) hNA1 hNC1 hc1 (by linarith) (by linarith) (by rw [hfdeg]; linarith) (by linarith)
    (by unfold dE; linarith) hlg (by rw [hNA]; linarith) (by linarith) hlc hlw
  rw [Real.mul_rpow (by linarith) (by linarith), ← mul_assoc] at hn hLa
  have hP : z ≤ z ^ A := by
    have := Real.rpow_le_rpow_of_exponent_le hz1 hA
    rwa [Real.rpow_one] at this
  have hmax : Real.log (max 1 (WeightFamilies.c1 D CR Tt cc j)) ≤ K * z := by
    rcases max_choice 1 (WeightFamilies.c1 D CR Tt cc j) with h | h <;> rw [h]
    · rw [Real.log_one]; linarith
    · exact hlc
  have ho : |large₂.logOm| ≤ K * z := by
    have : CA * large₂.sc.L ≤ |CA| * z := mul_le_mul (le_abs_self _) hLz (by linarith) ha0
    linarith
  have hR : Real.log (D.R.r : ℝ) ≤ z := (log_le_self' (by linarith)).trans hrz
  refine ⟨hz1, ?_⟩
  exact assemble K (C * K ^ A) (z ^ A) z ka.size _ _ (Real.log D.host.rdE) _ _ _ _ hz1 hP (by linarith)
    (by positivity) hs1 hmax hLa (by linarith) hR ho (by linarith) hn

end GlobalTheory.ArcCM.Room
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_bound_runConstants_degree_four : ∃ C₀ : ℝ → ℝ → ℝ → ℝ, (∀ a b c, 0 ≤ C₀ a b c) ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CA CR Ck Tt cc : ℝ), WeightAlgebra.ParA large₂ CA → Real.log (Ideal.absNorm D.host.ccK) ≤ large₂.sc.L → InR D j → j < D.R.m → 3 ≤ D.R.r → 0 ≤ CR → ka.size ≤ Ck * (D.R.k : ℝ) * (D.R.f : ℝ) * large₂.sc.b → 0 < Tt → 0 < cc → Tt * cc ≤ 1 → 1 ≤ zBase large₂ ∧ GlobalTheory.ArcCM.RoomAt large₂ j ka CR Tt cc (C₀ CA CR Ck) 4 := by
  atlas_forward_decl GlobalTheory.ArcCM.Room.room_four
end

section
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcKill

theorem eq_zero_of_eval_off {σ : Type} {P Q : MvPolynomial σ ℂ} (hQ : Q ≠ 0)
    (h : ∀ x, MvPolynomial.eval x Q ≠ 0 → MvPolynomial.eval x P = 0) : P = 0 := by
  have : P * Q = 0 := MvPolynomial.funext fun x => by
    rw [map_mul, map_zero]
    by_cases hx : MvPolynomial.eval x Q = 0
    · rw [hx, mul_zero]
    · rw [h x hx, zero_mul]
  exact (mul_eq_zero.1 this).resolve_right hQ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem coeff_eq_zero_of_invBl (S : Finset (ArcLt Dw →₀ ℕ)) (f : (ArcLt Dw →₀ ℕ) → ℂ)
    (h : ∀ x : ArcLt Dw → ℂ, InvBl x → ∑ mo ∈ S, f mo * ∏ v ∈ mo.support, x v ^ mo v = 0) : ∀ mo ∈ S, f mo = 0 := by
  classical
  let Q : MvPolynomial (ArcLt Dw) ℂ := ∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) =>
    (MvPolynomial.X (⟨τ, (i, k)⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) ℂ)).det
  have hQe : ∀ x : ArcLt Dw → ℂ, MvPolynomial.eval x Q ≠ 0 ↔ InvBl x := fun x => by
    rw [map_prod, Finset.prod_ne_zero_iff]
    refine forall_congr' fun τ => ?_
    have : (MvPolynomial.eval x).mapMatrix (Matrix.of fun i k : Fin (Dw.mult τ) =>
        (MvPolynomial.X (⟨τ, (i, k)⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) ℂ)) =
        Matrix.of fun i k : Fin (Dw.mult τ) => x ⟨τ, (i, k)⟩ := by
      ext i k : 2
      simp
    rw [RingHom.map_det, this]
    simp
  have hone : InvBl (Dw := Dw) fun v => (1 : Matrix (Fin (Dw.mult v.1)) (Fin (Dw.mult v.1)) ℂ) v.2.1 v.2.2 :=
    fun τ => (Matrix.det_one (n := Fin (Dw.mult τ)) (R := ℂ)).trans_ne one_ne_zero
  have hQ : Q ≠ 0 := fun h0 => (hQe _).2 hone (by rw [h0, map_zero])
  have hP : ∑ mo ∈ S, MvPolynomial.monomial mo (f mo) = 0 := eq_zero_of_eval_off hQ fun x hx => by
    rw [map_sum, ← h x ((hQe x).1 hx)]
    exact Finset.sum_congr rfl fun mo _ => MvPolynomial.eval_monomial
  intro mo hmo
  have := congrArg (MvPolynomial.coeff mo) hP
  rw [MvPolynomial.coeff_sum] at this
  simpa [MvPolynomial.coeff_monomial, hmo] using this

theorem cfOf_eq_zero : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (em : K₁ →+* ℂ) (r : ℕ) (U : Unf Xo c (em.comp (algebraMap c.F K₁)) r) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Fam n' La c₁ d → GoodEmb c (em.comp (algebraMap c.F K₁)) → IsUnf U → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ F ∈ sec Xo c a' n, (∀ k, rdU U F k ∈ (U.X k).SSgt (laU U a' n k) c₁) → cfOf d.yF d.μ d.jj F = 0 := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ em r U a' n hfam hgood hunf hdom htv F hF hS
  obtain ⟨⟨hover, -, hpush⟩, ⟨s⟩⟩ := hfam
  obtain ⟨k, ξ', fr, u₁, κ, hu, hiso, -, hfr, hmain⟩ := GlobalTheory.T.arcDatum_sectionValue_coeff_eq_fourierJacobi hK.laws hK.laws2 hK.ubc hK.laws5 hK.n5
    E H Dw l Xo c K₁ d em r U s.ξ s.ν₀ a' n (hK.ev E H Dw l Xo c) hgood hunf hover s.tan hpush s.rk s.ξ_ne s.beta
    hdom htv
  have hν : ∑ τ : (U.X k).Ψ, (τ.1 s.ν₀).re ≤ c₁ := by
    have h1 := TraceFormIndependence.trace_re (U.X k) s.ν₀
    have h2 := s.tr
    rw [h1, ← Finset.mul_sum] at h2
    linarith
  have h0 : ∀ x, InvBl x → ajAt d em F x = 0 := fun x hx => by
    have := hmain F hF (hS k).1.1 x hx
    rw [(hS k).2 ξ' hiso _ hν _ (hfr x hx), mul_zero] at this
    exact (mul_eq_zero.1 this).resolve_right (zpow_ne_zero _ hu)
  unfold cfOf
  by_cases hmo : d.μ ∈ (arcNum (evR Xo c F d.yF)).support
  · exact (map_eq_zero em).1 (coeff_eq_zero_of_invBl _
      (fun mo => em (((arcNum (evR Xo c F d.yF)).coeff mo).coeff d.jj)) h0 _ hmo)
  · rw [MvPolynomial.notMem_support_iff.1 hmo]
    rfl

end GlobalTheory.ArcKill
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmArcFunctional_vanishes_low_fourierJacobi : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (em : K₁ →+* ℂ) (r : ℕ) (U : Unf Xo c (em.comp (algebraMap c.F K₁)) r) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Fam n' La c₁ d → GoodEmb c (em.comp (algebraMap c.F K₁)) → IsUnf U → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ F ∈ sec Xo c a' n, (∀ k, rdU U F k ∈ (U.X k).SSgt (laU U a' n k) c₁) → cfOf d.yF d.μ d.jj F = 0 := by
  atlas_forward_decl GlobalTheory.ArcKill.cfOf_eq_zero
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM

theorem exists_extend_embedding {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K] [Algebra F K]
    (σ : F →+* ℂ) : ∃ em : K →+* ℂ, em.comp (algebraMap F K) = σ := by
  letI : Algebra F ℂ := σ.toAlgebra
  haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  let f : K →ₐ[F] ℂ := IsAlgClosed.lift
  exact ⟨f.toRingHom, RingHom.ext fun x => f.commutes x⟩

theorem killQ_of_gamAt : Known → ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), GlobalTheory.RunIn.GamAt T → InR D j → j < D.R.m → KillQ h j ka CR Tt cc := by
  intro hK D T h j ka CR Tt cc hG hj hm K₁ _ _ _ d hd F hF
  have key : ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ →
      (∀ k, rdU (T.U j σ) F.1 k ∈ ((T.U j σ).X k).SSgt (laU (T.U j σ) (wtA ka) ka.n k) (WeightFamilies.c1 D CR Tt cc j)) →
      cfOf d.yF d.μ d.jj F.1 = 0 := by
    intro σ hσ hr
    obtain ⟨em, rfl⟩ := exists_extend_embedding (K := K₁) σ
    have hc : F.1 ∈ T.C j ka := cutR_le T.C j ka F.2
    exact GlobalTheory.T.cmArcFunctional_vanishes_low_fourierJacobi hK _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d _ _ _ em _
      (Formalism.L2.PjFree.Unf.ofPj (T.U j _)) (wtA ka) ka.n hd hσ (h.unf j hj _ hσ) (dom_wtA ka)
      (GlobalTheory.TransvPrinc.transvIn_of_hasPrinc _ _ _ _ (T.Q.Xo j) T.Q.c _ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j _)) (wtA ka) ka.n
        (hG j hj _ hσ) (h.chiTriv j hj _ hσ _ _ (dom_wtA ka))) F.1 hc.1 hr
  exact key T.σ₀ T.good_σ₀ ((GlobalTheory.T.mem_forms_low_coeffs_vanish_iff_fourierJacobi D T h j ka CR Tt cc hj hm F).2.1 hF)

end GlobalTheory.ArcCM
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

set_option autoImplicit false

namespace GlobalTheory.RunJoin

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem qAt_run : ∃ Cq : ℝ → ℝ → ℝ, ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → j < D.R.m → LatAt (recB h.toLawsCore) j ka → QAt large₂ (recB h.toLawsCore) j ka 7 H.CK 1 4 (Cq H.CA H.CK) 4 Tn (cc D large₂ C2 A2 7 wL) := by
  obtain ⟨C₀, hC₀, hroom⟩ := GlobalTheory.T.exists_polynomial_bound_runConstants_degree_four
  refine ⟨fun a b => 1 + 3 * C₀ a 7 b + 1041, ?_⟩
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hP hjm hL hCR hO hn hlast hsz hT hc hTc
  have h3 : 3 ≤ D.R.r := le_trans (by norm_num) hP.r8
  have hcc : Real.log (Ideal.absNorm D.host.ccK) ≤ large₂.sc.L := by
    obtain ⟨Q, -, -⟩ := hP.page
    exact Q.ccK_log
  obtain ⟨hZ, hR⟩ := hroom D large₂ j ka H.CA 7 H.CK Tn (cc D large₂ C2 A2 7 wL) hP.hyp.1 hcc hj hjm h3 hCR hsz hT hc hTc
  obtain ⟨-, -, -, -, -, -, -, -, hdim, -⟩ := GlobalTheory.T.thetaNet_dimension_and_pointCount_bound D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hP
  have hG := GlobalTheory.RunIn.gamAt_of_lawsCore D _ h.toLawsCore
  have hK := GlobalTheory.T.arithmeticCMKnownTheorems_proof
  have hpp : 1041 * Zb D large₂ ^ 3 ≤ WeightFamilies.PPv D large₂ 1041 3 * ka.size := by
    have e : WeightFamilies.PPv D large₂ 1041 3 = 1041 * Zb D large₂ ^ 3 := by
      unfold WeightFamilies.PPv
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rfl
    rw [e]
    have hZ' : (1 : ℝ) ≤ Zb D large₂ := hZ
    exact le_mul_of_one_le_right (by positivity) ka.one_le_size
  have key := GlobalTheory.T.quotientBound_of_kill_detect_constantRoom hK D _ h.toLawsCore j ka 7 Tn (cc D large₂ C2 A2 7 wL) large₂ H.CK 1 4 (C₀ H.CA 7 H.CK) 4 1041 3
    hG hj hjm hL (GlobalTheory.ArcCM.killQ_of_gamAt hK D _ h.toLawsCore j ka 7 Tn _ hG hj hjm)
    (GlobalTheory.T.cmFamilyFunctionals_detect_lowCoefficients hK D _ h.toLawsCore j ka 7 Tn _ hG hj hjm h3 hT hc) hZ (hC₀ _ _ _) (by norm_num) hR
    (le_trans hdim hpp)
  have e4 : max (4 : ℝ) (max 4 3) = 4 := by norm_num
  rw [e4] at key
  exact key hCR hO hn hlast hsz hT hc hTc

end GlobalTheory.RunJoin
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.recursive_page_lattice_bound : ∃ Cq : ℝ → ℝ → ℝ, ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → j < D.R.m → LatAt (recB h.toLawsCore) j ka → QAt large₂ (recB h.toLawsCore) j ka 7 H.CK 1 4 (Cq H.CA H.CK) 4 Tn (cc D large₂ C2 A2 7 wL) := by
  atlas_forward_decl GlobalTheory.RunJoin.qAt_run
end
