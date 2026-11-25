module

public import Formalism.LocalToGlobal.ComplexLatticeArea
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.HfTrace
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralClosureCriterion
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PHfArith
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.AR

export Formalism.ComplexLatticeArea
  (Bf Bf_swap Bf_sub_zsmul_left Bf_sub_zsmul_right cramer Bf_comb cast_toNat area_spec)

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.FrobeniusOrbits
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable (D : Car)

abbrev bb : D.host.E := D.host.sqd

abbrev be : ℂ := Complex.I * (Real.sqrt D.host.d : ℂ)

def OKc (z : ℂ) : Prop :=
  ∃ x y : ℤ, Even (x - y) ∧ z = ((x : ℂ) + (y : ℂ) * be D) / 2

theorem d_pos : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos

alias sqrt_pos := _root_.Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO.sqrt_d_pos

theorem sq_sqrtC : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = (D.host.d : ℂ) := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (d_pos D).le]; simp

theorem be_sq : be D ^ 2 = -(D.host.d : ℂ) := by
  rw [be, mul_pow, Complex.I_sq, sq_sqrtC]; ring

theorem conj_be : starRingEnd ℂ (be D) = -be D := by
  simp [be, Complex.conj_ofReal]

theorem d_mod : ∃ k : ℤ, (D.host.d : ℤ) = 4 * k + 3 :=
  ⟨(D.host.d : ℤ) / 4, by have := D.host.hyp.2.2.2.1; omega⟩

theorem phi_b : D.host.φ₀ (bb D) = be D := D.host.φ₀_mem

theorem b_sq : bb D ^ 2 = -(D.host.d : D.host.E) := by
  apply D.host.φ₀.injective
  rw [map_pow, phi_b, be_sq, map_neg, map_natCast]

theorem bK_mem : bb D ∈ D.host.K := FL.bE_mem D

def bK : D.host.K := ⟨bb D, bK_mem D⟩

theorem okc_of (u : 𝓞 D.host.K) : OKc D (D.host.φ₀ ((u : D.host.K) : D.host.E)) :=
  by apply _root_.UpperTheory.Reformulated.B.IntegralClosureCriterion.okc_of

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.AR

end

noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.AR

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable (D : Car)

abbrev ph (c : 𝓞 D.host.K) : ℂ := D.host.φ₀ (((c : D.host.K) : D.host.E))

theorem okc_mul {z w : ℂ} (hz : OKc D z) (hw : OKc D w) : OKc D (z * w) := by
  obtain ⟨x, y, ⟨a, ha⟩, rfl⟩ := hz
  obtain ⟨x', y', ⟨a', ha'⟩, rfl⟩ := hw
  obtain ⟨k, hk⟩ := d_mod D
  obtain rfl : x = y + a + a := by omega
  obtain rfl : x' = y' + a' + a' := by omega
  refine ⟨-(2 * k + 1) * y * y' + a * y' + a' * y + 2 * a * a', y * y' + a * y' + a' * y,
    ⟨-(k + 1) * y * y' + a * a', by ring⟩, ?_⟩
  have hkC : (D.host.d : ℂ) = 4 * k + 3 := by exact_mod_cast hk
  have hsq := be_sq D
  push_cast
  linear_combination hsq * ((y : ℂ) * y' / 4) - hkC * ((y : ℂ) * y' / 4)

theorem okc_conj {z : ℂ} (hz : OKc D z) : OKc D (starRingEnd ℂ z) := by
  obtain ⟨x, y, ⟨a, ha⟩, rfl⟩ := hz
  refine ⟨x, -y, ⟨a + y, by omega⟩, ?_⟩
  rw [map_div₀, map_add (f := _), map_mul, conj_be, map_intCast, map_intCast, map_ofNat]; push_cast; ring

theorem coord_eq (x y : ℤ) :
    ((x : ℂ) + (y : ℂ) * be D) / 2 =
      (((x : ℝ) / 2 : ℝ) : ℂ) + (((y : ℝ) * Real.sqrt D.host.d / 2 : ℝ) : ℂ) * Complex.I := by
  push_cast; ring

theorem im_coord (x y : ℤ) :
    (((x : ℂ) + (y : ℂ) * be D) / 2).im = (y : ℝ) * Real.sqrt D.host.d / 2 := by
  rw [coord_eq]; simp

theorem good_of_okc {u : ℂ} (hu : OKc D u) : Good D (2 * u / (Real.sqrt D.host.d : ℂ)) := by
  obtain ⟨x, y, hxy, rfl⟩ := hu
  refine ⟨x, y, hxy, ?_⟩
  have hs : (Real.sqrt D.host.d : ℂ) ≠ 0 := by exact_mod_cast (sqrt_pos D).ne'
  push_cast
  field_simp

theorem bK_sq : bK D ^ 2 = -(D.host.d : D.host.K) := by
  apply Subtype.ext
  push_cast
  exact b_sq D

def om : 𝓞 D.host.K :=
  ⟨(1 + bK D) / 2, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR.half_int _ (d_mod D).choose (by
    have h2 : ((D.host.d : ℤ) : D.host.K) = ((4 * (d_mod D).choose + 3 : ℤ) : D.host.K) :=
      congrArg (fun t : ℤ => (t : D.host.K)) (d_mod D).choose_spec
    push_cast at h2
    rw [bK_sq D]; linear_combination -h2)⟩

theorem ph_om : ph D (om D) = (1 + be D) / 2 := by
  show D.host.φ₀ ((((1 + bK D) / 2 : D.host.K)) : D.host.E) = _
  have h2 : ((2 : D.host.K) : D.host.E) = 2 := by
    rw [show (2 : D.host.K) = 1 + 1 by norm_num, IntermediateField.coe_add, IntermediateField.coe_one]
    norm_num
  push_cast
  rw [h2, map_div₀, map_add (f := _), map_one, map_ofNat]
  exact congrArg (fun t => (1 + t) / 2) (phi_b D)

theorem Bf_lat (δ : ℂ) (c₁ c₂ : 𝓞 D.host.K) :
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR.Bf (δ * ph D c₁) (δ * ph D c₂) = Complex.normSq δ * (starRingEnd ℂ (ph D c₁) * ph D c₂).im := by
  have : starRingEnd ℂ (δ * ph D c₁) * (δ * ph D c₂) =
      (Complex.normSq δ : ℂ) * (starRingEnd ℂ (ph D c₁) * ph D c₂) := by
    rw [Complex.normSq_eq_conj_mul_self, map_mul]; ring
  rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR.Bf, this]; simp [Complex.mul_im]

theorem okc_pair (c₁ c₂ : 𝓞 D.host.K) : OKc D (starRingEnd ℂ (ph D c₁) * ph D c₂) :=
  okc_mul D (okc_conj D (okc_of D c₁)) (okc_of D c₂)

theorem div_okc (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ area (lamOf D cc δ) = Complex.normSq δ * (Real.sqrt D.host.d / 2) * m ∧
      ∀ c ∈ cc, ∀ c' ∈ cc, OKc D (starRingEnd ℂ (ph D c') * ph D c / m) := by
  have hn : 0 < Complex.normSq δ := Complex.normSq_pos.2 hδ
  have hs := sqrt_pos D
  have hκ : 0 < Complex.normSq δ * (Real.sqrt D.host.d / 2) := by positivity
  have hdisc : ∀ w₁ ∈ lamOf D cc δ, ∀ w₂ ∈ lamOf D cc δ, ∃ n : ℤ,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR.Bf w₁ w₂ = Complex.normSq δ * (Real.sqrt D.host.d / 2) * n := by
    intro w₁ h₁ w₂ h₂
    obtain ⟨c₁, -, rfl⟩ := FL.lam_mem D cc δ w₁ h₁
    obtain ⟨c₂, -, rfl⟩ := FL.lam_mem D cc δ w₂ h₂
    obtain ⟨x, y, -, hz⟩ := okc_pair D c₁ c₂
    refine ⟨y, ?_⟩
    rw [Bf_lat, hz, im_coord]; ring
  have hne : ∃ w₁ ∈ lamOf D cc δ, ∃ w₂ ∈ lamOf D cc δ, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR.Bf w₁ w₂ ≠ 0 := by
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcc
    refine ⟨δ * ph D c, AddSubgroup.subset_closure ⟨c, hc, rfl⟩,
      δ * ph D (c * om D), AddSubgroup.subset_closure ⟨c * om D, cc.mul_mem_right _ hc, rfl⟩, ?_⟩
    have hph : ph D (c * om D) = ph D c * ((1 + be D) / 2) := by
      rw [← ph_om]; simp [ph]
    have hc1 : ph D c ≠ 0 := by
      simp only [ph, map_ne_zero_iff _ D.host.φ₀.injective]
      intro h
      apply hc0
      apply RingOfIntegers.coe_eq_zero_iff.mp
      exact Subtype.ext h
    rw [Bf_lat, hph]
    have e : starRingEnd ℂ (ph D c) * (ph D c * ((1 + be D) / 2)) =
        (Complex.normSq (ph D c) : ℂ) * ((1 + be D) / 2) := by
      rw [Complex.normSq_eq_conj_mul_self]; ring
    have e4 : (1 + be D) / 2 =
        (((1 : ℝ) / 2 : ℝ) : ℂ) + ((Real.sqrt D.host.d / 2 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    have e5 : ((Complex.normSq (ph D c) : ℂ) * ((((1 : ℝ) / 2 : ℝ) : ℂ) +
        ((Real.sqrt D.host.d / 2 : ℝ) : ℂ) * Complex.I)).im =
        Complex.normSq (ph D c) * (Real.sqrt D.host.d / 2) := by simp [Complex.mul_im]
    rw [e, e4, e5]
    exact mul_ne_zero hn.ne' (mul_ne_zero (Complex.normSq_pos.2 hc1).ne' (by positivity))
  obtain ⟨m, hm, harea, hall⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR.area_spec (lamOf D cc δ) _ hκ hdisc hne
  refine ⟨m, hm, harea, fun c hc c' hc' => ?_⟩
  obtain ⟨x, y, -, hz⟩ := okc_pair D c' c
  obtain ⟨n₁, h₁⟩ := hall _ (AddSubgroup.subset_closure ⟨c', hc', rfl⟩) _
    (AddSubgroup.subset_closure ⟨c, hc, rfl⟩)
  obtain ⟨n₂, h₂⟩ := hall _ (AddSubgroup.subset_closure ⟨c', hc', rfl⟩) _
    (AddSubgroup.subset_closure ⟨c * om D, cc.mul_mem_right _ hc, rfl⟩)
  have hph : ph D (c * om D) = ph D c * ((1 + be D) / 2) := by
    rw [← ph_om]; simp [ph]
  rw [Bf_lat, hz, im_coord, harea] at h₁
  rw [Bf_lat, hph, ← mul_assoc, hz, harea] at h₂
  have e2 : ((x : ℂ) + (y : ℂ) * be D) / 2 * ((1 + be D) / 2) =
      ((((x - D.host.d * y : ℤ) : ℂ) + ((x + y : ℤ) : ℂ) * be D) / 2) / 2 := by
    push_cast; linear_combination (y : ℂ) / 4 * be_sq D
  rw [e2, Complex.div_ofNat_im, im_coord] at h₂
  have hy : (y : ℝ) = m * n₁ := by
    have : Complex.normSq δ * (Real.sqrt D.host.d / 2) * (y - m * n₁) = 0 := by linear_combination h₁
    have := (mul_eq_zero.1 this).resolve_left hκ.ne'
    linarith
  have hxy : ((x + y : ℤ) : ℝ) = 2 * (m * n₂) := by
    have : Complex.normSq δ * (Real.sqrt D.host.d / 2) * (((x + y : ℤ) : ℝ) - 2 * (m * n₂)) = 0 := by
      linear_combination 2 * h₂
    have := (mul_eq_zero.1 this).resolve_left hκ.ne'
    linarith
  have hyZ : y = m * n₁ := by exact_mod_cast hy
  have hxZ : x = 2 * m * n₂ - m * n₁ := by
    have : x + y = 2 * (m * n₂) := by exact_mod_cast hxy
    linarith
  refine ⟨2 * n₂ - n₁, n₁, ⟨n₂ - n₁, by ring⟩, ?_⟩
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [hz, hxZ, hyZ]
  field_simp
  push_cast
  ring

def HYYIntRec : Prop :=
  ∀ D : Car, ∀ N N' (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' →
    ∀ A ∈ YYl D L L', ∀ B ∈ YYl D L L', IsIntegral ℤ (hYY D A B)

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.AR

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.L2.Ker.Cd.IntegralLatticeDensity.IO Formalism.L2.Ker.Cd.IntegralLatticeDensity.AR
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

theorem HfArithRec_of_int (h : HYYIntRec) : HfArithRec := by
  intro D cc hcc δ hδ h0 N N' L L' hA c hc c' hc' A hA' B hB'
  obtain ⟨m, hm, harea, hdiv⟩ := div_okc D cc hcc.1 δ h0
  have hh : OKc D (D.host.φ₀ ((hYY D A B : D.host.K) : D.host.E)) :=
    okc_of D ⟨hYY D A B, h D N N' L L' hA A hA' B hB'⟩
  have hprod := okc_mul D (hdiv c hc c' hc') hh
  have hg := good_of_okc D hprod
  convert hg using 1
  have hnz : (Complex.normSq δ : ℂ) ≠ 0 := by exact_mod_cast (Complex.normSq_pos.2 h0).ne'
  have hs : (Real.sqrt D.host.d : ℂ) ≠ 0 := by exact_mod_cast (sqrt_pos D).ne'
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hcd : starRingEnd ℂ δ ≠ 0 := by simpa using h0
  rw [harea]
  simp only [ph, map_mul]
  push_cast
  rw [Complex.normSq_eq_conj_mul_self] at hnz ⊢
  field_simp

end Formalism.L2.Ker.Cd.IntegralLatticeDensity

end
