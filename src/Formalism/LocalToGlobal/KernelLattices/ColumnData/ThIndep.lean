import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData.HfTrace
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralClosureCriterion
import Lemmata.PowMulVecEigenvalue.PowMulVecEig
import Lemmata.GeneralBFactThirdBis.Imports
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExportFamilies

section
noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.AR

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

theorem sqrt_pos : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (d_pos D)

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

theorem phi_smul (s : ℚ) (x : D.host.E) : D.host.φ₀ (s • x) = (s : ℂ) * D.host.φ₀ x := by
  rw [Rat.smul_def, map_mul, map_ratCast]

theorem K_repr (u : D.host.K) :
    ∃ p q : ℚ, D.host.φ₀ (u : D.host.E) = (p : ℂ) + (q : ℂ) * be D := by
  have hK : Module.finrank ℚ D.host.K = 2 :=
    Formalism.FrobeniusOrbits.SplitK.finrank_K (L := D.host.E) (b := bb D) D.host.hyp.2.1.pos (b_sq D)
  have hli : LinearIndependent ℚ ![(1 : D.host.K), bK D] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun x : D.host.K => D.host.φ₀ (x : D.host.E)) hst
    simp only [IntermediateField.coe_add, IntermediateField.coe_smul, IntermediateField.coe_one,
      IntermediateField.coe_zero, map_add, phi_smul, map_one, map_zero, bK, phi_b, mul_one] at h1
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp [be] at hre him
    have hs := sqrt_pos D
    rcases him with h | h
    · exact ⟨by simpa [h] using hre, h⟩
    · exact absurd h D.host.hyp.2.1.ne_zero
  have hsp := hli.span_eq_top_of_card_eq_finrank (by simp [hK])
  have hu : u ∈ Submodule.span ℚ (Set.range ![(1 : D.host.K), bK D]) := by rw [hsp]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 hu
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    IntermediateField.coe_add, IntermediateField.coe_smul, IntermediateField.coe_one, map_add,
    phi_smul, map_one, mul_one, bK, phi_b]

theorem int_of_rat (r : ℚ) (h : IsIntegral ℤ (r : ℂ)) : ∃ n : ℤ, r = n := by
  have h' : IsIntegral ℤ r := by
    refine (isIntegral_algHom_iff (algebraMap ℚ ℂ).toIntAlgHom (algebraMap ℚ ℂ).injective).mp ?_
    simpa using h
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h'
  exact ⟨n, by rw [← hn]; simp⟩

abbrev psi : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)

theorem okc_of (u : 𝓞 D.host.K) : OKc D (D.host.φ₀ ((u : D.host.K) : D.host.E)) :=
  by apply _root_.UpperTheory.Reformulated.B.IntegralClosureCriterion.okc_of <;> assumption

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.AR

end

noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.AR

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

def Bf (w₁ w₂ : ℂ) : ℝ := (starRingEnd ℂ w₁ * w₂).im

theorem Bf_swap (w₁ w₂ : ℂ) : Bf w₂ w₁ = -Bf w₁ w₂ := by
  simp only [Bf, Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring

theorem Bf_sub_zsmul_left (u w w₂ : ℂ) (q : ℤ) : Bf (u - q • w) w₂ = Bf u w₂ - q * Bf w w₂ := by
  simp only [Bf, zsmul_eq_mul, map_sub, map_mul, map_intCast, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im]; ring

theorem Bf_sub_zsmul_right (w₁ u w : ℂ) (q : ℤ) : Bf w₁ (u - q • w) = Bf w₁ u - q * Bf w₁ w := by
  simp only [Bf, zsmul_eq_mul, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im]; ring

theorem cramer (w₁ w₂ u : ℂ) :
    (Bf u w₂ : ℂ) * w₁ + (Bf w₁ u : ℂ) * w₂ = (Bf w₁ w₂ : ℂ) * u := by
  apply Complex.ext <;>
    simp only [Bf, Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im] <;> ring

theorem Bf_comb (w₁ w₂ : ℂ) (s t s' t' : ℝ) :
    Bf ((s : ℂ) * w₁ + (t : ℂ) * w₂) ((s' : ℂ) * w₁ + (t' : ℂ) * w₂) = (s * t' - t * s') * Bf w₁ w₂ := by
  simp only [Bf, map_add, map_mul, Complex.conj_ofReal, Complex.mul_im, Complex.mul_re,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im]; ring

theorem cast_toNat (n : ℤ) (h : 0 ≤ n) : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h]

theorem area_spec (Λ : AddSubgroup ℂ) (κ : ℝ) (hκ : 0 < κ)
    (hdisc : ∀ w₁ ∈ Λ, ∀ w₂ ∈ Λ, ∃ n : ℤ, Bf w₁ w₂ = κ * n)
    (hne : ∃ w₁ ∈ Λ, ∃ w₂ ∈ Λ, Bf w₁ w₂ ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ area Λ = κ * m ∧ ∀ w₁ ∈ Λ, ∀ w₂ ∈ Λ, ∃ n : ℤ, Bf w₁ w₂ = area Λ * n := by
  classical

  have hQ : ∃ n : ℕ, 0 < n ∧ ∃ w₁ ∈ Λ, ∃ w₂ ∈ Λ, Bf w₁ w₂ = κ * n := by
    obtain ⟨w₁, h₁, w₂, h₂, h0⟩ := hne
    obtain ⟨n, hn⟩ := hdisc w₁ h₁ w₂ h₂
    rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
    · refine ⟨(-n).toNat, by omega, w₂, h₂, w₁, h₁, ?_⟩
      rw [Bf_swap, hn, cast_toNat _ (by omega)]; push_cast; ring
    · exact absurd (by rw [hn, hn0]; simp) h0
    · refine ⟨n.toNat, by omega, w₁, h₁, w₂, h₂, ?_⟩
      rw [hn, cast_toNat _ hn0.le]
  set m := Nat.find hQ with hm
  obtain ⟨hm0, w₁, h₁, w₂, h₂, hw⟩ := Nat.find_spec hQ
  have hmin : ∀ n : ℕ, 0 < n → ∀ u ∈ Λ, ∀ v ∈ Λ, Bf u v = κ * n → m ≤ n :=
    fun n hn u hu v hv h => Nat.find_min' hQ ⟨hn, u, hu, v, hv, h⟩

  have harea : area Λ = κ * m := by
    unfold area
    refine IsLeast.csInf_eq ⟨⟨by positivity, w₁, h₁, w₂, h₂, ?_⟩, ?_⟩
    · change κ * m = |Bf w₁ w₂|
      rw [hw, abs_of_nonneg (by positivity)]
    · rintro a ⟨ha, u, hu, v, hv, rfl⟩
      change κ * m ≤ |Bf u v|
      obtain ⟨n, hn⟩ := hdisc u hu v hv
      rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
      · have := hmin (-n).toNat (by omega) v hv u hu (by
          rw [Bf_swap, hn, cast_toNat _ (by omega)]; push_cast; ring)
        rw [hn, abs_mul, abs_of_pos hκ, abs_of_neg (by exact_mod_cast hn0 : (n : ℝ) < 0)]
        have h' : ((m : ℤ) : ℝ) ≤ ((-n : ℤ) : ℝ) := by exact_mod_cast (by omega : (m : ℤ) ≤ -n)
        push_cast at h'
        exact mul_le_mul_of_nonneg_left h' hκ.le
      · exfalso; change 0 < |Bf u v| at ha; rw [hn, hn0] at ha; simp at ha
      · have := hmin n.toNat (by omega) u hu v hv (by rw [hn, cast_toNat _ hn0.le])
        rw [hn, abs_mul, abs_of_pos hκ, abs_of_pos (by exact_mod_cast hn0 : (0 : ℝ) < n)]
        have h' : ((m : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast (by omega : (m : ℤ) ≤ n)
        push_cast at h'
        exact mul_le_mul_of_nonneg_left h' hκ.le
  refine ⟨m, hm0, harea, ?_⟩
  set g := κ * m with hg
  have hg0 : 0 < g := by positivity

  have hleft : ∀ u ∈ Λ, ∃ q : ℤ, Bf u w₂ = g * q := by
    intro u hu
    obtain ⟨n, hn⟩ := hdisc u hu w₂ h₂
    refine ⟨n / m, ?_⟩
    have hr : Bf (u - (n / m) • w₁) w₂ = κ * ((n % m : ℤ) : ℝ) := by
      rw [Bf_sub_zsmul_left, hn, hw]
      have := Int.mul_ediv_add_emod n m
      have : (n : ℝ) = ((n % m : ℤ) : ℝ) + m * ((n / m : ℤ) : ℝ) := by
        have h2 : (n : ℝ) = ((m : ℤ) : ℝ) * ((n / m : ℤ) : ℝ) + ((n % m : ℤ) : ℝ) := by exact_mod_cast this.symm
        rw [h2]; push_cast; ring
      rw [this]; ring
    have hr0 : n % (m : ℤ) = 0 := by
      by_contra hne0
      have hpos : 0 < n % (m : ℤ) := lt_of_le_of_ne (Int.emod_nonneg _ (by omega)) (Ne.symm hne0)
      have hlt : n % (m : ℤ) < m := Int.emod_lt_of_pos _ (by omega)
      have := hmin (n % (m : ℤ)).toNat (by omega) _ (Λ.sub_mem hu (Λ.zsmul_mem h₁ _)) w₂ h₂
        (by rw [hr, cast_toNat _ hpos.le])
      omega
    have := Int.mul_ediv_add_emod n m
    rw [hr0, add_zero] at this
    have h3 : (n : ℝ) = (m : ℝ) * ((n / m : ℤ) : ℝ) := by exact_mod_cast this.symm
    rw [hn, hg, h3]; ring
  have hright : ∀ u ∈ Λ, ∃ q : ℤ, Bf w₁ u = g * q := by
    intro u hu
    obtain ⟨n, hn⟩ := hdisc w₁ h₁ u hu
    refine ⟨n / m, ?_⟩
    have hr : Bf w₁ (u - (n / m) • w₂) = κ * ((n % m : ℤ) : ℝ) := by
      rw [Bf_sub_zsmul_right, hn, hw]
      have := Int.mul_ediv_add_emod n m
      have : (n : ℝ) = ((n % m : ℤ) : ℝ) + m * ((n / m : ℤ) : ℝ) := by
        have h2 : (n : ℝ) = ((m : ℤ) : ℝ) * ((n / m : ℤ) : ℝ) + ((n % m : ℤ) : ℝ) := by exact_mod_cast this.symm
        rw [h2]; push_cast; ring
      rw [this]; ring
    have hr0 : n % (m : ℤ) = 0 := by
      by_contra hne0
      have hpos : 0 < n % (m : ℤ) := lt_of_le_of_ne (Int.emod_nonneg _ (by omega)) (Ne.symm hne0)
      have hlt : n % (m : ℤ) < m := Int.emod_lt_of_pos _ (by omega)
      have := hmin (n % (m : ℤ)).toNat (by omega) w₁ h₁ _ (Λ.sub_mem hu (Λ.zsmul_mem h₂ _))
        (by rw [hr, cast_toNat _ hpos.le])
      omega
    have := Int.mul_ediv_add_emod n m
    rw [hr0, add_zero] at this
    have h3 : (n : ℝ) = (m : ℝ) * ((n / m : ℤ) : ℝ) := by exact_mod_cast this.symm
    rw [hn, hg, h3]; ring

  have hdec : ∀ u ∈ Λ, ∃ s t : ℤ, u = ((s : ℝ) : ℂ) * w₁ + ((t : ℝ) : ℂ) * w₂ := by
    intro u hu
    obtain ⟨s, hs⟩ := hleft u hu
    obtain ⟨t, ht⟩ := hright u hu
    refine ⟨s, t, ?_⟩
    have hc := cramer w₁ w₂ u
    rw [hs, ht, hw] at hc
    have hg0' : (g : ℂ) ≠ 0 := by exact_mod_cast hg0.ne'
    apply mul_left_cancel₀ hg0'
    rw [← hc]; push_cast; ring
  intro u hu v hv
  obtain ⟨s, t, rfl⟩ := hdec u hu
  obtain ⟨s', t', rfl⟩ := hdec v hv
  refine ⟨s * t' - t * s', ?_⟩
  rw [Bf_comb, hw, harea]; push_cast; ring

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
  rw [map_div₀, map_add, map_mul, conj_be, map_intCast, map_intCast, map_ofNat]; push_cast; ring

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

theorem half_int {F : Type*} [Field F] [CharZero F] (x : F) (k : ℤ)
    (hx : x ^ 2 = -(4 * (k : F) + 3)) : IsIntegral ℤ ((1 + x) / 2) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (k + 1), by monicity!, ?_⟩
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C]
  push_cast
  linear_combination hx / 4

theorem bK_sq : bK D ^ 2 = -(D.host.d : D.host.K) := by
  apply Subtype.ext
  push_cast
  exact b_sq D

def om : 𝓞 D.host.K :=
  ⟨(1 + bK D) / 2, half_int _ (d_mod D).choose (by
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
  rw [h2, map_div₀, map_add, map_one, map_ofNat]
  exact congrArg (fun t => (1 + t) / 2) (phi_b D)

theorem Bf_lat (δ : ℂ) (c₁ c₂ : 𝓞 D.host.K) :
    Bf (δ * ph D c₁) (δ * ph D c₂) = Complex.normSq δ * (starRingEnd ℂ (ph D c₁) * ph D c₂).im := by
  have : starRingEnd ℂ (δ * ph D c₁) * (δ * ph D c₂) =
      (Complex.normSq δ : ℂ) * (starRingEnd ℂ (ph D c₁) * ph D c₂) := by
    rw [Complex.normSq_eq_conj_mul_self, map_mul]; ring
  rw [Bf, this]; simp [Complex.mul_im]

theorem okc_pair (c₁ c₂ : 𝓞 D.host.K) : OKc D (starRingEnd ℂ (ph D c₁) * ph D c₂) :=
  okc_mul D (okc_conj D (okc_of D c₁)) (okc_of D c₂)

theorem div_okc (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ area (lamOf D cc δ) = Complex.normSq δ * (Real.sqrt D.host.d / 2) * m ∧
      ∀ c ∈ cc, ∀ c' ∈ cc, OKc D (starRingEnd ℂ (ph D c') * ph D c / m) := by
  have hn : 0 < Complex.normSq δ := Complex.normSq_pos.2 hδ
  have hs := sqrt_pos D
  have hκ : 0 < Complex.normSq δ * (Real.sqrt D.host.d / 2) := by positivity
  have hdisc : ∀ w₁ ∈ lamOf D cc δ, ∀ w₂ ∈ lamOf D cc δ, ∃ n : ℤ,
      Bf w₁ w₂ = Complex.normSq δ * (Real.sqrt D.host.d / 2) * n := by
    intro w₁ h₁ w₂ h₂
    obtain ⟨c₁, -, rfl⟩ := FL.lam_mem D cc δ w₁ h₁
    obtain ⟨c₂, -, rfl⟩ := FL.lam_mem D cc δ w₂ h₂
    obtain ⟨x, y, -, hz⟩ := okc_pair D c₁ c₂
    refine ⟨y, ?_⟩
    rw [Bf_lat, hz, im_coord]; ring
  have hne : ∃ w₁ ∈ lamOf D cc δ, ∃ w₂ ∈ lamOf D cc δ, Bf w₁ w₂ ≠ 0 := by
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcc
    refine ⟨δ * ph D c, AddSubgroup.subset_closure ⟨c, hc, rfl⟩,
      δ * ph D (c * om D), AddSubgroup.subset_closure ⟨c * om D, cc.mul_mem_right _ hc, rfl⟩, ?_⟩
    have hph : ph D (c * om D) = ph D c * ((1 + be D) / 2) := by
      rw [← ph_om]; simp [ph]
    have hc1 : ph D c ≠ 0 := by
      simp only [ph, map_ne_zero_iff _ D.host.φ₀.injective]
      exact_mod_cast hc0
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
  obtain ⟨m, hm, harea, hall⟩ := area_spec (lamOf D cc δ) _ hκ hdisc hne
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
end

section
noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.TI

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open Polynomial NumberField Matrix

theorem trace_isIntegral {E : Type*} [Field E] [NumberField E] (φ : E →+* ℂ) {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (M : Matrix (Fin n) (Fin n) E) (hM : ∀ x ∈ L, M *ᵥ x ∈ L) : IsIntegral ℤ M.trace := by
  first | exact Bl.general_b_fact_third_bis.goal1 .. | (apply Bl.general_b_fact_third_bis.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third_bis.goal1 <;> assumption) | (apply @Bl.general_b_fact_third_bis.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_third_bis.goal1 <;> assumption) | (apply @Bl.general_b_fact_third_bis.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_third_bis.goal1 E ‹_› ‹_› φ n L hfg hsp M hM | exact @Bl.general_b_fact_third_bis.goal1 E ‹_› ‹_› φ n L hfg hsp M | exact @Bl.general_b_fact_third_bis.goal1 E ‹_› ‹_› φ n L hfg hsp | exact @Bl.general_b_fact_third_bis.goal1 E ‹_› ‹_› φ n L hfg | exact @Bl.general_b_fact_third_bis.goal1 E ‹_› ‹_› φ n L | exact @Bl.general_b_fact_third_bis.goal1 E ‹_› ‹_› φ n | exact @Bl.general_b_fact_third_bis.goal1 E ‹_› ‹_› φ | exact @Bl.general_b_fact_third_bis.goal1 E ‹_› ‹_› | exact @Bl.general_b_fact_third_bis.goal1 E ‹_› | exact @Bl.general_b_fact_third_bis.goal1 E

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.TI

end

noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.TI

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.FrobeniusOrbits Matrix
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable (D : Car)

def sE {N N' : ℕ} (A B : Matrix (Fin N') (Fin N) D.host.E) : D.host.E :=
  ∑ i, ∑ j, A i j * D.host.conj (B i j)

theorem hYY_eq {N N' : ℕ} (A B : Matrix (Fin N') (Fin N) D.host.E) :
    hYY D A B = Algebra.trace D.host.K D.host.E (sE D A B) := rfl

theorem conj_int (o : 𝓞 D.host.E) : IsIntegral ℤ (D.host.conj (o : D.host.E)) :=
  o.isIntegral_coe.map (D.host.conj : D.host.E →ₐ[ℚ] D.host.E).toRingHom.toIntAlgHom

def cO (o : 𝓞 D.host.E) : 𝓞 D.host.E := ⟨D.host.conj (o : D.host.E), conj_int D o⟩

theorem smul_entry {N N' : ℕ} (o : 𝓞 D.host.E) (A : Matrix (Fin N') (Fin N) D.host.E) (i j) :
    (o • A) i j = (o : D.host.E) * A i j := by
  rw [Matrix.smul_apply, Algebra.smul_def]

theorem sE_add_left {N N' : ℕ} (A A' B : Matrix (Fin N') (Fin N) D.host.E) :
    sE D (A + A') B = sE D A B + sE D A' B := by
  simp only [sE, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem sE_add_right {N N' : ℕ} (A B B' : Matrix (Fin N') (Fin N) D.host.E) :
    sE D A (B + B') = sE D A B + sE D A B' := by
  simp only [sE, Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem sE_zero_left {N N' : ℕ} (B : Matrix (Fin N') (Fin N) D.host.E) : sE D 0 B = 0 := by
  simp [sE]

theorem sE_zero_right {N N' : ℕ} (A : Matrix (Fin N') (Fin N) D.host.E) : sE D A 0 = 0 := by
  simp [sE]

theorem sE_smul_left {N N' : ℕ} (o : 𝓞 D.host.E) (A B : Matrix (Fin N') (Fin N) D.host.E) :
    sE D (o • A) B = (o : D.host.E) * sE D A B := by
  simp only [sE, smul_entry, Finset.mul_sum, mul_assoc]

theorem sE_smul_right {N N' : ℕ} (o : 𝓞 D.host.E) (A B : Matrix (Fin N') (Fin N) D.host.E) :
    sE D A (o • B) = D.host.conj (o : D.host.E) * sE D A B := by
  simp only [sE, smul_entry, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sE_esmul_left {N N' : ℕ} (a : D.host.E) (A B : Matrix (Fin N') (Fin N) D.host.E) :
    sE D (a • A) B = a * sE D A B := by
  simp only [sE, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem sE_esmul_right {N N' : ℕ} (b : D.host.E) (A B : Matrix (Fin N') (Fin N) D.host.E) :
    sE D A (b • B) = D.host.conj b * sE D A B := by
  simp only [sE, Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sE_hom_gen {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L')
    (A B : Matrix (Fin N') (Fin N) D.host.E)
    (hA : ∀ x ∈ L, A *ᵥ x ∈ L') (hB : ∀ x ∈ L, B *ᵥ x ∈ L') : IsIntegral ℤ (sE D A B) := by
  let _ := D.host.cmStar
  set Bs : Matrix (Fin N) (Fin N') D.host.E := Matrix.of fun j i => D.host.conj (B i j) with hBs
  have hBs_mem : ∀ y ∈ L', Bs *ᵥ y ∈ L := by
    intro y hy
    rw [hL.2.2]
    intro x hx
    have h1 : stdH D.host.E N x (Bs *ᵥ y) = stdH D.host.E N' (B *ᵥ x) y := by
      simp only [stdH, CU.star_conj D, Matrix.mulVec, dotProduct, hBs, Matrix.of_apply, map_sum,
        map_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h1]
    exact (hL'.2.2 y).1 hy _ (hB x hx)
  have hM : ∀ x ∈ L, (Bs * A) *ᵥ x ∈ L := by
    intro x hx
    rw [← Matrix.mulVec_mulVec]
    exact hBs_mem _ (hA x hx)
  have h := trace_isIntegral D.host.φ₀ L hL.1 hL.2.1 (Bs * A) hM
  have htr : (Bs * A).trace = sE D A B := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, sE, hBs, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rwa [htr] at h

theorem sE_hom {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L')
    (A B : Matrix (Fin N') (Fin N) D.host.E) (hA : A ∈ homL D L L') (hB : B ∈ homL D L L') :
    IsIntegral ℤ (sE D A B) := by
  have h1 : ∀ A ∈ homL D L L', ∀ B, (∀ x ∈ L, B *ᵥ x ∈ L') → IsIntegral ℤ (sE D A B) := by
    intro A hA B hB
    induction hA using Submodule.span_induction with
    | mem A hA => exact sE_hom_gen D L L' hL hL' A B hA hB
    | zero => rw [sE_zero_left]; exact isIntegral_zero
    | add A A' _ _ h1 h2 => rw [sE_add_left]; exact h1.add h2
    | smul o A _ h1 => rw [sE_smul_left]; exact o.isIntegral_coe.mul h1
  induction hB using Submodule.span_induction with
  | mem B hB => exact h1 A hA B hB
  | zero => rw [sE_zero_right]; exact isIntegral_zero
  | add B B' _ _ h2 h3 => rw [sE_add_right]; exact h2.add h3
  | smul o B _ h2 => rw [sE_smul_right]; exact (conj_int D o).mul h2

def TrOK (z : D.host.E) : Prop :=
  ∀ o : 𝓞 D.host.E, IsIntegral ℤ (Algebra.trace D.host.K D.host.E ((o : D.host.E) * z))

theorem trOK_zero : TrOK D 0 := fun o => by rw [mul_zero, map_zero]; exact isIntegral_zero

theorem trOK_add {z w : D.host.E} (hz : TrOK D z) (hw : TrOK D w) : TrOK D (z + w) :=
  fun o => by rw [mul_add, map_add]; exact (hz o).add (hw o)

theorem trOK_mul {z : D.host.E} (hz : TrOK D z) (o' : 𝓞 D.host.E) : TrOK D ((o' : D.host.E) * z) :=
  fun o => by
    have := hz (o * o')
    rwa [show ((o * o' : 𝓞 D.host.E) : D.host.E) = (o : D.host.E) * o' from rfl, mul_assoc] at this

theorem trace_conj_integral (a b : D.host.E) (ha : a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E))
    (hb : b ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) :
    IsIntegral ℤ (Algebra.trace D.host.K D.host.E (a * D.host.conj b)) := by
  have h := ((D.host.der.unimodular D.host.𝔟 D.host.𝔟_spec.1 a).1 ha) b hb
  obtain ⟨r, hr⟩ := h
  rw [← hr]
  exact r.isIntegral_coe

theorem trOK_gen (a b : D.host.E) (ha : a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E))
    (hb : b ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) (t : 𝓞 D.host.E) :
    TrOK D (a * D.host.conj b * t) := by
  intro o
  have hot : ((o * t : 𝓞 D.host.E) : D.host.E) * a ∈
      (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
    have := (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem (o * t) ha
    rwa [Algebra.smul_def] at this
  have := trace_conj_integral D _ b hot hb
  rw [show ((o * t : 𝓞 D.host.E) : D.host.E) = (o : D.host.E) * t from rfl] at this
  convert this using 2
  ring

theorem trOK_YY {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L')
    (A B : Matrix (Fin N') (Fin N) D.host.E) (hA : A ∈ YYl D L L') (hB : B ∈ YYl D L L') :
    TrOK D (sE D A B) := by

  have hgen : ∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∀ A₀ ∈ homL D L L',
      ∀ b ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∀ B₀ ∈ homL D L L',
      TrOK D (sE D (a • A₀) (b • B₀)) := by
    intro a ha A₀ hA₀ b hb B₀ hB₀
    rw [sE_esmul_left, sE_esmul_right, ← mul_assoc]
    exact trOK_gen D a b ha hb ⟨sE D A₀ B₀, sE_hom D L L' hL hL' A₀ B₀ hA₀ hB₀⟩
  have h1 : ∀ A ∈ YYl D L L', ∀ b ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
      ∀ B₀ ∈ homL D L L', TrOK D (sE D A (b • B₀)) := by
    intro A hA b hb B₀ hB₀
    induction hA using Submodule.span_induction with
    | mem A hA =>
      obtain ⟨a, ha, A₀, hA₀, rfl⟩ := hA
      exact hgen a ha A₀ hA₀ b hb B₀ hB₀
    | zero => rw [sE_zero_left]; exact trOK_zero D
    | add A A' _ _ h2 h3 => rw [sE_add_left]; exact trOK_add D h2 h3
    | smul o A _ h2 => rw [sE_smul_left]; exact trOK_mul D h2 o
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨b, hb, B₀, hB₀, rfl⟩ := hB
    exact h1 A hA b hb B₀ hB₀
  | zero => rw [sE_zero_right]; exact trOK_zero D
  | add B B' _ _ h2 h3 => rw [sE_add_right]; exact trOK_add D h2 h3
  | smul o B _ h2 => rw [sE_smul_right]; exact trOK_mul D h2 (cO D o)

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.TI

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.L2.Ker.Cd.IntegralLatticeDensity.TI
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

theorem hermitian_pairing_integral : AR.HYYIntRec := by
  intro D N N' L L' hA A hA' B hB'
  have h := trOK_YY D L L' hA.2.2.1 hA.2.2.2 A B hA' hB' 1
  rw [hYY_eq]
  simpa using h

theorem arithmetic_hermitian_form : HfArithRec := HfArithRec_of_int hermitian_pairing_integral

end Formalism.L2.Ker.Cd.IntegralLatticeDensity

end
end

section
noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.SD

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.FrobeniusOrbits
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

variable (D : Car)

theorem mm_unimod (x : D.host.E) :
    x ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ↔
      ∀ y ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
        Algebra.trace D.host.K D.host.E (x * D.host.conj y) ∈
          (algebraMap (𝓞 D.host.K) D.host.K).range :=
  D.host.der.unimodular D.host.𝔟 D.host.𝔟_spec.1 x

theorem bb_ne_zero :
    (D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
  rw [FractionalIdeal.coeIdeal_ne_zero]
  intro h
  have := D.host.𝔟_spec.2
  rw [h] at this
  simp at this

theorem ideal_mul_inverse_integral {b a : D.host.E}
    (hb : b ∈ (D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))
    (ha : a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) :
    b * a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  have h := FractionalIdeal.mul_mem_mul hb ha
  rw [Host.AA0] at h
  rw [mul_inv_cancel₀ (bb_ne_zero D), FractionalIdeal.mem_one_iff] at h
  obtain ⟨r, hr⟩ := h
  exact ⟨r, hr⟩

theorem one_mem_ideal_mul_inverse :
    (1 : D.host.E) ∈ (D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) *
      D.host.AA0 := by
  rw [Host.AA0, mul_inv_cancel₀ (bb_ne_zero D)]
  exact FractionalIdeal.one_mem_one _

variable {D}

theorem stdH_eq {N : ℕ} (x y : Fin N → D.host.E) :
    (letI := D.host.cmStar; stdH D.host.E N x y) = ∑ i, D.host.conj (x i) * y i := by
  unfold stdH
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [CU.star_conj]

theorem hom_step {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L')
    (Z : Matrix (Fin N') (Fin N) D.host.E)
    (hZ : ∀ x ∈ L, ∀ y ∈ L', (∑ i, D.host.conj (y i) * Z.mulVec x i) ∈
      (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) :
    Z ∈ YYl D L L' := by
  have key : ∀ r ∈ (D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) *
      D.host.AA0, r • Z ∈ YYl D L L' := by
    intro r hr
    refine FractionalIdeal.mul_induction_on hr ?_ ?_
    · intro b hb a ha
      have hbZ : b • Z ∈ homL D L L' := by
        refine Submodule.subset_span ?_
        intro x hx
        refine (hL'.2.2 _).mpr ?_
        intro y hy
        rw [stdH_eq, Matrix.smul_mulVec]
        have : (∑ i, D.host.conj (y i) * (b • Z.mulVec x) i) =
            b * ∑ i, D.host.conj (y i) * Z.mulVec x i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Pi.smul_apply, smul_eq_mul]; ring
        rw [this]
        exact ideal_mul_inverse_integral D hb (hZ x hx y hy)
      have : (b * a) • Z = a • (b • Z) := by rw [smul_smul, mul_comm]
      rw [this]
      exact Submodule.subset_span ⟨a, ha, b • Z, hbZ, rfl⟩
    · intro x y hx hy
      rw [add_smul]
      exact Submodule.add_mem _ hx hy
  simpa using key 1 (one_mem_ideal_mul_inverse D)

theorem rank_one_mem_hom_lattice {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    {x : Fin N → D.host.E} (hx : x ∈ L) {y : Fin N' → D.host.E} (hy : y ∈ L') :
    (Matrix.of fun i j => y i * D.host.conj (x j)) ∈ homL D L L' := by
  refine Submodule.subset_span ?_
  intro v hv
  obtain ⟨r, hr⟩ := (hL.2.2 v).mp hv x hx
  have e : (Matrix.of fun i j => y i * D.host.conj (x j)).mulVec v = r • y := by
    funext i
    rw [Pi.smul_apply, Algebra.smul_def, hr, stdH_eq]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  exact L'.smul_mem r hy

theorem hYY_rank1 {N N' : ℕ} (X : Matrix (Fin N') (Fin N) D.host.E) (a : D.host.E)
    (x : Fin N → D.host.E) (y : Fin N' → D.host.E) :
    hYY D X (a • Matrix.of fun i j => y i * D.host.conj (x j)) =
      Algebra.trace D.host.K D.host.E
        ((∑ i, D.host.conj (y i) * X.mulVec x i) * D.host.conj a) := by
  unfold hYY
  congr 1
  simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, map_mul, CU.conj_conj,
    Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem alg_step (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hA : admitted D N N' L L')
    (X : Matrix (Fin N') (Fin N) D.host.E)
    (hX : ∀ Y ∈ YYl D L L', ∃ c ∈ cc, hYY D X Y = ((c : 𝓞 D.host.K) : D.host.K)) :
    X ∈ AddSubgroup.closure {B | ∃ c ∈ cc, ∃ Z ∈ YYl D L L',
      B = (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) • Z} := by
  obtain ⟨c0, hc0, hc0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcc
  have hdvd : cc ∣ Ideal.span {c0} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hc0)
  obtain ⟨cc', hcc'⟩ := hdvd
  have hc0K : ((c0 : D.host.K)) ≠ 0 := by
    intro h; apply hc0ne; exact RingOfIntegers.ext (by simpa using h)
  have hc0E : (((c0 : D.host.K) : D.host.E)) ≠ 0 := by
    intro h; apply hc0K; exact Subtype.ext (by simpa using h)
  have key : ∀ e ∈ cc', ((((e : D.host.K) / (c0 : D.host.K) : D.host.K) : D.host.E)) • X ∈
      YYl D L L' := by
    intro e he
    apply hom_step L L' hA.2.2.2
    intro x hx y hy
    rw [mm_unimod]
    intro a ha
    obtain ⟨c', hc', hh⟩ := hX _
      (Submodule.subset_span ⟨a, ha, _, rank_one_mem_hom_lattice L L' hA.2.2.1 hx hy, rfl⟩)
    rw [hYY_rank1] at hh
    have hmem : c' * e ∈ Ideal.span {c0} := by rw [hcc']; exact Ideal.mul_mem_mul hc' he
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨r, ?_⟩
    set k : D.host.K := (e : D.host.K) / (c0 : D.host.K)
    have e1 : (∑ i, D.host.conj (y i) * ((k : D.host.E) • X).mulVec x i) * D.host.conj a =
        k • ((∑ i, D.host.conj (y i) * X.mulVec x i) * D.host.conj a) := by
      rw [Algebra.smul_def, Matrix.smul_mulVec]
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [IntermediateField.algebraMap_apply]
      ring
    rw [e1, LinearMap.map_smul_of_tower, hh, smul_eq_mul]
    have hr' : ((r : D.host.K)) * (c0 : D.host.K) = (c' : D.host.K) * (e : D.host.K) := by
      have := congrArg (fun t : 𝓞 D.host.K => (t : D.host.K)) hr
      simpa using this
    show (r : D.host.K) = k * (c' : D.host.K)
    simp only [k]
    field_simp
    linear_combination hr'
  have main : ∀ z ∈ cc * cc', ((((z : D.host.K) / (c0 : D.host.K) : D.host.K) : D.host.E)) • X ∈
      AddSubgroup.closure {B | ∃ c ∈ cc, ∃ Z ∈ YYl D L L',
        B = (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) • Z} := by
    intro z hz
    refine Submodule.mul_induction_on hz ?_ ?_
    · intro c hc e he
      refine AddSubgroup.subset_closure ⟨c, hc, _, key e he, ?_⟩
      rw [smul_smul]
      congr 1
      push_cast
      ring
    · intro u w hu hw
      have : ((((u + w : 𝓞 D.host.K) : D.host.K) / (c0 : D.host.K) : D.host.K) : D.host.E) • X =
          ((((u : D.host.K) / (c0 : D.host.K) : D.host.K) : D.host.E)) • X +
          ((((w : D.host.K) / (c0 : D.host.K) : D.host.K) : D.host.E)) • X := by
        rw [← add_smul]; congr 1; push_cast; ring
      rw [this]
      exact AddSubgroup.add_mem _ hu hw
  have h1 := main c0 (by rw [← hcc']; exact Ideal.mem_span_singleton_self c0)
  rwa [div_self hc0K, IntermediateField.coe_one, one_smul] at h1

variable (D) in

theorem coord (δ : ℂ) (hδ : δ ≠ 0) (u : D.what₂.Tau → ℂ)
    (hu : ∀ y : D.host.E, ∃ k : D.host.K,
      ∑ τ, u τ * embT D τ y = δ * D.host.φ₀ (k : D.host.E)) :
    ∃ x : D.host.E, ∀ τ, u τ = δ * embT D τ x := by
  choose g hg using hu
  have ginj : ∀ k k' : D.host.K, δ * D.host.φ₀ (k : D.host.E) = δ * D.host.φ₀ (k' : D.host.E) →
      k = k' := fun k k' h => Subtype.ext (D.host.φ₀.injective (mul_left_cancel₀ hδ h))
  let lam : D.host.E →ₗ[D.host.K] D.host.K :=
    { toFun := g
      map_add' := fun y1 y2 => by
        apply ginj
        calc δ * D.host.φ₀ (g (y1 + y2) : D.host.E)
            = ∑ τ, u τ * embT D τ (y1 + y2) := (hg _).symm
          _ = ∑ τ, u τ * embT D τ y1 + ∑ τ, u τ * embT D τ y2 := by
              simp only [map_add, mul_add, Finset.sum_add_distrib]
          _ = δ * D.host.φ₀ (g y1 : D.host.E) + δ * D.host.φ₀ (g y2 : D.host.E) := by
              rw [hg, hg]
          _ = δ * D.host.φ₀ ((g y1 + g y2 : D.host.K) : D.host.E) := by
              simp only [IntermediateField.coe_add, map_add]; ring
      map_smul' := fun k y => by
        apply ginj
        calc δ * D.host.φ₀ (g (k • y) : D.host.E)
            = ∑ τ, u τ * embT D τ (k • y) := (hg _).symm
          _ = D.host.φ₀ (k : D.host.E) * ∑ τ, u τ * embT D τ y := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun τ _ => ?_
              rw [Algebra.smul_def, IntermediateField.algebraMap_apply, map_mul,
                FL.embT_K D τ _ k.2]
              ring
          _ = δ * D.host.φ₀ ((k * g y : D.host.K) : D.host.E) := by
              rw [hg, IntermediateField.coe_mul, map_mul]; ring }
  have hB := traceForm_nondegenerate D.host.K D.host.E
  set x := ((Algebra.traceForm D.host.K D.host.E).toDual hB).symm lam with hxdef
  have hx : ∀ y, Algebra.trace D.host.K D.host.E (x * y) = g y := by
    intro y
    have := LinearMap.BilinForm.apply_toDual_symm_apply
      (B := Algebra.traceForm D.host.K D.host.E) (hB := hB) lam y
    rw [Algebra.traceForm_apply] at this
    exact this
  refine ⟨x, ?_⟩
  set u' : D.what₂.Tau → ℂ := fun τ => u τ - δ * embT D τ x with hu'
  have h0 : ∀ y : D.host.E, ∑ τ, u' τ * embT D τ y = 0 := by
    intro y
    have h1 := FL.sum_tau_trace D (x * y)
    rw [hx] at h1
    simp only [u', sub_mul, Finset.sum_sub_distrib]
    rw [hg y, ← h1, Finset.mul_sum]
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul]; ring
  have hspan : ∀ z ∈ Submodule.span ℝ (Set.range (fun b : 𝓞 D.host.E => FL.embP D (b : D.host.E))),
      ∑ τ, u' τ * z τ = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, rfl⟩ := hz
      exact h0 _
    | zero => simp
    | add z w _ _ h1 h2 =>
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, h1, h2, add_zero]
    | smul r z _ h1 =>
      have : ∑ τ, u' τ * (r • z) τ = (r : ℂ) * ∑ τ, u' τ * z τ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [Pi.smul_apply, Complex.real_smul]; ring
      rw [this, h1, mul_zero]
  have hc := hspan (fun τ => starRingEnd ℂ (u' τ)) (by rw [FL.span_embP]; trivial)
  have hsq : ∑ τ, (Complex.normSq (u' τ) : ℂ) = 0 := by
    rw [← hc]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Complex.mul_conj]
  have hsq' : ∑ τ, Complex.normSq (u' τ) = 0 := by exact_mod_cast hsq
  intro τ
  have hτ := (Finset.sum_eq_zero_iff_of_nonneg (fun τ _ => Complex.normSq_nonneg (u' τ))).mp hsq'
    τ (Finset.mem_univ _)
  rw [Complex.normSq_eq_zero] at hτ
  have : u τ - δ * embT D τ x = 0 := hτ
  exact sub_eq_zero.mp this

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.SD

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.FrobeniusOrbits
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

def CurveSelfDualRec : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, δ ≠ 0 →
    ∀ x : ℂ, (∀ w ∈ lamOf D cc δ, ∃ b : ℤ,
      (x * starRingEnd ℂ w / (area (lamOf D cc δ) : ℂ)).im = b) → x ∈ lamOf D cc δ

namespace SD

variable {D : Car}

theorem mem_La_of {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {X : Matrix (Fin N') (Fin N) D.host.E}
    (hX : X ∈ AddSubgroup.closure {B | ∃ c ∈ cc, ∃ Z ∈ YYl D L L',
      B = (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) • Z}) :
    (fun τ i j => δ * embT D τ (X i j) : VC D N N') ∈ La D (tor0 D cc δ) L L' := by
  induction hX using AddSubgroup.closure_induction with
  | mem B hB =>
    obtain ⟨c, hc, Z, hZ, rfl⟩ := hB
    refine AddSubgroup.subset_closure ⟨δ * D.host.φ₀ (((c : D.host.K) : D.host.E)),
      AddSubgroup.subset_closure ⟨c, hc, rfl⟩, Z, hZ, ?_⟩
    funext τ i j
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply, embV, tor0]
    rw [FL.embT_K D τ _ (c : D.host.K).2]
    ring
  | zero =>
    have : (fun τ i j => δ * embT D τ ((0 : Matrix (Fin N') (Fin N) D.host.E) i j) : VC D N N') = 0 := by
      funext τ i j; simp
    rw [this]; exact AddSubgroup.zero_mem _
  | add A B _ _ h1 h2 =>
    have : (fun τ i j => δ * embT D τ ((A + B) i j) : VC D N N') =
        (fun τ i j => δ * embT D τ (A i j)) + (fun τ i j => δ * embT D τ (B i j)) := by
      funext τ i j; simp [mul_add]
    rw [this]; exact AddSubgroup.add_mem _ h1 h2
  | neg A _ h1 =>
    have : (fun τ i j => δ * embT D τ ((-A) i j) : VC D N N') =
        -(fun τ i j => δ * embT D τ (A i j)) := by
      funext τ i j; simp
    rw [this]; exact AddSubgroup.neg_mem _ h1

end SD

theorem SelfDualRec_of_curve (hC : CurveSelfDualRec) : SelfDualRec := by
  intro D cc hcc δ _ h0 N N' L L' hA v hv
  set ℓ : Matrix (Fin N') (Fin N) D.host.E → ℂ := fun Y =>
    ∑ τ, ∑ i, ∑ j, v τ i j * starRingEnd ℂ (embT D τ (Y i j)) with hℓdef

  have hℓ : ∀ Y ∈ YYl D L L', ∃ c ∈ cc, ℓ Y = δ * D.host.φ₀ (((c : D.host.K) : D.host.E)) := by
    intro Y hY
    apply FL.lam_mem
    apply hC D cc hcc δ h0
    intro w hw
    obtain ⟨b, hb⟩ := hv (w • embV D (tor0 D cc δ) Y)
      (AddSubgroup.subset_closure ⟨w, hw, Y, hY, rfl⟩)
    refine ⟨b, ?_⟩
    rw [← hb]
    congr 1
    unfold Hf
    congr 1
    simp only [ℓ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, embV, tor0]
    ring

  obtain ⟨M, hM, hMY⟩ := FL.YY_lower D L L' hA.2.2.1 hA.2.2.2
  have hcoord : ∀ i j, ∃ x : D.host.E, ∀ τ, v τ i j = δ * embT D τ x := by
    intro i j
    apply SD.coord D δ h0
    intro y
    obtain ⟨m, hm, hmy⟩ := FL.exists_int_mul D {D.host.conj y}
    have hy' := hmy _ (Finset.mem_singleton_self _)
    set A : Matrix (Fin N') (Fin N) D.host.E :=
      Matrix.of fun i' j' => if i' = i ∧ j' = j then (m : D.host.E) * D.host.conj y else 0
    have hAint : ∀ i' j', IsIntegral ℤ (A i' j') := by
      intro i' j'
      simp only [A, Matrix.of_apply]
      split_ifs
      · exact hy'
      · exact isIntegral_zero
    obtain ⟨c, hc, hcY⟩ := hℓ _ (hMY A hAint)
    have hMm : ((M * m : ℤ) : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero hM hm
    have hval : ℓ ((M : D.host.E) • A) = ((M * m : ℤ) : ℂ) * ∑ τ, v τ i j * embT D τ y := by
      simp only [ℓ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
      · simp only [A, Matrix.smul_apply, Matrix.of_apply, and_self, if_true, smul_eq_mul,
          map_mul, map_intCast, FL.emb_conj, Complex.conj_conj, map_intCast]
        push_cast; ring
      · intro j' _ hj'
        simp [A, hj']
      · intro h; exact absurd (Finset.mem_univ j) h
      · intro i' _ hi'
        refine Finset.sum_eq_zero fun j' _ => ?_
        simp [A, hi']
      · intro h; exact absurd (Finset.mem_univ i) h
    refine ⟨((c : D.host.K)) / ((M * m : ℤ) : D.host.K), ?_⟩
    rw [hval] at hcY
    rw [IntermediateField.coe_div, map_div₀]
    have e2 : D.host.φ₀ ((((M * m : ℤ) : D.host.K)) : D.host.E) = ((M * m : ℤ) : ℂ) := by
      simp
    rw [e2]
    field_simp
    linear_combination hcY
  choose X hXv using hcoord

  have hXc : ∀ Y ∈ YYl D L L', ∃ c ∈ cc, hYY D (Matrix.of X) Y = ((c : 𝓞 D.host.K) : D.host.K) := by
    intro Y hY
    obtain ⟨c, hc, hcY⟩ := hℓ Y hY
    refine ⟨c, hc, ?_⟩
    have e1 : ℓ Y = δ * D.host.φ₀ ((hYY D (Matrix.of X) Y : D.host.K) : D.host.E) := by
      unfold hYY
      rw [← FL.sum_tau_trace, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp only [map_sum, map_mul, FL.emb_conj, Finset.mul_sum, Matrix.of_apply, hXv]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e1] at hcY
    exact Subtype.ext (D.host.φ₀.injective (mul_left_cancel₀ h0 hcY))

  have hXS := SD.alg_step cc hcc.1 L L' hA (Matrix.of X) hXc
  have hv' : v = (fun τ i j => δ * embT D τ ((Matrix.of X) i j) : VC D N N') := by
    funext τ i j
    exact hXv i j τ
  rw [hv']
  exact SD.mem_La_of hXS

end Formalism.L2.Ker.Cd.IntegralLatticeDensity

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity.CS

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.FrobeniusOrbits Polynomial
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

theorem im_comb (w1 w2 : ℂ) (m1 n1 m2 n2 : ℤ) :
    (starRingEnd ℂ ((m1 : ℂ) * w1 + (n1 : ℂ) * w2) * ((m2 : ℂ) * w1 + (n2 : ℂ) * w2)).im =
      ((m1 * n2 - n1 * m2 : ℤ) : ℝ) * (starRingEnd ℂ w1 * w2).im := by
  simp only [map_add, map_mul, map_intCast, Complex.mul_im, Complex.mul_re,
    Complex.add_im, Complex.add_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im]
  push_cast
  ring

theorem area_of_basis (Λ : AddSubgroup ℂ) {w1 w2 : ℂ} (h1 : w1 ∈ Λ) (h2 : w2 ∈ Λ)
    (hb : ∀ w ∈ Λ, ∃ m n : ℤ, w = (m : ℂ) * w1 + (n : ℂ) * w2)
    (hD : (starRingEnd ℂ w1 * w2).im ≠ 0) :
    area Λ = |(starRingEnd ℂ w1 * w2).im| := by
  unfold area
  apply IsLeast.csInf_eq
  refine ⟨⟨abs_pos.mpr hD, w1, h1, w2, h2, rfl⟩, ?_⟩
  rintro a ⟨ha, u, hu, v, hv, rfl⟩
  obtain ⟨m1, n1, rfl⟩ := hb u hu
  obtain ⟨m2, n2, rfl⟩ := hb v hv
  rw [im_comb, abs_mul] at ha ⊢
  have hk : (m1 * n2 - n1 * m2 : ℤ) ≠ 0 := by
    intro h; rw [h] at ha; simp at ha
  have : (1 : ℝ) ≤ |((m1 * n2 - n1 * m2 : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
  nlinarith [abs_nonneg (starRingEnd ℂ w1 * w2).im]

theorem cramer (x w1 w2 : ℂ) :
    x * ((starRingEnd ℂ w1 * w2).im : ℂ) =
      ((x * starRingEnd ℂ w1).im : ℂ) * w2 - ((x * starRingEnd ℂ w2).im : ℂ) * w1 := by
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im] <;> ring

theorem dual_of_basis (Λ : AddSubgroup ℂ) {w1 w2 : ℂ} (h1 : w1 ∈ Λ) (h2 : w2 ∈ Λ)
    (hD : (starRingEnd ℂ w1 * w2).im ≠ 0) (harea : area Λ = |(starRingEnd ℂ w1 * w2).im|)
    (x : ℂ) (hx : ∀ w ∈ Λ, ∃ b : ℤ, (x * starRingEnd ℂ w / (area Λ : ℂ)).im = b) : x ∈ Λ := by
  obtain ⟨b1, hb1⟩ := hx w1 h1
  obtain ⟨b2, hb2⟩ := hx w2 h2
  rw [Complex.div_ofReal_im, harea] at hb1 hb2
  set D := (starRingEnd ℂ w1 * w2).im with hDdef
  have hA : |D| ≠ 0 := abs_ne_zero.mpr hD
  have e1 : (x * starRingEnd ℂ w1).im = b1 * |D| := (div_eq_iff hA).mp hb1
  have e2 : (x * starRingEnd ℂ w2).im = b2 * |D| := (div_eq_iff hA).mp hb2
  have hc := cramer x w1 w2
  rw [← hDdef, e1, e2] at hc
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD
  have m1 : (b1 : ℂ) * w2 ∈ Λ := by rw [← zsmul_eq_mul]; exact Λ.zsmul_mem h2 b1
  have m2 : (b2 : ℂ) * w1 ∈ Λ := by rw [← zsmul_eq_mul]; exact Λ.zsmul_mem h1 b2
  rcases abs_cases D with ⟨hDa, -⟩ | ⟨hDa, -⟩
  · have : x = (b1 : ℂ) * w2 - (b2 : ℂ) * w1 := by
      apply mul_right_cancel₀ hD'
      rw [hc, hDa]; push_cast; ring
    rw [this]; exact Λ.sub_mem m1 m2
  · have : x = -((b1 : ℂ) * w2 - (b2 : ℂ) * w1) := by
      apply mul_right_cancel₀ hD'
      rw [hc, hDa]; push_cast; ring
    rw [this]; exact Λ.neg_mem (Λ.sub_mem m1 m2)

variable (D : Car)

theorem s_sq : (D.host.sqd) ^ 2 = -(D.host.d : D.host.E) :=
  D.host.sqd_sq

theorem d_pos : (0 : ℚ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos

theorem K_repr (x : D.host.E) (hx : x ∈ D.host.K) :
    ∃ p q : ℚ, x = (p : D.host.E) + (q : D.host.E) * D.host.sqd := by
  first | exact UpperTheory.Reformulated.B.ExportFamilies.K_repr .. | (apply UpperTheory.Reformulated.B.ExportFamilies.K_repr <;> assumption) | (intros; apply UpperTheory.Reformulated.B.ExportFamilies.K_repr <;> assumption) | (apply @UpperTheory.Reformulated.B.ExportFamilies.K_repr <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.ExportFamilies.K_repr <;> assumption) | (apply @UpperTheory.Reformulated.B.ExportFamilies.K_repr <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.ExportFamilies.K_repr D x hx | exact @UpperTheory.Reformulated.B.ExportFamilies.K_repr D x | exact @UpperTheory.Reformulated.B.ExportFamilies.K_repr D

theorem embedding_sqrt_neg_d : D.host.φ₀ (D.host.sqd) = Complex.I * (Real.sqrt D.host.d : ℂ) :=
  D.host.φ₀_mem

theorem finrank_K : Module.finrank ℚ D.host.K = 2 := by
  set s := D.host.sqd
  have hs := s_sq D
  have hd := d_pos D
  have hmon : (X ^ 2 + C (D.host.d : ℚ)).Monic := monic_X_pow_add_C _ two_ne_zero
  have hev : aeval s (X ^ 2 + C (D.host.d : ℚ)) = 0 := by
    rw [map_add, map_pow, aeval_X, aeval_C, hs]
    simp
  have hirr : Irreducible (X ^ 2 + C (D.host.d : ℚ)) := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · rw [natDegree_X_pow_add_C]; simp
    · intro r hr
      simp only [IsRoot, eval_add, eval_pow, eval_X, eval_C] at hr
      nlinarith [sq_nonneg r]
  have hint : IsIntegral ℚ s := ⟨_, hmon, by rw [← aeval_def]; exact hev⟩
  have hmin : minpoly ℚ s = X ^ 2 + C (D.host.d : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hev hmon).symm
  have := IntermediateField.adjoin.finrank hint
  rw [hmin, natDegree_X_pow_add_C] at this
  exact this

theorem cc_basis (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) :
    ∃ c1 ∈ cc, ∃ c2 ∈ cc, (∀ c ∈ cc, ∃ m n : ℤ, c = (m : 𝓞 D.host.K) * c1 + (n : 𝓞 D.host.K) * c2) ∧
      ∀ p q : ℚ, (p : D.host.E) * ((c1 : D.host.K) : D.host.E) +
        (q : D.host.E) * ((c2 : D.host.K) : D.host.E) = 0 → p = 0 ∧ q = 0 := by
  have hr : Module.finrank ℤ (𝓞 D.host.K) = 2 := by rw [RingOfIntegers.rank, finrank_K]
  let b := Module.finBasisOfFinrankEq ℤ (𝓞 D.host.K) hr
  let bI := Ideal.selfBasis b cc hcc
  refine ⟨bI 0, (bI 0).2, bI 1, (bI 1).2, ?_, ?_⟩
  · intro c hc
    have h := bI.sum_repr ⟨c, hc⟩
    rw [Fin.sum_univ_two] at h
    refine ⟨bI.repr ⟨c, hc⟩ 0, bI.repr ⟨c, hc⟩ 1, ?_⟩
    have h2 := congrArg (fun t : cc => (t : 𝓞 D.host.K)) h
    simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, zsmul_eq_mul] at h2
    exact h2.symm
  · intro p q hpq
    have hli : LinearIndependent ℤ ![bI 0, bI 1] := by
      have : ![bI 0, bI 1] = ⇑bI := by ext i; fin_cases i <;> rfl
      rw [this]; exact bI.linearIndependent
    have key := LinearIndependent.pair_iff.mp hli (p.num * q.den) (q.num * p.den) (by
      apply Subtype.ext
      apply RingOfIntegers.ext
      apply Subtype.ext
      simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, zsmul_eq_mul, Submodule.coe_zero]
      have hc : ∀ n : ℤ, ((((n : 𝓞 D.host.K) : D.host.K)) : D.host.E) = (n : D.host.E) := by
        intro n
        have h1 : ((n : 𝓞 D.host.K) : D.host.K) = (n : D.host.K) :=
          map_intCast (algebraMap (𝓞 D.host.K) D.host.K) n
        rw [h1]; exact map_intCast D.host.K.val n
      push_cast [Int.cast_natCast, hc]
      have hp : (p : D.host.E) = (p.num : D.host.E) / (p.den : D.host.E) := by
        rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
      have hq : (q : D.host.E) = (q.num : D.host.E) / (q.den : D.host.E) := by
        rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
      rw [hp, hq] at hpq
      have hpd : (p.den : D.host.E) ≠ 0 := by exact_mod_cast p.den_nz
      have hqd : (q.den : D.host.E) ≠ 0 := by exact_mod_cast q.den_nz
      field_simp at hpq
      linear_combination hpq)
    constructor
    · have : p.num = 0 := by
        rcases mul_eq_zero.mp key.1 with h | h
        · exact h
        · exact absurd h (by exact_mod_cast q.den_nz)
      exact Rat.num_eq_zero.mp this
    · have : q.num = 0 := by
        rcases mul_eq_zero.mp key.2 with h | h
        · exact h
        · exact absurd h (by exact_mod_cast p.den_nz)
      exact Rat.num_eq_zero.mp this

end Formalism.L2.Ker.Cd.IntegralLatticeDensity.CS

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.FrobeniusOrbits
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

theorem CS.coe_intO (D : Car) (n : ℤ) :
    ((((n : 𝓞 D.host.K) : D.host.K)) : D.host.E) = (n : D.host.E) := by
  have h1 : ((n : 𝓞 D.host.K) : D.host.K) = (n : D.host.K) :=
    map_intCast (algebraMap (𝓞 D.host.K) D.host.K) n
  rw [h1]; exact map_intCast D.host.K.val n

theorem CS.im_conj_mul (δ a b : ℂ) :
    (starRingEnd ℂ (δ * a) * (δ * b)).im = Complex.normSq δ * (starRingEnd ℂ a * b).im := by
  have : starRingEnd ℂ (δ * a) * (δ * b) = (starRingEnd ℂ δ * δ) * (starRingEnd ℂ a * b) := by
    rw [map_mul]; ring
  rw [this, ← Complex.normSq_eq_conj_mul_self, Complex.im_ofReal_mul]

theorem curve_lattice_self_dual : CurveSelfDualRec := by
  intro D cc hcc δ hδ x hx
  obtain ⟨c1, hc1, c2, hc2, hspan, hind⟩ := CS.cc_basis D cc hcc.1
  set w1 := δ * D.host.φ₀ (((c1 : D.host.K) : D.host.E)) with hw1
  set w2 := δ * D.host.φ₀ (((c2 : D.host.K) : D.host.E)) with hw2
  have h1 : w1 ∈ lamOf D cc δ := AddSubgroup.subset_closure ⟨c1, hc1, rfl⟩
  have h2 : w2 ∈ lamOf D cc δ := AddSubgroup.subset_closure ⟨c2, hc2, rfl⟩
  have hb : ∀ w ∈ lamOf D cc δ, ∃ m n : ℤ, w = (m : ℂ) * w1 + (n : ℂ) * w2 := by
    intro w hw
    obtain ⟨c, hc, rfl⟩ := FL.lam_mem D cc δ w hw
    obtain ⟨m, n, rfl⟩ := hspan c hc
    refine ⟨m, n, ?_⟩
    have e : ((((m : 𝓞 D.host.K) * c1 + (n : 𝓞 D.host.K) * c2 : 𝓞 D.host.K) : D.host.K) : D.host.E) =
        (m : D.host.E) * ((c1 : D.host.K) : D.host.E) + (n : D.host.E) * ((c2 : D.host.K) : D.host.E) := by
      rw [← CS.coe_intO D m, ← CS.coe_intO D n]
      rfl
    rw [e, hw1, hw2, map_add, map_mul, map_mul, map_intCast, map_intCast]
    ring
  have hD : (starRingEnd ℂ w1 * w2).im ≠ 0 := by
    obtain ⟨p1, q1, e1⟩ := CS.K_repr D _ (c1 : D.host.K).2
    obtain ⟨p2, q2, e2⟩ := CS.K_repr D _ (c2 : D.host.K).2
    have hφ1 : D.host.φ₀ ((c1 : D.host.K) : D.host.E) =
        (p1 : ℂ) + (q1 : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℂ)) := by
      rw [e1, map_add, map_mul, map_ratCast, map_ratCast, CS.embedding_sqrt_neg_d]
    have hφ2 : D.host.φ₀ ((c2 : D.host.K) : D.host.E) =
        (p2 : ℂ) + (q2 : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℂ)) := by
      rw [e2, map_add, map_mul, map_ratCast, map_ratCast, CS.embedding_sqrt_neg_d]
    have him : (starRingEnd ℂ w1 * w2).im =
        Complex.normSq δ * (((p1 * q2 - q1 * p2 : ℚ) : ℝ) * Real.sqrt D.host.d) := by
      rw [hw1, hw2, CS.im_conj_mul, hφ1, hφ2]
      congr 1
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.mul_im,
        Complex.mul_re, Complex.add_im, Complex.add_re, Complex.ratCast_re, Complex.ratCast_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re,
        Complex.neg_im, map_ratCast]
      push_cast
      ring
    rw [him]
    have hsd : 0 < Real.sqrt D.host.d := IO.sqrt_d_pos D
    have hnδ : 0 < Complex.normSq δ := Complex.normSq_pos.mpr hδ
    intro h0
    have hpqR : ((p1 * q2 - q1 * p2 : ℚ) : ℝ) = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hnδ.ne'
      · rcases mul_eq_zero.mp h with h' | h'
        · exact h'
        · exact absurd h' hsd.ne'
    have hpq : p1 * q2 - q1 * p2 = 0 := by exact_mod_cast hpqR
    have hpqE : (p1 : D.host.E) * q2 - q1 * p2 = 0 := by
      have := congrArg (fun t : ℚ => (t : D.host.E)) hpq
      push_cast at this
      exact this
    by_cases hq : q1 = 0 ∧ q2 = 0
    · have r := hind p2 (-p1) (by rw [e1, e2, hq.1, hq.2]; push_cast; ring)
      have hp1 : p1 = 0 := by linarith [r.2]
      have r2 := hind 1 0 (by rw [e1, hp1, hq.1]; push_cast; ring)
      exact one_ne_zero r2.1
    · have r := hind q2 (-q1) (by rw [e1, e2]; push_cast; linear_combination hpqE)
      exact hq ⟨by linarith [r.2], r.1⟩
  exact CS.dual_of_basis _ h1 h2 hD (CS.area_of_basis _ h1 h2 hb hD) x hx

theorem self_dual_lattice : SelfDualRec := SelfDualRec_of_curve curve_lattice_self_dual

end Formalism.L2.Ker.Cd.IntegralLatticeDensity
end
end

section
noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

theorem hermitian_form_integral_values : HfIntRec := HfIntRec_of_gen (HfGenRec_of_arith arithmetic_hermitian_form)

theorem theta_operator_isometry : ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ,
    IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IopIso D (tor0 D cc δ) :=
  IopIso_of_parts hermitian_form_integral_values self_dual_lattice


end Formalism.L2.Ker.Cd.IntegralLatticeDensity

end
end
