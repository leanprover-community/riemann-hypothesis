import Mathlib
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.DualLattices.SurjectiveAinfTowerZero
import ReciprocityTheory.DualLattices.Imports
import ReciprocityTheory.DualLattices.CyclicRecursion
import ReciprocityTheory.DualLattices.IsFibreSq
import ReciprocityTheory.DualLattices.DualPairInh
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TateBasisMatrix
import ReciprocityTheory.DualLattices.IsPairingValueAddRight
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTateMatricesLink
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLiftOfNil
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NilpotentCoordinates
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSeriesOfNaturalOnNilpotent
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GroupLawPowerSeries
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFormalChart
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FiniteAlgebraSplitLocal
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FinEtaleFormallyUnramified
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FinRepExistsIsPullbackSpec
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvBasicNEvalSubCoeffMem

section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WittQuot

private lemma wS_mul (p : ℕ) [hp : Fact p.Prime] (n : ℕ) : (p : MvPolynomial (Fin n) ℤ) * wS p n =
    (∑ j, (MvPolynomial.X j) ^ p) - (∑ j, MvPolynomial.X j) ^ p := by
  set q : MvPolynomial (Fin n) ℤ := (∑ j, (MvPolynomial.X j) ^ p) - (∑ j, MvPolynomial.X j) ^ p with hq
  have hd : MvPolynomial.C (p : ℤ) ∣ q := by
    rw [MvPolynomial.C_dvd_iff_zmod, hq]
    simp only [map_sub, map_sum, map_pow, MvPolynomial.map_X]
    rw [sum_pow_char, sub_self]
  rw [MvPolynomial.C_dvd_iff_dvd_coeff] at hd
  conv_rhs => rw [q.as_sum]
  change _ * ∑ m ∈ q.support, MvPolynomial.monomial m (q.coeff m / (p : ℤ)) = _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← map_natCast (MvPolynomial.C : ℤ →+* _), MvPolynomial.C_mul_monomial,
    Int.mul_ediv_cancel' (hd m)]

private lemma teich_decomp (p : ℕ) [Fact p.Prime] {K : Type} [CommRing K] [CharP K p]
    [PerfectRing K p] (x : WittVector p K) :
    ∃ y : WittVector p K, x = WittVector.teichmuller p (x.coeff 0) + p * y := by
  have hmem : x - WittVector.teichmuller p (x.coeff 0) ∈
      Ideal.span {(p : WittVector p K) ^ 1} := by
    rw [WittVector.mem_span_p_pow_iff_le_coeff_eq_zero,
      ← WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero]
    intro i hi
    obtain rfl : i = 0 := by omega
    rw [WittVector.teichmuller_coeff_zero]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨w, ?_⟩
  rw [pow_one] at hw
  rw [mul_comm, hw]; abel

theorem teichmuller_quot :
  (∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) (ϖ : PreTilt O p), ϖ.untilt = (p : O) →
    ∀ (W : Type) [CommRing W] (pr : Ainf.A p O →+* W), Function.Surjective pr →
    RingHom.ker pr = Ideal.span {(p : Ainf.A p O) ^ 2, WittVector.teichmuller p ϖ} →
    (∀ w : W, ∃ c : PreTilt O p, ∃ c' : W, w = pr (WittVector.teichmuller p c) + p * c') ∧
    (∀ (n : ℕ) (a : Fin n → PreTilt O p), ∑ j, pr (WittVector.teichmuller p (a j)) = pr (WittVector.teichmuller p (∑ j, a j)) +
      p * pr (WittVector.teichmuller p (MvPolynomial.eval₂ (Int.castRingHom (PreTilt O p)) (fun j => (frobeniusEquiv (PreTilt O p) p).symm (a j)) (wS p n)))) ∧
    (∀ c : PreTilt O p, WittVector.fontaineTheta O p (WittVector.teichmuller p c) ∈ Ideal.span {(p : O)} → pr (WittVector.teichmuller p c) = 0)) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε ϖ hϖ W _ pr hpr hker
  have hp2 : pr ((p : Ainf.A p O) ^ 2) = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.subset_span (by simp)
  have hϖ0 : pr (WittVector.teichmuller p ϖ) = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.subset_span (by simp)
  refine ⟨fun w => ?_, fun n a => ?_, fun c hc => ?_⟩
  · obtain ⟨x, rfl⟩ := hpr w
    obtain ⟨y, hy⟩ := teich_decomp p x
    refine ⟨x.coeff 0, pr y, ?_⟩
    conv_lhs => rw [hy]
    rw [map_add, map_mul, map_natCast]
  · obtain ⟨w, hw⟩ := ((teichSum p (Fin n) Finset.univ).2 (PreTilt O p) a (wS p n) (wS_mul p n)).1
    have h := congrArg pr hw
    rw [map_sum, map_add, map_add, map_mul, map_mul, hp2, zero_mul, add_zero, map_natCast] at h
    rw [h, MvPolynomial.aeval_def]
    rfl
  · have hK := ((a0 p C v O hv).2.2.1 ϖ hϖ).2.2
    have hm : WittVector.teichmuller p c ∈
        Ideal.span {(p : WittVector p (PreTilt O p)), WittVector.teichmuller p ϖ} := by
      rw [← hK, RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact hc
    obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.mp hm
    have h := congrArg (WittVector.constantCoeff (p := p) (R := PreTilt O p)) hxy
    rw [map_add, map_mul, map_mul, map_natCast, CharP.cast_eq_zero, mul_zero, zero_add] at h
    simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at h
    rw [← h, map_mul, map_mul, hϖ0, mul_zero]

end GlobalTheory.WittQuot
end

section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.WdAinf

open WittVector Ideal

variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

abbrev WRing (ϖ : PreTilt O p) := Ainf.A p O ⧸ span {(p : Ainf.A p O) ^ 2, teichmuller p ϖ}

lemma mk_teich (ϖ : PreTilt O p) :
    Ideal.Quotient.mk (span {(p : Ainf.A p O) ^ 2, teichmuller p ϖ}) (teichmuller p ϖ) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp))

lemma p_sq (ϖ : PreTilt O p) : (p : WRing p O ϖ) ^ 2 = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (span {(p : Ainf.A p O) ^ 2, teichmuller p ϖ})), ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp))

lemma modP_valuationIntegers_prime_eq_zero : (p : Ainf.Rn p O 0) = 0 := by
  have h := Ainf.hpRn p O 0
  exact (pow_one _).symm.trans h

def piW (ϖ : PreTilt O p) (hϖ : ϖ.untilt = (p : O)) : WRing p O ϖ →+* Ainf.Rn p O 0 :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk (span {(p : O) ^ (0 + 1)})).comp (fontaineTheta O p))
    (fun a ha => by
      obtain ⟨b, c, rfl⟩ := Ideal.mem_span_pair.1 ha
      simp only [RingHom.comp_apply, map_add, map_mul, map_pow, map_natCast,
        fontaineTheta_teichmuller, hϖ, modP_valuationIntegers_prime_eq_zero]
      simp)

lemma piW_mk (ϖ : PreTilt O p) (hϖ : ϖ.untilt = (p : O)) (a : Ainf.A p O) :
    piW p O ϖ hϖ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (fontaineTheta O p a) := rfl

lemma piW_surj (hv : v.Integers O) (ϖ : PreTilt O p) (hϖ : ϖ.untilt = (p : O)) :
    Function.Surjective (piW p O ϖ hϖ) := by
  intro y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, rfl⟩ := Ainf.theta_surj p O hv b
  exact ⟨_, piW_mk p O ϖ hϖ a⟩

lemma ker_piW (hv : v.Integers O) (ϖ : PreTilt O p) (hϖ : ϖ.untilt = (p : O)) :
    RingHom.ker (piW p O ϖ hϖ) = span {(p : WRing p O ϖ)} := by
  obtain ⟨-, -, hK, -, -, -⟩ := a0 p C v O hv
  have h3 := (hK ϖ hϖ).2.2
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  constructor
  · intro hx
    rw [RingHom.mem_ker, piW_mk, Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one] at hx
    have ha : a ∈ RingHom.ker ((Ideal.Quotient.mk (span {(p : O)})).comp (fontaineTheta O p)) := by
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]; exact hx
    rw [h3] at ha
    obtain ⟨b, c, rfl⟩ := Ideal.mem_span_pair.1 ha
    refine Ideal.mem_span_singleton'.2 ⟨Ideal.Quotient.mk _ b, ?_⟩
    simp only [map_add, map_mul, map_natCast, mk_teich, mul_zero, add_zero]
  · intro hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx
    rw [RingHom.mem_ker, ← hy, map_mul, map_natCast, modP_valuationIntegers_prime_eq_zero, mul_zero]

lemma W_local (hv : v.Integers O) (ϖ : PreTilt O p) (hϖ : ϖ.untilt = (p : O)) :
    IsLocalRing (WRing p O ϖ) := by
  haveI := Ainf.Rn_local p O hv 0
  refine Ainf.local_of_surj_sq (piW p O ϖ hϖ) (piW_surj p O hv ϖ hϖ) ?_
  intro k hk
  rw [ker_piW p O hv ϖ hϖ] at hk
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hk
  rw [show y * (p : WRing p O ϖ) * (y * p) = y * y * (p : WRing p O ϖ) ^ 2 by ring, p_sq, mul_zero]

lemma ann_p (hv : v.Integers O) (ϖ : PreTilt O p) (hϖ : ϖ.untilt = (p : O)) (a : WRing p O ϖ) :
    (p : WRing p O ϖ) * a = 0 ↔ piW p O ϖ hϖ a = 0 := by
  obtain ⟨-, -, -, -, -, hF⟩ := a0 p C v O hv
  rw [← RingHom.mem_ker (f := piW p O ϖ hϖ), ker_piW p O hv ϖ hϖ]
  constructor
  · intro h
    obtain ⟨y, rfl⟩ := (hF ϖ hϖ).2.2.1 a h
    exact Ideal.mem_span_singleton'.2 ⟨y, mul_comm _ _⟩
  · intro h
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 h
    rw [show (p : WRing p O ϖ) * (y * p) = y * (p : WRing p O ϖ) ^ 2 by ring, p_sq, mul_zero]

lemma pow_mem_of_nonunit (hv : v.Integers O) (x : O) (hx : ¬IsUnit x) :
    ∃ n : ℕ, (p : O) ∣ x ^ n := by
  have h1 : v (algebraMap O C x) < 1 :=
    lt_of_le_of_ne (hv.map_le_one x) (fun e => hx (hv.isUnit_of_one' e))
  have h2 : 0 < v (p : C) :=
    pos_iff_ne_zero.2 fun h => Nat.cast_ne_zero.2 hp.out.ne_zero ((Valuation.zero_iff v).1 h)
  obtain ⟨n, hn⟩ := NNReal.exists_pow_lt_of_lt_one h2 h1
  refine ⟨n, hv.dvd_of_le ?_⟩
  rw [map_pow, map_pow, map_natCast]
  exact hn.le

abbrev ResK (hv : v.Integers O) : Type :=
  haveI := Ainf.O_local O hv
  ResidueField O

def resO (hv : v.Integers O) : O →+* ResK O hv :=
  haveI := Ainf.O_local O hv
  residue O

lemma resO_surj (hv : v.Integers O) : Function.Surjective (resO O hv) :=
  haveI := Ainf.O_local O hv
  residue_surjective

lemma resO_eq_zero (hv : v.Integers O) (x : O) : resO O hv x = 0 ↔ ¬IsUnit x :=
  haveI := Ainf.O_local O hv
  (residue_eq_zero_iff x).trans ((mem_maximalIdeal x).trans mem_nonunits_iff)

def rho1 (hv : v.Integers O) : Ainf.Rn p O 0 →+* ResK O hv :=
  Ideal.Quotient.lift _ (resO O hv) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [zero_add, pow_one, map_mul, (resO_eq_zero O hv (p : O)).2 Fact.out, mul_zero])

lemma modPToValuationResidueField_surjective (hv : v.Integers O) : Function.Surjective (rho1 p O hv) := by
  intro y
  obtain ⟨a, rfl⟩ := resO_surj O hv y
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

lemma nil_ker (hv : v.Integers O) (ϖ : PreTilt O p) (hϖ : ϖ.untilt = (p : O)) (w : WRing p O ϖ)
    (hw : rho1 p O hv (piW p O ϖ hϖ w) = 0) : IsNilpotent w := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective w
  have h1 : resO O hv (fontaineTheta O p a) = 0 := hw
  obtain ⟨n, c, hc⟩ := pow_mem_of_nonunit p O hv _ ((resO_eq_zero O hv _).1 h1)
  have h2 : (Ideal.Quotient.mk _ a : WRing p O ϖ) ^ n ∈ RingHom.ker (piW p O ϖ hϖ) := by
    rw [RingHom.mem_ker, map_pow, piW_mk, ← map_pow, hc, map_mul, map_natCast, modP_valuationIntegers_prime_eq_zero, zero_mul]
  rw [ker_piW p O hv ϖ hϖ] at h2
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h2
  refine ⟨n * 2, ?_⟩
  rw [pow_mul, ← hy, mul_pow, p_sq, mul_zero]

variable (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
  (ϖ : PreTilt O p) (hϖ : ϖ.untilt = (p : O))
include hv hε hϖ

lemma xi_img : ∃ u : (Ainf.A p O)ˣ,
    (Ideal.Quotient.mk _ (Ainf.xi p O ε) : WRing p O ϖ) =
      (p : WRing p O ϖ) * (Ideal.Quotient.mk _ (u : Ainf.A p O) : WRing p O ϖ) := by
  obtain ⟨-, -, -, hX, -, -⟩ := a0 p C v O hv
  obtain ⟨u, hu⟩ := ((hX ε hv hε).2.2.2 ϖ hϖ).2
  refine ⟨u, ?_⟩
  have hu' : Ainf.xi p O ε = u * ((p : Ainf.A p O) - teichmuller p ϖ) := hu
  rw [hu', map_mul, map_sub, map_natCast, mk_teich, sub_zero, mul_comm]

def toW : Ainf.R0 p O ε →+* WRing p O ϖ :=
  Ideal.Quotient.lift _ (Ideal.Quotient.mk _) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    obtain ⟨u, hu⟩ := xi_img p O hv ε hε ϖ hϖ
    rw [map_mul, map_pow, hu, mul_pow, p_sq, zero_mul, mul_zero])

def psiW : Ainf.R'n p O ε 1 →+* WRing p O ϖ :=
  Ideal.Quotient.lift _ (toW p O hv ε hε ϖ hϖ) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_pow, map_natCast, show (1 + 1 : ℕ) = 2 from rfl, p_sq, mul_zero])

lemma psiW_surj : Function.Surjective (psiW p O hv ε hε ϖ hϖ) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk _ a), rfl⟩

def LW : LAlg (Ainf.R0 p O ε) :=
  { carrier := WRing p O ϖ, alg := (toW p O hv ε hε ϖ hϖ).toAlgebra, loc := W_local p O hv ϖ hϖ }

omit hϖ in

def LK : LAlg (Ainf.R0 p O ε) :=
  { carrier := ResK O hv, alg := ((resO O hv).comp (Ainf.thetaBar p O hv ε hε)).toAlgebra }

def piWL : LHom (LW p O hv ε hε ϖ hϖ) ((Ainf.ainfTowerL p O hv ε hε).R 0) :=
  ⟨{ toRingHom := piW p O ϖ hϖ
     commutes' := fun r => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      rfl },
    TowerExample.isLocalHom_of_surj _ (piW_surj p O hv ϖ hϖ)⟩

omit hϖ in

def rho1L : LHom ((Ainf.ainfTowerL p O hv ε hε).R 0) (LK p O hv ε hε) :=
  ⟨{ toRingHom := rho1 p O hv
     commutes' := fun _ => rfl },
    TowerExample.isLocalHom_of_surj _ (modPToValuationResidueField_surjective p O hv)⟩

def psiL : LHom ((Ainf.ainfTowerL p O hv ε hε).R' 1) (LW p O hv ε hε ϖ hϖ) :=
  ⟨{ toRingHom := psiW p O hv ε hε ϖ hϖ
     commutes' := fun _ => rfl },
    TowerExample.isLocalHom_of_surj _ (psiW_surj p O hv ε hε ϖ hϖ)⟩

omit hϖ in
lemma thetaBar_surj : Function.Surjective (Ainf.thetaBar p O hv ε hε) := by
  intro y
  obtain ⟨a, rfl⟩ := Ainf.theta_surj p O hv y
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

omit hϖ in
lemma ainf_thetaQuotRing_isLocalRing : IsLocalRing (Ainf.R0 p O ε) := by
  haveI := Ainf.O_local O hv
  refine Ainf.local_of_surj_sq (Ainf.thetaBar p O hv ε hε) (thetaBar_surj p O hv ε hε) ?_
  intro k hk
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective k
  have ha : a ∈ RingHom.ker (fontaineTheta O p) := hk
  rw [Ainf.ker_theta p O hv ε hε] at ha
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton'.2 ⟨y * y, by ring⟩

omit hϖ in
lemma LK_localHom : IsLocalHom (algebraMap (Ainf.R0 p O ε) (LK p O hv ε hε : Type)) := by
  haveI := ainf_thetaQuotRing_isLocalRing p O hv ε hε
  exact IsLocalHom.of_surjective _ ((resO_surj O hv).comp (thetaBar_surj p O hv ε hε))

omit hϖ in
lemma LK_max : maximalIdeal (LK p O hv ε hε : Type) = ⊥ :=
  maximalIdeal_eq_bot (R := ResK O hv)

end GlobalTheory.WdAinf

namespace GlobalTheory

theorem wData_ainfTower_exists :
  (∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) (ϖ : PreTilt O p), ϖ.untilt = (p : O) →
    ∀ (W : Type) [CommRing W] (pr : Ainf.A p O →+* W), Function.Surjective pr →
    RingHom.ker pr = Ideal.span {(p : Ainf.A p O) ^ 2, WittVector.teichmuller p ϖ} →
    (∀ w : W, ∃ c : PreTilt O p, ∃ c' : W, w = pr (WittVector.teichmuller p c) + p * c') ∧
    (∀ (n : ℕ) (a : Fin n → PreTilt O p), ∑ j, pr (WittVector.teichmuller p (a j)) = pr (WittVector.teichmuller p (∑ j, a j)) +
      p * pr (WittVector.teichmuller p (MvPolynomial.eval₂ (Int.castRingHom (PreTilt O p)) (fun j => (frobeniusEquiv (PreTilt O p) p).symm (a j)) (wS p n)))) ∧
    (∀ c : PreTilt O p, WittVector.fontaineTheta O p (WittVector.teichmuller p c) ∈ Ideal.span {(p : O)} → pr (WittVector.teichmuller p c) = 0)) →
  (∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p),
    ∃ (K : LAlg (Ainf.R0 p O ε)) (wd : WData (Ainf.ainfTowerL p O hv ε hε) K), IsNilOver wd.ρW ∧ maximalIdeal (K : Type) = ⊥ ∧
      IsLocalHom (algebraMap (Ainf.R0 p O ε) (K : Type))) := by
  intro H p _ C _ _ _ v O _ _ _ _ hv ε hε
  obtain ⟨⟨ϖ, hϖ⟩, -⟩ := a0 p C v O hv
  obtain ⟨h1, h2, h3⟩ := H p O hv ε hε ϖ hϖ (WdAinf.WRing p O ϖ) (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective Ideal.mk_ker
  obtain ⟨u, hu⟩ := WdAinf.xi_img p O hv ε hε ϖ hϖ
  refine ⟨WdAinf.LK p O hv ε hε,
    { W := WdAinf.LW p O hv ε hε ϖ hϖ
      ρW := (WdAinf.rho1L p O hv ε hε).comp (WdAinf.piWL p O hv ε hε ϖ hϖ)
      ρ1 := WdAinf.rho1L p O hv ε hε
      ψ := WdAinf.psiL p O hv ε hε ϖ hϖ
      πW := WdAinf.piWL p O hv ε hε ϖ hϖ
      πW_surj := WdAinf.piW_surj p O hv ϖ hϖ
      ρW_eq := rfl
      p_sq := WdAinf.p_sq p O ϖ
      ker_πW := WdAinf.ker_piW p O hv ϖ hϖ
      ann_p := WdAinf.ann_p p O hv ϖ hϖ
      compat := fun a => by
        obtain ⟨a0, rfl⟩ := Ideal.Quotient.mk_surjective a
        obtain ⟨a1, rfl⟩ := Ideal.Quotient.mk_surjective a0
        rfl
      b := Units.map (Ideal.Quotient.mk (Ideal.span {(p : Ainf.A p O) ^ 2,
        WittVector.teichmuller p ϖ})).toMonoidHom u
      ξ_img := hu
      Rb := PreTilt O p
      T := (Ideal.Quotient.mk (Ideal.span {(p : Ainf.A p O) ^ 2,
        WittVector.teichmuller p ϖ})).toMonoidHom.comp (WittVector.teichmuller p)
      decomp := h1
      witt_add := h2
      T_kill := fun c hc => h3 c (by
        have hc' : Ideal.Quotient.mk (Ideal.span {(p : O) ^ (0 + 1)})
          (WittVector.fontaineTheta O p (WittVector.teichmuller p c)) = 0 := hc
        rwa [Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one] at hc') },
    ⟨(WdAinf.modPToValuationResidueField_surjective p O hv).comp (WdAinf.piW_surj p O hv ϖ hϖ),
      fun w hw => WdAinf.nil_ker p O hv ϖ hϖ w hw⟩,
    WdAinf.LK_max p O hv ε hε, WdAinf.LK_localHom p O hv ε hε⟩

end GlobalTheory
end
end

section
noncomputable section

namespace GlobalTheory

section Helpers

open ReciprocityTheory.PGsh

private def dualTowerRing {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S) (ψ : LHom Λ S) :
    DualNum.DN Λ →+* (Dq.D : Type) :=
  Ideal.Quotient.lift _
    (Polynomial.eval₂RingHom ((Dq.σ.1.comp ψ.1 : (Λ : Type) →ₐ[R₀] (Dq.D : Type)) :
      (Λ : Type) →+* (Dq.D : Type)) Dq.η) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_pow, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, sq, Dq.η_sq, mul_zero])

private lemma dualTowerRing_C {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) (r : (Λ : Type)) :
    dualTowerRing Dq ψ (Ideal.Quotient.mk _ (Polynomial.C r)) = Dq.σ.1 (ψ.1 r) := by
  rw [dualTowerRing, Ideal.Quotient.lift_mk, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  rfl

private lemma dualTowerRing_X {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) : dualTowerRing Dq ψ (DualNum.eta Λ) = Dq.η := by
  rw [dualTowerRing, DualNum.eta, Ideal.Quotient.lift_mk, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X]

private lemma dualTowerRing_π {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) (x : DualNum.DN Λ) :
    Dq.π.1 (dualTowerRing Dq ψ x) = ψ.1 (DualNum.ev Λ x) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction f using Polynomial.induction_on with
  | C a => rw [dualTowerRing_C, Dq.sect, DualNum.ev_mk, Polynomial.eval_C]
  | add f g hf hg => simp only [map_add, hf, hg]
  | monomial n a _ =>
    have h := dualTowerRing_X Dq ψ
    rw [DualNum.eta] at h
    rw [DualNum.ev_mk, pow_succ Polynomial.X n, ← mul_assoc, map_mul, map_mul, h, map_mul, Dq.π_η]
    simp

private lemma dualTower_map_exists {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) :
    ∃ f : LHom (DualNum.dualPair Λ).D Dq.D,
      (∀ x, Dq.π.1 (f.1 x) = ψ.1 ((DualNum.dualPair Λ).π.1 x)) ∧
      (∀ x, f.1 ((DualNum.dualPair Λ).σ.1 x) = Dq.σ.1 (ψ.1 x)) ∧
      f.1 (DualNum.dualPair Λ).η = Dq.η := by
  let fA : DualNum.DN Λ →ₐ[R₀] (Dq.D : Type) :=
    { dualTowerRing Dq ψ with
      commutes' := fun r => by
        show dualTowerRing Dq ψ (algebraMap R₀ (DualNum.DN Λ) r) = _
        rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_apply, dualTowerRing_C,
          AlgHom.commutes, AlgHom.commutes] }
  refine ⟨mkLHom (R := (DualNum.dualPair Λ).D) fA fun a ha => ?_, fun x => dualTowerRing_π Dq ψ x,
    fun x => ?_, dualTowerRing_X Dq ψ⟩
  · refine (DualNum.dualPair Λ).isUnit_of_π ?_
    have h1 : IsUnit (Dq.π.1 (dualTowerRing Dq ψ a)) := ha.map Dq.π.1
    exact ψ.2.map_nonunit _ ((dualTowerRing_π Dq ψ a) ▸ h1)
  · show dualTowerRing Dq ψ (algebraMap (Λ : Type) (DualNum.DN Λ) x) = _
    rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_apply, dualTowerRing_C]
    rfl

private lemma dualTower_nonempty {R₀ : Type} [CommRing R₀] {p : ℕ} (Tw : ATowerL R₀ p) :
    Nonempty (DualTower Tw) := by
  choose d h₁ h₂ h₃ using fun n => dualTower_map_exists (DualNum.dualPair (Tw.R n)) (Tw.r n)
  exact ⟨⟨fun n => DualNum.dualPair (Tw.R n), d, h₁, h₂, h₃⟩⟩

end Helpers

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_dualTower :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} (Tw : ATowerL R₀ p), Nonempty (DualTower Tw)) :=
  fun Tw => dualTower_nonempty Tw

end GlobalTheory
end
end

section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section SlopeTestRemainingChoices

variable {R₀ : Type} [CommRing R₀] (B : BX R₀) {R : LAlg R₀}

private lemma gram_zero (N : ℕ) (y : B.G R) (hy : N • y = 0) : B.IsPairing N 0 y 1 := by
  obtain ⟨z, hz⟩ := B.pairing_exists N 0 y (smul_zero N) hy
  have h := B.isPairingValue_add_left N 0 0 y z z hz hz
  rw [add_zero] at h
  have e : z * z = z := B.pairing_unique N 0 y _ _ h hz
  have e1 : z = 1 := by simpa using e
  rwa [e1] at hz

private lemma gram_nsmul (N : ℕ) (x y : B.G R) (z : (R : Type)ˣ) (h : B.IsPairing N x y z)
    (m : ℕ) : B.IsPairing N (m • x) y (z ^ m) := by
  induction m with
  | zero =>
    rw [zero_smul, pow_zero]
    exact gram_zero B N y h.2.1
  | succ m ih =>
    rw [succ_nsmul, pow_succ]
    exact B.isPairingValue_add_left N _ _ y _ _ ih h

private lemma gram_sum {κ : Type} (s : Finset κ) (N : ℕ) (x : κ → B.G R) (y : B.G R)
    (z : κ → (R : Type)ˣ) (hy : N • y = 0) (h : ∀ i, B.IsPairing N (x i) y (z i)) :
    B.IsPairing N (∑ i ∈ s, x i) y (∏ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty]
    exact gram_zero B N y hy
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact B.isPairingValue_add_left N _ _ y _ _ (h a) ih

end SlopeTestRemainingChoices

private lemma gram_limit {p : ℕ} [Fact p.Prime] (k : ℕ → ℕ)
    (hk : ∀ n, k n ≡ k (n + 1) [MOD p ^ (n + 1)]) :
    ∃ a : ℤ_[p], ∀ n, PadicInt.toZModPow (n + 1) a = (k n : ZMod (p ^ (n + 1))) := by
  have hi : ∀ i : ℕ, (p : ℤ) ^ i ∣ (fun i : ℕ => (k (i - 1) : ℤ)) (i + 1) -
      (fun i : ℕ => (k (i - 1) : ℤ)) i := by
    intro i
    cases i with
    | zero => simp
    | succ n =>
      have h := (Nat.modEq_iff_dvd.1 (hk n))
      simpa using h
  have key := PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun i : ℕ => (k (i - 1) : ℤ)) p hi
  refine ⟨_, fun n => (key (n + 1)).trans ?_⟩
  simp only [Nat.add_sub_cancel, Int.cast_natCast]

private lemma gram_ext {p : ℕ} [Fact p.Prime] (a b : ℤ_[p])
    (h : ∀ n, PadicInt.toZModPow (n + 1) a = PadicInt.toZModPow (n + 1) b) : a = b := by
  refine PadicInt.ext_of_toZModPow.1 fun n => ?_
  rw [← PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) a, h,
    PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) b]

private lemma gram_toZMod {p : ℕ} [Fact p.Prime] (a : ℤ_[p]) (k : ℕ)
    (h : PadicInt.toZModPow (0 + 1) a = (k : ZMod (p ^ (0 + 1)))) :
    PadicInt.toZMod a = (k : ZMod p) := by
  have h1 : a - (k : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZModPow (p := p) (0 + 1)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, h, sub_self]
  rw [PadicInt.ker_toZModPow, zero_add, pow_one, ← PadicInt.maximalIdeal_eq_span_p,
    ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at h1
  exact h1

theorem tateBasis_gram :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} (B : BX R₀) (Tw : ATowerL R₀ p) [IsDomain (Tw.O : Type)] [Algebra ℤ_[p] (Tw.O : Type)],
    (∀ n, RingHom.ker (Tw.q n).1 = Ideal.span {((p : ℕ) : (Tw.O : Type)) ^ (n + 1)}) →
    (∀ n, IsPrimitiveRoot (Tw.ζ n) (p ^ (n + 1))) → (∀ n, Tw.ζ (n + 1) ^ p = Tw.ζ n) →
    ∀ τ : Ix g → ℕ → B.G Tw.O, (∀ i n, (p ^ (n + 1)) • τ i n = 0) → (∀ i n, τ i n = p • τ i (n + 1)) →
    (∀ x : B.G Tw.O, p • x = 0 → ∃! t : Ix g → ZMod p, x = ptOf B τ t) →
    (∀ x : B.G Tw.O, p • x = 0 → (∀ y : B.G Tw.O, p • y = 0 → B.IsPairing p x y 1) → x = 0) →
    ∃ E : Matrix (Ix g) (Ix g) ℤ_[p], (Eᵀ = -E ∧ ∀ i, E i i = 0) ∧ IsUnit E.det ∧
      ∀ i j n, B.IsPairing (p ^ (n + 1)) (τ i n) (τ j n) (Tw.ζ n ^ (PadicInt.toZModPow (n + 1) (E i j)).val)) := by
  intro R₀ _ p hp g B Tw _ _ _ hζ hζp τ htors hcomp hbasis hnd
  have hex : ∀ i j n, ∃ k : ℕ, k < p ^ (n + 1) ∧
      B.IsPairing (p ^ (n + 1)) (τ i n) (τ j n) (Tw.ζ n ^ k) := by
    intro i j n
    obtain ⟨z, hz⟩ := B.pairing_exists _ _ _ (htors i n) (htors j n)
    have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    obtain ⟨k, hk, e⟩ := (hζ n).eq_pow_of_mem_rootsOfUnity
      ((mem_rootsOfUnity _ z).2 (B.pairing_pow _ _ _ _ hz))
    exact ⟨k, hk, e ▸ hz⟩
  choose k hklt hk using hex
  have hcompat : ∀ i j n, k i j n ≡ k i j (n + 1) [MOD p ^ (n + 1)] := by
    intro i j n
    have h1 := gram_nsmul B _ _ _ _ (hk i j (n + 1)) p
    rw [← hcomp, pow_succ p (n + 1)] at h1
    have h2 := B.pairing_mul _ p _ _ _ (htors i n)
      (by rw [← pow_succ]; exact htors j (n + 1)) h1
    rw [← hcomp, ← pow_mul, mul_comm, pow_mul, hζp] at h2
    have h3 := B.pairing_unique _ _ _ _ _ (hk i j n) h2
    rwa [pow_eq_pow_iff_modEq, ← (hζ n).eq_orderOf] at h3
  choose E hE using fun i j => gram_limit (k i j) (hcompat i j)
  have hanti : ∀ i j, E j i = -E i j := by
    intro i j
    refine gram_ext _ _ fun n => ?_
    have h1 := B.pairing_unique _ _ _ _ _ (hk j i n) (B.pairing_sw _ _ _ _ (hk i j n))
    rw [eq_inv_iff_mul_eq_one, ← pow_add, (hζ n).pow_eq_one_iff_dvd,
      ← ZMod.natCast_eq_zero_iff, Nat.cast_add] at h1
    rw [map_neg, hE, hE]
    exact eq_neg_of_add_eq_zero_left h1
  refine ⟨Matrix.of E, ⟨?_, fun i => ?_⟩, ?_, fun i j n => ?_⟩
  · ext i j
    exact hanti i j
  · exact self_eq_neg.1 (hanti i i)
  · by_contra hu
    have hd : (Matrix.of E).det ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
      rw [PadicInt.ker_toZMod]
      exact hu
    rw [RingHom.mem_ker, RingHom.map_det] at hd
    obtain ⟨s, hs0, hs⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hd
    have ht0 : ∀ i, p • τ i 0 = 0 := fun i => by simpa using htors i 0
    have hpt : ∀ t : Ix g → ZMod p, p • ptOf B τ t = 0 := fun t => by
      simp only [ptOf, Finset.smul_sum, smul_comm p]
      exact Finset.sum_eq_zero fun j _ => by rw [ht0, smul_zero]
    have hrow : ∀ j, B.IsPairing p (ptOf B τ s) (τ j 0) 1 := by
      intro j
      have h1 := gram_sum B Finset.univ (p ^ (0 + 1)) (fun i => (s i).val • τ i 0) (τ j 0)
        (fun i => (Tw.ζ 0 ^ k i j 0) ^ (s i).val) (htors j 0)
        (fun i => gram_nsmul B _ _ _ _ (hk i j 0) _)
      have h2 : ∏ i, (Tw.ζ 0 ^ k i j 0) ^ (s i).val = 1 := by
        simp only [← pow_mul]
        rw [Finset.prod_pow_eq_pow_sum, (hζ 0).pow_eq_one_iff_dvd, zero_add, pow_one,
          ← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
        refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (congrFun hs j)
        rw [Nat.cast_mul, ZMod.natCast_zmod_val, mul_comm, ← gram_toZMod _ _ (hE i j 0)]
        rfl
      rw [h2, zero_add, pow_one] at h1
      exact h1
    have hx : ptOf B τ s = 0 := by
      refine hnd _ (hpt s) fun y hy => ?_
      obtain ⟨t, rfl, -⟩ := hbasis y hy
      have h1 := gram_sum B Finset.univ p (fun j => (t j).val • τ j 0) (ptOf B τ s)
        (fun j => (1⁻¹) ^ (t j).val) (hpt s)
        (fun j => gram_nsmul B _ _ _ _ (B.pairing_sw _ _ _ _ (hrow j)) _)
      have h2 := B.pairing_sw _ _ _ _ h1
      simp only [inv_one, one_pow, Finset.prod_const_one] at h2
      exact h2
    have h0 : (0 : B.G Tw.O) = ptOf B τ (0 : Ix g → ZMod p) := by simp [ptOf]
    exact hs0 ((hbasis 0 (smul_zero p)).unique hx.symm h0)
  · rw [Matrix.of_apply, hE, ZMod.val_cast_of_lt (hklt i j n)]
    exact hk i j n

end GlobalTheory
end

section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

variable {R₀ : Type} [CommRing R₀]

private lemma endDiff_exists_lift {O R : LAlg R₀} (s : LHom O R) (i : (R : Type)) (hi : i * i = 0) :
    ∃ φ : LHom (DualNum.dualPair O).D R, φ.comp (DualNum.dualPair O).σ = s ∧
      φ.1 (DualNum.dualPair O).η = i := by
  let ψ : DualNum.DN O →ₐ[R₀] (R : Type) :=
    Ideal.Quotient.liftₐ _ (Polynomial.aevalTower s.1 i) (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      simp [pow_two, hi])
  have hσ : ∀ r, ψ ((DualNum.dualPair O).σ.1 r) = s.1 r := fun r => by
    change ψ (algebraMap (O : Type) (DualNum.DN O) r) = _
    rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_apply]
    exact Polynomial.aevalTower_C s.1 i r
  have hη : ψ (DualNum.dualPair O).η = i := by
    change ψ (Ideal.Quotient.mk _ Polynomial.X) = _
    exact Polynomial.aevalTower_X s.1 i
  refine ⟨⟨ψ, ⟨fun d hd => ?_⟩⟩, ?_, hη⟩
  · have hk : d - (DualNum.dualPair O).σ.1 ((DualNum.dualPair O).π.1 d) ∈
        RingHom.ker (DualNum.dualPair O).π.1 := by
      rw [RingHom.mem_ker, map_sub, (DualNum.dualPair O).sect, sub_self]
    rw [(DualNum.dualPair O).ker_eq] at hk
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hk
    have h1 : ψ y * i = ψ d - s.1 ((DualNum.dualPair O).π.1 d) := by
      rw [← hσ, ← hη]
      exact (map_mul ψ _ _).symm.trans ((congrArg ψ hy).trans (map_sub ψ _ _))
    have hn : IsNilpotent (-(ψ y * i)) := ⟨2, by
      rw [show (-(ψ y * i)) ^ 2 = ψ y * ψ y * (i * i) by ring, hi, mul_zero]⟩
    have hu : IsUnit (s.1 ((DualNum.dualPair O).π.1 d)) := by
      have h2 := hn.isUnit_add_left_of_commute (u := ψ d) hd (Commute.all _ _)
      rw [h1] at h2
      simpa using h2
    exact (DualNum.dualPair O).π.2.map_nonunit d (s.2.map_nonunit _ hu)
  · exact Subtype.ext (AlgHom.ext hσ)

private lemma endDiff_ηmap_surj {O : LAlg R₀} (Dp : DualPair O) :
    Function.Surjective Dp.ηmap := by
  rintro ⟨x, hx⟩
  have hx' := hx
  rw [Submodule.restrictScalars_mem, Dp.ker_eq] at hx'
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx'
  have hk : y - Dp.σ.1 (Dp.π.1 y) ∈ RingHom.ker Dp.π.1 := by
    rw [RingHom.mem_ker, map_sub, Dp.sect, sub_self]
  rw [Dp.ker_eq] at hk
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hk
  refine ⟨Dp.π.1 y, Subtype.ext ?_⟩
  change Dp.σ.1 (Dp.π.1 y) * Dp.η = y * Dp.η
  have := Dp.η_sq
  linear_combination (-Dp.η) * (-hz) - z * this

private lemma endDiff_ηmap_inj {O : LAlg R₀} (Dp : DualPair O) :
    Function.Injective Dp.ηmap := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  exact Dp.free r (congrArg Subtype.val hr)

private lemma endDiff_coord {g : ℕ} {V M : Type} [AddCommGroup V] [Module R₀ V] [AddCommGroup M]
    [Module R₀ M] (gb : Module.Basis (Fin g) R₀ V) :
    Function.Bijective (fun m : Fin g → M => ∑ k, gb k ⊗ₜ[R₀] m k) := by
  have : (fun m : Fin g → M => ∑ k, gb k ⊗ₜ[R₀] m k) =
      (TensorProduct.equivFinsuppOfBasisLeft gb).symm ∘ Finsupp.equivFunOnFinite.symm := by
    funext m
    simp [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype]
  rw [this]
  exact (TensorProduct.equivFinsuppOfBasisLeft gb).symm.bijective.comp
    Finsupp.equivFunOnFinite.symm.bijective

private def endDiff_IsMat {g : ℕ} {B : BX R₀} {O : LAlg R₀} (gb : Module.Basis (Fin g) R₀ B.gg)
    (e : OEnd B O) (d : Matrix (Fin g) (Fin g) (O : Type)) : Prop :=
  ∀ {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker)
    (m : Fin g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (d k l) * i) →
      e.f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k)

private lemma endDiff_exists {g : ℕ} {B : BX R₀} {O : LAlg R₀} (gb : Module.Basis (Fin g) R₀ B.gg)
    (e : OEnd B O) : ∃ d, endDiff_IsMat gb e d := by
  let Dp := DualNum.dualPair O
  have h1 : ∀ l, ∃ c : Fin g → (O : Type), e.f Dp.σ (B.tg Dp.π Dp.sqZero (gb l ⊗ₜ[R₀] Dp.ηk)) =
      B.tg Dp.π Dp.sqZero (∑ k, gb k ⊗ₜ[R₀] Dp.ηmap (c k)) := fun l => by
    have h0 : B.map Dp.π (e.f Dp.σ (B.tg Dp.π Dp.sqZero (gb l ⊗ₜ[R₀] Dp.ηk))) = 0 := by
      rw [← e.nat, (B.tg_ker Dp.π Dp.sqZero _).2 ⟨_, rfl⟩, map_zero]
    obtain ⟨v, hv⟩ := (B.tg_ker Dp.π Dp.sqZero _).1 h0
    obtain ⟨m, rfl⟩ := (endDiff_coord (M := Dp.π.ker) gb).2 v
    choose c hc using fun k => endDiff_ηmap_surj Dp (m k)
    exact ⟨c, by rw [← hv]; simp only [hc]⟩
  choose c hc using h1
  refine ⟨fun k l => c l k, ?_⟩
  intro R S s π hπ l i m hm
  have hi : (i : (R : Type)) * i = 0 := by
    have : (i : (R : Type)) * i ∈ RingHom.ker π.1 ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul i.2 i.2
    rw [hπ.2] at this
    simpa using this
  obtain ⟨φ, hφ, hη⟩ := endDiff_exists_lift s (i : (R : Type)) hi
  have hs : ∀ r, φ.1 (Dp.σ.1 r) = s.1 r := fun r => by rw [← hφ]; rfl
  have hf : ∀ a ∈ Dp.π.ker, φ.1.toLinearMap a ∈ π.ker := fun a ha => by
    obtain ⟨r, hr⟩ := endDiff_ηmap_surj Dp ⟨a, ha⟩
    have : a = Dp.σ.1 r * Dp.η := (congrArg Subtype.val hr).symm
    rw [this]
    change φ.1 (Dp.σ.1 r * Dp.η) ∈ RingHom.ker π.1
    rw [map_mul, hη]
    exact Ideal.mul_mem_left _ _ i.2
  have hA : gb l ⊗ₜ[R₀] i = LinearMap.lTensor B.gg (φ.1.toLinearMap.restrict hf)
      (gb l ⊗ₜ[R₀] Dp.ηk) := by
    rw [LinearMap.lTensor_tmul]
    congr 1
    exact Subtype.ext hη.symm
  have hB : ∑ k, gb k ⊗ₜ[R₀] m k = LinearMap.lTensor B.gg (φ.1.toLinearMap.restrict hf)
      (∑ k, gb k ⊗ₜ[R₀] Dp.ηmap (c l k)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.lTensor_tmul]
    congr 1
    refine Subtype.ext ?_
    change _ = φ.1 (Dp.σ.1 (c l k) * Dp.η)
    rw [hm k, map_mul, hη, hs]
  rw [hA, hB, B.tg_nat Dp.π π Dp.sqZero hπ φ hf, B.tg_nat Dp.π π Dp.sqZero hπ φ hf, ← hc l,
    ← e.nat, hφ]

private lemma endDiff_spec {g : ℕ} {B : BX R₀} {O : LAlg R₀} {gb : Module.Basis (Fin g) R₀ B.gg}
    {e : OEnd B O} {d : Matrix (Fin g) (Fin g) (O : Type)} (h : endDiff_IsMat gb e d)
    (Dp : DualPair O) (l : Fin g) (r : (O : Type)) :
    e.f Dp.σ (B.tg Dp.π Dp.sqZero (gb l ⊗ₜ[R₀] Dp.ηmap r)) =
      B.tg Dp.π Dp.sqZero (∑ k, gb k ⊗ₜ[R₀] Dp.ηmap (d k l * r)) :=
  h Dp.σ Dp.π Dp.sqZero l _ _ fun k => by
    change Dp.σ.1 (d k l * r) * Dp.η = Dp.σ.1 (d k l) * (Dp.σ.1 r * Dp.η)
    rw [map_mul, _root_.mul_assoc]

private lemma endDiff_unique {g : ℕ} {B : BX R₀} {O : LAlg R₀} {gb : Module.Basis (Fin g) R₀ B.gg}
    {e : OEnd B O} {d : Matrix (Fin g) (Fin g) (O : Type)} (h : endDiff_IsMat gb e d)
    (Dp : DualPair O) (d' : Matrix (Fin g) (Fin g) (O : Type))
    (h' : ∀ l, e.f Dp.σ (B.tg Dp.π Dp.sqZero (gb l ⊗ₜ[R₀] Dp.ηmap 1)) =
      B.tg Dp.π Dp.sqZero (∑ k, gb k ⊗ₜ[R₀] Dp.ηmap (d' k l))) : d = d' := by
  ext k l
  have h1 := B.tg_inj _ _ ((endDiff_spec h Dp l 1).symm.trans (h' l))
  have h2 := (endDiff_coord (M := Dp.π.ker) gb).1 h1
  simpa using endDiff_ηmap_inj Dp (congrFun h2 k)

theorem exists_endDifferential_ringHom :
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} (B : BX R₀) (O : LAlg R₀) (gb : Module.Basis (Fin g) R₀ B.gg) (O₀ : Type) [CommRing O₀] (f : O₀ → OEnd B O),
    (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R), (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) →
    ∃ dL : O₀ →+* Matrix (Fin g) (Fin g) (O : Type), (∀ a {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker),
      (∀ k, (m k : (R : Type)) = s.1 (dL a k l) * i) →
      (f a).f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k))) := by
  intro R₀ _ g B O gb O₀ _ f hf
  choose d hd using fun a => endDiff_exists gb (f a)
  let Dp := DualNum.dualPair O
  have hadd : ∀ a b, d (a + b) = d a + d b := fun a b =>
    endDiff_unique (hd _) Dp _ fun l => by
      rw [((hf _ _).2 a b).1, endDiff_spec (hd a), endDiff_spec (hd b), ← map_add,
        ← Finset.sum_add_distrib]
      simp [TensorProduct.tmul_add]
  have hone : d 1 = 1 :=
    endDiff_unique (hd _) Dp _ fun l => by
      rw [(hf _ _).1, Finset.sum_eq_single l]
      · simp
      · intro k _ hk
        simp [Matrix.one_apply_ne hk]
      · simp
  have hmul : ∀ a b, d (a * b) = d a * d b := fun a b =>
    endDiff_unique (hd _) Dp _ fun l => by
      rw [((hf _ _).2 a b).2, endDiff_spec (hd b), map_sum, map_sum]
      simp only [endDiff_spec (hd a)]
      rw [← map_sum, Finset.sum_comm]
      simp [Matrix.mul_apply, TensorProduct.tmul_sum]
  have hzero : d 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  exact ⟨⟨⟨⟨d, hone⟩, hmul⟩, hzero, hadd⟩, fun a => hd a⟩

end GlobalTheory
end
end

section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PadicOrderAction

def padicEnd (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] (hM : ∀ x : M, p • x = 0) :
    ℤ_[p] →+* AddMonoid.End M where
  toFun c := nsmulAddMonoidHom (PadicInt.toZMod c).val
  map_one' := by
    ext x
    change (PadicInt.toZMod (1 : ℤ_[p])).val • x = x
    rw [map_one, ZMod.val_one, one_nsmul]
  map_mul' a b := by
    ext x
    change (PadicInt.toZMod (a * b)).val • x = (PadicInt.toZMod a).val • (PadicInt.toZMod b).val • x
    rw [map_mul, ZMod.val_mul, ← nsmul_eq_mod_nsmul _ (hM x), mul_nsmul']
  map_zero' := by
    ext x
    change (PadicInt.toZMod (0 : ℤ_[p])).val • x = 0
    rw [map_zero, ZMod.val_zero, zero_nsmul]
  map_add' a b := by
    ext x
    change (PadicInt.toZMod (a + b)).val • x = (PadicInt.toZMod a).val • x + (PadicInt.toZMod b).val • x
    rw [map_add, ZMod.val_add, ← nsmul_eq_mod_nsmul _ (hM x), add_nsmul]


def liftInt {A B C : Type} [CommRing A] [CommRing B] [Ring C] (φ : A →+* C) (ψ : B →+* C)
    (h : ∀ a b, φ a * ψ b = ψ b * φ a) : A ⊗[ℤ] B →+* C :=
  (Algebra.TensorProduct.lift φ.toIntAlgHom ψ.toIntAlgHom h).toRingHom

lemma liftInt_tmul {A B C : Type} [CommRing A] [CommRing B] [Ring C] (φ : A →+* C) (ψ : B →+* C)
    (h : ∀ a b, φ a * ψ b = ψ b * φ a) (a : A) (b : B) : liftInt φ ψ h (a ⊗ₜ[ℤ] b) = φ a * ψ b :=
  Algebra.TensorProduct.lift_tmul φ.toIntAlgHom ψ.toIntAlgHom h a b

variable {R₀ : Type} [CommRing R₀]

lemma pTorsion_nsmul_eq_zero (B : BX R₀) (p : ℕ) (S : LAlg R₀) (x : torP B p S) : p • x = 0 :=
  Subtype.ext ((mem_torP B p _).1 x.2)

def resEnd {B : BX R₀} {O : LAlg R₀} (e : OEnd B O) (p : ℕ) {S : LAlg R₀} (s : LHom O S) :
    AddMonoid.End (torP B p S) :=
  ((e.f s).comp (torP B p S).subtype).codRestrict (torP B p S) fun x => by
    rw [mem_torP, ← map_nsmul, pTorsion_nsmul_eq_zero, map_zero]


def ordEnd {B : BX R₀} {O : LAlg R₀} {O₀ : Type} [CommRing O₀] (f : O₀ → OEnd B O) (p : ℕ)
    {S : LAlg R₀} (s : LHom O S)
    (h : ∀ x : B.G S, (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) : O₀ →+* AddMonoid.End (torP B p S) :=
  RingHom.mk' (α := O₀) (β := AddMonoid.End (torP B p S))
    { toFun := fun a => resEnd (f a) p s
      map_one' := AddMonoidHom.ext fun x => Subtype.ext (h x).1
      map_mul' := fun a b => AddMonoidHom.ext fun x => Subtype.ext ((h x).2 a b).2 }
    fun a b => AddMonoidHom.ext fun x => Subtype.ext ((h x).2 a b).1

def complEnd {B : BX R₀} {O : LAlg R₀} {O₀ : Type} [CommRing O₀] (f : O₀ → OEnd B O) (p : ℕ)
    [Fact p.Prime] {S : LAlg R₀} (s : LHom O S)
    (h : ∀ x : B.G S, (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) :
    ℤ_[p] ⊗[ℤ] O₀ →+* AddMonoid.End (torP B p S) :=
  liftInt (padicEnd p _ (pTorsion_nsmul_eq_zero B p S)) (ordEnd f p s h) fun c a =>
    AddMonoidHom.ext fun x => (map_nsmul (ordEnd f p s h a) (PadicInt.toZMod c).val x).symm

lemma complEnd_tmul {B : BX R₀} {O : LAlg R₀} {O₀ : Type} [CommRing O₀] (f : O₀ → OEnd B O) (p : ℕ)
    [Fact p.Prime] {S : LAlg R₀} (s : LHom O S)
    (h : ∀ x : B.G S, (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) (c : ℤ_[p]) (a : O₀) (x : torP B p S) :
    (complEnd f p s h (c ⊗ₜ[ℤ] a) x : B.G S) = (PadicInt.toZMod c).val • (f a).f s x := by
  have e : complEnd f p s h (c ⊗ₜ[ℤ] a) =
      padicEnd p _ (pTorsion_nsmul_eq_zero B p S) c * ordEnd f p s h a := liftInt_tmul _ _ _ c a
  rw [e]
  rfl

def complMat {g : ℕ} {O : Type} [CommRing O] {O₀ : Type} [CommRing O₀] (p : ℕ) [Fact p.Prime]
    [Algebra ℤ_[p] O] (dL : O₀ →+* Matrix (Fin g) (Fin g) O) :
    ℤ_[p] ⊗[ℤ] O₀ →+* Matrix (Fin g) (Fin g) O :=
  liftInt (algebraMap ℤ_[p] (Matrix (Fin g) (Fin g) O)) dL fun c a => Algebra.commutes c (dL a)

lemma complMat_tmul {g : ℕ} {O : Type} [CommRing O] {O₀ : Type} [CommRing O₀] (p : ℕ)
    [Fact p.Prime] [Algebra ℤ_[p] O] (dL : O₀ →+* Matrix (Fin g) (Fin g) O) (c : ℤ_[p]) (a : O₀) :
    complMat p dL (c ⊗ₜ[ℤ] a) = algebraMap ℤ_[p] O c • dL a := by
  rw [complMat, liftInt_tmul, algebraMap_smul]
  exact (Algebra.smul_def c (dL a)).symm

def kerMul {R S : LAlg R₀} (π : LHom R S) (r : (R : Type)) (i : π.ker) : π.ker :=
  ⟨r * i, Ideal.mul_mem_left (RingHom.ker π.1) r i.2⟩

lemma padic_mul_eq {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] (t : ℤ_[p] →+* R) (c : ℤ_[p])
    (i : R) (hi : p • i = 0) : t c * i = (PadicInt.toZMod c).val • i := by
  have h : c - ((PadicInt.toZMod c).val : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨d, hd⟩ := h
  have hc : c = d * p + ((PadicInt.toZMod c).val : ℤ_[p]) := by rw [hd]; ring
  rw [nsmul_eq_mul] at hi ⊢
  conv_lhs => rw [hc]
  rw [map_add, map_mul, map_natCast, map_natCast, add_mul, _root_.mul_assoc, hi, mul_zero, zero_add]

theorem main :
  (∀ {R₀ : Type} [CommRing R₀] {g : ℕ} (B : BX R₀) (O : LAlg R₀) (gb : Module.Basis (Fin g) R₀ B.gg) (O₀ : Type) [CommRing O₀] (f : O₀ → OEnd B O) (p : ℕ) [Fact p.Prime] [Algebra ℤ_[p] (O : Type)] (dL : O₀ →+* Matrix (Fin g) (Fin g) (O : Type)),
    Function.Surjective (algebraMap R₀ (O : Type)) → (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R), (f 1).f s x = x ∧ ∀ a b, (f (a + b)).f s x = (f a).f s x + (f b).f s x ∧
      (f (a * b)).f s x = (f a).f s ((f b).f s x)) →
    (∀ a {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker),
      (∀ k, (m k : (R : Type)) = s.1 (dL a k l) * i) →
      (f a).f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k)) →
    ∃ (A : OAct B O p (ℤ_[p] ⊗[ℤ] O₀)) (ρL : ℤ_[p] ⊗[ℤ] O₀ →+* Matrix (Fin g) (Fin g) (O : Type)),
      (∀ c a, ρL (c ⊗ₜ[ℤ] a) = algebraMap ℤ_[p] (O : Type) c • dL a) ∧
      (∀ a k l, ρL a k l = algebraMap R₀ (O : Type) (gb.repr (A.actL a (gb l)) k)) ∧
      ∀ c a (S : LAlg R₀) (s : LHom O S) (x : torP B p S), (A.act (c ⊗ₜ[ℤ] a) S s x : B.G S) = (PadicInt.toZMod c).val • (f a).f s x) := by
  intro R₀ _ g B O gb O₀ _ f p _ _ dL hs hf htg
  choose pre hpre using hs
  let L : ℤ_[p] ⊗[ℤ] O₀ → B.gg →ₗ[R₀] B.gg := fun a =>
    gb.constr R₀ fun l => ∑ k, pre (complMat p dL a k l) • gb k
  have hL : ∀ a l, L a (gb l) = ∑ k, pre (complMat p dL a k l) • gb k := fun a l =>
    gb.constr_basis R₀ _ l
  have key : ∀ a {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g)
      (i : π.ker) (hi : p • i = 0),
      (complEnd f p s (hf s) a ⟨B.tg π hπ (gb l ⊗ₜ i), tg_torP B p π hπ _ i hi⟩ : B.G R) =
        B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] kerMul π (s.1 (complMat p dL a k l)) i) := by
    intro a R S s π hπ l i hi
    induction a using TensorProduct.induction_on with
    | zero =>
      have : ∀ k, kerMul π (s.1 (complMat p dL 0 k l)) i = 0 := fun k =>
        Subtype.ext (by simp [kerMul])
      simp only [this]
      simp only [TensorProduct.tmul_zero, Finset.sum_const_zero, map_zero]
      rfl
    | tmul c a =>
      rw [complEnd_tmul]
      change _ • (f a).f s (B.tg π hπ (gb l ⊗ₜ i)) = _
      rw [htg a s π hπ l i (fun k => kerMul π (s.1 (dL a k l)) i) (fun k => rfl), ← map_nsmul,
        Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      refine (map_nsmul (TensorProduct.mk R₀ B.gg π.ker (gb k)) _ _).symm.trans ?_
      change gb k ⊗ₜ[R₀] _ = _
      congr 1
      apply Subtype.ext
      have hi' : p • (i : (R : Type)) = 0 := congrArg Subtype.val hi
      have h2 := padic_mul_eq (s.1.toRingHom.comp (algebraMap ℤ_[p] (O : Type))) c
        (s.1 (dL a k l) * i) (by rw [← mul_smul_comm, hi', mul_zero])
      change (PadicInt.toZMod c).val • (s.1 (dL a k l) * i) = s.1 (complMat p dL (c ⊗ₜ a) k l) * i
      rw [← h2, complMat_tmul, Matrix.smul_apply, smul_eq_mul, map_mul, _root_.mul_assoc]
      rfl
    | add a b ha hb =>
      have : ∀ k, kerMul π (s.1 (complMat p dL (a + b) k l)) i =
          kerMul π (s.1 (complMat p dL a k l)) i + kerMul π (s.1 (complMat p dL b k l)) i :=
        fun k => Subtype.ext (by simp [kerMul, add_mul])
      simp only [this, TensorProduct.tmul_add, Finset.sum_add_distrib]
      rw [map_add (B.tg π hπ), ← ha, ← hb, map_add]
      rfl
  have key2 : ∀ a {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g)
      (i : π.ker) (hi : p • i = 0),
      (complEnd f p s (hf s) a ⟨B.tg π hπ (gb l ⊗ₜ i), tg_torP B p π hπ _ i hi⟩ : B.G R) =
        B.tg π hπ (L a (gb l) ⊗ₜ[R₀] i) := by
    intro a R S s π hπ l i hi
    rw [key a s π hπ l i hi, hL, TensorProduct.sum_tmul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.smul_tmul]
    congr 1
    apply Subtype.ext
    change s.1 (complMat p dL a k l) * i = pre (complMat p dL a k l) • (i : (R : Type))
    rw [Algebra.smul_def, ← s.1.commutes, hpre]
  refine ⟨{ act := fun a S s => complEnd f p s (hf s) a
            act_one := fun S s x => by rw [map_one]; rfl
            act_mul := fun a b S s x => by rw [map_mul]; rfl
            act_add := fun a b S s x => by rw [map_add]; rfl
            act_nat := ?_
            actL := L
            act_tg := ?_ }, complMat p dL, complMat_tmul p dL, ?_,
            fun c a S s x => complEnd_tmul f p s (hf s) c a x⟩
  · intro a S S' s s' φ hφ x
    subst hφ
    change B.map φ (complEnd f p s (hf s) a x : B.G S) =
      (complEnd f p (φ.comp s) (hf _) a ⟨B.map φ x, map_torP B p φ x⟩ : B.G S')
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul c a => rw [complEnd_tmul, complEnd_tmul, map_nsmul, (f a).nat]
    | add a b ha hb =>
      rw [map_add, map_add]
      change B.map φ ((complEnd f p s (hf s) a x : B.G S) + (complEnd f p s (hf s) b x : B.G S)) = _
      rw [map_add, ha, hb]
      rfl
  · intro a R S s π hπ w i hi
    have hr : ∀ l, p • (gb.repr w l • i) = 0 := fun l => by rw [smul_comm, hi, smul_zero]
    have h1 : (⟨B.tg π hπ (w ⊗ₜ i), tg_torP B p π hπ w i hi⟩ : torP B p R) =
        ∑ l, ⟨B.tg π hπ (gb l ⊗ₜ (gb.repr w l • i)), tg_torP B p π hπ _ _ (hr l)⟩ := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finset_sum]
      change B.tg π hπ (w ⊗ₜ i) = ∑ l, B.tg π hπ (gb l ⊗ₜ (gb.repr w l • i))
      rw [← map_sum]
      congr 1
      conv_lhs => rw [← gb.sum_repr w, TensorProduct.sum_tmul]
      exact Finset.sum_congr rfl fun l _ => TensorProduct.smul_tmul _ _ _
    change (complEnd f p s (hf s) a ⟨B.tg π hπ (w ⊗ₜ i), tg_torP B p π hπ w i hi⟩ : B.G R) = _
    rw [h1, map_sum, AddSubmonoidClass.coe_finset_sum,
      Finset.sum_congr rfl fun l _ => key2 a s π hπ l _ (hr l), ← map_sum]
    congr 1
    conv_rhs => rw [← gb.sum_repr w, map_sum, TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl fun l _ => by rw [map_smul, TensorProduct.smul_tmul]
  · intro a k l
    change complMat p dL a k l = algebraMap R₀ (O : Type) (gb.repr (L a (gb l)) k)
    rw [hL, gb.repr_sum_self, hpre]

end GlobalTheory.PadicOrderAction
end
end

section
noncomputable section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FinOf

lemma finOf_idem {S : Type} [CommRing S] [IsLocalRing S] {x : S} (h : IsIdempotentElem x) :
    x = 0 ∨ x = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x with hu | hu
  · right
    exact hu.mul_left_cancel (by rw [_root_.mul_one]; exact h.eq)
  · left
    exact hu.mul_left_cancel (by rw [mul_zero]; exact h.one_sub_mul_self)

lemma finOf_local_of_comp {O Q S : Type} [CommRing O] [CommRing Q] [CommRing S] [IsLocalRing O]
    [IsLocalRing Q] [IsLocalRing S] [Algebra O Q] [Algebra.IsIntegral O Q] (g : Q →+* S)
    (h : IsLocalHom (g.comp (algebraMap O Q))) : IsLocalHom g := by
  have h1 : (maximalIdeal S).comap (g.comp (algebraMap O Q)) = maximalIdeal O :=
    ((local_hom_TFAE (g.comp (algebraMap O Q))).out 0 4).1 h
  have h2 : (((maximalIdeal S).comap g).comap (algebraMap O Q)).IsMaximal := by
    rw [Ideal.comap_comap, h1]; infer_instance
  have h3 := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ h2
  exact ((local_hom_TFAE g).out 4 0).1 (eq_maximalIdeal h3)

lemma finOf_local_algebraMap {O Q : Type} [CommRing O] [CommRing Q] [IsLocalRing O]
    [IsLocalRing Q] [Algebra O Q] [Algebra.IsIntegral O Q] : IsLocalHom (algebraMap O Q) :=
  ((local_hom_TFAE (algebraMap O Q)).out 4 0).1
    (eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal Q)))

variable {R₀ : Type} [CommRing R₀]

def finOf_fst (C : Type) [Field C] [Algebra R₀ C] :
    LHom (R₀ := R₀) ⟨DualNumber C⟩ ⟨C⟩ :=
  ⟨TrivSqZeroExt.fstHom R₀ C C, ⟨fun a h => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 h⟩⟩

lemma finOf_fst_sqZero (C : Type) [Field C] [Algebra R₀ C] : (finOf_fst (R₀ := R₀) C).SqZero := by
  refine ⟨fun c => ⟨TrivSqZeroExt.inl c, rfl⟩, ?_⟩
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro a ha b hb
  have ha' : TrivSqZeroExt.fst (a : DualNumber C) = 0 := ha
  have hb' : TrivSqZeroExt.fst (b : DualNumber C) = 0 := hb
  change (a * b : DualNumber C) = 0
  ext
  · simp [ha']
  · simp [ha', hb']

lemma finOf_tangent (B : BX R₀) (p : ℕ) (hp : p ≠ 0) (C : Type) [Field C] [CharZero C]
    [Algebra R₀ C] (z z' : B.G ⟨DualNumber C⟩) (hz : p • z = 0) (hz' : p • z' = 0)
    (h : B.map (finOf_fst C) z = B.map (finOf_fst C) z') : z = z' := by
  obtain ⟨v, hv⟩ := (B.tg_ker (finOf_fst C) (finOf_fst_sqZero C) (z - z')).1
    (by rw [map_sub, h, sub_self])
  have h1 : p • v = 0 := B.tg_inj (finOf_fst C) (finOf_fst_sqZero C)
    (by rw [map_nsmul, hv, smul_sub, hz, hz', sub_self, map_zero])
  have hinj : Function.Injective
      (p • LinearMap.id : (finOf_fst (R₀ := R₀) C).ker →ₗ[R₀] (finOf_fst (R₀ := R₀) C).ker) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have ha' : p • (a.1 : DualNumber C) = 0 := congrArg Subtype.val ha
    apply Subtype.ext
    have hpC : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hp
    rw [← Nat.cast_smul_eq_nsmul C] at ha'
    exact (smul_eq_zero.1 ha').resolve_left hpC
  have h2 := Module.Flat.lTensor_preserves_injective_linearMap (M := B.gg) _ hinj
  have h3 : v = 0 := h2 (by
    rw [map_zero, ← h1]
    have := map_nsmul (LinearMap.lTensorHom (R := R₀) B.gg) p
      (LinearMap.id : (finOf_fst (R₀ := R₀) C).ker →ₗ[R₀] (finOf_fst (R₀ := R₀) C).ker)
    simp only [LinearMap.coe_lTensorHom, LinearMap.lTensor_id] at this
    rw [this]; rfl)
  rw [h3, map_zero] at hv
  exact sub_eq_zero.1 hv.symm

lemma finOf_free {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A]
    [Module.Free O A] [Module.Finite O A] {n : ℕ} (ε : Fin n → A)
    (hε : CompleteOrthogonalIdempotents ε) :
    (∀ i, Module.Free O (A ⧸ Ideal.span {1 - ε i})) ∧
      (∑ i, Module.finrank O (A ⧸ Ideal.span {1 - ε i})) = Module.finrank O A := by
  let Q : Fin n → Type := fun i => A ⧸ Ideal.span {1 - ε i}
  let E : A ≃ₗ[O] (∀ i, Q i) :=
    LinearEquiv.ofBijective (LinearMap.pi fun i => (Ideal.Quotient.mkₐ O _).toLinearMap)
      hε.bijective_pi
  haveI hfree : ∀ i, Module.Free O (Q i) := fun i => by
    haveI : Module.Projective O (Q i) :=
      Module.Projective.of_split (M := A)
        (E.symm.toLinearMap ∘ₗ LinearMap.single O Q i) (LinearMap.proj i ∘ₗ E.toLinearMap)
        (LinearMap.ext fun x => by simp)
    exact Module.free_of_flat_of_isLocalRing
  refine ⟨hfree, ?_⟩
  rw [E.finrank_eq, Module.finrank_pi_fintype]

section Split

variable (O : LAlg R₀) {A : Type} [CommRing A] [Algebra (O : Type) A] [Algebra R₀ A]
  [IsScalarTower R₀ (O : Type) A]

def finOf_sO [Module.Finite (O : Type) A] (I : Ideal A) [IsLocalRing (A ⧸ I)] :
    LHom O ⟨A ⧸ I⟩ :=
  ⟨IsScalarTower.toAlgHom R₀ (O : Type) (A ⧸ I), finOf_local_algebraMap (O := O) (Q := A ⧸ I)⟩

lemma finOf_algOf [Module.Finite (O : Type) A] (I : Ideal A) [IsLocalRing (A ⧸ I)] :
    algOf (finOf_sO O I) = (inferInstance : Algebra (O : Type) (A ⧸ I)) :=
  Algebra.algebra_ext _ _ fun _ => rfl

lemma finOf_lift [Module.Finite (O : Type) A] (ε : A) [IsLocalRing (A ⧸ Ideal.span {1 - ε})]
    (S : LAlg R₀) (s : LHom O S) (φ : A →ₐ[R₀] S)
    (hφ : φ.comp (IsScalarTower.toAlgHom R₀ (O : Type) A) = s.1) (hε : φ ε = 1) :
    ∃ ψ : LHom ⟨A ⧸ Ideal.span {1 - ε}⟩ S, ψ.comp (finOf_sO O _) = s ∧
      ψ.1.comp (Ideal.Quotient.mkₐ R₀ _) = φ := by
  have hk : ∀ a ∈ Ideal.span {1 - ε}, φ a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_sub, map_one, hε, sub_self, mul_zero]
  let ψ : (A ⧸ Ideal.span {1 - ε}) →ₐ[R₀] S := Ideal.Quotient.liftₐ _ φ hk
  have hψ : ψ.comp (IsScalarTower.toAlgHom R₀ (O : Type) (A ⧸ Ideal.span {1 - ε})) = s.1 := by
    rw [← hφ]; rfl
  refine ⟨⟨ψ, finOf_local_of_comp (O := O) (ψ : (A ⧸ Ideal.span {1 - ε}) →+* S) ?_⟩,
    Subtype.ext hψ, by ext a; rfl⟩
  have : (ψ : (A ⧸ Ideal.span {1 - ε}) →+* S).comp (algebraMap (O : Type) _) = (s.1 : O →+* S) := by
    rw [← hψ]; rfl
  rw [this]; exact s.2

lemma finOf_split (B : BX R₀) (p : ℕ) [Module.Free (O : Type) A] [Module.Finite (O : Type) A]
    (pt : ∀ S : LAlg R₀, (A →ₐ[R₀] S) → B.G S)
    (pt_nat : ∀ {S S' : LAlg R₀} (f : LHom S S') (φ : A →ₐ[R₀] S),
      B.map f (pt S φ) = pt S' (f.1.comp φ))
    (pt_p : ∀ S φ, p • pt S φ = 0)
    (pt_univ : ∀ (S : LAlg R₀) (s : O →ₐ[R₀] S) (z : B.G S), p • z = 0 →
      ∃! φ : A →ₐ[R₀] S, φ.comp (IsScalarTower.toAlgHom R₀ (O : Type) A) = s ∧ pt S φ = z)
    (hsep : ∀ f : A, (∀ φ : A →ₐ[(O : Type)] O, φ f = 0) → f = 0)
    (hrank : Module.finrank (O : Type) A = Nat.card (A →ₐ[(O : Type)] O))
    {n : ℕ} (ε : Fin n → A) (hε : CompleteOrthogonalIdempotents ε)
    [hloc : ∀ i, IsLocalRing (A ⧸ Ideal.span {1 - ε i})] : Nonempty (FIN B O p) := by
  obtain ⟨hfree, h1⟩ := finOf_free (O := O) ε hε
  have hone : ∀ (S : LAlg R₀) (φ : A →ₐ[R₀] S), ∃ i, φ (ε i) = 1 := by
    intro S φ
    by_contra hcon
    have h0 : ∀ i, φ (ε i) = 0 := fun i =>
      (finOf_idem ((hε.idem i).map φ)).resolve_right fun h => hcon ⟨i, h⟩
    have h1 := congrArg φ hε.complete
    rw [map_sum, map_one, Finset.sum_eq_zero fun i _ => h0 i] at h1
    exact zero_ne_one h1
  have hmk : ∀ i, Ideal.Quotient.mk (Ideal.span {1 - ε i}) (ε i) = 1 := fun i => by
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {1 - ε i})), eq_comm, Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton_self _
  refine ⟨FIN.mk (Fin n) (fun i => ⟨A ⧸ Ideal.span {1 - ε i}⟩) (fun i => finOf_sO O _)
    (fun i => ?_) (fun i => pt _ (Ideal.Quotient.mkₐ R₀ _)) (fun i => pt_p _ _)
    (fun S s z hz => ?_) (fun i f hf => ?_) ?_⟩
  · rw [finOf_algOf]
    exact ⟨hfree i, inferInstance⟩
  · obtain ⟨φ, ⟨hφs, hφz⟩, huniq⟩ := pt_univ S s.1 z hz
    obtain ⟨i, hi⟩ := hone S φ
    obtain ⟨ψ, hψs, hψφ⟩ := finOf_lift O (ε i) S s φ hφs hi
    refine ⟨i, ψ, hψs, by rw [pt_nat, hψφ, hφz], fun j φ' h1 h2 => ?_⟩
    have h3 : φ'.1.comp (Ideal.Quotient.mkₐ R₀ _) = φ := by
      refine huniq _ ⟨?_, ?_⟩
      · rw [← h1]; rfl
      · rw [← h2, pt_nat]
    have hj : φ (ε j) = 1 := by
      rw [← h3]
      change φ'.1 (Ideal.Quotient.mk _ (ε j)) = 1
      rw [hmk, map_one]
    have hji : j = i := by
      by_contra hne
      have h4 := congrArg φ (hε.ortho hne)
      rw [map_mul, hi, hj, map_zero, _root_.mul_one] at h4
      exact one_ne_zero h4
    subst hji
    refine ⟨rfl, heq_of_eq (Subtype.ext ?_)⟩
    exact Ideal.Quotient.algHom_ext R₀ (h3.trans hψφ.symm)
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective f
    have h0 : a * ε i = 0 := by
      refine hsep _ fun φ => ?_
      rw [map_mul]
      rcases finOf_idem ((hε.idem i).map φ) with h | h
      · rw [h, mul_zero]
      · obtain ⟨ψ, hψs, hψφ⟩ := finOf_lift O (ε i) O (LHom.id O) (φ.restrictScalars R₀)
          (by ext r; exact φ.commutes r) h
        have h1 := hf ψ hψs
        have h2 : φ a = 0 := (AlgHom.congr_fun hψφ a).symm.trans h1
        rw [h2, zero_mul]
    refine Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton'.2 ⟨a, ?_⟩)
    rw [mul_sub, h0, sub_zero, _root_.mul_one]
  · have h2 : Nat.card (A →ₐ[(O : Type)] O) = Nat.card {t : B.G O // p • t = 0} := by
      refine Nat.card_congr (Equiv.ofBijective
        (fun φ => ⟨pt O (φ.restrictScalars R₀), pt_p _ _⟩) ⟨fun φ φ' h => ?_, fun t => ?_⟩)
      · have h' : pt O (φ.restrictScalars R₀) = pt O (φ'.restrictScalars R₀) :=
          congrArg Subtype.val h
        have := (pt_univ O (AlgHom.id R₀ O) _ (pt_p O (φ'.restrictScalars R₀))).unique
          (y₁ := φ.restrictScalars R₀) (y₂ := φ'.restrictScalars R₀)
          ⟨by ext r; exact φ.commutes r, h'⟩ ⟨by ext r; exact φ'.commutes r, rfl⟩
        exact AlgHom.restrictScalars_injective R₀ this
      · obtain ⟨φ, ⟨h1, h2⟩, -⟩ := pt_univ O (AlgHom.id R₀ O) t.1 t.2
        exact ⟨⟨φ.toRingHom, fun r => AlgHom.congr_fun h1 r⟩, Subtype.ext h2⟩
    rw [← h2, ← hrank, ← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [finOf_algOf]

lemma finOf_unram (B : BX R₀) (p : ℕ) (hp : p ≠ 0)
    (pt : ∀ S : LAlg R₀, (A →ₐ[R₀] S) → B.G S)
    (pt_nat : ∀ {S S' : LAlg R₀} (f : LHom S S') (φ : A →ₐ[R₀] S),
      B.map f (pt S φ) = pt S' (f.1.comp φ))
    (pt_p : ∀ S φ, p • pt S φ = 0)
    (pt_univ : ∀ (S : LAlg R₀) (s : O →ₐ[R₀] S) (z : B.G S), p • z = 0 →
      ∃! φ : A →ₐ[R₀] S, φ.comp (IsScalarTower.toAlgHom R₀ (O : Type) A) = s ∧ pt S φ = z)
    (C : Type) [Field C] [CharZero C] [Algebra (O : Type) C] [Algebra R₀ C]
    [IsScalarTower R₀ (O : Type) C] (φ φ' : A →ₐ[(O : Type)] DualNumber C)
    (h : ∀ a, (φ a).fst = (φ' a).fst) : φ = φ' := by
  let ψ : A →ₐ[R₀] DualNumber C := φ.restrictScalars R₀
  let ψ' : A →ₐ[R₀] DualNumber C := φ'.restrictScalars R₀
  have h1 : pt ⟨DualNumber C⟩ ψ = pt ⟨DualNumber C⟩ ψ' := by
    refine finOf_tangent B p hp C _ _ (pt_p _ _) (pt_p _ _) ?_
    rw [pt_nat, pt_nat]
    congr 1
    ext a
    exact h a
  have h2 : ψ.comp (IsScalarTower.toAlgHom R₀ (O : Type) A) =
      ψ'.comp (IsScalarTower.toAlgHom R₀ (O : Type) A) :=
    AlgHom.ext fun r => (φ.commutes r).trans (φ'.commutes r).symm
  have h3 : ψ = ψ' := (pt_univ ⟨DualNumber C⟩ (ψ'.comp (IsScalarTower.toAlgHom R₀ (O : Type) A)) _
    (pt_p ⟨DualNumber C⟩ ψ')).unique ⟨h2, h1⟩ ⟨rfl, rfl⟩
  exact AlgHom.ext fun a => AlgHom.congr_fun h3 a

end Split

theorem main :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (O : LAlg R₀) (p : ℕ), IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Flat ((𝟙 G) ^ p : G ⟶ G).left → Smooth G.hom →
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra (O : Type) A) (_ : Algebra R₀ A) (_ : IsScalarTower R₀ (O : Type) A),
      Module.Free (O : Type) A ∧ Module.Finite (O : Type) A ∧ ∃ y : sp (R₀ := R₀) A ⟶ G, y ^ p = 1 ∧
      ∀ (S : Type) [CommRing S] [Algebra (O : Type) S] [Algebra R₀ S] [IsScalarTower R₀ (O : Type) S] (z : sp (R₀ := R₀) S ⟶ G), z ^ p = 1 →
        ∃! φ : A →ₐ[(O : Type)] S, spMap (φ.restrictScalars R₀) ≫ y = z) →
  (∀ (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [Finite (A →ₐ[O] O)],
    (∀ f : A, (∀ φ : A →ₐ[O] O, φ f = 0) → f = 0) →
    ∃ (n : ℕ) (ε : Fin n → A), CompleteOrthogonalIdempotents ε ∧ ∀ i, IsLocalRing (A ⧸ Ideal.span {1 - ε i})) →
  (∀ (C O A : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [CommRing A] [Algebra O A] [Module.Free O A] [Module.Finite O A],
    (∀ φ φ' : A →ₐ[O] DualNumber C, (∀ a, (φ a).fst = (φ' a).fst) → φ = φ') →
    Finite (A →ₐ[O] O) ∧ (∀ f : A, (∀ φ : A →ₐ[O] O, φ f = 0) → f = 0) ∧ Module.finrank O A = Nat.card (A →ₐ[O] O)) →
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (O : LAlg R₀) (p : ℕ) (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) →
    (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) →
    IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Flat ((𝟙 G) ^ p : G ⟶ G).left → Smooth G.hom →
    ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) [Algebra (O : Type) C], v.Integers (O : Type) → p ≠ 0 →
    Nonempty (FIN B O p)) := by
  intro REP SPLIT ETA R₀ _ G _ _ O p B e hbij hadd hnat hfin hflat hsm C _ _ _ v _ hv hp
  obtain ⟨A, _, _, _, _, hAfree, hAfin, y, hy, huniv⟩ := REP G O p hfin hflat hsm
  have he0 : ∀ R, e R 0 = 1 := fun R => by
    have h := hadd R 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have hen : ∀ R (x : B.G R) (n : ℕ), e R (n • x) = e R x ^ n := fun R x n => by
    induction n with
    | zero => rw [zero_nsmul, pow_zero, he0]
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have htor : ∀ R (x : B.G R), p • x = 0 ↔ e R x ^ p = 1 := fun R x => by
    rw [← hen, ← he0 R, (hbij R).1.eq_iff]
  let pt : ∀ S : LAlg R₀, (A →ₐ[R₀] S) → B.G S := fun S φ =>
    (Equiv.ofBijective _ (hbij S)).symm (spMap φ ≫ y)
  have hpt : ∀ S φ, e S (pt S φ) = spMap φ ≫ y := fun S φ =>
    (Equiv.ofBijective _ (hbij S)).apply_symm_apply _
  have pt_nat : ∀ {S S' : LAlg R₀} (f : LHom S S') (φ : A →ₐ[R₀] S),
      B.map f (pt S φ) = pt S' (f.1.comp φ) := fun {S S'} f φ => (hbij S').1 (by
    rw [hnat, hpt, hpt, ← Category.assoc, spMap_comp])
  have pt_p : ∀ S φ, p • pt S φ = 0 := fun S φ => by
    rw [htor, hpt, ← MonObj.comp_pow, hy, MonObj.comp_one]
  have pt_univ : ∀ (S : LAlg R₀) (s : O →ₐ[R₀] S) (z : B.G S), p • z = 0 →
      ∃! φ : A →ₐ[R₀] S, φ.comp (IsScalarTower.toAlgHom R₀ (O : Type) A) = s ∧ pt S φ = z := by
    intro S s z hz
    letI : Algebra (O : Type) S := s.toRingHom.toAlgebra
    haveI : IsScalarTower R₀ (O : Type) S :=
      IsScalarTower.of_algebraMap_eq fun r => (s.commutes r).symm
    obtain ⟨φ, hφ, hu⟩ := huniv S (e S z) ((htor S z).1 hz)
    refine ⟨φ.restrictScalars R₀, ⟨by ext r; exact φ.commutes r, (hbij S).1 (by rw [hpt, hφ])⟩,
      fun φ' ⟨h1, h2⟩ => ?_⟩
    have h3 := hu ⟨φ'.toRingHom, fun r => AlgHom.congr_fun h1 r⟩ (by rw [← h2, hpt]; rfl)
    rw [← h3]; rfl
  letI : Algebra R₀ C := ((algebraMap (O : Type) C).comp (algebraMap R₀ (O : Type))).toAlgebra
  haveI : IsScalarTower R₀ (O : Type) C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨hfinite, hsep, hrank⟩ := ETA C O A v hv
    (finOf_unram O B p hp pt pt_nat pt_p pt_univ C)
  obtain ⟨n, ε, hε, hloc⟩ := SPLIT O A hsep
  exact finOf_split O B p pt pt_nat pt_p pt_univ hsep hrank ε hε

end GlobalTheory.FinOf
end
end

section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PeriodDatum

theorem exists_basis_of_card (p : ℕ) [hp : Fact p.Prime] (g : ℕ) (V : Type) [AddCommGroup V]
    [Module (ZMod p) V] (hcV : Nat.card V = p ^ (2 * g)) :
    ∃ f : Ix g → V, ∀ x : V, ∃! t : Ix g → ZMod p, x = ∑ j, (t j).val • f j := by
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hcV]; exact pow_ne_zero _ hp.out.ne_zero)
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hrk : Module.finrank (ZMod p) V = Fintype.card (Ix g) := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [hcV, Nat.card_zmod] at h
    have h2 := Nat.pow_right_injective hp.out.two_le h
    rw [← h2, Fintype.card_sum, Fintype.card_fin, two_mul]
  let b : Module.Basis (Ix g) (ZMod p) V :=
    (Module.finBasisOfFinrankEq (ZMod p) V hrk).reindex (Fintype.equivFin (Ix g)).symm
  have hsm : ∀ (t : ZMod p) (y : V), t.val • y = t • y := fun t y => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
  refine ⟨b, fun x => ⟨b.equivFun x, ?_, fun t ht => ?_⟩⟩
  · simp only [hsm]
    rw [← b.equivFun_symm_apply, LinearEquiv.symm_apply_apply]
  · simp only [hsm] at ht
    rw [← b.equivFun_symm_apply] at ht
    rw [ht, LinearEquiv.apply_symm_apply]

theorem exists_compatible_basis (p : ℕ) [hp : Fact p.Prime] (g : ℕ) (Γ : Type) [AddCommGroup Γ]
    (hdiv : ∀ x : Γ, ∃ y, p • y = x) (hcard : Nat.card {x : Γ // p • x = 0} = p ^ (2 * g)) :
    ∃ τ : Ix g → ℕ → Γ, (∀ i n, (p ^ (n + 1)) • τ i n = 0) ∧ (∀ i n, τ i n = p • τ i (n + 1)) ∧
      ∀ x : Γ, p • x = 0 → ∃! t : Ix g → ZMod p, x = ∑ j, (t j).val • τ j 0 := by
  obtain ⟨V, hV⟩ : ∃ V : AddSubgroup Γ, ∀ x : Γ, x ∈ V ↔ p • x = 0 :=
    ⟨(nsmulAddMonoidHom p : Γ →+ Γ).ker, fun x => Iff.rfl⟩
  have hcV : Nat.card V = p ^ (2 * g) :=
    (Nat.card_congr (Equiv.subtypeEquivRight hV)).trans hcard
  obtain ⟨b, hb⟩ := @exists_basis_of_card p _ g V _
    (AddCommGroup.zmodModule (fun x => Subtype.ext ((hV _).1 x.2))) hcV
  choose d hd using hdiv
  let τ : Ix g → ℕ → Γ := fun i n => d^[n] (b i : Γ)
  have hτp : ∀ i n, τ i n = p • τ i (n + 1) := fun i n => by
    simp only [τ, Function.iterate_succ_apply', hd]
  have hsum : ∀ t : Ix g → ZMod p, ((∑ j, (t j).val • b j : V) : Γ) = ∑ j, (t j).val • τ j 0 :=
    fun t => by
      rw [AddSubmonoidClass.coe_finset_sum]
      rfl
  refine ⟨τ, fun i n => ?_, hτp, fun x hx => ?_⟩
  · induction n with
    | zero => rw [zero_add, pow_one]; exact (hV _).1 (b i).2
    | succ n ih => rw [pow_succ, mul_smul, ← hτp i n, ih]
  · obtain ⟨t, ht, hu⟩ := hb ⟨x, (hV x).2 hx⟩
    refine ⟨t, ?_, fun t' ht' => hu t' (Subtype.ext ?_)⟩
    · exact (congrArg Subtype.val ht).trans (hsum t)
    · exact ht'.trans (hsum t').symm

theorem main :
  (∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) (g : ℕ)
    (G : Over (Spec (CommRingCat.of (Ainf.R0 p O ε)))) [GrpObj G] [IsCommMonObj G] (B : BX (Ainf.R0 p O ε))
    (e : ∀ R : LAlg (Ainf.R0 p O ε), B.G R → (sp (R₀ := (Ainf.R0 p O ε)) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) →
    (∀ {R S : LAlg (Ainf.R0 p O ε)} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) →
    SmoothOfRelativeDimension g G.hom → IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Flat ((𝟙 G) ^ p : G ⟶ G).left →
    (∀ x : B.G (Ainf.ainfTowerL p O hv ε hε).O, ∃ y, p • y = x) → Nat.card {x : B.G (Ainf.ainfTowerL p O hv ε hε).O // p • x = 0} = p ^ (2 * g) →
    (∀ x : B.G (Ainf.ainfTowerL p O hv ε hε).O, p • x = 0 → (∀ y : B.G (Ainf.ainfTowerL p O hv ε hε).O, p • y = 0 → B.IsPairing p x y 1) → x = 0) →
    ∀ [Algebra ℤ_[p] ((Ainf.ainfTowerL p O hv ε hε).O : Type)] (O₀ : Type) [CommRing O₀] (cj : O₀ ≃ₐ[ℤ] O₀) (Ad : O₀ → OAdj B (Ainf.ainfTowerL p O hv ε hε).O),
    (∀ a, (Ad a).ab = (Ad (cj a)).a) → (∀ a, cj (cj a) = a) →
    (∀ {R : LAlg (Ainf.R0 p O ε)} (s : LHom (Ainf.ainfTowerL p O hv ε hε).O R) (x : B.G R), (Ad 1).a.f s x = x ∧ ∀ a b, (Ad (a + b)).a.f s x = (Ad a).a.f s x + (Ad b).a.f s x ∧
      (Ad (a * b)).a.f s x = (Ad a).a.f s ((Ad b).a.f s x)) →
    ∃ (Dt : DualTower (Ainf.ainfTowerL p O hv ε hε)) (D : Dat p g B (Ainf.ainfTowerL p O hv ε hε) Dt (ℤ_[p] ⊗[ℤ] O₀) (Algebra.TensorProduct.congr (AlgEquiv.refl : ℤ_[p] ≃ₐ[ℤ_[p]] ℤ_[p]) cj) (Ainf.ainfTowerL p O hv ε hε).c),
      D.H.P = 0 ∧ D.H.PL = 0 ∧
      (∀ a {R S : LAlg (Ainf.R0 p O ε)} (s : LHom (Ainf.ainfTowerL p O hv ε hε).O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker),
      (∀ k, (m k : (R : Type)) = s.1 (D.H.ρL (1 ⊗ₜ[ℤ] a) k l) * i) →
      (Ad a).a.f s (B.tg π hπ (D.ch.gb l ⊗ₜ[(Ainf.R0 p O ε)] i)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[(Ainf.R0 p O ε)] m k)) ∧
      ∀ a j n, (Ad a).a.f (LHom.id (Ainf.ainfTowerL p O hv ε hε).O) (D.L.τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (D.H.ρ (1 ⊗ₜ[ℤ] a) k j)).val • D.L.τ k n) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε g G _ _ B e hbij hadd hnat hsm hfin hflat hdiv hcard hperf
    _ O₀ _ cj Ad hab hcj hAd
  haveI : IsLocalRing (Ainf.R0 p O ε) := WdAinf.ainf_thetaQuotRing_isLocalRing p O hv ε hε
  haveI : IsDomain ((Ainf.ainfTowerL p O hv ε hε).O : Type) := Ainf.ainfTower_isDomain p O hv ε hε
  have hsm' : Smooth G.hom := SmoothOfRelativeDimension.smooth g G.hom
  obtain ⟨K, wd, hnil, hK, hKl⟩ :=
    GlobalTheory.wData_ainfTower_exists GlobalTheory.WittQuot.teichmuller_quot p O hv ε hε
  obtain ⟨ch⟩ := GlobalTheory.FormalChartOf.exists_formalChart GlobalTheory.NilCoord.nilpotent_coordinates
    (GlobalTheory.ChLaw.groupLaw_powerSeries GlobalTheory.nEval_basic
      (GlobalTheory.exists_series_of_natural_on_nilpotent GlobalTheory.nEval_basic))
    G g B e hbij hadd hnat hsm K hK hKl
  have sm := GlobalTheory.SmoothNilLift.main G B e hbij hadd hnat hsm' K wd.W wd.ρW hnil
  obtain ⟨fin⟩ := @GlobalTheory.FinOf.main GlobalTheory.finRep_kernel_mul_finite_free GlobalTheory.finite_algebra_split_local
    GlobalTheory.finEtale_main _ _ G _ _ (Ainf.ainfTowerL p O hv ε hε).O p B e hbij hadd hnat hfin hflat hsm'
    C _ _ _ v (inferInstanceAs (Algebra O C)) hv (Fact.out : p.Prime).ne_zero
  obtain ⟨Dt⟩ := GlobalTheory.exists_dualTower (Ainf.ainfTowerL p O hv ε hε)
  obtain ⟨τ, hτ, hτp, hbas⟩ := exists_compatible_basis p g _ hdiv hcard
  obtain ⟨dL, hdL⟩ := GlobalTheory.exists_endDifferential_ringHom B _ ch.gb O₀ (fun a => (Ad a).a) hAd
  obtain ⟨A, H, L, hP, hPL, hL, hρL, hρ⟩ := GlobalTheory.exists_tateMatrices_link GlobalTheory.tate_basis_matrix
    GlobalTheory.tateBasis_gram GlobalTheory.PadicOrderAction.main B (Ainf.ainfTowerL p O hv ε hε) Dt ch.gb O₀ cj Ad dL
    (WdAinf.thetaBar_surj p O hv ε hε) hab hcj hAd hdL
    (fun n => Ideal.mk_ker (I := Ideal.span {(p : O) ^ (n + 1)}))
    (fun n => IsPrimitiveRoot.coe_units_iff.1 (Ainf.zeta_primitive p O hv ε hε n))
    (fun n => Units.ext (Ainf.zeta_succ_pow p O ε n))
    τ hτ hτp hbas hperf
  refine ⟨Dt,
    { K := K
      ρO := wd.ρ1.comp ((Ainf.ainfTowerL p O hv ε hε).q 0)
      ch := ch
      wd := wd
      ρO_eq := rfl
      sm := sm
      fin := fin
      A := A
      H := H
      L := L
      tower_zero_surjective := surjective_ainfTower_zero p O hv ε hε
      tower_zero_ker := ker_ainfTower_zero p O hv ε hε
      zeta0 := ainf_zeta0 p O hv ε hε }, hP, hPL, ?_, ?_⟩
  · intro a R S s π hπ l i m hm
    exact hdL a s π hπ l i m (fun k => by rw [hm k]; exact congrArg (fun M => s.1 (M k l) * (i : (R : Type))) (hρL a))
  · intro a j n
    subst hL
    exact hρ a j n

end GlobalTheory.PeriodDatum
end
end
