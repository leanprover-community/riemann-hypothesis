import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanUnitaryWeightsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDetCharInvariantsLeSpanProdMaximalMinorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSFockColumnSubstitutionUnitary
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralDetCharacterFockColumnSubstitutionEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv

section
open Classical MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockS_fockColumnSubstitution_unitary : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (u : ι → Matrix.unitaryGroup (Fin a) ℂ) (P Q : GlobalTheory.MinorFrame.Pol ι d a),
  Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.colSub (fun τ => (u τ : Matrix (Fin a) (Fin a) ℂ)) P)
    (GlobalTheory.MinorFrame.colSub (fun τ => (u τ : Matrix (Fin a) (Fin a) ℂ)) Q) = Formalism.L2.DIV.fockS P Q := by
  first | exact @GlobalTheory.MinorFrame.fockS_colSub_unitary | exact GlobalTheory.MinorFrame.fockS_colSub_unitary | (intros; apply GlobalTheory.MinorFrame.fockS_colSub_unitary <;> assumption)
end

section
section
open Classical MeasureTheory

noncomputable section

namespace GlobalTheory.UnitaryAvg

open MvPolynomial GlobalTheory.MinorFrame
open scoped Pointwise

variable {ι : Type} [Fintype ι]

theorem colSub_comp {d a : ℕ} (u v : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    colSub u (colSub v P) = colSub (fun τ => u τ * v τ) P := by
  have h : (colSub (d := d) u).comp (colSub v) = colSub (fun τ => u τ * v τ) := by
    apply MvPolynomial.algHom_ext
    intro y
    simp only [AlgHom.comp_apply, colSub, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq, Matrix.mul_apply,
      Finset.sum_mul, Finset.mul_sum, C_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  exact congrArg (fun φ : Pol ι d a →ₐ[ℂ] Pol ι d a => φ P) h

theorem colSub_one {d a : ℕ} (P : Pol ι d a) :
    colSub (fun _ : ι => (1 : Matrix (Fin a) (Fin a) ℂ)) P = P := by
  have h : (colSub (d := d) (fun _ : ι => (1 : Matrix (Fin a) (Fin a) ℂ))) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro y
    simp [colSub, Matrix.one_apply]
  rw [h]; rfl

theorem support_colSub_bdd {d a : ℕ} (P : Pol ι d a) :
    ∃ S : Finset (Var ι d a →₀ ℕ), ∀ u : ι → Matrix (Fin a) (Fin a) ℂ, (colSub u P).support ⊆ S := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨(C c : Pol ι d a).support, fun u => by rw [algHom_C]; rfl⟩
  | add p q hp hq =>
    obtain ⟨S, hS⟩ := hp
    obtain ⟨T, hT⟩ := hq
    exact ⟨S ∪ T, fun u => by rw [map_add]; exact support_add.trans (Finset.union_subset_union (hS u) (hT u))⟩
  | mul_X p y hp =>
    obtain ⟨S, hS⟩ := hp
    refine ⟨S + Finset.univ.image (fun j : Fin a => Finsupp.single (y.1, y.2.1, j) 1), fun u => ?_⟩
    rw [map_mul]
    refine (support_mul _ _).trans (Finset.add_subset_add (hS u) ?_)
    simp only [colSub, aeval_X]
    refine support_sum.trans ?_
    intro m hm
    simp only [Finset.mem_biUnion] at hm
    obtain ⟨j, _, hj⟩ := hm
    rw [C_mul_X_eq_monomial] at hj
    have := support_monomial_subset hj
    rw [Finset.mem_singleton] at this
    exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, this.symm⟩

section Meas

variable {K : Type} [Group K] [MeasurableSpace K] {a d : ℕ}

theorem coeff_colSub_good (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ))
    (hρ : ∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) (P : Pol ι d a) :
    ∀ m, Measurable (fun g => coeff m (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P)) ∧
      ∃ C : ℝ, ∀ g, ‖coeff m (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P)‖ ≤ C := by
  have hmul : ∀ p q : Pol ι d a,
      (∀ m, Measurable (fun g => coeff m (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) p)) ∧
        ∃ C : ℝ, ∀ g, ‖coeff m (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) p)‖ ≤ C) →
      (∀ m, Measurable (fun g => coeff m (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) q)) ∧
        ∃ C : ℝ, ∀ g, ‖coeff m (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) q)‖ ≤ C) →
      (∀ m, Measurable (fun g => coeff m (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) (p * q))) ∧
        ∃ C : ℝ, ∀ g, ‖coeff m (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) (p * q))‖ ≤ C) := by
    intro p q hp hq m
    have hpb : ∀ m, ∃ C : ℝ, ∀ g, ‖coeff m (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) p)‖ ≤ C :=
      fun m => (hp m).2
    have hqb : ∀ m, ∃ C : ℝ, ∀ g, ‖coeff m (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) q)‖ ≤ C :=
      fun m => (hq m).2
    choose Cp hCp using hpb
    choose Cq hCq using hqb
    simp only [map_mul, coeff_mul]
    refine ⟨Finset.measurable_sum _ fun x _ => (hp x.1).1.mul (hq x.2).1, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, Cp x.1 * Cq x.2,
      fun g => ?_⟩
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    refine (norm_mul_le _ _).trans ?_
    exact mul_le_mul (hCp _ g) (hCq _ g) (norm_nonneg _) ((norm_nonneg _).trans (hCp _ g))
  intro m
  induction P using MvPolynomial.induction_on generalizing m with
  | C c =>
    simp only [algHom_C, algebraMap_eq]
    exact ⟨measurable_const, _, fun _ => le_rfl⟩
  | add p q hp hq =>
    simp only [map_add, coeff_add]
    obtain ⟨hpm, Cp, hCp⟩ := hp m
    obtain ⟨hqm, Cq, hCq⟩ := hq m
    exact ⟨hpm.add hqm, Cp + Cq, fun g => (norm_add_le _ _).trans (add_le_add (hCp g) (hCq g))⟩
  | mul_X p y hp =>
    refine hmul p (X y) hp (fun m' => ?_) m
    simp only [colSub, aeval_X, coeff_sum, coeff_C_mul]
    refine ⟨Finset.measurable_sum _ fun j _ => (hρ _ _ _).mul measurable_const,
      ∑ j : Fin a, ‖coeff m' (X (y.1, y.2.1, j) : Pol ι d a)‖, fun g => ?_⟩
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (entry_norm_bound_of_unitary (ρ g y.1).2 _ _)

end Meas

end GlobalTheory.UnitaryAvg

namespace GlobalTheory.UnitaryAvg

open MvPolynomial GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι] {K : Type} [Group K] [MeasurableSpace K] {a d : ℕ}

def Mg (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)) (g : K) : ι → Matrix (Fin a) (Fin a) ℂ :=
  fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)

def cc (n : ι → ℕ) (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)) (g : K) : ℂ :=
  ∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(n τ : ℤ))

theorem det_unitary_norm (U : Matrix.unitaryGroup (Fin a) ℂ) : ‖(U : Matrix (Fin a) (Fin a) ℂ).det‖ = 1 :=
  CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary U.2)

theorem det_unitary_ne_zero (U : Matrix.unitaryGroup (Fin a) ℂ) : (U : Matrix (Fin a) (Fin a) ℂ).det ≠ 0 := by
  intro h
  have := det_unitary_norm U
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem norm_cc (n : ι → ℕ) (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)) (g : K) : ‖cc n ρ g‖ = 1 := by
  rw [cc, norm_prod]
  exact Finset.prod_eq_one fun τ _ => by rw [norm_zpow, det_unitary_norm, one_zpow]

theorem Mg_mul (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)) (g0 g : K) :
    Mg ρ (g0 * g) = fun τ => Mg ρ g0 τ * Mg ρ g τ := by
  funext τ
  simp only [Mg, map_mul]
  rfl

theorem cc_mul (n : ι → ℕ) (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)) (g0 g : K) :
    cc n ρ g = detChar n (Mg ρ g0) * cc n ρ (g0 * g) := by
  have h := Mg_mul ρ g0 g
  simp only [cc, detChar]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hτ : (ρ (g0 * g) τ : Matrix (Fin a) (Fin a) ℂ) = Mg ρ g0 τ * Mg ρ g τ := congrFun h τ
  have h0 : (Mg ρ g0 τ).det ≠ 0 := det_unitary_ne_zero _
  rw [hτ, Matrix.det_mul, mul_zpow, ← mul_assoc, zpow_neg ((Mg ρ g0 τ).det), zpow_natCast,
    mul_inv_cancel₀ (pow_ne_zero _ h0), one_mul]
  rfl

theorem measurable_det (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ))
    (hρ : ∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) (τ : ι) :
    Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det := by
  simp only [Matrix.det_apply']
  exact Finset.measurable_sum _ fun σ _ => measurable_const.mul (Finset.measurable_prod _ fun i _ => hρ _ _ _)

theorem measurable_cc (n : ι → ℕ) (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ))
    (hρ : ∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) : Measurable (cc n ρ) := by
  unfold cc
  refine Finset.measurable_prod _ fun τ _ => ?_
  simp only [zpow_neg, zpow_natCast]
  exact ((measurable_det ρ hρ τ).pow_const _).inv

theorem integrable_term (ν : Measure K) [IsProbabilityMeasure ν] (n : ι → ℕ)
    (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ))
    (hρ : ∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) (P : Pol ι d a) (m : Var ι d a →₀ ℕ) :
    Integrable (fun g => cc n ρ g * coeff m (colSub (Mg ρ g) P)) ν := by
  obtain ⟨hm, C, hC⟩ := coeff_colSub_good ρ hρ P m
  refine Integrable.of_bound ((measurable_cc n ρ hρ).mul hm).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun g => ?_)
  rw [norm_mul, norm_cc, one_mul]
  exact hC g

theorem integral_eq_lin (ν : Measure K) [IsProbabilityMeasure ν] (n : ι → ℕ)
    (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ))
    (hρ : ∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) (P : Pol ι d a)
    (S : Finset (Var ι d a →₀ ℕ)) (hS : ∀ u, (colSub u P).support ⊆ S) (ℓ : Pol ι d a →ₗ[ℂ] ℂ) :
    ∫ g, cc n ρ g * ℓ (colSub (Mg ρ g) P) ∂ν =
      ℓ (∑ m ∈ S, monomial m (∫ g, cc n ρ g * coeff m (colSub (Mg ρ g) P) ∂ν)) := by
  have hmono : ∀ (m : Var ι d a →₀ ℕ) (c : ℂ), ℓ (monomial m c) = c * ℓ (monomial m 1) := by
    intro m c
    have : (monomial m c : Pol ι d a) = c • monomial m 1 := by rw [smul_monomial, smul_eq_mul, mul_one]
    rw [this, map_smul, smul_eq_mul]
  have hexp : ∀ Q : Pol ι d a, Q.support ⊆ S → ℓ Q = ∑ m ∈ S, coeff m Q * ℓ (monomial m 1) := by
    intro Q hQ
    conv_lhs => rw [Q.as_sum]
    rw [Finset.sum_subset hQ (fun m _ hm => by rw [notMem_support_iff.1 hm, monomial_zero]), map_sum]
    exact Finset.sum_congr rfl fun m _ => hmono m _
  have hL : ∀ g, cc n ρ g * ℓ (colSub (Mg ρ g) P) =
      ∑ m ∈ S, (cc n ρ g * coeff m (colSub (Mg ρ g) P)) * ℓ (monomial m 1) := by
    intro g
    rw [hexp _ (hS _), Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hL),
    integral_finset_sum _ (fun m _ => (integrable_term ν n ρ hρ P m).mul_const _), map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_mul_const]
  exact (hmono m _).symm

theorem integral_mul_left_inv (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] (F : K → ℂ)
    (hF : Measurable F) (g0 : K) : ∫ g, F (g0 * g) ∂ν = ∫ g, F g ∂ν := by
  have hmap : ν.map (g0 * ·) = ν := map_mul_left_eq_self ν g0
  have hae : AEMeasurable (g0 * ·) ν := by
    by_contra h
    have h0 := Measure.map_of_not_aemeasurable h
    rw [hmap] at h0
    exact IsProbabilityMeasure.ne_zero ν h0
  have := integral_map hae hF.aestronglyMeasurable (μ := ν)
  rw [hmap] at this
  exact this.symm

theorem avg_perp : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) {K : Type} [Group K] [MeasurableSpace K] (ν : Measure K), IsProbabilityMeasure ν → ν.IsMulLeftInvariant →
  ∀ (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)), (∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) →
    Function.Surjective ρ →
  ∀ (Λ : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] ℂ) (P : GlobalTheory.MinorFrame.Pol ι d a),
    (∀ I ∈ GlobalTheory.MinorFrame.inv a d n, Formalism.L2.DIV.fockS I P = 0) →
    ∫ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(n τ : ℤ))) *
      Λ (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P) ∂ν = 0 := by
  intro ι _ a d n K _ _ ν hν hinv ρ hρ hsurj Λ P hP
  obtain ⟨S, hS⟩ := support_colSub_bdd P
  set Q : Pol ι d a := ∑ m ∈ S, monomial m (∫ g, cc n ρ g * coeff m (colSub (Mg ρ g) P) ∂ν) with hQdef
  have hav : ∀ ℓ : Pol ι d a →ₗ[ℂ] ℂ, ∫ g, cc n ρ g * ℓ (colSub (Mg ρ g) P) ∂ν = ℓ Q :=
    fun ℓ => integral_eq_lin ν n ρ hρ P S hS ℓ
  have hcoef : ∀ m, coeff m Q = ∫ g, cc n ρ g * coeff m (colSub (Mg ρ g) P) ∂ν :=
    fun m => (hav (lcoeff ℂ m)).symm
  have hQinv : Q ∈ inv a d n := by
    intro u
    obtain ⟨g0, rfl⟩ := hsurj u
    change colSub (Mg ρ g0) Q = detChar n (Mg ρ g0) • Q
    ext m
    rw [coeff_smul, smul_eq_mul]
    have h1 := hav ((lcoeff ℂ m).comp (colSub (Mg ρ g0)).toLinearMap)
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, lcoeff_apply] at h1
    rw [← h1, hcoef m]
    have hF : Measurable fun g => cc n ρ g * coeff m (colSub (Mg ρ g) P) :=
      (measurable_cc n ρ hρ).mul (coeff_colSub_good ρ hρ P m).1
    rw [← integral_mul_left_inv ν _ hF g0, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only
    rw [colSub_comp, ← Mg_mul, cc_mul n ρ g0 g]
    ring
  have horth : ∀ I ∈ inv a d n, Formalism.L2.DIV.fockS I Q = 0 := by
    intro I hI
    have key : ∀ g, Formalism.L2.DIV.fockS I (colSub (Mg ρ g) P) = 0 := by
      intro g
      have hIu : colSub (fun τ => ((ρ g)⁻¹ τ : Matrix (Fin a) (Fin a) ℂ)) I =
          detChar n (fun τ => ((ρ g)⁻¹ τ : Matrix (Fin a) (Fin a) ℂ)) • I := hI (ρ g)⁻¹
      have hI' : colSub (Mg ρ g) (colSub (fun τ => ((ρ g)⁻¹ τ : Matrix (Fin a) (Fin a) ℂ)) I) = I := by
        rw [colSub_comp]
        have h1 : (fun τ => Mg ρ g τ * ((ρ g)⁻¹ τ : Matrix (Fin a) (Fin a) ℂ)) = fun _ => (1 : Matrix (Fin a) (Fin a) ℂ) := by
          funext τ
          simp [Mg]
        rw [h1, colSub_one]
      rw [← hI', show Mg ρ g = fun τ => ((ρ g τ : Matrix.unitaryGroup (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) from rfl, GlobalTheory.T.fockS_fockColumnSubstitution_unitary, hIu, ← Formalism.L2.DIV.fockL_apply, LinearMap.map_smulₛₗ₂,
        Formalism.L2.DIV.fockL_apply, hP I hI, smul_zero]
    rw [← Formalism.L2.DIV.fockL_apply, ← hav]
    simp only [Formalism.L2.DIV.fockL_apply, key, mul_zero, integral_zero]
  have hQ0 : Q = 0 := by
    by_contra hne
    have := fockS_self_re_pos hne
    rw [horth Q hQinv, Complex.zero_re] at this
    exact lt_irrefl _ this
  change ∫ g, cc n ρ g * Λ (colSub (Mg ρ g) P) ∂ν = 0
  rw [hav Λ, hQ0, map_zero]

end GlobalTheory.UnitaryAvg
end
end

open Classical MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAverage_kills_fock_complement_relInvariants : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) {K : Type} [Group K] [MeasurableSpace K] (ν : Measure K), IsProbabilityMeasure ν → ν.IsMulLeftInvariant →
  ∀ (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)), (∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) →
    Function.Surjective ρ →
  ∀ (Λ : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] ℂ) (P : GlobalTheory.MinorFrame.Pol ι d a),
    (∀ I ∈ GlobalTheory.MinorFrame.inv a d n, Formalism.L2.DIV.fockS I P = 0) →
    ∫ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(n τ : ℤ))) *
      Λ (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P) ∂ν = 0 := by
  atlas_forward_decl GlobalTheory.UnitaryAvg.avg_perp
end

section
open Classical MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_detCharacter_fockColumnSubstitution_eq_zero : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (m : ι → ℤ) (τ₀ : ι), 0 < a → 0 < m τ₀ → ∀ {K : Type} [Group K] [MeasurableSpace K] (ν : Measure K), IsProbabilityMeasure ν → ν.IsMulLeftInvariant →
  ∀ (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)), (∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) →
    Function.Surjective ρ →
  ∀ (Λ : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] ℂ) (P : GlobalTheory.MinorFrame.Pol ι d a),
    ∫ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) *
      Λ (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P) ∂ν = 0 := by
  first | exact @GlobalTheory.MinorFrame.integral_detZpow_colSub_eq_zero | exact GlobalTheory.MinorFrame.integral_detZpow_colSub_eq_zero | (intros; apply GlobalTheory.MinorFrame.integral_detZpow_colSub_eq_zero <;> assumption)
end

section
section
open Classical MeasureTheory

noncomputable section

open MvPolynomial

namespace GlobalTheory.MinorFrame.RatProj

section Form

variable {σ : Type}

def fockQ (f g : MvPolynomial σ ℚ) : ℚ :=
  ∑ m ∈ f.support, f.coeff m * g.coeff m * (Formalism.L2.DIV.mfact m : ℚ)

theorem fockQ_eq_sum (f g : MvPolynomial σ ℚ) (s : Finset (σ →₀ ℕ)) (hs : f.support ⊆ s) :
    fockQ f g = ∑ m ∈ s, f.coeff m * g.coeff m * (Formalism.L2.DIV.mfact m : ℚ) := by
  refine Finset.sum_subset hs ?_
  intro m _ hm
  rw [notMem_support_iff.mp hm]
  simp

def fockQL : MvPolynomial σ ℚ →ₗ[ℚ] MvPolynomial σ ℚ →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ fockQ
    (by
      intro f f' g
      rw [fockQ_eq_sum (f + f') g (f.support ∪ f'.support) support_add,
        fockQ_eq_sum f g (f.support ∪ f'.support) Finset.subset_union_left,
        fockQ_eq_sum f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [coeff_add]; ring)
    (by
      intro c f g
      rw [fockQ_eq_sum (c • f) g f.support support_smul, fockQ, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [coeff_smul, smul_eq_mul]; ring)
    (by
      intro f g g'
      simp only [fockQ, coeff_add, mul_add, add_mul, Finset.sum_add_distrib])
    (by
      intro c f g
      simp only [fockQ, coeff_smul, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring)

theorem fockQL_apply (f g : MvPolynomial σ ℚ) : fockQL f g = fockQ f g := rfl

theorem fockS_map (f g : MvPolynomial σ ℚ) :
    Formalism.L2.DIV.fockS (map (algebraMap ℚ ℂ) f) (map (algebraMap ℚ ℂ) g) = (fockQ f g : ℂ) := by
  rw [Formalism.L2.DIV.fockS_eq_sum _ _ f.support (support_map_subset _ _), fockQ]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [coeff_map]

theorem eq_zero_of_fockQ_self {f : MvPolynomial σ ℚ} (h : fockQ f f = 0) : f = 0 := by
  by_contra hf
  have hf' : map (algebraMap ℚ ℂ) f ≠ 0 := by
    intro h0
    apply hf
    exact map_injective _ (algebraMap ℚ ℂ).injective (by rw [h0, map_zero])
  have := GlobalTheory.MinorFrame.fockS_self_re_pos hf'
  rw [fockS_map, h] at this
  simp at this

end Form

variable {ι : Type} [Fintype ι]

def prodMinorsQ {a d : ℕ} {n : ι → ℕ} (T : Tup ι a d n) : MvPolynomial (Var ι d a) ℚ :=
  ∏ τ, ∏ j, (Matrix.of fun i i' : Fin a => (X (τ, (T τ j).1 i, i') : MvPolynomial (Var ι d a) ℚ)).det

theorem map_prodMinorsQ {a d : ℕ} {n : ι → ℕ} (T : Tup ι a d n) :
    map (algebraMap ℚ ℂ) (prodMinorsQ T) = prodMinors T := by
  simp only [prodMinorsQ, prodMinors, minorAt, map_prod]
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun j _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext i i'
  simp

theorem exists_rat_proj : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (k : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
  ∃ (M : ℕ) (r : Fin M → ℚ) (U : Fin M → GlobalTheory.MinorFrame.Tup ι a d n), ∀ T : GlobalTheory.MinorFrame.Tup ι a d n,
    Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.prodMinors T)
      (MvPolynomial.monomial k 1 - ∑ p, ((r p : ℚ) : ℂ) • GlobalTheory.MinorFrame.prodMinors (U p)) = 0 := by
  intro ι _ a d n k
  let PQ : Tup ι a d n → MvPolynomial (Var ι d a) ℚ := fun T => prodMinorsQ T
  let W := Submodule.span ℚ (Set.range PQ)
  haveI : FiniteDimensional ℚ W := FiniteDimensional.span_of_finite ℚ (Set.finite_range PQ)
  let ψ : W →ₗ[ℚ] Module.Dual ℚ W := (fockQL (σ := Var ι d a)).flip.compl₁₂ W.subtype W.subtype
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    have h1 : ψ w w = 0 := by rw [LinearMap.mem_ker.mp hw]; rfl
    have h2 : fockQ (w : MvPolynomial (Var ι d a) ℚ) w = 0 := h1
    exact Subtype.ext (eq_zero_of_fockQ_self h2)
  have hsurj : Function.Surjective ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hinj
  obtain ⟨w₀, hw₀⟩ := hsurj ((fockQL.flip (monomial k (1 : ℚ))).comp W.subtype)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 w₀.2
  let e : Fin (Fintype.card (Tup ι a d n)) ≃ Tup ι a d n := (Fintype.equivFin _).symm
  refine ⟨Fintype.card (Tup ι a d n), fun p => c (e p), fun p => e p, fun T => ?_⟩
  have hsum : (∑ p, ((c (e p) : ℚ) : ℂ) • prodMinors (e p)) =
      map (algebraMap ℚ ℂ) (w₀ : MvPolynomial (Var ι d a) ℚ) := by
    rw [e.sum_comp (fun T => ((c T : ℚ) : ℂ) • prodMinors T), ← hc, map_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    simp only [PQ]
    rw [smul_eq_C_mul (prodMinorsQ T) (c T), map_mul, map_C, map_prodMinorsQ, smul_eq_C_mul]
    simp
  have hmon : (monomial k (1 : ℂ)) = map (algebraMap ℚ ℂ) (monomial k (1 : ℚ)) := by simp [map_monomial]
  rw [hsum, ← map_prodMinorsQ T, hmon, ← map_sub, fockS_map, ← fockQL_apply, map_sub]
  have h3 := LinearMap.congr_fun hw₀ ⟨PQ T, Submodule.subset_span ⟨T, rfl⟩⟩
  have h4 : fockQL (PQ T) (w₀ : MvPolynomial (Var ι d a) ℚ) = fockQL (PQ T) (monomial k 1) := h3
  simp only [PQ] at h4
  rw [h4, sub_self, Rat.cast_zero]

end GlobalTheory.MinorFrame.RatProj
end
end

open Classical MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_fock_projection_maximal_minors : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (k : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
  ∃ (M : ℕ) (r : Fin M → ℚ) (U : Fin M → GlobalTheory.MinorFrame.Tup ι a d n), ∀ T : GlobalTheory.MinorFrame.Tup ι a d n,
    Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.prodMinors T)
      (MvPolynomial.monomial k 1 - ∑ p, ((r p : ℚ) : ℂ) • GlobalTheory.MinorFrame.prodMinors (U p)) = 0 := by
  atlas_forward_decl GlobalTheory.MinorFrame.RatProj.exists_rat_proj
end

section
section
noncomputable section

open Classical MeasureTheory MvPolynomial

namespace GlobalTheory.MinorFrame.AvgCore

variable {ι : Type} [Fintype ι] {a d : ℕ}

theorem continuous_colSub_mul (Λ : Pol ι d a →ₗ[ℂ] ℂ) (P : Pol ι d a) : ∀ Q : Pol ι d a,
    Continuous (fun G : ι → Fin a → Fin a → ℂ => Λ (colSub (fun τ => Matrix.of (G τ)) P * Q)) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    intro Q
    have h : ∀ G : ι → Fin a → Fin a → ℂ, colSub (d := d) (fun τ => Matrix.of (G τ)) (C c) = C c := by
      intro G; simp [colSub, MvPolynomial.algebraMap_eq]
    simp only [h]
    exact continuous_const
  | add p q hp hq =>
    intro Q
    simp only [map_add, add_mul]
    exact (hp Q).add (hq Q)
  | mul_X p y hp =>
    intro Q
    have h : ∀ G : ι → Fin a → Fin a → ℂ, Λ (colSub (fun τ => Matrix.of (G τ)) (p * X y) * Q) =
        ∑ j' : Fin a, G y.1 j' y.2.2 * Λ (colSub (fun τ => Matrix.of (G τ)) p * (X (y.1, y.2.1, j') * Q)) := by
      intro G
      have hX : colSub (d := d) (fun τ => Matrix.of (G τ)) (X y) =
          ∑ j' : Fin a, C (G y.1 j' y.2.2) * X (y.1, y.2.1, j') := by
        simp [colSub]
      rw [map_mul (colSub (fun τ => Matrix.of (G τ))) p (X y), hX, Finset.mul_sum, Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show colSub (fun τ => Matrix.of (G τ)) p * (C (G y.1 j y.2.2) * X (y.1, y.2.1, j)) * Q =
          C (G y.1 j y.2.2) * (colSub (fun τ => Matrix.of (G τ)) p * (X (y.1, y.2.1, j) * Q)) by ring,
        ← smul_eq_C_mul, map_smul, smul_eq_mul]
    simp only [h]
    refine continuous_finset_sum _ fun j _ => ?_
    exact Continuous.mul (by fun_prop) (hp _)

theorem norm_det_unitary (u : Matrix.unitaryGroup (Fin a) ℂ) : ‖(u : Matrix (Fin a) (Fin a) ℂ).det‖ = 1 := by
  exact CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary u.2)

theorem integrable_avg {K : Type} [Group K] [MeasurableSpace K] (ν : Measure K) [IsFiniteMeasure ν]
    (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ))
    (hmeas : ∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) (z : ι → ℤ)
    (Λ : Pol ι d a →ₗ[ℂ] ℂ) (P : Pol ι d a) :
    Integrable (fun g => (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (z τ)) *
      Λ (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P)) ν := by
  let F : (ι → Fin a → Fin a → ℂ) → ℂ := fun G => Λ (colSub (fun τ => Matrix.of (G τ)) P)
  have hF : Continuous F := by simpa [F] using continuous_colSub_mul Λ P 1
  let e : K → (ι → Fin a → Fin a → ℂ) := fun g τ i j => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j
  have he : Measurable e := measurable_pi_lambda _ fun τ => measurable_pi_lambda _ fun i =>
    measurable_pi_lambda _ fun j => hmeas τ i j
  have hFe : ∀ g, Λ (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P) = F (e g) := fun g => rfl
  have hdetc : ∀ τ, Continuous fun G : ι → Fin a → Fin a → ℂ => (Matrix.of (G τ)).det :=
    fun τ => Continuous.matrix_det (continuous_apply τ)
  have hdete : ∀ g τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det = (Matrix.of (e g τ)).det := fun g τ => rfl
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ι → Fin a → Fin a → ℂ) 1).exists_bound_of_continuousOn hF.continuousOn
  have hball : ∀ g, e g ∈ Metric.closedBall (0 : ι → Fin a → Fin a → ℂ) 1 := by
    intro g
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun τ => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i =>
      (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => entry_norm_bound_of_unitary (ρ g τ).2 i j
  refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun g => ?_)
  · refine Measurable.aestronglyMeasurable ?_
    simp only [hFe, hdete]
    refine Measurable.mul ?_ (hF.measurable.comp he)
    refine Finset.measurable_prod _ fun τ _ => ?_
    exact Measurable.pow_const ((hdetc τ).measurable.comp he) _
  · rw [norm_mul, norm_prod]
    simp only [norm_zpow, norm_det_unitary, one_zpow, Finset.prod_const_one, one_mul, hFe]
    exact hC _ (hball g)

theorem average_monomial_eq_sum_prodMinors : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (m : ι → ℤ), ∃ n : ι → ℕ,
  ∀ {K : Type} [Group K] [MeasurableSpace K] (ν : Measure K), IsProbabilityMeasure ν → ν.IsMulLeftInvariant →
  ∀ (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)), (∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) → Function.Surjective ρ →
  ∀ (Λ : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] ℂ) (k : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
  ∃ (M : ℕ) (r : Fin M → ℂ) (U : Fin M → GlobalTheory.MinorFrame.Tup ι a d n), (∀ p, IsAlgebraic ℚ (r p)) ∧
    ∫ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) *
      Λ (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) (MvPolynomial.monomial k 1)) ∂ν =
    ∑ p, r p * Λ (GlobalTheory.MinorFrame.prodMinors (U p)) := by
  intro ι _ a d m
  refine ⟨fun τ => (-m τ).toNat, ?_⟩
  intro K _ _ ν hP hInv ρ hmeas hsurj Λ k
  haveI := hP
  by_cases hpos : 0 < a ∧ ∃ τ₀, 0 < m τ₀
  · obtain ⟨ha, τ₀, hτ₀⟩ := hpos
    refine ⟨0, Fin.elim0, Fin.elim0, fun p => p.elim0, ?_⟩
    rw [GlobalTheory.T.integral_detCharacter_fockColumnSubstitution_eq_zero a d m τ₀ ha hτ₀ ν hP hInv ρ hmeas hsurj Λ _]
    simp
  obtain ⟨M, r, U, hR⟩ := GlobalTheory.T.exists_rational_fock_projection_maximal_minors (ι := ι) a d (fun τ => (-m τ).toNat) k
  refine ⟨M, fun p => ((r p : ℚ) : ℂ), U, fun p => isAlgebraic_ratCast ℚ (r p), ?_⟩
  set R : Pol ι d a := MvPolynomial.monomial k 1 - ∑ p, ((r p : ℚ) : ℂ) • prodMinors (U p) with hRdef
  have hperp : ∀ I ∈ inv a d (fun τ => (-m τ).toNat), Formalism.L2.DIV.fockS I R = 0 := by
    intro I hI
    have hspan := GlobalTheory.T.fockDetCharInvariants_le_span_prodMaximalMinors a d (fun τ => (-m τ).toNat) hI
    clear hI
    show Formalism.L2.DIV.fockL I R = 0
    induction hspan using Submodule.span_induction with
    | mem x hx => obtain ⟨T, rfl⟩ := hx; exact hR T
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smulₛₗ, LinearMap.smul_apply, hx, smul_zero]
  have h0 := GlobalTheory.T.unitaryAverage_kills_fock_complement_relInvariants a d (fun τ => (-m τ).toNat) ν hP hInv ρ hmeas hsurj Λ R hperp
  have hdet0 : ∀ g τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ≠ 0 := fun g τ => by
    rw [← norm_ne_zero_iff, norm_det_unitary]; exact one_ne_zero
  have hD : ∀ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) =
      ∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ)) := by
    intro g
    refine Finset.prod_congr rfl fun τ _ => ?_
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      simp [Matrix.det_fin_zero]
    · have hm : m τ ≤ 0 := by
        by_contra h
        exact hpos ⟨ha, τ, by omega⟩
      rw [Int.toNat_of_nonneg (by omega), neg_neg]
  have hinv : ∀ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ))) *
      detChar (fun τ => (-m τ).toNat) (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) = 1 := by
    intro g
    unfold detChar
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ (hdet0 g τ))]
  have hmono : MvPolynomial.monomial k 1 = ∑ p, ((r p : ℚ) : ℂ) • prodMinors (U p) + R := by
    rw [hRdef]; abel
  have hpoint : ∀ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) *
      Λ (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) (MvPolynomial.monomial k 1)) =
      ∑ p, ((r p : ℚ) : ℂ) * Λ (prodMinors (U p)) +
        (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ))) *
          Λ (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) R) := by
    intro g
    rw [hD g, hmono, map_add, map_sum, map_add, map_sum, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul, colSub_prodMinors, smul_smul, map_smul, smul_eq_mul]
    rw [show (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ))) *
        ((((r p : ℚ) : ℂ) * detChar (fun τ => (-m τ).toNat) (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ))) *
          Λ (prodMinors (U p))) =
        ((∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ))) *
          detChar (fun τ => (-m τ).toNat) (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ))) *
          (((r p : ℚ) : ℂ) * Λ (prodMinors (U p))) by ring, hinv g, one_mul]
  refine (integral_congr_ae (Filter.Eventually.of_forall hpoint)).trans ?_
  rw [integral_add (integrable_const _) (integrable_avg ν ρ hmeas _ Λ R), integral_const, h0]
  simp

end GlobalTheory.MinorFrame.AvgCore
end
end

open Classical MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.average_det_char_monomial_eq_sum_prod_minors : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (m : ι → ℤ), ∃ n : ι → ℕ,
  ∀ {K : Type} [Group K] [MeasurableSpace K] (ν : Measure K), IsProbabilityMeasure ν → ν.IsMulLeftInvariant →
  ∀ (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)), (∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) → Function.Surjective ρ →
  ∀ (Λ : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] ℂ) (k : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
  ∃ (M : ℕ) (r : Fin M → ℂ) (U : Fin M → GlobalTheory.MinorFrame.Tup ι a d n), (∀ p, IsAlgebraic ℚ (r p)) ∧
    ∫ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) *
      Λ (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) (MvPolynomial.monomial k 1)) ∂ν =
    ∑ p, r p * Λ (GlobalTheory.MinorFrame.prodMinors (U p)) := by
  atlas_forward_decl GlobalTheory.MinorFrame.AvgCore.average_monomial_eq_sum_prodMinors
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

theorem GlobalTheory.RealProj.avg_monomial : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ n : D.what₂.Tau → ℕ, ∀ (κ : Measure (GinfC A')), κ.IsMulLeftInvariant → IsProbabilityMeasure κ →
      ∀ (t : T), ∀ x ∈ GfC A', ∀ h ∈ GfC WW, ∀ k : FVar D WW.rank A'.rank →₀ ℕ,
        ∃ (m : ℕ) (r : Fin m → ℂ) (U : Fin m → GlobalTheory.NormSum.Tup D A'.rank WW.rank n), (∀ p, IsAlgebraic ℚ (r p)) ∧
          ∫ g, X.ker' W.ψ W.θ t (MvPolynomial.monomial k 1) h (x * (g : GA D A')) ∂κ =
            ∑ p, r p * X.ker' W.ψ W.θ t (GlobalTheory.NormSum.minorPol D (U p)) h x := by
  intro D T _ L μ₀ sc G W i j A A' WW X hPr hInp hL hB
  obtain ⟨m, ρ, hρm, hρs, hact⟩ := GlobalTheory.T.exists_archimedean_unitary_weights hPr hInp hL hB
  obtain ⟨n, hn⟩ := GlobalTheory.T.average_det_char_monomial_eq_sum_prod_minors (ι := D.what₂.Tau) A'.rank WW.rank m
  refine ⟨n, fun κ hκ hκp t x hx h hh k => ?_⟩
  let Λ : GlobalTheory.MinorFrame.Pol D.what₂.Tau WW.rank A'.rank →ₗ[ℂ] ℂ :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : WO A' WW => ℂ) 0).comp
      ((X.ω' t (x, h)).comp (pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (X.f' t)))
  have hΛ : ∀ P, Λ P = X.ker' W.ψ W.θ t P h x := fun P => rfl
  obtain ⟨M, r, U, hr, hI⟩ := hn κ hκp hκ ρ hρm hρs Λ k
  refine ⟨M, r, U, hr, ?_⟩
  have e : (fun g : GinfC A' => X.ker' W.ψ W.θ t (MvPolynomial.monomial k 1) h (x * (g : GA D A'))) =
      fun g => (∏ τ, (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ).det ^ (m τ)) *
        Λ (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) (MvPolynomial.monomial k 1)) := by
    funext g; rw [hact t x hx h hh g, hΛ]
  rw [e, hI]
  rfl

end
end
