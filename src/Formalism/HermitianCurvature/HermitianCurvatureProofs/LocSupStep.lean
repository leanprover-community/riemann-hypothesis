import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCStep
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCStmt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LatticeSummability
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelSizesJointMean
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PeriodLatticeFactsSplitOfGeneral
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalConditionsAndQuotientSplitting
import Lemmata.GeneralBFactRightSide.Imports
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstNormRealNonneg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PairingTriangular
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PsdFormConjRewrite
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualCovolumeChangeOfVariables
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PoissonJointFirstReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleWordMemBoundedLetterLists

section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology NumberField MeasureTheory
open scoped Pointwise

noncomputable section

open Classical

namespace Lat

theorem rd_ge_one (E : Type) [Field E] [NumberField E] : 1 ≤ S6.rd E := by
  unfold S6.rd
  apply Real.one_le_rpow _ (by positivity)
  have h := NumberField.discr_ne_zero E
  have : (1 : ℤ) ≤ |discr E| := Int.one_le_abs h
  exact_mod_cast this

theorem sizesSup : PBC.SizesSup := by
  intro Cs hCs
  refine ⟨Cs, hCs, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ S hg1 hg2 hU b n hb hn hthr
  obtain ⟨-, hcard, hdeg⟩ := Formalism.FourierDecayAlt.P.degreeFacts_statement E
  have hf : S.f = S6.deg E := by
    rw [← hcard, ← Fintype.card_fin S.f]; exact Fintype.card_congr S.pl
  have hfpos : 0 < S.f := hf ▸ hdeg
  have : Nonempty (Fin S.f) := ⟨⟨0, hfpos⟩⟩
  have hgN : 0 < S.g := Nat.mul_pos hg1 hg2
  have hg1R : (1 : ℝ) ≤ S.g := by exact_mod_cast hgN
  have hgR : (0 : ℝ) < S.g := by linarith
  have hrd1 := rd_ge_one E
  have hrd : 0 < S6.rd E := by linarith
  obtain ⟨-, -, -, -, -, -, hN, -⟩ := Formalism.FourierDecayAlt.P.block_lattices Formalism.FourierDecayAlt.P.lattice_facts_general
    Formalism.FourierDecayAlt.P.dualIdealEqLiftIdeal Formalism.FourierDecayAlt.P.scaledIdealNorm E hU S.g S.G.r b n hgN
  set ν : ℤ := S6.nuBlock S.G.r b n with hν
  set x : ℝ := S6.rd E ^ ν with hx
  have hxpos : 0 < x := zpow_pos hrd _
  have hexp : ((2 * S.G.r + 4 : ℤ) - 2 * b - n) = ν + 1 := by
    simp only [hν, S6.nuBlock]; ring
  rw [hexp, zpow_add₀ hrd.ne', zpow_one] at hN
  set m : ℝ := Finset.univ.inf' Finset.univ_nonempty (thr S b n) with hm
  have hmpos : 0 < m := by
    rw [hm, Finset.lt_inf'_iff]; exact fun v _ => hthr v
  have hmle : ∀ v, m ≤ thr S b n v := fun v => Finset.inf'_le _ (Finset.mem_univ v)
  refine ⟨S.g / m, div_pos hgR hmpos, ?_⟩
  set R : ℝ := S.g / m with hR
  have hRpos : 0 < R := div_pos hgR hmpos

  set Nn : ℝ := (FractionalIdeal.absNorm (S6.dualIdl E S.g ν) : ℝ) with hNn
  have hNn0 : 0 ≤ Nn := by
    have : 0 < √Nn := by rw [hN]; positivity
    exact (Real.sqrt_pos.mp this).le
  have hNinv : Nn⁻¹ = ((S.g : ℝ) * (x * S6.rd E)) ^ (2 * S.f) := by
    have h2 : Nn = (√Nn) ^ 2 := (Real.sq_sqrt hNn0).symm
    rw [h2, hN, ← hf]
    rw [inv_pow, inv_inv, ← pow_mul, mul_comm S.f 2]

  have hvol : S.base.vol b n = (∏ v, thr S b n v) ^ 2 * Nn⁻¹ := by
    simp only [C.HidaSetting.base, C.HidaSetting.mkData, thr]
    rw [div_eq_mul_inv]
    congr 2
    exact (Equiv.prod_comp S.pl (fun w => J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b n w)).symm
  have hdlB : KB.dlB S b n = x ^ 2 * (S6.rd E * (S.g : ℝ) ^ 3 / 2) := by
    have e : S6.rd E ^ (2 * ν) = x ^ 2 := by rw [hx, ← zpow_natCast, ← zpow_mul]; ring_nf
    simp only [KB.dlB, D.deG]
    rw [← hν, e]
    field_simp
  rw [hvol, hNinv, hdlB]

  have key : ∀ v, x ^ 2 * (S6.rd E * (S.g : ℝ) ^ 3 / 2) * (Cs * (1 + (R * thr S b n v / S.g) ^ 2)) / R ^ 2 ≤
      Cs * (thr S b n v ^ 2 * ((S.g : ℝ) * (x * S6.rd E)) ^ 2) := by
    intro v
    have ht := hthr v
    have h1 : (1 + (R * thr S b n v / S.g) ^ 2) / R ^ 2 ≤ 2 * thr S b n v ^ 2 / (S.g : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hR' : R * m = S.g := by rw [hR]; field_simp
      have hmt : m ^ 2 ≤ thr S b n v ^ 2 := pow_le_pow_left₀ hmpos.le (hmle v) 2
      have : (S.g : ℝ) ^ 2 ≤ R ^ 2 * thr S b n v ^ 2 := by
        rw [← hR']; nlinarith [sq_nonneg R]
      have e : (1 + (R * thr S b n v / S.g) ^ 2) * (S.g : ℝ) ^ 2 =
          (S.g : ℝ) ^ 2 + R ^ 2 * thr S b n v ^ 2 := by field_simp
      rw [e] <;> nlinarith
    calc x ^ 2 * (S6.rd E * (S.g : ℝ) ^ 3 / 2) * (Cs * (1 + (R * thr S b n v / S.g) ^ 2)) / R ^ 2
        = x ^ 2 * (S6.rd E * (S.g : ℝ) ^ 3 / 2) * Cs * ((1 + (R * thr S b n v / S.g) ^ 2) / R ^ 2) := by ring
      _ ≤ x ^ 2 * (S6.rd E * (S.g : ℝ) ^ 3 / 2) * Cs * (2 * thr S b n v ^ 2 / (S.g : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Cs * (thr S b n v ^ 2 * ((S.g : ℝ) * (x * S6.rd E)) ^ 2) * (1 / ((S.g : ℝ) * S6.rd E)) := by
          field_simp
      _ ≤ Cs * (thr S b n v ^ 2 * ((S.g : ℝ) * (x * S6.rd E)) ^ 2) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_one (by positivity)] <;> nlinarith
      _ = _ := mul_one _
  calc (∏ _v : Fin S.f, x ^ 2 * (S6.rd E * (S.g : ℝ) ^ 3 / 2)) *
        (∏ v, Cs * (1 + (R * thr S b n v / S.g) ^ 2)) / R ^ (2 * S.f)
      = ∏ v, x ^ 2 * (S6.rd E * (S.g : ℝ) ^ 3 / 2) * (Cs * (1 + (R * thr S b n v / S.g) ^ 2)) / R ^ 2 := by
        conv_rhs => rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [pow_mul]
    _ ≤ ∏ v, Cs * (thr S b n v ^ 2 * ((S.g : ℝ) * (x * S6.rd E)) ^ 2) :=
        Finset.prod_le_prod (fun v _ => by have := hthr v; positivity) (fun v _ => key v)
    _ = Cs ^ S.f * ((∏ v, thr S b n v) ^ 2 * ((S.g : ℝ) * (x * S6.rd E)) ^ (2 * S.f)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ← pow_mul, mul_comm 2 S.f]

theorem psi_add {f : ℕ} (a b : crystallineComparison.V f) : crystallineComparison.psi (a + b) = crystallineComparison.psi a * crystallineComparison.psi b := by
  unfold crystallineComparison.psi
  rw [← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp only [Pi.add_apply, map_add]
  ring

theorem psi_zero {f : ℕ} : crystallineComparison.psi (0 : crystallineComparison.V f) = 1 := by simp [crystallineComparison.psi]

theorem psi_single {f : ℕ} (v : Fin f) (w : ℂ) :
    crystallineComparison.psi (Pi.single v w : crystallineComparison.V f) = Complex.exp (2 * Real.pi * Complex.I * (w + (starRingEnd ℂ) w)) := by
  unfold crystallineComparison.psi
  congr 2
  rw [Finset.sum_eq_single v]
  · simp
  · intro u _ hu; simp [hu]
  · simp

theorem mul_single {f : ℕ} (σ : crystallineComparison.V f) (v : Fin f) (w : ℂ) :
    σ * (Pi.single v w : crystallineComparison.V f) = Pi.single v (σ v * w) := by
  funext u
  by_cases h : u = v
  · subst h; simp
  · simp [h]

theorem exp_eq_one_iff_int (x : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) = 1 ↔ ∃ n : ℤ, x = n := by
  first | exact Bl.general_b_fact_right_side.goal1 .. | (apply Bl.general_b_fact_right_side.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_side.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_side.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right_side.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_side.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_right_side.goal1 x

theorem add_conj (w : ℂ) : w + (starRingEnd ℂ) w = ((2 * w.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp; ring

def gen (f : ℕ) (R : ℝ) (p : Fin f × Bool) : crystallineComparison.V f :=
  Pi.single p.1 (if p.2 then (R : ℂ) * Complex.I else (R : ℂ))

theorem lstd_eq (f : ℕ) (R : ℝ) : Lstd f R = Submodule.span ℤ (Set.range (gen f R)) := rfl

def kerPsi {f : ℕ} (σ : crystallineComparison.V f) : AddSubgroup (crystallineComparison.V f) where
  carrier := {z | crystallineComparison.psi (σ * z) = 1}
  zero_mem' := by simp [psi_zero]
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [mul_add, psi_add, ha, hb, one_mul]
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have h := psi_add (σ * -a) (σ * a)
    rw [← mul_add, neg_add_cancel, mul_zero, psi_zero, ha, mul_one] at h
    exact h.symm

theorem mem_dual_iff (f : ℕ) (R : ℝ) (hR : 0 < R) (σ : crystallineComparison.V f) :
    σ ∈ crystallineComparison.dualSet (Lstd f R) ↔
      ∀ v, ∃ a b : ℤ, σ v = ((a : ℂ) + (b : ℂ) * Complex.I) / (2 * (R : ℂ)) := by
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hgen : ∀ v (β : Bool), crystallineComparison.psi (σ * gen f R (v, β)) = 1 ↔
      ∃ n : ℤ, (if β then -(2 * R * (σ v).im) else 2 * R * (σ v).re) = n := by
    intro v β
    rw [gen, mul_single, psi_single, add_conj, ← exp_eq_one_iff_int]
    congr! 4
    cases β <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  constructor
  · intro h v
    obtain ⟨a, ha⟩ := (hgen v false).1 (h _ (Submodule.subset_span ⟨(v, false), rfl⟩))
    obtain ⟨c, hc⟩ := (hgen v true).1 (h _ (Submodule.subset_span ⟨(v, true), rfl⟩))
    simp only [if_false, if_true, Bool.false_eq_true] at ha hc
    refine ⟨a, -c, ?_⟩
    rw [eq_div_iff (by simp [hR'])]
    apply Complex.ext
    · simp [Complex.mul_re]; linarith
    · simp [Complex.mul_im]; linarith
  · intro h z hz
    have hle : Lstd f R ≤ AddSubgroup.toIntSubmodule (kerPsi σ) := by
      rw [lstd_eq, Submodule.span_le]
      rintro _ ⟨⟨v, β⟩, rfl⟩
      show crystallineComparison.psi (σ * gen f R (v, β)) = 1
      rw [hgen]
      obtain ⟨a, b, hab⟩ := h v
      have h2 : σ v * (2 * (R : ℂ)) = (a : ℂ) + (b : ℂ) * Complex.I := by
        rw [hab]; field_simp
      have hre : 2 * R * (σ v).re = a := by
        have := congrArg Complex.re h2
        simp [Complex.mul_re] at this; linarith
      have him : 2 * R * (σ v).im = b := by
        have := congrArg Complex.im h2
        simp [Complex.mul_im] at this; linarith
      cases β
      · exact ⟨a, by simpa using hre⟩
      · exact ⟨-b, by simp [him]⟩
    exact hle hz

def eqv (f : ℕ) : (Σ _ : Fin f, Fin 2) ≃ Fin f × Bool :=
  (Equiv.sigmaEquivProd (Fin f) (Fin 2)).trans (Equiv.prodCongr (Equiv.refl _) finTwoEquiv)

def b0 (f : ℕ) : Module.Basis (Fin f × Bool) ℝ (crystallineComparison.V f) :=
  (Pi.basis fun _ : Fin f => Complex.basisOneI).reindex (eqv f)

theorem standard_lattice_basis_apply (f : ℕ) (v : Fin f) (β : Bool) :
    b0 f (v, β) = (Pi.single v (if β then Complex.I else 1) : crystallineComparison.V f) := by
  cases β <;> simp [b0, eqv, Pi.basis_apply] <;> rfl

theorem standard_lattice_basis_repr (f : ℕ) (m : crystallineComparison.V f) (v : Fin f) (β : Bool) :
    (b0 f).repr m (v, β) = if β then (m v).im else (m v).re := by
  rw [b0, Module.Basis.repr_reindex_apply]
  cases β <;> simp [eqv, Pi.basis_repr] <;> rfl

def bR (f : ℕ) (R : ℝ) (hR : 0 < R) : Module.Basis (Fin f × Bool) ℝ (crystallineComparison.V f) :=
  (b0 f).isUnitSMul (w := fun _ => R) (fun _ => hR.ne'.isUnit)

theorem bR_eq (f : ℕ) (R : ℝ) (hR : 0 < R) : ⇑(bR f R hR) = gen f R := by
  funext p
  obtain ⟨v, β⟩ := p
  rw [bR, Module.Basis.isUnitSMul_apply, standard_lattice_basis_apply, gen]
  cases β <;> funext u <;> by_cases h : u = v <;> simp_all [Complex.real_smul]

theorem fundamentalDomain_standard_basis_eq (f : ℕ) : ZSpan.fundamentalDomain (b0 f) =
    Set.pi Set.univ (fun _ : Fin f => {z : ℂ | z.re ∈ Set.Ico (0 : ℝ) 1 ∧ z.im ∈ Set.Ico (0 : ℝ) 1}) := by
  ext m
  simp only [ZSpan.fundamentalDomain, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Prod.forall,
    standard_lattice_basis_repr, Bool.forall_bool, if_false, if_true, Bool.false_eq_true]

theorem vol_square : (volume : Measure ℂ) {z : ℂ | z.re ∈ Set.Ico (0 : ℝ) 1 ∧ z.im ∈ Set.Ico (0 : ℝ) 1} = 1 := by
  have h : {z : ℂ | z.re ∈ Set.Ico (0 : ℝ) 1 ∧ z.im ∈ Set.Ico (0 : ℝ) 1} =
      Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) := by
    ext z; simp [Complex.measurableEquivRealProd]
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet), Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ico]
  simp

theorem volume_fundamentalDomain_standard_basis (f : ℕ) : (volume : Measure (crystallineComparison.V f)) (ZSpan.fundamentalDomain (b0 f)) = 1 := by
  rw [fundamentalDomain_standard_basis_eq, volume_pi_pi, Finset.prod_eq_one (fun _ _ => vol_square)]

theorem fd_bR (f : ℕ) (R : ℝ) (hR : 0 < R) :
    ZSpan.fundamentalDomain (bR f R hR) = R • ZSpan.fundamentalDomain (b0 f) := by
  ext m
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hR.ne']
  simp only [ZSpan.fundamentalDomain, Set.mem_ofPred_eq, bR, Module.Basis.repr_isUnitSMul, map_smul,
    Finsupp.smul_apply, smul_eq_mul]
  constructor <;> intro h i <;> simpa [Units.smul_def, Units.val_inv_eq_inv_val, IsUnit.unit_spec] using h i

theorem finrank_V (f : ℕ) : Module.finrank ℝ (crystallineComparison.V f) = 2 * f := by
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

theorem lstdFacts : PBC.LstdFacts := by
  intro f R hR
  rw [lstd_eq, ← bR_eq f R hR]
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (ZSpan.isAddFundamentalDomain (bR f R hR) volume),
      fd_bR, Measure.real, Measure.addHaar_smul, volume_fundamentalDomain_standard_basis, finrank_V]
    simp [abs_of_pos hR, hR.le]
  · intro σ
    rw [bR_eq, ← lstd_eq]
    exact mem_dual_iff f R hR σ

theorem mfac_scale (K : ℕ) (L g a : ℝ) (hg : 0 < g) :
    crystallineComparison.mfac K L (g * a) = crystallineComparison.mfac K (L / g) a := by
  unfold crystallineComparison.mfac
  by_cases h : a = 0
  · simp [h]
  · rw [if_neg (mul_ne_zero hg.ne' h), if_neg h]
    congr 2
    field_simp

theorem mL_scale {f : ℕ} (K : ℕ) (L : Fin f → ℝ) (g : ℝ) (hg : 0 < g) (σ : crystallineComparison.V f) :
    crystallineComparison.mL K L (g • σ) = crystallineComparison.mL K (fun v => L v / g) σ := by
  unfold crystallineComparison.mL
  refine Finset.prod_congr rfl (fun v _ => ?_)
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hg, mfac_scale K _ g _ hg]

theorem mfac_shift0 (K : ℕ) {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ) {a : ℝ} (ha : 0 ≤ a) :
    crystallineComparison.mfac K L a ≤ crystallineComparison.mfac K (L + δ) (a + δ) := by
  have had : 0 < a + δ := by linarith
  unfold crystallineComparison.mfac
  rw [if_neg had.ne']
  split_ifs with h0
  · subst h0
    rw [min_eq_left (one_le_pow₀ ((one_le_div (by linarith)).mpr (by linarith)))]
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm h0)
    rcases le_or_gt a L with haL | haL
    · rw [min_eq_left (one_le_pow₀ ((one_le_div had).mpr (by linarith)))]
      exact min_le_left _ _
    · apply min_le_min_left
      apply pow_le_pow_left₀ (div_nonneg hL ha)
      rw [div_le_div_iff₀ hapos had]
      nlinarith

theorem gauss_norm (m n : ℤ) (h : (m : ℂ) + (n : ℂ) * Complex.I ≠ 0) :
    1 ≤ ‖(m : ℂ) + (n : ℂ) * Complex.I‖ := by
  have hmn : m ≠ 0 ∨ n ≠ 0 := by
    by_contra hc; push Not at hc; apply h; simp [hc.1, hc.2]
  have hsq : (1 : ℝ) ≤ (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := by
    rcases hmn with hm | hn
    · have : (1 : ℤ) ≤ m ^ 2 := by nlinarith [Int.one_le_abs hm, sq_abs m]
      have : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by exact_mod_cast this
      nlinarith [sq_nonneg (n : ℝ)]
    · have : (1 : ℤ) ≤ n ^ 2 := by nlinarith [Int.one_le_abs hn, sq_abs n]
      have : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast this
      nlinarith [sq_nonneg (m : ℝ)]
  rw [← Real.sqrt_one, Complex.norm_def, Complex.normSq_apply]
  apply Real.sqrt_le_sqrt
  simp; nlinarith

theorem dual_sep (f : ℕ) (R : ℝ) (hR : 0 < R) (σ σ' : crystallineComparison.V f) (hσ : σ ∈ crystallineComparison.dualSet (Lstd f R))
    (hσ' : σ' ∈ crystallineComparison.dualSet (Lstd f R)) (hne : σ ≠ σ') : 1 / (2 * R) ≤ ‖σ - σ'‖ := by
  obtain ⟨v, hv⟩ : ∃ v, σ v ≠ σ' v := by
    by_contra h; push Not at h; exact hne (funext h)
  obtain ⟨a, b, hab⟩ := (mem_dual_iff f R hR σ).1 hσ v
  obtain ⟨a', b', hab'⟩ := (mem_dual_iff f R hR σ').1 hσ' v
  have hR' : (2 * (R : ℂ)) ≠ 0 := by simp [hR.ne']
  have hd : σ v - σ' v = (((a - a' : ℤ) : ℂ) + ((b - b' : ℤ) : ℂ) * Complex.I) / (2 * (R : ℂ)) := by
    rw [hab, hab']; push_cast; field_simp; ring
  have hnz : (((a - a' : ℤ) : ℂ) + ((b - b' : ℤ) : ℂ) * Complex.I) ≠ 0 := by
    intro h0; apply hv; rw [← sub_eq_zero, hd, h0, zero_div]
  calc 1 / (2 * R) ≤ ‖(((a - a' : ℤ) : ℂ) + ((b - b' : ℤ) : ℂ) * Complex.I)‖ / (2 * R) :=
        div_le_div_of_nonneg_right (gauss_norm _ _ hnz) (by positivity)
    _ = ‖σ v - σ' v‖ := by
        rw [hd, norm_div]; congr 1; simp [abs_of_pos hR]
    _ = ‖(σ - σ') v‖ := rfl
    _ ≤ ‖σ - σ'‖ := norm_le_pi_norm (σ - σ') v

theorem vol_ball_V (f : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (volume : Measure (crystallineComparison.V f)).real (Metric.ball 0 δ) = (Real.pi * δ ^ 2) ^ f := by
  rw [Measure.real, volume_pi_ball _ hδ]
  simp only [Pi.zero_apply, Complex.volume_ball, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hδ.le]
  simp [mul_comm]

theorem lstdSum : PBC.LstdSum := by
  refine ⟨54, by norm_num, ?_⟩
  intro f R g L hR hg hL
  set K := C.Kst with hKdef
  have hK : 2 < K := by simp [hKdef, C.Kst]
  set large₂ : Fin f → ℝ := fun v => L v / g with hLg
  have hLg0 : ∀ v, 0 ≤ large₂ v := fun v => div_nonneg (hL v) hg.le
  set δ : ℝ := 1 / (4 * R) with hδdef
  have hδ : 0 < δ := by positivity
  set L' : Fin f → ℝ := fun v => large₂ v + δ with hL'
  have hL'pos : ∀ v, 0 < L' v := fun v => by simp only [hL']; linarith [hLg0 v]
  have hmaj := Formalism.FourierDecayAlt.P.MajorantIntegrals.majIntegralProd_ok f K L' hK hL'pos
  have hint := hmaj.1
  have hnn : ∀ y : crystallineComparison.V f, 0 ≤ crystallineComparison.mL K L' y := fun y =>
    Finset.prod_nonneg (fun v _ => Formalism.FourierDecayAlt.P.LatticeSummability.mfac_nonneg K (hL'pos v).le _ (norm_nonneg _))
  have hnn0 : ∀ y : crystallineComparison.V f, 0 ≤ crystallineComparison.mL K large₂ y := fun y =>
    Finset.prod_nonneg (fun v _ => Formalism.FourierDecayAlt.P.LatticeSummability.mfac_nonneg K (hLg0 v) _ (norm_nonneg _))
  set vb := (volume : Measure (crystallineComparison.V f)).real (Metric.ball 0 δ) with hvb
  have hvb0 : 0 < vb := by rw [hvb, vol_ball_V f δ hδ]; positivity
  have hvbσ : ∀ σ : crystallineComparison.V f, (volume : Measure (crystallineComparison.V f)).real (Metric.ball σ δ) = vb := by
    intro σ; rw [hvb, Measure.real, Measure.real, Measure.addHaar_ball_center]
  have hpt : ∀ σ : crystallineComparison.V f, ∀ y ∈ Metric.ball σ δ, crystallineComparison.mL K large₂ σ ≤ crystallineComparison.mL K L' y := by
    intro σ y hy
    apply Finset.prod_le_prod (fun v _ => Formalism.FourierDecayAlt.P.LatticeSummability.mfac_nonneg K (hLg0 v) _ (norm_nonneg _))
    intro v _
    have hyv : ‖y v‖ ≤ ‖σ v‖ + δ := by
      have h1 : ‖y v - σ v‖ ≤ ‖y - σ‖ := norm_le_pi_norm (y - σ) v
      have h2 : ‖y - σ‖ < δ := by rw [← dist_eq_norm]; exact hy
      have h3 : ‖y v‖ ≤ ‖σ v‖ + ‖y v - σ v‖ := by
        calc ‖y v‖ = ‖σ v + (y v - σ v)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      linarith
    exact (mfac_shift0 K (hLg0 v) hδ (norm_nonneg _)).trans
      (Formalism.FourierDecayAlt.P.LatticeSummability.mfac_anti K (hL'pos v) (norm_nonneg _) hyv)
  have hloc : ∀ σ : crystallineComparison.V f, crystallineComparison.mL K large₂ σ * vb ≤ ∫ y in Metric.ball σ δ, crystallineComparison.mL K L' y := by
    intro σ
    rw [← hvbσ σ, mul_comm, ← smul_eq_mul, ← setIntegral_const]
    exact setIntegral_mono_on (integrableOn_const (measure_ball_lt_top).ne) hint.integrableOn
      measurableSet_ball (fun y hy => hpt σ y hy)
  have hsum : ∀ u : Finset (crystallineComparison.dualSet (Lstd f R)),
      ∑ σ ∈ u, crystallineComparison.mL K L (g • (σ : crystallineComparison.V f)) ≤ (∫ y, crystallineComparison.mL K L' y) / vb := by
    intro u
    simp only [mL_scale K L g hg]
    rw [le_div_iff₀ hvb0, Finset.sum_mul]
    have hdisj : Set.Pairwise (↑u : Set (crystallineComparison.dualSet (Lstd f R)))
        (Function.onFun Disjoint fun σ : crystallineComparison.dualSet (Lstd f R) => Metric.ball (σ : crystallineComparison.V f) δ) := by
      intro σ _ σ' _ hne
      apply Metric.ball_disjoint_ball
      have := dual_sep f R hR σ σ' σ.2 σ'.2 (fun h => hne (Subtype.ext h))
      rw [dist_eq_norm]
      have e : δ + δ = 1 / (2 * R) := by rw [hδdef]; field_simp; ring
      linarith
    calc ∑ σ ∈ u, crystallineComparison.mL K large₂ (σ : crystallineComparison.V f) * vb
        ≤ ∑ σ ∈ u, ∫ y in Metric.ball (σ : crystallineComparison.V f) δ, crystallineComparison.mL K L' y :=
          Finset.sum_le_sum (fun σ _ => hloc σ)
      _ = ∫ y in ⋃ σ ∈ u, Metric.ball (σ : crystallineComparison.V f) δ, crystallineComparison.mL K L' y :=
          (integral_biUnion_finset u (fun σ _ => measurableSet_ball) hdisj
            (fun σ _ => hint.integrableOn)).symm
      _ ≤ ∫ y, crystallineComparison.mL K L' y := setIntegral_le_integral hint (Filter.Eventually.of_forall hnn)
  have hnng : ∀ σ : crystallineComparison.dualSet (Lstd f R), 0 ≤ crystallineComparison.mL K L (g • (σ : crystallineComparison.V f)) := fun σ =>
    Finset.prod_nonneg (fun v _ => Formalism.FourierDecayAlt.P.LatticeSummability.mfac_nonneg K (hL v) _ (norm_nonneg _))
  have hS : Summable (fun σ : crystallineComparison.dualSet (Lstd f R) => crystallineComparison.mL K L (g • (σ : crystallineComparison.V f))) :=
    summable_of_sum_le hnng hsum
  refine ⟨hS, (hS.tsum_le_of_sum_le hsum).trans ?_⟩

  rw [hmaj.2, hvb, vol_ball_V f δ hδ, show (Real.pi * δ ^ 2) ^ f = ∏ _v : Fin f, (Real.pi * δ ^ 2) by simp]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_le_prod
  · intro v _
    have hK2 : (0 : ℝ) < (K : ℝ) - 2 := by simp [hKdef, C.Kst]; norm_num
    have := hL'pos v
    exact div_nonneg (div_nonneg (by positivity) hK2.le) (by positivity)
  intro v _
  have hKr : (K : ℝ) = 5 := by simp [hKdef, C.Kst]
  rw [hKr]
  set x : ℝ := R * L v / g with hxdef
  have hx0 : 0 ≤ x := by have := hL v; positivity
  have hx : L' v = 4 * δ * x + δ := by
    show L v / g + δ = _
    rw [hxdef, hδdef]; field_simp
  rw [hx]
  have ht : 0 < Real.pi * δ ^ 2 := by positivity
  have e : Real.pi * (4 * δ * x + δ) ^ 2 * 5 / (5 - 2) / (Real.pi * δ ^ 2) = (4 * x + 1) ^ 2 * 5 / 3 := by
    field_simp; ring
  rw [e]
  nlinarith [sq_nonneg (x - 1)]

end Lat

theorem pbc_lstdSum : PBC.LstdSum := Lat.lstdSum

theorem pbc_lstdFacts : PBC.LstdFacts := Lat.lstdFacts

theorem pbc_sizesSup : PBC.SizesSup := Lat.sizesSup

end

end Formalism.FourierDecayAlt.P.PBC
end

section
namespace Formalism.FourierDecayAlt.P.PBC.GlobalTheory

open Formalism.FourierDecayAlt Finset Filter Topology NumberField MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem frame_facts (g : ℕ) (hg : 0 < g) (ν : ℤ) (s : ℕ) :
    DiscreteTopology (S6.frameLat E (S6.perLat E g ν s) 1) ∧
    Submodule.span ℝ (S6.frameLat E (S6.perLat E g ν s) 1 : Set (mixedEmbedding.mixedSpace E)) = ⊤ := by
  have hA : S6.idl E g 1 ν ≠ 0 := Cx2.idl_ne_zero g hg 1 ν
  have hB : S6.idl E g 2 ν ≠ 0 := Cx2.idl_ne_zero g hg 2 ν
  obtain ⟨hBL, hLA⟩ := twistedLatticeBetween E (S6.idl E g 1 ν) (S6.idl E g 2 ν) s (Cx2.idl_two_le_one g ν)
    (different_power_conj_stable E g 2 ν)
  have hmem : ∀ x, x ∈ S6.frameLat E (S6.perLat E g ν s) 1 ↔
      ∃ t ∈ S6.perLat E g ν s, mixedEmbedding E t = x := by
    intro x
    simp [S6.frameLat]
  constructor
  · have hsub : (S6.frameLat E (S6.perLat E g ν s) 1 : Set (mixedEmbedding.mixedSpace E)) ⊆
        (mixedEmbedding.idealLattice E (Units.mk0 _ hA) : Set (mixedEmbedding.mixedSpace E)) := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := (hmem x).1 hx
      exact (mixedEmbedding.mem_idealLattice E _).2 ⟨t, hLA ht, rfl⟩
    exact DiscreteTopology.of_subset
      (inferInstanceAs (DiscreteTopology (mixedEmbedding.idealLattice E (Units.mk0 _ hA)))) hsub
  · have hsub : (mixedEmbedding.idealLattice E (Units.mk0 _ hB) : Set (mixedEmbedding.mixedSpace E)) ⊆
        (S6.frameLat E (S6.perLat E g ν s) 1 : Set (mixedEmbedding.mixedSpace E)) := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := (mixedEmbedding.mem_idealLattice E _).1 hx
      exact (hmem _).2 ⟨t, hBL ht, rfl⟩
    have hr : Set.range (mixedEmbedding.fractionalIdealLatticeBasis E (Units.mk0 _ hB)) ⊆
        (S6.frameLat E (S6.perLat E g ν s) 1 : Set (mixedEmbedding.mixedSpace E)) := by
      intro x hx
      have hx' : x ∈ mixedEmbedding.idealLattice E (Units.mk0 _ hB) := by
        rw [← mixedEmbedding.span_idealLatticeBasis]
        exact Submodule.subset_span hx
      exact hsub hx'
    rw [eq_top_iff, ← (mixedEmbedding.fractionalIdealLatticeBasis E (Units.mk0 _ hB)).span_eq]
    exact Submodule.span_mono hr

theorem eLat_facts (g : ℕ) (hg : 0 < g) (ν : ℤ) (s : ℕ) :
    ∃ _ : DiscreteTopology (J.eLat E (S6.perLat E g ν s) 1), IsZLattice ℝ (J.eLat E (S6.perLat E g ν s) 1) := by
  obtain ⟨hd, hs⟩ := frame_facts (E := E) g hg ν s
  obtain ⟨hd', hs', -⟩ := Formalism.FourierDecayAlt.P.euclidean_frame E _ 1 hd hs
  exact ⟨hd', ⟨hs'⟩⟩

variable {Wp Wq : InfinitePlace E → Type} [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

def Qe (S : C.HidaSetting E Wp Wq) : J.CV E ≃ₗ[ℝ] crystallineComparison.V S.f :=
  (WithLp.linearEquiv 2 ℝ (InfinitePlace E → ℂ)).trans (LinearEquiv.piCongrLeft' ℝ (fun _ => ℂ) S.pl.symm)

theorem Qe_apply (S : C.HidaSetting E Wp Wq) (c : J.CV E) (v : Fin S.f) : Qe S c v = c (S.pl v) := by
  rfl

def QL (S : C.HidaSetting E Wp Wq) : J.CV E ≃L[ℝ] crystallineComparison.V S.f := (Qe S).toContinuousLinearEquiv

theorem QL_apply (S : C.HidaSetting E Wp Wq) (c : J.CV E) (v : Fin S.f) : QL S c v = c (S.pl v) := by
  exact Qe_apply S c v

theorem QL_symm_apply (S : C.HidaSetting E Wp Wq) (y : crystallineComparison.V S.f) (v : Fin S.f) : (QL S).symm y (S.pl v) = y v := by
  have h := congrArg (fun z => z v) ((QL S).apply_symm_apply y)
  simpa only [QL_apply] using h

theorem QL_mp (S : C.HidaSetting E Wp Wq) : MeasurePreserving (QL S) volume volume := by
  have h : ⇑(QL S) = Formalism.FourierDecayAlt.P.JCx1.needs.Qm S := by
    funext c v
    rw [QL_apply, Formalism.FourierDecayAlt.P.JCx1.needs.Qm_apply]
  rw [h]
  exact Formalism.FourierDecayAlt.P.JCx1.needs.Qm_mp S

theorem QL_symm_mp (S : C.HidaSetting E Wp Wq) : MeasurePreserving (QL S).symm volume volume := by
  exact MeasurePreserving.symm (QL S).toHomeomorph.toMeasurableEquiv (QL_mp S)

def eT (S : C.HidaSetting E Wp Wq) : crystallineComparison.V S.f ≃L[ℝ] J.CV E :=
  (QL S).symm.trans (Cx2.cj S).toContinuousLinearEquiv

theorem eT_mp (S : C.HidaSetting E Wp Wq) : MeasurePreserving (eT S) volume volume :=
  (LinearIsometryEquiv.measurePreserving (Cx2.cj S)).comp (QL_symm_mp S)

theorem latV_eq (S : C.HidaSetting E Wp Wq) (L : Submodule ℤ E) :
    PBC.latV S L.toAddSubgroup = ZLattice.comap ℝ (J.eLat E L 1) (eT S).toLinearEquiv.toLinearMap := by
  have hkey : ∀ t : E, eT S (PBC.embV S t) = J.semb E 1 t := by
    intro t
    ext w
    obtain ⟨v, rfl⟩ := S.pl.surjective w
    have hq : (QL S).symm (PBC.embV S t) (S.pl v) = S.σ v t := QL_symm_apply S _ v
    have hs : (J.semb E 1 t) (S.pl v) = (S.pl v).embedding t := by simp [J.semb, J.cemb]
    rw [hs]
    change (Cx2.cj S) ((QL S).symm (PBC.embV S t)) (S.pl v) = _
    by_cases h : S.σ v = (S.pl v).embedding
    · rw [(Cx2.cj_apply S _ v).1 h, hq, h]
    · rw [(Cx2.cj_apply S _ v).2 h, hq]
      have hm := InfinitePlace.embedding_mk_eq (S.σ v)
      rw [show InfinitePlace.mk (S.σ v) = S.pl v from S.hemb v] at hm
      rcases hm with hm | hm
      · exact absurd hm.symm h
      · rw [hm, ComplexEmbedding.conjugate_coe_eq]
  ext x
  simp only [PBC.latV, ZLattice.comap, J.eLat, Submodule.mem_map, Submodule.mem_comap,
    AddMonoidHom.coe_toIntLinearMap, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, (hkey t).symm⟩
  · rintro ⟨t, ht, hx⟩
    refine ⟨t, ht, (eT S).injective ?_⟩
    rw [hkey]
    exact hx

end

end Formalism.FourierDecayAlt.P.PBC.GlobalTheory

namespace Formalism.FourierDecayAlt.P.PBC.GlobalTheory

open Formalism.FourierDecayAlt Finset Filter Topology NumberField MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

theorem f_eq_deg (S : C.HidaSetting E Wp Wq) : S.f = S6.deg E := by
  have h := Fintype.card_congr S.pl
  rw [Fintype.card_fin] at h
  rw [h]
  exact (Formalism.FourierDecayAlt.P.S6x2.degreeFacts E).2.1

theorem prod_dlB_eq_covolume (S : C.HidaSetting E Wp Wq) (hg : 0 < S.g) (hU : S6.Unram E) (b s : ℕ) :
    ∏ _v : Fin S.f, KB.dlB S b s =
      ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r b s) s) 1) := by
  rw [Formalism.FourierDecayAlt.P.unipotent_dual_lattice_covolume E hU S.g _ s hg]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, f_eq_deg S]
  unfold KB.dlB D.deG
  have hrd := Formalism.FourierDecayAlt.P.Jx4.rd_pos E
  have hg' : (0 : ℝ) < (S.g : ℝ) := by exact_mod_cast hg
  have e : S6.rd E ^ (2 * S6.nuBlock (S.G.r : ℤ) (b : ℤ) (s : ℤ)) / (2 / (S6.rd E * (S.g : ℝ) ^ 3)) =
      S6.rd E ^ (2 * S6.nuBlock (S.G.r : ℤ) (b : ℤ) (s : ℤ)) * (S6.rd E / 2) * (S.g : ℝ) ^ 3 := by
    field_simp
  rw [e, mul_pow, mul_pow, ← zpow_natCast, ← zpow_mul, ← pow_mul]

theorem lat_facts (S : C.HidaSetting E Wp Wq) (hg : 0 < S.g) (hU : S6.Unram E) (b s : ℕ) :
    ∃ (_ : DiscreteTopology (PBC.latV S (J.LaB E S.g S.G.r b s)))
      (_ : IsZLattice ℝ (PBC.latV S (J.LaB E S.g S.G.r b s))),
      ZLattice.covolume (PBC.latV S (J.LaB E S.g S.G.r b s)) = ∏ _v : Fin S.f, KB.dlB S b s := by
  have hL := latV_eq S (S6.perLat E S.g (S6.nuBlock S.G.r b s) s)
  obtain ⟨hd, hz⟩ := eLat_facts (E := E) S.g hg (S6.nuBlock S.G.r b s) s
  rw [show J.LaB E S.g S.G.r b s = (S6.perLat E S.g (S6.nuBlock S.G.r b s) s).toAddSubgroup from rfl, hL,
    prod_dlB_eq_covolume S hg hU b s]
  haveI := hd
  haveI := hz
  have hd' : DiscreteTopology (ZLattice.comap ℝ (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r b s) s) 1)
      (eT S).toLinearEquiv.toLinearMap) :=
    ZLattice.comap_discreteTopology _ _ (eT S).continuous (eT S).injective
  haveI := hd'
  have hz' : IsZLattice ℝ (ZLattice.comap ℝ (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r b s) s) 1)
      (eT S).toLinearEquiv.toLinearMap) := inferInstance
  exact ⟨hd', hz', ZLattice.covolume_comap _ _ _ (eT_mp S)⟩

theorem dual_smul_mem {f : ℕ} (La : Submodule ℤ (crystallineComparison.V f)) [DiscreteTopology La] [IsZLattice ℝ La] (g : ℝ)
    (hg : g ≠ 0) : ∃ (Lm : Submodule ℤ (crystallineComparison.V f)) (_ : DiscreteTopology Lm) (_ : IsZLattice ℝ Lm),
      ∀ σ ∈ crystallineComparison.dualSet La, g • σ ∈ Lm := by
  let b0 : Module.Basis (Fin (Module.finrank ℤ La)) ℝ (crystallineComparison.V f) :=
    (Pi.basisFun ℝ (Fin (Module.finrank ℤ La))).map (Formalism.FourierDecayAlt.P.PairingConjugationLemmas.Le La).symm
  let bd := b0.isUnitSMul (w := fun _ => g) (fun _ => isUnit_iff_ne_zero.mpr hg)
  refine ⟨Submodule.span ℤ (Set.range bd), inferInstance, inferInstance, ?_⟩
  intro σ hσ
  obtain ⟨m, rfl⟩ := Formalism.FourierDecayAlt.P.PairingConjugationLemmas.ψd_surj La σ hσ
  have hx : (fun j => ((m j : ℤ) : ℝ)) = ∑ j, ((m j : ℤ) : ℝ) • Pi.basisFun ℝ (Fin (Module.finrank ℤ La)) j :=
    ((Pi.basisFun ℝ _).sum_repr _).symm
  have h : g • Formalism.FourierDecayAlt.P.PairingConjugationLemmas.ψd La m = ∑ j, (m j) • bd j := by
    unfold Formalism.FourierDecayAlt.P.PairingConjugationLemmas.ψd
    rw [hx, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Module.Basis.isUnitSMul_apply, ← Int.cast_smul_eq_zsmul ℝ, smul_comm]
    rfl
  rw [h]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem dual_to_E (S : C.HidaSetting E Wp Wq) (hg : 0 < S.g) (L : Submodule ℤ E)
    (hL : ∀ t : E, ∃ n : ℕ, 0 < n ∧ (n : E) * t ∈ L) (σ : crystallineComparison.V S.f)
    (hσ : σ ∈ crystallineComparison.dualSet (PBC.latV S L.toAddSubgroup)) :
    ∃ l ∈ S6.dualLat E S.g L, ∀ v, ((S.g : ℝ) : ℂ) * σ v = S.σ v l := by
  set μ : J.CV E := WithLp.toLp 2 (fun w => if S.σ (S.pl.symm w) = w.embedding then
    2 * conj (σ (S.pl.symm w)) else 2 * σ (S.pl.symm w)) with hμdef
  have hμv : ∀ v, μ (S.pl v) = if S.σ v = (S.pl v).embedding then 2 * conj (σ v) else 2 * σ v := by
    intro v; simp [hμdef]
  have hμ : μ ∈ Formalism.H.dual (J.eLat E L 1) := by
    rw [Formalism.H.dual, LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.1 hy
    have hmem : PBC.embV S t ∈ PBC.latV S L.toAddSubgroup :=
      Submodule.mem_map.2 ⟨t, ht, rfl⟩
    have h1 := hσ _ hmem
    rw [Formalism.FourierDecayAlt.P.PairingConjugationLemmas.psi_mul, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    have hpair : Formalism.FourierDecayAlt.P.PairingConjugationLemmas.pair σ (PBC.embV S t) = n := by
      have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have h2 : ((Formalism.FourierDecayAlt.P.PairingConjugationLemmas.pair σ (PBC.embV S t) : ℝ) : ℂ) = ((n : ℝ) : ℂ) := by
        apply mul_left_cancel₀ hne
        rw [hn]; push_cast; ring
      exact_mod_cast h2
    have hinner : inner ℝ μ ((J.semb E 1).toIntLinearMap t) = Formalism.FourierDecayAlt.P.PairingConjugationLemmas.pair σ (PBC.embV S t) := by
      have hs : (J.semb E 1).toIntLinearMap t = J.cemb E t := by simp [J.semb]
      rw [hs, PiLp.inner_apply, ← Equiv.sum_comp S.pl]
      unfold Formalism.FourierDecayAlt.P.PairingConjugationLemmas.pair
      refine Finset.sum_congr rfl fun v _ => ?_
      have hc : (J.cemb E t) (S.pl v) = (S.pl v).embedding t := by simp [J.cemb]
      rw [hμv v, hc]
      simp only [PBC.embV, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      by_cases h : S.σ v = (S.pl v).embedding
      · rw [if_pos h, ← h]
        simp [Complex.inner, Complex.mul_re]
        ring
      · rw [if_neg h]
        have h2 := (Cx2.σ_or S v).resolve_left h
        rw [← h2, ComplexEmbedding.conjugate_coe_eq]
        simp [Complex.inner, Complex.mul_re]
        ring
    rw [Submodule.mem_one]
    refine ⟨n, ?_⟩
    rw [innerₗ_apply_apply, hinner, hpair]
    simp
  obtain ⟨l, hl, hlμ⟩ := (Formalism.FourierDecayAlt.P.trace_dual_alt E L S.g 1 hg one_ne_zero hL μ).1 hμ
  refine ⟨l, hl, fun v => ?_⟩
  have hcoord := congrArg (fun c : J.CV E => c (S.pl v)) hlμ
  simp only [J.dm, hμv v] at hcoord
  have hg' : ((S.g : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.cast_pos.mpr hg).ne'
  by_cases h : S.σ v = (S.pl v).embedding
  · rw [if_pos h, ← h] at hcoord
    have := congrArg conj hcoord
    simp only [map_mul, Complex.conj_conj, map_ofNat] at this
    have h3 : conj (((2 / ((S.g : ℝ) * 1) : ℝ)) : ℂ) = ((2 / (S.g : ℝ) : ℝ) : ℂ) := by
      rw [Complex.conj_ofReal]; simp
    rw [h3] at this
    push_cast at this ⊢
    have hg2 : (S.g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
    calc (S.g : ℂ) * σ v = ((S.g : ℂ) / 2) * (2 * σ v) := by ring
      _ = ((S.g : ℂ) / 2) * (2 / (S.g : ℂ) * S.σ v l) := by rw [this]
      _ = S.σ v l := by field_simp
  · rw [if_neg h] at hcoord
    have h2 := (Cx2.σ_or S v).resolve_left h
    rw [← h2, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj] at hcoord
    push_cast at hcoord ⊢
    have hg2 : (S.g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
    calc (S.g : ℂ) * σ v = ((S.g : ℂ) / 2) * (2 * σ v) := by ring
      _ = ((S.g : ℂ) / 2) * (2 / (S.g : ℂ) * S.σ v l) := by rw [← hcoord, mul_one]
      _ = S.σ v l := by field_simp

end

end Formalism.FourierDecayAlt.P.PBC.GlobalTheory

namespace Formalism.FourierDecayAlt.P.PBC.GlobalTheory

open Formalism.FourierDecayAlt Finset Filter Topology NumberField MeasureTheory
open scoped ComplexConjugate nonZeroDivisors

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

theorem mfac_nonneg (K : ℕ) (L a : ℝ) (hL : 0 ≤ L) (ha : 0 ≤ a) : 0 ≤ crystallineComparison.mfac K L a := by
  unfold crystallineComparison.mfac
  split_ifs
  · exact zero_le_one
  · exact le_min zero_le_one (pow_nonneg (div_nonneg hL ha) K)

theorem mfac_le_one (K : ℕ) (L a : ℝ) : crystallineComparison.mfac K L a ≤ 1 := by
  unfold crystallineComparison.mfac
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem min_scale (c y : ℝ) (hc : 1 ≤ c) (_hy : 0 ≤ y) : min 1 (c * y) ≤ c * min 1 y := by
  rcases le_total y 1 with h | h
  · rw [min_eq_right h]
    exact min_le_right _ _
  · rw [min_eq_left h, mul_one]
    exact (min_le_left _ _).trans hc

theorem mL_le_prof (S : C.HidaSetting E Wp Wq) (K : ℕ) (Λ : Fin S.f → ℝ) (hΛ : ∀ v, 0 ≤ Λ v) (σ : crystallineComparison.V S.f)
    (l : E) (hl0 : l ≠ 0) (hσ : ∀ v, ((S.g : ℝ) : ℂ) * σ v = S.σ v l) :
    crystallineComparison.mL K Λ ((S.g : ℝ) • σ) ≤ ((3 : ℝ) ^ K) ^ S.f *
      J.prof (fun w => Λ (S.pl.symm w) / 3) K l := by
  unfold crystallineComparison.mL J.prof
  rw [← Equiv.prod_comp S.pl (fun w => min 1 ((Λ (S.pl.symm w) / 3 / w l) ^ K))]
  simp only [Equiv.symm_apply_apply]
  rw [← Fin.prod_const S.f ((3 : ℝ) ^ K), ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun v _ => mfac_nonneg _ _ _ (hΛ v) (norm_nonneg _)) (fun v _ => ?_)
  have hpos : 0 < (S.pl v) l := by
    rw [← S.hemb v, InfinitePlace.apply]
    exact norm_pos_iff.2 ((map_ne_zero _).2 hl0)
  have ha : ‖((S.g : ℝ) • σ) v‖ = (S.pl v) l := by
    rw [Pi.smul_apply, Complex.real_smul, hσ v, ← S.hemb v, InfinitePlace.apply]
    rfl
  unfold crystallineComparison.mfac
  rw [ha, if_neg hpos.ne']
  have hy : 0 ≤ (Λ v / 3 / (S.pl v) l) ^ K :=
    pow_nonneg (div_nonneg (div_nonneg (hΛ v) (by norm_num)) hpos.le) K
  have key := min_scale ((3 : ℝ) ^ K) ((Λ v / 3 / (S.pl v) l) ^ K) (one_le_pow₀ (by norm_num)) hy
  calc min 1 ((Λ v / (S.pl v) l) ^ K) = min 1 ((3 : ℝ) ^ K * (Λ v / 3 / (S.pl v) l) ^ K) := by
        rw [← mul_pow]
        congr 2
        field_simp
    _ ≤ _ := key

theorem card_places (S : C.HidaSetting E Wp Wq) : Fintype.card (InfinitePlace E) = S.f := by
  rw [← Fintype.card_fin S.f]
  exact Fintype.card_congr S.pl.symm

theorem sum_le (S : C.HidaSetting E Wp Wq) (hg : 0 < S.g) (hU : S6.Unram E) (b s : ℕ) (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hbox : ∀ (aa : FractionalIdeal (𝓞 E)⁰ E) (L : AddSubgroup E) (x : InfinitePlace E → ℝ) (K : ℕ) (Θ a : ℝ),
      aa ≠ 0 → (∀ l ∈ L, l ∈ aa) → (∀ w, 0 ≤ x w) → 3 ≤ K → 1 ≤ a → 2 * a < Θ →
      ∏ w, x w ≤ (a / Θ) ^ Fintype.card (InfinitePlace E) * √(FractionalIdeal.absNorm aa : ℝ) →
      TA.LatSum L (J.prof x K) ((C0 * a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2))) ^
        Fintype.card (InfinitePlace E)))
    (Λ : Fin S.f → ℝ) (hΛ : ∀ v, 0 ≤ Λ v ∧ Λ v ≤ PBC.thr S b s v) (hvol : S.base.vol b s ≤ 1)
    (T : Finset (crystallineComparison.dualSet (PBC.latV S (J.LaB E S.g S.G.r b s)))) :
    ∑ σ ∈ T, crystallineComparison.mL C.Kst Λ ((S.g : ℝ) • (σ : crystallineComparison.V S.f)) ≤ 1 + ((3 : ℝ) ^ C.Kst) ^ S.f * C0 ^ S.f := by
  set ν := S6.nuBlock S.G.r b s with hν
  set L := S6.perLat E S.g ν s with hLdef
  have hA : S6.idl E S.g 1 ν ≠ 0 := Cx2.idl_ne_zero S.g hg 1 ν
  have hB : S6.idl E S.g 2 ν ≠ 0 := Cx2.idl_ne_zero S.g hg 2 ν
  have hL : ∀ t : E, ∃ n : ℕ, 0 < n ∧ (n : E) * t ∈ L :=
    (twistedIsRealOrderLattice E (S6.idl E S.g 1 ν) (S6.idl E S.g 2 ν) s hB (Cx2.idl_two_le_one S.g ν)
      (different_power_conj_stable E S.g 2 ν)).2
  have hLaB : J.LaB E S.g S.G.r b s = L.toAddSubgroup := rfl
  have hBL := block_lattices lattice_facts_general dualIdealEqLiftIdeal scaledIdealNorm E hU
    S.g S.G.r b s hg
  have hdual : ∀ σ : crystallineComparison.dualSet (PBC.latV S (J.LaB E S.g S.G.r b s)),
      ∃ l ∈ S6.dualLat E S.g L, ∀ v, ((S.g : ℝ) : ℂ) * (σ : crystallineComparison.V S.f) v = S.σ v l := by
    intro σ
    exact dual_to_E S hg L hL σ.1 σ.2
  choose lσ hlσ hlσv using hdual
  have hΛ0 : ∀ v, 0 ≤ Λ v := fun v => (hΛ v).1
  have hF0 : ∀ σ : crystallineComparison.dualSet (PBC.latV S (J.LaB E S.g S.G.r b s)),
      0 ≤ crystallineComparison.mL C.Kst Λ ((S.g : ℝ) • (σ : crystallineComparison.V S.f)) :=
    fun σ => Finset.prod_nonneg fun v _ => mfac_nonneg _ _ _ (hΛ0 v) (norm_nonneg _)
  rw [← Finset.sum_filter_add_sum_filter_not T (fun σ : crystallineComparison.dualSet (PBC.latV S (J.LaB E S.g S.G.r b s)) => σ.1 = 0)]
  refine add_le_add ?_ ?_
  ·
    have hcard : (T.filter (fun σ : crystallineComparison.dualSet (PBC.latV S (J.LaB E S.g S.G.r b s)) => σ.1 = 0)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha a' ha'
      rw [Finset.mem_filter] at ha ha'
      exact Subtype.ext (ha.2.trans ha'.2.symm)
    calc _ ≤ ∑ σ ∈ T.filter (fun σ : crystallineComparison.dualSet (PBC.latV S (J.LaB E S.g S.G.r b s)) => σ.1 = 0), (1 : ℝ) :=
          Finset.sum_le_sum fun σ _ => Finset.prod_le_one (fun v _ => mfac_nonneg _ _ _ (hΛ0 v) (norm_nonneg _))
            fun v _ => mfac_le_one _ _ _
      _ ≤ 1 := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]; exact_mod_cast hcard
  ·
    set T1 := T.filter (fun σ : crystallineComparison.dualSet (PBC.latV S (J.LaB E S.g S.G.r b s)) => ¬ σ.1 = 0) with hT1
    have hl0 : ∀ σ ∈ T1, lσ σ ≠ 0 := by
      intro σ hσ h0
      rw [hT1, Finset.mem_filter] at hσ
      apply hσ.2
      funext v
      have := hlσv σ v
      rw [h0, map_zero] at this
      have hg' : (S.g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
      push_cast at this
      exact (mul_eq_zero.1 this).resolve_left hg'
    have hinj : Set.InjOn lσ (T1 : Set _) := by
      intro σ _ σ' _ h
      apply Subtype.ext
      funext v
      have h1 := hlσv σ v
      have h2 := hlσv σ' v
      rw [h] at h1
      have hg' : ((S.g : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.cast_pos.mpr hg).ne'
      exact mul_left_cancel₀ hg' (h1.trans h2.symm)
    set x : InfinitePlace E → ℝ := fun w => Λ (S.pl.symm w) / 3 with hx
    have hx0 : ∀ w, 0 ≤ x w := fun w => div_nonneg (hΛ0 _) (by norm_num)
    have hN0 : S6.dualIdl E S.g ν ≠ 0 := hBL.2.2.2.1
    have hNpos : (0 : ℝ) < (FractionalIdeal.absNorm (S6.dualIdl E S.g ν) : ℝ) := by
      have h1 : FractionalIdeal.absNorm (S6.dualIdl E S.g ν) ≠ 0 := by
        rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]
      have h2 := FractionalIdeal.absNorm_nonneg (S6.dualIdl E S.g ν)
      exact_mod_cast lt_of_le_of_ne h2 (Ne.symm h1)
    have hthr0 : ∀ w, 0 ≤ J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s w := by
      intro w
      have := hΛ (S.pl.symm w)
      have h' : PBC.thr S b s (S.pl.symm w) = J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s w := by
        simp [PBC.thr]
      linarith [this.1, this.2, h'.le, h'.ge]
    have hprodthr : ∏ w, J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s w ≤
        √(FractionalIdeal.absNorm (S6.dualIdl E S.g ν) : ℝ) := by
      have hv : (∏ w, J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s w) ^ 2 /
          (FractionalIdeal.absNorm (S6.dualIdl E S.g ν) : ℝ) ≤ 1 := hvol
      rw [div_le_one hNpos] at hv
      exact Real.le_sqrt_of_sq_le hv
    have hprodx : ∏ w, x w ≤ (1 / 3) ^ Fintype.card (InfinitePlace E) *
        √(FractionalIdeal.absNorm (S6.dualIdl E S.g ν) : ℝ) := by
      calc ∏ w, x w = (1 / 3) ^ Fintype.card (InfinitePlace E) * ∏ w, Λ (S.pl.symm w) := by
            rw [hx, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, one_div, inv_pow]; ring
        _ ≤ (1 / 3) ^ Fintype.card (InfinitePlace E) * ∏ w, J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s w := by
            refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun w _ => hΛ0 _) fun w _ => ?_)
              (by positivity)
            have := (hΛ (S.pl.symm w)).2
            simpa [PBC.thr] using this
        _ ≤ _ := mul_le_mul_of_nonneg_left hprodthr (by positivity)
    have hLS := hbox (S6.dualIdl E S.g ν) (S6.dualLat E S.g L).toAddSubgroup x C.Kst 3 1 hN0
      (fun l hl => hBL.2.1 l hl) hx0 (by norm_num [C.Kst]) le_rfl (by norm_num) (by simpa using hprodx)
    rw [card_places S] at hLS
    have hep : (C0 * (1 : ℝ) ^ ((C.Kst : ℝ) - 5 / 2) * (3 : ℝ) ^ (-((C.Kst : ℝ) - 5 / 2))) ^ S.f ≤ C0 ^ S.f := by
      refine pow_le_pow_left₀ (by positivity) ?_ _
      rw [Real.one_rpow, mul_one]
      refine mul_le_of_le_one_right (by linarith) ?_
      exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num [C.Kst])
    calc ∑ σ ∈ T1, crystallineComparison.mL C.Kst Λ ((S.g : ℝ) • (σ : crystallineComparison.V S.f))
        ≤ ∑ σ ∈ T1, ((3 : ℝ) ^ C.Kst) ^ S.f * J.prof x C.Kst (lσ σ) :=
          Finset.sum_le_sum fun σ hσ => mL_le_prof S C.Kst Λ hΛ0 σ (lσ σ) (hl0 σ hσ) (hlσv σ)
      _ = ((3 : ℝ) ^ C.Kst) ^ S.f * ∑ l ∈ T1.image lσ, J.prof x C.Kst l := by
          rw [← Finset.mul_sum, Finset.sum_image hinj]
      _ ≤ ((3 : ℝ) ^ C.Kst) ^ S.f * C0 ^ S.f := by
          refine mul_le_mul_of_nonneg_left ((hLS.2 _ fun l hl => ?_).trans hep) (by positivity)
          obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hl
          exact ⟨hlσ σ, hl0 σ hσ⟩

end

end Formalism.FourierDecayAlt.P.PBC.GlobalTheory

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset NumberField

theorem pbc_blockLatV : PBC.BlockLatV := by
  obtain ⟨C0, hC0, hbox⟩ := Formalism.FourierDecayAlt.P.box_sum_lattice Formalism.SA.P.smoothedSumBound
  refine ⟨2 * 3 ^ C.Kst * C0, by
    have : (1 : ℝ) ≤ 3 ^ C.Kst := one_le_pow₀ (by norm_num)
    nlinarith, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ S hg1 hg2 hU b s _hb _hs
  have hg : 0 < S.g := Nat.mul_pos hg1 hg2
  obtain ⟨i1, i2, hcov⟩ := GlobalTheory.lat_facts S hg hU b s
  refine ⟨i1, i2, hcov, GlobalTheory.dual_smul_mem _ _ (by exact_mod_cast hg.ne'), ?_⟩
  intro Λ hΛ hvol
  have hf : 1 ≤ S.f := by
    rw [GlobalTheory.f_eq_deg S]; exact (Formalism.FourierDecayAlt.P.degreeFacts_statement E).2.2
  have hbound : 1 + ((3 : ℝ) ^ C.Kst) ^ S.f * C0 ^ S.f ≤ (2 * 3 ^ C.Kst * C0) ^ S.f := by
    have h1 : (1 : ℝ) ≤ (3 ^ C.Kst * C0) ^ S.f := one_le_pow₀ (by
      have : (1 : ℝ) ≤ 3 ^ C.Kst := one_le_pow₀ (by norm_num)
      nlinarith)
    have h2 : (2 : ℝ) ≤ 2 ^ S.f := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ S.f := pow_le_pow_right₀ (by norm_num) hf
    rw [← mul_pow, mul_assoc, mul_pow 2]
    nlinarith
  have hsum := GlobalTheory.sum_le S hg hU b s C0 hC0 (hbox E) Λ hΛ hvol
  have hF0 : ∀ σ : crystallineComparison.dualSet (PBC.latV S (J.LaB E S.g S.G.r b s)),
      0 ≤ crystallineComparison.mL C.Kst Λ ((S.g : ℝ) • (σ : crystallineComparison.V S.f)) :=
    fun σ => Finset.prod_nonneg fun v _ => GlobalTheory.mfac_nonneg _ _ _ (hΛ v).1 (norm_nonneg _)
  have hS : Summable (fun σ : crystallineComparison.dualSet (PBC.latV S (J.LaB E S.g S.G.r b s)) =>
      crystallineComparison.mL C.Kst Λ ((S.g : ℝ) • (σ : crystallineComparison.V S.f))) :=
    summable_of_sum_le hF0 (fun T => (hsum T).trans hbound)
  exact ⟨hS, hS.tsum_le_of_sum_le fun T => (hsum T).trans hbound⟩

end Formalism.FourierDecayAlt.P.PBC
end

section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.PBB

open Finset Filter Topology NumberField MeasureTheory
open scoped ComplexConjugate

noncomputable section
open Classical

theorem psd_congr {α : Type} (F : Finset α) (k1 k2 : α → α → ℂ) (h : ∀ x ∈ F, ∀ y ∈ F, k1 x y = k2 x y)
    (hk : TB.PSDOn F k1) : TB.PSDOn F k2 := by
  unfold TB.PSDOn at hk ⊢
  convert hk using 1
  ext x y
  exact (h x.1 x.2 y.1 y.2).symm

theorem block_schur2 {X ι : Type} [Fintype ι] (Y : Finset X) (κa κw κb : X → X → ℂ)
    (hκ : KB.BlockPSD Y Y κa κw κb) (a w b : ι → X → X → ℂ) (hB : ∀ v, KB.BlockPSD Y Y (a v) (w v) (b v)) :
    ‖∑ p ∈ Y, ∑ q ∈ Y, κw p q * ∏ v, w v p q‖ ≤
      ((∑ p ∈ Y, ∑ q ∈ Y, κa p q * ∏ v, a v p q).re + (∑ p ∈ Y, ∑ q ∈ Y, κb p q * ∏ v, b v p q).re) / 2 := by
  let A' : Option ι → X → X → ℂ := fun o => match o with | none => κa | some v => a v
  let W' : Option ι → X → X → ℂ := fun o => match o with | none => κw | some v => w v
  let B' : Option ι → X → X → ℂ := fun o => match o with | none => κb | some v => b v
  have hB2 : ∀ o : Option ι, ∃ K : X ⊕ X → X ⊕ X → ℂ, TB.PSDOn (Y.disjSum Y) K ∧
      ∀ p q, K (.inl p) (.inl q) = A' o p q ∧ K (.inl p) (.inr q) = W' o p q ∧ K (.inr p) (.inr q) = B' o p q := by
    intro o
    rcases o with _ | v
    · exact ⟨_, hκ, fun p q => ⟨rfl, rfl, rfl⟩⟩
    · exact ⟨_, hB v, fun p q => ⟨rfl, rfl, rfl⟩⟩
  choose K hKp hKv using hB2
  have hP := Formalism.FourierDecayAlt.P.schur_product (X ⊕ X) (Option ι) (Y.disjSum Y) K hKp
  have h2 := Formalism.FourierDecayAlt.P.JCx1.decay.psd_compress (Y.disjSum Y) (fun x y => ∏ o, K o x y) hP
    (fun _ : Fin 2 => Y) (fun j => if j = 0 then Sum.inl else Sum.inr) (by
      intro j h hh
      fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]; rw [Finset.inl_mem_disjSum]; exact hh
      · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]; rw [Finset.inr_mem_disjSum]; exact hh)
  obtain ⟨hcs, hA, hB'⟩ := Formalism.FourierDecayAlt.P.JCx1.decay.psd_two_cs _ h2
  simp only [Matrix.of_apply, Fintype.prod_option, Fin.isValue, one_ne_zero, ↓reduceIte, hKv, A', W', B']
    at hcs hA hB'
  set Wn := ∑ p ∈ Y, ∑ q ∈ Y, κw p q * ∏ v, w v p q
  set A := (∑ p ∈ Y, ∑ q ∈ Y, κa p q * ∏ v, a v p q).re
  set B := (∑ p ∈ Y, ∑ q ∈ Y, κb p q * ∏ v, b v p q).re
  have hW : ‖Wn‖ ^ 2 ≤ A * B := hcs
  have hA0 : 0 ≤ A := hA
  have hB0 : 0 ≤ B := hB'
  have hn := norm_nonneg Wn
  nlinarith [sq_nonneg (A - B), sq_nonneg (‖Wn‖ - (A + B) / 2)]

section lift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem sizeAt_nonneg (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) : 0 ≤ S.sizeAt v a := by
  unfold C.HidaSetting.sizeAt
  exact List.prod_nonneg fun x hx => by
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact abs_nonneg _

theorem gN_psd (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r + 1) (w : S.W) (Z : Finset C.LPt) : TB.PSDOn Z (KB.gN S v ε j (w.1 v)) := by
  have h0 := hpos v ε hε j hj w Z
  have h1 := Formalism.FourierDecayAlt.P.diagonal_scaling C.LPt Z _ (fun _ => (√(S.sizeAt v (w.1 v)))⁻¹) h0
  refine psd_congr Z _ _ (fun x _ y _ => ?_) h1
  unfold KB.gN
  have hs := sizeAt_nonneg S v (w.1 v)
  have e : (((√(S.sizeAt v (w.1 v)))⁻¹ : ℝ) : ℂ) * (((√(S.sizeAt v (w.1 v)))⁻¹ : ℝ) : ℂ) =
      ((S.sizeAt v (w.1 v) : ℝ) : ℂ)⁻¹ := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hs, Complex.ofReal_inv]
  rw [e, div_eq_mul_inv, mul_comm]

theorem lift_block0 (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r + 1) (w : S.W) (Y : Finset (TB.Pt E)) (P P' : TB.Pt E → C.LPt) :
    KB.BlockPSD Y Y (fun p q => KB.gN S v ε j (w.1 v) (P p) (P q))
      (fun p q => KB.gN S v ε j (w.1 v) (P p) (P' q)) (fun p q => KB.gN S v ε j (w.1 v) (P' p) (P' q)) := by
  let G : TB.Pt E ⊕ TB.Pt E → C.LPt := Sum.elim P P'
  have hZ := gN_psd S hpos v ε hε j hj w ((Y.disjSum Y).image G)
  have hpull := Formalism.FourierDecayAlt.P.JCx1.decay.psd_pull _ _ hZ (Y.disjSum Y) G
    (fun x hx => Finset.mem_image_of_mem G hx)
  unfold KB.BlockPSD
  refine psd_congr _ _ _ (fun x hx y hy => ?_) hpull
  rcases x with p | p <;> rcases y with q | q
  · rfl
  · rfl
  · have hp : G (.inr p) ∈ (Y.disjSum Y).image G := Finset.mem_image_of_mem G hx
    have hq : G (.inl q) ∈ (Y.disjSum Y).image G := Finset.mem_image_of_mem G hy
    have := hZ.1.apply (⟨G (.inr p), hp⟩ : (Y.disjSum Y).image G) (⟨G (.inl q), hq⟩ : (Y.disjSum Y).image G)
    simp only [Matrix.of_apply] at this
    exact this.symm
  · rfl

theorem rhs_eval2 (S : C.HidaSetting E Wp Wq) (ε : ℝ) (j : ℕ) (Y : Finset (TB.Pt E))
    (κ : TB.Pt E → TB.Pt E → ℂ) (n : ℕ) (hn : n ≤ S.Ntop) (U : Fin S.f → Finset (List C.Letter))
    (θ : Fin S.f → List C.Letter → ℝ) (hU : ∀ v, KB.LocProb S v n (U v) (θ v)) (s : Fin S.f → ℝ)
    (P P' : Fin S.f → TB.Pt E → C.LPt) :
    (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, ((s v : ℂ) * ∑ a ∈ U v, (θ v a : ℂ) *
        KB.gN S v ε j a (P v h) (P' v h'))).re =
      (∏ v, s v) * ∑ w' ∈ S.base.Wb n, (∏ v, θ v (w'.1 v)) *
        ((∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, S.gramLoc v ε j (w'.1 v) (P v h) (P' v h')) /
          (C.Word.size S.P w'.1 : ℂ)).re := by
  have e1 : ∀ h h' : TB.Pt E, ∏ v, ((s v : ℂ) * ∑ a ∈ U v, (θ v a : ℂ) * KB.gN S v ε j a (P v h) (P' v h')) =
      ((∏ v, s v : ℝ) : ℂ) * ∑ w' ∈ S.base.Wb n, ((∏ v, θ v (w'.1 v) : ℝ) : ℂ) *
        ((∏ v, S.gramLoc v ε j (w'.1 v) (P v h) (P' v h')) / (C.Word.size S.P w'.1 : ℂ)) := by
    intro h h'
    rw [Finset.prod_mul_distrib,
      ← prod_sum_words S n hn U θ hU (fun v a => KB.gN S v ε j a (P v h) (P' v h'))]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun w' _ => ?_
    congr 1
    simp only [KB.gN, Finset.prod_div_distrib]
    congr 1
    simp only [C.Word.size, C.HidaSetting.sizeAt, Complex.ofReal_prod]
  have e2 : ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, ((s v : ℂ) * ∑ a ∈ U v, (θ v a : ℂ) *
        KB.gN S v ε j a (P v h) (P' v h')) =
      ((∏ v, s v : ℝ) : ℂ) * ∑ w' ∈ S.base.Wb n, ((∏ v, θ v (w'.1 v) : ℝ) : ℂ) *
        ((∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, S.gramLoc v ε j (w'.1 v) (P v h) (P' v h')) /
          (C.Word.size S.P w'.1 : ℂ)) := by
    rw [Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ => by rw [e1 h h']]
    simp only [Finset.mul_sum, Finset.sum_div]
    rw [Finset.sum_congr rfl (fun h _ => Finset.sum_comm), Finset.sum_comm]
    refine Finset.sum_congr rfl fun w' _ => Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ => ?_
    ring
  rw [e2, Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun w' _ => ?_
  rw [Complex.re_ofReal_mul]

theorem pair_sum {ι : Type} (s : Finset ι) (p q a b : ι → ℝ) (hp : ∑ x ∈ s, p x = 1) (hq : ∑ x ∈ s, q x = 1) :
    ∑ x ∈ s, ∑ y ∈ s, p x * q y * ((a x + b y) / 2) = ((∑ x ∈ s, p x * a x) + ∑ y ∈ s, q y * b y) / 2 := by
  calc ∑ x ∈ s, ∑ y ∈ s, p x * q y * ((a x + b y) / 2) =
        (∑ x ∈ s, ∑ y ∈ s, (p x * a x) * q y + ∑ x ∈ s, ∑ y ∈ s, p x * (q y * b y)) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring
    _ = _ := by rw [← Finset.sum_mul_sum, ← Finset.sum_mul_sum, hq, hp]; ring

theorem liftV_core (S : C.HidaSetting E Wp Wq) (Λ : ℕ → ℕ → Fin S.f → ℝ) (hpos : C.ThmPPos S)
    (hL : ∀ v, KB.LiftLoc S v fun b s => Λ b s v) (ε : ℝ) (hε : 0 < ε) (i s : ℕ) (hs1 : 1 ≤ s) (hsi : s ≤ i)
    (hir : i ≤ S.G.r) (w : S.W) (hcnt : S.base.cnt w + C.Kst ≤ S.Ntop) :
    ∃ θ : Finset (Fin S.f) → S.W × S.W → ℝ,
      (∀ A, TB.IsProb (S.base.Wb (S.base.cnt w + C.Kst) ×ˢ S.base.Wb (S.base.cnt w + C.Kst)) (θ A)) ∧
      ∀ (Y : Finset (TB.Pt E)) (κa κw κb : TB.Pt E → TB.Pt E → ℂ),
        (∀ h ∈ Y, TB.level h = i - s) → KB.BlockPSD Y Y κa κw κb →
        ∀ (t t' : Fin S.f → ℂ), (∀ v, t v ≠ 0) → (∀ v, t' v ≠ 0) → ∀ A : Finset (Fin S.f),
          (∏ v ∈ A, ‖(t v)⁻¹ - (t' v)⁻¹‖ ^ C.Kst) * ‖KB.NstV S ε i s w Y κw t t'‖ ≤
            (∏ v ∈ A, Λ (i - s + 1) s v ^ C.Kst) *
              ∑ x ∈ S.base.Wb (S.base.cnt w + C.Kst) ×ˢ S.base.Wb (S.base.cnt w + C.Kst), θ A x *
                (((KB.NstV S ε i s x.1 Y κa t t).re + (KB.NstV S ε i s x.2 Y κb t' t').re) / 2) := by
  have hlen : ∀ v, (w.1 v).length + C.Kst ≤ S.Ntop := fun v => by have := len_le_cnt S w v; omega
  have H := fun v => hL v (i - s + 1) s (by omega) hs1 (by omega) (w.1 v) ⟨w, rfl⟩ (hlen v)
  have hbi : i - s + 1 + s - 1 = i := by omega
  have hb1 : i - s + 1 - 1 = i - s := by omega
  simp only [hbi, hb1] at H
  choose Up θp Um θm hUp hUm hblk using H
  have hwid : ∀ v, (w.1 v).length + C.Kst ≤ S.base.cnt w + C.Kst := fun v => by
    have := len_le_cnt S w v; omega
  have hUp' : ∀ v, KB.LocProb S v (S.base.cnt w + C.Kst) (Up v) (θp v) := fun v =>
    ⟨(hUp v).1, fun a ha => ⟨((hUp v).2 a ha).1, le_trans ((hUp v).2 a ha).2 (hwid v)⟩⟩
  have hUm' : ∀ v, KB.LocProb S v (S.base.cnt w + C.Kst) (Um v) (θm v) := fun v =>
    ⟨(hUm v).1, fun a ha => ⟨((hUm v).2 a ha).1, le_trans ((hUm v).2 a ha).2 (hwid v)⟩⟩
  let U : Bool → Finset (Fin S.f) → Fin S.f → Finset (List C.Letter) := fun sg A v =>
    if v ∈ A then (if sg then Up v else Um v) else {w.1 v}
  let th : Bool → Finset (Fin S.f) → Fin S.f → List C.Letter → ℝ := fun sg A v =>
    if v ∈ A then (if sg then θp v else θm v) else fun a => if a = w.1 v then 1 else 0
  have hU : ∀ sg A v, KB.LocProb S v (S.base.cnt w + C.Kst) (U sg A v) (th sg A v) := by
    intro sg A v
    by_cases hv : v ∈ A
    · cases sg
      · simp only [U, th, hv, if_true, Bool.false_eq_true, if_false]; exact hUm' v
      · simp only [U, th, hv, if_true]; exact hUp' v
    · simp only [U, th, hv, if_false]; exact locProb_single S w v _ (by omega)
  have hP : ∀ sg A, TB.IsProb (S.base.Wb (S.base.cnt w + C.Kst)) (fun w' : S.W => ∏ v, th sg A v (w'.1 v)) :=
    fun sg A => isProb_prod S _ hcnt (U sg A) (th sg A) (hU sg A)
  refine ⟨fun A x => (∏ v, th true A v (x.1.1 v)) * ∏ v, th false A v (x.2.1 v), fun A => ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hP true A
    obtain ⟨g1, g2, g3⟩ := hP false A
    refine ⟨fun x => mul_nonneg (h1 _) (g1 _), fun x hx => ?_, ?_⟩
    · rw [Finset.mem_product, not_and_or] at hx
      rcases hx with hx | hx
      · simp only [h2 _ hx, zero_mul]
      · simp only [g2 _ hx, mul_zero]
    · rw [Finset.sum_product]
      dsimp only at h3 g3 ⊢
      rw [← Finset.sum_mul_sum, h3, g3, one_mul]
  intro Y κa κw κb hY hκ t t' ht ht' A
  have hYv : ∀ v, ∀ h ∈ Y.image (C.loc (S.σ v)), D.ptSize h = i - s := by
    intro v h hh
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
    rw [Formalism.FourierDecayAlt.P.JCx1.needs.ptSize_loc]
    exact hY p hp
  let Pt : Fin S.f → TB.Pt E → C.LPt := fun v h => C.loc (S.σ v) h ++ [(s, t v)]
  let Pt' : Fin S.f → TB.Pt E → C.LPt := fun v h => C.loc (S.σ v) h ++ [(s, t' v)]
  let sc : Fin S.f → ℝ := fun v => if v ∈ A then Λ (i - s + 1) s v ^ C.Kst else 1
  let aK : Bool → Fin S.f → C.LPt → C.LPt → ℂ := fun sg v p q =>
    (sc v : ℂ) * ∑ a ∈ U sg A v, (th sg A v a : ℂ) * KB.gN S v ε i a p q
  have haK : ∀ sg v, (aK sg v) = if v ∈ A then (fun p q => ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) *
      KB.mix S v ε i (if sg then Up v else Um v) (if sg then θp v else θm v) p q)
      else KB.gN S v ε i (w.1 v) := by
    intro sg v
    funext p q
    by_cases hv : v ∈ A
    · cases sg <;> simp [aK, sc, U, th, hv, KB.mix]
    · simp [aK, sc, U, th, hv]
  have hc : ∀ v, ∃ c : ℂ, ‖c‖ = (if v ∈ A then ‖(t v)⁻¹ - (t' v)⁻¹‖ ^ C.Kst else 1) ∧
      KB.BlockPSD Y Y (fun p q => aK true v (Pt v p) (Pt v q))
        (fun p q => c * KB.gN S v ε i (w.1 v) (Pt v p) (Pt' v q)) (fun p q => aK false v (Pt' v p) (Pt' v q)) := by
    intro v
    by_cases hv : v ∈ A
    · obtain ⟨u, hu, hB⟩ := hblk v ε hε (t v) (t' v) (Y.image (C.loc (S.σ v))) (ht v) (ht' v) (hYv v)
      have hB' := blockPSD_pull Y (C.loc (S.σ v)) _ _ _ hB
      refine ⟨u * ((t v)⁻¹ - (t' v)⁻¹) ^ C.Kst, by simp [hv, hu, norm_pow], ?_⟩
      rw [haK true v, haK false v]
      simp only [hv, if_true, Bool.false_eq_true, if_false]
      exact hB'
    · refine ⟨1, by simp [hv], ?_⟩
      rw [haK true v, haK false v]
      simp only [hv, if_false, one_mul]
      exact lift_block0 S hpos v ε hε i (by omega) w Y (Pt v) (Pt' v)
  choose c hcn hcB using hc
  have hS := block_schur2 Y κa κw κb hκ (fun v p q => aK true v (Pt v p) (Pt v q))
    (fun v p q => c v * KB.gN S v ε i (w.1 v) (Pt v p) (Pt' v q))
    (fun v p q => aK false v (Pt' v p) (Pt' v q)) hcB
  have hsz' : ∏ v, (S.sizeAt v (w.1 v) : ℂ) = (C.Word.size S.P w.1 : ℂ) := by
    simp only [C.Word.size, C.HidaSetting.sizeAt, Complex.ofReal_prod]
  have hLh : ∑ p ∈ Y, ∑ q ∈ Y, κw p q * ∏ v, (c v * KB.gN S v ε i (w.1 v) (Pt v p) (Pt' v q)) =
      (∏ v, c v) * KB.NstV S ε i s w Y κw t t' := by
    unfold KB.NstV KB.gN
    simp only [Finset.prod_mul_distrib, Finset.prod_div_distrib, hsz']
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  have hcp : ‖∏ v, c v‖ = ∏ v ∈ A, ‖(t v)⁻¹ - (t' v)⁻¹‖ ^ C.Kst := by
    rw [norm_prod, Finset.prod_congr rfl (fun v _ => hcn v)]
    convert prod_univ_ite (R := ℝ) A (fun v => ‖(t v)⁻¹ - (t' v)⁻¹‖ ^ C.Kst) using 3
  have hR : ∀ (sg : Bool) (κ : TB.Pt E → TB.Pt E → ℂ) (P : Fin S.f → TB.Pt E → C.LPt),
      (∑ p ∈ Y, ∑ q ∈ Y, κ p q * ∏ v, aK sg v (P v p) (P v q)).re =
      (∏ v ∈ A, Λ (i - s + 1) s v ^ C.Kst) * ∑ w' ∈ S.base.Wb (S.base.cnt w + C.Kst),
        (∏ v, th sg A v (w'.1 v)) *
          ((∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, S.gramLoc v ε i (w'.1 v) (P v h) (P v h')) /
            (C.Word.size S.P w'.1 : ℂ)).re := by
    intro sg κ P
    rw [rhs_eval2 S ε i Y κ _ hcnt (U sg A) (th sg A) (hU sg A) sc P P]
    congr 1
    convert prod_univ_ite (R := ℝ) A (fun v => Λ (i - s + 1) s v ^ C.Kst) using 3
  try dsimp only at hS
  rw [hLh, norm_mul, hcp, hR true κa Pt, hR false κb Pt'] at hS
  refine hS.trans (le_of_eq ?_)
  rw [Finset.sum_product]
  have hps := pair_sum (S.base.Wb (S.base.cnt w + C.Kst)) (fun x => ∏ v, th true A v (x.1 v))
    (fun y => ∏ v, th false A v (y.1 v)) (fun x => (KB.NstV S ε i s x Y κa t t).re)
    (fun y => (KB.NstV S ε i s y Y κb t' t').re) (hP true A).2.2 (hP false A).2.2
  dsimp only at hps ⊢
  rw [hps, ← mul_add, mul_div_assoc]
  rfl

end lift

end

end Formalism.FourierDecayAlt.P.PBB

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem lift_bound_below_top_all_places : Formalism.FourierDecayAlt.KB.LiftV :=
  fun _ _ _ _ _ _ _ _ _ _ S Λ hpos hL ε hε i s hs1 hsi hir w _ hcnt =>
    PBB.liftV_core S Λ hpos hL ε hε i s hs1 hsi hir w hcnt

end Formalism.FourierDecayAlt.P
end

section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def LocSup (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (n b : ℕ) (a : List C.Letter) (h : C.LPt) : Prop :=
  ∃ B : ℝ, ∀ t : ℂ, t ≠ 0 → ‖KB.gN S v ε (b + n - 1) a (h ++ [(n, t)]) (h ++ [(n, t)])‖ ≤ B

theorem psd_single_one {α : Type} (h : α) : TB.PSDOn ({h} : Finset α) (fun _ _ => (1 : ℂ)) := by
  unfold TB.PSDOn
  have hA : (Matrix.of fun (x y : ↥({h} : Finset α)) => (1 : ℂ)) =
      (Matrix.of fun (_ : ↥({h} : Finset α)) (_ : Unit) => (1 : ℂ)) *
        Matrix.conjTranspose (Matrix.of fun (_ : ↥({h} : Finset α)) (_ : Unit) => (1 : ℂ)) := by
    ext x y
    simp [Matrix.mul_apply]
  rw [hA]
  exact Matrix.posSemidef_self_mul_conjTranspose _

theorem dlB_pos (S : C.HidaSetting E Wp Wq) (hg : 0 < S.g) (b s : ℕ) : 0 < KB.dlB S b s := by
  have hd : (0 : ℝ) < ((|discr E| : ℤ) : ℝ) := by
    have := NumberField.discr_ne_zero E
    exact_mod_cast abs_pos.2 this
  have hrd : 0 < S6.rd E := Real.rpow_pos_of_pos hd _
  unfold KB.dlB D.deG
  have hg' : (0 : ℝ) < S.g := by exact_mod_cast hg
  refine div_pos ?_ (div_pos two_pos (mul_pos hrd (pow_pos hg' 3)))
  first
  | exact pow_pos hrd _
  | exact zpow_pos hrd _
  | exact Real.rpow_pos_of_pos hrd _

theorem exists_word_of_admissible_at_place (S : C.HidaSetting E Wp Wq) {v : Fin S.f} {a : List C.Letter} (ha : D.AdmAt S v a) :
    ∃ w : S.W, w.1 v = a := ha

theorem locSup_one (S : C.HidaSetting E Wp Wq) (hI : KB.IntAll S) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (b : ℕ)
    (hb : 1 ≤ b) (hbr : b ≤ S.G.r + 1) (a : List C.Letter) (ha : D.AdmAt S v a) (h : C.LPt)
    (hh : D.ptSize h = b - 1) : LocSup S v ε 1 b a h := by
  obtain ⟨w, hw⟩ := exists_word_of_admissible_at_place S ha
  obtain ⟨φ, -, hφ, ⟨Cφ, hCφ⟩, -⟩ := hI v ε hε b hb hbr w h h hh hh
  refine ⟨|Cφ| * ‖((S.sizeAt v a : ℝ) : ℂ)‖⁻¹, fun t ht => ?_⟩
  have hb1 : b + 1 - 1 = b := Nat.add_sub_cancel b 1
  unfold KB.gN
  rw [hb1, norm_div, div_eq_mul_inv, ← hw, ← hφ t ht]
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (norm_nonneg _))
  have h1 : ((1 + ‖t‖) ^ 3)⁻¹ ≤ (1 : ℝ) := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg t]))
  have h2 : 0 ≤ ((1 + ‖t‖) ^ 3)⁻¹ := inv_nonneg.2 (by positivity)
  calc ‖φ t‖ ≤ Cφ * ((1 + ‖t‖) ^ 3)⁻¹ := hCφ t
    _ ≤ |Cφ| * ((1 + ‖t‖) ^ 3)⁻¹ := mul_le_mul_of_nonneg_right (le_abs_self _) h2
    _ ≤ |Cφ| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |Cφ| := mul_one _

theorem mL_one (K : ℕ) (L : ℝ) (σ : crystallineComparison.V 1) : crystallineComparison.mL K (fun _ => L) σ = crystallineComparison.mfac K L ‖σ 0‖ := by
  simp [crystallineComparison.mL]

theorem offdiag_bound {Z : Type} (w : Z → Z → ℂ) (a b : Z → Z → ℂ) (p : Z) (Y : Finset Z) (hp : p ∈ Y)
    (hB : KB.BlockPSD Y Y a w b) (Ba Bb : ℝ) (ha : (a p p).re ≤ Ba) (hb : (b p p).re ≤ Bb) :
    ‖w p p‖ ^ 2 ≤ Ba * Bb := by
  have hpsd := hB
  unfold KB.BlockPSD TB.PSDOn at hpsd
  let f : Fin 2 → ↥(Y.disjSum Y) := ![⟨Sum.inl p, by simp [hp]⟩, ⟨Sum.inr p, by simp [hp]⟩]
  have hs := hpsd.submatrix f
  have hdet := hs.det_nonneg
  have hd0 := hs.diag_nonneg (i := 0)
  have hd1 := hs.diag_nonneg (i := 1)
  rw [Matrix.det_fin_two] at hdet
  simp [f, Matrix.submatrix_apply] at hdet hd0 hd1
  rw [Complex.le_def] at hdet
  rw [Complex.nonneg_iff] at hd0 hd1
  have hw : ‖w p p‖ ^ 2 ≤ (a p p).re * (b p p).re := by
    have h3 := hdet.1
    simp only [Complex.sub_re, Complex.mul_re, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq, ← hd0.2, ← hd1.2] at h3
    nlinarith [h3]
  calc ‖w p p‖ ^ 2 ≤ (a p p).re * (b p p).re := hw
    _ ≤ Ba * Bb := mul_le_mul ha hb hd1.1 (le_trans hd0.1 ha)

end

end Formalism.FourierDecayAlt.P.PBC
end

section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem re_mix_le (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (i : ℕ) (U : Finset (List C.Letter))
    (θ : List C.Letter → ℝ) (hθ : ∀ a, 0 ≤ θ a) (p : C.LPt) (B : List C.Letter → ℝ)
    (hB : ∀ u ∈ U, ‖KB.gN S v ε i u p p‖ ≤ B u) :
    (KB.mix S v ε i U θ p p).re ≤ ∑ u ∈ U, θ u * max (B u) 0 := by
  unfold KB.mix
  rw [Complex.re_sum]
  refine Finset.sum_le_sum fun u hu => ?_
  rw [Complex.re_ofReal_mul]
  exact mul_le_mul_of_nonneg_left
    ((Complex.re_le_norm _).trans ((hB u hu).trans (le_max_left _ _))) (hθ u)

private lemma two_mul_norm_le_add_of_psdOn_pair {α : Type} [DecidableEq α] (G : α → α → ℂ) (p q : α) (hpq : p ≠ q)
    (h : TB.PSDOn ({p, q} : Finset α) G) : 2 * ‖G p q‖ ≤ ‖G p p‖ + ‖G q q‖ := by
  set Y : Finset α := {p, q} with hY
  let e : Fin 2 → Y := ![⟨p, by simp [Y]⟩, ⟨q, by simp [Y]⟩]
  have hN := Matrix.PosSemidef.submatrix h e
  have hqp : G q p = conj (G p q) := by
    have h0 := hN.1.apply 1 0
    simp [e] at h0
    rw [← h0]
  by_cases hw : G p q = 0
  · rw [hw, norm_zero, mul_zero]
    positivity
  set w := G p q with hwdef
  set ζ : ℂ := conj w / (‖w‖ : ℂ) with hζ
  have hw' : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hw)
  have hcw : conj w * w = (‖w‖ : ℂ) ^ 2 := Complex.conj_mul' w
  have h1 : ζ * w = ‖w‖ := by
    rw [hζ, div_mul_eq_mul_div, hcw, pow_two, mul_div_assoc, div_self hw', mul_one]
  have h2 : conj ζ * conj w = ‖w‖ := by
    rw [← map_mul, h1, Complex.conj_ofReal]
  have hnz : ‖ζ‖ = 1 := by
    rw [hζ, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.2 hw)]
  have h3 : conj ζ * ζ = 1 := by
    rw [Complex.conj_mul', hnz]
    simp
  have key := hN.re_dotProduct_nonneg ![1, -ζ]
  have hform : star (![1, -ζ] : Fin 2 → ℂ) ⬝ᵥ
      Matrix.mulVec ((Matrix.of fun x y : Y => G x y).submatrix e e) ![1, -ζ] =
      G p p - ζ * w - conj ζ * G q p + conj ζ * ζ * G q q := by
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, e, w]
    try ring
  rw [hform, hqp, h1, h2, h3, one_mul] at key
  simp only [RCLike.re_to_complex, Complex.sub_re, Complex.add_re, Complex.ofReal_re] at key
  have ha := Complex.re_le_norm (G p p)
  have hb := Complex.re_le_norm (G q q)
  linarith

theorem gN_entry (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r + 1) (w : S.W) (p q : C.LPt) (B : ℝ) (hp : ‖KB.gN S v ε j (w.1 v) p p‖ ≤ B)
    (hq : ‖KB.gN S v ε j (w.1 v) q q‖ ≤ B) : ‖KB.gN S v ε j (w.1 v) p q‖ ≤ B := by
  by_cases hpq : p = q
  · subst hpq
    exact hp
  have hps := hpos v ε hε j hj w {p, q}
  have hcs := two_mul_norm_le_add_of_psdOn_pair (S.gramLoc v ε j (w.1 v)) p q hpq hps
  unfold KB.gN at hp hq ⊢
  rw [norm_div] at hp hq ⊢
  rcases (norm_nonneg (S.sizeAt v (w.1 v) : ℂ)).eq_or_lt with h0 | hs
  · rw [← h0, div_zero] at hp ⊢
    exact hp
  · rw [div_le_iff₀ hs] at hp hq ⊢
    linarith

theorem locSup_step (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (hg : 0 < S.g) (v : Fin S.f)
    (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : KB.LiftLoc S v fun b s => Λ b s v) (hGL : KB.GermLoc S v)
    (ε : ℝ) (hε : 0 < ε) (n : ℕ) (hn : 2 ≤ n) (b : ℕ) (hb : 1 ≤ b) (hbn : b + n ≤ S.G.r + 2)
    (hΛ0 : 0 ≤ Λ b (n - 1) v) (h : C.LPt) (hh : D.ptSize h = b - 1)
    (hIH : ∀ u, D.AdmAt S v u → u.length + (n - 2) * C.Kst ≤ S.Ntop → LocSup S v ε (n - 1) b u h)
    (a : List C.Letter) (ha : D.AdmAt S v a) (hlen : a.length + (n - 1) * C.Kst ≤ S.Ntop) :
    LocSup S v ε n b a h := by
  have hk : (n - 1) * C.Kst = (n - 2) * C.Kst + C.Kst := by
    have : n - 1 = (n - 2) + 1 := by omega
    rw [this, add_mul, one_mul]
  have hl2 : b + (n - 1) - 1 = b + n - 2 := by omega
  obtain ⟨Ba, hBa⟩ := hIH a ha (by omega)
  rw [hl2] at hBa
  obtain ⟨w, rfl⟩ := exists_word_of_admissible_at_place S ha

  have hsup : ∃ B : ℝ, ∀ p ∈ ({h} : Finset C.LPt), ∀ t : ℂ, t ≠ 0 →
      ‖KB.gN S v ε (b + n - 2) (w.1 v) (p ++ [(n - 1, t)]) (p ++ [(n - 1, t)])‖ ≤ B :=
    ⟨Ba, fun p hp t ht => by rw [Finset.mem_singleton] at hp; subst hp; exact hBa t ht⟩
  obtain ⟨hcont, Pua, Paa, hblk, ⟨B', hB'⟩, hlim⟩ :=
    hGL ε hε b n hb hn hbn (w.1 v) ha {h} (by simp [hh]) hsup

  obtain ⟨Up, θp, Um, θm, hUp, hUm, hLB⟩ := hLL b (n - 1) hb (by omega) (by omega) (w.1 v) ha (by omega)
  have hBu : ∀ u ∈ Up ∪ Um, LocSup S v ε (n - 1) b u h := by
    intro u hu
    rcases Finset.mem_union.1 hu with hu | hu
    · exact hIH u (hUp.2 u hu).1 (by have := (hUp.2 u hu).2; omega)
    · exact hIH u (hUm.2 u hu).1 (by have := (hUm.2 u hu).2; omega)
  choose! Bu hBu' using hBu
  set Bp := ∑ u ∈ Up, θp u * max (Bu u) 0 with hBp
  set Bq := ∑ u ∈ Um, θm u * max (Bu u) 0 with hBq
  have hBp0 : 0 ≤ Bp := Finset.sum_nonneg fun u _ => mul_nonneg (hUp.1.1 u) (le_max_right _ _)
  have hBq0 : 0 ≤ Bq := Finset.sum_nonneg fun u _ => mul_nonneg (hUm.1.1 u) (le_max_right _ _)
  set Bt := max (max Ba 0) (Bp + Bq) with hBt
  have hBt0 : 0 ≤ Bt := (le_max_right _ _).trans (le_max_left _ _)

  obtain ⟨i1, i2, hcov, -⟩ := pbc_lstdFacts 1 1 one_pos
  have := i1; have := i2
  have hgR : (0 : ℝ) < S.g := by exact_mod_cast hg
  obtain ⟨Lm, j1, j2, hLm⟩ := GlobalTheory.dual_smul_mem (Lstd 1 1) (S.g : ℝ) hgR.ne'
  have := j1; have := j2
  obtain ⟨Cs, -, hCsum⟩ := pbc_lstdSum
  obtain ⟨hsm, -⟩ := hCsum 1 1 (S.g : ℝ) (fun _ => Λ b (n - 1) v) one_pos hgR (fun _ => hΛ0)
  let D : Fin 1 → C.LPt → C.LPt → ℂ → ℂ := fun _ p q c =>
    KB.gN S v ε (b + n - 1) (w.1 v) (p ++ [(n, c)]) (q ++ [(n, c)])
  let U : Fin 1 → C.LPt × ℂ → C.LPt × ℂ → ℂ := fun _ p q =>
    KB.gN S v ε (b + n - 2) (w.1 v) (p.1 ++ [(n - 1, p.2⁻¹)]) (q.1 ++ [(n - 1, q.2⁻¹)])
  have hGD : GermData {h} U (fun _ => Pua) (fun _ => Paa) (fun _ σ p q => KB.hatB S v ε b n (w.1 v) σ p q) := by
    refine ⟨fun _ Xs hXs => hblk Xs hXs, ⟨max Ba B' ⊔ 0, le_max_right _ _, fun _ p hp x hx => ?_⟩,
      fun _ p hp q hq σ => (hlim p hp q hq σ).1, fun _ p hp q hq σ => (hlim p hp q hq σ).2.1,
      fun _ p hp q hq σ => (hlim p hp q hq σ).2.2⟩
    rw [Finset.mem_singleton] at hp; subst hp
    refine ⟨(hBa x⁻¹ (inv_ne_zero hx)).trans ?_, (hB' p (Finset.mem_singleton_self p) x hx).trans ?_⟩
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
  have hD : ∀ (v' : Fin 1) (z : ℂ), z ≠ 0 → TB.PSDOn ({h} : Finset C.LPt) (fun p q => D v' p q z) := by
    intro v' z _
    have := PBB.gN_psd S hpos v ε hε (b + n - 1) (by omega) w (({h} : Finset C.LPt).image fun p => p ++ [(n, z)])
    exact JCx1.decay.psd_pull _ _ this {h} (fun p => p ++ [(n, z)]) (fun p hp => Finset.mem_image_of_mem _ hp)

  have hF : ∀ σ ∈ crystallineComparison.dualSet (Lstd 1 1), ∀ x : crystallineComparison.V 1, Good x → Good (x + (S.g : ℝ) • σ) →
      ‖phi {h} (fun _ _ => (1 : ℂ)) U x (x + (S.g : ℝ) • σ)‖ ≤
        Bt * crystallineComparison.mL C.Kst (fun _ => Λ b (n - 1) v) ((S.g : ℝ) • σ) := by
    intro σ _ x hx hx'
    set t := (x 0)⁻¹ with ht_def
    set t' := ((x + (S.g : ℝ) • σ) 0)⁻¹ with ht'_def
    have ht : t ≠ 0 := inv_ne_zero (hx 0)
    have ht' : t' ≠ 0 := inv_ne_zero (hx' 0)
    have ephi : phi {h} (fun _ _ => (1 : ℂ)) U x (x + (S.g : ℝ) • σ) =
        KB.gN S v ε (b + n - 2) (w.1 v) (h ++ [(n - 1, t)]) (h ++ [(n - 1, t')]) := by
      simp [phi, U, t, t']
    rw [ephi, mL_one]
    set a0 := ‖((S.g : ℝ) • σ) 0‖
    have ediff : t⁻¹ - t'⁻¹ = -(((S.g : ℝ) • σ) 0) := by
      simp only [t, t', inv_inv, Pi.add_apply]; ring

    have hcs : ‖KB.gN S v ε (b + n - 2) (w.1 v) (h ++ [(n - 1, t)]) (h ++ [(n - 1, t')])‖ ≤ Ba :=
      gN_entry S hpos v ε hε _ (by omega) w _ _ Ba (hBa t ht) (hBa t' ht')

    obtain ⟨u, hu, hB⟩ := hLB ε hε t t' {h} ht ht' (by simp [hh])
    have hob := offdiag_bound _ _ _ h {h} (Finset.mem_singleton_self h) hB
      (Λ b (n - 1) v ^ C.Kst * Bp) (Λ b (n - 1) v ^ C.Kst * Bq) ?_ ?_
    rotate_left
    · simp only
      rw [show (((Λ b (n - 1) v ^ C.Kst : ℝ) : ℂ) * KB.mix S v ε (b + (n - 1) - 1) Up θp (h ++ [(n - 1, t)])
          (h ++ [(n - 1, t)])).re = Λ b (n - 1) v ^ C.Kst * (KB.mix S v ε (b + (n - 1) - 1) Up θp (h ++ [(n - 1, t)])
          (h ++ [(n - 1, t)])).re from Complex.re_ofReal_mul _ _]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hΛ0 _)
      rw [hl2]
      exact re_mix_le S v ε _ Up θp hUp.1.1 _ Bu fun u hu => by
        have := hBu' u (Finset.mem_union_left _ hu) t ht; rwa [hl2] at this
    · simp only
      rw [show (((Λ b (n - 1) v ^ C.Kst : ℝ) : ℂ) * KB.mix S v ε (b + (n - 1) - 1) Um θm (h ++ [(n - 1, t')])
          (h ++ [(n - 1, t')])).re = Λ b (n - 1) v ^ C.Kst * (KB.mix S v ε (b + (n - 1) - 1) Um θm
          (h ++ [(n - 1, t')]) (h ++ [(n - 1, t')])).re from Complex.re_ofReal_mul _ _]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hΛ0 _)
      rw [hl2]
      exact re_mix_le S v ε _ Um θm hUm.1.1 _ Bu fun u hu => by
        have := hBu' u (Finset.mem_union_right _ hu) t' ht'; rwa [hl2] at this
    rw [hl2, norm_mul, norm_mul, hu, one_mul, norm_pow, ediff, norm_neg] at hob
    set X := ‖KB.gN S v ε (b + n - 2) (w.1 v) (h ++ [(n - 1, t)]) (h ++ [(n - 1, t')])‖ with hX
    have hX0 : 0 ≤ X := norm_nonneg _
    have hl : a0 ^ C.Kst * X ≤ Λ b (n - 1) v ^ C.Kst * (Bp + Bq) := by
      have h1 : (a0 ^ C.Kst * X) ^ 2 ≤ (Λ b (n - 1) v ^ C.Kst * (Bp + Bq)) ^ 2 := by
        refine hob.trans ?_
        have hL := pow_nonneg hΛ0 C.Kst
        nlinarith [mul_nonneg hL hBp0, mul_nonneg hL hBq0, mul_nonneg (mul_nonneg hL hL) (mul_nonneg hBp0 hBq0)]
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h1
    unfold crystallineComparison.mfac
    split_ifs with h0
    · rw [mul_one]; exact hcs.trans ((le_max_left _ _).trans (le_max_left _ _))
    · have ha0 : 0 < a0 := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      rw [mul_min_of_nonneg _ _ hBt0, mul_one]
      refine le_min (hcs.trans ((le_max_left _ _).trans (le_max_left _ _))) ?_
      have h2 : X ≤ (Λ b (n - 1) v / a0) ^ C.Kst * (Bp + Bq) := by
        rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (pow_pos ha0 _)]
        linarith [hl]
      refine h2.trans ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (div_nonneg hΛ0 ha0.le) _)
  refine ⟨(∏ _v : Fin 1, KB.dlB S b n) *
    ∑' σ : crystallineComparison.dualSet (Lstd 1 1), Bt * crystallineComparison.mL C.Kst (fun _ => Λ b (n - 1) v) ((S.g : ℝ) • (σ : crystallineComparison.V 1)),
    fun t ht => ?_⟩
  have hH := herglotz_germ (H := C.LPt) (f := 1) {h} (fun _ _ => 1) (psd_single_one h) D hD
    (fun _ p hp q hq => (hcont p hp q hq).1) (fun _ p hp q hq => (hcont p hp q hq).2) (S.g : ℝ) hgR
    (fun _ => KB.dlB S b n) (fun _ => dlB_pos S hg b n) U (fun _ => Pua) (fun _ => Paa)
    (fun _ σ p q => KB.hatB S v ε b n (w.1 v) σ p q) hGD (fun _ _ _ _ => rfl) (Lstd 1 1) Lm hLm
    (fun σ => Bt * crystallineComparison.mL C.Kst (fun _ => Λ b (n - 1) v) ((S.g : ℝ) • σ)) (hsm.mul_left Bt) hF
    (fun _ => t) {fun _ => t} (by simp)
  rw [hcov, Finset.sum_singleton] at hH
  have hgood : Good (fun _ : Fin 1 => t) := fun _ => ht
  have hN : Nz {h} (fun _ _ => (1 : ℂ)) D (fun _ => t) =
      (KB.gN S v ε (b + n - 1) (w.1 v) (h ++ [(n, t)]) (h ++ [(n, t)])).re := by
    simp [Nz, hgood, Fz, D]
  rw [hN, one_pow, one_mul] at hH
  have h0 := psd_diag _ _ (PBB.gN_psd S hpos v ε hε (b + n - 1) (by omega) w {h ++ [(n, t)]})
    (Finset.mem_singleton_self _)
  have hc := Complex.nonneg_iff.1 h0
  have e : KB.gN S v ε (b + n - 1) (w.1 v) (h ++ [(n, t)]) (h ++ [(n, t)]) =
      ((KB.gN S v ε (b + n - 1) (w.1 v) (h ++ [(n, t)]) (h ++ [(n, t)])).re : ℂ) :=
    Complex.ext (by simp) (by simp [hc.2.symm])
  rw [e, Complex.norm_real, Real.norm_of_nonneg hc.1]
  exact hH

theorem locSup_all (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (hI : KB.IntAll S) (hg : 0 < S.g) (v : Fin S.f)
    (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : KB.LiftLoc S v fun b s => Λ b s v) (hGL : KB.GermLoc S v)
    (hΛ0 : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → 0 ≤ Λ b s v) (ε : ℝ) (hε : 0 < ε) :
    ∀ n, 1 ≤ n → ∀ b, 1 ≤ b → b + n ≤ S.G.r + 2 → ∀ h, D.ptSize h = b - 1 → ∀ a, D.AdmAt S v a →
      a.length + (n - 1) * C.Kst ≤ S.Ntop → LocSup S v ε n b a h := by
  intro n
  induction n with
  | zero => intro h0; omega
  | succ m ih =>
    intro _ b hb hbn h hh a ha hlen
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact locSup_one S hI v ε hε b hb (by omega) a ha h hh
    · refine locSup_step S hpos hg v Λ hLL hGL ε hε (m + 1) (by omega) b hb hbn
        (by rw [Nat.add_sub_cancel]; exact hΛ0 b m hb hm (by omega)) h hh ?_ a ha hlen
      intro u hu hulen
      have e1 : m + 1 - 2 = m - 1 := by omega
      rw [e1] at hulen
      rw [Nat.add_sub_cancel]
      exact ih hm b hb (by omega) h hh u hu hulen

end

end Formalism.FourierDecayAlt.P.PBC
end
