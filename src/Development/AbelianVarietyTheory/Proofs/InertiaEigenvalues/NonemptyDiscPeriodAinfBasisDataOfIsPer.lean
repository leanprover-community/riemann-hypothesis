import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClosedDiscExtensionOfPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFlatRadiusIdealFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionExtendsToAinfDiscRings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedPeriodsDiscAinfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodsGaloisActionEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralWittLatticeBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeFrobeniusRationalColumns
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitOfSaturated
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedMembershipLimit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodModuleIsClosedLAdic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedDiscLinearDisjointOverPowerSeriesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeDiscSpanFrobeniusStable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NullPowerSeriesOfNullAinfMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinExistsAdicSumOfNullFamily
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfJAdicLimitEqDiscSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscCoefficientsTopologicallyFreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMemSpanCoeffPeriodPowStatement

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineDiscPeriods_galois_action_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ g : ↥(GK K), bk.FixFlat g → ∀ G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (Per.σA (g : GQ l)) G → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → ∀ x, G (j x) = j x) ∧ bk.iA τ ^ s.N • ((ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * s.W.map G) = G (bk.iA τ) ^ s.N • s.W := by
  first | exact @GlobalTheory.BSP.seed_gal_periods | exact GlobalTheory.BSP.seed_gal_periods | (intros; apply GlobalTheory.BSP.seed_gal_periods <;> assumption)
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralWittLattice_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (Y1 : Matrix (Fin d) (Fin d) (WCb l)), Y1.det ≠ 0 → ∃ (m : ℕ) (P Y' : Matrix (Fin d) (Fin d) (WCb l)), (∀ i j, P i j ∈ bk.OE) ∧ P.det ≠ 0 ∧ (l : WCb l) ^ m • Y' = Y1 * P ∧ (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → ∀ n : ℕ, (∀ i, (l : WCb l) ^ n ∣ (Y1 *ᵥ v) i) → ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (l : WCb l) ^ m • v = (l : WCb l) ^ n • (P *ᵥ w)) ∧ ∀ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) → (∀ i, (l : WCb l) ∣ (Y' *ᵥ w) i) → ∀ i, (l : WCb l) ∣ w i := by
  first | exact @GlobalTheory.SatLattice.exists_lattice_basis | exact GlobalTheory.SatLattice.exists_lattice_basis | (intros; apply GlobalTheory.SatLattice.exists_lattice_basis <;> assumption)
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLattice_frobenius_rational_columns : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y1.det ≠ 0 → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W * Z1.map j = Y1.map bk.iA) → ∃ (δ : bk.S) (A1 : Matrix (Fin d) (Fin d) (bk.S)), δ ≠ 0 ∧ bk.ev δ • Y1.map WittVector.frobenius = Y1 * A1.map bk.ev := by
  first | exact @GlobalTheory.BSP.FrobRational.main | exact GlobalTheory.BSP.FrobRational.main | (intros; apply GlobalTheory.BSP.FrobRational.main <;> assumption)
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_of_saturated' : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (Y A : Matrix (Fin d) (Fin d) (WCb l)), Y.det ≠ 0 → (∀ i j, A i j ∈ bk.OE) → Y.map (frobW l) = Y * A → (∀ g : ↥(GK K), bk.FixFlat g → ∃ R : Matrix (Fin d) (Fin d) (WCb l), IsUnit R ∧ R * Y.map (galW l (g : GQ l)) = Y) → (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → (∀ i, ((l : ℕ) : WCb l) ∣ Y.mulVec v i) → ∀ i, ((l : ℕ) : WCb l) ∣ v i) → IsUnit Y := by
  first | exact @GlobalTheory.SatInvUnit.isUnit_of_saturated | exact GlobalTheory.SatInvUnit.isUnit_of_saturated | (intros; apply GlobalTheory.SatInvUnit.isUnit_of_saturated <;> assumption)
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.EtaleLattice

theorem exists_frob_matrix {R : Type} [CommRing R] [IsDomain R] (O : Subring R) (φ : R →+* R) (p : R) (hp : p ≠ 0)
    (hφp : φ p = p) (hφO : ∀ w ∈ O, φ w ∈ O) {d : ℕ} (Y A P Y' : Matrix (Fin d) (Fin d) R) (k m : ℕ) (u u' : R)
    (hu' : u' ∈ O) (huu : u * u' = 1) (hA : ∀ i j, A i j ∈ O) (hP : ∀ i j, P i j ∈ O)
    (hφ : (p ^ k * u) • Y.map φ = Y * A) (hY' : p ^ m • Y' = Y * P)
    (hlat : ∀ v : Fin d → R, (∀ i, v i ∈ O) → ∀ n : ℕ, (∀ i, p ^ n ∣ (Y *ᵥ v) i) →
      ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ p ^ m • v = p ^ n • (P *ᵥ w)) :
    ∃ B : Matrix (Fin d) (Fin d) R, (∀ i j, B i j ∈ O) ∧ Y'.map φ = Y' * B := by
  have cancel : ∀ (n : ℕ) (M N : Matrix (Fin d) (Fin d) R), p ^ n • M = p ^ n • N → M = N := by
    intro n M N h
    refine Matrix.ext fun i j => ?_
    exact mul_left_cancel₀ (pow_ne_zero n hp) (congrFun (congrFun h i) j)
  have h1 : p ^ m • Y'.map φ = Y.map φ * P.map φ := by
    rw [← Matrix.map_mul, ← hY']
    refine Matrix.ext fun i j => ?_
    simp [hφp]
  set V : Matrix (Fin d) (Fin d) R := u' • (A * P.map φ) with hV
  have hVO : ∀ i j, V i j ∈ O := by
    intro i j
    rw [hV, Matrix.smul_apply, Matrix.mul_apply]
    exact O.mul_mem hu' (O.sum_mem fun c _ => O.mul_mem (hA i c) (hφO _ (hP c j)))
  have h2 : Y * V = p ^ (k + m) • Y'.map φ := by
    rw [hV, Matrix.mul_smul, ← Matrix.mul_assoc, ← hφ, Matrix.smul_mul, ← h1, smul_smul, smul_smul]
    congr 1
    linear_combination (p ^ k * p ^ m) * huu
  have h3 : ∀ j, ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ p ^ m • (fun i => V i j) = p ^ (k + m) • (P *ᵥ w) := by
    intro j
    refine hlat _ (fun i => hVO i j) _ fun i => ⟨φ (Y' i j), ?_⟩
    exact congrFun (congrFun h2 i) j
  choose w hwO hw using h3
  refine ⟨Matrix.of fun i j => w j i, fun i j => hwO j i, ?_⟩
  have h4 : p ^ m • V = p ^ (k + m) • (P * Matrix.of fun i j => w j i) := by
    refine Matrix.ext fun i j => ?_
    exact congrFun (hw j) i
  apply cancel (k + m)
  apply cancel m
  rw [← h2, ← Matrix.mul_smul, h4, Matrix.mul_smul, ← Matrix.mul_assoc, ← hY', Matrix.smul_mul, smul_comm]

theorem isUnit_saturated_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (δ : bk.S) (A1 : Matrix (Fin d) (Fin d) (bk.S)), (Y1.map (inclW l)).det ≠ 0 → δ ≠ 0 → bk.ev δ • Y1.map WittVector.frobenius = Y1 * A1.map bk.ev → (∀ g : ↥(GK K), bk.FixFlat g → τ ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y1.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • Y1) → ∀ (m : ℕ) (P Y' : Matrix (Fin d) (Fin d) (WCb l)), (∀ i j, P i j ∈ bk.OE) → P.det ≠ 0 → (l : WCb l) ^ m • Y' = Y1.map (inclW l) * P → (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → ∀ n : ℕ, (∀ i, (l : WCb l) ^ n ∣ (Y1.map (inclW l) *ᵥ v) i) → ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (l : WCb l) ^ m • v = (l : WCb l) ^ n • (P *ᵥ w)) → (∀ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) → (∀ i, (l : WCb l) ∣ (Y' *ᵥ w) i) → ∀ i, (l : WCb l) ∣ w i) → IsUnit Y' := by
  intro l hl K bk τ hτ d N ρ hρ Y1 δ A1 hdet hδ hφ hg m P Y' hP hPdet hY' hlat hsat
  obtain ⟨-, -, h3, -, -, h6, h7⟩ := GlobalTheory.T.integral_elements_unit_factorization l K bk
  obtain ⟨ht1, -, -, ht4⟩ := GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ
  haveI : PerfectRing (Cb l) l := by
    refine PerfectRing.ofSurjective _ l fun x => ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
    obtain ⟨a', rfl⟩ := surjective_frobenius (OCb l) l a
    obtain ⟨b', rfl⟩ := surjective_frobenius (OCb l) l b
    exact ⟨algebraMap (OCb l) (Cb l) a' / algebraMap (OCb l) (Cb l) b', by
      simp [frobenius_def, div_pow, map_pow]⟩
  have hl0 : (l : WCb l) ≠ 0 := WittVector.p_nonzero l (Cb l)
  have hlu : ¬ IsUnit (l : bk.S) := fun h => by
    have := h.map bk.evW
    rw [map_natCast] at this
    exact (WittVector.irreducible l (k := Cb l)).not_isUnit this
  have hev : ∀ s, bk.evW s ∈ bk.OE := fun s n => ⟨0, s, 0, by simp⟩
  obtain ⟨k, δ', hnd, rfl⟩ := WfDvdMonoid.max_power_factor' hδ hlu
  obtain ⟨u', hu', huu⟩ := h3 δ' hnd
  have hφW : ((l : WCb l) ^ k * bk.evW δ') • (Y1.map (inclW l)).map (frobW l).toRingHom =
      Y1.map (inclW l) * A1.map bk.evW := by
    have := congrArg (fun M => Matrix.map M (inclW l)) hφ
    simp only [Matrix.map_mul] at this
    rw [show A1.map bk.evW = (A1.map bk.ev).map (inclW l) from rfl, ← this]
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
    rw [BK.evW, RingHom.comp_apply, ← GlobalTheory.Prism.frobW_inclW]
    rfl
  obtain ⟨B, hB, hBφ⟩ := exists_frob_matrix bk.OE (frobW l).toRingHom (l : WCb l) hl0 (map_natCast _ _) h7
    (Y1.map (inclW l)) (A1.map bk.evW) P Y' k m (bk.evW δ') u' hu' huu (fun i j => hev _) hP hφW hY' hlat
  refine GlobalTheory.T.isUnit_of_saturated' l K bk d Y' B ?_ hB hBφ ?_ hsat
  · intro h0
    have := congrArg Matrix.det hY'
    rw [Matrix.det_smul, h0, mul_zero, Matrix.det_mul] at this
    exact mul_ne_zero hdet hPdet this.symm
  · intro g hfix
    obtain ⟨t, ht⟩ := ht1
    obtain ⟨s, hs⟩ := ht4 (g : GQ l)
    set Z : Matrix (Fin d) (Fin d) (WCb l) := ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) with hZ
    have hZu : IsUnit Z := ((hρ g).map (algebraMap ℤ_[l] (Ainf l)).mapMatrix).map (inclW l).mapMatrix
    have e1 : (t : WCb l) ^ N • (Z * (Y1.map (inclW l)).map (galW l (g : GQ l))) =
        (s : WCb l) ^ N • Y1.map (inclW l) := by
      have := congrArg (fun M => Matrix.map M (inclW l)) (hg g hfix)
      have e : (Y1.map (inclW l)).map (galW l (g : GQ l)) = (Y1.map (Per.σA (g : GQ l))).map (inclW l) := by
        refine Matrix.ext fun i j => ?_
        exact GlobalTheory.Prism.galW_inclW _ _
      rw [e, hZ, ← Matrix.map_mul, ht, hs]
      refine Matrix.ext fun i j => ?_
      have := congrFun (congrFun this i) j
      simpa only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow] using this
    have e2 : (l : WCb l) ^ m • Y'.map (galW l (g : GQ l)) = (Y1.map (inclW l)).map (galW l (g : GQ l)) * P := by
      have eP : P.map (galW l (g : GQ l)) = P := by
        refine Matrix.ext fun i j => ?_
        exact h6 g hfix _ (hP i j)
      rw [← eP, ← Matrix.map_mul, ← hY']
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
    refine ⟨((s⁻¹ * t) ^ N : (WCb l)ˣ) • Z, ?_, ?_⟩
    · exact hZu.smul _
    · have e3 : (l : WCb l) ^ m • ((((s⁻¹ * t) ^ N : (WCb l)ˣ) • Z) * Y'.map (galW l (g : GQ l))) =
          (l : WCb l) ^ m • Y' := by
        rw [← Matrix.mul_smul, e2, hY', ← Matrix.mul_assoc, Units.smul_def, Matrix.smul_mul, Units.val_pow_eq_pow_val,
          Units.val_mul, mul_pow, mul_smul, e1, smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul]
      refine Matrix.ext fun i j => ?_
      exact mul_left_cancel₀ (pow_ne_zero m hl0) (congrFun (congrFun e3 i) j)

end GlobalTheory.EtaleLattice
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_saturated_basis_etale_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (δ : bk.S) (A1 : Matrix (Fin d) (Fin d) (bk.S)), (Y1.map (inclW l)).det ≠ 0 → δ ≠ 0 → bk.ev δ • Y1.map WittVector.frobenius = Y1 * A1.map bk.ev → (∀ g : ↥(GK K), bk.FixFlat g → τ ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y1.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • Y1) → ∀ (m : ℕ) (P Y' : Matrix (Fin d) (Fin d) (WCb l)), (∀ i j, P i j ∈ bk.OE) → P.det ≠ 0 → (l : WCb l) ^ m • Y' = Y1.map (inclW l) * P → (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → ∀ n : ℕ, (∀ i, (l : WCb l) ^ n ∣ (Y1.map (inclW l) *ᵥ v) i) → ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (l : WCb l) ^ m • v = (l : WCb l) ^ n • (P *ᵥ w)) → (∀ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) → (∀ i, (l : WCb l) ∣ (Y' *ᵥ w) i) → ∀ i, (l : WCb l) ∣ w i) → IsUnit Y' := by
  atlas_forward_decl GlobalTheory.EtaleLattice.isUnit_saturated_basis
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_disc_period_module_isClosed_lAdic : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ y : ℕ → Fin d → Ainf l, (∀ n, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) (y n)) → (∀ n a, (l : Ainf l) ^ n ∣ y (n + 1) a - y n a) → ∀ z : Fin d → Ainf l, (∀ n a, (l : Ainf l) ^ n ∣ z a - y n a) → (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) z := by
  first | exact @GlobalTheory.BSP.seed_module_lAdic_closed | exact GlobalTheory.BSP.seed_module_lAdic_closed | (intros; apply GlobalTheory.BSP.seed_module_lAdic_closed <;> assumption)
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP

private theorem map_mulVec_fun {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (f : R →+* S)
    (M : Matrix (Fin d) (Fin d) R) (v : Fin d → R) :
    (fun a => f ((M *ᵥ v) a)) = M.map f *ᵥ fun a => f (v a) := funext fun a => RingHom.map_mulVec f M v a

private theorem det_map_ringHom {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (f : R →+* S)
    (M : Matrix (Fin d) (Fin d) R) : (M.map f).det = f M.det := (RingHom.map_det f M).symm

private theorem adjugate_map_ringHom {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (f : R →+* S)
    (M : Matrix (Fin d) (Fin d) R) : (M.map f).adjugate = M.adjugate.map f := (RingHom.map_adjugate f M).symm

theorem rational_in_columns : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), (Y1.map (inclW l)).det ≠ 0 → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W * Z1.map j = Y1.map bk.iA) → ∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y → ∃ (δ : bk.S) (c : Fin d → bk.S), δ ≠ 0 ∧ (fun a => bk.ev δ * y a) = Y1 *ᵥ fun a => bk.ev (c a) := by
  intro l _ K bk τ hτ d ρ hρ s Y1 Z1 hdet hWZ y hy
  obtain ⟨x, hx⟩ := hy
  have hl : (1 : ℝ≥0) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have he : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
  have hρ0 : 0 < bk.ρ₀ := NNReal.rpow_pos (zero_lt_one.trans hl)
  have hρ1 : bk.ρ₀ < 1 := NNReal.rpow_lt_one_of_one_lt_of_neg hl (by simp only [Left.neg_neg_iff]; positivity)
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk (Ainf l) bk.ev ι TB bk.ρ₀ hρ0 hρ1).1
  have hXn : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ0
  let j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) bk.ev hXn
  have hj : IsDiscMap bk.ev j := isDiscMap_map _ _
  have hWZj := hWZ j hj
  have hxj := hx j hj
  have hD : Y1.det ≠ 0 := by
    intro h; apply hdet; rw [det_map_ringHom, h, map_zero]
  have hdetA : bk.iA Y1.det = (s.W).det * j Z1.det := by
    rw [← det_map_ringHom, ← hWZj, det_mul, det_map_ringHom]
  have hΔ : Z1.det ≠ 0 := by
    intro h; apply hD; apply hinj; rw [hdetA, h, map_zero, mul_zero, map_zero]
  have h1 : Y1.map bk.iA *ᵥ (fun a => j ((Z1.adjugate *ᵥ x) a)) = j Z1.det • fun a => bk.iA (y a) := by
    rw [map_mulVec_fun j, ← hWZj, ← adjugate_map_ringHom, mulVec_mulVec, Matrix.mul_assoc, mul_adjugate,
      det_map_ringHom, Matrix.mul_smul, Matrix.mul_one, smul_mulVec, hxj]
  have h2 : bk.iA Y1.det • (fun a => j ((Z1.adjugate *ᵥ x) a)) =
      j Z1.det • fun a => bk.iA ((Y1.adjugate *ᵥ y) a) := by
    have h3 : (Y1.map bk.iA).adjugate *ᵥ (Y1.map bk.iA *ᵥ (fun a => j ((Z1.adjugate *ᵥ x) a))) =
        (Y1.map bk.iA).adjugate *ᵥ (j Z1.det • fun a => bk.iA (y a)) := by rw [h1]
    rw [mulVec_mulVec, adjugate_mul, det_map_ringHom, smul_mulVec, one_mulVec, mulVec_smul,
      adjugate_map_ringHom, ← map_mulVec_fun] at h3
    exact h3
  have key : ∀ a, ∃ δ c : bk.S, δ ≠ 0 ∧ bk.ev δ * (Y1.adjugate *ᵥ y) a = bk.ev c * Y1.det := fun a =>
    GlobalTheory.T.ainf_closedDisc_linearDisjoint_over_powerSeries l K bk (Ainf l) bk.ev ι TB j hj ((Y1.adjugate *ᵥ y) a) Y1.det ((Z1.adjugate *ᵥ x) a) Z1.det
      hΔ hD (by
        have h4 := congrFun h2 a
        simp only [Pi.smul_apply, smul_eq_mul] at h4
        calc _ = j Z1.det * bk.iA ((Y1.adjugate *ᵥ y) a) := mul_comm _ _
          _ = _ := h4.symm)
  choose δs cs hδ hc using key
  refine ⟨∏ a, δs a, fun a => cs a * ∏ b ∈ Finset.univ.erase a, δs b,
    Finset.prod_ne_zero_iff.2 fun a _ => hδ a, ?_⟩
  have hw : ∀ a, bk.ev (∏ b, δs b) * (Y1.adjugate *ᵥ y) a =
      Y1.det * bk.ev (cs a * ∏ b ∈ Finset.univ.erase a, δs b) := by
    intro a
    rw [← Finset.mul_prod_erase Finset.univ δs (Finset.mem_univ a), map_mul, map_mul, mul_comm (bk.ev (δs a)),
      mul_assoc, hc a]
    ring
  have hYw : Y1 *ᵥ (Y1.adjugate *ᵥ y) = Y1.det • y := by
    rw [mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec]
  have hcancel : Y1.det • (fun a => bk.ev (∏ b, δs b) * y a) =
      Y1.det • (Y1 *ᵥ fun a => bk.ev (cs a * ∏ b ∈ Finset.univ.erase a, δs b)) := by
    calc Y1.det • (fun a => bk.ev (∏ b, δs b) * y a) = bk.ev (∏ b, δs b) • (Y1 *ᵥ (Y1.adjugate *ᵥ y)) := by
          rw [hYw]; funext a; simp only [Pi.smul_apply, smul_eq_mul]; ring
      _ = Y1 *ᵥ (bk.ev (∏ b, δs b) • (Y1.adjugate *ᵥ y)) := by rw [mulVec_smul]
      _ = Y1 *ᵥ (Y1.det • fun a => bk.ev (cs a * ∏ b ∈ Finset.univ.erase a, δs b)) := by
          congr 1; funext a; simp only [Pi.smul_apply, smul_eq_mul]; exact hw a
      _ = _ := by rw [mulVec_smul]
  exact smul_right_injective _ hD hcancel

end GlobalTheory.BSP
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLattice_rational_in_columns : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), (Y1.map (inclW l)).det ≠ 0 → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W * Z1.map j = Y1.map bk.iA) → ∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y → ∃ (δ : bk.S) (c : Fin d → bk.S), δ ≠ 0 ∧ (fun a => bk.ev δ * y a) = Y1 *ᵥ fun a => bk.ev (c a) := by
  atlas_forward_decl GlobalTheory.BSP.rational_in_columns
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLattice_discSpan_frobenius_stable : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y → (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) (fun a => WittVector.frobenius (y a)) := by
  first | exact @GlobalTheory.BSP.seed_span_frobenius_stable | exact GlobalTheory.BSP.seed_span_frobenius_stable | (intros; apply GlobalTheory.BSP.seed_span_frobenius_stable <;> assumption)
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section
namespace GlobalTheory.BSP.HeightSprime

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) → (∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y ↔ ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a)) → ∃ (k : ℕ) (S' : Matrix (Fin d) (Fin d) (Ainf l)), Y * S' = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
  intro l _ K bk τ hτ d ρ hρ s Y hY hP
  obtain ⟨ι, TB, k, v, Z, hnull, hWZ, hsum⟩ := GlobalTheory.T.exists_bounded_periods_disc_ainf l K bk τ hτ d ρ hρ s
  have hcol : ∀ i (b : Fin d), ∃ c : Fin d → bk.S, (fun a => v i a b) = Y *ᵥ fun a => bk.ev (c a) := by
    intro i b
    refine (hP _).1 ⟨fun a => Z i a b, fun j hj => ?_⟩
    funext a
    have h := congrFun (congrFun (hWZ j hj i) a) b
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using h
  choose σc hσc using hcol
  set σ : ι → Matrix (Fin d) (Fin d) bk.S := fun i => Matrix.of fun a b => σc i b a with hσdef
  have hv : ∀ i, v i = Y * (σ i).map bk.ev := by
    intro i
    refine Matrix.ext fun a b => ?_
    have h := congrFun (hσc i b) a
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, σ] using h
  have hσn := GlobalTheory.T.null_powerSeries_of_null_ainf_mul l K bk ι TB d Y hY σ (fun n a b => by simpa only [← hv] using hnull n a b)
  have hL : ∀ c b : Fin d, ∃ L : Ainf l, ∀ n : ℕ, ∃ F : Finset ι, ∀ G : Finset ι, F ⊆ G →
      L - ∑ i ∈ G, bk.ev (σ i c b) * TB.b i ∈ (bk.J ^ n).map bk.ev :=
    fun c b => GlobalTheory.T.breuilKisin_exists_adic_sum_of_null_family l K bk ι TB (fun i => σ i c b) (fun n => hσn n c b)
  choose L hL using hL
  refine ⟨k, Matrix.of L, ?_⟩
  refine Matrix.ext fun a b => ?_
  refine GlobalTheory.T.ainf_jAdic_limit_eq_disc_sum l K bk ι TB (fun i => v i a b * TB.b i) _ _ ?_ ?_
  · simpa [Matrix.smul_apply, Matrix.one_apply] using hsum a b
  · classical
    intro n
    choose F hF using fun c => hL c b n
    refine ⟨Finset.univ.biUnion F, fun G hG => ?_⟩
    have e : (Y * Matrix.of L) a b - ∑ i ∈ G, v i a b * TB.b i =
        ∑ c, Y a c * (L c b - ∑ i ∈ G, bk.ev (σ i c b) * TB.b i) := by
      simp only [hv, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib,
        Finset.sum_mul, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_left _ _
      (hF c G ((Finset.subset_biUnion_of_mem F (Finset.mem_univ c)).trans hG))
end GlobalTheory.BSP.HeightSprime
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basis_dvd_tauPow_lPow_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) → (∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y ↔ ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a)) → ∃ (k : ℕ) (S' : Matrix (Fin d) (Fin d) (Ainf l)), Y * S' = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
  atlas_forward_decl GlobalTheory.BSP.HeightSprime.main
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP

theorem breuilKisinDatum_radius_pos_lt_one {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have h1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < 1 / (bk.Ep.natDegree : ℝ) := by
    have := bk.deg_pos
    positivity
  refine ⟨NNReal.rpow_pos (by exact_mod_cast hl.out.pos), ?_⟩
  exact NNReal.rpow_lt_one_of_one_lt_of_neg h1 (neg_neg_of_pos he)

theorem height_Z_isUnit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ)
    (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (k : ℕ)
    (S' : Matrix (Fin d) (Fin d) (Ainf l)),
    Y * S' = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) →
    (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W * Z.map j = Y.map bk.iA) → IsUnit Z := by
  intro l _ K bk τ hτ d ρ _ s Y Z k S' hYS hW
  obtain ⟨hρ0, hρ1⟩ := breuilKisinDatum_radius_pos_lt_one bk
  have hu : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ0
  let j0 : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map (u := (X : bk.S)) (ρ := bk.ρ₀) bk.ev hu
  have hj0 : IsDiscMap bk.ev j0 := isDiscMap_map bk.ev hu
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  obtain ⟨cD, hcD1, hcD2, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk (Ainf l) bk.ev ι TB bk.ρ₀ hρ0 hρ1 j0 hj0
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_mem_span_coeff_period_pow l K bk τ hτ ι TB (2 * s.N * d)

  set δ := Z.det with hδ
  have hdet : j0 δ * (s.W.det * bk.iA S'.det) =
      bk.iA (bk.ev ((l : bk.S) ^ (k * d)) * τ ^ (2 * s.N * d)) := by
    have h1 := congrArg (fun M => bk.iA M.det) hYS
    simp only [det_mul, det_smul, det_one, mul_one, Fintype.card_fin] at h1
    have h2 : bk.iA Y.det = s.W.det * j0 δ := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hW j0 hj0, det_mul, hδ, RingHom.map_det,
        RingHom.mapMatrix_apply]
    rw [map_mul, h2] at h1
    have e : bk.ev ((l : bk.S) ^ (k * d)) * τ ^ (2 * s.N * d) = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) ^ d := by
      rw [map_pow, map_natCast]; ring
    rw [e, ← h1]
    ring
  have hdvd : ∀ i, δ ∣ toDisc l (X : bk.S) bk.ρ₀ (TB.c i (τ ^ (2 * s.N * d))) := by
    intro i
    have h3 := congrArg (cD i) hdet
    rw [hcD2, hcD1, TB.c_mul, map_mul (toDisc l (X : bk.S) bk.ρ₀)] at h3
    have hunit : IsUnit (toDisc l (X : bk.S) bk.ρ₀ ((l : bk.S) ^ (k * d))) := by
      rw [map_pow, map_natCast]; exact (isUnit_l_disc l _ _).pow _
    exact (hunit.dvd_mul_left).1 ⟨_, h3.symm⟩
  have hle : Ideal.span (Set.range fun i => TB.c i (τ ^ (2 * s.N * d))) ≤
      (Ideal.span {δ}).comap (toDisc l (X : bk.S) bk.ρ₀) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.mem_span_singleton.2 (hdvd i)
  have hl := Ideal.mem_span_singleton.1 (hle hr)
  rw [map_pow, map_natCast] at hl
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_of_dvd_unit hl ((isUnit_l_disc l _ _).pow _)

end GlobalTheory.BSP
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_discBasis_crystallineLattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (k : ℕ) (S' : Matrix (Fin d) (Fin d) (Ainf l)), Y * S' = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W * Z.map j = Y.map bk.iA) → IsUnit Z := by
  atlas_forward_decl GlobalTheory.BSP.height_Z_isUnit
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.HeightAprime

theorem dvd_of_dvd_prime_pow_mul {R : Type} [CommRing R] [IsDomain R] {p a b : R} (hp : Prime p)
    (ha : ¬ p ∣ a) : ∀ n : ℕ, a ∣ p ^ n * b → a ∣ b
  | 0, h => by simpa using h
  | n + 1, h => by
    obtain ⟨x, hx⟩ := h
    have hpx : p ∣ a * x := ⟨p ^ n * b, by rw [← hx]; ring⟩
    obtain ⟨y, rfl⟩ := (hp.dvd_or_dvd hpx).resolve_left ha
    refine dvd_of_dvd_prime_pow_mul hp ha n ⟨y, mul_left_cancel₀ hp.ne_zero ?_⟩
    linear_combination hx

theorem C_dvd_iff {R : Type} [CommRing R] (p : R) (f : R⟦X⟧) :
    C p ∣ f ↔ ∀ n, p ∣ coeff n f := by
  constructor
  · rintro ⟨g, rfl⟩ n
    rw [coeff_C_mul]; exact dvd_mul_right _ _
  · intro h
    refine ⟨mk fun n => (h n).choose, ?_⟩
    ext n
    rw [coeff_C_mul, coeff_mk]
    exact (h n).choose_spec

theorem prime_C {R : Type} [CommRing R] [IsDomain R] {p : R} (hp : Prime p) : Prime (C p : R⟦X⟧) := by
  haveI : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  let q : R →+* R ⧸ Ideal.span {p} := Ideal.Quotient.mk _
  have key : ∀ f : R⟦X⟧, C p ∣ f ↔ PowerSeries.map q f = 0 := by
    intro f
    rw [C_dvd_iff]
    constructor
    · intro h; ext n
      rw [coeff_map, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 (h n))
    · intro h n
      have := congrArg (coeff n) h
      rw [coeff_map, map_zero] at this
      exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 this)
  refine ⟨fun h => hp.ne_zero (by simpa using congrArg (constantCoeff) h), fun h => hp.not_unit ?_, ?_⟩
  · simpa using h.map (constantCoeff (R := R))
  · intro f g hfg
    rw [key, key]
    rw [key, map_mul] at hfg
    exact mul_eq_zero.1 hfg

theorem prime_l {l : ℕ} [Fact l.Prime] (a : ℕ) [NeZero a] : Prime (l : (Wq l a)⟦X⟧) := by
  have h : Prime (l : Wq l a) := (WittVector.irreducible l).prime
  have := prime_C h
  simpa using this

end GlobalTheory.BSP.HeightAprime

namespace GlobalTheory.BSP.HeightAprime

variable {l : ℕ} [hl : Fact l.Prime]

theorem not_l_dvd_det {K : FinExt l} (bk : BK K) {d : ℕ} (Y : Matrix (Fin d) (Fin d) (Ainf l))
    (A : Matrix (Fin d) (Fin d) bk.S) (hY : IsUnit (Y.map (inclW l)))
    (hφ : Y.map WittVector.frobenius = Y * A.map bk.ev) : ¬ (l : bk.S) ∣ A.det := by
  rintro ⟨t, ht⟩
  have h2 : WittVector.frobenius Y.det = Y.det * bk.ev A.det := by
    rw [RingHom.map_det, RingHom.map_det, ← det_mul]
    exact congrArg det hφ
  have h0 := congrArg WittVector.constantCoeff h2
  rw [ht, map_mul, map_mul, map_mul, map_natCast, map_natCast, CharP.cast_eq_zero, zero_mul, mul_zero] at h0
  have hc : (WittVector.frobenius Y.det).coeff 0 = Y.det.coeff 0 ^ l :=
    WittVector.coeff_frobenius_charP l _ 0
  have hz : Y.det.coeff 0 = 0 := by
    have : WittVector.constantCoeff (WittVector.frobenius Y.det) = (WittVector.frobenius Y.det).coeff 0 := rfl
    rw [this, hc] at h0
    exact pow_eq_zero_iff hl.out.ne_zero |>.1 h0
  have hu : IsUnit (inclW l Y.det) := by
    rw [RingHom.map_det]; exact (Matrix.isUnit_iff_isUnit_det _).1 hY
  have hu0 := hu.map (WittVector.constantCoeff (p := l) (R := Cb l))
  have : WittVector.constantCoeff (inclW l Y.det) = (inclW l Y.det).coeff 0 := rfl
  rw [this, inclW, WittVector.map_coeff, hz, map_zero] at hu0
  exact not_isUnit_zero hu0

end GlobalTheory.BSP.HeightAprime

theorem GlobalTheory.BSP.HeightAprime.main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (Y S' : Matrix (Fin d) (Fin d) (Ainf l)) (A : Matrix (Fin d) (Fin d) (bk.S)) (k M : ℕ), IsUnit (Y.map (inclW l)) → Y * S' = ((l : Ainf l) ^ k * τ ^ M) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → Y.map WittVector.frobenius = Y * A.map bk.ev → ∃ (b : ℕ) (A' : Matrix (Fin d) (Fin d) (bk.S)), A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) (bk.S)) := by
  intro l _ K bk τ hτ d Y S' A k M hY hYS hφ
  have h1 : Y.det * S'.det = ((l : Ainf l) ^ k * τ ^ M) ^ d := by
    rw [← det_mul, hYS, det_smul, det_one, mul_one, Fintype.card_fin]
  have h2 : WittVector.frobenius Y.det = Y.det * bk.ev A.det := by
    rw [RingHom.map_det, RingHom.map_det, ← det_mul]
    exact congrArg det hφ
  have h3 : bk.ev A.det * (Y.det * WittVector.frobenius S'.det) =
      bk.ev ((l : bk.S) ^ (k * d) * bk.E ^ (M * d)) * τ ^ (M * d) := by
    have := congrArg WittVector.frobenius h1
    rw [map_mul, h2, map_pow, map_mul, map_pow, map_pow, map_natCast, hτ.1] at this
    rw [map_mul, map_pow, map_pow, map_natCast, pow_mul, pow_mul, pow_mul]
    linear_combination this
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_mem_span_coeff_period_pow l K bk τ hτ ι TB (M * d)
  set c : bk.S := (l : bk.S) ^ (k * d) * bk.E ^ (M * d)
  have hdiv : ∀ i, A.det ∣ c * TB.c i (τ ^ (M * d)) := fun i => by
    have := congrArg (TB.c i) h3
    rw [TB.c_mul, TB.c_mul] at this
    exact ⟨_, this.symm⟩
  have hdvd : A.det ∣ c * (l : bk.S) ^ r := by
    refine Submodule.span_induction (p := fun x _ => A.det ∣ c * x) ?_ ?_ ?_ ?_ hr
    · rintro _ ⟨i, rfl⟩; exact hdiv i
    · simp
    · intro x y _ _ hx hy; rw [mul_add]; exact dvd_add hx hy
    · intro a x _ hx; rw [smul_eq_mul, mul_left_comm]; exact dvd_mul_of_dvd_right hx a
  have hdvd' : A.det ∣ (l : bk.S) ^ (k * d + r) * bk.E ^ (M * d) := by
    have e : c * (l : bk.S) ^ r = (l : bk.S) ^ (k * d + r) * bk.E ^ (M * d) := by
      simp only [c]; ring
    rwa [e] at hdvd
  obtain ⟨q, hq⟩ := GlobalTheory.BSP.HeightAprime.dvd_of_dvd_prime_pow_mul (GlobalTheory.BSP.HeightAprime.prime_l bk.a)
    (GlobalTheory.BSP.HeightAprime.not_l_dvd_det bk Y A hY hφ) _ hdvd'
  refine ⟨M * d, q • A.adjugate, ?_⟩
  rw [Matrix.mul_smul, mul_adjugate, smul_smul, mul_comm q, ← hq]
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobenius_matrix_mul_eq_E_pow_of_period : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (Y S' : Matrix (Fin d) (Fin d) (Ainf l)) (A : Matrix (Fin d) (Fin d) (bk.S)) (k M : ℕ), IsUnit (Y.map (inclW l)) → Y * S' = ((l : Ainf l) ^ k * τ ^ M) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → Y.map WittVector.frobenius = Y * A.map bk.ev → ∃ (b : ℕ) (A' : Matrix (Fin d) (Fin d) (bk.S)), A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) (bk.S)) := by
  atlas_forward_decl GlobalTheory.BSP.HeightAprime.main
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.HeightEx

theorem exists_cols_det_ne_zero {R : Type} [CommRing R] [IsDomain R] {d : ℕ} {κ : Type} (col : κ → Fin d → R)
    (h : ∀ r : Fin d → R, (∀ k, r ⬝ᵥ col k = 0) → r = 0) :
    ∃ σ : Fin d → κ, (Matrix.of fun a b => col (σ b) a).det ≠ 0 := by
  classical
  let F := FractionRing R
  let v : κ → Fin d → F := fun k a => algebraMap R F (col k a)
  have hinj : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  have hspan : Submodule.span F (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
      (fun a : Fin d => f (Pi.single a 1))
    choose r hr using hb
    have hb0 : algebraMap R F b ≠ 0 := fun h0 => nonZeroDivisors.coe_ne_zero b (hinj (h0.trans (map_zero _).symm))
    have hr0 : r = 0 := h r fun k => hinj (by
      have h1 : f (v k) = 0 := hf (Submodule.subset_span ⟨k, rfl⟩)
      rw [LinearMap.pi_apply_eq_sum_univ] at h1
      rw [map_zero, dotProduct, map_sum]
      have h2 : ∀ a, algebraMap R F (r a * col k a) =
          algebraMap R F b * (v k a • f fun j => if a = j then 1 else 0) := fun a => by
        have e : (fun j => if a = j then (1 : F) else 0) = Pi.single a 1 := by
          ext j; simp [Pi.single_apply, eq_comm]
        rw [map_mul, hr, e, Algebra.smul_def, smul_eq_mul]; ring
      rw [Finset.sum_congr rfl fun a _ => h2 a, ← Finset.mul_sum, h1, mul_zero])
    refine hf0 ((Pi.basisFun F (Fin d)).ext fun a => ?_)
    have h3 := hr a
    rw [hr0, Pi.zero_apply, map_zero, Algebra.smul_def] at h3
    rw [Pi.basisFun_apply]
    exact (mul_eq_zero.1 h3.symm).resolve_left hb0
  obtain ⟨κ', a, -, hs, hli⟩ := exists_linearIndependent' F v
  let B : Module.Basis κ' F (Fin d → F) := Module.Basis.mk hli (by rw [hs, hspan])
  let e : κ' ≃ Fin d := B.indexEquiv (Pi.basisFun F (Fin d))
  refine ⟨a ∘ e.symm, fun h0 => ?_⟩
  have hu : IsUnit ((Matrix.of fun x y => col (a (e.symm y)) x).map (algebraMap R F)) :=
    Matrix.linearIndependent_cols_iff_isUnit.1 (hli.comp e.symm e.symm.injective)
  have h4 := (Matrix.isUnit_iff_isUnit_det _).1 hu
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h4
  exact h4.ne_zero ((congrArg (algebraMap R F) h0).trans (map_zero _))

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem inclW_injective : Function.Injective (inclW l) :=
  WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))

theorem injective_of_topBasis {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S} {ι : Type}
    (TB : TopBasis s I ι) : Function.Injective s := fun a b h => by
  have e : ∀ a, TB.c TB.i₀ (s a * TB.b TB.i₀) = a := fun a => by rw [TB.c_mul, TB.c_self, mul_one]
  rw [← e a, h, e]

theorem evW_mem (s : bk.S) : bk.evW s ∈ bk.OE := fun _ => ⟨0, s, 0, by simp⟩

theorem exists_cols (hinj : Function.Injective bk.iA) {d : ℕ} {ι : Type}
    (v : ι → Matrix (Fin d) (Fin d) (Ainf l)) (β : ι → Ainf l) (c : Ainf l) (hc : c ≠ 0)
    (h : ∀ a b : Fin d, HasSum (fun i => bk.iA (v i a b * β i)) (bk.iA (c * if a = b then 1 else 0))) :
    ∃ σ : Fin d → ι × Fin d, (Matrix.of fun a b => v (σ b).1 a (σ b).2).det ≠ 0 := by
  refine exists_cols_det_ne_zero (fun (k : ι × Fin d) a => v k.1 a k.2) fun r hr => funext fun b => ?_
  have h1 := hasSum_sum (s := Finset.univ) fun a _ => (h a b).mul_left (bk.iA (r a))
  have h2 : (fun i => ∑ a, bk.iA (r a) * bk.iA (v i a b * β i)) = fun _ => 0 := funext fun i => by
    have h3 := hr (i, b)
    simp only [dotProduct] at h3
    simp only [← map_mul, ← map_sum, ← mul_assoc, ← Finset.sum_mul, h3, zero_mul, map_zero]
  rw [h2] at h1
  have h4 := h1.unique hasSum_zero
  simp only [← map_mul, ← map_sum] at h4
  have h5 := hinj (h4.trans (map_zero _).symm)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h5
  exact (mul_eq_zero.1 h5).resolve_right hc

theorem mem_lattice (hev : Function.Injective bk.ev) {d : ℕ} (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (m : ℕ)
    (P Y' : Matrix (Fin d) (Fin d) (WCb l)) (hY' : (l : WCb l) ^ m • Y' = Y1.map (inclW l) * P)
    (hP : ∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → ∀ n : ℕ, (∀ i, (l : WCb l) ^ n ∣ (Y1.map (inclW l) *ᵥ v) i) →
      ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (l : WCb l) ^ m • v = (l : WCb l) ^ n • (P *ᵥ w))
    (y : Fin d → Ainf l) (δ : bk.S) (c : Fin d → bk.S) (hδ : δ ≠ 0)
    (h : (fun a => bk.ev δ * y a) = Y1 *ᵥ fun a => bk.ev (c a)) :
    ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun a => inclW l (y a)) = Y' *ᵥ w := by
  have h0 : bk.evW δ ≠ 0 := fun h0 =>
    hδ (hev (inclW_injective (h0.trans (by rw [map_zero, map_zero]))))
  obtain ⟨n, u, u', -, hu', huu, he⟩ := (GlobalTheory.T.integral_elements_unit_factorization l K bk).2.2.2.1 _ (evW_mem bk δ) h0
  have hl0 : (l : WCb l) ≠ 0 := WittVector.p_nonzero l (Cb l)
  have h1 : Y1.map (inclW l) *ᵥ (u' • fun a => bk.evW (c a)) = (l : WCb l) ^ n • fun a => inclW l (y a) := by
    rw [Matrix.mulVec_smul]
    funext a
    have h2 := congrArg (inclW l) (congrFun h a)
    rw [RingHom.map_mulVec, map_mul] at h2
    change bk.evW δ * _ = (Y1.map (inclW l) *ᵥ fun a => bk.evW (c a)) a at h2
    rw [Pi.smul_apply, ← h2, he, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    linear_combination ((l : WCb l) ^ n * inclW l (y a)) * huu
  obtain ⟨w, hw, hw2⟩ := hP (u' • fun a => bk.evW (c a)) (fun i => bk.OE.mul_mem hu' (evW_mem bk _)) n
    (fun i => by rw [h1]; exact ⟨_, rfl⟩)
  refine ⟨w, hw, ?_⟩
  have h3 := congrArg (Y1.map (inclW l)).mulVec hw2
  rw [Matrix.mulVec_smul, h1, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← hY', Matrix.smul_mulVec, smul_comm] at h3
  exact smul_right_injective _ (pow_ne_zero m hl0) (smul_right_injective _ (pow_ne_zero n hl0) h3)

theorem nonempty_height : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ s : Seed bk d ρ τ, Nonempty (Height s) := by
  intro l _ K bk τ hτ d ρ hρ s
  obtain ⟨-, -, ⟨hρ0, hρ1, -⟩, -⟩ := GlobalTheory.BSP.flat_disc l K bk
  obtain ⟨ι, TB, k, v, Zf, -, hvZ, hsum⟩ := GlobalTheory.T.exists_bounded_periods_disc_ainf l K bk τ hτ d ρ hρ s
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk _ bk.ev ι TB _ hρ0 hρ1).1
  have hev := injective_of_topBasis TB
  have hτ0 : τ ≠ 0 := (GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ).2.2.1
  have hl0 : (l : Ainf l) ≠ 0 := WittVector.p_nonzero l (OCb l)
  obtain ⟨j₀, hj₀⟩ : ∃ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j :=
    GlobalTheory.BSP.exists_discMap_of_pow_dvd l _ _ bk.ev X (bk.ev X) _ _ 1 hρ0 (by rw [pow_one]) (by rw [pow_one])
  obtain ⟨σ, hσ⟩ := exists_cols bk hinj v TB.b _ (mul_ne_zero (pow_ne_zero k hl0) (pow_ne_zero _ hτ0)) hsum
  set Y1 : Matrix (Fin d) (Fin d) (Ainf l) := Matrix.of fun a b => v (σ b).1 a (σ b).2 with hY1
  let Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀) := Matrix.of fun a b => Zf (σ b).1 a (σ b).2
  have hZ1 : ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W * Z1.map j = Y1.map bk.iA :=
    fun j hj => Matrix.ext fun a b => congrFun (congrFun (hvZ j hj (σ b).1) a) (σ b).2
  clear_value Y1 Z1
  have hdet : (Y1.map (inclW l)).det ≠ 0 := fun h0 => hσ (inclW_injective (by
    rw [RingHom.map_det, map_zero]; exact h0))
  obtain ⟨δ, A1, hδ, hA1⟩ := GlobalTheory.T.crystallineLattice_frobenius_rational_columns l K bk τ hτ d ρ hρ s Y1 Z1 hσ hZ1
  have hgal : ∀ g : ↥(GK K), bk.FixFlat g → τ ^ s.N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) *
      Y1.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ s.N • Y1 := fun g hg => by
    obtain ⟨G, hG⟩ := (GlobalTheory.BSP.galois_discMap l K bk).2 _ hρ0 (g : GQ l)
    obtain ⟨hfix, hW⟩ := GlobalTheory.T.crystallineDiscPeriods_galois_action_eq l K bk τ hτ d ρ hρ s g hg G hG
    have e1 : (Z1.map j₀).map G = Z1.map j₀ := Matrix.ext fun a b => hfix j₀ hj₀ _
    have e2 : s.W.map G * Z1.map j₀ = (Y1.map (Per.σA (g : GQ l))).map bk.iA := by
      rw [← e1, ← Matrix.map_mul, hZ1 j₀ hj₀]
      exact Matrix.ext fun a b => hG.ext _
    have e3 := congrArg (· * Z1.map j₀) hW
    simp only [Matrix.smul_mul, Matrix.mul_assoc] at e3
    rw [e2, hZ1 j₀ hj₀, hG.ext] at e3
    refine Matrix.ext fun a b => hinj ?_
    have e4 := congrFun (congrFun e3 a) b
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow, map_sum,
      RingHom.comp_apply] at e4 ⊢
    exact e4
  obtain ⟨m, P, Y', hP, hPd, hY', hlat, hsat⟩ := GlobalTheory.T.exists_integralWittLattice_basis l K bk d _ hdet
  have hY'u := GlobalTheory.T.isUnit_saturated_basis_etale_lattice l K bk τ hτ d s.N ρ hρ Y1 δ A1 hdet hδ hA1 hgal m P Y' hP hPd hY' hlat hsat
  obtain ⟨Y, hYu, hY⟩ := GlobalTheory.T.ainf_closed_membership_limit l K bk d (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀,
      ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a))
    ⟨0, fun j _ => by simp only [Pi.zero_apply, map_zero]; exact Matrix.mulVec_zero _⟩
    (fun y z ⟨x, hx⟩ ⟨x', hx'⟩ => ⟨x + x', fun j hj => by
      simp only [Pi.add_apply, map_add]
      exact (Matrix.mulVec_add s.W (fun a => j (x a)) fun a => j (x' a)).trans (by rw [hx j hj, hx' j hj]; rfl)⟩)
    (fun c y ⟨x, hx⟩ => ⟨fun a => toDisc l X bk.ρ₀ c * x a, fun j hj => by
      simp only [map_mul, hj.ext]
      exact (Matrix.mulVec_smul s.W (bk.iA (bk.ev c)) fun a => j (x a)).trans (by rw [hx j hj]; rfl)⟩)
    (fun y ⟨x, hx⟩ => by
      obtain ⟨t, ht⟩ := (isUnit_l_disc l (X : bk.S) bk.ρ₀).exists_left_inv
      refine ⟨fun a => t * x a, fun j hj => ?_⟩
      have ht' := congrArg j ht
      rw [map_mul, map_natCast, map_one] at ht'
      simp only [map_mul]
      refine (Matrix.mulVec_smul s.W (j t) fun a => j (x a)).trans ?_
      rw [hx j hj]
      funext a
      rw [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, ← mul_assoc, ht', one_mul])
    (GlobalTheory.T.crystalline_disc_period_module_isClosed_lAdic l K bk τ hτ d ρ hρ s) Y1 Y' hdet hY'u
    (fun c => ⟨Z1 *ᵥ fun a => toDisc l X bk.ρ₀ (c a), fun j hj => by
      simp only [RingHom.map_mulVec]
      have e : (j ∘ fun a => toDisc l X bk.ρ₀ (c a)) = bk.iA ∘ fun a => bk.ev (c a) := funext fun a => hj.ext _
      rw [e, ← hZ1 j hj, ← Matrix.mulVec_mulVec]⟩)
    (fun y hy => by
      obtain ⟨δ, c, hδ, h⟩ := GlobalTheory.T.crystallineLattice_rational_in_columns l K bk τ hτ d ρ hρ s Y1 Z1 hdet hZ1 y hy
      exact mem_lattice bk hev Y1 m P Y' hY' hlat y δ c hδ h)
  obtain ⟨k', S', hS'⟩ := GlobalTheory.T.basis_dvd_tauPow_lPow_ainf l K bk τ hτ d ρ hρ s Y hYu hY
  have hcol : ∀ b : Fin d, ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j →
      s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (Y a b) := fun b =>
    (hY fun a => Y a b).2 ⟨Pi.single b 1, by
      funext a
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, apply_ite]⟩
  have hφ := fun b => (hY _).1 (GlobalTheory.T.crystallineLattice_discSpan_frobenius_stable l K bk τ hτ d ρ hρ s _ (hcol b))
  choose x hx using hcol
  choose c hc using hφ
  have hZ : ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j →
      s.W * (Matrix.of fun a b => x b a).map j = Y.map bk.iA :=
    fun j hj => Matrix.ext fun a b => congrFun (hx b j hj) a
  have hA : Y.map WittVector.frobenius = Y * (Matrix.of fun a b => c b a).map bk.ev :=
    Matrix.ext fun a b => congrFun (hc b) a
  obtain ⟨b, A', hA'⟩ := GlobalTheory.T.exists_frobenius_matrix_mul_eq_E_pow_of_period l K bk τ hτ d Y S' _ k' _ hYu hS' hA
  exact ⟨⟨Y, hYu, _, GlobalTheory.T.isUnit_discBasis_crystallineLattice l K bk τ hτ d ρ hρ s Y _ k' S' hS' hZ, hZ, 0, b, _, A', hA', by
    rw [pow_zero, one_smul]; exact hA⟩⟩

end GlobalTheory.BSP.HeightEx
end
