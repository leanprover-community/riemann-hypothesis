import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjCongr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedPeriodAinfUnit
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRingEmbeddingProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LtSeriesCoeffEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiedTensorInj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffEqZeroOfStable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEigenFilOneIsUnitExactDegree

section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.BKReal Formalism.BasicNotions.Examples₂.LB
open scoped Formalism.Per

namespace GlobalTheory.ConjNorm

theorem det_dvd_det {D : Type*} [CommRing D] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (V : Matrix m n D) (W : Matrix n m D) (M : Matrix n n D) (Y : Matrix m m D) (h1 : V * W = 1)
    (h2 : V * M = Y * V) : Y.det ∣ M.det := by
  have e : M = (1 + W * ((Y - 1) * V)) * ((1 - W * V) * M + W * V) := by
    have h3 : ∀ X : Matrix m n D, V * (W * X) = X := fun X => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc,
      h3, h2]
    abel
  rw [e, Matrix.det_mul, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, h1, Matrix.mul_one, add_sub_cancel]
  exact dvd_mul_right _ _

section Norm

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]

theorem norm_map {A' S' ι : Type*} [CommRing A'] [CommRing S'] [Algebra A' S'] [Fintype ι]
    (b : Module.Basis ι A S) (b' : Module.Basis ι A' S') (f : A →+* A') (F : S →+* S')
    (hf : ∀ a, F (algebraMap A S a) = algebraMap A' S' (f a)) (hb : ∀ i, F (b i) = b' i) (x : S) :
    Algebra.norm A' (F x) = f (Algebra.norm A x) := by
  classical
  have hr : ∀ y i, b'.repr (F y) i = f (b.repr y i) := fun y i => by
    conv_lhs => rw [← b.sum_repr y]
    simp only [map_sum, Algebra.smul_def, map_mul, hf, hb]
    simp [← Algebra.smul_def, Finsupp.single_apply]
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b', RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, ← hb, ← map_mul, hr]

theorem prod_dvd_norm [Module.Free A S] [Module.Finite A S] {D m : Type*} [CommRing D] [Fintype m] [DecidableEq m]
    (φ : m → S →+* D) (ψ : A →+* D) (h : ∀ i a, φ i (algebraMap A S a) = ψ a) (c : m → S)
    (hc : IsUnit (Matrix.of fun i k => φ i (c k)).det) (x : S) : ∏ i, φ i x ∣ ψ (Algebra.norm A x) := by
  classical
  let b := Module.Free.chooseBasis A S
  have hr : ∀ i y, ∑ k, φ i (b k) * ψ (b.repr y k) = φ i y := fun i y => by
    conv_rhs => rw [← b.sum_repr y]
    simp only [map_sum, Algebra.smul_def, map_mul, h, mul_comm]
  rw [Algebra.norm_eq_matrix_det b, RingHom.map_det, ← Matrix.det_diagonal]
  refine det_dvd_det (Matrix.of fun i k => φ i (b k))
    ((Matrix.of fun k j => ψ (b.repr (c j) k)) * (Matrix.of fun i k => φ i (c k))⁻¹) _ _ ?_ ?_
  · rw [← Matrix.mul_assoc, ← Matrix.mul_nonsing_inv _ hc]
    congr 1
    ext i j
    exact hr i (c j)
  · ext i k
    rw [Matrix.diagonal_mul, Matrix.mul_apply, Matrix.of_apply, ← map_mul, ← hr]
    simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]

theorem dvd_norm [Module.Free A S] [Module.Finite A S] (x : S) : x ∣ algebraMap A S (Algebra.norm A x) := by
  simpa using prod_dvd_norm (fun _ : Unit => RingHom.id S) (algebraMap A S) (fun _ _ => rfl) (fun _ => 1)
    (by simp) x

theorem mul_dvd_norm [Module.Free A S] [Module.Finite A S] {D : Type*} [CommRing D] (φ₁ φ₂ : S →+* D)
    (h : ∀ a, φ₂ (algebraMap A S a) = φ₁ (algebraMap A S a)) (c : S) (hc : IsUnit (φ₂ c - φ₁ c)) (x : S) :
    φ₁ x * φ₂ x ∣ φ₁ (algebraMap A S (Algebra.norm A x)) := by
  simpa using prod_dvd_norm ![φ₁, φ₂] (φ₁.comp (algebraMap A S)) (fun i a => by fin_cases i <;> simp [h])
    ![1, c] (by simpa [Matrix.det_fin_two] using hc) x

end Norm

variable {l : ℕ} [hl : Fact l.Prime] (K : FinExt l)

theorem norm_unif {π : ↥(OL K)} (hπ : Irreducible π) :
    ∃ u : W0 K, IsUnit u ∧ Algebra.norm (W0 K) π = (l : W0 K) * u := by
  haveI : FaithfulSMul (W0 K) ↥(OL K) := (faithfulSMul_iff_algebraMap_injective _ _).2 (thetaW_injective K)
  haveI : CharZero (W0 K) := (algebraMap (W0 K) ↥(OL K)).charZero
  let P := IsLocalRing.maximalIdeal ↥(OL K)
  let p := IsLocalRing.maximalIdeal (W0 K)
  haveI hlo : P.LiesOver p := by
    constructor
    have : (P.under (W0 K)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
    exact (IsLocalRing.eq_maximalIdeal this).symm
  have hrel := Ideal.relNorm_eq_pow_of_isMaximal P p
  have hf : P.inertiaDeg (W0 K) = 1 := by
    rw [Ideal.inertiaDeg_eq_of_isMaximal p P]
    letI := Ideal.Quotient.field p
    letI := Ideal.Quotient.field P
    refine Algebra.finrank_eq_one_iff_bijective_algebraMap.2 ⟨RingHom.injective _, fun y => ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨w, hw⟩ := exists_thetaW (card_res K) x
    exact ⟨Ideal.Quotient.mk _ w, hw⟩
  have hP : P = Ideal.span {π} := hπ.maximalIdeal_eq
  have hp : p = Ideal.span {(l : W0 K)} := (WittVector.irreducible l).maximalIdeal_eq
  rw [hf, pow_one, hP, Ideal.relNorm_singleton, hp, Algebra.intNorm_eq_norm] at hrel
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hrel.symm
  exact ⟨u, u.isUnit, hu.symm⟩

theorem exists_lang (u : W0 K) (hu : IsUnit u) :
    ∃ a : Per.Ainf l, IsUnit a ∧ Per.φA l a = wA l (fK K) u * a := by
  obtain ⟨f⟩ := GlobalTheory.Per.nonempty_algClosure_zmod_to_tilt l
  have hr : ∀ x : Fq l (fK K), ∃ y, f y = Fq.val l (fK K) x := fun x => by
    have h1 := one_lt_pow_l l (fK K)
    have hm : (Polynomial.X ^ l ^ fK K - Polynomial.X : Polynomial (AlgebraicClosure (ZMod l))).Monic :=
      Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast h1)
    have h2 := congrArg (Polynomial.eval₂ f (Fq.val l (fK K) x))
      ((IsAlgClosed.splits _).eq_prod_roots_of_monic hm)
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, ← map_pow, Fq.pow_card, sub_self,
      Polynomial.eval₂_multiset_prod, eq_comm, Multiset.prod_eq_zero_iff, Multiset.map_map] at h2
    obtain ⟨y, -, hy⟩ := Multiset.mem_map.1 h2
    refine ⟨y, ?_⟩
    simp only [Function.comp, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at hy
    exact (sub_eq_zero.1 hy).symm
  choose r hr using hr
  let u' : WittVector l (AlgebraicClosure (ZMod l)) := WittVector.mk l fun n => r (u.coeff n)
  have hfu : WittVector.map f u' = wA l (fK K) u := WittVector.ext fun n => hr (u.coeff n)
  have hu' : IsUnit u' := WittVector.isUnit_of_coeff_zero_ne_zero _ fun h => by
    have h0 : u.coeff 0 ≠ 0 := (hu.map (WittVector.constantCoeff (p := l) (R := Fq l (fK K)))).ne_zero
    have h1 := hr (u.coeff 0)
    rw [show r (u.coeff 0) = 0 from h, map_zero, eq_comm, map_eq_zero] at h1
    exact h0 h1
  obtain ⟨w, hw, hφ⟩ := GlobalTheory.MemLoc.exists_unit_frobenius_eq_mul l _ u' hu'
  refine ⟨WittVector.map f w, hw.map _, ?_⟩
  rw [← hfu, ← map_mul, ← hφ]
  refine WittVector.ext fun n => ?_
  have h := GlobalTheory.AinfK.coeff_iter 1 (WittVector.map f w) n
  rw [Function.iterate_one, pow_one] at h
  rw [h, WittVector.map_coeff, WittVector.map_coeff, WittVector.coeff_frobenius_charP, map_pow]

end GlobalTheory.ConjNorm

end
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.BKReal GlobalTheory.ConjPeriod
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.ConjPeriod

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

abbrev plusR (l : ℕ) [Fact l.Prime] : Subring (Per.BdR l) := (algebraMap (Per.BdRp l) (Per.BdR l)).range

theorem eD_uj_mem (T : LocTied l P AI) (j : ℕ) (a : Per.Acris l) : T.eD (uj T j a) ∈ plusR l := by
  obtain ⟨i, hi, -⟩ := GlobalTheory.CrisIncl.exists_restrict l _ T.incl
  exact ⟨_, (hi ((GlobalTheory.MemLoc.phiA l ^ j) a)).symm⟩

theorem eD_om_mem (T : LocTied l P AI) (x : Om l) : T.eD (algebraMap (Om l) P.R.BdR x) ∈ plusR l := by
  obtain ⟨y, hy, -⟩ := T.om x
  exact ⟨y, hy.symm⟩

theorem l_inv_mem (l : ℕ) [Fact l.Prime] : ∃ u ∈ plusR l, (l : Per.BdR l) * u = 1 := by
  obtain ⟨v, hv⟩ := (GlobalTheory.RingBasics.isUnit_l l).exists_right_inv
  refine ⟨algebraMap (Per.BdRp l) (Per.BdR l) (algebraMap (Per.AinfP l) (Per.BdRp l) v), ⟨_, rfl⟩, ?_⟩
  have h := congrArg ((algebraMap (Per.BdRp l) (Per.BdR l)).comp (algebraMap (Per.AinfP l) (Per.BdRp l))) hv
  rwa [map_mul, map_natCast, map_one] at h

theorem conj_mem_Fil_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K : FinExt l) (j : ℕ) (s : ↥K.1 →ₐ[ℚ_[l]] Om l) (h : Compat T K j s) (b : BK K),
    conj T K j s h b ∈ (P.PD K).Fil 0 := by
  intro l _ P AI T K j s h b
  let f : BK K →+* Per.BdR l := T.eD.toRingHom.comp (conj T K j s h)
  have hz : ∀ z : CK K, f (toB K z) ∈ plusR l := fun z => by
    induction z using GlobalTheory.AcrisK.induction_on with
    | mul a c =>
      rw [map_mul, map_mul]
      refine mul_mem ?_ ?_
      · exact eD_uj_mem T j a |> fun h' => by
          simpa only [f, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, conj_inC] using h'
      · rw [← inK_oK]
        simpa only [f, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, conj_inK] using
          eD_om_mem T (s (oK K c))
    | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
  obtain ⟨D, z, hD⟩ := exists_pow_mul b
  obtain ⟨u, hu, hlu⟩ := l_inv_mem l
  have e : f b = u ^ D * f (toB K z) := by
    rw [← hD, map_mul, map_pow, map_natCast, ← mul_assoc, ← mul_pow, mul_comm u, hlu, one_pow, one_mul]
  have hm : f b ∈ plusR l := e ▸ mul_mem (pow_mem hu D) (hz z)
  obtain ⟨y, hy⟩ := hm
  rw [T.fil]
  change f b ∈ Per.FilD l 0
  rw [← hy]
  exact GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD_zero y

end GlobalTheory.ConjPeriod

end
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC

namespace GlobalTheory

theorem prod_mem_Fil_zero_of_factors {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) {ι : Type}
    (s : Finset ι) (x : ι → P.R.BdR) (h : ∀ i ∈ s, x i ∈ (P.PD K).Fil 0) :
    (∏ i ∈ s, x i) ∈ (P.PD K).Fil 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (P.PD K).one_mem
  | insert a t ha ih =>
    rw [Finset.prod_insert ha]
    have h1 := (P.PD K).Fil_mul 0 0 _ _ (h a (Finset.mem_insert_self a t))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa using h1

theorem prod_degree_of_not_mem_Fil_two : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) {ι : Type} (s : Finset ι) (x : ι → P.R.BdR) (i₀ : ι), i₀ ∈ s →
    (∀ i ∈ s, x i ∈ (P.PD K).Fil 0) → x i₀ ∈ (P.PD K).Fil 1 → (∏ i ∈ s, x i) ∉ (P.PD K).Fil 2 →
    x i₀ ∉ (P.PD K).Fil 2 ∧ ∀ i ∈ s, i ≠ i₀ → x i ∉ (P.PD K).Fil 1 := by
  classical
  intro l _ P K ι s x i₀ hi₀ h0 h1 hprod
  have hrest : (∏ i ∈ s.erase i₀, x i) ∈ (P.PD K).Fil 0 :=
    prod_mem_Fil_zero_of_factors P K _ x fun i hi => h0 i (Finset.mem_of_mem_erase hi)
  refine ⟨fun h2 => hprod ?_, fun i hi hne h1i => hprod ?_⟩
  · rw [← Finset.mul_prod_erase s x hi₀]
    simpa using (P.PD K).Fil_mul 2 0 _ _ h2 hrest
  · have hi' : i ∈ s.erase i₀ := Finset.mem_erase.mpr ⟨hne, hi⟩
    have hrest2 : (∏ j ∈ (s.erase i₀).erase i, x j) ∈ (P.PD K).Fil 0 :=
      prod_mem_Fil_zero_of_factors P K _ x fun j hj =>
        h0 j (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hj))
    have hA : x i * (∏ j ∈ (s.erase i₀).erase i, x j) ∈ (P.PD K).Fil 1 := by
      simpa using (P.PD K).Fil_mul 1 0 _ _ h1i hrest2
    rw [← Finset.mul_prod_erase s x hi₀, ← Finset.mul_prod_erase (s.erase i₀) x hi']
    simpa [one_add_one_eq_two] using (P.PD K).Fil_mul 1 1 _ _ h1 hA

end GlobalTheory
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.BKReal GlobalTheory.ConjPeriod
open GlobalTheory.MemLoc GlobalTheory.ConjNorm Formalism.BasicNotions.Examples₂.LB GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.ConjDegree

variable {l : ℕ} [hl : Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem exists_period (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l) (hD : LTData K χ π z) :
    ∃ (ω : AK K) (t u : BK K), thetaK K ω = 0 ∧ t = toB K (ofA K ω) * u ∧ t ≠ 0 ∧
      frobB K t = inK K (π : ↥K.1) * t ∧ ∀ g : ↥(GK K), galB g t = inK K (χ g : ↥K.1) * t := by
  haveI := Formalism.BasicNotions.Examples₂.LB.OL_resFinite K
  have hπ : Irreducible π := hD.1
  obtain ⟨hf, hE⟩ := GlobalTheory.T.lubin_tate_endomorphism_unique l K π hπ
  obtain ⟨ω, hω0, hθ, hφ, hg⟩ := GlobalTheory.T.lubin_tate_period_galois_expansion l K χ π z hD
  have hθ' : ω ∈ RingHom.ker (thetaK K) := hθ
  obtain ⟨L', u, -, -, -, ht⟩ := GlobalTheory.AcrisK.ev_shift l K _ (onDisc_log hπ hf) ω hθ _ (ev_ltLog hπ hf ω hθ)
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, GlobalTheory.LTLog.constantCoeff_log _ hπ hf, map_zero, zero_add] at ht
  refine ⟨ω, ltLog hπ hf ω hθ, u, hθ, ht,
    GlobalTheory.T.lubin_tate_log_ne_zero l K π hπ _ hf ω hθ (GlobalTheory.T.lubin_tate_period_theta_kernel l K χ π z hD ω hω0 hθ hφ hg), ?_, fun g => ?_⟩
  · refine ev_log_self hπ hf hθ (y := frobq K ω) (fun n => ?_) (Ev.frob (ev_ltLog hπ hf ω hθ))
    rw [hφ, GlobalTheory.LTPer.ltSeries_eval]
    exact GlobalTheory.LTPer.sum_sub_sum_mem _ hθ' _ _ (fun j hj => GlobalTheory.LTPer.ltSeries_coeff_eq_zero K π j hj) n
  · obtain ⟨a, ha, φ, hφE, -⟩ := hD.2.2.2.2 g
    have hy := hg g a φ ha hφE
    rw [(hE a φ).1 hφE] at hy
    rw [ev_log_hom hπ hf a hθ hy (Ev.gal g (ev_ltLog hπ hf ω hθ)), ← ha]
    rfl

variable (T : LocTied l P AI) (K : FinExt l)

def jB : Per.Acris l →+* P.R.B := T.eB.symm.toRingHom.comp (algebraMap (Per.Acris l) (Per.Bcris l))

theorem uj_eq (j : ℕ) (a : Per.Acris l) : uj T j a = P.ιB (jB T ((phiA l ^ j) a)) := rfl

theorem uj_add (i j : ℕ) (a : Per.Acris l) : uj T (i + j) a = uj T i ((phiA l ^ j) a) := by
  rw [uj_eq, uj_eq, pow_add]
  rfl

theorem jB_injective : Function.Injective (jB T) := by
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  exact T.eB.symm.injective.comp (GlobalTheory.MemLoc.AwayT.acris_injective C)

theorem phi_jB (a : Per.Acris l) : (P.PD K).φ (jB T a) = jB T (phiA l a) := by
  have := GlobalTheory.PZ.ColmezVec.pow_phi_acris T K 1 a
  rwa [pow_one] at this

private theorem aB_eq_alg_aC (a : Per.Ainf l) :
    Per.aB l a = algebraMap (Per.Acris l) (Per.Bcris l) (aC l a) := by
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  apply GlobalTheory.MemLoc.ULaws.iota_injective C
  rw [GlobalTheory.MemLoc.ULaws.iota_aB, C.ι_j]
  exact congrArg _ (GlobalTheory.MemLoc.TFil.j_alg C.j_cris a).symm

theorem compat_zero : Compat T K 0 K.1.val := fun w =>
  (GlobalTheory.WittCompat.exists_unramified_witt_element l P AI T K w).elim fun c hc =>
    ((P.PD_ι K _).symm.trans ((congrArg (P.PD K).ι
      (hc.2.trans (congrArg T.eB.symm (aB_eq_alg_aC _)))).symm.trans ((P.PD K).ι.commutes c))).trans
      ((IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 P.R.BdR c).trans (congrArg _ hc.1))

theorem conj_zero_mem (x : AK K) (hx : thetaK K x = 0) :
    conj T K 0 K.1.val (compat_zero T K) (toB K (ofA K x)) ∈ (P.PD K).Fil 1 := by
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  have hD : ∀ a, T.eD (uj T 0 a) = algebraMap (Per.BdRp l) (Per.BdR l) (C.j a) := fun a => by
    rw [uj_eq, hC.ι, ← C.ι_j]
    exact congrArg C.ι (T.eB.apply_symm_apply _)
  have hA : ∀ x : AK K, T.eD (conj T K 0 K.1.val (compat_zero T K) (toB K (ofA K x))) =
      algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.CrisToDR.psiA C K x) := fun x =>
    GlobalTheory.AinfK.induction_on x (fun a c => by
      simp only [map_mul]
      rw [ofA_inA, ofA_inO, ← inK_oK, conj_inK, conj_inC, hD, GlobalTheory.CrisToDR.psiA_inA, GlobalTheory.CrisToDR.psiA_inO]
      congr 1
      · exact congrArg _ (GlobalTheory.MemLoc.TFil.j_alg C.j_cris a)
      · exact hC.o _)
      fun x y hx hy => by simp only [map_add, hx, hy]
  rw [T.fil, hA]
  refine GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD 1 (((thetaD_props l).2.1 _).1 ?_)
  rw [GlobalTheory.CrisToDR.thetaD_psiA, hx]
  rfl

include T in

theorem isDomain_CK : IsDomain (CK K) := by
  haveI : IsDomain P.R.BdR := (GlobalTheory.RegularRing.isField_of_tied T).isDomain
  refine Function.Injective.isDomain ((conj T K 0 K.1.val (compat_zero T K)).comp (toB K))
    ((injective_iff_map_eq_zero _).2 fun z hz => ?_)
  let b := Module.finBasis (W0 K) ↥(OL K)
  have hb := GlobalTheory.UnramDisjoint.linearIndependent_Kur l K _ _
    (GlobalTheory.CrisInj.li_of_frac (W := W0 K) (F := ↥(K0 K)) (oK K) (IsFractionRing.injective ↥(OL K) ↥K.1)
      (thetaW_injective K) (GlobalTheory.CrisInj.exists_frac K) _ b.linearIndependent)
  obtain ⟨a, ha⟩ := GlobalTheory.CrisInj.exists_coord (A := Per.Acris l) b z
  have ha' : z = ∑ i, inC K (a i) * inI K (b i) :=
    ha.trans (Finset.sum_congr (M := CK K) rfl fun i _ => GlobalTheory.AcrisK.tmul_eq K _ _)
  have h0 := GlobalTheory.LocTensor.tied_tensor_inj l P AI T _ _ hb (fun i => jB T (a i)) (by
    rw [← hz, ha', map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RingHom.comp_apply, map_mul, map_mul, ← inK_oK, conj_inC, conj_inK, mul_comm]
    rfl)
  rw [ha']
  exact Finset.sum_eq_zero fun i _ => by
    rw [jB_injective T ((h0 i).trans (map_zero _).symm), map_zero, zero_mul]

include T in
theorem om_mem (x : Om l) : algebraMap (Om l) P.R.BdR x ∈ (P.PD K).Fil 0 := by
  obtain ⟨y, hy, -⟩ := T.om x
  rw [T.fil, hy]
  exact GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD_zero y

theorem uj_mem (j : ℕ) (a : Per.Acris l) : uj T j a ∈ (P.PD K).Fil 0 := by
  obtain ⟨y, hy⟩ := eD_uj_mem T j a
  rw [T.fil, ← hy]
  exact GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD_zero y

theorem mul_mem_left {a : ℤ} {x y : P.R.BdR} (hx : x ∈ (P.PD K).Fil 0) (hy : y ∈ (P.PD K).Fil a) :
    x * y ∈ (P.PD K).Fil a := by
  simpa using (P.PD K).Fil_mul 0 a _ _ hx hy

include T in

theorem not_mem_two (x : P.R.B) (hx : (P.PD K).φ x = (l : P.R.B) * x) (h0 : x ≠ 0)
    (h1 : P.ιB x ∈ (P.PD K).Fil 1) : P.ιB x ∉ (P.PD K).Fil 2 := by
  haveI : IsDomain P.R.BdR := (GlobalTheory.RegularRing.isField_of_tied T).isDomain
  have hι : ∀ b, (P.PD K).ι.toRingHom b = P.ιB b := P.PD_ι K
  have hlu : IsUnit (l : P.R.B) := by
    simpa using ((Nat.cast_ne_zero.2 hl.out.ne_zero : (l : ℚ_[l]) ≠ 0).isUnit).map (algebraMap ℚ_[l] P.R.B)
  have h := GlobalTheory.MemLoc.EigenDegree.abstract (P.PD K).ι.toRingHom (P.PD K).ι_inj (P.PD K).φ.toRingHom
    (fun a y => y ∈ (P.PD K).Fil a) (P.PD K).one_mem (P.PD K).Fil_mul (l : P.R.B) (P.PD K).t hlu (P.PD K).t_unit
    (by
      have := (P.PD K).t_φ
      rwa [P.PD_p, Algebra.smul_def, map_natCast] at this) (P.PD K).not_mem_filtration_two
    (fun y hy => by
      obtain ⟨z, hz, e⟩ := ((GlobalTheory.MemLoc.TiedUnif.tied_uniformiser l P AI T).2.2 K 0 y).1 (by rwa [zero_add])
      exact ⟨z, hz, by rw [hι, P.period_datum_t_eq]; exact e⟩)
    (fun b hb hb0 hne => by
      obtain ⟨c, rfl⟩ := (P.PD K).fund b hb hb0
      have hc : c ≠ 0 := by
        rintro rfl
        exact hne (map_zero _)
      refine ⟨algebraMap ℚ_[l] P.R.B c⁻¹, by rw [← map_mul, inv_mul_cancel₀ hc, map_one], ?_⟩
      rw [hι, AlgHom.commutes, IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR]
      exact om_mem T K _) 1 one_pos x hx h0 (by rwa [hι]) (fun j hj => by
      obtain rfl : j = 0 := by omega
      rw [hι]
      exact (P.PD K).Fil_anti 0 h1)
  rw [← hι]
  exact h.2.1

def filZero : Subring P.R.BdR where
  carrier := (P.PD K).Fil 0
  mul_mem' := mul_mem_left K
  one_mem' := (P.PD K).one_mem
  add_mem' := add_mem
  zero_mem' := zero_mem _
  neg_mem' := neg_mem

theorem norm_mem_two {j : ℕ} {s s' : ↥K.1 →ₐ[ℚ_[l]] Om l} (h : Compat T K j s) (h' : Compat T K j s') (hs : s' ≠ s)
    (z : CK K) (h1 : conj T K j s h (toB K z) ∈ (P.PD K).Fil 1) (h2 : conj T K j s' h' (toB K z) ∈ (P.PD K).Fil 1) :
    uj T j (Algebra.norm (Per.Acris l) z) ∈ (P.PD K).Fil 2 := by
  obtain ⟨c, hc⟩ : ∃ c : ↥(OL K), s' (oK K c) - s (oK K c) ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hs (AlgHom.coe_ringHom_injective (ringHom_extK fun c => sub_eq_zero.1 (hn c)))
  obtain ⟨y, hy⟩ := mul_dvd_norm (A := Per.Acris l)
    (((conj T K j s h).comp (toB K)).codRestrict (filZero K) fun x => conj_mem_Fil_zero l P AI T K j s h _)
    (((conj T K j s' h').comp (toB K)).codRestrict (filZero K) fun x => conj_mem_Fil_zero l P AI T K j s' h' _)
    (fun a => Subtype.ext ((conj_inC T K j s' h' a).trans (conj_inC T K j s h a).symm)) (inI K c)
    (IsUnit.of_mul_eq_one ⟨_, om_mem T K (s' (oK K c) - s (oK K c))⁻¹⟩ (Subtype.ext (by
      change (conj T K j s' h' (toB K (inI K c)) - conj T K j s h (toB K (inI K c))) * algebraMap _ _ _ = 1
      rw [← inK_oK, conj_inK, conj_inK, ← map_sub, ← map_mul, mul_inv_cancel₀ hc, map_one]))) z
  have hy' : conj T K j s h (toB K (inC K (Algebra.norm (Per.Acris l) z))) =
      conj T K j s h (toB K z) * conj T K j s' h' (toB K z) * y.1 := congrArg Subtype.val hy
  rw [conj_inC] at hy'
  rw [hy', mul_comm]
  exact mul_mem_left K y.2 ((P.PD K).Fil_mul 1 1 _ _ h1 h2)

theorem norm_mem_one {j : ℕ} {s : ↥K.1 →ₐ[ℚ_[l]] Om l} (h : Compat T K j s) (z : CK K)
    (h1 : conj T K j s h (toB K z) ∈ (P.PD K).Fil 1) :
    uj T j (Algebra.norm (Per.Acris l) z) ∈ (P.PD K).Fil 1 := by
  obtain ⟨y, hy⟩ := dvd_norm (A := Per.Acris l) z
  rw [← conj_inC T K j s h, hy, map_mul, map_mul, mul_comm]
  exact mul_mem_left K (conj_mem_Fil_zero l P AI T K j s h _) h1

def basisC : Module.Basis (Module.Free.ChooseBasisIndex (W0 K) ↥(OL K)) (Per.Acris l) (CK K) :=
  Algebra.TensorProduct.basis (Per.Acris l) (Module.Free.chooseBasis (W0 K) ↥(OL K))

theorem basisC_apply (i) : basisC K i = inI K (Module.Free.chooseBasis (W0 K) ↥(OL K) i) :=
  Algebra.TensorProduct.basis_apply _ i

theorem norm_frobC (z : CK K) :
    Algebra.norm (Per.Acris l) (frobC K z) = (phiA l ^ fK K) (Algebra.norm (Per.Acris l) z) :=
  norm_map (basisC K) (basisC K) _ (frobC K) (fun a => by rw [frobC_inC, RingHom.coe_pow])
    (fun i => by rw [basisC_apply, frobC_inI]) z

theorem norm_inI (c : ↥(OL K)) :
    Algebra.norm (Per.Acris l) (inI K c) = aC l (wA l (fK K) (Algebra.norm (W0 K) c)) :=
  norm_map (Module.Free.chooseBasis (W0 K) ↥(OL K)) (basisC K) ((aC l).comp (wA l (fK K)).toRingHom) (inI K)
    (fun w => (inC_wA K w).symm) (fun i => (basisC_apply K i).symm) c

theorem prod_not_mem_two {π : ↥(OL K)} (hπ : Irreducible π) (z : CK K) (h0 : z ≠ 0) (hφ : frobC K z = inI K π * z)
    (h1 : uj T 0 (Algebra.norm (Per.Acris l) z) ∈ (P.PD K).Fil 1) :
    ∏ j ∈ Finset.range (fK K), uj T j (Algebra.norm (Per.Acris l) z) ∉ (P.PD K).Fil 2 := by
  haveI := isDomain_CK T K
  haveI := (GlobalTheory.AcrisNZD.acris_dom l).1
  have hN0 : Algebra.norm (Per.Acris l) z ≠ 0 := fun h => h0 (Algebra.norm_eq_zero_iff.1 h)
  obtain ⟨u, hu, hn⟩ := norm_unif K hπ
  have hf := norm_frobC K z
  rw [hφ, map_mul, norm_inI, hn, map_mul, map_mul, map_natCast, map_natCast] at hf
  generalize Algebra.norm (Per.Acris l) z = N at hN0 hf h1 ⊢
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨a, ha, hφa⟩ := exists_lang K v (IsUnit.of_mul_eq_one_right u hv)
  have hφa' : phiA l (aC l a) = aC l (wA l (fK K) v) * aC l a := by
    have := phiA_pow_aC 1 a
    rwa [pow_one, pow_one, hφa, map_mul] at this
  have huv : aC l (wA l (fK K) u) * aC l (wA l (fK K) v) = 1 := by
    rw [← map_mul, ← map_mul, hv, map_one, map_one]
  have hinj : Function.Injective (phiA l) := fun x y e =>
    jB_injective T ((P.PD K).φ_inj (by rw [phi_jB, phi_jB, e]))
  have hne : ∀ j : ℕ, (phiA l ^ j) N ≠ 0 := fun j e => hN0 (by
    rw [RingHom.coe_pow] at e
    exact hinj.iterate j (e.trans (iterate_map_zero _ _).symm))
  obtain ⟨M, hM⟩ : ∃ M, M = ∏ j ∈ Finset.range (fK K), (phiA l ^ j) N := ⟨_, rfl⟩
  have hφM : phiA l M = (l : Per.Acris l) * aC l (wA l (fK K) u) * M := by
    apply mul_right_cancel₀ hN0
    have e1 := Finset.prod_range_succ (fun j => (phiA l ^ j) N) (fK K)
    have e2 := Finset.prod_range_succ' (fun j => (phiA l ^ j) N) (fK K)
    have e3 : ∀ j, (phiA l ^ (j + 1)) N = phiA l ((phiA l ^ j) N) := fun j => by rw [pow_succ']; rfl
    simp only [e3] at e2
    rw [← map_prod, ← hM, e1, ← hM, ← hf] at e2
    refine e2.symm.trans ?_
    ring
  have hMu : uj T 0 M = ∏ j ∈ Finset.range (fK K), uj T j N := by
    rw [hM, map_prod]
    exact Finset.prod_congr rfl fun j _ => by rw [← uj_add, zero_add]
  have hM1 : uj T 0 M ∈ (P.PD K).Fil 1 := by
    rw [hMu, ← Finset.mul_prod_erase _ _ (Finset.mem_range.2 (NeZero.pos (fK K))), mul_comm]
    exact mul_mem_left K (GlobalTheory.prod_mem_Fil_zero_of_factors P K _ _ fun j _ => uj_mem T K j N) h1
  have hx : ∀ y, P.ιB (jB T y) = uj T 0 y := fun _ => rfl
  intro h2
  refine not_mem_two T K (jB T (aC l a * M)) ?_ (fun e => ?_) ?_ ?_
  · rw [phi_jB, ← map_natCast (jB T), ← map_mul, map_mul, hφa', hφM]
    congr 1
    linear_combination ((l : Per.Acris l) * aC l a * M) * huv
  · refine mul_ne_zero (ha.map (aC l)).ne_zero ?_ (jB_injective T (e.trans (map_zero _).symm))
    rw [hM]
    exact Finset.prod_ne_zero_iff.2 fun j _ => hne j
  · rw [hx, map_mul]
    exact mul_mem_left K (uj_mem T K 0 _) hM1
  · rw [hx, map_mul, hMu]
    exact mul_mem_left K (uj_mem T K 0 _) h2

theorem compat_of_add {j : ℕ} {s : ↥K.1 →ₐ[ℚ_[l]] Om l} (h : Compat T K (j + fK K) s) : Compat T K j s := fun w => by
  rw [← h w, uj_add, phiA_pow_aC, iter_wA]

theorem conj_add {j : ℕ} {s : ↥K.1 →ₐ[ℚ_[l]] Om l} (h : Compat T K (j + fK K) s) (b : BK K) :
    conj T K (j + fK K) s h b = conj T K j s (compat_of_add T K h) (frobB K b) :=
  RingHom.congr_fun (GlobalTheory.PZ.ColmezVec.ext_BK (conj T K (j + fK K) s h)
    ((conj T K j s (compat_of_add T K h)).comp (frobB K))
    (fun c => by rw [RingHom.comp_apply, frobB_inK, conj_inK, conj_inK])
    fun a => by rw [RingHom.comp_apply, frobB_toB, frobC_inC, conj_inC, conj_inC, uj_add, RingHom.coe_pow]) b

theorem conj_not_mem {π : ↥(OL K)} (hπ : Irreducible π) (t : BK K) (h0 : t ≠ 0)
    (hφ : frobB K t = inK K (π : ↥K.1) * t) (h1 : conj T K 0 K.1.val (compat_zero T K) t ∈ (P.PD K).Fil 1)
    (j : ℕ) (s : ↥K.1 →ₐ[ℚ_[l]] Om l) (h : Compat T K j s) (hs : s ≠ K.1.val) :
    conj T K j s h t ∉ (P.PD K).Fil 1 := by
  obtain ⟨D, z, hz⟩ := exists_pow_mul t
  have hz0 : z ≠ 0 := fun e => h0 (((isUnit_l K).pow D).mul_right_eq_zero.1 (by rw [hz, e, map_zero]))
  have hφz : frobC K z = inI K π * z := toB_injective K (by
    rw [← frobB_toB, map_mul, ← hz, map_mul, map_pow, map_natCast, hφ, ← inK_oK, mul_left_comm]
    rfl)
  have hmem : ∀ (j : ℕ) (s : ↥K.1 →ₐ[ℚ_[l]] Om l) (h : Compat T K j s), conj T K j s h t ∈ (P.PD K).Fil 1 →
      conj T K j s h (toB K z) ∈ (P.PD K).Fil 1 := fun j s h hm => by
    rw [← hz, map_mul]
    exact mul_mem_left K (conj_mem_Fil_zero l P AI T K j s h _) hm
  have hN1 := norm_mem_one T K _ z (hmem _ _ _ h1)
  obtain ⟨hA, hB⟩ := GlobalTheory.prod_degree_of_not_mem_Fil_two l P K (Finset.range (fK K))
    (fun j => uj T j (Algebra.norm (Per.Acris l) z)) 0 (Finset.mem_range.2 (NeZero.pos (fK K)))
    (fun j _ => uj_mem T K j _) hN1 (prod_not_mem_two T K hπ z hz0 hφz hN1)
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hm
    rcases lt_or_ge j (fK K) with hj | hj
    · rcases eq_or_ne j 0 with rfl | hj0
      · exact hA (norm_mem_two T K _ h hs z (hmem _ _ _ h1) (hmem _ _ _ hm))
      · exact hB j (Finset.mem_range.2 hj) hj0 (norm_mem_one T K h z (hmem _ _ _ hm))
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hj
      refine ih i (Nat.lt_add_of_pos_right (NeZero.pos (fK K))) (compat_of_add T K h) ?_
      rw [conj_add, hφ, map_mul, conj_inK] at hm
      have hp : s (π : ↥K.1) ≠ 0 := (map_ne_zero s).2 fun e => hπ.ne_zero (Subtype.ext e)
      have := mul_mem_left K (om_mem T K (s (π : ↥K.1))⁻¹) hm
      rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hp, map_one, one_mul] at this

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l), LTData K χ π z →
    ∃ t : BK K, (∀ g : ↥(GK K), galB g t = inK K (χ g : ↥K.1) * t) ∧
      ∀ (j : ℕ) (s : ↥K.1 →ₐ[ℚ_[l]] Om l) (h : Compat T K j s), s ≠ K.1.val →
        conj T K j s h t ∉ (P.PD K).Fil 1 := by
  intro l _ P AI T K χ π z hD
  obtain ⟨ω, t, u, hω, ht, h0, hφ, hg⟩ := exists_period K χ π z hD
  refine ⟨t, hg, conj_not_mem T K hD.1 t h0 hφ ?_⟩
  rw [ht, map_mul, mul_comm]
  exact mul_mem_left K (conj_mem_Fil_zero l P AI T K 0 _ _ u) (conj_zero_mem T K ω hω)

end GlobalTheory.ConjDegree

end
end
