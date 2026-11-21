import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTvalNeZero
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeLatticeOfLocalMatrixFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGramFrameEmbeddingMatrixNormOfVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeDeterminantLineTwoHermitianLattices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxSlopeSqLeOfNoShortVector
import Formalism.PolynomialDimension.WeylDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerProductFamilyMulOneDet
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsOrthonormalOfLinearIndependent
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreActionPreservesAdelicMatrices

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGramFrame_embeddingMatrixNormOfVector : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] [DecidableEq ι] (Y : (K →+* ℂ) → Matrix ι ι ℂ), (∀ σ, (Y σ).det ≠ 0) → IsGram (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) (matNorm Y) ∧ HasGram (matNorm Y) := by
  first | exact @GlobalTheory.DefPt.isGram_matNorm | exact GlobalTheory.DefPt.isGram_matNorm | (intros; apply GlobalTheory.DefPt.isGram_matNorm <;> assumption)
end

section
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.LocMatBasis

variable {K : Type} [Field K] [NumberField K]

theorem exists_notMem_mul_le (P u : HeightOneSpectrum (𝓞 K)) (y : K) (h : u ≠ P ∨ u.valuation K y ≤ 1) :
    ∃ s : 𝓞 K, s ∉ P.asIdeal ∧ u.valuation K ((s : K) * y) ≤ 1 := by
  have h1 : (1 : 𝓞 K) ∉ P.asIdeal := (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  by_cases hy : u.valuation K y ≤ 1
  · exact ⟨1, h1, by simpa using hy⟩
  have hne : u ≠ P := h.resolve_right hy
  have hy0 : u.valuation K y ≠ 0 := fun h0 => hy (by rw [h0]; exact zero_le_one)
  have hnle : ¬ u.asIdeal ≤ P.asIdeal := fun hle =>
    hne (HeightOneSpectrum.ext (u.isMaximal.eq_of_le P.isPrime.ne_top hle))
  obtain ⟨π, hπu, hπP⟩ := SetLike.not_le_iff_exists.1 hnle
  have hlt : u.valuation K (π : K) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem u π).2 hπu
  obtain ⟨N, hN⟩ := exists_pow_lt₀ hlt (Units.mk0 _ hy0)⁻¹
  refine ⟨π ^ N, fun hm => hπP (P.isPrime.mem_of_pow_mem N hm), ?_⟩
  have e : ((π ^ N : 𝓞 K) : K) = (π : K) ^ N := by simp
  rw [e, map_mul, map_pow]
  have hN' : u.valuation K (π : K) ^ N ≤ (u.valuation K y)⁻¹ := by simpa using hN.le
  calc _ ≤ (u.valuation K y)⁻¹ * u.valuation K y := by gcongr
    _ = 1 := inv_mul_cancel₀ hy0

theorem exists_denom_notMem {ι : Type} [Fintype ι] (B : HeightOneSpectrum (𝓞 K) → Matrix ι ι K)
    (h : {w | ¬ IntAt w (B w)}.Finite) (P : HeightOneSpectrum (𝓞 K)) (hP : IntAt P (B P)) :
    ∃ s : 𝓞 K, s ∉ P.asIdeal ∧ ∀ w, IntAt w ((s : K) • B w) := by
  classical
  haveI : Fintype {w | ¬ IntAt w (B w)} := h.fintype
  have hex : ∀ p : {w | ¬ IntAt w (B w)} × ι × ι, ∃ s : 𝓞 K, s ∉ P.asIdeal ∧
      p.1.1.valuation K ((s : K) * B p.1.1 p.2.1 p.2.2) ≤ 1 := fun p =>
    exists_notMem_mul_le P _ _ (Or.inl fun e => p.1.2 (by rw [e]; exact hP))
  choose s hs hv using hex
  refine ⟨∏ p, s p, fun hm => ?_, fun w i j => ?_⟩
  · obtain ⟨p, -, hp⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hm
    exact hs p hp
  by_cases hw : IntAt w (B w)
  · rw [Matrix.smul_apply, smul_eq_mul, map_mul]
    exact mul_le_one' (w.valuation_le_one _) (hw i j)
  · rw [Matrix.smul_apply, smul_eq_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨w, hw⟩, i, j))]
    have e : ∀ a b : 𝓞 K, ((a * b : 𝓞 K) : K) = (a : K) * (b : K) := fun a b => by simp
    rw [e, mul_assoc, map_mul]
    exact mul_le_one' (w.valuation_le_one _) (hv (⟨w, hw⟩, i, j))

theorem intAt_mul {ι : Type} [Fintype ι] {w : HeightOneSpectrum (𝓞 K)} {M N : Matrix ι ι K}
    (hM : IntAt w M) (hN : IntAt w N) : IntAt w (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  exact mul_le_one' (hM i k) (hN k j)

theorem finite_not_intAt {ι : Type} [Fintype ι] (M : Matrix ι ι K) :
    {w : HeightOneSpectrum (𝓞 K) | ¬ IntAt w M}.Finite := by
  refine (Set.finite_iUnion fun p : ι × ι => HeightOneSpectrum.Support.finite (𝓞 K) (M p.1 p.2)).subset ?_
  intro w hw
  simp only [IntAt, Set.mem_setOf_eq, not_forall, not_le] at hw
  obtain ⟨i, j, hij⟩ := hw
  exact Set.mem_iUnion.2 ⟨(i, j), hij⟩

theorem exists_locBasis_inv : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (A : HeightOneSpectrum (𝓞 K) → Matrix (Fin n) (Fin n) K), IsAdelic A → ∀ P : HeightOneSpectrum (𝓞 K), ∃ s : 𝓞 K, s ∉ P.asIdeal ∧ GlobalTheory.PtDeg.LocBasis P (locLat A) (fun j => (s : K) • ((A P)⁻¹ *ᵥ (Pi.single j 1 : Fin n → K))) := by
  intro K _ _ n A hA P
  classical
  obtain ⟨hdet, hfin⟩ := hA
  have hu : IsUnit (A P).det := isUnit_iff_ne_zero.2 (hdet P)
  have hone : ∀ (w : HeightOneSpectrum (𝓞 K)) (j k : Fin n), w.valuation K ((Pi.single j 1 : Fin n → K) k) ≤ 1 :=
    fun w j k => by by_cases hk : k = j <;> simp [Pi.single_apply, hk]
  obtain ⟨s, hs, hint⟩ := exists_denom_notMem (fun w => A w * (A P)⁻¹)
    ((hfin.union (finite_not_intAt (A P)⁻¹)).subset fun w hw => by
      by_contra hn
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn
      exact hw (intAt_mul hn.1.1 hn.2)) P (by
      intro i j
      rw [Matrix.mul_nonsing_inv _ hu]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij])
  have hs0 : (s : K) ≠ 0 := fun h0 => hs (by
    have : s = 0 := by exact_mod_cast h0
    rw [this]; exact P.asIdeal.zero_mem)
  refine ⟨s, hs, fun j w i => ?_, ?_, fun x hx => ?_⟩
  · rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Matrix.smul_mulVec]
    exact GlobalTheory.LocMatLat.mulVec_le w (hint w) (hone w j) i
  · have h1 : LinearIndependent K (A P)⁻¹.col :=
      Matrix.linearIndependent_cols_iff_isUnit.2 (Matrix.isUnit_nonsing_inv_iff.2 ((Matrix.isUnit_iff_isUnit_det _).2 hu))
    have h2 : LinearIndependent K (fun j => (s : K) • (A P)⁻¹.col j) :=
      h1.units_smul fun _ => Units.mk0 (s : K) hs0
    convert h2 using 3 with j
    simp
  · have hex := fun j => P.exists_primeCompl_mul_eq_of_integer _ (hx P j)
    choose c d hcd using hex
    have hd : (∏ j, (d j : 𝓞 K)) ∉ P.asIdeal := fun hm => by
      obtain ⟨p, -, hp⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hm
      exact (d p).2 hp
    refine ⟨(∏ j, (d j : 𝓞 K)) * s, fun hm => (P.isPrime.mem_or_mem hm).elim hd hs, ?_⟩
    have hx' : x = ∑ j, (A P *ᵥ x) j • ((A P)⁻¹ *ᵥ (Pi.single j 1 : Fin n → K)) := by
      simp_rw [← Matrix.mulVec_smul]
      rw [← Matrix.mulVec_sum, ← pi_eq_sum_univ', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu,
        Matrix.one_mulVec]
    rw [hx', Finset.smul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    have e : ((∏ k ∈ Finset.univ.erase j, (d k : 𝓞 K)) * (d j : 𝓞 K) * s) •
        (A P *ᵥ x) j • ((A P)⁻¹ *ᵥ (Pi.single j 1 : Fin n → K)) =
        ((∏ k ∈ Finset.univ.erase j, (d k : 𝓞 K)) * c j) •
          ((s : K) • ((A P)⁻¹ *ᵥ (Pi.single j 1 : Fin n → K))) := by
      rw [← algebraMap_smul K, ← algebraMap_smul K (_ * c j), smul_smul, smul_smul, map_mul, map_mul, map_mul,
        ← hcd j]
      congr 1
      change _ = _ * algebraMap (𝓞 K) K s
      ring
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end GlobalTheory.LocMatBasis
end

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localBasis_lattice_of_inverse_adelicMatrixFamily : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (A : HeightOneSpectrum (𝓞 K) → Matrix (Fin n) (Fin n) K), IsAdelic A → ∀ P : HeightOneSpectrum (𝓞 K), ∃ s : 𝓞 K, s ∉ P.asIdeal ∧ GlobalTheory.PtDeg.LocBasis P (locLat A) (fun j => (s : K) • ((A P)⁻¹ *ᵥ (Pi.single j 1 : Fin n → K))) := by
  atlas_forward_decl GlobalTheory.LocMatBasis.exists_locBasis_inv
end

section
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

theorem GlobalTheory.DefPt.det_gramPl_smul_single : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (eqv : ι ≃ Fin n) (Y : (K →+* ℂ) → Matrix ι ι ℂ), (∀ σ, (Y σ).det ≠ 0) → ∀ (t : K) (v : InfinitePlace K), (Formalism.HN.gramPl (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) v (fun k => t • (Pi.single (eqv.symm k) 1 : ι → K))).det.re = ‖v.embedding t‖ ^ (2 * n) * ‖(Y v.embedding).det‖ ^ 2 := by
  intro K _ _ _ ι _ _ n eqv Y hY t v
  have hinv : ((Y v.embedding)⁻¹)⁻¹ = Y v.embedding :=
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.2 (hY _))
  have hf : ∀ a : ι, Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) v
      (t • (Pi.single a 1 : ι → K)) = fun i => v.embedding t * Y v.embedding i a := by
    intro a
    funext i
    simp only [Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, hinv, Matrix.mulVec, dotProduct, Pi.basisFun_repr,
      Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single a]
    · simp [mul_comm]
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  have hg : Formalism.HN.gramPl (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) v
      (fun k => t • (Pi.single (eqv.symm k) 1 : ι → K)) =
      ((‖v.embedding t‖ ^ 2 : ℝ) : ℂ) • Matrix.reindex eqv eqv ((Y v.embedding)ᴴ * Y v.embedding) := by
    ext a b
    simp only [Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, hf, Matrix.of_apply, Matrix.smul_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Pi.star_apply,
      smul_eq_mul, Finset.mul_sum, star_mul']
    refine Finset.sum_congr rfl fun i _ => ?_
    have := Complex.conj_mul' (v.embedding t)
    push_cast
    rw [← this]
    simp only [RCLike.star_def]
    ring
  rw [hg, Matrix.det_smul, Matrix.det_reindex_self, Matrix.det_mul, Matrix.det_conjTranspose, Fintype.card_fin,
    RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re, ← pow_mul]
end

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramDeterminant_smul_standardBasis_inverse_frames : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (eqv : ι ≃ Fin n) (Y : (K →+* ℂ) → Matrix ι ι ℂ), (∀ σ, (Y σ).det ≠ 0) → ∀ (t : K) (v : InfinitePlace K), (Formalism.HN.gramPl (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) v (fun k => t • (Pi.single (eqv.symm k) 1 : ι → K))).det.re = ‖v.embedding t‖ ^ (2 * n) * ‖(Y v.embedding).det‖ ^ 2 := by
  atlas_forward_decl GlobalTheory.DefPt.det_gramPl_smul_single
end

section
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.LocMatSlope

variable {K : Type} [Field K] [NumberField K]

theorem exists_locBasis {n : ℕ} (A : HeightOneSpectrum (𝓞 K) → Matrix (Fin n) (Fin n) K) (hA : IsAdelic A)
    (P : HeightOneSpectrum (𝓞 K)) : ∃ s : 𝓞 K, s ∉ P.asIdeal ∧
      GlobalTheory.PtDeg.LocBasis P (locLat A) (fun j => (s : K) • ((A P)⁻¹ *ᵥ (Pi.single j 1 : Fin n → K))) :=
  GlobalTheory.T.exists_localBasis_lattice_of_inverse_adelicMatrixFamily K n A hA P

theorem det_gramPl [StarRing K] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (eqv : ι ≃ Fin n)
    (Y : (K →+* ℂ) → Matrix ι ι ℂ) (hY : ∀ σ, (Y σ).det ≠ 0) (t : K) (v : InfinitePlace K) :
    (Formalism.HN.gramPl (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) v
      (fun k => t • (Pi.single (eqv.symm k) 1 : ι → K))).det.re =
      ‖v.embedding t‖ ^ (2 * n) * ‖(Y v.embedding).det‖ ^ 2 :=
  GlobalTheory.T.gramDeterminant_smul_standardBasis_inverse_frames K ι n eqv Y hY t v

theorem smul_single_mem {ι : Type} [Fintype ι] [DecidableEq ι] (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K)
    (d : 𝓞 K) (hd : ∀ w, IntAt w ((d : K) • A w)) (i : ι) : (d : K) • (Pi.single i 1 : ι → K) ∈ locLat A := by
  intro w j
  have : (A w *ᵥ ((d : K) • (Pi.single i 1 : ι → K))) j = ((d : K) • A w) j i := by
    simp [Matrix.mulVec_smul, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
  rw [this]; exact hd w j i

theorem isAdelic_reindex {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (e : ι ≃ Fin n)
    {A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K} (hA : IsAdelic A) :
    IsAdelic (fun w => Matrix.reindex e e (A w)) := by
  refine ⟨fun w => by simpa [Matrix.det_reindex_self] using hA.1 w, hA.2.subset fun w hw h => hw ?_⟩
  have hi : ∀ (M : Matrix ι ι K), IntAt w M → IntAt w (Matrix.reindex e e M) :=
    fun M hM i j => by simpa using hM (e.symm i) (e.symm j)
  refine ⟨hi _ h.1, ?_⟩
  show IntAt w (Matrix.reindex e e (A w))⁻¹
  rw [Matrix.inv_reindex]
  exact hi _ h.2

theorem relIndex_reindex {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (e : ι ≃ Fin n)
    (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K) (t : K) :
    (Submodule.span (𝓞 K) (Set.range fun k => t • (Pi.single (e.symm k) 1 : ι → K))).toAddSubgroup.relIndex
        (locLat A).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range fun k => t • (Pi.single k 1 : Fin n → K))).toAddSubgroup.relIndex
        (locLat (fun w => Matrix.reindex e e (A w))).toAddSubgroup := by
  let φ : (ι → K) ≃ₗ[𝓞 K] (Fin n → K) := LinearEquiv.funCongrLeft (𝓞 K) K e.symm
  have hφ : ∀ x, φ x = fun k => x (e.symm k) := fun x => rfl
  have hmv : ∀ (M : Matrix ι ι K) (x : ι → K), Matrix.reindex e e M *ᵥ φ x = φ (M *ᵥ x) := by
    intro M x
    rw [hφ, hφ, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv M _ e.symm e.symm]
    ext k
    simp [Function.comp_def]
  have h1 : (Submodule.span (𝓞 K) (Set.range fun k => t • (Pi.single (e.symm k) 1 : ι → K))).map
      (φ : (ι → K) →ₗ[𝓞 K] (Fin n → K)) = Submodule.span (𝓞 K) (Set.range fun k => t • (Pi.single k 1 : Fin n → K)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext k
    simp only [Function.comp_apply, LinearEquiv.coe_coe, hφ]
    funext j
    simp [Pi.single_apply, e.symm_apply_eq, eq_comm]
  have h2 : (locLat A).map (φ : (ι → K) →ₗ[𝓞 K] (Fin n → K)) = locLat (fun w => Matrix.reindex e e (A w)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ w i
      rw [LinearEquiv.coe_coe, hmv, hφ]
      exact hx w (e.symm i)
    · intro hy
      refine ⟨φ.symm y, fun w i => ?_, by simp⟩
      have := hy w (e i)
      rw [show y = φ (φ.symm y) by simp, hmv, hφ] at this
      simpa using this
  rw [← h1, ← h2, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
  exact (AddSubgroup.relIndex_map_map_of_injective _ _ φ.injective).symm

theorem vAdd_mul_inv_pow {P : HeightOneSpectrum (𝓞 K)} {s : 𝓞 K} (hs : s ∉ P.asIdeal) (x : K) (n : ℕ) :
    vAdd P (x * ((s : K) ^ n)⁻¹) = vAdd P x := by
  have h1 : P.valuation K (s : K) = 1 := by
    rw [show ((s : K)) = algebraMap (𝓞 K) K s from rfl, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_eq_one_iff]
    exact hs
  unfold vAdd
  rw [map_mul, map_inv₀, map_pow, h1, one_pow, inv_one, mul_one]

theorem log_relIndex {n : ℕ} (A : HeightOneSpectrum (𝓞 K) → Matrix (Fin n) (Fin n) K) (hA : IsAdelic A)
    (t : 𝓞 K) (ht : t ≠ 0) (hmem : ∀ i, (t : K) • (Pi.single i 1 : Fin n → K) ∈ locLat A) :
    (Function.support fun w => (vAdd w ((t : K) ^ n * (A w).det) : ℝ)).Finite ∧
      ∑ᶠ w, (vAdd w ((t : K) ^ n * (A w).det) : ℝ) * lw K w =
        Real.log ((Submodule.span (𝓞 K) (Set.range fun i => (t : K) • (Pi.single i 1 : Fin n → K))).toAddSubgroup.relIndex
          (locLat A).toAddSubgroup : ℝ) / finrank ℚ K := by
  classical
  choose s hs hB using fun P => exists_locBasis A hA P
  have hL := GlobalTheory.LocMatLat.isLattice_locLat K (Fin n) A hA
  have htK : (t : K) ≠ 0 := by simpa using ht
  have hw : ReciprocityTheory.GeometryOfNumbersTheory.IsFrame K (locLat A) (fun i => (t : K) • (Pi.single i 1 : Fin n → K)) := by
    refine ⟨hmem, ?_, fun x _ => ?_⟩
    · have := (Pi.basisFun K (Fin n)).linearIndependent.units_smul (fun _ => Units.mk0 (t : K) htK)
      convert this using 1
      all_goals first
        | rfl
        | (funext i; simp [Pi.basisFun_apply])
    · have hx : x = ∑ i, (x i / t) • ((t : K) • (Pi.single i 1 : Fin n → K)) := by
        funext j
        simp [Finset.sum_apply, Pi.single_apply, smul_smul, div_mul_cancel₀ _ htK]
        rw [Algebra.smul_def, show algebraMap (𝓞 K) K t = (t : K) from rfl, mul_div_cancel₀ _ htK]
      rw [SetLike.mem_coe, hx]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hcomb : ∀ (P : HeightOneSpectrum (𝓞 K)) (i : Fin n), (t : K) • (Pi.single i 1 : Fin n → K) =
      ∑ j, (Matrix.of fun i j => (t : K) / (s P : K) * A P j i) i j •
        ((s P : K) • ((A P)⁻¹ *ᵥ (Pi.single j 1 : Fin n → K))) := by
    intro P i
    have hsK : (s P : K) ≠ 0 := by
      intro h0
      apply hs P
      have : s P = 0 := by simpa using h0
      rw [this]; exact P.asIdeal.zero_mem
    have hcol : ∑ j, A P j i • (Pi.single j 1 : Fin n → K) = A P *ᵥ Pi.single i 1 := by
      funext k
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]
    have e1 : ∀ j, (Matrix.of fun i j => (t : K) / (s P : K) * A P j i) i j •
        ((s P : K) • ((A P)⁻¹ *ᵥ (Pi.single j 1 : Fin n → K))) =
        (A P)⁻¹ *ᵥ (((t : K) * A P j i) • (Pi.single j 1 : Fin n → K)) := by
      intro j
      rw [Matrix.mulVec_smul, smul_smul, Matrix.of_apply]
      congr 1
      field_simp
    simp only [e1]
    rw [← Matrix.mulVec_sum]
    simp only [← smul_smul]
    rw [← Finset.smul_sum, hcol, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (Ne.isUnit (hA.1 P)), Matrix.one_mulVec]
  obtain ⟨hf, h⟩ := GlobalTheory.LatDetDeg.index_formula hL.fg hw _ _ hB hcomb
  have hv : ∀ P, vAdd P (Matrix.of fun i j => (t : K) / (s P : K) * A P j i).det =
      vAdd P ((t : K) ^ n * (A P).det) := by
    intro P
    have : (Matrix.of fun i j => (t : K) / (s P : K) * A P j i) = ((t : K) / (s P : K)) • (A P)ᵀ := by
      ext i j; simp
    rw [this, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin, div_pow, div_eq_mul_inv, mul_right_comm,
      vAdd_mul_inv_pow (hs P)]
  simp only [hv] at hf h
  exact ⟨hf, h⟩

end GlobalTheory.LocMatSlope

open GlobalTheory.LocMatSlope in

theorem GlobalTheory.LocMatSlope.slope_sq_locLat : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (ι : Type)
    [Fintype ι] [DecidableEq ι] [Nonempty ι] (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K)
    (Y : (K →+* ℂ) → Matrix ι ι ℂ), IsAdelic A → (∀ σ, (Y σ).det ≠ 0) →
    (∀ σ, ‖(Y ((starRingEnd ℂ).comp σ)).det‖ = ‖(Y σ).det‖) →
    slope_sq (matNorm Y) (locLat A) = 2 * detDeg A Y / (Fintype.card ι : ℝ) := by
  intro K _ _ _ ι _ _ _ A Y hA hY hconj
  classical
  letI : StarRing K := starRingOfComm
  set n := Fintype.card ι with hn
  set eqv : ι ≃ Fin n := Fintype.equivFin ι with heqv
  have hL := GlobalTheory.LocMatLat.isLattice_locLat K ι A hA
  have hG := (GlobalTheory.T.isGramFrame_embeddingMatrixNormOfVector K ι Y hY).1
  rw [slope_sq_eq hG hL.fg]
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.LocMatLat.exists_denom A (hA.2.subset fun w hw h => hw h.1)
  have hdK : (d : K) ≠ 0 := by simpa using hd0
  set e : Fin n → ι → K := fun k => (d : K) • (Pi.single (eqv.symm k) 1 : ι → K) with he
  have hli : LinearIndependent K e := by
    have := ((Pi.basisFun K ι).linearIndependent.comp eqv.symm eqv.symm.injective).units_smul
      (fun _ => Units.mk0 (d : K) hdK)
    convert this using 1
    all_goals first
      | rfl
      | (funext k; simp [he, Pi.basisFun_apply])
  have hle : Submodule.span (𝓞 K) (Set.range e) ≤ locLat A :=
    Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact smul_single_mem A d hd _)
  have hrk : Formalism.HN.rkK (locLat A) = n := by
    unfold Formalism.HN.rkK
    rw [hL.span_eq_top, finrank_top, Module.finrank_fintype_fun_eq_card]
  have hL0 : locLat A ≠ ⊥ := by
    intro h0
    have h := hL.span_eq_top
    rw [h0, Submodule.bot_coe, Submodule.span_zero_singleton] at h
    exact bot_ne_top h
  have hX : ∀ v : InfinitePlace K, IsUnit ((Y v.embedding)⁻¹).det := fun v => (hG v).1
  obtain ⟨-, hmu, -⟩ := Formalism.HN.size_maximal_slope K (ι → K) ι (Pi.basisFun K ι) _ hX _ hL.fg hL0
  have hpos := (Formalism.HN.place_lattice_structure K (ι → K) ι (Pi.basisFun K ι) _ hX _ hL.fg).2.2
  obtain ⟨hg1, hg2⟩ := Formalism.HN.height_gram_determinant K (ι → K) ι (Pi.basisFun K ι) _ hX n e hli
  have hht := hg2 (locLat A) hL.fg hle hrk
  rw [hg1] at hht
  have hA' := isAdelic_reindex eqv hA
  obtain ⟨hfin, hidx⟩ := log_relIndex (fun w => Matrix.reindex eqv eqv (A w)) hA' d hd0
    (fun i => smul_single_mem (fun w => Matrix.reindex eqv eqv (A w)) d
      (fun w i j => by simpa using hd w (eqv.symm i) (eqv.symm j)) i)
  rw [← relIndex_reindex eqv A (d : K)] at hidx
  simp only [Matrix.det_reindex_self] at hfin hidx
  set H := Formalism.HN.ht (Pi.basisFun K ι) (fun v ↦ (Y v.embedding)⁻¹) (locLat A) with hH
  set I : ℕ := (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex (locLat A).toAddSubgroup with hI
  have hidx' : ∑ᶠ w, (vAdd w ((d : K) ^ n * (A w).det) : ℝ) * lw K w = Real.log (I : ℝ) / finrank ℚ K := hidx
  have hdet : ∀ v : InfinitePlace K, (Formalism.HN.gramPl (Pi.basisFun K ι) (fun v ↦ (Y v.embedding)⁻¹) v e).det.re =
      ‖v.embedding (d : K)‖ ^ (2 * n) * ‖(Y v.embedding).det‖ ^ 2 := fun v => det_gramPl eqv Y hY (d : K) v
  have hdv : ∀ v : InfinitePlace K, 0 < ‖v.embedding (d : K)‖ := fun v => norm_pos_iff.2 ((map_ne_zero _).2 hdK)
  have hYv : ∀ v : InfinitePlace K, 0 < ‖(Y v.embedding).det‖ := fun v => norm_pos_iff.2 (hY _)
  have hfac : ∀ v : InfinitePlace K, 0 < ‖v.embedding (d : K)‖ ^ (2 * n) * ‖(Y v.embedding).det‖ ^ 2 :=
    fun v => mul_pos (pow_pos (hdv v) _) (pow_pos (hYv v) _)
  simp only [hdet] at hht
  have hprod : 0 < ∏ v : InfinitePlace K, ‖v.embedding (d : K)‖ ^ (2 * n) * ‖(Y v.embedding).det‖ ^ 2 :=
    Finset.prod_pos fun v _ => hfac v
  have hIpos : (0 : ℝ) < I := by
    rcases Nat.eq_zero_or_pos I with h | h
    · rw [h, Nat.cast_zero, mul_zero] at hht; linarith
    · exact_mod_cast h
  have hlogH : Real.log H = 2 * n * (∑ v : InfinitePlace K, Real.log ‖v.embedding (d : K)‖) +
      2 * (∑ v : InfinitePlace K, Real.log ‖(Y v.embedding).det‖) - Real.log I := by
    have h1 := congrArg Real.log hht
    rw [Real.log_mul hpos.ne' hIpos.ne', Real.log_prod (fun v _ => (hfac v).ne')] at h1
    have h2 : ∀ v : InfinitePlace K, Real.log (‖v.embedding (d : K)‖ ^ (2 * n) * ‖(Y v.embedding).det‖ ^ 2) =
        2 * n * Real.log ‖v.embedding (d : K)‖ + 2 * Real.log ‖(Y v.embedding).det‖ := fun v => by
      rw [Real.log_mul (pow_pos (hdv v) _).ne' (pow_pos (hYv v) _).ne', Real.log_pow, Real.log_pow]
      push_cast; ring
    simp only [h2, Finset.sum_add_distrib, ← Finset.mul_sum] at h1
    linarith
  have hsd : ∑ σ : K →+* ℂ, Real.log ‖σ (d : K)‖ = 2 * ∑ v : InfinitePlace K, Real.log ‖v.embedding (d : K)‖ :=
    GlobalTheory.SlopeMink.sum_embeddings_eq_two_mul (fun σ => Real.log ‖σ (d : K)‖) (fun σ => by
      simp [RingHom.comp_apply, Complex.norm_conj])
  have hsY : ∑ σ : K →+* ℂ, Real.log ‖(Y σ).det‖ = 2 * ∑ v : InfinitePlace K, Real.log ‖(Y v.embedding).det‖ :=
    GlobalTheory.SlopeMink.sum_embeddings_eq_two_mul (fun σ => Real.log ‖(Y σ).det‖) (fun σ => by simp only [hconj])
  have hnum := lineDeg_num hdK
  unfold lineDeg at hnum
  have hsplit : ∀ w, (vAdd w ((d : K) ^ n * (A w).det) : ℝ) = n * (vAdd w (d : K) : ℝ) + (vAdd w (A w).det : ℝ) :=
    fun w => by
      rw [GlobalTheory.LatDetDeg.vAdd_mul' w (pow_ne_zero _ hdK) (hA.1 w), GlobalTheory.LatDetDeg.vAdd_pow' w hdK]
      push_cast; ring
  have hfd := finite_vAdd (K := K) hdK
  have hfdet : (Function.support fun w => (vAdd w (A w).det : ℝ)).Finite := by
    refine (hfin.union hfd).subset fun w h => ?_
    by_contra hc
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc
    apply h
    have := hsplit w
    rw [hc.1, hc.2] at this
    show (vAdd w (A w).det : ℝ) = 0
    linarith
  have hsum : ∑ᶠ w, (vAdd w ((d : K) ^ n * (A w).det) : ℝ) * lw K w =
      n * ∑ᶠ w, (vAdd w (d : K) : ℝ) * lw K w + ∑ᶠ w, (vAdd w (A w).det : ℝ) * lw K w := by
    have e1 : ∀ w, (vAdd w ((d : K) ^ n * (A w).det) : ℝ) * lw K w =
        (n : ℝ) * ((vAdd w (d : K) : ℝ) * lw K w) + (vAdd w (A w).det : ℝ) * lw K w := fun w => by
      rw [hsplit]; ring
    simp only [e1]
    rw [finsum_add_distrib ((fin_mul hfd _).subset (Function.support_mul_subset_right _ _)) (fin_mul hfdet _),
      ← mul_finsum]
  have hD : (finrank ℚ K : ℝ) = 2 * (Formalism.HN.nPl K : ℝ) := by exact_mod_cast Formalism.HN.sizeMu_finrank_eq K
  have hF : (0 : ℝ) < Formalism.HN.nPl K := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (InfinitePlace K))
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  rw [hmu]
  unfold Formalism.HN.size
  rw [Real.log_rpow hpos, hrk, hlogH]
  unfold detDeg lineDeg
  rw [hsY]
  rw [hsum, hD] at hidx'
  rw [hsd, hD] at hnum
  set Sa := ∑ v : InfinitePlace K, Real.log ‖v.embedding (d : K)‖
  set Sb := ∑ v : InfinitePlace K, Real.log ‖(Y v.embedding).det‖
  set V := ∑ᶠ w, (vAdd w (A w).det : ℝ) * lw K w
  set W := ∑ᶠ w, (vAdd w (d : K) : ℝ) * lw K w
  set F := (Formalism.HN.nPl K : ℝ)
  have hW : W = 2 * Sa / (2 * F) := by linarith
  have hlogI : Real.log I = 2 * F * (n * W + V) := by
    field_simp at hidx'
    linarith
  rw [hlogI, hW, hD]
  field_simp
  ring
end
end

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeSlopeSq_localMatrices_eq_determinants : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K) (Y : (K →+* ℂ) → Matrix ι ι ℂ), IsAdelic A → (∀ σ, (Y σ).det ≠ 0) → (∀ σ, ‖(Y ((starRingEnd ℂ).comp σ)).det‖ = ‖(Y σ).det‖) → slope_sq (matNorm Y) (locLat A) = 2 * detDeg A Y / (Fintype.card ι : ℝ) := by
  atlas_forward_decl GlobalTheory.LocMatSlope.slope_sq_locLat
end

section
noncomputable section

namespace GlobalTheory.DefPt

open Matrix

section Char

variable {K : Type} [Field K] {n : ℕ} (χ : Matrix (Fin n) (Fin n) K →* K)

theorem matChar_submatrix (σ : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) K) :
    χ (M.submatrix σ σ) = χ M := by
  have h1 : ∀ N : Matrix (Fin n) (Fin n) K,
      σ.toPEquiv.toMatrix * N * σ.symm.toPEquiv.toMatrix = N.submatrix σ σ := by
    intro N
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm, submatrix_submatrix]
    rfl
  have h2 := congrArg χ (h1 1)
  rw [submatrix_one_equiv, Matrix.mul_one, map_mul, map_one] at h2
  rw [← h1 M, map_mul, map_mul, mul_comm (χ _) (χ M), mul_assoc, h2, mul_one]

theorem matChar_transvection [CharZero K] {i j : Fin n} (hij : i ≠ j) (c : K) :
    χ (transvection i j c) = 1 := by
  set D : Matrix (Fin n) (Fin n) K := diagonal (Function.update 1 i 2)
  set D' : Matrix (Fin n) (Fin n) K := diagonal (Function.update 1 i (1 / 2))
  have hDD : D * D' = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  have hD : χ D ≠ 0 := fun h => by
    have := congrArg χ hDD
    rw [map_mul, map_one, h, zero_mul] at this
    exact zero_ne_one this
  have hT : χ (transvection i j c) ≠ 0 := fun h => by
    have := congrArg χ (transvection_mul_transvection_same i j hij c (-c))
    rw [add_neg_cancel, transvection_zero, map_mul, map_one, h, zero_mul] at this
    exact zero_ne_one this
  have hcomm : D * transvection i j c = transvection i j (c + c) * D := by
    ext a b
    rw [diagonal_mul, mul_diagonal]
    have hdi : Function.update (1 : Fin n → K) i 2 i = 2 := by simp
    have hdj : Function.update (1 : Fin n → K) i 2 j = 1 := by simp [Ne.symm hij]
    simp only [transvection, Matrix.add_apply, Matrix.single_apply]
    by_cases h : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := h
      rw [Matrix.one_apply_ne hij, hdi, hdj]
      simp only [and_self, ite_true]
      ring
    · have h' : ¬(i = a ∧ j = b) := fun h' => h ⟨h'.1.symm, h'.2.symm⟩
      rw [if_neg h', if_neg h']
      simp only [add_zero]
      by_cases hab : a = b
      · subst hab; ring
      · rw [Matrix.one_apply_ne hab]; ring
  have e := congrArg χ hcomm
  rw [map_mul, map_mul, ← transvection_mul_transvection_same i j hij, map_mul, mul_comm (χ D)] at e
  have e2 : χ (transvection i j c) * 1 = χ (transvection i j c) * χ (transvection i j c) := by
    rw [mul_one]
    exact mul_right_cancel₀ hD e
  exact (mul_left_cancel₀ hT e2).symm

theorem matChar_mulSingle (k k' : Fin n) (a : K) :
    χ (diagonal (Pi.mulSingle k a)) = χ (diagonal (Pi.mulSingle k' a)) := by
  rw [← matChar_submatrix χ (Equiv.swap k k') (diagonal (Pi.mulSingle k' a)), submatrix_diagonal_equiv]
  congr 2
  funext x
  simp only [Function.comp_apply, Pi.mulSingle_apply]
  by_cases hx : x = k
  · subst hx; simp
  · by_cases hx' : x = k'
    · subst hx'; rw [Equiv.swap_apply_right]; simp [hx, Ne.symm hx]
    · rw [Equiv.swap_apply_of_ne_of_ne hx hx']; simp [hx, hx']

theorem matChar_diagonal_pow (m : ℕ) (hs : ∀ t : K, χ (t • 1) = t ^ m) (d : Fin n → K) :
    χ (diagonal d) ^ n = (diagonal d).det ^ m := by
  let ψ : (Fin n → K) →* K := χ.comp (diagonalRingHom (Fin n) K).toMonoidHom
  have hψ : ∀ v, ψ v = χ (diagonal v) := fun v => rfl
  have hone : ∀ (k : Fin n) (a : K), χ (diagonal (Pi.mulSingle k a)) ^ n = a ^ m := by
    intro k a
    calc χ (diagonal (Pi.mulSingle k a)) ^ n = ∏ k' : Fin n, ψ (Pi.mulSingle k' a) := by
          rw [Finset.prod_congr rfl fun k' _ => (hψ _).trans (matChar_mulSingle χ k' k a), Finset.prod_const,
            Finset.card_univ, Fintype.card_fin]
      _ = ψ (fun _ => a) := by rw [← map_prod, Finset.univ_prod_mulSingle]
      _ = a ^ m := by rw [hψ, ← smul_one_eq_diagonal, hs]
  calc χ (diagonal d) ^ n = (∏ k, ψ (Pi.mulSingle k (d k))) ^ n := by
        rw [← map_prod, Finset.univ_prod_mulSingle, hψ]
    _ = ∏ k, d k ^ m := by
        rw [← Finset.prod_pow]; exact Finset.prod_congr rfl fun k _ => hone k (d k)
    _ = (diagonal d).det ^ m := by rw [det_diagonal, Finset.prod_pow]

theorem matChar_pow_eq_det_pow [CharZero K] (m : ℕ) (hs : ∀ t : K, χ (t • 1) = t ^ m)
    (g : Matrix (Fin n) (Fin n) K) : χ g ^ n = g.det ^ m := by
  refine diagonal_transvection_induction (fun M => χ M ^ n = M.det ^ m) g
    (fun D _ => matChar_diagonal_pow χ m hs D) (fun t => ?_) (fun A B hA hB => ?_)
  · show χ t.toMatrix ^ n = t.toMatrix.det ^ m
    rw [show t.toMatrix = transvection t.i t.j t.c from rfl, matChar_transvection χ t.hij,
      det_transvection_of_ne _ _ t.hij]
    simp
  · show χ (A * B) ^ n = (A * B).det ^ m
    have hA' : χ A ^ n = A.det ^ m := hA
    have hB' : χ B ^ n = B.det ^ m := hB
    rw [map_mul, det_mul, mul_pow, mul_pow, hA', hB']

end Char

end GlobalTheory.DefPt

namespace GlobalTheory.DefPt

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine MvPolynomial
open scoped Matrix

def rhoDetHom {n : ℕ} (la : Fin n → ℕ) (K : Type) [Field K] [CharZero K] : Matrix (Fin n) (Fin n) K →* K where
  toFun g := (GlobalTheory.DefPt.rhoMat la g).det
  map_one' := by rw [Model.rhoMat_one, Matrix.det_one]
  map_mul' g h := by rw [Model.rhoMat_mul, Matrix.det_mul, mul_comm]

theorem det_rhoMat_pow : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (la : Fin n → ℕ), Antitone la →
    ∀ g : Matrix (Fin n) (Fin n) K, (rhoMat la g).det ^ n = g.det ^ (size la * dim la) := by
  intro K _ _ n la _ g
  have hs : ∀ t : K, rhoDetHom la K (t • 1) = t ^ (size la * dim la) := by
    intro t
    show (GlobalTheory.DefPt.rhoMat la (t • 1)).det = _
    rw [Model.rhoMat_scalar, Matrix.det_smul, Matrix.det_one, mul_one, dim_eq_card, pow_mul]
  exact matChar_pow_eq_det_pow (rhoDetHom la K) _ hs g

end GlobalTheory.DefPt

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial in
open scoped Matrix in
example : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (la : Fin n → ℕ), Antitone la → ∀ g : Matrix (Fin n) (Fin n) K, (rhoMat la g).det ^ n = g.det ^ (size la * dim la) :=
  GlobalTheory.DefPt.det_rhoMat_pow
end
end

section
section
open scoped Matrix

namespace GlobalTheory.UnitaryMinor

theorem sum_norm_sq_col {n : ℕ} (u : Matrix.unitaryGroup (Fin n) ℂ) (j : Fin n) :
    ∑ i, ‖u.1 i j‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 u.2) j) j
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
  have h2 : ((∑ i, ‖u.1 i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  exact_mod_cast h2

theorem norm_det_submatrix_le_one (n s : ℕ) (u : Matrix.unitaryGroup (Fin n) ℂ)
    (I J : Fin s → Fin n) : ‖(u.1.submatrix I J).det‖ ≤ 1 := by
  by_cases hI : Function.Injective I
  · have h : ‖(u.1.submatrix I J).det‖ ^ 2 ≤ 1 := by
      refine (GlobalTheory.Hadamard.norm_det_sq_le_prod_col (u.1.submatrix I J)).trans ?_
      refine Finset.prod_le_one (fun j _ => Finset.sum_nonneg fun _ _ => by positivity)
        fun j _ => ?_
      rw [← sum_norm_sq_col u (J j)]
      simp only [Matrix.submatrix_apply]
      rw [← Finset.sum_image (s := Finset.univ) (g := I) (f := fun i => ‖u.1 i (J j)‖ ^ 2)
        (fun a _ b _ h => hI h)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun _ _ _ => by positivity
    exact (sq_le_one_iff₀ (norm_nonneg _)).1 h
  · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.1 hI
    rw [Matrix.det_zero_of_row_eq hne (by funext k; simp [hab])]
    simp

theorem unitary_minor_and_hadamard :
    (∀ (n s : ℕ) (u : Matrix.unitaryGroup (Fin n) ℂ) (I J : Fin s → Fin n),
      ‖(u.1.submatrix I J).det‖ ≤ 1) ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ),
      ‖M.det‖ ^ 2 ≤ ∏ j, ∑ i, ‖M i j‖ ^ 2 :=
  ⟨norm_det_submatrix_le_one, fun _ _ _ M => GlobalTheory.Hadamard.norm_det_sq_le_prod_col M⟩

end GlobalTheory.UnitaryMinor
end

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_minor_le_one_and_hadamard_columns : (∀ (n s : ℕ) (u : Matrix.unitaryGroup (Fin n) ℂ) (I J : Fin s → Fin n), ‖(u.1.submatrix I J).det‖ ≤ 1) ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ), ‖M.det‖ ^ 2 ≤ ∏ j, ∑ i, ‖M i j‖ ^ 2 := by
  atlas_forward_decl GlobalTheory.UnitaryMinor.unitary_minor_and_hadamard
end

section
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.OnMatGram

theorem norm_evalAt_intVec_le {n : ℕ} (la : Fin n → ℕ) (j : Idx la) (g : UN n) :
    ‖evalAt g.1 (map (Int.castRingHom ℂ) (intVec la j))‖ ≤ 1 := by
  obtain ⟨-, -, K, sz, hsz, I, -, -, hb⟩ := (Formalism.GradedWeylDivisibility.sSBasis ℤ n n la).choose_spec.2 j
  have hv : intVec la j = Formalism.GradedWeylDivisibility.bideterminant ℤ sz hsz I := hb
  rw [hv, Formalism.GradedWeylDivisibility.ldlat_map_bidet]
  unfold Formalism.GradedWeylDivisibility.bideterminant
  rw [map_prod, norm_prod]
  refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun k _ => ?_
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [Formalism.GradedWeylDivisibility.algHom_det_of]
  have h : (Matrix.of fun p q : Fin (sz k) => evalAt g.1 (X (I k p, Fin.castLE (hsz k) q) : Pol n ℂ)) =
      g.1.submatrix (I k) (Fin.castLE (hsz k)) := by
    ext p q
    simp
  rw [h]
  exact GlobalTheory.T.unitary_minor_le_one_and_hadamard_columns.1 n (sz k) g (I k) (Fin.castLE (hsz k))

theorem normSq_basis_le {n : ℕ} (la : Fin n → ℕ) (j : Idx la) :
    normSq la (basis la ℂ j).1 ≤ dim la := by
  refine normSq_le_dim fun g => ?_
  rw [coe_basis]
  exact norm_evalAt_intVec_le la j g

theorem sum_norm_sq_onMat {n : ℕ} (la : Fin n → ℕ) (j : Idx la) :
    ∑ i, ‖onMat la i j‖ ^ 2 = normSq la (basis la ℂ j).1 := by
  rw [← norm_toSpace_sq, ← (onBasis la).repr.norm_map, EuclideanSpace.norm_sq_eq]
  rfl

theorem det_onMat_ne_zero {n : ℕ} (la : Fin n → ℕ) : (onMat la).det ≠ 0 := by
  let c : Module.Basis (Idx la) ℂ (Space la) := (basis la ℂ).map (toSpace la)
  have hc : onMat la = (onBasis la).toBasis.toMatrix c := by
    ext i j
    simp [onMat, c, Module.Basis.toMatrix_apply]
  rw [hc]
  exact (Matrix.isUnit_det_of_left_inverse (Module.Basis.toMatrix_mul_toMatrix_flip c _)).ne_zero

end GlobalTheory.OnMatGram

namespace GlobalTheory.OnMatGram

theorem norm_det_onMat_sq_le : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → (onMat la).det ≠ 0 ∧ ‖(onMat la).det‖ ^ 2 ≤ (dim la : ℝ) ^ dim la := by
  intro n la _
  refine ⟨det_onMat_ne_zero la, ?_⟩
  refine (GlobalTheory.T.unitary_minor_le_one_and_hadamard_columns.2 (Idx la) (onMat la)).trans ?_
  calc ∏ j, ∑ i, ‖onMat la i j‖ ^ 2 ≤ ∏ _j : Idx la, (dim la : ℝ) :=
        Finset.prod_le_prod (fun j _ => Finset.sum_nonneg fun _ _ => by positivity)
          fun j _ => (sum_norm_sq_onMat la j).trans_le (normSq_basis_le la j)
    _ = (dim la : ℝ) ^ dim la := by rw [Finset.prod_const, Finset.card_univ, ← dim_eq_card]

end GlobalTheory.OnMatGram
end

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_gramDeterminant_le_dim_pow_dim : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la → (onMat la).det ≠ 0 ∧ ‖(onMat la).det‖ ^ 2 ≤ (dim la : ℝ) ^ dim la := by
  atlas_forward_decl GlobalTheory.OnMatGram.norm_det_onMat_sq_le
end

section
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.FibSlope

section Log

variable {K : Type} [Field K] {φ : K → ℝ} (hφ : ∀ x y, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
include hφ

theorem log_one : φ 1 = 0 := by
  have := hφ 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at this
  linarith

theorem log_prod {ι : Type} (s : Finset ι) (f : ι → K) (hf : ∀ i, f i ≠ 0) :
    φ (∏ i ∈ s, f i) = ∑ i ∈ s, φ (f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using log_one hφ
  | cons i s hi ih =>
    rw [Finset.prod_cons, Finset.sum_cons, hφ _ _ (hf i) (Finset.prod_ne_zero_iff.2 fun j _ => hf j), ih]

theorem log_pow {x : K} (hx : x ≠ 0) (n : ℕ) : φ (x ^ n) = n * φ x := by
  have := log_prod hφ (Finset.range n) (fun _ => x) fun _ => hx
  simpa using this

theorem log_det_rhoMat [CharZero K] {n : ℕ} {la : Fin n → ℕ} (hla : Antitone la) {g : Matrix (Fin n) (Fin n) K}
    (hg : g.det ≠ 0) : (rhoMat la g).det ≠ 0 ∧
      φ (rhoMat la g).det = (dim la : ℝ) * ((size la : ℝ) / (n : ℝ) * φ g.det) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Subsingleton.elim g 1, GlobalTheory.DefPt.Model.rhoMat_one, Matrix.det_one, log_one hφ]
    simp
  · have h := det_rhoMat_pow K n la hla g
    have h0 : (rhoMat la g).det ≠ 0 := fun h0 => by
      rw [h0, zero_pow hn.ne'] at h
      exact pow_ne_zero _ hg h.symm
    refine ⟨h0, ?_⟩
    have h1 := congrArg φ h
    rw [log_pow hφ h0, log_pow hφ hg] at h1
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    push_cast at h1
    field_simp
    linarith

theorem log_det_kron {T : Type} [Fintype T] [DecidableEq T] {J : T → Type} [∀ t, Fintype (J t)]
    [∀ t, DecidableEq (J t)] {c : K} (hc : c ≠ 0) (M : ∀ t, Matrix (J t) (J t) K) (hM : ∀ t, (M t).det ≠ 0)
    (r : T → ℝ) (hr : ∀ t, φ (M t).det = Fintype.card (J t) * r t) :
    (c • kron M).det ≠ 0 ∧ φ (c • kron M).det = Fintype.card (∀ t, J t) * (φ c + ∑ t, r t) := by
  have hk := (kronFamily_mul_one_det T J K M M).2.2
  have hp : ∀ t, (M t).det ^ (∏ s ∈ Finset.univ.erase t, Fintype.card (J s)) ≠ 0 := fun t => pow_ne_zero _ (hM t)
  have h0 : (kron M).det ≠ 0 := hk ▸ Finset.prod_ne_zero_iff.2 fun t _ => hp t
  rw [Matrix.det_smul]
  refine ⟨mul_ne_zero (pow_ne_zero _ hc) h0, ?_⟩
  rw [hφ _ _ (pow_ne_zero _ hc) h0, log_pow hφ hc, hk, log_prod hφ _ _ hp, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [log_pow hφ (hM t), hr, ← mul_assoc, ← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ t),
    Fintype.card_pi]

end Log

section Val

variable {K : Type} [Field K] [NumberField K]

theorem vAdd_mul_real (w : HeightOneSpectrum (𝓞 K)) (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    (vAdd w (x * y) : ℝ) = vAdd w x + vAdd w y := by
  have h1 : w.valuation K x ≠ 0 := by simpa using hx
  have h2 : w.valuation K y ≠ 0 := by simpa using hy
  rw [← Int.cast_add, vAdd, vAdd, vAdd, map_mul, WithZero.log_mul h1 h2, neg_add]

theorem valuation_det_le {ι : Type} [Fintype ι] [DecidableEq ι] (w : HeightOneSpectrum (𝓞 K)) {M : Matrix ι ι K}
    (hM : IntAt w M) : w.valuation K M.det ≤ 1 := by
  rw [Matrix.det_apply']
  refine Valuation.map_sum_le _ fun σ _ => ?_
  rw [map_mul, map_prod]
  refine mul_le_one' ?_ (Finset.prod_le_one' fun i _ => hM _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem finite_vAdd_det {ι : Type} [Fintype ι] [DecidableEq ι] {A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K}
    (hA : IsAdelic A) : (Function.support fun w => (vAdd w (A w).det : ℝ)).Finite := by
  refine hA.2.subset fun w hw h => hw ?_
  have h1 := valuation_det_le w h.1
  have h2 := valuation_det_le w h.2
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀] at h2
  have h0 : w.valuation K (A w).det ≠ 0 := by simpa using hA.1 w
  have h3 : w.valuation K (A w).det = 1 :=
    le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 h0)).1 h2)
  simp [vAdd, h3]

end Val

theorem log_norm_mul (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) : Real.log ‖x * y‖ = Real.log ‖x‖ + Real.log ‖y‖ := by
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy)]

variable {T : Type} [Fintype T] [DecidableEq T] {N : T → ℕ} {la : ∀ t, Fin (N t) → ℕ}

theorem vAdd_det_fibA {K : Type} [Field K] [NumberField K] (hla : ∀ t, Antitone (la t)) (w : HeightOneSpectrum (𝓞 K))
    {a : K} (ha : a ≠ 0) {B : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K} (hB : ∀ t, (B t).det ≠ 0) :
    (vAdd w (fibA la a B).det : ℝ) =
      Fintype.card (TIdx la) * (vAdd w a + ∑ t, (size (la t) : ℝ) / (N t : ℝ) * vAdd w (B t).det) :=
  (log_det_kron (φ := fun x => (vAdd w x : ℝ)) (vAdd_mul_real w) ha _
    (fun t => (log_det_rhoMat (φ := fun x => (vAdd w x : ℝ)) (vAdd_mul_real w) (hla t) (hB t)).1) _
    (fun t => by
      rw [← dim_eq_card]
      exact (log_det_rhoMat (φ := fun x => (vAdd w x : ℝ)) (vAdd_mul_real w) (hla t) (hB t)).2)).2

theorem log_det_fibY (hla : ∀ t, Antitone (la t)) {s : ℝ} (hs : 0 < s) {X : ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ}
    (hX : ∀ t, (X t).det ≠ 0) : (fibY la s X).det ≠ 0 ∧ Real.log ‖(fibY la s X).det‖ =
      Fintype.card (TIdx la) * (Real.log s + ∑ t, (Real.log ‖(onMat (la t)).det‖ / dim (la t) +
        (size (la t) : ℝ) / (N t : ℝ) * Real.log ‖(X t).det‖)) := by
  have hρ := fun t => log_det_rhoMat (φ := fun x : ℂ => Real.log ‖x‖) log_norm_mul (hla t) (hX t)
  have ho := fun t => (GlobalTheory.T.dualWeyl_gramDeterminant_le_dim_pow_dim _ (la t) (hla t)).1
  have h := log_det_kron (φ := fun x : ℂ => Real.log ‖x‖) log_norm_mul (c := (s : ℂ))
    (Complex.ofReal_ne_zero.2 hs.ne') (fun t => onMat (la t) * rhoMat (la t) (X t))
    (fun t => by rw [Matrix.det_mul]; exact mul_ne_zero (ho t) (hρ t).1)
    (fun t => Real.log ‖(onMat (la t)).det‖ / dim (la t) + (size (la t) : ℝ) / (N t : ℝ) * Real.log ‖(X t).det‖)
    (fun t => by
      have hd : (dim (la t) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (dim_pos (hla t)).ne'
      have h2 := (hρ t).2
      rw [← dim_eq_card, Matrix.det_mul, log_norm_mul _ _ (ho t) (hρ t).1, h2, mul_add, mul_div_cancel₀ _ hd])
  simp only [Complex.norm_real, Real.norm_of_nonneg hs.le] at h
  exact h

theorem log_det_onMat_le {n : ℕ} {la : Fin n → ℕ} (hla : Antitone la) :
    Real.log ‖(onMat la).det‖ / dim la ≤ Real.log (dim la) / 2 := by
  obtain ⟨h0, h⟩ := GlobalTheory.T.dualWeyl_gramDeterminant_le_dim_pow_dim _ la hla
  have hd : (0 : ℝ) < dim la := Nat.cast_pos.2 (dim_pos hla)
  have h1 := Real.log_le_log (pow_pos (norm_pos_iff.2 h0) 2) h
  rw [Real.log_pow, Real.log_pow] at h1
  rw [div_le_iff₀ hd]
  push_cast at h1
  linarith

theorem slope_fibre_ge : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ), (∀ t, Antitone (la t)) → ∀ (a : HeightOneSpectrum (𝓞 K) → K) (B : HeightOneSpectrum (𝓞 K) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) (s : (K →+* ℂ) → ℝ) (X : (K →+* ℂ) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ), (∀ w, a w ≠ 0) → (Function.support fun w => vAdd w (a w)).Finite → (∀ t, IsAdelic fun w => B w t) → (∀ σ, 0 < s σ) → (∀ σ t, (X σ t).det ≠ 0) → (∀ σ, s ((starRingEnd ℂ).comp σ) = s σ) → (∀ σ t, ‖(X ((starRingEnd ℂ).comp σ) t).det‖ = ‖(X σ t).det‖) → (∀ σ, (fibY la (s σ) (X σ)).det ≠ 0) ∧ lineDeg s (fun w => (vAdd w (a w) : ℝ)) + ∑ t, ((size (la t) : ℝ) / (N t : ℝ) * detDeg (fun w => B w t) (fun σ => X σ t) - Real.log (dim (la t)) / 2) ≤ slope_sq (matNorm fun σ => fibY la (s σ) (X σ)) (locLat fun w => fibA la (a w) (B w)) / 2 := by
  intro K _ _ _ T _ _ N la hla a B s X ha hfa hB hs hX hsc hXc
  have hY := fun σ => log_det_fibY hla (hs σ) (hX σ)
  refine ⟨fun σ => (hY σ).1, ?_⟩
  have hD : 0 < Fintype.card (TIdx la) := by
    rw [Fintype.card_pi]
    exact Finset.prod_pos fun t _ => dim_eq_card (la t) ▸ dim_pos (hla t)
  haveI : Nonempty (TIdx la) := Fintype.card_pos_iff.1 hD
  have hD' : (Fintype.card (TIdx la) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hD.ne'
  have hK : (0 : ℝ) < finrank ℚ K := Nat.cast_pos.mpr finrank_pos
  rw [GlobalTheory.T.latticeSlopeSq_localMatrices_eq_determinants K (TIdx la) _ _ (GlobalTheory.FibAdel.fibA_isAdelic K T N la a B ha hfa hB) (fun σ => (hY σ).1)
    (fun σ => Real.log_injOn_pos (norm_pos_iff.2 (hY _).1) (norm_pos_iff.2 (hY _).1) (by
      rw [(hY _).2, (hY _).2]; simp only [hsc, hXc]))]
  have hfa' : (Function.support fun w => (vAdd w (a w) : ℝ)).Finite := hfa.subset fun w hw h => hw (by
    simp only at h ⊢; rw [h, Int.cast_zero])
  have hfB := fun t => finite_vAdd_det (hB t)
  have hfin : ∑ᶠ w, (vAdd w (fibA la (a w) (B w)).det : ℝ) * lw K w = Fintype.card (TIdx la) *
      (∑ᶠ w, (vAdd w (a w) : ℝ) * lw K w +
        ∑ t, (size (la t) : ℝ) / (N t : ℝ) * ∑ᶠ w, (vAdd w (B w t).det : ℝ) * lw K w) := by
    have hsub : ∀ t, (Function.support fun w => (size (la t) : ℝ) / (N t : ℝ) *
        ((vAdd w (B w t).det : ℝ) * lw K w)).Finite := fun t =>
      (fin_mul (hfB t) (lw K)).subset (Function.support_mul_subset_right _ _)
    simp only [mul_finsum]
    rw [← finsum_sum_comm _ _ (fun t _ => hsub t), ← finsum_add_distrib (fin_mul hfa' _), mul_finsum]
    · refine finsum_congr fun w => ?_
      rw [vAdd_det_fibA hla w (ha w) (fun t => (hB t).1 w), mul_assoc, add_mul, Finset.sum_mul]
      simp only [mul_assoc]
    · exact (Set.finite_iUnion hsub).subset fun w hw => by
        by_contra hn
        simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hn
        exact hw (Finset.sum_eq_zero fun t _ => hn t)
  have hinf : ∑ σ, Real.log ‖(fibY la (s σ) (X σ)).det‖ = Fintype.card (TIdx la) *
      (∑ σ, Real.log (s σ) + ∑ t, (finrank ℚ K * (Real.log ‖(onMat (la t)).det‖ / dim (la t)) +
        (size (la t) : ℝ) / (N t : ℝ) * ∑ σ, Real.log ‖(X σ t).det‖)) := by
    simp only [(hY _).2]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Embeddings.card, nsmul_eq_mul,
      Finset.mul_sum]
  simp only [detDeg, lineDeg]
  rw [hfin, hinf]
  have key : ∀ u v : ℝ, 2 * (Fintype.card (TIdx la) * u - Fintype.card (TIdx la) * v / finrank ℚ K) /
      (Fintype.card (TIdx la) : ℝ) / 2 = u - v / finrank ℚ K := fun u v => by field_simp
  rw [key, add_div, Finset.sum_div (ι := T)]
  have hle : ∑ t, ((size (la t) : ℝ) / (N t : ℝ) * ((∑ᶠ w, (vAdd w (B w t).det : ℝ) * lw K w) -
      (∑ σ, Real.log ‖(X σ t).det‖) / finrank ℚ K) - Real.log (dim (la t)) / 2) ≤
      ∑ t, ((size (la t) : ℝ) / (N t : ℝ) * ∑ᶠ w, (vAdd w (B w t).det : ℝ) * lw K w -
        (finrank ℚ K * (Real.log ‖(onMat (la t)).det‖ / dim (la t)) +
        (size (la t) : ℝ) / (N t : ℝ) * ∑ σ, Real.log ‖(X σ t).det‖) / finrank ℚ K) :=
    Finset.sum_le_sum fun t _ => by
      have := log_det_onMat_le (hla t)
      rw [add_div, mul_div_cancel_left₀ _ hK.ne', mul_sub, mul_div_assoc]
      linarith
  rw [Finset.sum_sub_distrib (f := fun t => (size (la t) : ℝ) / (N t : ℝ) * ∑ᶠ w, (vAdd w (B w t).det : ℝ) * lw K w)]
    at hle
  linarith

end GlobalTheory.FibSlope

end
end

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slope_dualWeylFibreLattice_ge : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ), (∀ t, Antitone (la t)) → ∀ (a : HeightOneSpectrum (𝓞 K) → K) (B : HeightOneSpectrum (𝓞 K) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) (s : (K →+* ℂ) → ℝ) (X : (K →+* ℂ) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ), (∀ w, a w ≠ 0) → (Function.support fun w => vAdd w (a w)).Finite → (∀ t, IsAdelic fun w => B w t) → (∀ σ, 0 < s σ) → (∀ σ t, (X σ t).det ≠ 0) → (∀ σ, s ((starRingEnd ℂ).comp σ) = s σ) → (∀ σ t, ‖(X ((starRingEnd ℂ).comp σ) t).det‖ = ‖(X σ t).det‖) → (∀ σ, (fibY la (s σ) (X σ)).det ≠ 0) ∧ lineDeg s (fun w => (vAdd w (a w) : ℝ)) + ∑ t, ((size (la t) : ℝ) / (N t : ℝ) * detDeg (fun w => B w t) (fun σ => X σ t) - Real.log (dim (la t)) / 2) ≤ slope_sq (matNorm fun σ => fibY la (s σ) (X σ)) (locLat fun w => fibA la (a w) (B w)) / 2 := by
  atlas_forward_decl GlobalTheory.FibSlope.slope_fibre_ge
end
