import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AevalNeZeroOfNotMem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartNormPtsA
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Values
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericFlagAlgebraicallyIndependent

section
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.MinorAny

theorem minorIJ_map {R S : Type} [CommRing R] [CommRing S] {N : ℕ} (f : R →+* S)
    (A : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) :
    minorIJ (A.map f) I J = f (minorIJ A I J) := by
  unfold minorIJ
  split_ifs with e
  · rw [RingHom.map_det]
    rfl
  · exact (map_zero f).symm

def gap {N : ℕ} {Ω : Type} [Field Ω] (T : Matrix (Fin N) (Fin N) Ω) (c₀ c₁ : Ω)
    (coef u : Finset (Fin N) → Ω) (J : Finset (Fin N)) (S : Type) [CommRing S] [Algebra Ω S]
    (h : Matrix (Fin N) (Fin N) S) : S :=
  algebraMap Ω S c₀ * ∑ I, algebraMap Ω S (coef I) * minorIJ (T.map (algebraMap Ω S) * h) I J -
    algebraMap Ω S c₁ * ∑ I, algebraMap Ω S (u I) * minorIJ h I J

theorem gap_map {N : ℕ} {Ω : Type} [Field Ω] (T : Matrix (Fin N) (Fin N) Ω) (c₀ c₁ : Ω)
    (coef u : Finset (Fin N) → Ω) (J : Finset (Fin N)) {S S' : Type} [CommRing S] [Algebra Ω S]
    [CommRing S'] [Algebra Ω S'] (f : S →ₐ[Ω] S') (h : Matrix (Fin N) (Fin N) S) :
    f (gap T c₀ c₁ coef u J S h) = gap T c₀ c₁ coef u J S' (h.map f.toRingHom) := by
  have hm : ∀ (M : Matrix (Fin N) (Fin N) S) (I J : Finset (Fin N)),
      f (minorIJ M I J) = minorIJ (M.map f.toRingHom) I J :=
    fun M I J => (minorIJ_map f.toRingHom M I J).symm
  have hT : (T.map (algebraMap Ω S) * h).map f.toRingHom = T.map (algebraMap Ω S') * h.map f.toRingHom := by
    rw [Matrix.map_mul, Matrix.map_map]
    congr 1
    congr 1
    funext x
    exact f.commutes x
  simp only [gap, map_sub, map_mul, map_sum, AlgHom.commutes, hm, hT]

theorem minor_any : ∀ (Ω : Type) [Field Ω] [Infinite Ω] (N j : ℕ) (T : Matrix (Fin N) (Fin N) Ω) (c₀ c₁ : Ω) (coef u : Finset (Fin N) → Ω) (J : Finset (Fin N)), (∀ h : Matrix (Fin N) (Fin N) Ω, IsBlockDiag j h → c₀ * ∑ I, coef I * minorIJ (T * h) I J = c₁ * ∑ I, u I * minorIJ h I J) → ∀ (S : Type) [CommRing S] [Algebra Ω S] (h : Matrix (Fin N) (Fin N) S), IsBlockDiag j h → algebraMap Ω S c₀ * ∑ I, algebraMap Ω S (coef I) * minorIJ (T.map (algebraMap Ω S) * h) I J = algebraMap Ω S c₁ * ∑ I, algebraMap Ω S (u I) * minorIJ h I J := by
  intro Ω _ _ N j T c₀ c₁ coef u J hyp S _ _ h hh
  have hT : T.map (algebraMap Ω Ω) = T := Matrix.ext fun _ _ => rfl
  have key : ∀ M : Matrix (Fin N) (Fin N) Ω, IsBlockDiag j M → gap T c₀ c₁ coef u J Ω M = 0 := by
    intro M hM
    simp only [gap, hT]
    exact sub_eq_zero.mpr (hyp M hM)
  let G : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) Ω) :=
    Matrix.of fun a b => if ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) then X (a, b) else 0
  have hP : gap T c₀ c₁ coef u J (MvPolynomial (Fin N × Fin N) Ω) G = 0 := by
    apply MvPolynomial.funext
    intro x
    show aeval x (gap T c₀ c₁ coef u J (MvPolynomial (Fin N × Fin N) Ω) G) = aeval x 0
    rw [map_zero, gap_map]
    apply key
    intro a b hab
    simp only [G, Matrix.map_apply, Matrix.of_apply, if_neg hab, map_zero]
  have hG : G.map (aeval (fun p : Fin N × Fin N => h p.1 p.2)).toRingHom = h := by
    ext a b
    simp only [G, Matrix.map_apply, Matrix.of_apply]
    split_ifs with hab
    · simp [aeval_X]
    · rw [map_zero]
      exact (hh a b hab).symm
  have hz := congrArg (aeval (fun p : Fin N × Fin N => h p.1 p.2)) hP
  rw [gap_map, hG, map_zero] at hz
  simp only [gap] at hz
  exact sub_eq_zero.mp hz

end GlobalTheory.CompanionTheory.Ar.PB.MinorAny
end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minor_sum_identity_base_change : ∀ (Ω : Type) [Field Ω] [Infinite Ω] (N j : ℕ) (T : Matrix (Fin N) (Fin N) Ω) (c₀ c₁ : Ω) (coef u : Finset (Fin N) → Ω) (J : Finset (Fin N)), (∀ h : Matrix (Fin N) (Fin N) Ω, IsBlockDiag j h → c₀ * ∑ I, coef I * minorIJ (T * h) I J = c₁ * ∑ I, u I * minorIJ h I J) → ∀ (S : Type) [CommRing S] [Algebra Ω S] (h : Matrix (Fin N) (Fin N) S), IsBlockDiag j h → algebraMap Ω S c₀ * ∑ I, algebraMap Ω S (coef I) * minorIJ (T.map (algebraMap Ω S) * h) I J = algebraMap Ω S c₁ * ∑ I, algebraMap Ω S (u I) * minorIJ h I J := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.MinorAny.minor_any
end

section
section
noncomputable section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.IwBlock

theorem exists_blocks_add {L : Type} [Field L] (V : ValuationSubring L) (n m : ℕ)
    (A : Matrix (Fin (n + m)) (Fin (n + m)) L)
    (hA : ∀ a b : Fin (n + m), ¬ ((a : ℕ) < n ↔ (b : ℕ) < n) → A a b = 0) (hd : A.det ≠ 0) :
    ∃ (K : Matrix (Fin (n + m)) (Fin (n + m)) V) (U : Matrix (Fin (n + m)) (Fin (n + m)) L),
      IsUnit K.det ∧ (∀ a b : Fin (n + m), ¬ ((a : ℕ) < n ↔ (b : ℕ) < n) → U a b = 0) ∧
      U.BlockTriangular id ∧ (∀ a, U a a ≠ 0) ∧ A = K.map (algebraMap V L) * U := by
  let e : Fin n ⊕ Fin m ≃ Fin (n + m) := finSumFinEquiv
  let A₁ : Matrix (Fin n) (Fin n) L := fun i k => A (e (Sum.inl i)) (e (Sum.inl k))
  let A₂ : Matrix (Fin m) (Fin m) L := fun i k => A (e (Sum.inr i)) (e (Sum.inr k))
  have lt_l : ∀ i : Fin n, ((e (Sum.inl i) : Fin (n + m)) : ℕ) < n := fun i => by simp [e]
  have ge_r : ∀ i : Fin m, ¬ ((e (Sum.inr i) : Fin (n + m)) : ℕ) < n := fun i => by simp [e]
  have val_l : ∀ i : Fin n, ((e (Sum.inl i) : Fin (n + m)) : ℕ) = i := fun i => by simp [e]
  have val_r : ∀ i : Fin m, ((e (Sum.inr i) : Fin (n + m)) : ℕ) = n + i := fun i => by simp [e]
  have hB : A.submatrix e e = fromBlocks A₁ 0 0 A₂ := by
    ext (i | i) (k | k)
    · rfl
    · exact hA _ _ fun h => ge_r k (h.1 (lt_l i))
    · exact hA _ _ fun h => ge_r i (h.2 (lt_l k))
    · rfl
  have hdet : A₁.det * A₂.det ≠ 0 := by
    rw [← det_fromBlocks_zero₂₁ A₁ 0 A₂, ← hB, det_submatrix_equiv_self]
    exact hd
  obtain ⟨k₁, U₁, hk₁, hU₁, hd₁, e₁⟩ := GlobalTheory.ValIwasawa.iwasawa_matrix (V := V) A₁ (left_ne_zero_of_mul hdet)
  obtain ⟨k₂, U₂, hk₂, hU₂, hd₂, e₂⟩ := GlobalTheory.ValIwasawa.iwasawa_matrix (V := V) A₂ (right_ne_zero_of_mul hdet)
  refine ⟨(fromBlocks k₁ 0 0 k₂).submatrix e.symm e.symm, (fromBlocks U₁ 0 0 U₂).submatrix e.symm e.symm,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁]
    exact hk₁.mul hk₂
  · intro a b h
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    rcases x with i | i <;> rcases y with k | k
    · exact absurd (iff_of_true (lt_l i) (lt_l k)) h
    · simp
    · simp
    · exact absurd (iff_of_false (ge_r i) (ge_r k)) h
  · intro a b h
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    have h' : ((e y : Fin (n + m)) : ℕ) < (e x : Fin (n + m)) := h
    rcases x with i | i <;> rcases y with k | k
    · rw [val_l, val_l] at h'
      simpa using hU₁ (show k < i from h')
    · simp
    · simp
    · rw [val_r, val_r] at h'
      simpa using hU₂ (show k < i from Nat.lt_of_add_lt_add_left h')
  · intro a
    obtain ⟨x, rfl⟩ := e.surjective a
    rcases x with i | i
    · simpa using hd₁ i
    · simpa using hd₂ i
  · have h1 : A = (fromBlocks A₁ 0 0 A₂).submatrix e.symm e.symm := by
      rw [← hB]; ext a b; simp
    have h3 : fromBlocks A₁ 0 0 A₂ =
        (fromBlocks k₁ 0 0 k₂).map (algebraMap V L) * fromBlocks U₁ 0 0 U₂ := by
      rw [fromBlocks_map, fromBlocks_multiply, ← e₁, ← e₂,
        Matrix.map_zero _ (map_zero (algebraMap V L)), Matrix.map_zero _ (map_zero (algebraMap V L))]
      simp
    rw [h1, h3, ← submatrix_mul_equiv _ _ _ e.symm _]
    rfl

theorem exists_blocks {L : Type} [Field L] (V : ValuationSubring L) (N n : ℕ) (hn : n ≤ N)
    (A : Matrix (Fin N) (Fin N) L)
    (hA : ∀ a b : Fin N, ¬ ((a : ℕ) < n ↔ (b : ℕ) < n) → A a b = 0) (hd : A.det ≠ 0) :
    ∃ (K : Matrix (Fin N) (Fin N) V) (U : Matrix (Fin N) (Fin N) L),
      IsUnit K.det ∧ (∀ a b : Fin N, ¬ ((a : ℕ) < n ↔ (b : ℕ) < n) → U a b = 0) ∧
      U.BlockTriangular id ∧ (∀ a, U a a ≠ 0) ∧ A = K.map (algebraMap V L) * U := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact exists_blocks_add V n m A hA hd

theorem inv_diag_ne_zero {L : Type} [Field L] {N : ℕ} {U : Matrix (Fin N) (Fin N) L}
    (hU : U.BlockTriangular id) (hd : IsUnit U.det) (a : Fin N) : U⁻¹ a a ≠ 0 := by
  have hI : U⁻¹.BlockTriangular id := by
    letI := Matrix.invertibleOfIsUnitDet U hd
    exact blockTriangular_inv_of_blockTriangular hU
  intro e
  have h := congrFun (congrFun (nonsing_inv_mul U hd) a) a
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single a (fun c _ hc => ?_) (by simp), e,
    zero_mul] at h
  · exact zero_ne_one h
  · rcases lt_or_gt_of_ne hc with l | l
    · rw [hI l, zero_mul]
    · rw [hU l, mul_zero]

theorem main : ∀ (L : Type) [Field L] (V : ValuationSubring L) (N j : ℕ) (A : Matrix (Fin N) (Fin N) L), IsBlockDiag j A → A.det ≠ 0 → ∃ b : Matrix (Fin N) (Fin N) L, IsBlockDiag j b ∧ b.BlockTriangular id ∧ (∀ a, b a a ≠ 0) ∧ (∀ a c, (A * b) a c ∈ V) ∧ (A * b).det ≠ 0 ∧ ((A * b).det)⁻¹ ∈ V := by
  intro L _ V N j A hA hd
  obtain ⟨K, U, hK, hUb, hUt, hUd, hAe⟩ := exists_blocks V N (N - j) (Nat.sub_le N j) A hA hd
  have hUdet : IsUnit U.det := by
    rw [det_of_upperTriangular hUt]
    exact (Finset.prod_ne_zero_iff.2 fun a _ => hUd a).isUnit
  have hAU : A * U⁻¹ = K.map (algebraMap V L) := by
    rw [hAe, Matrix.mul_nonsing_inv_cancel_right _ _ hUdet]
  have hKdet : (K.map (algebraMap V L)).det = algebraMap V L K.det := (RingHom.map_det _ K).symm
  have hUb' : IsBlockDiag j U := hUb
  refine ⟨U⁻¹, hUb'.inv hUdet, ?_, inv_diag_ne_zero hUt hUdet, fun a c => ?_, ?_, ?_⟩
  · letI := Matrix.invertibleOfIsUnitDet U hUdet
    exact blockTriangular_inv_of_blockTriangular hUt
  · rw [hAU]
    exact (K a c).2
  · rw [hAU, hKdet]
    exact (hK.map (algebraMap V L)).ne_zero
  · rw [hAU, hKdet]
    obtain ⟨u, hu⟩ := hK
    rw [← hu]
    have e : (algebraMap V L (u : V))⁻¹ = algebraMap V L ((u⁻¹ : Vˣ) : V) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← map_mul, Units.mul_inv, map_one]
    rw [e]
    exact ((u⁻¹ : Vˣ) : V).2

end GlobalTheory.CompanionTheory.Ar.PB.IwBlock
end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_diag_valuation_normalization : ∀ (L : Type) [Field L] (V : ValuationSubring L) (N j : ℕ) (A : Matrix (Fin N) (Fin N) L), IsBlockDiag j A → A.det ≠ 0 → ∃ b : Matrix (Fin N) (Fin N) L, IsBlockDiag j b ∧ b.BlockTriangular id ∧ (∀ a, b a a ≠ 0) ∧ (∀ a c, (A * b) a c ∈ V) ∧ (A * b).det ≠ 0 ∧ ((A * b).det)⁻¹ ∈ V := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.IwBlock.main
end

section
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.ComplexPlace

theorem exists_ringHom_of_finiteType {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] (v : A →+* ℂ) (hv : (RingHom.ker v).IsMaximal) (M : Ideal B)
    (hMm : M.IsMaximal) (hM : ∀ a, v a = 0 → algebraMap A B a ∈ M) :
    ∃ ψ : B →+* ℂ, ∀ a, ψ (algebraMap A B a) = v a := by
  letI κF : Field (A ⧸ RingHom.ker v) := Ideal.Quotient.field _
  letI KF : Field (B ⧸ M) := Ideal.Quotient.field _
  let φ : A ⧸ RingHom.ker v →+* B ⧸ M :=
    Ideal.quotientMap M (algebraMap A B) (fun a ha => hM a (RingHom.mem_ker.mp ha))
  letI : Algebra (A ⧸ RingHom.ker v) (B ⧸ M) := φ.toAlgebra
  haveI : IsScalarTower A (A ⧸ RingHom.ker v) (B ⧸ M) :=
    IsScalarTower.of_algebraMap_eq (fun a => rfl)
  haveI : Algebra.FiniteType A (B ⧸ M) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A M) (Ideal.Quotient.mkₐ_surjective A M)
  haveI : Algebra.FiniteType (A ⧸ RingHom.ker v) (B ⧸ M) :=
    Algebra.FiniteType.of_restrictScalars_finiteType A (A ⧸ RingHom.ker v) (B ⧸ M)
  haveI : Module.Finite (A ⧸ RingHom.ker v) (B ⧸ M) :=
    finite_of_finite_type_of_isJacobsonRing _ _
  letI : Algebra (A ⧸ RingHom.ker v) ℂ := (RingHom.kerLift v).toAlgebra
  let g : (B ⧸ M) →ₐ[A ⧸ RingHom.ker v] ℂ := IsAlgClosed.lift
  refine ⟨g.toRingHom.comp (Ideal.Quotient.mk M), fun a => ?_⟩
  exact g.commutes (Ideal.Quotient.mk (RingHom.ker v) a)

theorem isLocalRing_and_ker {L : Type} [Field L] (O : Subring L) (v : O →+* ℂ)
    (hv : ∀ s : O, v s ≠ 0 → (s : L)⁻¹ ∈ O) :
    ∃ _ : IsLocalRing O, RingHom.ker v = IsLocalRing.maximalIdeal O := by
  have hunit : ∀ s : O, IsUnit s ↔ v s ≠ 0 := by
    intro s
    constructor
    · intro h
      exact (h.map v).ne_zero
    · intro h
      have hs : (s : L) ≠ 0 := by
        intro h0
        apply h
        have : s = 0 := Subtype.ext h0
        simp [this]
      refine IsUnit.of_mul_eq_one (⟨(s : L)⁻¹, hv s h⟩ : O) ?_
      exact Subtype.ext (mul_inv_cancel₀ hs)
  have hloc : IsLocalRing O := by
    refine IsLocalRing.of_nonunits_add ?_
    intro a b ha hb
    have ha' : v a = 0 := by
      by_contra h
      exact ha ((hunit a).2 h)
    have hb' : v b = 0 := by
      by_contra h
      exact hb ((hunit b).2 h)
    intro hab
    exact (hunit _).1 hab (by simp [ha', hb'])
  refine ⟨hloc, ?_⟩
  ext s
  rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]
  simp

theorem exists_valuationSubring_place (L : Type) [Field L] (O : Subring L) (v : O →+* ℂ)
    (hv : ∀ s : O, v s ≠ 0 → (s : L)⁻¹ ∈ O) :
    ∃ V : ValuationSubring L, (∀ s ∈ O, s ∈ V) ∧ ∀ T : Finset L, (∀ t ∈ T, t ∈ V) →
      ∃ (R : Subring L) (hO : O ≤ R) (ψ : R →+* ℂ), (∀ t ∈ T, t ∈ R) ∧
        (∀ s : O, ψ (Subring.inclusion hO s) = v s) ∧ ∀ t ∈ T, t ≠ 0 → t⁻¹ ∈ V → t⁻¹ ∈ R := by
  obtain ⟨hloc, hker⟩ := isLocalRing_and_ker O v hv
  obtain ⟨V, hV, hlocal⟩ := IsLocalRing.exists_factor_valuationRing O.subtype
  refine ⟨V, fun s hs => hV ⟨s, hs⟩, fun T hT => ?_⟩
  let S : Finset L := T ∪ (T.filter (fun t => t⁻¹ ∈ V)).image (fun t => t⁻¹)
  have hSV : ∀ x ∈ S, x ∈ V := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact hT x h
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp ht).2
  let B : Subalgebra O L := Algebra.adjoin O (S : Set L)
  let VA : Subalgebra O L :=
    { V.toSubring with algebraMap_mem' := fun s => hV s }
  have hBV : B ≤ VA := Algebra.adjoin_le (fun x hx => hSV x hx)
  haveI : Algebra.FiniteType O B :=
    (Subalgebra.fg_iff_finiteType B).1 (Subalgebra.fg_adjoin_finset S)
  let f : B →+* V :=
    { toFun := fun x => ⟨x.1, hBV x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let n : Ideal B := (IsLocalRing.maximalIdeal V).comap f
  have hn : n ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ n := h ▸ Submodule.mem_top
    have h2 : f 1 ∈ IsLocalRing.maximalIdeal V := h1
    rw [map_one] at h2
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal V).ne_top h2
  obtain ⟨M, hMm, hnM⟩ := Ideal.exists_le_maximal n hn
  have hM : ∀ a : O, v a = 0 → algebraMap O B a ∈ M := by
    intro a ha
    apply hnM
    have ha' : a ∈ IsLocalRing.maximalIdeal O := hker ▸ RingHom.mem_ker.mpr ha
    show f (algebraMap O B a) ∈ IsLocalRing.maximalIdeal V
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha' ⊢
    intro hu
    apply ha'
    exact hlocal.map_nonunit a hu
  have hvm : (RingHom.ker v).IsMaximal := by
    rw [hker]
    exact IsLocalRing.maximalIdeal.isMaximal O
  obtain ⟨ψ, hψ⟩ := exists_ringHom_of_finiteType v hvm M hMm hM
  have hO : O ≤ B.toSubring := fun s hs => B.algebraMap_mem (⟨s, hs⟩ : O)
  refine ⟨B.toSubring, hO, ψ, ?_, ?_, ?_⟩
  · intro t ht
    exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_union_left _ ht))
  · intro s
    exact hψ s
  · intro t ht _ hi
    exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨t, Finset.mem_filter.2 ⟨ht, hi⟩, rfl⟩)))

end GlobalTheory.CompanionTheory.Ar.ComplexPlace
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_ring_extension_specialization : ∀ (L : Type) [Field L] (O : Subring L) (v : O →+* ℂ), (∀ s : O, v s ≠ 0 → (s : L)⁻¹ ∈ O) → ∃ V : ValuationSubring L, (∀ s ∈ O, s ∈ V) ∧ ∀ T : Finset L, (∀ t ∈ T, t ∈ V) → ∃ (R : Subring L) (hO : O ≤ R) (ψ : R →+* ℂ), (∀ t ∈ T, t ∈ R) ∧ (∀ s : O, ψ (Subring.inclusion hO s) = v s) ∧ ∀ t ∈ T, t ≠ 0 → t⁻¹ ∈ V → t⁻¹ ∈ R := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.ComplexPlace.exists_valuationSubring_place
end

section
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.UnitComb

theorem coe_minorIJ {L : Type} [Field L] (V : ValuationSubring L) {N : ℕ}
    (h : Matrix (Fin N) (Fin N) V) (I J : Finset (Fin N)) :
    ((minorIJ h I J : V) : L) = minorIJ (h.map V.subtype) I J := by
  unfold minorIJ
  split_ifs with e
  · exact RingHom.map_det V.subtype _
  · rfl

theorem minorIJ_one_diag {R : Type} [CommRing R] {N : ℕ} (J : Finset (Fin N)) :
    minorIJ (1 : Matrix (Fin N) (Fin N) R) J J = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.submatrix_one _ (J.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem exists_isUnit_of_sum {R : Type} [CommRing R] [IsLocalRing R] {ι : Type} (s : Finset ι)
    (f : ι → R) (h : IsUnit (∑ a ∈ s, f a)) : ∃ a ∈ s, IsUnit (f a) := by
  by_contra hc
  push_neg at hc
  have : ∑ a ∈ s, f a ∈ IsLocalRing.maximalIdeal R :=
    Ideal.sum_mem _ fun a ha => (IsLocalRing.mem_maximalIdeal _).2 (hc a ha)
  exact (IsLocalRing.mem_maximalIdeal _).1 this h

theorem stepCols_ne_empty {N j : ℕ} (i : Fin N) (hj : j ≤ N) : stepCols N j i ≠ ∅ := by
  have hi := i.2
  by_cases c : (i : ℕ) + 1 ≤ j
  · refine Finset.Nonempty.ne_empty ⟨⟨N - j, by omega⟩, ?_⟩
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos c]
    omega
  · refine Finset.Nonempty.ne_empty ⟨⟨0, by omega⟩, ?_⟩
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg c]
    omega

theorem unit_comb : ∀ (L : Type) [Field L] (V : ValuationSubring L) (N j : ℕ) (i : Fin N) (H : Matrix (Fin N) (Fin N) L) (κ : Type) [Fintype κ] (u : κ → Finset (Fin N) → L) (u' : Finset (Fin N) → κ → L), j ≤ N → IsBlockDiag j H → (∀ a b, H a b ∈ V) → H.det ≠ 0 → (H.det)⁻¹ ∈ V → (∀ I m, u' I m ∈ V) → (∀ m I, u m I ∈ V) → (∀ I I', IsStepRows N j i I → IsStepRows N j i I' → ∑ m, u' I m * u m I' = if I = I' then 1 else 0) → ∃ m, (∑ I, u m I * minorIJ H I (stepCols N j i)) ≠ 0 ∧ (∑ I, u m I * minorIJ H I (stepCols N j i))⁻¹ ∈ V := by
  intro L _ V N j i H κ _ u u' hj hB hH hdet hinv hu' hu horth
  let Hv : Matrix (Fin N) (Fin N) V := Matrix.of fun a b => ⟨H a b, hH a b⟩
  have hHv : Hv.map V.subtype = H := by ext a b; rfl
  let uv : κ → Finset (Fin N) → V := fun m I => ⟨u m I, hu m I⟩
  let uv' : Finset (Fin N) → κ → V := fun I m => ⟨u' I m, hu' I m⟩
  have hdetc : ((Hv.det : V) : L) = H.det := by
    have := RingHom.map_det V.subtype Hv
    rw [RingHom.mapMatrix_apply, hHv] at this
    exact this
  have hunit : IsUnit Hv.det := by
    refine IsUnit.of_mul_eq_one (⟨(H.det)⁻¹, hinv⟩ : V) ?_
    apply Subtype.ext
    change ((Hv.det : V) : L) * (H.det)⁻¹ = 1
    rw [hdetc, mul_inv_cancel₀ hdet]
  have main := GlobalTheory.T.block_diagonal_minor_vanishing V N j i hj
  have hJ := stepCols_ne_empty (j := j) i hj
  have hBv : IsBlockDiag j Hv := fun a b hab => Subtype.ext (hB a b hab)
  have hstep : ∀ I, ¬ IsStepRows N j i I → minorIJ Hv I (stepCols N j i) = 0 := fun I hI =>
    (main.2.1 Hv I hBv hI).resolve_right hJ
  have hsum1 : IsUnit (∑ I', minorIJ Hv⁻¹ (stepCols N j i) I' * minorIJ Hv I' (stepCols N j i)) := by
    rw [← main.1, Matrix.nonsing_inv_mul _ hunit, minorIJ_one_diag]
    exact isUnit_one
  obtain ⟨I₀, -, hI₀⟩ := exists_isUnit_of_sum _ _ hsum1
  have hI₀' : IsUnit (minorIJ Hv I₀ (stepCols N j i)) := isUnit_of_mul_isUnit_right hI₀
  have hI₀s : IsStepRows N j i I₀ := by
    by_contra hc
    rw [hstep I₀ hc] at hI₀'
    exact not_isUnit_zero hI₀'
  have horthV : ∀ I', IsStepRows N j i I' → ∑ m, uv' I₀ m * uv m I' = if I₀ = I' then 1 else 0 := by
    intro I' hI'
    apply Subtype.ext
    have := horth I₀ I' hI₀s hI'
    split_ifs at this ⊢ with e
    · simpa [uv, uv'] using this
    · simpa [uv, uv'] using this
  let w : κ → V := fun m => ∑ I, uv m I * minorIJ Hv I (stepCols N j i)
  have hw : ∑ m, uv' I₀ m * w m = minorIJ Hv I₀ (stepCols N j i) := by
    have e1 : ∑ m, uv' I₀ m * w m =
        ∑ I, (∑ m, uv' I₀ m * uv m I) * minorIJ Hv I (stepCols N j i) := by
      simp only [w, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [mul_assoc]
    rw [e1, Finset.sum_eq_single I₀]
    · rw [horthV I₀ hI₀s, if_pos rfl, one_mul]
    · intro b _ hb
      by_cases hs : IsStepRows N j i b
      · rw [horthV b hs, if_neg (Ne.symm hb), zero_mul]
      · rw [hstep b hs, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [← hw] at hI₀'
  obtain ⟨m, -, hm⟩ := exists_isUnit_of_sum _ _ hI₀'
  have hwm : IsUnit (w m) := isUnit_of_mul_isUnit_right hm
  have hcoe : ((w m : V) : L) = ∑ I, u m I * minorIJ H I (stepCols N j i) := by
    simp only [w, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, coe_minorIJ, hHv]
    rfl
  refine ⟨m, ?_, ?_⟩
  · rw [← hcoe]
    intro h0
    exact hwm.ne_zero (Subtype.ext h0)
  · obtain ⟨c, hc⟩ := hwm.exists_right_inv
    have hc' : ((w m : V) : L) * (c : L) = 1 := congrArg Subtype.val hc
    rw [← hcoe, inv_eq_of_mul_eq_one_right hc']
    exact c.2

end GlobalTheory.CompanionTheory.Ar.PB.UnitComb
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_rows_inverse_nonzero_entry : ∀ (L : Type) [Field L] (V : ValuationSubring L) (N j : ℕ) (i : Fin N) (H : Matrix (Fin N) (Fin N) L) (κ : Type) [Fintype κ] (u : κ → Finset (Fin N) → L) (u' : Finset (Fin N) → κ → L), j ≤ N → IsBlockDiag j H → (∀ a b, H a b ∈ V) → H.det ≠ 0 → (H.det)⁻¹ ∈ V → (∀ I m, u' I m ∈ V) → (∀ m I, u m I ∈ V) → (∀ I I', IsStepRows N j i I → IsStepRows N j i I' → ∑ m, u' I m * u m I' = if I = I' then 1 else 0) → ∃ m, (∑ I, u m I * minorIJ H I (stepCols N j i)) ≠ 0 ∧ (∑ I, u m I * minorIJ H I (stepCols N j i))⁻¹ ∈ V := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.UnitComb.unit_comb
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_flag_algebraically_independent : ∀ (Ω Φ : Type) [Field Ω] [Field Φ] [Algebra Ω Φ] (Ψ : Type) (N j : ℕ) (g : Ψ → Matrix (Fin N) (Fin N) Φ) (T : Ψ → Matrix (Fin N) (Fin N) Ω), (∀ τ, IsBlockDiag j (g τ)) → IsGenericFlag Ω j g → (∀ τ, IsBlockDiag j (T τ) ∧ (T τ).det ≠ 0) → AlgebraicIndependent Ω (fun q : inertBlockIndex Ψ N j => (((T q.1.1)⁻¹.map (algebraMap Ω (MvPolynomial (UpIdx Ψ N j) Φ))) * ((g q.1.1).map (C : Φ →+* MvPolynomial (UpIdx Ψ N j) Φ) * genUp Φ N j q.1.1)) q.1.2.1 q.1.2.2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag.indep_twist_mul_genUp | exact GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag.indep_twist_mul_genUp | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag.indep_twist_mul_genUp <;> assumption)
end

section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CPts

open GlobalTheory.CompanionTheory.Ar.PB.ValRing

section Forms

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem sum_mapDomain_block {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hv : ∀ p, (v p).1 = κ p.1)
    (m : (Σ k, ι k) →₀ ℕ) (k' : K') :
    ∑ i, (Finsupp.mapDomain v m) ⟨k', i⟩ = ∑ p : Σ k, ι k, if κ p.1 = k' then m p else 0 := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add]
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf, hg]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  | single p n =>
    have hR : (∑ q : Σ k, ι k, if κ q.1 = k' then (Finsupp.single p n) q else 0) =
        if κ p.1 = k' then n else 0 := by
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hq
        simp [Finsupp.single_apply, Ne.symm hq]
      · simp
    have hL : ∀ q : Σ k, ι' k, ∑ i, (Finsupp.single q n) ⟨k', i⟩ = if q.1 = k' then n else 0 := by
      rintro ⟨kq, iq⟩
      by_cases h : kq = k'
      · subst h
        simp [Finsupp.single_apply]
      · simp [Finsupp.single_apply, h]
    rw [Finsupp.mapDomain_single, hL, hR, hv]

theorem isMultiHomog_rename_block {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hb : IsBlockMap κ v) {f : MRing ι}
    {b : K → ℕ} (hf : IsMultiHomog f b) : IsMultiHomog (rename v f) (Function.extend κ b 0) := by
  intro m hm k'
  rw [support_rename_of_injective hb.2.1, Finset.mem_image] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  rw [sum_mapDomain_block hb.2.2.1, Fintype.sum_sigma]
  by_cases hk : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := hk
    rw [hb.1.extend_apply, Finset.sum_eq_single k]
    · simpa using hf m₀ hm₀ k
    · intro k₂ _ hne
      exact Finset.sum_eq_zero fun i _ => if_neg (hb.1.ne hne)
    · simp
  · rw [Function.extend_apply' _ _ _ hk]
    exact Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun i _ => if_neg fun h => hk ⟨k, h⟩

theorem mConeMap_rename {Ω : Type} [Field Ω] {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hb : IsBlockMap κ v)
    (y : (Σ k, ι' k) → Ω) (g : MRing ι) : mConeMap y (rename v g) = rename κ (mConeMap (y ∘ v) g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMap, hb.2.2.1 n]

theorem mConeMap_comp {Ω Ω' : Type} [Field Ω] [Field Ω'] (φ : Ω →+* Ω') (x : (Σ k, ι k) → Ω) (g : MRing ι) :
    mConeMap (φ ∘ x) g = map φ (mConeMap x g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp]
    congr 1
    simp [mConeMap]

theorem aeval_comp_ringHom {Ω Ω' : Type} [Field Ω] [Field Ω'] (φ : Ω →+* Ω') (x : (Σ k, ι k) → Ω) (g : MRing ι) :
    aeval (φ ∘ x) g = φ (aeval x g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, aeval_X, Function.comp]

theorem eval_rename_block (v : (Σ k, ι k) → Σ k, ι' k) (z : (Σ k, ι' k) → ℂ) (f : MRing ι) :
    eval z (map (Int.castRingHom ℂ) (rename v f)) = eval (z ∘ v) (map (Int.castRingHom ℂ) f) := by
  rw [map_rename, eval_rename]

theorem rename_notMem {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hb : IsBlockMap κ v)
    {z : (Σ k, ι' k) → ℂ} {h : MRing ι} (hn : h ∉ mCoordIdeal (z ∘ v)) : rename v h ∉ mCoordIdeal z := by
  intro hm
  have h0 : mConeMap z (rename v h) = 0 := hm
  rw [mConeMap_rename hb] at h0
  exact hn ((rename_injective κ hb.1) (by rw [h0, map_zero]))

theorem comp_mem_mcPts {Ω Ω' : Type} [Field Ω] [Field Ω'] {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k}
    (hb : IsBlockMap κ v) (φ : Ω →+* Ω') {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'} (hx : x' ∘ v = φ ∘ x)
    {z : (Σ k, ι' k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x')) : z ∘ v ∈ mcPts (mCoordIdeal x) := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i', hi'⟩ := hz.1 (κ k)
    obtain ⟨⟨k₂, i⟩, hp⟩ := hb.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
    have hk : k₂ = k := hb.1 (by simpa [hp] using (hb.2.2.1 ⟨k₂, i⟩).symm)
    subst hk
    exact ⟨i, by simpa [Function.comp, hp] using hi'⟩
  · have h0 : mConeMap x f = 0 := hf
    have h1 : rename v f ∈ mCoordIdeal x' := by
      show mConeMap x' (rename v f) = 0
      rw [mConeMap_rename hb, hx, mConeMap_comp, h0, map_zero, map_zero]
    rw [← eval_rename_block]
    exact hz.2 _ h1

end Forms

section Reg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def regRing (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : Subring Ω where
  carrier := {s | ∃ v, IsValueAt y s z v}
  mul_mem' := fun ⟨v, hv⟩ ⟨w, hw⟩ => ⟨v * w, isValueAt_mul hv hw⟩
  one_mem' := ⟨1, isValueAt_one_self y z⟩
  add_mem' := fun ⟨v, hv⟩ ⟨w, hw⟩ => ⟨v + w, GroundTheory.Heights₂.Heights.LowerBoundFree.isValueAt_add hv hw⟩
  zero_mem' := ⟨0, isValueAt_zero_self y z⟩
  neg_mem' := fun {s} ⟨v, hv⟩ => ⟨(-1 : ℤ) * v, by
    have := isValueAt_mul (isValueAt_intCast y z (-1)) hv
    simpa using this⟩

def regVal {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) : regRing y z →+* ℂ where
  toFun s := valAt y s z
  map_one' := valAt_eq hz (isValueAt_one_self y z)
  map_zero' := valAt_eq hz (isValueAt_zero_self y z)
  map_mul' := fun ⟨s, v, hv⟩ ⟨t, w, hw⟩ => by
    show valAt y (s * t) z = valAt y s z * valAt y t z
    rw [valAt_eq hz hv, valAt_eq hz hw, valAt_eq hz (isValueAt_mul hv hw)]
  map_add' := fun ⟨s, v, hv⟩ ⟨t, w, hw⟩ => by
    show valAt y (s + t) z = valAt y s z + valAt y t z
    rw [valAt_eq hz hv, valAt_eq hz hw, valAt_eq hz (GroundTheory.Heights₂.Heights.LowerBoundFree.isValueAt_add hv hw)]

theorem regVal_apply {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (s : regRing y z) :
    regVal hz s = valAt y s z := rfl

theorem regVal_eq {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (s : regRing y z)
    {v : ℂ} (hv : IsValueAt y s z v) : regVal hz s = v := valAt_eq hz hv

theorem regVal_local {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (s : regRing y z)
    (h : regVal hz s ≠ 0) : (s : Ω)⁻¹ ∈ regRing y z := by
  obtain ⟨s, v, hv⟩ := s
  have e : regVal hz ⟨s, v, hv⟩ = v := regVal_eq hz _ hv
  rw [e] at h
  have hs : s ≠ 0 := fun h0 => h (isValueAt_zero hz (h0 ▸ hv))
  exact ⟨v⁻¹, isValueAt_inv hv hs h⟩

theorem isValueAt_ratio {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} {k : K} {m c : ι k}
    (hy : y ⟨k, c⟩ ≠ 0) (hz : z ⟨k, c⟩ ≠ 0) : IsValueAt y (y ⟨k, m⟩ / y ⟨k, c⟩) z (z ⟨k, m⟩ / z ⟨k, c⟩) := by
  refine ⟨_, X ⟨k, m⟩, X ⟨k, c⟩, isMultiHomog_X_single _, isMultiHomog_X_single _, by simpa using hy, ?_,
    by simpa using hz, by simp⟩
  rw [aeval_X, aeval_X, div_mul_cancel₀ _ hy]

theorem coord_ne {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) {q : Σ k, ι k}
    (h : z q ≠ 0) : y q ≠ 0 := fun h0 => h (by
  have := eval_eq_zero_of_mem_mcPts hz
    (mem_mCoordIdeal_of_aeval_eq_zero y (isMultiHomog_X_single (ι := ι) q) (by simpa using h0))
  simpa using this)

theorem mCoordIdeal_le {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) :
    mCoordIdeal x ≤ mCoordIdeal z := by
  obtain ⟨T, hT, hE⟩ := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal x
  refine hE.le.trans (Ideal.span_le.2 fun g hg => ?_)
  obtain ⟨d, hd⟩ := hT g hg
  refine mem_mCoordIdeal_of_aeval_eq_zero z hd ?_
  have := eval_eq_zero_of_mem_mcPts hz (hE ▸ Ideal.subset_span hg : g ∈ mCoordIdeal x)
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map]
  simpa using this

theorem mem_mcPts_of_ringHom {L R : Type} [Field L] [CommRing R] (i : R →+* L) (hi : Function.Injective i)
    (ρ : R →+* ℂ) (a : (Σ k, ι k) → L) (s : (Σ k, ι k) → R) (e : K → L) (t : K → ℂ) (zt : (Σ k, ι k) → ℂ)
    (hzt : ∀ k, ∃ i, zt ⟨k, i⟩ ≠ 0) (he : ∀ k, e k ≠ 0) (ht : ∀ k, t k ≠ 0) (has : ∀ q, a q = e q.1 * i (s q))
    (hv : ∀ q, ρ (s q) = t q.1 * zt q) : zt ∈ mcPts (mCoordIdeal a) := by
  refine ⟨hzt, fun f hf => ?_⟩
  obtain ⟨T, hT, hE⟩ := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal a
  rw [hE] at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨d, hd⟩ := hT g hg
    have h0 : aeval a g = 0 :=
      (GlobalTheory.CompanionTheory.Ar.PB.form_mem_mCoordIdeal_iff a hd).1 (by rw [hE]; exact Ideal.subset_span hg)
    have ha : a = fun p => e p.1 * i (s p) := funext has
    have h1 : aeval (fun p => i (s p)) g = 0 := by
      have h := GroundTheory.Heights₂.Heights.Inter.ChartNormPts.aeval_smul_homog g d hd e fun p => i (s p)
      rw [← ha, h0] at h
      have hne : (∏ k, e k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (he k)
      exact (mul_eq_zero.1 h.symm).resolve_left hne
    have comp : ∀ {R' R'' : Type} [CommRing R'] [CommRing R''] (φ : R' →+* R'') (w : (Σ k, ι k) → R') (f : MRing ι),
        aeval (fun p => φ (w p)) f = φ (aeval w f) := by
      intro R' R'' _ _ φ w f
      induction f using MvPolynomial.induction_on with
      | C a => simp
      | add p q hp hq => simp only [map_add, hp, hq]
      | mul_X p n hp => simp only [map_mul, hp, aeval_X]
    have h2 : aeval s g = 0 := hi (by rw [← comp, h1, map_zero])
    have h3 : eval (fun p => t p.1 * zt p) (map (Int.castRingHom ℂ) g) = 0 := by
      have : aeval (fun p => ρ (s p)) g = 0 := by rw [comp, h2, map_zero]
      rw [funext hv, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map] at this
      simpa using this
    rw [ReciprocityTheory.ChartRestriction.G.Geo.eval_smul_homog g d hd t zt] at h3
    have hne : (∏ k, t k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ht k)
    exact (mul_eq_zero.1 h3).resolve_left hne
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul r x _ hx => simp [smul_eq_mul, map_mul, hx]

end Reg

section Mat

variable {R S : Type} [CommRing R] [CommRing S] {N : ℕ}

theorem minorIJ_map (f : R →+* S) (A : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) :
    minorIJ (A.map f) I J = f (minorIJ A I J) := by
  unfold minorIJ
  split_ifs with e
  · rw [RingHom.map_det]; rfl
  · rw [map_zero]

theorem minorIJ_mem {L : Type} [Field L] (P : Subring L) {A : Matrix (Fin N) (Fin N) L} (hA : ∀ a b, A a b ∈ P)
    (I J : Finset (Fin N)) : minorIJ A I J ∈ P := by
  have e : A = (Matrix.of fun a b => (⟨A a b, hA a b⟩ : P)).map P.subtype := by ext a b; rfl
  rw [e, minorIJ_map]
  exact Subtype.coe_prop _

theorem det_mem {L : Type} [Field L] (P : Subring L) {A : Matrix (Fin N) (Fin N) L} (hA : ∀ a b, A a b ∈ P) :
    A.det ∈ P := by
  have e : A = (Matrix.of fun a b => (⟨A a b, hA a b⟩ : P)).map P.subtype := by ext a b; rfl
  rw [e, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact Subtype.coe_prop _

theorem minorIJ_one (I : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) R) I I = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.submatrix_one _ (I.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem detFac_one (j : ℕ) (i : Fin N) : detFac j i (1 : Matrix (Fin N) (Fin N) R) = 1 := by
  simp only [detFac, minorIJ_one]
  simp

theorem stepCols_nonempty {j : ℕ} (hj : j ≤ N) (i : Fin N) : (stepCols N j i).Nonempty := by
  by_cases h : (i : ℕ) + 1 ≤ j
  · refine ⟨⟨N - j, by omega⟩, ?_⟩
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h]
    omega
  · refine ⟨⟨0, by have := i.2; omega⟩, ?_⟩
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h]
    omega

theorem detFac_ne_zero {L : Type} [Field L] {j : ℕ} (hj : j ≤ N) (i : Fin N) {T : Matrix (Fin N) (Fin N) L}
    (hT : IsBlockDiag j T) (hd : T.det ≠ 0) : detFac j i T ≠ 0 := by
  have hu : IsUnit T.det := hd.isUnit
  have h := ((GlobalTheory.T.block_diagonal_minor_vanishing L N j i hj).2.2.2 T T⁻¹ hT (hT.inv hu)).2
  rw [Matrix.mul_nonsing_inv _ hu, detFac_one] at h
  exact left_ne_zero_of_mul_eq_one h.symm

theorem map_mul_inv_map {L : Type} [Field L] (f : L →+* S) {T : Matrix (Fin N) (Fin N) L} (hd : T.det ≠ 0)
    (X : Matrix (Fin N) (Fin N) S) : T.map f * (T⁻¹.map f * X) = X := by
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hd.isUnit, Matrix.map_one _ (map_zero f) (map_one f),
    Matrix.one_mul]

end Mat

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (M : FlagModel y Ψ N j)

include M in

theorem blockMap_base : IsBlockMap (ι := baseIdx ι M.blk) (ι' := ι) (Subtype.val : NonPluckerBlocks M.blk → K)
    (fun q => (⟨q.1.1, q.2⟩ : Σ k, ι k)) := by
  refine ⟨Subtype.val_injective, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨⟨k, hk⟩, i⟩ ⟨⟨k', hk'⟩, i'⟩ h
    simp only [Sigma.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [heq_eq_eq] at h
    subst h
    rfl
  · rintro ⟨k, i⟩ ⟨kb, rfl⟩
    exact ⟨⟨kb, i⟩, rfl⟩

theorem base_mem {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    basePart M.blk z ∈ mcPts (mCoordIdeal M.x) :=
  comp_mem_mcPts (blockMap_base M) (algebraMap M.Ω Φ) (funext M.y_base) hz

theorem val_lift {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) {s : M.Ω}
    (hs : RegAt M.x (mCoordIdeal (basePart M.blk z)) s) :
    IsValueAt y (algebraMap M.Ω Φ s) z (valAt M.x s (basePart M.blk z)) := by
  have hb := blockMap_base M
  have hzb := base_mem M hz
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  have hg' := isMultiHomog_rename_block hb hg
  have hh' := isMultiHomog_rename_block hb hh
  have hn' : rename _ h ∉ mCoordIdeal z := rename_notMem hb hn
  have hy : y ∘ (fun q : Σ k, baseIdx ι M.blk k => (⟨q.1.1, q.2⟩ : Σ k, ι k)) = (algebraMap M.Ω Φ) ∘ M.x :=
    funext M.y_base
  have heq' : aeval y (rename (fun q : Σ k, baseIdx ι M.blk k => (⟨q.1.1, q.2⟩ : Σ k, ι k)) g) =
      algebraMap M.Ω Φ s * aeval y (rename (fun q : Σ k, baseIdx ι M.blk k => (⟨q.1.1, q.2⟩ : Σ k, ι k)) h) := by
    rw [aeval_rename, aeval_rename, hy, aeval_comp_ringHom, aeval_comp_ringHom, heq, map_mul]
  have v1 : IsValueAt M.x s (basePart M.blk z) _ :=
    ⟨d, g, h, hg, hh, aeval_ne_zero_of_notMem hzb hh hn, heq, eval_ne_zero_of_notMem hh hn, rfl⟩
  have v2 : IsValueAt y (algebraMap M.Ω Φ s) z _ :=
    ⟨_, _, _, hg', hh', aeval_ne_zero_of_notMem hz hh' hn', heq', eval_ne_zero_of_notMem hh' hn', rfl⟩
  rw [valAt_eq hzb v1, eval_rename_block, eval_rename_block] at *
  exact v2

theorem frame_gen {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {S : Type} [CommRing S] (f : Φ →+* S)
    {p : Ψ × Fin N} {k : K} (hp : M.blk p = some k) (m : ι k) {G bb : Matrix (Fin N) (Fin N) S}
    (hG : IsBlockDiag j G) (hbb : IsBlockDiag j bb) (hbt : bb.BlockTriangular id)
    (e : (F.T p.1).map (f.comp (algebraMap M.Ω Φ)) * G = (M.g p.1).map f * bb) :
    f (algebraMap M.Ω Φ (detFac j p.2 (F.T p.1))) * (∏ c ∈ stepCols N j p.2, bb c c) * f (y ⟨k, m⟩) =
      f (algebraMap M.Ω Φ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k')) *
        ∑ I, f (algebraMap M.Ω Φ (F.u ⟨k, m⟩ I)) * minorIJ G I (stepCols N j p.2) := by
  haveI : Infinite M.Ω := Infinite.of_injective (Nat.cast : ℕ → M.Ω) Nat.cast_injective
  letI : Algebra M.Ω S := (f.comp (algebraMap M.Ω Φ)).toAlgebra
  have h1 := GlobalTheory.T.minor_sum_identity_base_change M.Ω N j (F.T p.1) _ _ (M.coef ⟨k, m⟩) (F.u ⟨k, m⟩) (stepCols N j p.2)
    (hF.2.1 p k hp m) S G hG
  have e' : (F.T p.1).map (algebraMap M.Ω S) * G = (M.g p.1).map f * bb := e
  rw [e'] at h1
  have h2 : ∀ I, minorIJ ((M.g p.1).map f * bb) I (stepCols N j p.2) =
      f (minorIJ (M.g p.1) I (stepCols N j p.2)) * ∏ c ∈ stepCols N j p.2, bb c c := fun I => by
    rw [(GlobalTheory.T.block_diagonal_minor_vanishing S N j p.2 M.j_le).2.2.1 _ bb I hbb hbt, minorIJ_map]
  simp only [h2] at h1
  have h3 : f (y ⟨k, m⟩) = ∑ I, algebraMap M.Ω S (M.coef ⟨k, m⟩ I) * f (minorIJ (M.g p.1) I (stepCols N j p.2)) := by
    rw [M.y_step p k hp m, map_sum]
    exact Finset.sum_congr rfl fun I _ => by rw [map_mul]; rfl
  have ha : algebraMap M.Ω S (detFac j p.2 (F.T p.1)) = f (algebraMap M.Ω Φ (detFac j p.2 (F.T p.1))) := rfl
  rw [h3, Finset.mul_sum]
  refine Eq.trans ?_ h1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [ha]
  ring

end Flag

section Back

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (M : FlagModel y Ψ N j)

theorem flag_nonzero {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {z : (Σ k, ι k) → ℂ}
    (hzb : basePart M.blk z ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal (basePart M.blk z)))
    {h : Ψ → Matrix (Fin N) (Fin N) ℂ} (H : M.IsFlagOf F z h) (k : K) : ∃ i, z ⟨k, i⟩ ≠ 0 := by
  by_cases hk : ∀ p, M.blk p ≠ some k
  · obtain ⟨i, hi⟩ := hzb.1 ⟨k, hk⟩
    exact ⟨i, hi⟩
  · push_neg at hk
    obtain ⟨p, hp⟩ := hk
    obtain ⟨a, ha, hz⟩ := H.2.2 p k hp
    let val := regVal hzb
    let uA : (Σ k, ι k) → Finset (Fin N) → regRing M.x (basePart M.blk z) :=
      fun q I => ⟨F.u q I, exists_isValueAt hzb (hG.2.1 q I).1⟩
    let vA : Finset (Fin N) → (Σ k, ι k) → regRing M.x (basePart M.blk z) :=
      fun I q => ⟨F.u' I q, exists_isValueAt hzb (hG.2.1 q I).2⟩
    have rel : ∀ I I', IsStepRows N j p.2 I → IsStepRows N j p.2 I' →
        ∑ m : ι k, val (vA I ⟨k, m⟩) * val (uA ⟨k, m⟩ I') = if I = I' then 1 else 0 := fun I I' hI hI' => by
      have e : ∑ m : ι k, vA I ⟨k, m⟩ * uA ⟨k, m⟩ I' = if I = I' then 1 else 0 := by
        apply Subtype.ext
        have := hF.2.2.1 p k hp I I' hI hI'
        split_ifs at this ⊢ <;> simpa [uA, vA] using this
      have e' := congrArg val e
      rw [map_sum] at e'
      simp only [map_mul] at e'
      rw [e']
      split_ifs <;> simp
    obtain ⟨m, hm, -⟩ := GlobalTheory.T.step_rows_inverse_nonzero_entry ℂ ⊤ N j p.2 (h p.1) (ι k) (fun m I => val (uA ⟨k, m⟩ I))
      (fun I m => val (vA I ⟨k, m⟩)) M.j_le (H.2.1 p.1).1 (fun _ _ => ValuationSubring.mem_top _) (H.2.1 p.1).2
      (ValuationSubring.mem_top _) (fun _ _ => ValuationSubring.mem_top _) (fun _ _ => ValuationSubring.mem_top _) rel
    refine ⟨m, ?_⟩
    rw [hz m]
    exact mul_ne_zero ha hm

theorem flag_back {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {z : (Σ k, ι k) → ℂ}
    (hzb : basePart M.blk z ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal (basePart M.blk z)))
    {h : Ψ → Matrix (Fin N) (Fin N) ℂ} (H : M.IsFlagOf F z h) : z ∈ mcPts (mCoordIdeal y) := by
  have hnz := flag_nonzero M hF hzb hG H
  let A := regRing M.x (basePart M.blk z)
  let val : A →+* ℂ := regVal hzb
  let S := MvPolynomial (UpIdx Ψ N j) Φ
  let L := FractionRing S
  let G' : Ψ → Matrix (Fin N) (Fin N) S := fun τ =>
    ((F.T τ)⁻¹.map (algebraMap M.Ω S)) * ((M.g τ).map (C : Φ →+* S) * genUp Φ N j τ)
  have indep := GlobalTheory.T.generic_flag_algebraically_independent M.Ω Φ Ψ N j M.g F.T M.g_block M.g_indep hF.1
  let iS : MvPolynomial (inertBlockIndex Ψ N j) A →+* S :=
    eval₂Hom ((algebraMap M.Ω S).comp A.subtype) fun q => G' q.1.1 q.1.2.1 q.1.2.2
  have eS : ∀ r, iS r = aeval (fun q : inertBlockIndex Ψ N j => G' q.1.1 q.1.2.1 q.1.2.2) (MvPolynomial.map A.subtype r) := by
    intro r
    induction r using MvPolynomial.induction_on with
    | C a => simp [iS]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p n hp => simp only [map_mul, hp, map_X, aeval_X]; simp [iS]
  have hiS : Function.Injective iS := fun a b e => by
    refine MvPolynomial.map_injective A.subtype Subtype.val_injective
      ((algebraicIndependent_iff_injective_aeval.1 indep) ?_)
    rw [← eS, ← eS, e]
  let i : MvPolynomial (inertBlockIndex Ψ N j) A →+* L := (algebraMap S L).comp iS
  have hi : Function.Injective i := (IsFractionRing.injective S L).comp hiS
  let ρ : MvPolynomial (inertBlockIndex Ψ N j) A →+* ℂ := eval₂Hom val fun q => h q.1.1 q.1.2.1 q.1.2.2
  have hGb : ∀ τ, IsBlockDiag j (G' τ) := fun τ =>
    ((((hF.1 τ).1.inv (hF.1 τ).2.isUnit)).map _).mul (((M.g_block τ).map _).mul (genUp_blockDiag τ))
  have hiG : ∀ τ, (genericBlockMatrix A N j τ).map iS = G' τ := generic_block_matrix_map iS hGb fun q => by simp [iS]
  have hρ : ∀ τ, (genericBlockMatrix A N j τ).map ρ = h τ := generic_block_matrix_map ρ (fun τ => (H.2.1 τ).1) fun q => by simp [ρ]
  let φL : Φ →+* L := (algebraMap S L).comp (C : Φ →+* S)
  have hiC : ∀ a : A, i (C a) = φL (algebraMap M.Ω Φ a) := fun a => by
    show algebraMap S L (iS (C a)) = algebraMap S L (C (algebraMap M.Ω Φ a))
    congr 1
    exact (eval₂Hom_C _ _ _).trans (MvPolynomial.algebraMap_apply ..)
  have key : ∀ k, ∃ (e : L) (t : ℂ) (sv : ι k → MvPolynomial (inertBlockIndex Ψ N j) A), e ≠ 0 ∧ t ≠ 0 ∧
      (∀ m, φL (y ⟨k, m⟩) = e * i (sv m)) ∧ ∀ m, ρ (sv m) = t * z ⟨k, m⟩ := by
    intro k
    by_cases hk : ∀ p, M.blk p ≠ some k
    · let kb : NonPluckerBlocks M.blk := ⟨k, hk⟩
      have hxc : M.x ⟨kb, F.c kb⟩ ≠ 0 := M.x_chart_ne (mCoordIdeal_le hzb) hG kb
      have hzc : basePart M.blk z ⟨kb, F.c kb⟩ = 1 := H.1 kb
      have hv : ∀ m : ι k, IsValueAt M.x (M.x ⟨kb, m⟩ / M.x ⟨kb, F.c kb⟩) (basePart M.blk z)
          (basePart M.blk z ⟨kb, m⟩ / basePart M.blk z ⟨kb, F.c kb⟩) := fun m =>
        isValueAt_ratio hxc (by rw [hzc]; exact one_ne_zero)
      refine ⟨φL (algebraMap M.Ω Φ (M.x ⟨kb, F.c kb⟩)), 1, fun m => C ⟨_, _, hv m⟩, ?_, one_ne_zero, fun m => ?_, fun m => ?_⟩
      · exact (map_ne_zero _).2 ((map_ne_zero _).2 hxc)
      · rw [hiC, ← map_mul, ← map_mul, show y ⟨k, m⟩ = algebraMap M.Ω Φ (M.x ⟨kb, m⟩) from M.y_base ⟨kb, m⟩]
        congr 2
        exact (mul_div_cancel₀ _ hxc).symm
      · have e1 : ρ (C ⟨_, _, hv m⟩) = val ⟨_, _, hv m⟩ := eval₂Hom_C _ _ _
        rw [e1, show val ⟨_, _, hv m⟩ = _ from regVal_eq hzb _ (hv m), hzc, div_one, one_mul]
        rfl
    · push_neg at hk
      obtain ⟨p, hp⟩ := hk
      obtain ⟨a, ha, hz⟩ := H.2.2 p k hp
      let uA : (Σ k, ι k) → Finset (Fin N) → A := fun q I => ⟨F.u q I, exists_isValueAt hzb (hG.2.1 q I).1⟩
      let D : S := ∏ c ∈ stepCols N j p.2, genUp Φ N j p.1 c c
      have hD : D ≠ 0 := Finset.prod_ne_zero_iff.2 fun c _ => by
        rw [show genUp Φ N j p.1 c c = X ⟨(p.1, c, c), le_rfl, Iff.rfl⟩ from
          genUp_apply (⟨(p.1, c, c), le_rfl, Iff.rfl⟩ : UpIdx Ψ N j)]
        exact X_ne_zero _
      have hCam : (C : Φ →+* S).comp (algebraMap M.Ω Φ) = algebraMap M.Ω S :=
        RingHom.ext fun s => (MvPolynomial.algebraMap_apply ..).symm
      have hsv : ∀ m : ι k, i (∑ I, C (uA ⟨k, m⟩ I) * minorIJ (genericBlockMatrix A N j p.1) I (stepCols N j p.2)) =
          algebraMap S L (∑ I, C (algebraMap M.Ω Φ (F.u ⟨k, m⟩ I)) * minorIJ (G' p.1) I (stepCols N j p.2)) := fun m => by
        show algebraMap S L (iS _) = _
        congr 1
        rw [map_sum]
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [map_mul, ← minorIJ_map, hiG]
        congr 1
        exact (eval₂Hom_C _ _ _).trans (MvPolynomial.algebraMap_apply ..)
      have hdet : detFac j p.2 (F.T p.1) ≠ 0 := detFac_ne_zero M.j_le p.2 (hF.1 p.1).1 (hF.1 p.1).2
      have hE : (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') ≠ 0 := Finset.prod_ne_zero_iff.2 fun k' _ =>
        zpow_ne_zero _ (M.x_chart_ne (mCoordIdeal_le hzb) hG k')
      have hdetL : φL (algebraMap M.Ω Φ (detFac j p.2 (F.T p.1))) ≠ 0 := (map_ne_zero _).2 ((map_ne_zero _).2 hdet)
      have hEL : φL (algebraMap M.Ω Φ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k')) ≠ 0 := (map_ne_zero _).2 ((map_ne_zero _).2 hE)
      have hDL : algebraMap S L D ≠ 0 := fun e => hD (IsFractionRing.injective S L (by rw [e, map_zero]))
      refine ⟨φL (algebraMap M.Ω Φ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k')) /
          (φL (algebraMap M.Ω Φ (detFac j p.2 (F.T p.1))) * algebraMap S L D), a⁻¹,
        fun m => ∑ I, C (uA ⟨k, m⟩ I) * minorIJ (genericBlockMatrix A N j p.1) I (stepCols N j p.2),
        div_ne_zero hEL (mul_ne_zero hdetL hDL), inv_ne_zero ha, fun m => ?_, fun m => ?_⟩
      · have rel := frame_gen M hF (C : Φ →+* S) hp m (hGb p.1) (genUp_blockDiag p.1) (genUp_upper p.1)
          (by rw [hCam]; exact map_mul_inv_map _ (hF.1 p.1).2 _)
        have rel' := congrArg (algebraMap S L) rel
        rw [map_mul, map_mul, map_mul] at rel'
        rw [hsv, div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hdetL hDL)]
        refine Eq.trans ?_ (rel'.trans ?_)
        · show _ = φL _ * algebraMap S L D * φL _
          ring
        · rfl
      · rw [map_sum, hz m, inv_mul_cancel_left₀ ha]
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [map_mul, ← minorIJ_map, hρ]
        congr 1
        exact eval₂Hom_C _ _ _
  choose e t sv he ht has hv using key
  have hz' : z ∈ mcPts (mCoordIdeal (fun q : Σ k, ι k => φL (y q))) :=
    mem_mcPts_of_ringHom i hi ρ _ (fun q => sv q.1 q.2) e t z hnz he ht (fun q => has q.1 q.2) fun q => hv q.1 q.2
  refine ⟨hnz, fun f hf => hz'.2 f ?_⟩
  have h0 : mConeMap y f = 0 := hf
  show mConeMap (φL ∘ y) f = 0
  rw [mConeMap_comp, h0, map_zero]

end Back

section Fwd

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (M : FlagModel y Ψ N j)

theorem flag_fwd {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) (hG : M.GoodAt F (mCoordIdeal (basePart M.blk z)))
    (hc : ∀ k, basePart M.blk z ⟨k, F.c k⟩ = 1) : ∃ h, M.IsFlagOf F z h := by
  have hzb := base_mem M hz
  let am := algebraMap M.Ω Φ
  let O := regRing y z
  let v : O →+* ℂ := regVal hz
  obtain ⟨V, hOV, hpl⟩ := GlobalTheory.T.valuation_ring_extension_specialization Φ O v (regVal_local hz)
  have hO : ∀ {s}, RegAt M.x (mCoordIdeal (basePart M.blk z)) s → am s ∈ O := fun hs => ⟨_, val_lift M hz hs⟩
  let Ag : Ψ → Matrix (Fin N) (Fin N) Φ := fun τ => (F.T τ)⁻¹.map am * M.g τ
  have hinvD : ∀ τ, ((F.T τ)⁻¹.map am).det ≠ 0 := fun τ => by
    have : ((F.T τ)⁻¹.map am).det = am ((F.T τ)⁻¹.det) := (RingHom.map_det am _).symm
    rw [this]
    refine (map_ne_zero am).2 fun h0 => ?_
    have h1 := Matrix.det_nonsing_inv_mul_det (F.T τ) (hF.1 τ).2.isUnit
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hAgB : ∀ τ, IsBlockDiag j (Ag τ) := fun τ =>
    (((hF.1 τ).1.inv (hF.1 τ).2.isUnit).map am).mul (M.g_block τ)
  have hAgD : ∀ τ, (Ag τ).det ≠ 0 := fun τ => by
    rw [Matrix.det_mul]
    exact mul_ne_zero (hinvD τ) (M.isUnit_det_g τ).ne_zero
  choose b hbB hbT hbd hbV hbdet hbinv using fun τ => GlobalTheory.T.block_diag_valuation_normalization Φ V N j (Ag τ) (hAgB τ) (hAgD τ)
  let H : Ψ → Matrix (Fin N) (Fin N) Φ := fun τ => Ag τ * b τ
  have hHB : ∀ τ, IsBlockDiag j (H τ) := fun τ => (hAgB τ).mul (hbB τ)
  let wf : ∀ (p : Ψ × Fin N) (k : K), ι k → Φ := fun p k m =>
    ∑ I, am (F.u ⟨k, m⟩ I) * minorIJ (H p.1) I (stepCols N j p.2)
  have data : ∀ p, ∃ wc : Φ, wc ∈ V ∧ wc ≠ 0 ∧ wc⁻¹ ∈ V ∧ ∀ k, M.blk p = some k → ∃ c : ι k, z ⟨k, c⟩ ≠ 0 ∧
      ∀ m, ∃ r, IsValueAt y r z (z ⟨k, m⟩ / z ⟨k, c⟩) ∧ wf p k m = r * wc := by
    intro p
    cases hp : M.blk p with
    | none => exact ⟨1, V.one_mem, one_ne_zero, by simpa using V.one_mem, fun k hk => by cases hk⟩
    | some k =>
      obtain ⟨c, hzc⟩ := hz.1 k
      have hyc : y ⟨k, c⟩ ≠ 0 := coord_ne hz hzc
      have hdet : am (detFac j p.2 (F.T p.1)) ≠ 0 :=
        (map_ne_zero am).2 (detFac_ne_zero M.j_le p.2 (hF.1 p.1).1 (hF.1 p.1).2)
      have hE : am (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') ≠ 0 := (map_ne_zero am).2 (Finset.prod_ne_zero_iff.2 fun k' _ =>
        zpow_ne_zero _ (M.x_chart_ne (mCoordIdeal_le hzb) hG k'))
      have hB : (∏ c ∈ stepCols N j p.2, b p.1 c c) ≠ 0 := Finset.prod_ne_zero_iff.2 fun c _ => hbd p.1 c
      have rel : ∀ m, am (detFac j p.2 (F.T p.1)) * (∏ c ∈ stepCols N j p.2, b p.1 c c) * y ⟨k, m⟩ =
          am (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') * wf p k m := fun m =>
        frame_gen M hF (RingHom.id Φ) hp m (hHB p.1) (hbB p.1) (hbT p.1) (by
          show (F.T p.1).map am * ((F.T p.1)⁻¹.map am * M.g p.1 * b p.1) = (M.g p.1).map (RingHom.id Φ) * b p.1
          rw [Matrix.mul_assoc ((F.T p.1)⁻¹.map am), map_mul_inv_map am (hF.1 p.1).2]
          rfl)
      obtain ⟨e, he, hw⟩ : ∃ e : Φ, e ≠ 0 ∧ ∀ m, wf p k m = e * y ⟨k, m⟩ :=
        ⟨am (detFac j p.2 (F.T p.1)) * (∏ c ∈ stepCols N j p.2, b p.1 c c) / am (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k'),
          div_ne_zero (mul_ne_zero hdet hB) hE, fun m => by
            rw [div_mul_eq_mul_div, rel m, mul_div_cancel_left₀ _ hE]⟩
      obtain ⟨m₀, hm₀, hm₀i⟩ := GlobalTheory.T.step_rows_inverse_nonzero_entry Φ V N j p.2 (H p.1) (ι k) (fun m I => am (F.u ⟨k, m⟩ I))
        (fun I m => am (F.u' I ⟨k, m⟩)) M.j_le (hHB p.1) (hbV p.1) (hbdet p.1) (hbinv p.1)
        (fun I m => hOV _ (hO (hG.2.1 _ I).2)) (fun m I => hOV _ (hO (hG.2.1 _ I).1)) (fun I I' hI hI' => by
          have := congrArg am (hF.2.2.1 p k hp I I' hI hI')
          rw [map_sum] at this
          simp only [map_mul] at this
          rw [this]
          split_ifs <;> simp)
      have hwc : wf p k c ≠ 0 := by rw [hw]; exact mul_ne_zero he hyc
      have hr : ∀ m, wf p k m = y ⟨k, m⟩ / y ⟨k, c⟩ * wf p k c := fun m => by
        rw [hw, hw]
        field_simp
      refine ⟨wf p k c, ?_, hwc, ?_, fun k' hk' => ?_⟩
      · exact sum_mem fun I _ => V.mul_mem _ _ (hOV _ (hO (hG.2.1 _ I).1)) (minorIJ_mem V.toSubring (hbV p.1) I _)
      · have h1 : y ⟨k, m₀⟩ / y ⟨k, c⟩ ∈ O := ⟨_, isValueAt_ratio hyc hzc⟩
        have h2 : (wf p k c)⁻¹ = y ⟨k, m₀⟩ / y ⟨k, c⟩ * (wf p k m₀)⁻¹ := by
          have hm₀' : wf p k m₀ ≠ 0 := hm₀
          rw [hr m₀] at hm₀' ⊢
          have h3 := left_ne_zero_of_mul hm₀'
          rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ h3, one_mul]
        rw [h2]
        exact V.mul_mem _ _ (hOV _ h1) hm₀i
      · obtain rfl := Option.some.inj hk'
        exact ⟨c, hzc, fun m => ⟨_, isValueAt_ratio hyc hzc, hr m⟩⟩
  choose wc hwV hw0 hwinv hdat using data
  let T : Finset Φ := (Finset.univ.image fun t : Ψ × Fin N × Fin N => H t.1 t.2.1 t.2.2) ∪
    (Finset.univ.image fun τ => (H τ).det) ∪ (Finset.univ.image wc)
  have hT1 : ∀ τ a c, H τ a c ∈ T := fun τ a c => Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_image.2 ⟨(τ, a, c), Finset.mem_univ _, rfl⟩))
  have hT2 : ∀ τ, (H τ).det ∈ T := fun τ => Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image.2 ⟨τ, Finset.mem_univ _, rfl⟩))
  have hT3 : ∀ p, wc p ∈ T := fun p => Finset.mem_union_right _ (Finset.mem_image.2 ⟨p, Finset.mem_univ _, rfl⟩)
  have hTV : ∀ t ∈ T, t ∈ V := fun t ht => by
    rcases Finset.mem_union.1 ht with ht | ht
    · rcases Finset.mem_union.1 ht with ht | ht
      · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ht
        exact hbV _ _ _
      · obtain ⟨τ, -, rfl⟩ := Finset.mem_image.1 ht
        exact det_mem V.toSubring (hbV τ)
    · obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 ht
      exact hwV p
  obtain ⟨R, hOR, ψ, hTR, hψ, hinv⟩ := hpl T hTV
  let HR : Ψ → Matrix (Fin N) (Fin N) R := fun τ => Matrix.of fun a c => ⟨H τ a c, hTR _ (hT1 τ a c)⟩
  have hHR : ∀ τ, (HR τ).map R.subtype = H τ := fun τ => by ext a c; rfl
  refine ⟨fun τ => (HR τ).map ψ, hc, fun τ => ⟨?_, ?_⟩, fun p k hp => ?_⟩
  · intro a c hac
    have h0 : HR τ a c = 0 := Subtype.ext (hHB τ a c hac)
    show ψ (HR τ a c) = 0
    rw [h0, map_zero]
  · have e1 : R.subtype (HR τ).det = (H τ).det := by rw [RingHom.map_det]; exact congrArg _ (hHR τ)
    have e2 : (HR τ).det * ⟨(H τ).det⁻¹, hinv _ (hT2 τ) (hbdet τ) (hbinv τ)⟩ = 1 := Subtype.ext (by
      show R.subtype (HR τ).det * (H τ).det⁻¹ = 1
      rw [e1, mul_inv_cancel₀ (hbdet τ)])
    have e3 := congrArg ψ e2
    rw [map_mul, map_one, RingHom.map_det] at e3
    exact left_ne_zero_of_mul_eq_one e3
  · obtain ⟨c, hzc, hm⟩ := hdat p k hp
    let wR : R := ⟨wc p, hTR _ (hT3 p)⟩
    have hβ : ψ wR ≠ 0 := by
      have e2 : wR * ⟨(wc p)⁻¹, hinv _ (hT3 p) (hw0 p) (hwinv p)⟩ = 1 := Subtype.ext (mul_inv_cancel₀ (hw0 p))
      have e3 := congrArg ψ e2
      rw [map_mul, map_one] at e3
      exact left_ne_zero_of_mul_eq_one e3
    refine ⟨z ⟨k, c⟩ / ψ wR, div_ne_zero hzc hβ, fun m => ?_⟩
    obtain ⟨r, hr, hw⟩ := hm m
    let uR : Finset (Fin N) → R := fun I => Subring.inclusion hOR ⟨am (F.u ⟨k, m⟩ I), hO (hG.2.1 _ I).1⟩
    let rR : R := Subring.inclusion hOR ⟨r, _, hr⟩
    have e1 : ∑ I, uR I * minorIJ (HR p.1) I (stepCols N j p.2) = rR * wR := Subtype.ext (by
      show R.subtype _ = r * wc p
      rw [map_sum]
      simp only [map_mul, ← minorIJ_map, hHR]
      exact hw)
    have e2 := congrArg ψ e1
    rw [map_sum] at e2
    simp only [map_mul, ← minorIJ_map] at e2
    have e3 : ∀ I, ψ (uR I) = valAt M.x (F.u ⟨k, m⟩ I) (basePart M.blk z) := fun I =>
      (hψ _).trans (regVal_eq hz _ (val_lift M hz (hG.2.1 _ I).1))
    have e4 : ψ rR = z ⟨k, m⟩ / z ⟨k, c⟩ := (hψ _).trans (regVal_eq hz _ hr)
    simp only [e3] at e2
    rw [e4] at e2
    show z ⟨k, m⟩ = _ * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (basePart M.blk z) * minorIJ ((HR p.1).map ψ) I (stepCols N j p.2)
    rw [e2]
    field_simp

end Fwd

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j), (∀ z ∈ mcPts (mCoordIdeal y), basePart M.blk z ∈ mcPts (mCoordIdeal M.x)) ∧ (∀ zb ∈ mcPts (mCoordIdeal M.x), ∃ F, M.IsFrame F ∧ M.GoodAt F (mCoordIdeal zb)) ∧ ∀ F, M.IsFrame F → ∀ z : (Σ k, ι k) → ℂ, basePart M.blk z ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal (basePart M.blk z)) → (∀ k, basePart M.blk z ⟨k, F.c k⟩ = 1) → (z ∈ mcPts (mCoordIdeal y) ↔ ∃ h, M.IsFlagOf F z h) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M
  refine ⟨fun z hz => base_mem M hz, fun zb hzb => ?_, fun F hF z hzb hG hc => ⟨fun hz => flag_fwd M hF hz hG hc, fun ⟨h, H⟩ => flag_back M hF hzb hG H⟩⟩
  choose c hc using hzb.1
  exact M.frames _ (RingHom.ker_isPrime _) (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.relevant zb c hc)
    (mCoordIdeal_le hzb)

end GlobalTheory.CompanionTheory.Ar.PB.CPts
end
end
