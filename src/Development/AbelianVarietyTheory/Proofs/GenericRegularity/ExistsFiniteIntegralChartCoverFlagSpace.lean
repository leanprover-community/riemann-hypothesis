import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsEigenProjectorRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PolyChartSmoothFractionLift
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NonemptyLift
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsEigenvectorIffLieBasisCoordinates
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsRingHomOfIsLieComb
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FinrankEqOfExistsUniqueComb
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFrPtTie
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TieBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FramedPointVectorsIntegralInCell
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralGeneratorOfChartPointCdvr
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ModelChartLiftCoordsGeneratorIndepStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsCombAtIffCoordinateCombinationStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsOpenImmersionOfSurj
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.AppLEInjective
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFiniteMchartCover
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralPivotDecomposition

section
namespace GlobalTheory

open Matrix

theorem eq_cols_mul_inv_minor_mul_rows {Ω : Type} [Field Ω] {n r : ℕ}
    (π : Matrix (Fin n) (Fin n) Ω) (hπ : π.rank = r) (ι κ : Fin r → Fin n)
    (hd : (π.submatrix ι κ).det ≠ 0) :
    π = π.submatrix id κ * (π.submatrix ι κ)⁻¹ * π.submatrix ι id := by
  have hu : IsUnit (π.submatrix ι κ).det := isUnit_iff_ne_zero.mpr hd
  have hC : π.submatrix id κ = π * (1 : Matrix (Fin n) (Fin n) Ω).submatrix id κ := by
    ext i j; simp [Matrix.mul_apply, Matrix.one_apply]
  have hA : π.submatrix ι κ
      = (1 : Matrix (Fin n) (Fin n) Ω).submatrix ι id * π.submatrix id κ := by
    ext i j; simp [Matrix.mul_apply, Matrix.one_apply]
  have hrA : (π.submatrix ι κ).rank = r := by
    have := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
    simpa using this
  have hle : LinearMap.range (π.submatrix id κ).mulVecLin ≤ LinearMap.range π.mulVecLin := by
    rw [hC, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  have hr : π.rank ≤ (π.submatrix id κ).rank := by
    rw [hπ]
    calc r = (π.submatrix ι κ).rank := hrA.symm
      _ ≤ (π.submatrix id κ).rank := by
        conv_lhs => rw [hA]
        exact Matrix.rank_mul_le_right _ _
  have heq := Submodule.eq_of_le_of_finrank_le hle hr
  have hcol : ∀ j : Fin n, ∃ c : Fin r → Ω, (π.submatrix id κ) *ᵥ c = fun i => π i j := by
    intro j
    have : (fun i => π i j) ∈ LinearMap.range π.mulVecLin :=
      ⟨Pi.single j 1, by ext i; simp⟩
    rw [← heq] at this
    exact this
  choose c hc using hcol
  set X : Matrix (Fin r) (Fin n) Ω := Matrix.of fun a j => c j a with hX
  have h1 : π = π.submatrix id κ * X := by
    ext i j
    have := congrFun (hc j) i
    rw [← this]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hX]
  have h2 : π.submatrix ι id = π.submatrix ι κ * X := by
    ext i j
    have := congrFun (congrFun h1 (ι i)) j
    simpa [Matrix.mul_apply] using this
  rw [h2, Matrix.mul_assoc, ← Matrix.mul_assoc (π.submatrix ι κ)⁻¹, Matrix.nonsing_inv_mul _ hu,
    Matrix.one_mul]
  exact h1

theorem exists_cols_det_ne_zero_of_mul {Ω : Type} [Field Ω] {n r : ℕ}
    (R : Matrix (Fin r) (Fin n) Ω) (u : Matrix (Fin n) (Fin r) Ω) (hd : (R * u).det ≠ 0) :
    ∃ κ : Fin r → Fin n, (R.submatrix id κ).det ≠ 0 := by
  have hu : IsUnit (R * u).det := isUnit_iff_ne_zero.mpr hd
  have hrA : (R * u).rank = r := by
    have := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
    simpa using this
  have hrR : R.rank = r := by
    apply le_antisymm
    · simpa using Matrix.rank_le_card_height R
    · calc r = (R * u).rank := hrA.symm
        _ ≤ R.rank := Matrix.rank_mul_le_left _ _
  obtain ⟨K, a, ha, hspan, hli⟩ := exists_linearIndependent' Ω R.col
  haveI : Fintype K := Fintype.ofInjective a ha
  have hcard : Fintype.card K = r := by
    rw [← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_cols, hrR]
  let e : Fin r ≃ K := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ?_⟩
  have h3 : LinearIndependent Ω (R.submatrix id (a ∘ e)).col := hli.comp e e.injective
  rw [Matrix.linearIndependent_cols_iff_isUnit] at h3
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp h3)

theorem rank_minor_factorisation :
    ∀ (Ω : Type) [Field Ω] (n r : ℕ) (π : Matrix (Fin n) (Fin n) Ω), π.rank = r → ∀ ι : Fin r → Fin n, (∀ κ : Fin r → Fin n, (π.submatrix ι κ).det ≠ 0 → π = π.submatrix id κ * (π.submatrix ι κ)⁻¹ * π.submatrix ι id) ∧ ∀ u : Matrix (Fin n) (Fin r) Ω, π * u = u → (u.submatrix ι id).det ≠ 0 → ∃ κ : Fin r → Fin n, (π.submatrix ι κ).det ≠ 0 := by
  intro Ω _ n r π hπ ι
  refine ⟨fun κ hd => eq_cols_mul_inv_minor_mul_rows π hπ ι κ hd, fun u hu hd => ?_⟩
  have h : π.submatrix ι id * u = u.submatrix ι id := by
    ext i j
    have := congrFun (congrFun hu (ι i)) j
    simpa [Matrix.mul_apply] using this
  obtain ⟨κ, hκ⟩ := exists_cols_det_ne_zero_of_mul (π.submatrix ι id) u (h ▸ hd)
  exact ⟨κ, hκ⟩

end GlobalTheory
end

section
open NumberField

namespace GlobalTheory.Reg.CellChart

section Lin
open Matrix

theorem det_of_inCell {R : Type} [CommRing R] {n r : ℕ} (ix : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) R)
    (h : InCell ix u) : (u.submatrix ix id).det = 1 := by
  rw [Matrix.det_of_lowerTriangular (u.submatrix ix id) (fun i j hij => h.1 i j hij)]
  simp [h.2]

theorem rank_of_quasi_idem {L : Type} [Field L] {n : ℕ} (P : Matrix (Fin n) (Fin n) L) (N : L) (hN : N ≠ 0)
    (hP : P * P = N • P) (S : Submodule L (Fin n → L)) (hS : ∀ x, x ∈ S ↔ P.mulVec x = N • x) :
    P.rank = Module.finrank L S := by
  have : LinearMap.range P.mulVecLin = S := by
    ext x
    rw [hS, LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hP, Matrix.smul_mulVec]
    · intro h
      refine ⟨N⁻¹ • x, ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_smul, h, smul_smul, inv_mul_cancel₀ hN, one_smul]
  rw [Matrix.rank, this]

theorem exists_minor {L : Type} [Field L] {n r : ℕ} (P : Matrix (Fin n) (Fin n) L) (N : L) (hN : N ≠ 0)
    (ix : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) L) (hu : P * u = N • u) (hc : InCell ix u) :
    ∃ κ : Fin r → Fin n, (P.submatrix ix κ).det ≠ 0 := by
  have h : P.submatrix ix id * u = N • u.submatrix ix id := by
    ext i j
    have := congrFun (congrFun hu (ix i)) j
    simpa [Matrix.mul_apply] using this
  obtain ⟨κ, hκ⟩ := GlobalTheory.exists_cols_det_ne_zero_of_mul (P.submatrix ix id) u (by
    rw [h, Matrix.det_smul, det_of_inCell ix u hc]; simp [hN])
  exact ⟨κ, hκ⟩

theorem eq_of_rows {L : Type} [Field L] {n r m : ℕ} (P : Matrix (Fin n) (Fin n) L) (hr : P.rank = r) (N : L)
    (hN : N ≠ 0) (ix κ : Fin r → Fin n) (hd : (P.submatrix ix κ).det ≠ 0) (u : Matrix (Fin n) (Fin m) L)
    (hu : P * u = N • u) : u = P.submatrix id κ * (P.submatrix ix κ)⁻¹ * u.submatrix ix id := by
  have h : P.submatrix ix id * u = N • u.submatrix ix id := by
    ext i j
    have := congrFun (congrFun hu (ix i)) j
    simpa [Matrix.mul_apply] using this
  have h1 := ((GlobalTheory.rank_minor_factorisation L n r P hr ix).1 κ hd)
  have h2 : N • u = N • (P.submatrix id κ * (P.submatrix ix κ)⁻¹ * u.submatrix ix id) := by
    rw [← hu, ← Matrix.mul_smul, ← h, ← Matrix.mul_assoc, ← h1]
  exact smul_right_injective _ hN h2

end Lin

theorem exists_projector (E K : Type) [Field E] [NumberField E] [Field K] (emb : (E →+* ℂ) → (E →+* K))
    (hemb : Function.Injective emb) (O : Type) [CommRing O] [IsDomain O] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] (α : O →+* A) (n : ℕ) (ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) A) (τ : E →+* ℂ) :
    ∃ (N : O) (p : Matrix (Fin n) (Fin n) A), N ≠ 0 ∧ ∀ (R : Type) [CommRing R] [Algebra K R] (f : A →+* R),
      f.comp α = (algebraMap K R).comp (algebraMap O K) →
      (p.map f * p.map f = f (α N) • p.map f) ∧ ∀ x : Fin n → R,
        (∀ b : 𝓞 E, ((ρ b).map f).mulVec x = algebraMap K R (emb τ (b : E)) • x) ↔
          (p.map f).mulVec x = f (α N) • x := by
  obtain ⟨m, a, κ, h⟩ := GlobalTheory.exists_eigen_projector_ringOfIntegers E K emb hemb τ
  obtain ⟨N, hN⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) κ
  choose t ht using hN
  refine ⟨N, ∑ k, α (t k) • ρ (a k), nonZeroDivisors.ne_zero N.2, fun R _ _ f hf => ?_⟩
  have hf' : ∀ o, f (α o) = algebraMap K R (algebraMap O K o) := fun o => RingHom.congr_fun hf o
  obtain ⟨h1, h2⟩ := h R n (f.mapMatrix.comp ρ)
  set π := ∑ k, algebraMap K R (κ k) • (f.mapMatrix.comp ρ) (a k) with hπ
  have hp : (∑ k, α (t k) • ρ (a k)).map f = f (α N) • π := by
    ext i j
    have ht' : ∀ i, algebraMap O K (t i) = algebraMap O K N * κ i := fun i => (ht i).trans (Algebra.smul_def _ _)
    simp only [hπ, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, hf', ht',
      Finset.mul_sum, RingHom.comp_apply, RingHom.mapMatrix_apply, mul_assoc]
  have hu : IsUnit (f (α N)) := by
    rw [hf']
    exact (IsLocalization.map_units K N).map _
  have hππ : π * π = π := by
    ext i j
    have := h2 (fun k => π k j) (fun b => by
      funext k
      have := congrFun (congrFun (h1 b) k) j
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this)
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun this i
  rw [hp]
  refine ⟨by rw [Matrix.smul_mul, Matrix.mul_smul, hππ], fun x => ⟨fun hx => ?_, fun hx b => ?_⟩⟩
  · rw [Matrix.smul_mulVec, h2 x hx]
  · rw [Matrix.smul_mulVec] at hx
    have hx' : π.mulVec x = x := hu.smul_left_cancel.mp hx
    have := congrArg (fun M => Matrix.mulVec M x) (h1 b)
    simp only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, hx'] at this
    exact this

theorem loc_descr {K O A F : Type} [Field K] [CommRing O] [IsDomain O] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [Field F] [Algebra K F] (α : O →+* A) (i : A →+* F)
    (hi : i.comp α = (algebraMap K F).comp (algebraMap O K)) (g : A) (hg : i g ≠ 0) (x : F)
    (hx : x ∈ Algebra.adjoin K (insert (i g)⁻¹ (Set.range i))) :
    ∃ (a : A) (b : O) (m : ℕ), b ≠ 0 ∧ x * i (α b * g ^ m) = i a := by
  have hi' : ∀ o, i (α o) = algebraMap K F (algebraMap O K o) := fun o => RingHom.congr_fun hi o
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨a, rfl⟩
    · exact ⟨1, 1, 1, one_ne_zero, by simp [hg]⟩
    · exact ⟨a, 1, 0, one_ne_zero, by simp⟩
  | algebraMap k =>
    obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (nonZeroDivisors O) k
    refine ⟨α a, b, 0, nonZeroDivisors.ne_zero b.2, ?_⟩
    rw [pow_zero, mul_one, hi', hi', ← map_mul, h]
  | add x y _ _ hx hy =>
    obtain ⟨a, b, m, hb, h⟩ := hx
    obtain ⟨a', b', m', hb', h'⟩ := hy
    refine ⟨a * (α b' * g ^ m') + a' * (α b * g ^ m), b * b', m + m', mul_ne_zero hb hb', ?_⟩
    simp only [map_add, map_mul, map_pow] at h h' ⊢
    rw [← h, ← h']; ring
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, m, hb, h⟩ := hx
    obtain ⟨a', b', m', hb', h'⟩ := hy
    refine ⟨a * a', b * b', m + m', mul_ne_zero hb hb', ?_⟩
    simp only [map_add, map_mul, map_pow] at h h' ⊢
    rw [← h, ← h']; ring

theorem loc_lift {K O A F L : Type} [Field K] [CommRing O] [IsDomain O] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [Field F] [Algebra K F] [Field L] [Algebra K L] (α : O →+* A) (i : A →+* F)
    (hinj : Function.Injective i)
    (hi : i.comp α = (algebraMap K F).comp (algebraMap O K)) (g : A) (hg : i g ≠ 0) (f : A →+* L)
    (hf : f.comp α = (algebraMap K L).comp (algebraMap O K)) (hfg : f g ≠ 0) :
    ∃ ψ : Algebra.adjoin K (insert (i g)⁻¹ (Set.range i)) →ₐ[K] L,
      ∀ a (h : i a ∈ Algebra.adjoin K (insert (i g)⁻¹ (Set.range i))), ψ ⟨i a, h⟩ = f a := by
  have hi' : ∀ o, i (α o) = algebraMap K F (algebraMap O K o) := fun o => RingHom.congr_fun hi o
  have hf' : ∀ o, f (α o) = algebraMap K L (algebraMap O K o) := fun o => RingHom.congr_fun hf o
  set R₀ := Algebra.adjoin K (insert (i g)⁻¹ (Set.range i)) with hR₀
  have hm : ∀ a, i a ∈ R₀ := fun a => Algebra.subset_adjoin (Or.inr ⟨a, rfl⟩)
  let i₀ : A →+* R₀ := i.codRestrict R₀.toSubring hm
  letI : Algebra A R₀ := i₀.toAlgebra
  let S : Submonoid A := (IsUnit.submonoid R₀).comap i₀ ⊓ (IsUnit.submonoid L).comap f
  have hO : ∀ b : O, i₀ (α b) = algebraMap K R₀ (algebraMap O K b) := fun b => Subtype.ext (hi' b)
  have hK : ∀ b : O, b ≠ 0 → IsUnit (algebraMap O K b) := fun b hb =>
    IsLocalization.map_units K (⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩ : nonZeroDivisors O)
  have hgS : g ∈ S := ⟨IsUnit.of_mul_eq_one (⟨(i g)⁻¹, Algebra.subset_adjoin (Or.inl rfl)⟩ : R₀)
    (Subtype.ext (mul_inv_cancel₀ hg)), isUnit_iff_ne_zero.mpr hfg⟩
  have hbS : ∀ b : O, b ≠ 0 → α b ∈ S := fun b hb =>
    ⟨show IsUnit (i₀ (α b)) from hO b ▸ (hK b hb).map _, show IsUnit (f (α b)) from hf' b ▸ (hK b hb).map _⟩
  haveI : IsLocalization S R₀ := by
    refine (isLocalization_iff S R₀).mpr ⟨fun y => y.2.1, fun z => ?_, fun {x y} h => ⟨1, ?_⟩⟩
    · obtain ⟨a, b, m, hb, h⟩ := loc_descr α i hi g hg z z.2
      exact ⟨⟨a, ⟨α b * g ^ m, S.mul_mem (hbS b hb) (S.pow_mem hgS m)⟩⟩, Subtype.ext h⟩
    · rw [hinj (congrArg Subtype.val h)]
  let φ : R₀ →+* L := IsLocalization.lift (M := S) (g := f) (fun y => y.2.2)
  have hφ : ∀ a, φ (i₀ a) = f a := fun a => IsLocalization.lift_eq (M := S) (g := f) (fun y => y.2.2) a
  have hc : φ.comp (algebraMap K R₀) = algebraMap K L := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors O) (RingHom.ext fun o => ?_)
    simp only [RingHom.comp_apply]
    rw [← hO, hφ, hf']
  exact ⟨⟨φ, fun k => RingHom.congr_fun hc k⟩, fun a h => hφ a⟩

end GlobalTheory.Reg.CellChart
end

section
open NumberField

namespace GlobalTheory.Reg.CellChart

noncomputable def genLower {V Ω : Type} [CommRing Ω] {r : ℕ} (X : ∀ i j : Fin r, j < i → V) (x : V → Ω) :
    Matrix (Fin r) (Fin r) Ω := fun i j => if h : j < i then x (X i j h) else if i = j then 1 else 0

theorem adjoin_insert_eq' {K O A F Ω : Type} [Field K] [CommRing O] [Algebra O K] [CommRing A] [Field F] [Field Ω]
    [Algebra K F] [Algebra K Ω] [Algebra F Ω] [IsScalarTower K F Ω] (i : A →+* F) (a₀ : A) (gens X : Set Ω)
    (h1 : ∀ a, algebraMap F Ω (i a) ∈ Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ gens))
    (h2 : X ⊆ gens)
    (h3 : gens ⊆ Algebra.adjoin K (algebraMap F Ω '' (Algebra.adjoin K (insert (i a₀)⁻¹ (Set.range i)) : Set F) ∪ X)) :
    Algebra.adjoin K (insert (algebraMap F Ω (i a₀))⁻¹ gens) =
      Algebra.adjoin K (algebraMap F Ω '' (Algebra.adjoin K (insert (i a₀)⁻¹ (Set.range i)) : Set F) ∪ X) := by
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro x (rfl | hx)
    · exact Algebra.subset_adjoin (Or.inl ⟨(i a₀)⁻¹, Algebra.subset_adjoin (Or.inl rfl), map_inv₀ _ _⟩)
    · exact h3 hx
  · rw [Algebra.adjoin_le_iff]
    rintro x (⟨y, hy, rfl⟩ | hx)
    · have : Algebra.adjoin K (insert (i a₀)⁻¹ (Set.range i)) ≤
          (Algebra.adjoin K (insert (algebraMap F Ω (i a₀))⁻¹ gens)).comap (IsScalarTower.toAlgHom K F Ω) := by
        rw [Algebra.adjoin_le_iff]
        rintro z (rfl | ⟨a, rfl⟩)
        · exact Algebra.subset_adjoin (Or.inl (map_inv₀ (algebraMap F Ω) _))
        · have : Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ gens) ≤
              (Algebra.adjoin K (insert (algebraMap F Ω (i a₀))⁻¹ gens)).toSubring := by
            rw [Subring.closure_le]
            rintro w (⟨o, rfl⟩ | hw)
            · exact Subalgebra.algebraMap_mem _ _
            · exact Algebra.subset_adjoin (Or.inr hw)
          exact this (h1 a)
      exact this hy
    · exact Algebra.subset_adjoin (Or.inr (h2 hx))

theorem adjoin_insert_eq {K O A F Ω : Type} [Field K] [CommRing O] [Algebra O K] [CommRing A] [Field F] [Field Ω]
    [Algebra K F] [Algebra K Ω] [Algebra F Ω] [IsScalarTower K F Ω] (i : A →+* F) (g : A →+* Ω)
    (hg : ∀ a, g a = algebraMap F Ω (i a)) (a₀ : A) (gens X : Set Ω)
    (h1 : ∀ a, g a ∈ Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ gens))
    (h2 : X ⊆ gens)
    (h3 : gens ⊆ Algebra.adjoin K (algebraMap F Ω '' (Algebra.adjoin K (insert (i a₀)⁻¹ (Set.range i)) : Set F) ∪ X)) :
    Algebra.adjoin K (insert (g a₀)⁻¹ gens) =
      Algebra.adjoin K (algebraMap F Ω '' (Algebra.adjoin K (insert (i a₀)⁻¹ (Set.range i)) : Set F) ∪ X) := by
  rw [hg]
  exact adjoin_insert_eq' i a₀ gens X (fun a => hg a ▸ h1 a) h2 h3

theorem mul_inv_mem {K F : Type} [Field K] [Field F] [Algebra K F] (R : Subalgebra K F) {n r : ℕ}
    (C : Matrix (Fin n) (Fin r) F) (D : Matrix (Fin r) (Fin r) F) (hC : ∀ i j, C i j ∈ R) (hD : ∀ i j, D i j ∈ R)
    (hd : D.det⁻¹ ∈ R) (i : Fin n) (j : Fin r) : (C * D⁻¹) i j ∈ R := by
  let D' : Matrix (Fin r) (Fin r) R := fun i j => ⟨D i j, hD i j⟩
  have h : D = R.val.toRingHom.mapMatrix D' := rfl
  have hadj : ∀ i j, D.adjugate i j ∈ R := fun i j => by
    rw [h, ← RingHom.map_adjugate]
    exact (D'.adjugate i j).2
  rw [Matrix.mul_apply, Matrix.inv_def, Ring.inverse_eq_inv]
  exact R.sum_mem fun k _ => R.mul_mem (hC i k) (R.mul_mem hd (hadj k j))

theorem basis_over_subalgebra {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (R : Subalgebra K Ω) {n r : ℕ}
    (ix : Fin r ↪ Fin n) (κ : Fin r → Fin n) (P : Matrix (Fin n) (Fin n) R) (N : R) (hN : N ≠ 0)
    (hr : (P.map R.val).rank = r) (hd : ((P.map R.val).submatrix ix κ).det ≠ 0)
    (u : Matrix (Fin n) (Fin r) R) (hu : P * u = N • u) (hc : InCell ix u) (x : Fin n → R)
    (hx : P.mulVec x = N • x) : ∃! a, u.mulVec a = x := by
  have hdet : IsUnit (u.submatrix ix id).det := by rw [det_of_inCell ix u hc]; exact isUnit_one
  have hrow : ∀ a, (u.submatrix ix id).mulVec a = u.mulVec a ∘ ix := fun a => rfl
  refine ⟨(u.submatrix ix id)⁻¹.mulVec (x ∘ ix), ?_, fun a ha => ?_⟩
  · set a := (u.submatrix ix id)⁻¹.mulVec (x ∘ ix) with ha
    have h1 : u.mulVec a ∘ ix = x ∘ ix := by
      rw [← hrow, ha, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    have h2 : P.mulVec (u.mulVec a) = N • u.mulVec a := by
      rw [Matrix.mulVec_mulVec, hu, Matrix.smul_mulVec]
    have hN' : (N : Ω) ≠ 0 := fun h => hN (Subtype.ext h)
    have key : ∀ y : Fin n → R, P.mulVec y = N • y →
        P.map R.val * (Matrix.of fun i (_ : Fin 1) => (y i : Ω)) = (N : Ω) • Matrix.of fun i (_ : Fin 1) => (y i : Ω) := by
      intro y hy
      ext i j
      have := congrArg Subtype.val (congrFun hy i)
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    have e1 := eq_of_rows _ hr (N : Ω) hN' ix κ hd _ (key _ h2)
    have e2 := eq_of_rows _ hr (N : Ω) hN' ix κ hd _ (key _ hx)
    have e3 : (Matrix.of fun i (_ : Fin 1) => (u.mulVec a i : Ω)).submatrix ix id =
        (Matrix.of fun i (_ : Fin 1) => (x i : Ω)).submatrix ix id := by
      ext i j
      exact congrArg Subtype.val (congrFun h1 i)
    rw [e3, ← e2] at e1
    funext i
    exact Subtype.ext (congrFun (congrFun e1 i) 0)
  · rw [← ha, ← hrow, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

theorem exists_fraction_field (K O A : Type) [Field K] [CommRing O] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [IsDomain A] (α : O →+* A) (hinj : Function.Injective α) :
    ∃ (F : Type) (_ : Field F) (_ : Algebra K F) (i : A →+* F), Function.Injective i ∧
      i.comp α = (algebraMap K F).comp (algebraMap O K) ∧ ∀ x : F, ∃ a b : A, i b ≠ 0 ∧ x * i b = i a := by
  have h := IsFractionRing.injective A (FractionRing A)
  have h' : Function.Injective ((algebraMap A (FractionRing A)).comp α) := h.comp hinj
  obtain ⟨φ, hφ⟩ : ∃ φ : K →+* FractionRing A, ∀ o, φ (algebraMap O K o) = algebraMap A (FractionRing A) (α o) :=
    ⟨IsFractionRing.lift (K := K) h', fun o => IsFractionRing.lift_algebraMap h' o⟩
  refine ⟨FractionRing A, inferInstance, φ.toAlgebra, algebraMap A _, h,
    RingHom.ext fun o => (hφ o).symm, fun x => ?_⟩
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors A) x
  exact ⟨a, b, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2, hab⟩

theorem exists_polyChart (K F V : Type) [Field K] [Field F] [Algebra K F] [Finite V] :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra K Ω) (_ : Algebra F Ω) (_ : IsScalarTower K F Ω) (x : V → Ω),
      ∀ (R₀ : Subalgebra K F) (R : Subalgebra K Ω),
        R = Algebra.adjoin K (algebraMap F Ω '' (R₀ : Set F) ∪ Set.range x) →
        (Algebra.Smooth K R₀ → Algebra.Smooth K R) ∧
        ((∀ y : F, ∃ a ∈ R₀, ∃ b ∈ R₀, b ≠ 0 ∧ y * b = a) → ∀ y : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ y * b = a) ∧
        ∀ (S : Type) [CommRing S] [Algebra K S] (ψ : R₀ →ₐ[K] S) (t : V → S), ∃! ψ' : R →ₐ[K] S,
          (∀ (a : R₀) (h : algebraMap F Ω a ∈ R), ψ' ⟨_, h⟩ = ψ a) ∧ ∀ (v : V) (h : x v ∈ R), ψ' ⟨_, h⟩ = t v :=
  ⟨FractionRing (MvPolynomial V F), inferInstance, inferInstance, inferInstance, inferInstance, _,
    GlobalTheory.polyChart_smooth_fraction_lift K F V⟩

set_option maxHeartbeats 400000 in
theorem exists_cell_algebra (K O A T : Type) [Field K] [CommRing O] [IsDomain O] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [IsDomain A] [Finite T] (α : O →+* A) (hft : α.FiniteType) (hinj : Function.Injective α)
    (es : Finset A) (hes : ∀ e ∈ es, e ≠ 0) (hne : es.Nonempty) (n : ℕ) (r : T → ℕ)
    (ix : ∀ τ, Fin (r τ) ↪ Fin n) (N : T → O) (hN : ∀ τ, N τ ≠ 0) (p : T → Matrix (Fin n) (Fin n) A)
    (hpp : ∀ (L : Type) [Field L] [Algebra K L] (f : A →+* L), f.comp α = (algebraMap K L).comp (algebraMap O K) →
      ∀ τ, (p τ).map f * (p τ).map f = f (α (N τ)) • (p τ).map f)
    (hrk : ∀ (L : Type) [Field L] [Algebra K L] (f : A →+* L), f.comp α = (algebraMap K L).comp (algebraMap O K) →
      ∀ e ∈ es, f e ≠ 0 → ∀ τ, ((p τ).map f).rank = r τ)
    (hsm : ∀ e ∈ es, ∀ (R : Type) [CommRing R] [Algebra K R] (f : A →+* R),
      f.comp α = (algebraMap K R).comp (algebraMap O K) → IsUnit (f e) → ∀ d : A, Function.Injective f →
      IsUnit (f d) → (∀ x : R, ∃ (a : A) (k : K) (m : ℕ), x * f (e * d) ^ m = algebraMap K R k * f a) →
      Algebra.Smooth K R)
    (κ₀ : ∀ τ, Fin (r τ) → Fin n) (hκ₀ : ∀ τ, ((p τ).submatrix (ix τ) (κ₀ τ)).det ≠ 0) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra K Ω) (gens es' : Finset Ω) (g : A →+* Ω)
      (u : ∀ τ, Matrix (Fin n) (Fin (r τ)) Ω),
      Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = ⊤ ∧ es'.Nonempty ∧
      (∀ e ∈ es', e ≠ 0 ∧
        e ∈ Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ (gens : Set Ω))) ∧
      (∀ a, g a ∈ Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ (gens : Set Ω))) ∧
      (∀ τ i j, u τ i j ∈ gens) ∧ (∀ x ∈ gens, (∃ a, x = g a) ∨ ∃ τ i j, x = u τ i j) ∧
      (∀ τ, InCell (ix τ) (u τ)) ∧
      (∀ e ∈ es', Algebra.Smooth K (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))) ∧
        ∃ (fe : A →+* Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)))
          (ue : ∀ τ, Matrix (Fin n) (Fin (r τ)) (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)))),
          (∀ a, (fe a : Ω) = g a) ∧ (∀ τ i j, (ue τ i j : Ω) = u τ i j) ∧
          fe.comp α = (algebraMap K _).comp (algebraMap O K) ∧ (∃ e₀ ∈ es, IsUnit (fe e₀)) ∧
          (∀ τ, (p τ).map fe * ue τ = fe (α (N τ)) • ue τ) ∧
          ∀ τ x, ((p τ).map fe).mulVec x = fe (α (N τ)) • x → ∃! a, (ue τ).mulVec a = x) ∧
      ∀ (L : Type) [Field L] [Algebra K L] (f : A →+* L), f.comp α = (algebraMap K L).comp (algebraMap O K) →
        ∀ e₀ ∈ es, f e₀ ≠ 0 → ∀ u' : ∀ τ, Matrix (Fin n) (Fin (r τ)) L,
        (∀ τ, (p τ).map f * u' τ = f (α (N τ)) • u' τ) → (∀ τ, InCell (ix τ) (u' τ)) →
        ∃ e ∈ es', ∃ ψ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) →ₐ[K] L,
          (∀ a (h : g a ∈ Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))), ψ ⟨g a, h⟩ = f a) ∧
          ∀ τ i j (h : u τ i j ∈ Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))), ψ ⟨u τ i j, h⟩ = u' τ i j := by
  classical
  haveI := Fintype.ofFinite T
  obtain ⟨F, _, _, i, hi, hiα, hfr⟩ := exists_fraction_field K O A α hinj
  obtain ⟨sA, hsA⟩ : ∃ sA : Finset A, ∀ a, a ∈ Subring.closure (Set.range α ∪ (sA : Set A)) := by
    letI := α.toAlgebra
    obtain ⟨s, hs⟩ := hft.out
    exact ⟨s, fun a => Algebra.mem_adjoin_iff.mp (hs ▸ Algebra.mem_top)⟩
  let V : Type := Σ τ, {q : Fin (r τ) × Fin (r τ) // q.2 < q.1}
  obtain ⟨Ω, _, _, _, _, x, hpoly⟩ := exists_polyChart K F V
  obtain ⟨g, hgi⟩ : ∃ g : A →+* Ω, ∀ a, g a = algebraMap F Ω (i a) := ⟨(algebraMap F Ω).comp i, fun _ => rfl⟩
  have hg : Function.Injective g := fun a b h => hi ((algebraMap F Ω).injective (by rw [← hgi, ← hgi, h]))
  have hg0 : ∀ a, a ≠ 0 → g a ≠ 0 := fun a ha => (map_ne_zero_iff g hg).mpr ha
  have hi0 : ∀ a, a ≠ 0 → i a ≠ 0 := fun a ha => (map_ne_zero_iff i hi).mpr ha
  have hgα : g.comp α = (algebraMap K Ω).comp (algebraMap O K) := by
    ext o
    have := RingHom.congr_fun hiα o
    simp only [RingHom.comp_apply] at this ⊢
    rw [hgi, this, ← IsScalarTower.algebraMap_apply]
  have hgα' : ∀ o, g (α o) = algebraMap K Ω (algebraMap O K o) := fun o => RingHom.congr_fun hgα o
  have hαN : ∀ τ, α (N τ) ≠ 0 := fun τ => (map_ne_zero_iff α hinj).mpr (hN τ)
  obtain ⟨e₁, he₁⟩ := hne
  have hrΩ : ∀ τ, ((p τ).map g).rank = r τ := hrk Ω g hgα e₁ he₁ (hg0 _ (hes _ he₁))
  have hdet : ∀ {B : Type} [CommRing B] (f : A →+* B) τ (κ : Fin (r τ) → Fin n),
      (((p τ).map f).submatrix (ix τ) κ).det = f ((p τ).submatrix (ix τ) κ).det := fun f τ κ =>
    (RingHom.map_det f ((p τ).submatrix (ix τ) κ)).symm
  let ℓ : ∀ τ, Matrix (Fin (r τ)) (Fin (r τ)) Ω := fun τ => genLower (fun a b h => (⟨τ, ⟨(a, b), h⟩⟩ : V)) x
  obtain ⟨u, hu1, hu2⟩ : ∃ u : ∀ τ, Matrix (Fin n) (Fin (r τ)) Ω, (∀ τ, (u τ).submatrix (ix τ) id = ℓ τ) ∧
      ∀ τ, (p τ).map g * u τ = g (α (N τ)) • u τ := by
    refine ⟨fun τ => ((p τ).map g).submatrix id (κ₀ τ) * (((p τ).map g).submatrix (ix τ) (κ₀ τ))⁻¹ * ℓ τ,
      fun τ => ?_, fun τ => ?_⟩
    · have : (((p τ).map g).submatrix id (κ₀ τ) * (((p τ).map g).submatrix (ix τ) (κ₀ τ))⁻¹ * ℓ τ).submatrix
          (ix τ) id = ((p τ).map g).submatrix (ix τ) (κ₀ τ) * (((p τ).map g).submatrix (ix τ) (κ₀ τ))⁻¹ * ℓ τ := rfl
      rw [this, Matrix.mul_nonsing_inv _ (by rw [hdet]; exact (hg0 _ (hκ₀ τ)).isUnit), Matrix.one_mul]
    · have : (p τ).map g * ((p τ).map g).submatrix id (κ₀ τ) =
          g (α (N τ)) • ((p τ).map g).submatrix id (κ₀ τ) :=
        congrArg (fun M => Matrix.submatrix M id (κ₀ τ)) (hpp Ω g hgα τ)
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, this, Matrix.smul_mul, Matrix.smul_mul]
  have hu1' : ∀ τ a b, u τ (ix τ a) b = ℓ τ a b := fun τ a b => congrFun (congrFun (hu1 τ) a) b
  have hcell : ∀ τ, InCell (ix τ) (u τ) := fun τ => ⟨fun a b hab => by
      rw [hu1']; simp [ℓ, genLower, hab.not_gt, hab.ne], fun a => by rw [hu1']; simp [ℓ, genLower]⟩
  have hux : ∀ τ a b (h : b < a), u τ (ix τ a) b = x ⟨τ, ⟨(a, b), h⟩⟩ := fun τ a b h => by
    rw [hu1']; simp [ℓ, genLower, h]
  obtain ⟨gens, hsg, hug, hgens⟩ : ∃ gens : Finset Ω, (∀ a ∈ sA, g a ∈ gens) ∧ (∀ τ a b, u τ a b ∈ gens) ∧
      ∀ y ∈ gens, (∃ a, y = g a) ∨ ∃ τ a b, y = u τ a b := by
    refine ⟨sA.image g ∪ Finset.univ.image (fun q : Σ τ, Fin n × Fin (r τ) => u q.1 q.2.1 q.2.2),
      fun a ha => Finset.mem_union_left _ (Finset.mem_image_of_mem g ha), fun τ a b =>
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨τ, a, b⟩, Finset.mem_univ _, rfl⟩), ?_⟩
    intro y hy
    rcases Finset.mem_union.mp hy with h | h
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp h
      exact Or.inl ⟨a, rfl⟩
    · obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp h
      exact Or.inr ⟨_, _, _, rfl⟩
  have hgB : ∀ a, g a ∈ Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ (gens : Set Ω)) := by
    intro a
    have : Subring.closure (Set.range α ∪ (sA : Set A)) ≤
        (Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ (gens : Set Ω))).comap g := by
      rw [Subring.closure_le]
      rintro w (⟨o, rfl⟩ | hw)
      · exact Subring.subset_closure (Or.inl ⟨o, (hgα' o).symm⟩)
      · exact Subring.subset_closure (Or.inr (hsg _ hw))
    exact this (hsA a)
  obtain ⟨d, hdd⟩ : ∃ d : (∀ τ, Fin (r τ) → Fin n) → A, ∀ κ, d κ = ∏ τ, ((p τ).submatrix (ix τ) (κ τ)).det :=
    ⟨_, fun _ => rfl⟩
  have hd : ∀ κ, d κ ≠ 0 ↔ ∀ τ, ((p τ).submatrix (ix τ) (κ τ)).det ≠ 0 := fun κ => by
    simp [hdd, Finset.prod_ne_zero_iff]
  obtain ⟨es', hes', hes''⟩ : ∃ es' : Finset Ω, (∀ e' ∈ es', ∃ e ∈ es, ∃ κ, d κ ≠ 0 ∧ e' = g (e * d κ)) ∧
      ∀ e ∈ es, ∀ κ, d κ ≠ 0 → g (e * d κ) ∈ es' := by
    refine ⟨(es ×ˢ Finset.univ.filter fun κ => d κ ≠ 0).image fun q => g (q.1 * d q.2), ?_, fun e he κ hκ =>
      Finset.mem_image.mpr ⟨(e, κ), Finset.mem_product.mpr
        ⟨he, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hκ⟩⟩, rfl⟩⟩
    intro e' he'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp he'
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hq
    exact ⟨q.1, h1, q.2, (Finset.mem_filter.mp h2).2, rfl⟩
  have hR : ∀ e ∈ es, ∀ κ, d κ ≠ 0 → Algebra.adjoin K (insert (g (e * d κ))⁻¹ (gens : Set Ω)) =
      Algebra.adjoin K (algebraMap F Ω '' (Algebra.adjoin K (insert (i (e * d κ))⁻¹ (Set.range i)) : Set F) ∪
        Set.range x) := by
    intro e he κ hκ
    refine adjoin_insert_eq (O := O) i g hgi (e * d κ) gens (Set.range x) hgB ?_ ?_
    · rintro _ ⟨⟨τ, ⟨a, b⟩, h⟩, rfl⟩
      rw [← hux τ a b h]
      exact hug _ _ _
    · set R' := Algebra.adjoin K (algebraMap F Ω '' (Algebra.adjoin K (insert (i (e * d κ))⁻¹ (Set.range i)) : Set F) ∪
        Set.range x) with hR'
      have hA : ∀ a, g a ∈ R' := fun a =>
        Algebra.subset_adjoin (Or.inl ⟨i a, Algebra.subset_adjoin (Or.inr ⟨a, rfl⟩), (hgi a).symm⟩)
      have hI : (g (e * d κ))⁻¹ ∈ R' :=
        Algebra.subset_adjoin (Or.inl ⟨(i (e * d κ))⁻¹, Algebra.subset_adjoin (Or.inl rfl), by rw [map_inv₀, hgi]⟩)
      intro y hy
      rcases hgens y hy with ⟨a, rfl⟩ | ⟨τ, a, b, rfl⟩
      · exact hA a
      · have hdτ := hg0 _ ((hd κ).mp hκ τ)
        rw [eq_of_rows _ (hrΩ τ) _ (hg0 _ (hαN τ)) (ix τ) (κ τ) (by rw [hdet]; exact hdτ) (u τ) (hu2 τ), hu1,
          Matrix.mul_apply]
        refine R'.sum_mem fun k _ => R'.mul_mem (mul_inv_mem R' (((p τ).map g).submatrix id (κ τ))
          (((p τ).map g).submatrix (ix τ) (κ τ)) (fun _ _ => hA _) (fun _ _ => hA _) ?_ _ _) ?_
        · obtain ⟨w, hw⟩ : ((p τ).submatrix (ix τ) (κ τ)).det ∣ e * d κ :=
            Dvd.dvd.mul_left (hdd κ ▸ Finset.dvd_prod_of_mem _ (Finset.mem_univ τ)) e
          have hw0 : g w ≠ 0 := hg0 _ fun h => mul_ne_zero (hes e he) hκ (by rw [hw, h, mul_zero])
          have : (g ((p τ).submatrix (ix τ) (κ τ)).det)⁻¹ = (g (e * d κ))⁻¹ * g w := by
            rw [hw, map_mul]; field_simp
          rw [hdet, this]
          exact R'.mul_mem hI (hA w)
        · simp only [ℓ, genLower]
          split_ifs
          · exact Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩)
          · exact R'.one_mem
          · exact R'.zero_mem
  have hP := fun e he κ hκ => hpoly _ _ (hR e he κ hκ)
  have hAR : ∀ e' a, g a ∈ Algebra.adjoin K (insert e' (gens : Set Ω)) := by
    intro e' a
    have : Subring.closure (Set.range ((algebraMap K Ω).comp (algebraMap O K)) ∪ (gens : Set Ω)) ≤
        (Algebra.adjoin K (insert e' (gens : Set Ω))).toSubring := by
      rw [Subring.closure_le]
      rintro w (⟨o, rfl⟩ | hw)
      · exact Subalgebra.algebraMap_mem _ _
      · exact Algebra.subset_adjoin (Or.inr hw)
    exact this (hgB a)
  have hA₀ : ∀ a₀ a, i a ∈ Algebra.adjoin K (insert a₀ (Set.range i)) := fun a₀ a =>
    Algebra.subset_adjoin (Or.inr ⟨a, rfl⟩)
  have hκ₀' := (hd κ₀).mpr hκ₀
  refine ⟨Ω, inferInstance, inferInstance, gens, es', g, u, ?_, ⟨_, hes'' e₁ he₁ κ₀ hκ₀'⟩, ?_, hgB, hug, hgens,
    hcell, ?_, ?_⟩
  · rw [eq_top_iff]
    intro y _
    obtain ⟨a, ha, b, hb, hb0, hab⟩ := (hP e₁ he₁ κ₀ hκ₀').2.1 (fun z => by
      obtain ⟨a, b, h1, h2⟩ := hfr z
      exact ⟨i a, hA₀ _ a, i b, hA₀ _ b, h1, h2⟩) y
    have hle : ∀ z ∈ Algebra.adjoin K (insert (g (e₁ * d κ₀))⁻¹ (gens : Set Ω)),
        z ∈ Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) := by
      intro z hz
      rw [Algebra.mem_adjoin_iff] at hz
      refine (Subring.closure_le (t := (Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω))).toSubring)).mpr
        ?_ hz
      rintro w (hw | rfl | hw)
      · exact Subfield.subset_closure (Or.inl hw)
      · refine Subfield.inv_mem _ ((Subring.closure_le
          (t := (Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω))).toSubring)).mpr ?_ (hgB _))
        rintro w (⟨o, rfl⟩ | hw)
        · exact Subfield.subset_closure (Or.inl ⟨_, rfl⟩)
        · exact Subfield.subset_closure (Or.inr hw)
      · exact Subfield.subset_closure (Or.inr hw)
    rw [eq_div_of_mul_eq hb0 hab]
    exact Subfield.div_mem _ (hle a ha) (hle b hb)
  · intro e' he'
    obtain ⟨e, he, κ, hκ, rfl⟩ := hes' e' he'
    exact ⟨hg0 _ (mul_ne_zero (hes e he) hκ), hgB _⟩
  · intro e' he'
    obtain ⟨e, he, κ, hκ, rfl⟩ := hes' e' he'
    have hed := mul_ne_zero (hes e he) hκ
    constructor
    · refine (hP e he κ hκ).1 ?_
      set R₀ := Algebra.adjoin K (insert (i (e * d κ))⁻¹ (Set.range i)) with hR₀
      let i₀ : A →+* R₀ := i.codRestrict R₀.toSubring (hA₀ _)
      have hi₀ : ∀ o, i₀ (α o) = algebraMap K R₀ (algebraMap O K o) := fun o =>
        Subtype.ext (RingHom.congr_fun hiα o)
      have hun : IsUnit (i₀ e * i₀ (d κ)) := by
        rw [← map_mul]
        exact IsUnit.of_mul_eq_one (⟨(i (e * d κ))⁻¹, Algebra.subset_adjoin (Or.inl rfl)⟩ : R₀)
          (Subtype.ext (mul_inv_cancel₀ (hi0 _ hed)))
      refine hsm e he R₀ i₀ (RingHom.ext hi₀) (isUnit_of_mul_isUnit_left hun) (d κ)
        (fun a b h => hi (congrArg Subtype.val h)) (isUnit_of_mul_isUnit_right hun) fun z => ?_
      obtain ⟨a, b, m, hb, h⟩ := loc_descr α i hiα (e * d κ) (hi0 _ hed) z z.2
      have hb' : algebraMap O K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr hb
      refine ⟨a, (algebraMap O K b)⁻¹, m, ?_⟩
      have h' : z * i₀ (α b * (e * d κ) ^ m) = i₀ a := Subtype.ext h
      rw [← h', map_mul i₀ (α b), hi₀, map_pow]
      have : algebraMap K R₀ (algebraMap O K b)⁻¹ * algebraMap K R₀ (algebraMap O K b) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hb', map_one]
      linear_combination (-(z * i₀ (e * d κ) ^ m)) * this
    · set R := Algebra.adjoin K (insert (g (e * d κ))⁻¹ (gens : Set Ω)) with hRdef
      let fe : A →+* R := g.codRestrict R.toSubring (hAR _)
      let ue : ∀ τ, Matrix (Fin n) (Fin (r τ)) R := fun τ a b =>
        ⟨u τ a b, Algebra.subset_adjoin (Or.inr (hug τ a b))⟩
      have hun : IsUnit (fe e * fe (d κ)) := by
        rw [← map_mul]
        exact IsUnit.of_mul_eq_one (⟨(g (e * d κ))⁻¹, Algebra.subset_adjoin (Or.inl rfl)⟩ : R)
          (Subtype.ext (mul_inv_cancel₀ (hg0 _ hed)))
      have hpu : ∀ τ, (p τ).map fe * ue τ = fe (α (N τ)) • ue τ := by
        intro τ
        ext a b
        have := congrFun (congrFun (hu2 τ) a) b
        simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
        rw [AddSubmonoidClass.coe_finset_sum]
        exact this
      refine ⟨fe, ue, fun _ => rfl, fun _ _ _ => rfl, RingHom.ext fun o => Subtype.ext (hgα' o),
        ⟨e, he, isUnit_of_mul_isUnit_left hun⟩, hpu, fun τ y hy => ?_⟩
      have hmap : ((p τ).map fe).map R.val = (p τ).map g := by
        ext a b
        rfl
      refine basis_over_subalgebra R (ix τ) (κ τ) ((p τ).map fe) (fe (α (N τ)))
        (fun h => hg0 _ (hαN τ) (congrArg Subtype.val h)) (by rw [hmap]; exact hrΩ τ)
        ?_ (ue τ) (hpu τ) ⟨fun a b h => Subtype.ext ((hcell τ).1 a b h), fun a => Subtype.ext ((hcell τ).2 a)⟩ y hy
      rw [hmap, hdet]
      exact hg0 _ ((hd κ).mp hκ τ)
  · intro L _ _ f hf e he hfe u' hu' hc'
    have hf' : ∀ o, f (α o) = algebraMap K L (algebraMap O K o) := fun o => RingHom.congr_fun hf o
    have hfN : ∀ τ, f (α (N τ)) ≠ 0 := fun τ => by
      rw [hf']
      exact (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr (hN τ))
    choose κ hκL using fun τ => exists_minor _ _ (hfN τ) (ix τ) (u' τ) (hu' τ) (hc' τ)
    have hfd : f (d κ) ≠ 0 := by
      simp only [hdd, map_prod, Finset.prod_ne_zero_iff]
      exact fun τ _ => hdet f τ (κ τ) ▸ hκL τ
    have hκ : d κ ≠ 0 := fun h => hfd (by rw [h, map_zero])
    have hed := mul_ne_zero (hes e he) hκ
    obtain ⟨ψ₀, hψ₀⟩ := loc_lift α i hi hiα (e * d κ) (hi0 _ hed) f hf (by rw [map_mul]; exact mul_ne_zero hfe hfd)
    obtain ⟨ψ, ⟨hψ1, hψ2⟩, -⟩ := (hP e he κ hκ).2.2 L ψ₀ (fun v => u' v.1 (ix v.1 v.2.1.1) v.2.1.2)
    have hψA : ∀ a (h : g a ∈ Algebra.adjoin K (insert (g (e * d κ))⁻¹ (gens : Set Ω))), ψ ⟨g a, h⟩ = f a :=
      fun a h => (congrArg ψ (Subtype.ext (hgi a))).trans
        ((hψ1 ⟨i a, hA₀ _ a⟩ (by rw [← hgi a]; exact h)).trans (hψ₀ a _))
    refine ⟨_, hes'' e he κ hκ, ψ, hψA, fun τ a b h => ?_⟩
    let R := Algebra.adjoin K (insert (g (e * d κ))⁻¹ (gens : Set Ω))
    let ue : Matrix (Fin n) (Fin (r τ)) R := fun a b => ⟨u τ a b, Algebra.subset_adjoin (Or.inr (hug τ a b))⟩
    have hpu : (p τ).map f * ue.map ψ = f (α (N τ)) • ue.map ψ := by
      ext a b
      have h0 := congrFun (congrFun (hu2 τ) a) b
      simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at h0 ⊢
      have h1 : ∑ j, (⟨g (p τ a j), hAR _ _⟩ : R) * ue j b = (⟨g (α (N τ)), hAR _ _⟩ : R) * ue a b := by
        apply Subtype.ext
        rw [AddSubmonoidClass.coe_finset_sum]
        exact h0
      have h2 := congrArg ψ h1
      rw [map_sum ψ, map_mul ψ ⟨g (α (N τ)), _⟩, hψA] at h2
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h2
      rw [map_mul ψ, hψA]
      rfl
    have hrow : (ue.map ψ).submatrix (ix τ) id = (u' τ).submatrix (ix τ) id := by
      ext a b
      show ψ (ue (ix τ a) b) = u' τ (ix τ a) b
      rcases lt_trichotomy a b with h | rfl | h
      · rw [(hc' τ).1 a b h, show ue (ix τ a) b = 0 from Subtype.ext ((hcell τ).1 a b h), map_zero]
      · rw [(hc' τ).2 a, show ue (ix τ a) a = 1 from Subtype.ext ((hcell τ).2 a), map_one]
      · have hm : x ⟨τ, ⟨(a, b), h⟩⟩ ∈ R := hux τ a b h ▸ (ue (ix τ a) b).2
        rw [show ue (ix τ a) b = ⟨x ⟨τ, ⟨(a, b), h⟩⟩, hm⟩ from Subtype.ext (hux τ a b h)]
        exact hψ2 ⟨τ, ⟨(a, b), h⟩⟩ hm
    have e1 := eq_of_rows _ (hrk L f hf e he hfe τ) _ (hfN τ) (ix τ) (κ τ) (hκL τ) _ hpu
    have e2 := eq_of_rows _ (hrk L f hf e he hfe τ) _ (hfN τ) (ix τ) (κ τ) (hκL τ) _ (hu' τ)
    rw [hrow, ← e2] at e1
    exact congrFun (congrFun e1 a) b

end GlobalTheory.Reg.CellChart
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedPoint_vectors_integral_in_cell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin M.n) (u₀ : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) T.V), (∀ τ, InCell (ix τ) (u₀ τ)) → letI := io.toAlgebra; ∀ (z : FrPt Xo c T.Fr) (Λ : M.Lift ((algebraMap T.V T.Fr).comp f₀) z.x), Λ.LieTie (fun τ => (u₀ τ).map (algebraMap T.V T.Fr)) z.u → ∀ (G : SAB H (Sp T.V)) (m : SABMap G Y.t (spMap f₀ ≫ M.hU.fromSpec)) (m2 : SABMap Λ.t' G (spMap (algebraMap T.V T.Fr))), m2.φ ≫ m.φ = Λ.m2.φ → ∃ ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G), (∀ τ i, IsTan (ub τ i)) ∧ (∀ τ i, IsEigV c io G τ (ub τ i)) ∧ (∀ τ (w : epsOver T.V T.V ⟶ G.G), IsTan w → IsEigV c io G τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub τ) a w) ∧ ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ Λ.t'.G.left, u' ≫ Λ.m1.φ = z.u τ i ∧ u' ≫ m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub τ i).left := by
  first | exact @GlobalTheory.Reg.tie_vectors_integral | exact GlobalTheory.Reg.tie_vectors_integral | (intros; apply GlobalTheory.Reg.tie_vectors_integral <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralGenerator_of_chartPoint_cdvr : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V), letI := io.toAlgebra; ∀ (x : Sp T.Fr ⟶ Xo.X) (s : LB.Sec (PPx x)) (Λ : M.Lift ((algebraMap T.V T.Fr).comp f₀) x), Λ.ThTie s → ∀ (G : SAB H (Sp T.V)) (m : SABMap G Y.t (spMap f₀ ≫ M.hU.fromSpec)) (m2 : SABMap Λ.t' G (spMap (algebraMap T.V T.Fr))), m2.φ ≫ m.φ = Λ.m2.φ → ∃ θ : LB.Sec G.PP.L, (∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G.G.left (le_top : G.PP.L.U i ≤ ⊤) ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) ∧ ∃ (w1 : LB.Iso Λ.t'.PP.L (Xo.univ.t.PP.L.pull Λ.m1.φ)) (w2 : LB.Iso Λ.t'.PP.L (G.PP.L.pull m2.φ)) (σ : LB.Sec Λ.t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull Λ.m1.φ)) (θ2 : LB.Sec (G.PP.L.pull m2.φ)), RigIso Λ.m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec m2.φ θ θ2 ∧ ∀ g : Λ.t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = Λ.m1.φ → g ≫ (fst (Over.mk x) Xo.univ.t.G).left = Λ.t'.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull Λ.m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit)) := by
  first | exact @GlobalTheory.Reg.exists_generator_of_thTie | exact GlobalTheory.Reg.exists_generator_of_thTie | (intros; apply GlobalTheory.Reg.exists_generator_of_thTie <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem tie_integral : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin M.n) (u₀ : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) T.V), (∀ τ, InCell (ix τ) (u₀ τ)) → letI := io.toAlgebra; ∀ z : FrPt Xo c T.Fr, M.Comparison₂ ((algebraMap T.V T.Fr).comp f₀) (fun τ => (u₀ τ).map (algebraMap T.V T.Fr)) z → Integral T io z := by
  intro hS E _ _ _ H Dw l Xo c O _ β Y M hP T io f₀ ix u₀ hu
  letI := io.toAlgebra
  intro z ⟨Λ, hL, hT⟩
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap f₀ ≫ M.hU.fromSpec) Y.t
  have e : spMap ((algebraMap T.V T.Fr).comp f₀) ≫ M.hU.fromSpec =
      spMap (algebraMap T.V T.Fr) ≫ spMap f₀ ≫ M.hU.fromSpec := by
    rw [← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp]
    rfl
  have key : ∀ (g : Sp T.Fr ⟶ Y.X) (n : SABMap Λ.t' Y.t g),
      g = spMap (algebraMap T.V T.Fr) ≫ spMap f₀ ≫ M.hU.fromSpec →
      ∃ m2 : SABMap Λ.t' _ (spMap (algebraMap T.V T.Fr)), m2.φ ≫ m.φ = n.φ := by
    intro g n hg
    subst hg
    obtain ⟨m2, h⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m n
    exact ⟨m2, h.symm⟩
  obtain ⟨m2, h2⟩ := key _ Λ.m2 e
  exact ⟨_, Λ.t', Λ.m1, m2,
    GlobalTheory.T.framedPoint_vectors_integral_in_cell E H Dw l Xo c O β Y M T io f₀ ix u₀ hu z Λ hL _ m m2 h2,
    GlobalTheory.T.exists_integralGenerator_of_chartPoint_cdvr hS E H Dw l Xo c O β Y M hP T io f₀ z.x z.s Λ hT _ m m2 h2⟩

end GlobalTheory.Reg
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem triangular_inv_of_diag_ne {L : Type} [Field L] {n : ℕ} (b : Matrix (Fin n) (Fin n) L)
    (hb : b.BlockTriangular id) (hd : ∀ i, b i i ≠ 0) :
    b * b⁻¹ = 1 ∧ (b⁻¹).BlockTriangular id ∧ ∀ i, b⁻¹ i i ≠ 0 := by

  have hdet : IsUnit b.det := by
    rw [Matrix.det_of_isUpperTriangular hb]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => hd i)
  let _ : Invertible b := Matrix.invertibleOfIsUnitDet b hdet
  have htri : (b⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hb
  refine ⟨Matrix.mul_nonsing_inv b hdet, htri, fun i => ?_⟩

  have hii : (b⁻¹ * b) i i = b⁻¹ i i * b i i := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun k _ hki => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rcases lt_or_gt_of_ne hki with h | h
    · rw [htri h, zero_mul]
    · rw [hb h, mul_zero]
  rw [Matrix.nonsing_inv_mul b hdet, Matrix.one_apply_eq] at hii
  exact left_ne_zero_of_mul_eq_one hii.symm

theorem scal_mul_tie {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a a' : S) (i : (PPx x).ι) :
    scal x (a * a') i = scal x a i * scal x a' i := by
  simp only [scal, map_mul, Out.liftFun]

theorem scal_one_tie {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) :
    scal x 1 i = 1 := by
  simp only [scal, map_one, Out.liftFun]

theorem frBor_of_tie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L) (y z : FrPt Xo c L) (Λ : M.Lift f y.x) (u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) L) (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) L), z.x = y.x → (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) → Λ.LieTie (fun τ => u τ * b τ) y.u → M.Comparison₂ f u z → ∃ t : Ix Dw → Lˣ, FrBor t y z := by
  intro E _ _ _ H Dw l Xo c O _ β Y M L _ _ f y z Λ u b hxz hb hΛ hM
  obtain ⟨zx, zo, zu, zt, ze, zb, zs, zg⟩ := z
  subst hxz
  obtain ⟨Λ', hΛ'u, -⟩ := hM

  have hB : ∀ τ, b τ * (b τ)⁻¹ = 1 ∧ ((b τ)⁻¹).BlockTriangular id ∧ ∀ i, (b τ)⁻¹ i i ≠ 0 :=
    fun τ => triangular_inv_of_diag_ne (b τ) (hb τ).1 (hb τ).2

  obtain ⟨a, ha, -⟩ := y.gen zs
  obtain ⟨a', ha', -⟩ := zg y.s
  obtain ⟨w, -, huniq⟩ := zg zs
  have h1 : ∀ i, zs.f i = scal y.x (a * a') i * zs.f i := fun i => by
    rw [scal_mul_tie, _root_.mul_assoc, ← ha' i, ← ha i]
  have h2 : ∀ i, zs.f i = scal y.x 1 i * zs.f i := fun i => by
    rw [scal_one_tie, _root_.one_mul]
  have haa : a * a' = 1 := (huniq _ h1).trans (huniq _ h2).symm
  refine ⟨fun k => Option.elim k (Units.mkOfMulEqOne a a' haa)
    (fun p => Units.mk0 ((b p.1)⁻¹ p.2 p.2) ((hB p.1).2.2 p.2)), ?_⟩
  unfold FrBor
  refine ⟨rfl, fun τ i => ⟨fun j => (b τ)⁻¹ j i, rfl, fun j hij => (hB τ).2.1 hij, ?_⟩,
    𝟙 _, Category.id_comp _, Category.id_comp _, fun i h => ?_⟩
  ·
    refine (GlobalTheory.T.isCombAt_iff_coordinate_combination E H Dw l Xo c O β Y M L f y.x Λ (Dw.mult τ) (fun j k => (u τ * b τ) k j)
      (y.u τ) (fun j => (b τ)⁻¹ j i) (zu τ i) (fun j => hΛ τ j)).mpr ?_
    have hv := (GlobalTheory.T.modelChartLift_coords_generator_indep E H Dw l Xo c O β Y M L f y.x Λ' Λ).1 _ _ (hΛ'u τ i)
    convert hv using 1
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc ∑ j, (b τ)⁻¹ j i * (u τ * b τ) k j = (u τ * b τ * (b τ)⁻¹) k i := by
          rw [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun j _ => _root_.mul_comm _ _
      _ = u τ k i := by rw [Matrix.mul_assoc, (hB τ).1, Matrix.mul_one]
  ·
    have e : homOfLE h = 𝟙 _ := Subsingleton.elim _ _
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, e, Option.elim_none, Units.val_mkOfMulEqOne]
    erw [op_id, CategoryTheory.Functor.map_id, Category.comp_id, CommRingCat.hom_id, RingHom.id_apply]
    exact (ha i).symm

end GlobalTheory.Reg
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.CellChart

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {M : MChart Y}

theorem lift_point_unique {R : Type} [CommRing R] [Algebra c.F R] {f : Γ(Y.X, M.U) →+* R} {x x' : Sp R ⟶ Xo.X}
    (Λ : M.Lift f x) (Λ' : M.Lift f x') : x = x' := by
  haveI := Y.jQ_open
  have h : Λ.xF = Λ'.xF := by
    rw [← cancel_mono Y.jQ]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]
      exact Λ.xF_j.trans Λ'.xF_j.symm
    · rw [Category.assoc, Category.assoc, Y.jQ_over]
      exact Λ.xF_snd.trans Λ'.xF_snd.symm
  rw [← Λ.xF_fst, h, Λ'.xF_fst]

theorem tie_unique {L : Type} [Field L] [Algebra c.F L] {f : Γ(Y.X, M.U) →+* L}
    {u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) L} {y z : FrPt Xo c L} (hy : M.Comparison₂ f u y)
    (hz : M.Comparison₂ f u z) : y = z :=
  GlobalTheory.Reg.TieUniq.frPt_eq_of_tie E H Dw l Xo c O β Y M L f u y z hy hz (lift_point_unique hy.choose hz.choose)

theorem tie_congr {R : Type} [CommRing R] [Algebra c.F R] {f f' : Γ(Y.X, M.U) →+* R}
    {u u' : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) R} {y : FrPt Xo c R} (hy : M.Comparison₂ f u y)
    (hf : ∀ a, f a = f' a) (hu : ∀ τ i j, u τ i j = u' τ i j) : M.Comparison₂ f' u' y := by
  obtain rfl : f = f' := RingHom.ext hf
  obtain rfl : u = u' := funext fun τ => Matrix.ext (hu τ)
  exact hy

end

theorem mul_eq_smul_iff_cols {R : Type} [CommRing R] {n r : ℕ} (P : Matrix (Fin n) (Fin n) R) (N : R)
    (u : Matrix (Fin n) (Fin r) R) : P * u = N • u ↔ ∀ i, P.mulVec (fun j => u j i) = N • fun j => u j i :=
  ⟨fun h i => funext fun j => congrFun (congrFun h j) i, fun h => Matrix.ext fun j i => congrFun (h i) j⟩

end GlobalTheory.Reg.CellChart

namespace GlobalTheory.Reg

open GlobalTheory.Reg.CellChart in

theorem exists_pChart_of_cell : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FrBC Xo c → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O c.F] [IsFractionRing O c.F] (Y : Model Xo c (algebraMap O c.F)), PushInvertible Y.t.G Y.t.PP.L → ∀ (M : MChart Y) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin M.n), ∃ (J : Type) (_ : Finite J) (P : J → PChart Xo c (algebraMap O c.F)), ∀ (L : Type) [Field L] [Algebra c.F L] (W : ValuationSubring L) (f : Γ(Y.X, M.U) →+* L) (y : FrPt Xo c L) (Λ : M.Lift f y.x) (u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) L) (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) L), (∀ a, f a ∈ W) → (∀ τ i j, u τ i j ∈ W) → (∀ τ, InCell (ix τ) (u τ)) → (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) → Λ.LieTie (fun τ => u τ * b τ) y.u → ∃ j, (P j).Catches W y := by
  intro hS E _ _ _ H Dw l Xo c hbc O _ _ _ _ _ Y hpush M ix
  haveI := M.dom
  obtain ⟨α, es, -, hft, hinj, hne, hes, hop, hpt⟩ := GlobalTheory.Reg.ChartOpens.moduli_basicOpens E H Dw l Xo c O Y M
  obtain ⟨ρ, hρ⟩ := GlobalTheory.Reg.MChart.exists_ringHom_rho E H Dw l Xo c O _ Y M
  have hemb : Function.Injective (embF (E := E) c) := fun τ τ' h =>
    RingHom.ext fun a => congrArg Subtype.val (RingHom.congr_fun h a)
  choose N p hN hp using exists_projector E c.F (embF c) hemb O Γ(Y.X, M.U) α M.n ρ
  have heig : ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R),
      f.comp α = (algebraMap c.F R).comp (algebraMap O c.F) → ∀ τ x,
        M.Eig f τ x ↔ ((p τ).map f).mulVec x = f (α (N τ)) • x := by
    intro R _ _ f hf τ x
    rw [← (hp τ R f hf).2 x]
    simp only [hρ]
    rfl
  have hfN : ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L),
      f.comp α = (algebraMap c.F L).comp (algebraMap O c.F) → ∀ τ, f (α (N τ)) ≠ 0 := by
    intro L _ _ f hf τ
    rw [show f (α (N τ)) = algebraMap c.F L (algebraMap O c.F (N τ)) from RingHom.congr_fun hf _]
    exact (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective O c.F)).mpr (hN τ))
  have hlift : ∀ e ∈ es, ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R),
      f.comp α = (algebraMap c.F R).comp (algebraMap O c.F) → IsUnit (f e) → ∃ x, Nonempty (M.Lift f x) := by
    intro e he R _ _ f hf hu
    obtain ⟨xF, h1, h2⟩ := (hop e he R f hf hu).1
    exact ⟨_, MChart.nonempty_lift E H Dw l Xo c O _ Y M R f xF h1 h2⟩
  have hrk : ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L),
      f.comp α = (algebraMap c.F L).comp (algebraMap O c.F) →
      ∀ e ∈ es, f e ≠ 0 → ∀ τ, ((p τ).map f).rank = Dw.mult τ := by
    intro L _ _ f hf e he hfe τ
    obtain ⟨x, ⟨Λ⟩⟩ := hlift e he L f hf hfe.isUnit
    let S : Submodule L (Fin M.n → L) := Module.End.eigenspace ((p τ).map f).mulVecLin (f (α (N τ)))
    have hS' : ∀ y, y ∈ S ↔ ((p τ).map f).mulVec y = f (α (N τ)) • y := fun y => Module.End.mem_eigenspace_iff
    rw [rank_of_quasi_idem _ _ (hfN L f hf τ) (hp τ L f hf).1 S hS']
    exact GlobalTheory.Reg.finrank_chart_eig E H Dw l Xo c O _ Y M L f x Λ τ S fun y => (hS' y).trans (heig L f hf τ y).symm
  have hpoint : ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L) (y : FrPt Xo c L)
      (Λ : M.Lift f y.x) (u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) L)
      (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) L),
      (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) → Λ.LieTie (fun τ => u τ * b τ) y.u →
      f.comp α = (algebraMap c.F L).comp (algebraMap O c.F) ∧ (∃ e ∈ es, f e ≠ 0) ∧
        ∀ τ, (p τ).map f * u τ = f (α (N τ)) • u τ := by
    intro L _ _ f y Λ u b hb ht
    obtain ⟨hf, he⟩ := hpt L f Λ.xF Λ.xF_snd Λ.xF_j
    refine ⟨hf, he, fun τ => ?_⟩
    have h1 : (p τ).map f * (u τ * b τ) = f (α (N τ)) • (u τ * b τ) :=
      (mul_eq_smul_iff_cols _ _ _).mpr fun i => (heig L f hf τ _).mp
        ((GlobalTheory.Reg.isEigAt_iff_eig E H Dw l Xo c O _ Y M L f y.x Λ τ _ _ (ht τ i)).mp (y.eig τ i))
    have hd : IsUnit (b τ).det := by
      rw [Matrix.det_of_upperTriangular (hb τ).1]
      exact (Finset.prod_ne_zero_iff.mpr fun i _ => (hb τ).2 i).isUnit
    have h2 := congrArg (· * (b τ)⁻¹) h1
    simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one] at h2
    exact h2
  by_cases hκ : ∃ κ₀ : ∀ τ, Fin (Dw.mult τ) → Fin M.n, ∀ τ, ((p τ).submatrix (ix τ) (κ₀ τ)).det ≠ 0
  swap
  · refine ⟨Empty, inferInstance, Empty.elim, fun L _ _ W f y Λ u b _ _ hc hb ht => (hκ ?_).elim⟩
    obtain ⟨hf, -, hu⟩ := hpoint L f y Λ u b hb ht
    choose κ hκL using fun τ => exists_minor _ _ (hfN L f hf τ) (ix τ) (u τ) (hu τ) (hc τ)
    refine ⟨κ, fun τ h => hκL τ ?_⟩
    have := RingHom.map_det f ((p τ).submatrix (ix τ) (κ τ))
    rw [h, map_zero] at this
    exact this.symm
  obtain ⟨κ₀, hκ₀⟩ := hκ
  obtain ⟨Ω, _, _, gens, es', g, u, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    exists_cell_algebra c.F O Γ(Y.X, M.U) (E →+* ℂ) α hft hinj es hes hne M.n Dw.mult ix N hN p
      (fun L _ _ f hf τ => (hp τ L f hf).1) hrk (fun e he R _ _ f hf hu => (hop e he R f hf hu).2) κ₀ hκ₀
  choose hsm fe ue k1 k2 k3 k4 k5 k6 using h8
  have hy : ∀ e (he : e ∈ es'), ∃ y : FrPt Xo c (Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω))),
      M.Comparison₂ (fe e he) (ue e he) y := by
    intro e he
    obtain ⟨e₀, he₀, hu⟩ := k4 e he
    obtain ⟨x, ⟨Λ⟩⟩ := hlift e₀ he₀ _ (fe e he) (k3 e he) hu
    obtain ⟨y, -, hy⟩ := GlobalTheory.Reg.exists_frPt_tie hS E H Dw l Xo c O _ Y M _ (fe e he) x Λ (ue e he)
      (fun τ i => (heig _ _ (k3 e he) τ _).mpr ((mul_eq_smul_iff_cols _ _ _).mp (k5 e he τ) i))
      (fun τ cv h => k6 e he τ cv ((heig _ _ (k3 e he) τ _).mp h))
    exact ⟨y, hy⟩
  choose yy hyy using hy
  have hgen : ∀ e (he : e ∈ es') z, FrMap (Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω))).val (yy e he) z →
      M.Comparison₂ g u z := fun e he z hz =>
    tie_congr (GlobalTheory.Reg.MChart.tie_baseChange E H Dw l Xo c O _ Y M _ _ _ _ _ _ _ (hyy e he) hz) (k1 e he) (k2 e he)
  obtain ⟨e₁, he₁⟩ := id h2
  obtain ⟨yg, hyg⟩ := hbc _ _ (Algebra.adjoin c.F (insert e₁⁻¹ (gens : Set Ω))).val (yy e₁ he₁)
  have hint : ∀ e (he : e ∈ es') (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra
      ∀ (ψ : Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω)) →ₐ[c.F] T.Fr),
        (∀ a : O, io (algebraMap O c.F a) ∈ Set.range (algebraMap T.V T.Fr)) →
        (∀ w : Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω)), (w : Ω) ∈ gens →
          ψ w ∈ Set.range (algebraMap T.V T.Fr)) →
        ∀ z : FrPt Xo c T.Fr, FrMap ψ (yy e he) z → Integral T io z := by
    intro e he T io
    letI := io.toAlgebra
    intro ψ hO hg z hz
    have hVinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
    have hB : ∀ w ∈ Subring.closure (Set.range ((algebraMap c.F Ω).comp (algebraMap O c.F)) ∪ (gens : Set Ω)),
        w ∈ (((algebraMap T.V T.Fr).range.comap ψ.toRingHom).map
          (Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω))).val.toRingHom) := by
      intro w hw
      refine (Subring.closure_le.mpr ?_) hw
      rintro w (⟨o, rfl⟩ | hw)
      · refine ⟨algebraMap c.F _ (algebraMap O c.F o), ?_, rfl⟩
        obtain ⟨v, hv⟩ := hO o
        exact ⟨v, hv.trans (ψ.commutes _).symm⟩
      · exact ⟨⟨w, Algebra.subset_adjoin (Or.inr hw)⟩, hg _ hw, rfl⟩
    have hfa : ∀ a, ψ.toRingHom.comp (fe e he) a ∈ (algebraMap T.V T.Fr).range := by
      intro a
      obtain ⟨w, hw, hw'⟩ := hB _ (h4 a)
      obtain rfl : w = fe e he a := Subtype.ext (hw'.trans (k1 e he a).symm)
      exact hw
    let φ := (algebraMap T.V T.Fr).rangeRestrict
    let ε : T.V ≃+* (algebraMap T.V T.Fr).range := RingEquiv.ofBijective φ
      ⟨fun a b h => hVinj (congrArg Subtype.val h), (algebraMap T.V T.Fr).rangeRestrict_surjective⟩
    let f₀ : Γ(Y.X, M.U) →+* T.V := ε.symm.toRingHom.comp ((ψ.toRingHom.comp (fe e he)).codRestrict _ hfa)
    have hf₀ : ∀ a, algebraMap T.V T.Fr (f₀ a) = ψ (fe e he a) := fun a =>
      congrArg Subtype.val (ε.apply_symm_apply ⟨_, hfa a⟩)
    choose u₀ hu₀ using fun τ i j => hg (ue e he τ i j) (by rw [k2]; exact h5 τ i j)
    refine GlobalTheory.Reg.tie_integral hS E H Dw l Xo c O _ Y M hpush T io f₀ ix u₀ (fun τ => ⟨fun i j hij => hVinj ?_,
      fun i => hVinj ?_⟩) z (tie_congr (GlobalTheory.Reg.MChart.tie_baseChange E H Dw l Xo c O _ Y M _ _ _ _ _ _ _ (hyy e he) hz)
        (fun a => (hf₀ a).symm) fun τ i j => (hu₀ τ i j).symm)
    · rw [hu₀, show ue e he τ (ix τ i) j = 0 from Subtype.ext ((k2 e he τ _ _).trans ((h7 τ).1 i j hij)),
        map_zero, map_zero]
    · rw [hu₀, show ue e he τ (ix τ i) i = 1 from Subtype.ext ((k2 e he τ _ _).trans ((h7 τ).2 i)),
        map_one, map_one]
  let P : PChart Xo c (algebraMap O c.F) :=
    { Ω := Ω, gens := gens, frac := h1, es := es', es_ne := h2, es_mem := h3, sm := hsm, yg := yg, y := yy
      gen := fun e he => by
        obtain ⟨z, hz⟩ := hbc _ _ (Algebra.adjoin c.F (insert e⁻¹ (gens : Set Ω))).val (yy e he)
        rw [tie_unique (hgen _ _ _ hyg) (hgen _ _ _ hz)]
        exact hz
      int := hint }
  refine ⟨Unit, inferInstance, fun _ => P, fun L _ _ W f y Λ u' b hW hW' hc hb ht => ⟨(), ?_⟩⟩
  obtain ⟨hf, ⟨e₀, he₀, hfe⟩, hu⟩ := hpoint L f y Λ u' b hb ht
  obtain ⟨e, he, ψ, hψ1, hψ2⟩ := h9 L f hf e₀ he₀ hfe u' hu hc
  obtain ⟨z, hz⟩ := hbc _ _ ψ (yy e he)
  have htz : M.Comparison₂ f u' z := by
    refine tie_congr (GlobalTheory.Reg.MChart.tie_baseChange E H Dw l Xo c O _ Y M _ _ _ _ _ _ _ (hyy e he) hz) (fun a => ?_) fun τ i j => ?_
    · exact (congrArg ψ (Subtype.ext (k1 e he a))).trans (hψ1 a (k1 e he a ▸ (fe e he a).2))
    · exact (congrArg ψ (Subtype.ext (k2 e he τ i j))).trans (hψ2 τ i j (k2 e he τ i j ▸ (ue e he τ i j).2))
  obtain ⟨t, ht'⟩ := GlobalTheory.Reg.frBor_of_tie E H Dw l Xo c O _ Y M L f y z Λ u' b (lift_point_unique htz.choose Λ) hb ht htz
  refine ⟨e, he, ψ, z, t, ?_, hz, ht'⟩
  rintro ⟨w, hw⟩ hwg
  rcases h6 w hwg with ⟨a, rfl⟩ | ⟨τ, i, j, rfl⟩
  · exact (hψ1 a hw).symm ▸ hW a
  · exact (hψ2 τ i j hw).symm ▸ hW' τ i j

end GlobalTheory.Reg
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flagCellChart_over_modelChart : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FrBC Xo c → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O c.F] [IsFractionRing O c.F] (Y : Model Xo c (algebraMap O c.F)), PushInvertible Y.t.G Y.t.PP.L → ∀ (M : MChart Y) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin M.n), ∃ (J : Type) (_ : Finite J) (P : J → PChart Xo c (algebraMap O c.F)), ∀ (L : Type) [Field L] [Algebra c.F L] (W : ValuationSubring L) (f : Γ(Y.X, M.U) →+* L) (y : FrPt Xo c L) (Λ : M.Lift f y.x) (u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) L) (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) L), (∀ a, f a ∈ W) → (∀ τ i j, u τ i j ∈ W) → (∀ τ, InCell (ix τ) (u τ)) → (∀ τ, (b τ).BlockTriangular id ∧ ∀ i, b τ i i ≠ 0) → Λ.LieTie (fun τ => u τ * b τ) y.u → ∃ j, (P j).Catches W y := by
  first | exact @GlobalTheory.Reg.exists_pChart_of_cell | exact GlobalTheory.Reg.exists_pChart_of_cell | (intros; apply GlobalTheory.Reg.exists_pChart_of_cell <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem MChart.Lift.exists_coordinates (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    (M : MChart Y) (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L) (y : FrPt Xo c L)
    (Λ : M.Lift f y.x) :
    ∃ g : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) L,
      Λ.LieTie g y.u ∧ ∀ τ, LinearIndependent L (g τ).transpose := by
  classical
  have hb := vec_bijective E H Dw l Xo c O β Y M L f y.x Λ
  have hc := GlobalTheory.T.isCombAt_iff_coordinate_combination E H Dw l Xo c O β Y M L f y.x Λ
  choose cv hcv using fun τ i => (hb.2.2 (y.u τ i) (y.4 τ i)).exists
  refine ⟨fun τ j i => cv τ i j, fun τ i => hcv τ i, fun τ => ?_⟩
  refine Fintype.linearIndependent_iff.2 fun a ha k => ?_
  have ha' : ∑ i, a i • cv τ i = 0 := ha
  have s1 : ∑ i, ((Pi.single k (1 : L) : Fin (Dw.mult τ) → L) + a) i • cv τ i = cv τ k := by
    simp [Pi.single_apply, add_smul, Finset.sum_add_distrib, ha']
  have s2 : ∑ i, (Pi.single k (1 : L) : Fin (Dw.mult τ) → L) i • cv τ i = cv τ k := by
    simp [Pi.single_apply]
  have e1 : IsCombAt y.x (y.u τ) (Pi.single k 1 + a) (y.u τ k) :=
    (hc _ (cv τ) (y.u τ) _ (y.u τ k) (hcv τ)).2 (by rw [s1]; exact hcv τ k)
  have e2 : IsCombAt y.x (y.u τ) (Pi.single k 1) (y.u τ k) :=
    (hc _ (cv τ) (y.u τ) _ (y.u τ k) (hcv τ)).2 (by rw [s2]; exact hcv τ k)
  have h := (y.6 τ (y.u τ k) (y.4 τ k) (y.5 τ k)).unique e1 e2
  simpa using congrFun h k

private theorem spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  unfold spMap
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem exists_integral_lift (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    {J : Type} (M : J → MChart Y) (hM : ∀ x : Y.X, ∃ j, x ∈ (M j).U) (L : Type) [Field L] [Algebra c.F L]
    (W : ValuationSubring L) (hW : ∀ a : O, algebraMap c.F L (β a) ∈ W) (y : FrPt Xo c L) :
    ∃ (j : J) (f : Γ(Y.X, (M j).U) →+* L), (∀ a, f a ∈ W) ∧ Nonempty ((M j).Lift f y.x) := by
  classical
  have hx : y.x ≫ Xo.s = spMap (algebraMap c.F L) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [y.2]
    unfold sOf
    exact spMap_comp_moduli_spaces _ _
  obtain ⟨yt, ⟨-, hyt⟩, -⟩ := (GlobalTheory.ModelPoints.model_points_charts E H Dw l Xo c O β Y).1 W L
    (((algebraMap c.F L).comp β).codRestrict W hW) (algebraMap c.F L)
    (pullback.lift y.x (spMap (algebraMap c.F L)) hx) (RingHom.ext fun _ => rfl) (pullback.lift_snd _ _ _)
  obtain ⟨j, hj⟩ := hM (yt (IsLocalRing.closedPoint W))
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.ModelPoints.existsUnique_chartHom (M j).hU W yt hj
  refine ⟨j, (algebraMap W L).comp ψ, fun a => (ψ a).2, ?_⟩
  have key : pullback.lift y.x (spMap (algebraMap c.F L)) hx ≫ Y.j =
      spMap ((algebraMap W L).comp ψ) ≫ (M j).hU.fromSpec := by
    rw [spMap_comp_moduli_spaces, Category.assoc, hψ, hyt]
  have hn := MChart.nonempty_lift E H Dw l Xo c O β Y (M j) L ((algebraMap W L).comp ψ)
    (pullback.lift y.x (spMap (algebraMap c.F L)) hx) (pullback.lift_snd _ _ _) key
  rwa [pullback.lift_fst] at hn

theorem exists_finite_pchart_cover : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FrBC Xo c → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O c.F] [IsFractionRing O c.F] (Y : Model Xo c (algebraMap O c.F)), PushInvertible Y.t.G Y.t.PP.L → ∃ (J : Type) (_ : Finite J) (P : J → PChart Xo c (algebraMap O c.F)), Covers P := by
  intro hS E _ _ _ H Dw l Xo c hBC O _ _ _ _ _ Y hP
  classical
  obtain ⟨J₀, hJ₀, M, hM⟩ := exists_finite_mchart_cover E H Dw l Xo c O (algebraMap O c.F) Y hP
  have hT := fun (j : J₀) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin (M j).n) =>
    GlobalTheory.T.exists_flagCellChart_over_modelChart hS E H Dw l Xo c hBC O Y hP (M j) ix
  choose K hK P hPc using hT
  refine ⟨(j : J₀) × (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin (M j).n) × K j ix, ?_,
    fun q => P q.1 q.2.1 q.2.2, ?_⟩
  · infer_instance
  · intro L _ _ W hW y
    obtain ⟨j, f, hf, ⟨Λ⟩⟩ := exists_integral_lift E H Dw l Xo c O (algebraMap O c.F) Y M hM L W hW y
    obtain ⟨g, hg, hind⟩ := MChart.Lift.exists_coordinates E H Dw l Xo c O (algebraMap O c.F) Y (M j) L f y Λ
    choose ixs u b hu hlow hone hbt hdiag hgu using
      fun τ => GlobalTheory.exists_integral_pivot_decomposition L W (M j).n (Dw.mult τ) (g τ) (hind τ)
    obtain ⟨k, hk⟩ := hPc j ixs L W f y Λ u b hf hu (fun τ => ⟨hlow τ, hone τ⟩) (fun τ => ⟨hbt τ, hdiag τ⟩)
      (by rw [← funext hgu]; exact hg)
    exact ⟨⟨j, ixs, k⟩, hk⟩

end GlobalTheory.Reg
end
end
