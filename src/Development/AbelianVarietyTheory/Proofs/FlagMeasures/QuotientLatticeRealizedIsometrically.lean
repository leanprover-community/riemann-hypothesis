module

public import Mathlib
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.Complexify

@[expose] public section

open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset

namespace GlobalTheory.QuotCoord

theorem exists_quot_matrix {K : Type} [Field K] {n : ℕ} (U U' : Submodule K (Fin n → K))
    (h : U ≤ U') : ∃ (m : ℕ) (q : Matrix (Fin m) (Fin n) K),
      m + Module.finrank K U = Module.finrank K U' ∧ (∀ y ∈ U', q *ᵥ y = 0 ↔ y ∈ U) ∧
      U'.map (Matrix.toLin' q) = ⊤ := by
  let W := U.comap U'.subtype
  let e : (U' ⧸ W) ≃ₗ[K] (Fin (Module.finrank K (U' ⧸ W)) → K) := (Module.finBasis K (U' ⧸ W)).equivFun
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (e.toLinearMap ∘ₗ W.mkQ)
  have hg' : ∀ y : U', g y = e (W.mkQ y) := fun y => LinearMap.congr_fun hg y
  refine ⟨_, LinearMap.toMatrix' g, ?_, ?_, ?_⟩
  · rw [← (Submodule.comapSubtypeEquivOfLe h).finrank_eq]
    exact Submodule.finrank_quotient_add_finrank W
  · intro y hy
    rw [LinearMap.toMatrix'_mulVec, hg' ⟨y, hy⟩, LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    rfl
  · rw [Matrix.toLin'_toMatrix', eq_top_iff]
    intro z _
    obtain ⟨y, hy⟩ := W.mkQ_surjective (e.symm z)
    exact ⟨y, y.2, by rw [hg', hy, LinearEquiv.apply_symm_apply]⟩

theorem exists_coisometry {n m : ℕ} (P P' : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (h : P ≤ P')
    (hm : m + Module.finrank ℂ P = Module.finrank ℂ P') :
    ∃ Q : Matrix (Fin m) (Fin n) ℂ, Q * Qᴴ = 1 ∧
      (∀ z, (WithLp.toLp 2 (Qᴴ *ᵥ z) : EuclideanSpace ℂ (Fin n)) ∈ P') ∧
      (∀ u ∈ P', u - WithLp.toLp 2 (Qᴴ *ᵥ (Q *ᵥ u.ofLp)) ∈ P) ∧
      (∀ u ∈ P', ‖Pᗮ.starProjection u‖ = cnorm (Q *ᵥ u.ofLp)) := by
  let T : Submodule ℂ (EuclideanSpace ℂ (Fin n)) := Pᗮ ⊓ P'
  have hT : Module.finrank ℂ T = m := by
    have := Submodule.finrank_add_inf_finrank_orthogonal h
    simp only [T]; omega
  let ob : OrthonormalBasis (Fin m) ℂ T := (stdOrthonormalBasis ℂ T).reindex (finCongr hT)
  let Q : Matrix (Fin m) (Fin n) ℂ := Matrix.of fun i j => star ((ob i : EuclideanSpace ℂ (Fin n)) j)
  have hQ : ∀ (u : EuclideanSpace ℂ (Fin n)) i, (Q *ᵥ u.ofLp) i =
      inner ℂ (ob i : EuclideanSpace ℂ (Fin n)) u := by
    intro u i
    simp [Q, Matrix.mulVec, dotProduct, PiLp.inner_apply, mul_comm]
  have hQh : ∀ z, (WithLp.toLp 2 (Qᴴ *ᵥ z) : EuclideanSpace ℂ (Fin n)) =
      ((∑ i, z i • ob i : T) : EuclideanSpace ℂ (Fin n)) := by
    intro z
    ext j
    simp [Q, Matrix.mulVec, dotProduct, mul_comm]
  have hproj : ∀ u ∈ P', ∃ t : T, (t : EuclideanSpace ℂ (Fin n)) = Pᗮ.starProjection u ∧
      Q *ᵥ u.ofLp = (ob.repr t).ofLp ∧ u - t ∈ P := by
    intro u hu
    have h1 : u - Pᗮ.starProjection u ∈ P := by
      rw [Submodule.starProjection_orthogonal_val, sub_sub_cancel]
      exact Submodule.starProjection_apply_mem _ _
    have h2 : Pᗮ.starProjection u ∈ T := by
      refine ⟨Submodule.starProjection_apply_mem _ _, ?_⟩
      have := P'.sub_mem hu (h h1)
      rwa [sub_sub_cancel] at this
    refine ⟨⟨_, h2⟩, rfl, ?_, h1⟩
    funext i
    rw [hQ, ob.repr_apply_apply, Submodule.coe_inner]
    have h3 := Submodule.inner_left_of_mem_orthogonal h1 (ob i).2.1
    rwa [inner_sub_right, sub_eq_zero] at h3
  refine ⟨Q, ?_, fun z => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · ext i k
    have h1 := hQ (ob k) i
    have h2 := orthonormal_iff_ite.1 ob.orthonormal i k
    rw [Submodule.coe_inner, ← h1] at h2
    rw [Matrix.one_apply, ← h2]
    simp [Q, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · rw [hQh]
    exact (∑ i, z i • ob i : T).2.2
  · obtain ⟨t, -, h2, h3⟩ := hproj u hu
    rw [hQh, h2, ob.sum_repr]
    exact h3
  · obtain ⟨t, h1, h2, -⟩ := hproj u hu
    rw [← h1, h2, PlaceOperatorNorms.cnorm_eq]
    simp

open QuotientRealization

section
variable {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] {n m : ℕ}

theorem toLp_mem_pv (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (A : Submodule (𝓞 K) (Fin n → K)) (w : InfinitePlace K) (u : Fin n → ℂ)
    (hu : u ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (A : Set (Fin n → K)))) :
    (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin n)) ∈
      pv (Pi.basisFun K (Fin n)) X (Submodule.span K (A : Set (Fin n → K))) w := by
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨y, hy, rfl⟩ := hy
    exact Submodule.subset_span ⟨y, Submodule.subset_span hy, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add y w _ _ h1 h2 => rw [WithLp.toLp_add]; exact Submodule.add_mem _ h1 h2
  | smul a y _ h => rw [WithLp.toLp_smul]; exact Submodule.smul_mem _ _ h

omit [StarRing K] [_root_.NumberField.IsTotallyComplex K] in
theorem mul_fcoord (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (w : InfinitePlace K)
    (hX : IsUnit (X w).det) (q : Matrix (Fin m) (Fin n) K) (y : Fin n → K) :
    (q.map w.embedding * X w) *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y =
      vecAt (Pi.basisFun K (Fin m)) w (q *ᵥ y) := by
  rw [fcoord, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hX, Matrix.mul_one]
  funext i
  simp [vecAt, Matrix.mulVec, dotProduct]

theorem exists_frame (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (w : InfinitePlace K)
    (hX : IsUnit (X w).det) (q : Matrix (Fin m) (Fin n) K) (A S : Submodule (𝓞 K) (Fin n → K))
    (hS : ∀ y ∈ S, q *ᵥ y = 0)
    (hA : Submodule.span K (A.map ((Matrix.toLin' q).restrictScalars (𝓞 K)) : Set (Fin m → K)) = ⊤)
    (Q : Matrix (Fin m) (Fin n) ℂ)
    (hQ : ∀ u ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (A : Set (Fin n → K))),
      u - Qᴴ *ᵥ (Q *ᵥ u) ∈
        Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (S : Set (Fin n → K)))) :
    ∃ Y : Matrix (Fin m) (Fin m) ℂ, IsUnit Y.det ∧ ∀ y ∈ A,
      Y⁻¹ *ᵥ vecAt (Pi.basisFun K (Fin m)) w (q *ᵥ y) =
        Q *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y := by
  set M := q.map w.embedding * X w with hM
  have hker : Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (S : Set (Fin n → K))) ≤
      LinearMap.ker (Matrix.toLin' M) := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    show Matrix.toLin' M _ = 0
    rw [Matrix.toLin'_apply, hM, mul_fcoord X w hX, hS y hy]
    funext i; simp [vecAt]
  have hkey : ∀ y ∈ A, vecAt (Pi.basisFun K (Fin m)) w (q *ᵥ y) =
      (M * Qᴴ) *ᵥ (Q *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y) := by
    intro y hy
    have h1 := hker (hQ _ (Submodule.subset_span ⟨y, hy, rfl⟩))
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.mulVec_sub, sub_eq_zero] at h1
    rw [← Matrix.mulVec_mulVec, ← h1, hM, mul_fcoord X w hX]
  have hu : IsUnit (M * Qᴴ).det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_surjective_iff_isUnit]
    have hle : Submodule.span ℂ (fcoord (Pi.basisFun K (Fin m)) (fun _ => 1) w ''
        (A.map ((Matrix.toLin' q).restrictScalars (𝓞 K)) : Set (Fin m → K))) ≤
        LinearMap.range (Matrix.toLin' (M * Qᴴ)) := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨Q *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y, ?_⟩
      rw [Matrix.toLin'_apply, ← hkey y hy]
      simp [fcoord]
    have htop : Submodule.span ℂ (fcoord (Pi.basisFun K (Fin m)) (fun _ => 1) w ''
        (A.map ((Matrix.toLin' q).restrictScalars (𝓞 K)) : Set (Fin m → K))) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [PlaceDecomposition.finrank_span_complex _ _ (fun _ => by simp), rkK, hA]
      simp
    intro z
    obtain ⟨x, hx⟩ := hle (htop ▸ Submodule.mem_top (x := z))
    exact ⟨x, by simpa using hx⟩
  refine ⟨M * Qᴴ, hu, fun y hy => ?_⟩
  rw [hkey y hy, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

end

end GlobalTheory.QuotCoord
