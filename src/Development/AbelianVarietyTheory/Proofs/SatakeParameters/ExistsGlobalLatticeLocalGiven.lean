import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists

noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO

namespace TupApx

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem exists_pow_smul {π : R} (hπ : Irreducible π) {k : ℕ} (g : Matrix (Fin k) (Fin k) K) :
    ∃ (a : ℕ) (g0 : Matrix (Fin k) (Fin k) R), algebraMap R K π ^ a • g = g0.map (algebraMap R K) := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun ij : Fin k × Fin k => g ij.1 ij.2)
  obtain ⟨a, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.coe_ne_zero d) hπ
  choose y hy using hd
  refine ⟨a, Matrix.of fun i j => (u⁻¹ : Rˣ) * y (i, j), ?_⟩
  ext i j
  have h1 : π ^ a = (u⁻¹ : Rˣ) * (d : R) := by rw [hu]; simp
  rw [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, map_mul, hy, ← map_pow, h1, map_mul, smul_eq_mul,
    Algebra.smul_def, mul_assoc]

theorem exists_approx {E : Type} [Field E] (f : E →+* K) {π : R} (hπ : Irreducible π) (t : E)
    (ht : f t = algebraMap R K π)
    (hd : ∀ (y : R) (N : ℕ), ∃ (x : E) (z : R), f x = algebraMap R K (y + π ^ N * z))
    {k : ℕ} (g : Matrix (Fin k) (Fin k) K) (hg : IsUnit g.det) :
    ∃ (B : Matrix (Fin k) (Fin k) E) (u : Matrix (Fin k) (Fin k) R), IsUnit u.det ∧
      B.map f = g * u.map (algebraMap R K) := by
  obtain ⟨a, g0, h0⟩ := exists_pow_smul (K := K) hπ g
  obtain ⟨b, h, h1⟩ := exists_pow_smul (K := K) hπ g⁻¹
  choose x z hx using fun i j => hd (g0 i j) (a + b + 1)
  have hp0 : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ.ne_zero
  refine ⟨Matrix.of fun i j => (t ^ a)⁻¹ * x i j, 1 + π • (h * Matrix.of z), ?_, ?_⟩
  · rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    have hr : IsLocalRing.residue R π = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff]; exact hπ.not_isUnit
    have : (IsLocalRing.residue R).mapMatrix (1 + π • (h * Matrix.of z)) = 1 := by
      rw [map_add, map_one]
      have : (IsLocalRing.residue R).mapMatrix (π • (h * Matrix.of z)) = 0 := by
        ext i j; simp [hr]
      rw [this, add_zero]
    rw [this]; simp
  · have e1 : (1 + π • (h * Matrix.of z)).map (algebraMap R K) =
        1 + algebraMap R K π • (h.map (algebraMap R K) * (Matrix.of z).map (algebraMap R K)) := by
      rw [← Matrix.map_mul]
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, Matrix.one_apply,
        apply_ite (algebraMap R K), map_one, map_zero]
    rw [e1, ← h1, mul_add, mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]
    ext i j
    have h2 := congrFun (congrFun h0 i) j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h2
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀,
      map_pow, ht, hx, map_add, ← h2]
    field_simp
    ring

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem colSpan_mul_le {k : ℕ} (g : Matrix (Fin k) (Fin k) K) (u : Matrix (Fin k) (Fin k) R) :
    colSpan R (g * u.map (algebraMap R K)) ≤ colSpan R g := by
  rw [colSpan, Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  have : (fun i => (g * u.map (algebraMap R K)) i c) = ∑ j, u j c • fun i => g i j := by
    funext i
    simp [Matrix.mul_apply, Algebra.smul_def, mul_comm]
  change (fun i => (g * u.map (algebraMap R K)) i c) ∈ colSpan R g
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem colSpan_mul_eq {k : ℕ} (g : Matrix (Fin k) (Fin k) K) (u : Matrix (Fin k) (Fin k) R) (hu : IsUnit u.det) :
    colSpan R (g * u.map (algebraMap R K)) = colSpan R g := by
  refine le_antisymm (colSpan_mul_le g u) ?_
  have := colSpan_mul_le (g * u.map (algebraMap R K)) u⁻¹
  rwa [Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this


theorem span_image {A E R K : Type} [CommRing A] [Field E] [Algebra A E] [CommRing R] [Field K] [Algebra R K]
    (f : E →+* K) (hf : ∀ r : A, f (algebraMap A E r) ∈ Set.range (algebraMap R K)) {k : ℕ}
    (B : Matrix (Fin k) (Fin k) E) :
    Submodule.span R ((fun (x : Fin k → E) i => f (x i)) '' (colSpan A B : Set (Fin k → E))) = colSpan R (B.map f) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    change (fun i => f (x i)) ∈ colSpan R (B.map f)
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      exact Submodule.subset_span ⟨c, rfl⟩
    | zero =>
      have : (fun i => f ((0 : Fin k → E) i)) = 0 := by funext i; simp
      rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : (fun i => f ((x + y) i)) = (fun i => f (x i)) + fun i => f (y i) := by funext i; simp
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      obtain ⟨s, hs⟩ := hf a
      have : (fun i => f ((a • x) i)) = s • fun i => f (x i) := by
        funext i; simp [Algebra.smul_def, hs]
      rw [this]; exact Submodule.smul_mem _ _ hx
  · rw [colSpan, Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact Submodule.subset_span ⟨fun i => B i c, Submodule.subset_span ⟨c, rfl⟩, rfl⟩

end TupApx


end GlobalTheory.GO
