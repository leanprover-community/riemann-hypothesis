module

public import Formalism.CorankShare.StatementFR
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

/-!
# Hilbert–Schmidt Frame Bounds, Gram-to-Frame Variance, and Subspace Projection

This module provides Hilbert–Schmidt identities and inequalities for finite-dimensional
complex frames `frQ c B = ∑ i, c i • (B i ∘ₗ adjoint (B i))` and near-isometry blocks
`frK (c i) (B i) = c i • (adjoint (B i) ∘ₗ B i)`.

In addition to the orthonormal-basis estimates used in the corank-share step, this file
formalizes the coordinate-free centered frame variance identity (`hs2_sub_smul_id_of_adjoint_eq`,
`hs2_frQ_centered`) and the traceless subspace projection bound (`subspace_projection_bound`),
which sharpens the naive `√w · √(hs2 A)` deviation bound by `√((D - w) / D)` for a
`w`-dimensional subspace `W ⊆ H` of a `D`-dimensional Hilbert space `H`.
-/

noncomputable section

namespace Formalism.CorankShareLayerCake.FR

namespace Pgsn2pfrla

open Finset Module LinearMap
open scoped InnerProductSpace

section gen
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

lemma norm_inner_swap (x y : E) : ‖⟪x, y⟫_ℂ‖ = ‖⟪y, x⟫_ℂ‖ :=
  norm_inner_symm x y

private lemma re_inner_self_eq_norm_sq {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] (x : G) :
    (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 :=
  inner_self_eq_norm_sq (𝕜 := ℂ) x

lemma sum_adj_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (A : E →ₗ[ℂ] F)
    (v : OrthonormalBasis ι ℂ E) (u : OrthonormalBasis κ ℂ F) :
    ∑ n, ‖adjoint A (u n)‖ ^ 2 = ∑ m, ‖A (v m)‖ ^ 2 := by
  have h1 : ∀ n, ‖adjoint A (u n)‖ ^ 2 = ∑ m, ‖⟪u n, A (v m)⟫_ℂ‖ ^ 2 := fun n => by
    rw [← v.sum_sq_norm_inner_right]
    exact Finset.sum_congr rfl fun m _ => by rw [LinearMap.adjoint_inner_right, norm_inner_swap]
  simp only [h1, fun m => (u.sum_sq_norm_inner_right (A (v m))).symm]
  exact Finset.sum_comm

omit [FiniteDimensional ℂ E] in
private lemma trace_eq_sum_inner_orthonormalBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ E) (T : E →ₗ[ℂ] E) :
    trace ℂ E T = ∑ i, ⟪b i, T (b i)⟫_ℂ := by
  rw [LinearMap.trace_eq_matrix_trace ℂ b.toBasis, Matrix.trace]
  simp [LinearMap.toMatrix_apply, OrthonormalBasis.repr_apply_apply]

lemma hilbert_schmidt_eq_basis_sum {ι : Type*} [Fintype ι] (A : E →ₗ[ℂ] F)
    (v : OrthonormalBasis ι ℂ E) :
    hs2 A = ∑ m, ‖A (v m)‖ ^ 2 := by
  classical
  unfold hs2
  rw [trace_eq_sum_inner_orthonormalBasis v, Complex.re_sum]
  exact Finset.sum_congr rfl fun m _ => by
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, re_inner_self_eq_norm_sq]

lemma hs2_nonneg (A : E →ₗ[ℂ] F) : 0 ≤ hs2 A := by
  rw [hilbert_schmidt_eq_basis_sum A (stdOrthonormalBasis ℂ E)]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Cauchy–Schwarz inequality for the real part of the Hilbert–Schmidt inner product. -/
lemma abs_re_trace_adjoint_comp_le (A B : E →ₗ[ℂ] F) :
    |(trace ℂ E (adjoint A ∘ₗ B)).re| ≤ Real.sqrt (hs2 A) * Real.sqrt (hs2 B) := by
  set v := stdOrthonormalBasis ℂ E
  have hre : (trace ℂ E (adjoint A ∘ₗ B)).re = ∑ m, (⟪A (v m), B (v m)⟫_ℂ).re := by
    rw [trace_eq_sum_inner_orthonormalBasis v, Complex.re_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun m => ‖A (v m)‖) (fun m => ‖B (v m)‖)
  calc |(trace ℂ E (adjoint A ∘ₗ B)).re|
      = |∑ m, (⟪A (v m), B (v m)⟫_ℂ).re| := by rw [hre]
    _ ≤ ∑ m, |(⟪A (v m), B (v m)⟫_ℂ).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m, ‖A (v m)‖ * ‖B (v m)‖ :=
        Finset.sum_le_sum fun m _ => (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
    _ = √((∑ m, ‖A (v m)‖ * ‖B (v m)‖) ^ 2) :=
        (Real.sqrt_sq (Finset.sum_nonneg fun _ _ => by positivity)).symm
    _ ≤ √((∑ m, ‖A (v m)‖ ^ 2) * (∑ m, ‖B (v m)‖ ^ 2)) := Real.sqrt_le_sqrt h2
    _ = √(hs2 A) * √(hs2 B) := by
        rw [← hilbert_schmidt_eq_basis_sum A v, ← hilbert_schmidt_eq_basis_sum B v,
          Real.sqrt_mul (hs2_nonneg A)]

/-- Coordinate-free quadratic expansion of `hs2 (Q - s • id)` for a self-adjoint operator `Q`. -/
lemma hs2_sub_smul_id_of_adjoint_eq {Q : E →ₗ[ℂ] E} (hQ : adjoint Q = Q) (s : ℝ) :
    hs2 (Q - (s : ℂ) • LinearMap.id) =
      (trace ℂ E (Q ∘ₗ Q)).re - 2 * s * (trace ℂ E Q).re + s ^ 2 * finrank ℂ E := by
  have hA : adjoint (Q - (s : ℂ) • LinearMap.id) = Q - (s : ℂ) • LinearMap.id := by
    rw [map_sub, map_smulₛₗ, hQ, LinearMap.adjoint_id, Complex.conj_ofReal]
  unfold hs2
  rw [hA]
  simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.smul_comp, LinearMap.comp_smul,
    LinearMap.id_comp, LinearMap.comp_id, map_sub, map_smul, LinearMap.trace_id, smul_eq_mul,
    Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re,
    Complex.natCast_im]
  ring

/-- Sharp traceless subspace projection bound for any self-adjoint operator `Q` and subspace `W`.
Exploiting `Re tr(Q - s I) = 0` yields the factor `√(w (D - w) / D)` in place of `√w`. -/
lemma subspace_projection_bound {Q : E →ₗ[ℂ] E} (hQ : adjoint Q = Q)
    (W : Submodule ℂ E) (hD : finrank ℂ E ≠ 0) :
    |(∑ l, (⟪(stdOrthonormalBasis ℂ W l : E), Q (stdOrthonormalBasis ℂ W l : E)⟫_ℂ).re) -
        (trace ℂ E Q).re / (finrank ℂ E : ℝ) * (finrank ℂ W : ℝ)| ≤
      Real.sqrt ((finrank ℂ W : ℝ) * ((finrank ℂ E : ℝ) - finrank ℂ W) / (finrank ℂ E : ℝ)) *
        Real.sqrt (hs2 (Q - (((trace ℂ E Q).re / (finrank ℂ E : ℝ) : ℝ) : ℂ) • LinearMap.id)) := by
  let P : E →ₗ[ℂ] E := (W.starProjection : E →ₗ[ℂ] E)
  have hPadj : adjoint P = P := by
    symm; rw [LinearMap.eq_adjoint_iff]; exact W.starProjection_isSymmetric
  have hPidem : P ∘ₗ P = P := by
    ext x; exact congrArg (fun f => f x) W.isIdempotentElem_starProjection
  have hPcomp : ∀ T : E →ₗ[ℂ] E,
      trace ℂ E (P ∘ₗ T) =
        ∑ l, ⟪(stdOrthonormalBasis ℂ W l : E), T (stdOrthonormalBasis ℂ W l : E)⟫_ℂ := fun T => by
    change trace ℂ E (W.subtype ∘ₗ (W.orthogonalProjectionOnto.toLinearMap ∘ₗ T)) = _
    rw [LinearMap.trace_comp_comm', trace_eq_sum_inner_orthonormalBasis (stdOrthonormalBasis ℂ W)]
    exact Finset.sum_congr rfl fun l _ => by
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, Submodule.coe_subtype,
        Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  have hPtr : trace ℂ E P = (finrank ℂ W : ℂ) := by
    have h1 := hPcomp LinearMap.id
    rw [LinearMap.comp_id] at h1
    rw [h1]
    have hnorm : ∀ l, ⟪(stdOrthonormalBasis ℂ W l : E), (stdOrthonormalBasis ℂ W l : E)⟫_ℂ = 1 :=
      fun l => by
        rw [← Submodule.coe_inner, inner_self_eq_norm_sq_to_K, (stdOrthonormalBasis ℂ W).orthonormal.1 l]
        simp
    simp only [LinearMap.id_apply, hnorm, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  set w : ℝ := (finrank ℂ W : ℝ)
  set D : ℝ := (finrank ℂ E : ℝ)
  have hDne : D ≠ 0 := Nat.cast_ne_zero.mpr hD
  set s : ℝ := (trace ℂ E Q).re / D
  set P0 : E →ₗ[ℂ] E := P - ((w / D : ℝ) : ℂ) • LinearMap.id
  set A : E →ₗ[ℂ] E := Q - (s : ℂ) • LinearMap.id
  have hP0adj : adjoint P0 = P0 := by
    rw [show P0 = P - ((w / D : ℝ) : ℂ) • LinearMap.id from rfl,
      map_sub, map_smulₛₗ, hPadj, LinearMap.adjoint_id, Complex.conj_ofReal]
  have hhsP0 : hs2 P0 = w * (D - w) / D := by
    rw [hs2_sub_smul_id_of_adjoint_eq hPadj (w / D), hPidem, hPtr, Complex.natCast_re]
    change w - 2 * (w / D) * w + (w / D) ^ 2 * D = w * (D - w) / D
    field_simp [hDne]; ring
  have htrA : (trace ℂ E A).re = 0 := by
    simp only [A, map_sub, map_smul, LinearMap.trace_id, smul_eq_mul, Complex.sub_re,
      Complex.re_ofReal_mul, Complex.natCast_re, s]
    change (trace ℂ E Q).re - (trace ℂ E Q).re / D * D = 0
    field_simp [hDne]; ring
  have hinner : (trace ℂ E (adjoint P0 ∘ₗ A)).re =
      (∑ l, (⟪(stdOrthonormalBasis ℂ W l : E), Q (stdOrthonormalBasis ℂ W l : E)⟫_ℂ).re) - s * w := by
    rw [hP0adj, show P0 ∘ₗ A = P ∘ₗ Q - (s : ℂ) • P - ((w / D : ℝ) : ℂ) • A by
      simp only [P0, A, LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.smul_comp,
        LinearMap.comp_smul, LinearMap.id_comp, LinearMap.comp_id, smul_sub, smul_smul, mul_comm]
      abel]
    simp only [map_sub, map_smul, hPcomp Q, hPtr, Complex.sub_re, smul_eq_mul,
      Complex.re_ofReal_mul, Complex.re_sum, Complex.natCast_re, htrA, mul_zero, sub_zero]
    rfl
  have hcs := abs_re_trace_adjoint_comp_le P0 A
  rwa [hinner, hhsP0] at hcs

lemma sum_norm_sq_le_hilbert_schmidt {κ : Type*} [Fintype κ] (A : E →ₗ[ℂ] F) {g : κ → E}
    (hg : Orthonormal ℂ g) :
    ∑ l, ‖A (g l)‖ ^ 2 ≤ hs2 A := by
  rw [hilbert_schmidt_eq_basis_sum A (stdOrthonormalBasis ℂ E),
    ← sum_adj_eq A (stdOrthonormalBasis ℂ E) (stdOrthonormalBasis ℂ F)]
  have h1 : ∀ l, ‖A (g l)‖ ^ 2 = ∑ n, ‖⟪g l, adjoint A (stdOrthonormalBasis ℂ F n)⟫_ℂ‖ ^ 2 :=
    fun l => by
      rw [← (stdOrthonormalBasis ℂ F).sum_sq_norm_inner_right]
      exact Finset.sum_congr rfl fun n _ => by rw [LinearMap.adjoint_inner_right, norm_inner_swap]
  simp only [h1]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun _ _ => Orthonormal.sum_inner_products_le _ hg

lemma sum_re_inner_bound {κ : Type*} [Fintype κ] (A : E →ₗ[ℂ] E) {g : κ → E}
    (hg : Orthonormal ℂ g) :
    |∑ l, (⟪g l, A (g l)⟫_ℂ).re| ≤ Real.sqrt (Fintype.card κ) * Real.sqrt (hs2 A) := by
  have h1 : ∀ l, |(⟪g l, A (g l)⟫_ℂ).re| ≤ ‖A (g l)‖ := fun l => by
    calc |(⟪g l, A (g l)⟫_ℂ).re| ≤ ‖⟪g l, A (g l)⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖g l‖ * ‖A (g l)‖ := norm_inner_le_norm _ _
      _ = ‖A (g l)‖ := by rw [hg.1 l, one_mul]
  have h2 : (∑ l, ‖A (g l)‖) ^ 2 ≤ (Fintype.card κ) * hs2 A := by
    have h3 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun l => ‖A (g l)‖)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h3
    exact h3.trans (mul_le_mul_of_nonneg_left (sum_norm_sq_le_hilbert_schmidt A hg) (Nat.cast_nonneg _))
  calc |∑ l, (⟪g l, A (g l)⟫_ℂ).re| ≤ ∑ l, |(⟪g l, A (g l)⟫_ℂ).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, ‖A (g l)‖ := Finset.sum_le_sum fun l _ => h1 l
    _ = √((∑ l, ‖A (g l)‖) ^ 2) := (Real.sqrt_sq (Finset.sum_nonneg fun _ _ => norm_nonneg _)).symm
    _ ≤ √((Fintype.card κ) * hs2 A) := Real.sqrt_le_sqrt h2
    _ = √(Fintype.card κ) * √(hs2 A) := Real.sqrt_mul (Nat.cast_nonneg _) _

lemma fam_bound (c : ℝ) (B : E →ₗ[ℂ] F) {κ : Type*} [Fintype κ] {g : κ → E}
    (hg : Orthonormal ℂ g) :
    |c * ∑ l, ‖B (g l)‖ ^ 2 - Fintype.card κ|
      ≤ Real.sqrt (Fintype.card κ) * Real.sqrt (hs2 (frK c B - LinearMap.id)) := by
  have h1 : ∀ l, (⟪g l, ((frK c B - LinearMap.id : E →ₗ[ℂ] E)) (g l)⟫_ℂ).re =
      c * ‖B (g l)‖ ^ 2 - 1 := fun l => by
    simp only [frK, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.id_apply, inner_sub_right, inner_smul_right, LinearMap.adjoint_inner_right,
      Complex.sub_re, Complex.re_ofReal_mul, re_inner_self_eq_norm_sq, hg.1 l]
    norm_num
  have h2 : ∑ l, (⟪g l, ((frK c B - LinearMap.id : E →ₗ[ℂ] E)) (g l)⟫_ℂ).re =
      c * ∑ l, ‖B (g l)‖ ^ 2 - Fintype.card κ := by
    rw [Finset.sum_congr rfl fun l _ => h1 l, Finset.sum_sub_distrib, Finset.mul_sum]; simp
  rw [← h2]
  exact sum_re_inner_bound _ hg

end gen

section fam
variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
    [∀ i, InnerProductSpace ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

lemma re_inner_Q (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) (x : H) :
    (⟪x, frQ c B x⟫_ℂ).re = ∑ i, c i * ‖adjoint (B i) x‖ ^ 2 := by
  simp only [frQ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    inner_sum, inner_smul_right, Complex.re_sum, Complex.re_ofReal_mul]
  exact Finset.sum_congr rfl fun i _ => by
    rw [← LinearMap.adjoint_inner_left (B i) (adjoint (B i) x) x, re_inner_self_eq_norm_sq]

lemma Q_symm (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) (x y : H) :
    ⟪frQ c B x, y⟫_ℂ = ⟪x, frQ c B y⟫_ℂ := by
  simp only [frQ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    sum_inner, inner_sum, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  exact Finset.sum_congr rfl fun i _ => by
    rw [← LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_left]

lemma adjoint_frQ (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) :
    adjoint (frQ c B) = frQ c B := by
  symm; rw [LinearMap.eq_adjoint_iff]; exact Q_symm c B

lemma tQ_eq (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) :
    (trace ℂ H (frQ c B)).re = ∑ i, c i * ∑ m, ‖B i (stdOrthonormalBasis ℂ (V i) m)‖ ^ 2 := by

  simp only [frQ, map_sum, map_smul, smul_eq_mul, Complex.re_sum, Complex.re_ofReal_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  rw [← hilbert_schmidt_eq_basis_sum (B i) (stdOrthonormalBasis ℂ (V i)), hs2,
    LinearMap.trace_comp_comm']

lemma trace_frame_sq_eq_sum (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) :
    (trace ℂ H (frQ c B ∘ₗ frQ c B)).re = ∑ n, ‖frQ c B (stdOrthonormalBasis ℂ H n)‖ ^ 2 := by
  have h := hilbert_schmidt_eq_basis_sum (frQ c B) (stdOrthonormalBasis ℂ H)
  unfold hs2 at h
  rwa [adjoint_frQ] at h

/-- Exact centered Hilbert–Schmidt frame variance identity. -/
lemma hs2_frQ_centered (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) (hD : finrank ℂ H ≠ 0) :
    hs2 (frQ c B - (((trace ℂ H (frQ c B)).re / (finrank ℂ H : ℝ) : ℝ) : ℂ) • LinearMap.id) =
      (trace ℂ H (frQ c B ∘ₗ frQ c B)).re - (trace ℂ H (frQ c B)).re ^ 2 / (finrank ℂ H : ℝ) := by
  rw [hs2_sub_smul_id_of_adjoint_eq (adjoint_frQ c B)]
  have hD' : (finrank ℂ H : ℝ) ≠ 0 := by exact_mod_cast hD
  field_simp [hD']
  ring

end fam

section wup
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

lemma W_upper (B : V →ₗ[ℂ] H) (N : Submodule ℂ V) {κ : Type*} [Fintype κ] {g : κ → H}
    (hg : Orthonormal ℂ g) (hperp : ∀ l, ∀ n ∈ N, ⟪B n, g l⟫_ℂ = 0) :
    ∑ l, ‖adjoint B (g l)‖ ^ 2 ≤ ∑ m, ‖B ((stdOrthonormalBasis ℂ Nᗮ m : V))‖ ^ 2 := by
  have hmem : ∀ l, adjoint B (g l) ∈ Nᗮ := fun l =>
    (Submodule.mem_orthogonal _ _).mpr fun n hn => by
      rw [LinearMap.adjoint_inner_right, hperp l n hn]
  have h1 : ∀ l, ‖adjoint B (g l)‖ ^ 2 =
      ∑ m, ‖⟪g l, B ((stdOrthonormalBasis ℂ Nᗮ m : V))⟫_ℂ‖ ^ 2 := fun l => by
    have h := (stdOrthonormalBasis ℂ Nᗮ).sum_sq_norm_inner_right ⟨adjoint B (g l), hmem l⟩
    change ∑ m, ‖⟪stdOrthonormalBasis ℂ Nᗮ m, (⟨adjoint B (g l), hmem l⟩ : Nᗮ)⟫_ℂ‖ ^ 2 =
      ‖adjoint B (g l)‖ ^ 2 at h
    rw [← h]
    exact Finset.sum_congr rfl fun m _ => by
      change ‖⟪(stdOrthonormalBasis ℂ Nᗮ m : V), adjoint B (g l)⟫_ℂ‖ ^ 2 = _
      rw [LinearMap.adjoint_inner_right, norm_inner_swap]
  simp only [h1]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun _ _ => Orthonormal.sum_inner_products_le _ hg

end wup

end Pgsn2pfrla

open Finset Module LinearMap Pgsn2pfrla
open scoped InnerProductSpace

end Formalism.CorankShareLayerCake.FR
