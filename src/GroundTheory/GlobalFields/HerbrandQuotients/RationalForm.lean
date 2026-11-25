module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Basic

@[expose] public section

namespace GroundTheory.Global

open Matrix

theorem exists_rat_intertwiner {ι J : Type*} [Fintype ι] [DecidableEq ι]
    (A A' : J → Matrix ι ι ℚ) (P : Matrix ι ι ℝ) (hP : P.det ≠ 0)
    (h : ∀ j, P * (A j).map (Rat.cast : ℚ → ℝ) = (A' j).map (Rat.cast : ℚ → ℝ) * P) :
    ∃ Q : Matrix ι ι ℚ, Q.det ≠ 0 ∧ ∀ j, Q * A j = A' j * Q := by

  obtain ⟨V, hV⟩ : ∃ V : Submodule ℚ ℝ,
      V = Submodule.span ℚ (Set.range fun p : ι × ι => P p.1 p.2) := ⟨_, rfl⟩
  have : Module.Finite ℚ V := hV ▸ Module.Finite.span_of_finite ℚ (Set.finite_range _)
  obtain ⟨κ, _, ⟨c⟩⟩ : ∃ (κ : Type) (_ : Fintype κ), Nonempty (Module.Basis κ ℚ V) :=
    ⟨_, inferInstance, ⟨Module.Free.chooseBasis ℚ V⟩⟩
  have hmem : ∀ a b, P a b ∈ V := fun a b => hV ▸ Submodule.subset_span ⟨(a, b), rfl⟩

  let Bm : κ → Matrix ι ι ℚ := fun k a b => c.repr ⟨P a b, hmem a b⟩ k
  have hcast : ∀ (q : ℚ) (r : ℝ), q • r = (q : ℝ) * r := fun q r => by
    rw [Algebra.smul_def, eq_ratCast]
  have hP_eq : P = ∑ k, (c k : ℝ) • (Bm k).map (Rat.cast : ℚ → ℝ) := by
    ext a b
    have h1 := congrArg (Subtype.val : V → ℝ) (c.sum_repr ⟨P a b, hmem a b⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, hcast] at h1
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [← h1]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hli : LinearIndependent ℚ (fun k => (c k : ℝ)) :=
    c.linearIndependent.map' V.subtype (Submodule.ker_subtype V)

  have hB : ∀ k j, Bm k * A j = A' j * Bm k := by
    intro k j
    have hsum : ∑ k, (c k : ℝ) • (Bm k * A j - A' j * Bm k).map (Rat.cast : ℚ → ℝ) = 0 := by
      have hmap : ∀ X Y : Matrix ι ι ℚ, (X * Y).map (Rat.cast : ℚ → ℝ) =
          X.map (Rat.cast : ℚ → ℝ) * Y.map (Rat.cast : ℚ → ℝ) := fun X Y =>
        Matrix.map_mul (f := Rat.castHom ℝ)
      have hsub : ∀ X Y : Matrix ι ι ℚ, (X - Y).map (Rat.cast : ℚ → ℝ) =
          X.map (Rat.cast : ℚ → ℝ) - Y.map (Rat.cast : ℚ → ℝ) := fun X Y => by
        ext; simp
      have e1 : ∑ k, (c k : ℝ) • ((Bm k).map (Rat.cast : ℚ → ℝ) * (A j).map (Rat.cast : ℚ → ℝ)) =
          P * (A j).map (Rat.cast : ℚ → ℝ) := by
        simp only [hP_eq, Finset.sum_mul, Matrix.smul_mul]
      have e2 : ∑ k, (c k : ℝ) • ((A' j).map (Rat.cast : ℚ → ℝ) * (Bm k).map (Rat.cast : ℚ → ℝ)) =
          (A' j).map (Rat.cast : ℚ → ℝ) * P := by
        simp only [hP_eq, Finset.mul_sum, Matrix.mul_smul]
      simp only [hsub, hmap, smul_sub, Finset.sum_sub_distrib, e1, e2, h j, sub_self]
    ext a b
    have hab := congrFun (congrFun hsum a) b
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Matrix.zero_apply] at hab
    have := Fintype.linearIndependent_iff.1 hli (fun k => (Bm k * A j - A' j * Bm k) a b)
      (by simpa only [hcast, mul_comm] using hab) k
    rwa [Matrix.sub_apply, sub_eq_zero] at this

  clear_value Bm
  obtain ⟨Mx, hMx⟩ : ∃ Mx : Matrix ι ι (MvPolynomial κ ℚ),
      Mx = Matrix.of fun a b => ∑ k, MvPolynomial.X k * MvPolynomial.C (Bm k a b) := ⟨_, rfl⟩
  have hF : Mx.det ≠ 0 := by
    intro h0
    apply hP
    have hPM : P = (MvPolynomial.aeval fun k => (c k : ℝ) :
        MvPolynomial κ ℚ →ₐ[ℚ] ℝ).mapMatrix Mx := by
      ext a b
      rw [hP_eq]
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
        AlgHom.mapMatrix_apply, hMx, Matrix.of_apply, map_sum, map_mul, MvPolynomial.aeval_X,
        MvPolynomial.aeval_C, eq_ratCast]
    rw [hPM, ← AlgHom.map_det, h0]
    exact map_zero _
  obtain ⟨q, hq⟩ : ∃ q : κ → ℚ, MvPolynomial.eval q Mx.det ≠ 0 := by
    by_contra! hall
    exact hF (MvPolynomial.funext fun x => by rw [hall x, map_zero])
  refine ⟨∑ k, q k • Bm k, ?_, fun j => ?_⟩
  · have hQ : (MvPolynomial.eval q).mapMatrix Mx = ∑ k, q k • Bm k := by
      ext a b
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hMx, Matrix.of_apply, map_sum,
        map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul]
    rw [← hQ, ← RingHom.map_det]
    exact hq
  · rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [Matrix.smul_mul, Matrix.mul_smul, hB]

end GroundTheory.Global
