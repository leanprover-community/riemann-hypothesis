module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

noncomputable def matrixEntriesEuclideanReal (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℝ] PiLp 2 (fun _ : Fin n × Fin n => ℂ) where
  toFun X := WithLp.toLp 2 (fun p => X p.1 p.2)
  invFun v := Matrix.of fun i j => v.ofLp (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem inner_matrixEntriesEuclideanReal (n : ℕ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    inner ℝ (matrixEntriesEuclideanReal n Y) (matrixEntriesEuclideanReal n X)
      = ((X * Yᴴ).trace).re := by
  change inner ℝ (WithLp.toLp 2 (fun p : Fin n × Fin n => Y p.1 p.2))
      (WithLp.toLp 2 (fun p : Fin n × Fin n => X p.1 p.2)) = _
  rw [PiLp.inner_apply]
  simp only [WithLp.ofLp_toLp, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.inner, mul_comm]

theorem exists_orthonormal_basis_re_trace_mul_conjTranspose (n : ℕ)
    (U : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ),
      (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ LinearIndependent ℝ E ∧
        U = Submodule.span ℝ (Set.range E) := by
  classical
  set e := matrixEntriesEuclideanReal n
  set V : Submodule ℝ (PiLp 2 (fun _ : Fin n × Fin n => ℂ)) := U.map e.toLinearMap
  let b := stdOrthonormalBasis ℝ V
  refine ⟨Module.finrank ℝ V, fun i => e.symm (b i : PiLp 2 (fun _ : Fin n × Fin n => ℂ)), ?_, ?_, ?_⟩
  · intro i k
    have h := inner_matrixEntriesEuclideanReal n (e.symm (b i)) (e.symm (b k))
    simp only [e, LinearEquiv.apply_symm_apply] at h
    rw [← h, ← Submodule.coe_inner, orthonormal_iff_ite.mp b.orthonormal k i]
    by_cases hik : i = k
    · subst hik; simp
    · simp [hik, Ne.symm hik]
  · have hb : LinearIndependent ℝ (fun i => (b i : PiLp 2 (fun _ : Fin n × Fin n => ℂ))) :=
      b.orthonormal.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
    exact hb.map' e.symm.toLinearMap e.symm.ker
  · symm
    have hrange : Set.range (fun i => e.symm (b i : PiLp 2 (fun _ : Fin n × Fin n => ℂ)))
        = e.symm.toLinearMap '' (V.subtype '' Set.range b) := by
      ext x; simp [Set.mem_image, Set.mem_range]
    have hspan : Submodule.span ℝ (Set.range b) = ⊤ := by
      simpa [OrthonormalBasis.coe_toBasis] using b.toBasis.span_eq
    rw [hrange, Submodule.span_image, Submodule.span_image, hspan, Submodule.map_subtype_top]
    ext x
    simp [V]

end GlobalTheory
