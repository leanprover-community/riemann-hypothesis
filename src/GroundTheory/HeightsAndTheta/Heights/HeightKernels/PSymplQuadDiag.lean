module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace PSymplQuadDiag

theorem abs_det_eq_one_of_mul_transpose {ι : Type} [Fintype ι] [DecidableEq ι]
    (O : Matrix ι ι ℝ) (h : Oᵀ * O = 1) : |O.det| = 1 := by
  have h1 : O.det * O.det = 1 := by
    have := congrArg Matrix.det h
    rwa [det_mul, det_transpose, det_one] at this
  have h2 : |O.det| * |O.det| = 1 := by rw [← abs_mul, h1, abs_one]
  nlinarith [abs_nonneg O.det]

end PSymplQuadDiag

theorem SymplQuadDiag.proof : SymplQuadDiag.Statement := by
  intro ι _ _ G hG
  have hH := hG.isHermitian
  set U : Matrix ι ι ℝ := (hH.eigenvectorUnitary : Matrix ι ι ℝ) with hUdef
  have hstar : star U = Uᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hspec : G = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U := by
    conv_lhs => rw [hH.spectral_theorem]
    simp [hUdef]
  refine ⟨star U, hH.eigenvalues, fun i => hG.eigenvalues_pos i, ?_, ?_, ?_⟩
  · rw [hstar]
    apply PSymplQuadDiag.abs_det_eq_one_of_mul_transpose
    rw [transpose_transpose, ← hstar]
    exact Unitary.coe_mul_star_self hH.eigenvectorUnitary
  · rw [hH.det_eq_prod_eigenvalues]
    simp
  · intro x
    have hx : x ᵥ* U = star U *ᵥ x := by rw [hstar, mulVec_transpose]
    calc qf G x = x ⬝ᵥ (U *ᵥ (diagonal (RCLike.ofReal ∘ hH.eigenvalues) *ᵥ (star U *ᵥ x))) := by
          have hG' : G *ᵥ x = U *ᵥ (diagonal (RCLike.ofReal ∘ hH.eigenvalues) *ᵥ (star U *ᵥ x)) := by
            rw [mulVec_mulVec, mulVec_mulVec, ← hspec]
          rw [qf, hG']
      _ = (star U *ᵥ x) ⬝ᵥ (diagonal (RCLike.ofReal ∘ hH.eigenvalues) *ᵥ (star U *ᵥ x)) := by
          rw [dotProduct_mulVec, hx]
      _ = ∑ i, hH.eigenvalues i * (star U *ᵥ x) i ^ 2 := by
          simp only [dotProduct, mulVec_diagonal, Function.comp_apply, RCLike.ofReal_real_eq_id,
            id]
          exact Finset.sum_congr rfl fun i _ => by ring

end

end GroundTheory.Heights₂.Heights
