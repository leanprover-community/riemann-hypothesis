module

public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Em0Injective
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
import Development.WeilBound.ThetaLifts.LatticeBasics.Hypotheses2
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Lean.Elab.MutualDef

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexa
open PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {m n : ℕ}

def BfE (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) : LinearMap.BilinForm F (Matrix (Fin m) (Fin n) E) :=
  LinearMap.mk₂ F (fun x z => Algebra.trace F E (xᵀ * J * z.map σ).trace)
    (fun x x' z => by simp [Matrix.transpose_add, Matrix.add_mul, Matrix.trace_add])
    (fun c x z => by simp [Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul])
    (fun x z z' => by simp [Matrix.map_add _ (map_add σ), Matrix.mul_add, Matrix.trace_add])
    (fun c x z => by
      have : (c • z).map σ = c • z.map σ := by ext i j; exact σ.toLinearMap.map_smul c (z i j)
      simp [this, Matrix.mul_smul, Matrix.trace_smul])

theorem BfE_apply (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (x z : Matrix (Fin m) (Fin n) E) :
    BfE σ J x z = Algebra.trace F E (xᵀ * J * z.map σ).trace := rfl

theorem BfE_nondeg [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (J : Matrix (Fin m) (Fin m) E)
    (hJ : J.det ≠ 0) : (BfE (n := n) σ J).Nondegenerate := by
  have hdet : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ
  have hdetT : IsUnit Jᵀ.det := by
    rw [Matrix.det_transpose]
    exact hdet
  have htr1 : Algebra.trace F E 1 ≠ 0 := by
    rw [← map_one (algebraMap F E), Algebra.trace_algebraMap]
    simp only [nsmul_eq_mul, mul_one, ne_eq, Nat.cast_eq_zero]
    exact Module.finrank_pos.ne'
  refine ⟨fun x hx => ?_, fun z hz => ?_⟩
  · by_contra hne
    have hy : Jᵀ * x ≠ 0 := by
      intro h0
      apply hne
      have h2 := congrArg (fun M => (Jᵀ)⁻¹ * M) h0
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetT] using h2
    obtain ⟨b0, j0, hb⟩ : ∃ b j, (Jᵀ * x) b j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hy (Matrix.ext h)
    have h1 := hx ((Matrix.single b0 j0 ((Jᵀ * x) b0 j0)⁻¹).map σ)
    have hσσ : ((Matrix.single b0 j0 ((Jᵀ * x) b0 j0)⁻¹).map σ).map σ =
        Matrix.single b0 j0 ((Jᵀ * x) b0 j0)⁻¹ := by
      ext a b
      simp only [Matrix.map_apply]
      exact hσ _
    have hswap : (xᵀ * J) j0 b0 = (Jᵀ * x) b0 j0 := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have hv : (xᵀ * J * Matrix.single b0 j0 ((Jᵀ * x) b0 j0)⁻¹).trace = 1 := by
      rw [Matrix.trace_mul_single, hswap, op_smul_eq_mul, mul_inv_cancel₀ hb]
    rw [BfE_apply, hσσ, hv] at h1
    exact htr1 h1
  · by_contra hne
    have hw : J * z.map σ ≠ 0 := by
      intro h0
      apply hne
      have hz0 : z.map σ = 0 := by
        have h2 := congrArg (fun M => J⁻¹ * M) h0
        simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet] using h2
      ext a b
      have := congrFun (congrFun hz0 a) b
      simp only [Matrix.map_apply, Matrix.zero_apply] at this
      rw [Matrix.zero_apply, ← hσ (z a b), this, map_zero]
    obtain ⟨a0, b0, hb⟩ : ∃ a b, (J * z.map σ) a b ≠ 0 := by
      by_contra h
      push_neg at h
      exact hw (Matrix.ext h)
    have h1 := hz (Matrix.single a0 b0 ((J * z.map σ) a0 b0)⁻¹)
    have hv : ((Matrix.single a0 b0 ((J * z.map σ) a0 b0)⁻¹)ᵀ * J * z.map σ).trace = 1 := by
      rw [Matrix.mul_assoc, Matrix.transpose_single, Matrix.trace_single_mul]
      simp [inv_mul_cancel₀ hb, mul_inv_cancel₀ hb]
    rw [BfE_apply, hv] at h1
    exact htr1 h1

end PositivityTheory.SiegelWeilFormula.Ldexa
