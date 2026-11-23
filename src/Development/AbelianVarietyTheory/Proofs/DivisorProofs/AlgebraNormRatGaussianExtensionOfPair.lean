module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleXSqAddOne
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable

@[expose] public section

open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.GaussExt

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

theorem X_sq_add_one_ne_zero : (X ^ 2 + 1 : F[X]) ≠ 0 := Monic.ne_zero (by monicity!)

theorem natDegree_X_sq_add_one : (X ^ 2 + 1 : F[X]).natDegree = 2 := by compute_degree!

def basisOneI : Module.Basis (Fin 2) F (Ext F) :=
  (AdjoinRoot.powerBasis (X_sq_add_one_ne_zero F)).basis.reindex
    (finCongr (by rw [AdjoinRoot.powerBasis_dim, natDegree_X_sq_add_one]))

theorem basisOneI_apply (j : Fin 2) : basisOneI F j = ii F ^ (j : ℕ) := by
  simp [basisOneI, Module.Basis.reindex_apply, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen, ii]

theorem basisOneI_zero : basisOneI F 0 = 1 := by simp [basisOneI_apply]
theorem basisOneI_one : basisOneI F 1 = ii F := by simp [basisOneI_apply]

theorem gEmb_eq (a b : F) : gEmb F (a, b) = a • basisOneI F 0 + b • basisOneI F 1 := by
  simp [gEmb, basisOneI_zero, basisOneI_one, Algebra.smul_def]

theorem gEmb_mul_ii (a b : F) : gEmb F (a, b) * ii F = (-b) • basisOneI F 0 + a • basisOneI F 1 := by
  simp only [gEmb, basisOneI_zero, basisOneI_one, Algebra.smul_def, map_neg]
  linear_combination (algebraMap F (Ext F) b) * ii_sq F

theorem norm_gEmb_F (a b : F) : Algebra.norm F (gEmb F (a, b)) = a ^ 2 + b ^ 2 := by
  rw [Algebra.norm_eq_matrix_det (basisOneI F), Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, Algebra.coe_lmul_eq_mul,
    LinearMap.mul_apply']
  rw [basisOneI_zero, mul_one, basisOneI_one, gEmb_mul_ii, gEmb_eq]
  simp [Module.Basis.repr_self, Finsupp.single_apply]
  ring

theorem norm_gEmb (a b : F) :
    ((Algebra.norm ℚ (gEmb F (a, b)) : ℚ) : ℝ) = ∏ τ : F →+* ℝ, ((τ a) ^ 2 + (τ b) ^ 2) := by
  rw [← Algebra.norm_norm (S := F), norm_gEmb_F]
  have h := prod_emb (F := F) (a ^ 2 + b ^ 2)
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, ← h, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp

end GlobalTheory.GaussExt
