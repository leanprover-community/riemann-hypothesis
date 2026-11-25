module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.RightSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.LinDer
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
/-! # ExpFirst: Preliminary helper declarations for global theta kernels. -/

@[expose] public section

open scoped TensorProduct Matrix Kronecker
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.RealLift UpperTheory.TP.RP

theorem UpperTheory.TP.RP.expFirst :
    ∀ {n d : ℕ} (Y : Mat n 0) (g : GL (Fin n) ℂ) (c : ℤ) (κ : ℂ), (∀ a b, g.1 a b = NormedSpace.exp Y (Sum.inl a) (Sum.inl b)) →
      2 * (c : ℂ) = d + 2 * κ → IsExp (fockAct1 n 0 d 0 Y + (κ * Y.trace) • 1) (act1 c g) := by
  intro n d Y g c κ hg hc
  have hF : fockAct1 n 0 d 0 Y + (κ * Y.trace) • 1 =
      ((linDer (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) Y (1 : Matrix (Ix d 0) (Ix d 0) ℂ)) :
        Module.End ℂ (Pol n 0 d 0))) + ((c : ℂ) * Y.trace) • 1 := by
    unfold fockAct1
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, Matrix.kroneckerMapBilinear_apply_apply,
      LinearMap.mul_apply']
    rw [omAct_definite, add_assoc, ← add_smul]
    congr 2
    rw [Matrix.trace_kronecker, Matrix.trace_one]
    simp only [Fintype.card_sum, Fintype.card_fin, add_zero]
    linear_combination (-(Y.trace / 2)) * hc
  have hgm : (g : Matrix (Fin n) (Fin n) ℂ) =
      (NormedSpace.exp Y).submatrix (Equiv.sumEmpty (Fin n) (Fin 0)).symm
        (Equiv.sumEmpty (Fin n) (Fin 0)).symm := by
    ext a b
    simp [hg]
  have hA : (act1 c g : Module.End ℂ (PP n d)) = Complex.exp ((c : ℂ) * Y.trace) •
      (linSub (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (NormedSpace.exp Y)
        (1 : Matrix (Ix d 0) (Ix d 0) ℂ))).toLinearMap := by
    unfold act1
    congr 1
    · unfold detPow
      rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, hgm,
        Matrix.det_submatrix_equiv_self, GlobalTheory.DetSqrtCover.det_exp, Complex.exp_int_mul]
    · congr 1
      apply MvPolynomial.algHom_ext
      rintro ⟨a | a, b | b⟩
      · simp [leftSub, linSub, xv, hg, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
          Fintype.sum_sum_type, Matrix.one_apply, MvPolynomial.smul_eq_C_mul]
      · exact b.elim0
      · exact a.elim0
      · exact a.elim0
  rw [hF, hA]
  exact isExp_add_smul (linDer_kron_left_isExp Y) ((c : ℂ) * Y.trace)
