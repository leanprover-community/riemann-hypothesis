module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.RightSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.LinDer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
    push_cast
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
