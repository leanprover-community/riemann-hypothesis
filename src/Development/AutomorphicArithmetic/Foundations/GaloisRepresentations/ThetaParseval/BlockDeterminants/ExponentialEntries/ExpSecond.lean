module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.RightSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Formalism.PeriodIntegrals.JointBlockShapes.MinusPart
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.ExpDer
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.LoweringPartRightActionInlInr
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open scoped TensorProduct Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.RealLift UpperTheory.TP.RP

noncomputable section

namespace UpperTheory.TP.RP.Der

open MvPolynomial

private def derR {n d : ℕ} (Y : Mat d 0) : Derivation ℂ (PP n d) (PP n d) :=
  ∑ a : Ix n 0, ∑ c : Ix d 0, ∑ e : Ix d 0, Y c e • (X (a, c) : PP n d) • pderiv (a, e)

private theorem derR_X {n d : ℕ} (Y : Mat d 0) (b : Ix n 0) (f : Ix d 0) :
    derR (n := n) Y (X (b, f)) = ∑ c, Y c f • (X (b, c) : PP n d) := by
  unfold derR
  simp only [der_sum_apply, Derivation.smul_apply, pderiv_X, Pi.single_apply, Prod.mk.injEq]
  simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

private theorem om_eq {n d : ℕ} (a : Ix n 0) (c e : Ix d 0) :
    FockH1Action.omE (p := n) (q := 0) (r := d) (s := 0) (a, c) (a, e) =
      LinearMap.mulLeft ℂ (X (a, c)) * (pderiv (a, e)).toLinearMap + (if (a, c) = (a, e) then (1 / 2 : ℂ) • 1 else 0) := by
  rcases a with a | a
  · rcases c with c | c
    · rcases e with e | e
      · simp [FockH1Action.omE, FockH1Action.raiB, FockH1Action.lowB, FockH1Action.linePos]
      · exact e.elim0
    · exact c.elim0
  · exact a.elim0

private theorem fock_second_action_eq_derivation {n d : ℕ} (Y : Mat d 0) :
    fockAct2 n 0 d 0 Y = (derR Y).toLinearMap + (((n : ℂ) / 2) * Y.trace) • 1 := by
  show FockH1Action.fockAct2 n 0 d 0 Y = _
  rw [PI.WFJM.fockAct2_eq]
  simp only [om_eq, smul_add, Finset.sum_add_distrib]
  congr 1
  · refine LinearMap.ext fun p => ?_
    simp only [derR, Derivation.coeFn_coe, der_sum_apply, Derivation.smul_apply,
      LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
      LinearMap.mulLeft_apply, smul_eq_mul]
  · simp only [Prod.mk.injEq, true_and, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, Finset.sum_const, Finset.card_univ, smul_smul, ← Finset.sum_smul]
    have hcard : Fintype.card (FockH1Action.Ix n 0) = n := by simp [FockH1Action.Ix]
    rw [hcard, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← Finset.sum_mul, Matrix.trace]
    simp only [Matrix.diag]
    ring

private theorem det_of_block {d : ℕ} (Y : Mat d 0) (g : GL (Fin d) ℂ)
    (hg : ∀ a b, g.1 a b = NormedSpace.exp Y (Sum.inl a) (Sum.inl b)) (c : ℤ) :
    detPow ℂ d g c = Complex.exp (c * Y.trace) := by
  have hgm : (g : Matrix (Fin d) (Fin d) ℂ) =
      (NormedSpace.exp Y).submatrix (Equiv.sumEmpty (Fin d) (Fin 0)).symm
        (Equiv.sumEmpty (Fin d) (Fin 0)).symm := by
    ext a b
    simp [hg]
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, hgm,
    Matrix.det_submatrix_equiv_self, GlobalTheory.DetSqrtCover.det_exp, Complex.exp_int_mul]

end UpperTheory.TP.RP.Der

theorem UpperTheory.TP.RP.expSecond :
    ∀ {n d : ℕ} (Y : Mat d 0) (g : GL (Fin d) ℂ) (c : ℤ) (κ : ℂ), (∀ a b, g.1 a b = NormedSpace.exp Y (Sum.inl a) (Sum.inl b)) →
      2 * (c : ℂ) = n + 2 * κ → IsExp (fockAct2 n 0 d 0 Y + (κ * Y.trace) • 1) (act2 c g) := by
  intro n d Y g c κ hg hc
  have hF : fockAct2 n 0 d 0 Y + (κ * Y.trace) • 1 =
      (UpperTheory.TP.RP.Der.derR (n := n) Y).toLinearMap + ((c : ℂ) * Y.trace) • 1 := by
    rw [UpperTheory.TP.RP.Der.fock_second_action_eq_derivation, add_assoc, ← add_smul]
    congr 2
    linear_combination (-(Y.trace / 2)) * hc
  have hA : (act2 c g : Module.End ℂ (PP n d)) = Complex.exp ((c : ℂ) * Y.trace) •
      (rightSub (n := n) (g : Matrix (Fin d) (Fin d) ℂ)).toLinearMap := by
    unfold act2
    rw [UpperTheory.TP.RP.Der.det_of_block Y g hg c]
  rw [hF, hA]
  apply UpperTheory.TP.RP.Der.isExp_shift
  apply UpperTheory.TP.RP.Der.isExp_of_gens
  rintro ⟨b, f⟩
  have key := UpperTheory.TP.RP.Der.good_lin (UpperTheory.TP.RP.Der.derR (n := n) Y) Y
    (fun e => (MvPolynomial.X (b, e) : PP n d)) (fun e => UpperTheory.TP.RP.Der.derR_X Y b e) f
  convert key using 1
  rcases b with b | b
  · rcases f with f | f
    · simp [rightSub, xv, hg, Fintype.sum_sum_type, MvPolynomial.smul_eq_C_mul]
    · exact f.elim0
  · exact b.elim0
