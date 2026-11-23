module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedR
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadicalReductionUnitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.RadicalReductionOperator

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD

def MxOp (k r : ℕ) : Type := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

instance (k r : ℕ) : NormedRing (MxOp k r) := Matrix.linftyOpNormedRing

instance (k r : ℕ) : NormedAlgebra ℂ (MxOp k r) := Matrix.linftyOpNormedAlgebra

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def toOp (k r : ℕ) : Q.Mx k r ≃ₗ[ℝ] MxOp k r where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' c x := by
    change (c • x : Q.Mx k r) = (c • (@id (MxOp k r) x))
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c x, RCLike.real_smul_eq_coe_smul (K := ℂ) c (@id (MxOp k r) x)]
    rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem locLog : NFRadRedR.LocLog := by
  intro k r z _ _
  obtain ⟨O, hO, h1, Λ, hΛ, hΛg⟩ := RadicalReductionUnitary.locLogOp (k := k) (r := r) z
  have hΛ' : ContDiffOn ℝ ∞ (fun x : MxOp k r => @id (MxOp k r) (Λ x)) (@id (Set (MxOp k r)) O) := hΛ
  have hO' : IsOpen (O : Set (Q.Mx k r)) := hO
  refine ⟨O, hO', h1, Λ, ?_, hΛg⟩
  have hL1 := (toOp k r).toContinuousLinearEquiv.toContinuousLinearMap.contDiff (n := ∞)
  have hL2 := (toOp k r).toContinuousLinearEquiv.symm.toContinuousLinearMap.contDiff (n := ∞)
  have h := hL2.comp_contDiffOn (hΛ'.comp (s := (O : Set (Q.Mx k r))) hL1.contDiffOn (fun x hx => hx))
  exact h.congr (fun x _ => rfl)

end Formalism.FourierDecayAlt.P.RadicalReductionOperator

namespace Formalism.FourierDecayAlt.P

theorem local_logarithm_unitary : NFRadRedR.LocLog := RadicalReductionOperator.locLog

end Formalism.FourierDecayAlt.P
