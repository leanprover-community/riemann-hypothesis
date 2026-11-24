module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelTransfer.LzOutRight
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Matrix

@[expose] public section

open Matrix

noncomputable section

namespace PIQnLT

open Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k i r' : ℕ}

set_option backward.isDefEq.respectTransparency false in
theorem exp_Lz (hL : LevHom) (Y : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    NormedSpace.exp (Lz k i r' Y) = ιLev k i r' (NormedSpace.exp Y) := by
  have h0 : ιLev k i r' 0 = 1 - Lz k i r' 1 := by
    rw [← Lz_one (k := k) (i := i) (r' := r') hL]
    abel
  letI : NormedRing (Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :=
    Matrix.linftyOpNormedAlgebra
  letI : NormedRing (Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ) :=
    Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ) :=
    Matrix.linftyOpNormedAlgebra
  have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y
  have h3 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (Lz k i r' Y)
  have hc : Continuous (LzL k i r') := (LzL k i r').continuous_of_finiteDimensional
  have h2 := h1.map (LzL k i r') hc
  have hfun : (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • (Lz k i r' Y) ^ n) =
      (fun n : ℕ => (LzL k i r') (((n.factorial : ℂ)⁻¹) • Y ^ n) +
        (if n = 0 then (1 - Lz k i r' 1) else 0)) := by
    funext n
    cases n with
    | zero => simp [LzL_apply]
    | succ m =>
      have hm : m + 1 ≠ 0 := by omega
      rw [if_neg hm, add_zero, LinearMap.map_smul, LzL_apply, Lz_pow hL]
  have h5 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • (Lz k i r' Y) ^ n)
      (LzL k i r' (NormedSpace.exp Y) + (1 - Lz k i r' 1)) := by
    rw [hfun]
    exact h2.add (hasSum_ite_eq 0 (1 - Lz k i r' 1))
  have e := h3.unique h5
  refine e.trans ?_
  rw [ιLev_eq, h0]
  rfl

end PIQnLT
