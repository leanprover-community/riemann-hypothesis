module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianPosDefSimultaneousNormalForm
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

open Matrix

theorem _root_.GlobalTheory.T.hermitian_posDef_simultaneous_normal_form : ∀ {n : ℕ} {J P : Matrix (Fin n) (Fin n) ℂ}, J.IsHermitian → J.det ≠ 0 → P.IsHermitian →
    (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) →
    ∃ (ε : Fin n → Bool) (Q : GL (Fin n) ℂ), Q.1ᴴ * J * Q.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) ∧
      ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * P * g = P → gᴴ * J * g = J →
        ((Q⁻¹).1 * g * Q.1)ᴴ * ((Q⁻¹).1 * g * Q.1) = 1 := by
  first | exact @GlobalTheory.SimNormal.simultaneous_normal_form | exact GlobalTheory.SimNormal.simultaneous_normal_form | (intros; apply GlobalTheory.SimNormal.simultaneous_normal_form <;> assumption)
