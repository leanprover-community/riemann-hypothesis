module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
namespace GlobalTheory.FockOm
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem omE_form_and_degree : ∀ (p q r s : ℕ) (l l' : Ln p q r s) (d : ℕ) (P : Pol p q r s), P ∈ homog (Ix p q × Ix r s) d → (linePos l = linePos l' → omE l l' P ∈ homog (Ix p q × Ix r s) d) ∧ (linePos l = true → linePos l' = false → omE l l' P = X l * X l' * P) ∧ (linePos l = false → linePos l' = true → omE l l' P = - pderiv l (pderiv l' P)) := by
  intro p q r s l l' d P hP
  refine ⟨fun h => GlobalTheory.FockDeg.omE_mem_homog h hP, fun hl hl' => ?_, fun hl hl' => ?_⟩
  · have hne : l ≠ l' := fun e => by rw [e, hl'] at hl; exact absurd hl (by simp)
    simp [omE, raiB, lowB, hl, hl', hne, mul_assoc]
  · have hne : l ≠ l' := fun e => by rw [e, hl'] at hl; exact absurd hl (by simp)
    simp [omE, raiB, lowB, hl, hl', hne]

end GlobalTheory.FockOm
