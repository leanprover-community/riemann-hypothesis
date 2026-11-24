module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem compact_to_unitary_hermitian (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool)
    (P g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hP : IsCayleyU k r ε P)
    (hg : g ∈ Formalism.REAL.Kset ε) :
    P⁻¹ * g * P ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∩
      (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _) := by
  have a1 : P.conjTranspose * P = 1 := Matrix.mem_unitaryGroup_iff'.1 hP.2
  have a2 : P * P.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.1 hP.2
  have iP : P⁻¹ = P.conjTranspose := Matrix.inv_eq_left_inv a1
  have gJ : g.conjTranspose * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := (Formalism.REAL.maximal_compact_facts _ ε).1 g hg
  rw [iP]
  constructor
  · show (P.conjTranspose * g * P).conjTranspose * Formalism.QuantumDeterminants.Hpk k r * (P.conjTranspose * g * P) = Formalism.QuantumDeterminants.Hpk k r
    rw [← hP.1.2]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc P.conjTranspose * (g.conjTranspose * P) * (P.conjTranspose * Formalism.REAL.Jm ε * P) * (P.conjTranspose * g * P)
        = P.conjTranspose * (g.conjTranspose * ((P * P.conjTranspose) * Formalism.REAL.Jm ε * (P * P.conjTranspose)) * g) * P := by
          simp only [Matrix.mul_assoc]
      _ = P.conjTranspose * Formalism.REAL.Jm ε * P := by
          rw [a2, Matrix.one_mul, Matrix.mul_one, gJ, Matrix.mul_assoc]
  · have hs : P.conjTranspose ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
      rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mem hP.2
    exact mul_mem (mul_mem hs hg.1) hP.2

end Formalism.MainNotions.BridgeLemma

end
