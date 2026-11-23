module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAct2EqSymmetrisedHeisenbergQuadratic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation

@[expose] public section

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

theorem _root_.GlobalTheory.T.fockAct2_eq_symmetrised_heisenbergQuadratic : ∀ (P Q R S : ℕ) (Y : Mat R S), Y ∈ upq R S →
    fockAct2 P Q R S Y = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ a : Ix P Q, ∑ b : Ix R S, (lineSign a b / 4) •
      ((heisOp (Matrix.single a b (1 : ℂ) * Yᵀ) * heisOp (Matrix.single a b Complex.I) +
          heisOp (Matrix.single a b Complex.I) * heisOp (Matrix.single a b (1 : ℂ) * Yᵀ)) -
        (heisOp (Matrix.single a b Complex.I * Yᵀ) * heisOp (Matrix.single a b (1 : ℂ)) +
          heisOp (Matrix.single a b (1 : ℂ)) * heisOp (Matrix.single a b Complex.I * Yᵀ))) := by
  first | exact @GlobalTheory.FockHeisQuad.fockAct2_eq_heisOp_quad | exact GlobalTheory.FockHeisQuad.fockAct2_eq_heisOp_quad | (intros; apply GlobalTheory.FockHeisQuad.fockAct2_eq_heisOp_quad <;> assumption)
