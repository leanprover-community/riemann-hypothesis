module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CoreStar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.PolyBB
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

@[expose] public section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem polynomial_bound : PolyB := by
  intro k r κ P hP
  obtain ⟨hsmooth, hbound⟩ := pb_poly hP
  refine ⟨hsmooth, fun n => ?_⟩
  obtain ⟨C, hC⟩ := hbound n
  refine ⟨C, fun u v hu hv hn g hg => ?_⟩
  rw [Formalism.FourierDecayAlt.P.BetaSesquilinearity.dLR_eq]
  have hw : ∀ x ∈ Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v, B.unitLie k r x.2 := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · obtain ⟨X, hX, rfl⟩ := List.mem_map.1 h
      exact hu X hX
    · obtain ⟨X, hX, rfl⟩ := List.mem_map.1 h
      exact hv X hX
  have hlen : (Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v).length ≤ n := by
    simpa [Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL, Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR] using hn
  simpa using hC _ hw hlen g hg

end PI.UnitaryCorollaryDerivatives
