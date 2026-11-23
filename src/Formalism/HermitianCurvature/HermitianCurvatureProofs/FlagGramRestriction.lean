module

public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GNonneg
public import Formalism.HermitianCurvature.StatementB
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FixedPointsGramVector
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormBasics
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFlagVector
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LinearChangeOfVariablesBis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MajorantEstimate
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentUpperFacts

@[expose] public section

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P

namespace FlagGramRestriction

open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector UnipotentUpperFacts

variable {k r : ℕ}

lemma col_mul (M : B.Mat k r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (j : Fin (r + 1) ⊕ Fin (r + 1)) :
    (fun a => (M * gnB k r z z' γ) a j) = M *ᵥ gramVec k r z z' γ j := by
  funext a; simp [gnB, Matrix.mul_apply, Matrix.mulVec, dotProduct]

end FlagGramRestriction

end Formalism.FourierDecayAlt.P
