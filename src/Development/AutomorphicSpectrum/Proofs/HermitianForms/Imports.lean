module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Instances.Matrix
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankFour
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix

namespace GlobalTheory.CompanionTheory.UnitaryLog

theorem main : ∀ (n : ℕ) (g : Matrix.unitaryGroup (Fin n) ℂ),
    ∃ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X ∧
      (g : Matrix (Fin n) (Fin n) ℂ) = NormedSpace.exp X := by
  intro n g
  have hA : (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * (g : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 g.2
  obtain ⟨B, h1, h2⟩ := Formalism.FourierDecayAlt.P.HermitianFormRankFour.unitary_log _ hA
  exact ⟨B, h1, h2.symm⟩

end GlobalTheory.CompanionTheory.UnitaryLog
