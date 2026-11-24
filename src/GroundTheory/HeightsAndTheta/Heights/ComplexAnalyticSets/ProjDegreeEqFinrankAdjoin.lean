module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.IsClosedComplexSubmanifoldIn
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

noncomputable section

namespace Objects

variable {n d : ℕ}

theorem linPoly_eq (A : Matrix (Fin d) (Fin n) ℂ) (i : Fin d) :
    linPoly A.mulVecLin i = GroundTheory.Heights₂.Heights.ComplexSets.linPoly A i := by
  simp [linPoly, GroundTheory.Heights₂.Heights.ComplexSets.linPoly]

theorem projHom_eq (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) :
    GroundTheory.Heights₂.Heights.ComplexSets.projHom J A = projAlgHom J A.mulVecLin := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [GroundTheory.Heights₂.Heights.ComplexSets.projHom, GroundTheory.Heights₂.Heights.ComplexSets.pullback,
    projAlgHom, linPoly_eq]

theorem isFiniteProjection_iff (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin d) (Fin n) ℂ) :
    GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A ↔
      IsFiniteProjection J A.mulVecLin := by
  rw [IsFiniteProjection, ← projHom_eq]
  exact ⟨fun h => ⟨h.injective, h.finite⟩, fun h => ⟨h.1, h.2⟩⟩

theorem orthoRows_eq (d n : ℕ) :
    GroundTheory.Heights₂.Heights.ComplexSets.orthoRows d n = unitaryRows d n :=
  rfl

section Degree

variable (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime]

end Degree

end Objects

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
