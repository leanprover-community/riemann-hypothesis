module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

theorem rename_comp_restrictToBlock (f N : ℕ) (τ : Fin f) (π : Equiv.Perm (Fin N)) :
    (rename π).comp (restrictToBlock f N τ) =
      (restrictToBlock f N τ).comp (blockPermute f N (Function.update 1 τ π)) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨σ, i⟩
  by_cases h : σ = τ
  · subst h
    simp [restrictToBlock, blockPermute]
  · simp [restrictToBlock, blockPermute, h]

theorem FlagRestrictSymmetric.proof : FlagRestrictSymmetric.Statement := by
  intro f N τ R hR π
  have key := congrArg (fun φ : RootRing f N →ₐ[ℚ] MvPolynomial (Fin N) ℚ => φ R)
    (rename_comp_restrictToBlock f N τ π)
  simp only [AlgHom.comp_apply] at key
  rw [key, hR]

end RestTerms

end GroundTheory.Heights₂.Heights
