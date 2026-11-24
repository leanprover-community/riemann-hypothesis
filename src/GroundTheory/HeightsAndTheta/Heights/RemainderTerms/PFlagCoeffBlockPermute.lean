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

noncomputable section

def blockPermuteEquiv (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) :
    Fin f × Fin N ≃ Fin f × Fin N where
  toFun p := (p.1, w p.1 p.2)
  invFun p := (p.1, (w p.1).symm p.2)
  left_inv p := by simp
  right_inv p := by simp

theorem FlagCoeffBlockPermute.proof : FlagCoeffBlockPermute.Statement := by
  intro f N w P α
  classical
  set E := blockPermuteEquiv f N w with hE
  set β : Fin f × Fin N →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm fun p : Fin f × Fin N => α (p.1, w p.1 p.2) with hβ
  have hmap : Finsupp.mapDomain E β = α := by
    ext q
    obtain ⟨p, rfl⟩ := E.surjective q
    rw [Finsupp.mapDomain_apply_of_injective E.injective]
    simp [hβ, hE, blockPermuteEquiv]
  have hren : blockPermute f N w P = rename E P := rfl
  rw [hren, ← hmap, coeff_rename_mapDomain E E.injective]

end

end RestTerms

end GroundTheory.Heights₂.Heights
