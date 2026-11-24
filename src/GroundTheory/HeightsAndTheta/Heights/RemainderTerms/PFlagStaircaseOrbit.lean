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

namespace GroundTheory.Heights₂.Heights.RestTerms

noncomputable section

theorem FlagStaircaseOrbit.bijective_of_injective {f N : ℕ} (γ : Fin f × Fin N →₀ ℕ) (τ : Fin f)
    (hlt : ∀ i, γ (τ, i) < N) (hinj : Function.Injective fun i : Fin N => γ (τ, i)) :
    Function.Bijective fun i : Fin N => (⟨γ (τ, i), hlt i⟩ : Fin N) := by
  refine Finite.injective_iff_bijective.mp ?_
  intro i j h
  exact hinj (congrArg Fin.val h)

theorem FlagStaircaseOrbit.proof : FlagStaircaseOrbit.Statement := by
  intro f N α β hα hβ iα iβ
  let A : Fin f → (Fin N ≃ Fin N) := fun τ =>
    Equiv.ofBijective _ (FlagStaircaseOrbit.bijective_of_injective α τ (hα τ) (iα τ))
  let B : Fin f → (Fin N ≃ Fin N) := fun τ =>
    Equiv.ofBijective _ (FlagStaircaseOrbit.bijective_of_injective β τ (hβ τ) (iβ τ))
  refine ⟨fun τ => (B τ).trans (A τ).symm, fun τ i => ?_⟩
  have h : A τ ((A τ).symm (B τ i)) = B τ i := Equiv.apply_symm_apply _ _
  have h' := congrArg Fin.val h
  exact h'

end

end GroundTheory.Heights₂.Heights.RestTerms
