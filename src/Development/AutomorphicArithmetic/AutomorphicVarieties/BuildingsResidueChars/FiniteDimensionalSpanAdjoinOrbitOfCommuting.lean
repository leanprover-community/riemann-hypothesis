module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt
public import Development.AutomorphicArithmetic.DivisorFrames.FiniteDimensionalSpanAdjoinApplyOfCommutingAlgeb
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

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.finiteDimensional_span_adjoin_orbit_of_commuting :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (x : M) (s : Set (Module.End ℂ M)), s.Finite → (∀ a ∈ s, ∀ b ∈ s, a * b = b * a) → (∀ T ∈ s, AlgMod (Submodule.span ℂ {x}) ⊥ T) → FiniteDimensional ℂ (Submodule.span ℂ ((fun T : Module.End ℂ M => T x) '' (Algebra.adjoin ℂ s : Set (Module.End ℂ M)))) := by
  intro M _ _ x s hs hc h
  refine UpperTheory.finiteDimensional_span_adjoin_apply_of_commuting_algebraic M s x hc (FiniteDimensional.span_of_finite ℂ hs) fun a ha => ?_
  obtain ⟨p, hp, hx⟩ := h a ha
  exact ⟨p, hp.ne_zero, (Submodule.mem_bot ℂ).1 (hx x (Submodule.mem_span_singleton_self x))⟩
