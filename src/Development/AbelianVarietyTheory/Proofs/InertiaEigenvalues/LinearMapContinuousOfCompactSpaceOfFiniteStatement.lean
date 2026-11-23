module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearMapContinuousOfCompactSpaceOfFinite
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


theorem _root_.GlobalTheory.T.continuous_linearMap_of_finite : ∀ {O : Type} [CommRing O] [TopologicalSpace O] [CompactSpace O] {M M' : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul O M] [T2Space M] [Module.Finite O M] [AddCommGroup M'] [Module O M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousSMul O M'] (f : M →ₗ[O] M'), Continuous f := by
  first | exact @GlobalTheory.linearMap_continuous_of_compactSpace_of_finite | exact GlobalTheory.linearMap_continuous_of_compactSpace_of_finite | (intros; apply GlobalTheory.linearMap_continuous_of_compactSpace_of_finite <;> assumption)
