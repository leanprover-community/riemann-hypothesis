module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanAlgebraOrbitOfAnnihilated
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


theorem _root_.GlobalTheory.T.finiteDimensional_span_algebra_orbit_of_annihilated : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (T : Finset (Module.End ℂ V)) (p : Module.End ℂ V → Polynomial ℂ), (∀ s ∈ T, ∀ t ∈ T, Commute s t) → (∀ t ∈ T, p t ≠ 0) → ∀ ψ : V, (∀ t ∈ T, Polynomial.aeval t (p t) ψ = 0) → FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V)))) ∧ Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z ψ) '' (Algebra.adjoin ℂ (T : Set (Module.End ℂ V)) : Set (Module.End ℂ V)))) ≤ ∏ t ∈ T, (p t).natDegree := by
  first | exact @GlobalTheory.killed_span_adjoin_finrank_le | exact GlobalTheory.killed_span_adjoin_finrank_le | (intros; apply GlobalTheory.killed_span_adjoin_finrank_le <;> assumption)
