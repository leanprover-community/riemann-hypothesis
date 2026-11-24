module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Topology.Algebra.Group.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Lean.Elab.MutualDef
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.Measure

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace SchurOrthogonality

open MeasureTheory Topology Set Function ComplexConjugate Module

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G V} {σ : Representation ℂ G W}

theorem span_orbit_eq_top [π.IsIrreducible] {v : V} (hv : v ≠ 0) :
    Submodule.span ℂ (range fun g => π g v) = ⊤ := by
  set S := Submodule.span ℂ (range fun g => π g v)
  have hS : ∀ g, ∀ ⦃x⦄, x ∈ S → π g x ∈ S := by
    intro g x hx
    have : S ≤ S.comap (π g) := Submodule.span_le.2 (by
      rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, by simp⟩)
    exact this hx
  rcases IsSimpleOrder.eq_bot_or_eq_top (⟨S, hS⟩ : Subrepresentation π) with h | h
  · exfalso
    apply hv
    have : v ∈ (⟨S, hS⟩ : Subrepresentation π).toSubmodule := Submodule.subset_span ⟨1, by simp⟩
    rw [h] at this
    exact (Submodule.mem_bot ℂ).1 this
  · exact congrArg Subrepresentation.toSubmodule h

variable [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {Z : Subgroup G} [Z.Normal]

variable [MeasurableSpace (G ⧸ Z)] [BorelSpace (G ⧸ Z)] {ν : Measure (G ⧸ Z)}

section Characters

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

end Characters

section Orthogonality

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [SecondCountableTopology G]
  {Z : Subgroup G} [Z.Normal] [MeasurableSpace (G ⧸ Z)] [BorelSpace (G ⧸ Z)]
  {ν : Measure (G ⧸ Z)} [ν.IsHaarMeasure] [ν.IsMulRightInvariant] [CompactSpace (G ⧸ Z)]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G V} {σ : Representation ℂ G W}


end Orthogonality

end SchurOrthogonality

end GroundTheory.Automorphic
