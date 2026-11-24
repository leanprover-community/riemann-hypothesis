module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
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

noncomputable section

namespace GlobalTheory.ReducedFactor

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem nontrivial_of_irr {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) : Nontrivial V := by
  have : IsSimpleOrder (Subrepresentation ρ) := h
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  ext x
  rw [Subsingleton.elim x 0]
  exact iff_of_true (zero_mem _) (zero_mem _)

end General

section Tensor

variable {G H V V' U : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup U] [Module ℂ U]

end Tensor

end GlobalTheory.ReducedFactor

namespace GlobalTheory.ReducedFactor

end GlobalTheory.ReducedFactor
