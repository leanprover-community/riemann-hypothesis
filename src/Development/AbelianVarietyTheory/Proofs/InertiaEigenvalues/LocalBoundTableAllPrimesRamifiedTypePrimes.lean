module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem localBoundTableAllPrimes_ramified_typePrimes : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L),
    Concl L P X C → TwistedPlaces.RamifiedPrimeLengthBound L (tab L X tf C) C ∧ TwistedPlaces.GeneratorPrimeEtaBound L (tab L X tf C) C := by
  intro D L P X C tf hC
  refine ⟨⟨?_, hC.small.2.2.2.2.1⟩, ?_⟩
  · intro i _ hl
    obtain ⟨hq, hd, hq8, hd16, -⟩ := D.host.hyp
    have h3q := D.host.q_ne_three
    have h2 : D.nd.l i ∉ D.host.small := UpperTheory.Small.not_mem_of_qd D.host hl
    have h3 : D.nd.l i ≠ 3 := by rcases hl with h | h <;> rw [h] <;> omega
    have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun h => h.2.1 hl
    have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, h2, h3, hR, if_false]
    have hBB : (tab L X tf C).BB i = TwistedPlaces.midG L C (D.nd.l i) := by
      simp only [tab, h2, hl, if_false, if_true]
    rw [hlen, hBB]
    simp [TwistedPlaces.sumOver]
  · intro j hj l hl
    exact ⟨hC.typ j hj l hl, le_rfl⟩

end GlobalTheory.NLink
