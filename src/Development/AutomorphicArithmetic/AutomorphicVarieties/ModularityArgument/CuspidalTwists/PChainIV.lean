module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.PromodularityCaseThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ChainBetweenPairs
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Cu.RankFourChainReduction

open UpperTheory.V.Ws.Chn

theorem inA_of {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [Field k] {Φ : Fr O Γ} {a : O →+* k}
    {P P' : PD Φ.ι Γ k} (h : Φ.IsRes a P) (hq : Supp qQ P.r) (e : P.SameAl P') (h' : InA P') : InA P := by
  have r10 : ∀ g, P.r g 1 0 = 0 := fun g => (e.1 g).trans (h'.1 g 1 0 (by decide) (by decide))
  refine ⟨fun g i j hij hw => ?_, fun v => (e.2 v).symm ▸ h'.2 v⟩
  have : wt i j ∉ qQ ∨ i = 1 ∧ j = 0 ∨ i = 3 ∧ j = 2 := by revert hw; revert i j; decide
  rcases this with h1 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hq g i j hij h1
  · exact r10 g
  · exact al_zero h (qM hq) (r10 g)

end UpperTheory.V.Cu.RankFourChainReduction

