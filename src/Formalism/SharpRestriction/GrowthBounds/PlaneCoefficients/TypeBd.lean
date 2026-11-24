module

public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TypeBound
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GrowthBounds.GLWeightTheory
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

theorem typeBound_proved (D : Formalism.BasicNotions.D7) : TypeBound := by

  have hV := Formalism.MainNotions.G.GLWeightTheory.valuation_field D
  unfold Formalism.MainNotions.CovariantDegrees.ValuationLemmaField Formalism.MainNotions.CovariantDegrees.ShaLengthVersionTwo at hV
  unfold TypeBound
  intro K _ _ ι _ LL n _ S e he _ G lam hne
  obtain ⟨hval, hlam⟩ := hV.2 K ι LL n S e he
  exact ⟨fun M hM => (hlam G M).1 hM lam hne, fun th hth => (hval G th).1 hth lam hne⟩

end Formalism.MainNotions.PairMembershipBlocks
