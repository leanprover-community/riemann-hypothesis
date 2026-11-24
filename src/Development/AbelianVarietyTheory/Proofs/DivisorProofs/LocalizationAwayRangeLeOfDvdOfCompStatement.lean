module

public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.OreLocalization.Ring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayRangeLeOfDvdOfComp
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


theorem _root_.GlobalTheory.T.localization_away_range_le_of_dvd_of_comp : ∀ (R : Type) [CommRing R] (P : Type) [CommRing P] (g : R →+* P) (c c' : R), c ∣ c' → ∀ (κ : Localization.Away c →+* P) (κ' : Localization.Away c' →+* P), κ.comp (algebraMap R (Localization.Away c)) = g → κ'.comp (algebraMap R (Localization.Away c')) = g → κ.range ≤ κ'.range := by
  first | exact @GlobalTheory.away_range_le_of_dvd' | exact GlobalTheory.away_range_le_of_dvd' | (intros; apply GlobalTheory.away_range_le_of_dvd' <;> assumption)
