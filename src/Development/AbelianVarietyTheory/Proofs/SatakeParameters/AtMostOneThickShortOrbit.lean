module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Development.AutomorphicArithmetic.CyclotomicBounds.PlaceOfLetterInjective
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
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

@[expose] public section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem short_orbit_one_thick : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG),
    orderOf φ.2 ≤ 4 * H.Lw → ∀ a b : ZMod (orderOf φ), Thick H (letter τ φ a) →
      Thick H (letter τ φ b) → plc (letter τ φ a) = plc (letter τ φ b) := by
  intro R H τ φ hord a b ha hb
  have key : ∀ g : R.GG, Thick H g → ∃ s ∈ H.T2, R.tau2 (R.dig s + H.u0) = plc g := by
    intro g hg
    unfold Thick Host.thickPlaces at hg
    simpa [Finset.mem_image] using hg
  exact UpperTheory.KStar.Words.thick_one_place H.T2 H.second_set_range H.u0 τ φ
    ((Nat.le_of_dvd (orderOf_pos _) (R.toFrame.orderOf_hH_dvd φ.2)).trans hord) a.val b.val (key _ ha) (key _ hb)

end GlobalTheory.HTW
