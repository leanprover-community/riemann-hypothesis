module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtMostTwoThickInWindowLongOrbitStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordMarkedClustersOfAtMostTwoInWindowStatement
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

namespace GlobalTheory

theorem long_clusters : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG) (j : ℕ), 4 * H.Lw < orderOf φ.2 → 1 ≤ j →
    2 * j + 2 ≤ H.Lw →
    Clusters (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) j ∧ j + 1 ≤ orderOf φ := by
  intro R H τ φ j h4 hj hjL
  have hpos : 0 < orderOf φ := orderOf_pos φ
  have hdvd : orderOf φ.2 ∣ orderOf φ := orderOf_snd_dvd_orderOf
  have hle : orderOf φ.2 ≤ orderOf φ := Nat.le_of_dvd hpos hdvd
  have hw := GlobalTheory.T.atMostTwoThick_in_window_long_orbit H τ φ h4
  refine ⟨GlobalTheory.T.cyclicWord_markedClusters_of_atMostTwoInWindow _ H.Lw j hj (by omega) (by omega) hw, by omega⟩

end GlobalTheory
