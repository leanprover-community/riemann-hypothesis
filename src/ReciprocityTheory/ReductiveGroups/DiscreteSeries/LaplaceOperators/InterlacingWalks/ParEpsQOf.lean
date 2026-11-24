module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.GlueSt
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.Walk
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.GapBigLap
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem parEps_qOf (k r : ℕ) (hk : 1 ≤ k) : qOf (parEps k r) = r + 1 :=
  noncompactCount_parabolicSign k r hk

theorem parEps_pOf (k r : ℕ) (hk : 1 ≤ k) : pOf (parEps k r) = k + r := by
  have h := compactCount_parabolicSign k r hk
  rw [show parEps k r = Formalism.MainNotions.CayleySignature.eps48 k r from rfl, h]
  omega

theorem walkStep : WalkStepStatement := by
  intro hIS hStep k r u v b h t hk hHC hI hH hL hG hB
  exact walk k r u v b h t (fun lam => BesselNZ (parEps k r) lam u) hk hHC hI hH hL
    (hStep hIS k r (parEps k r) u h hG (parEps_pOf k r hk) (parEps_qOf k r hk)) hB

end ReciprocityTheory.ChartRestriction.DS.Lap
