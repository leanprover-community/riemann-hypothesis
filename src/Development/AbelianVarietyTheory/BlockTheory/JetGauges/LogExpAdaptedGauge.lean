module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
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
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.IndefiniteRowSideFullHecke.LogExpAdaptedGauge

section Chart

variable {k : Type} [CommRing k] {d : ℕ}

def linMap (U : Matrix (Fin d) (Fin d) k) : Pt k 1 d :=
  fun i => ∑ j : Fin d, MvPowerSeries.C (U i j) * X ((0 : Fin 1), j)

end Chart


variable {R : Type} [CommRing R] {d : ℕ} (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

variable {O : Type} [CommRing O] [StarRing O]



variable {C : Type} [NormedField C] {d : ℕ}



variable {C : Type} [NormedField C] [IsUltrametricDist C] [CharZero C]
  {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {d : ℕ}


end GlobalTheory.IndefiniteRowSideFullHecke.LogExpAdaptedGauge
