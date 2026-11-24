module

public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.PolyDef
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.PolyCons
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.PolyPb
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Amb

variable {k : Type} [CommRing k]

theorem polyCovered_pSpace [IsDomain k] (N : ℕ) : PolyCovered (PSpace.str k N) N :=
  polyCovered_pSpace' N

theorem polyCovered_pullback [IsDomain k] {X Y : Scheme.{0}} (f : X ⟶ Sp k) (g : Y ⟶ Sp k) (a b : ℕ) (hf : PolyCovered f a)
    (hg : PolyCovered g b) : PolyCovered (pullback.fst f g ≫ f) (a + b) :=
  polyCovered_pullback' f g a b hf hg

theorem isIntegral_of_polyCovered [IsDomain k] {X : Scheme.{0}} (f : X ⟶ Sp k) (d : ℕ) (h : PolyCovered f d) :
    IsIntegral X :=
  isIntegral_of_polyCovered' f d h

theorem topologicalKrullDim_of_polyCovered [IsDomain k] [IsNoetherianRing k] (hk : ringKrullDim k = 1)
    {X : Scheme.{0}} (f : X ⟶ Sp k) (d : ℕ) (h : PolyCovered f d) : topologicalKrullDim X = (d + 1 : ℕ) :=
  topologicalKrullDim_of_polyCovered' hk f d h

theorem ringKrullDim_eq_one [IsDomain k] [CharZero k] (hf : Module.Finite ℤ k) : ringKrullDim k = 1 :=
  ringKrullDim_eq_one' hf

end GlobalTheory.Amb
