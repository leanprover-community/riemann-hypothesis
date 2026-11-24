module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPointsOpenIntegralCover
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsFiniteNonempty
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
theorem _root_.GlobalTheory.T.generic_points_finite_nonempty :
    _root_.GlobalTheory.CompanionTheory.Ar.Top.Given →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
      (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)),
      {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}.Finite ∧
      {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}.Nonempty := by
  intro hG E _ _ _ H D l Xo c Y
  have : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have : TopologicalSpace.NoetherianSpace Y.X := GlobalTheory.ModelSum.noetherianSpace_of_isProjOver Y.proj
  have : Nonempty Y.X := Comps.model_nonempty Y (Comps.moduli_nonempty hG.1.2.2.1 Xo)
  exact ⟨Comps.finite_maximal_points Y.X, Comps.nonempty_maximal_points Y.X⟩
