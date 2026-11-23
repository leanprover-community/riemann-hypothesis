module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerDatumOfIsotropicSaturated
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_lower_datum_of_isotropic_saturated : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (Z : Submodule (𝓞 E) Dw.La),
  GlobalTheory.LowDat.IsIsoSat Dw Z → ∃ (D' : Datum H) (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La), GlobalTheory.LowDat.IsLower Dw D' Z f ∧
    D'.p = Dw.p - Module.finrank (𝓞 E) Z ∧ D'.q = Dw.q - Module.finrank (𝓞 E) Z := by
  first | exact @GlobalTheory.LowDat.exists_lowerDatum | exact GlobalTheory.LowDat.exists_lowerDatum | (intros; apply GlobalTheory.LowDat.exists_lowerDatum <;> assumption)
