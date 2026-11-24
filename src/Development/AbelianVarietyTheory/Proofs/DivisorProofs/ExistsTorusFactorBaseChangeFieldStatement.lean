module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusFactorBaseChangeField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_torus_factor_baseChange_field : ∀ (k k' : Type) [CommRing k] [CommRing k'], IsField k' → ∀ (ρ : k →+* k') (G₀ : Over (Sp k)) [GrpObj G₀] (G'₀ : Over (Sp k')) [GrpObj G'₀] (β₀ : G'₀.left ⟶ G₀.left), IsGrpPullback G'₀ G₀ (spMap ρ) β₀ → ∀ (X X' : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] (Q₀ : GlobalTheory.UU.TQ G₀ X) (Q'₀ : GlobalTheory.UU.TQ G'₀ X'), ∃ (i₁ : splitTorus (Sp k') X ⟶ G'₀) (e : splitTorus (Sp k') X ⟶ splitTorus (Sp k') X'), IsMonHom e ∧ e ≫ Q'₀.i = i₁ ∧ GlobalTheory.UU.TorusCompat (spMap ρ) β₀ i₁ Q₀.i := by
  first | exact @GlobalTheory.Mum.exists_torus_factor | exact GlobalTheory.Mum.exists_torus_factor | (intros; apply GlobalTheory.Mum.exists_torus_factor <;> assumption)
