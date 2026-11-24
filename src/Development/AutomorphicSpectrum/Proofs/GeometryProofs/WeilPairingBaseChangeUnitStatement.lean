module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilPairingBaseChangeUnit
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.weil_pairing_base_change_unit : ∀ {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB → ∀ (k M : Type) [Field k] [Field M] (j : k →+* M) (q : Sp k ⟶ X) (q' : Sp M ⟶ X), q' = spMap j ≫ q → ∀ (n : ℤ) (x y : Over.mk q ⟶ G) (x' y' : Over.mk q' ⟶ G), x'.left = spMap j ≫ x.left → y'.left = spMap j ≫ y.left → ∀ (c : kˣ) (c' : Mˣ), Out.WeilIs G L n x y (unitOn c) → Out.WeilIs G L n x' y' (unitOn c') → c' = Units.map j.toMonoidHom c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.weilIs_fieldExt | exact GlobalTheory.CompanionTheory.Ar.weilIs_fieldExt | (intros; apply GlobalTheory.CompanionTheory.Ar.weilIs_fieldExt <;> assumption)
