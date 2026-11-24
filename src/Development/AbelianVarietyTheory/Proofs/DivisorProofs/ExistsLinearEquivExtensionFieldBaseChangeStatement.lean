module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionOfIsPushout
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivExtensionFieldBaseChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExtensionSecPull

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_linearEquiv_extension_fieldBaseChange : ∀ (K F V V' W W' : Type) [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V'] [AddCommGroup W] [Module F W] [AddCommGroup W'] [Module F W'] (a : V →ₛₗ[algebraMap K F] W) (d : V' →ₛₗ[algebraMap K F] W'), GlobalTheory.FieldBaseChange.IsExtension a → GlobalTheory.FieldBaseChange.IsExtension d → ∀ e : V →ₗ[K] V', Function.Bijective e → ∃ e' : W →ₗ[F] W', Function.Bijective e' ∧ ∀ v, e' (a v) = d (e v) := by
  first | exact @GlobalTheory.FieldBaseChange.exists_bijective_extension | exact GlobalTheory.FieldBaseChange.exists_bijective_extension | (intros; apply GlobalTheory.FieldBaseChange.exists_bijective_extension <;> assumption)
