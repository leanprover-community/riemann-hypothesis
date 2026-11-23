module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFibrePullbackSiegelTraitModel
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.exists_genericFibre_pullback_siegelTrait_model : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F) (W : Type) [CommRing W] [IsDomain W] (f : T.V →+* W) (fK : FractionRing T.V →+* FractionRing W), (∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) → ∃ κ : ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)).left ⟶ T.A.A.left, IsGrpPullback ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)) T.A.A (spMap fK) κ ∧ κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) = pullback.fst ((Over.pullback (spMap f)).obj T.G).hom (jK W) ≫ pullback.fst T.G.hom (spMap f) := by
  first | exact @GlobalTheory.Poinc.GenFibre.exists_generic_pullback | exact GlobalTheory.Poinc.GenFibre.exists_generic_pullback | (intros; apply GlobalTheory.Poinc.GenFibre.exists_generic_pullback <;> assumption)
