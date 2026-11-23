module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIsTorusExtensionOnPointsModIdeal
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_isTorusExtensionOnPoints_mod_ideal : ∀ (W : Type) [CommRing W] [IsDomain W] (I : Ideal W) (D : Out.DegPre W) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (gt : Out.GtCoord I D 0 G) (Ω : Type) [Field Ω] (β : W →+* Ω), (∀ a ∈ I, β a = 0) → ∃ (τ : PtHom (spMap β) (spMap β) G D.P.A) (io : TorHom (spMap β) G D.X), IsTorExt (spMap β) (spMap β) G D.P.A D.X τ io ∧ ∀ (A : Type) [CommRing A] [Algebra Ω A] (x : overAt (spMap β) A ⟶ G) (x₀ : Sp A ⟶ (Out.thickObj W I 0 G).left), x₀ ≫ (Out.fstG I 0 G).left = x.left → (τ A x).left = x₀ ≫ gt.pG.left := by
  first | exact @GlobalTheory.TorExtPoints.exists_isTorExt | exact GlobalTheory.TorExtPoints.exists_isTorExt | (intros; apply GlobalTheory.TorExtPoints.exists_isTorExt <;> assumption)
