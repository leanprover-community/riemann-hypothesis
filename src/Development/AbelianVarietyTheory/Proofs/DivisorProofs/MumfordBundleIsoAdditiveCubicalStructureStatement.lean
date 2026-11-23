module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoAdditiveCubicalStructure
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
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.mumfordBundleIso_additive_cubicalStructure : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (Z : Over (Sp V)) (x x' y : Z ⟶ D.P.A) (x₀ x₀' y₀ : Over.mk (Z.hom ≫ spMap ω) ⟶ T.B), x.left ≫ β = x₀.left → x'.left ≫ β = x₀'.left → y.left ≫ β = y₀.left → ∀ (z : Z.left) J J', Good T.M.L z J → Good D.P.L z J' → lamVal w (lift (x * x') y).left z J J' * cubV D.cub z J' x x' y = lamVal w (lift x y).left z J J' * lamVal w (lift x' y).left z J J' * @id (Z.left.presheaf.stalk z)ˣ (cubV T.cub (T := Over.mk (Z.hom ≫ spMap ω)) z J x₀ x₀' y₀) ∧ lamVal w (lift y (x * x')).left z J J' * cubV D.cub z J' y x x' = lamVal w (lift y x).left z J J' * lamVal w (lift y x').left z J J' * @id (Z.left.presheaf.stalk z)ˣ (cubV T.cub (T := Over.mk (Z.hom ≫ spMap ω)) z J y₀ x₀ x₀') := by
  first | exact @GlobalTheory.TInj.lamVal_add_cub | exact GlobalTheory.TInj.lamVal_add_cub | (intros; apply GlobalTheory.TInj.lamVal_add_cub <;> assumption)
