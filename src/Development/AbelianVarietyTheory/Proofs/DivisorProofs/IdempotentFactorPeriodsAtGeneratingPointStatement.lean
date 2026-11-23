module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorPeriodsAtGeneratingPoint
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.idempotent_factor_periods_at_generating_point : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (D₀ : DegPre R) (F : PFactor Q D₀) (W : (Sp R).Opens) (ψW : PsiOn D₀ W) (g : (TK V).left ⟶ W.toScheme), g ≫ W.ι = jK V ≫ spMap θ → ∀ (a b : Q.X) (u : LB.Gen (LB.LinComb Q.M.L (lamPts (Q.c a) (Q.c b)) negε)) (x y : R) (k : (FractionRing R)ˣ) (k' : (FractionRing V)ˣ), u.IsGen → θ y ≠ 0 → (k : FractionRing R) * algebraMap R _ y = algebraMap R _ x → (k' : FractionRing V) * algebraMap V _ (θ y) = algebraMap V _ (θ x) → (∀ z J, Good Q.M.L z J → val (Q.tau a b) (𝟙 _) z J = gm (𝟙 (TK R).left) z ⊤ (unitOn k) * val u (toUnit (TK R)).left z J) → ∀ z J J', Good D₀.P.L z J → Good Q.M.L z J' → gm (𝟙 (TK V).left) z ⊤ (unitOn k') * val u ((TK V).hom ≫ spMap θ) z J' = lamVal F.w (((TK V).hom ≫ spMap θ) ≫ (lift (Q.c a) (Q.c b)).left) z J J' * val (ψW.tau (F.xi a) (F.f • F.xi b)) g z J := by
  first | exact @GlobalTheory.FactorPeriod.factor_period | exact GlobalTheory.FactorPeriod.factor_period | (intros; apply GlobalTheory.FactorPeriod.factor_period <;> assumption)
