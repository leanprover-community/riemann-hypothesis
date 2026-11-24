module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodGeneratorOnOpen
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_period_generator_on_open : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Sp R).Opens) (ψW : PsiOn D W) (a b : D.X), ∃ t : LB.Gen (LB.LinComb D.P.L (lamPts (toUnit (TW W) ≫ D.c a) (toUnit (TW W) ≫ D.c b)) negε), t.IsGen ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ W.toScheme) (z : Z) J, Good D.P.L z J → val t r z J = val (ψW.tau a b) r z J) ∧ ∀ (lam : (TK R).left ⟶ W.toScheme), lam ≫ W.ι = jK R → ∀ z J, Good D.P.L z J → val t lam z J = val (D.tau a b) (𝟙 _) z J := by
  first | exact @GlobalTheory.exists_tau_onOpen | exact GlobalTheory.exists_tau_onOpen | (intros; apply GlobalTheory.exists_tau_onOpen <;> assumption)
