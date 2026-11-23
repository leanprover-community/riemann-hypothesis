module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedIdempotentFactorPairingPeriodsPullback
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

theorem _root_.GlobalTheory.T.polarisedIdempotentFactor_pairing_periods_pullback : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (D₀ : DegPre R) (F : PFactor Q D₀) (D₁ : DegPre V) (hD : IsPullDeg θ D₀ D₁) [Module F.O D₁.X] (o₁ : D₁.OAct F.O), (∀ (a : F.O) (y : D₁.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (o₁.onB.act a).left ≫ GlobalTheory.PsiEvenPull.proj hD = GlobalTheory.PsiEvenPull.proj hD ≫ (F.o.onB.act a).left) → ∀ (Q' : Data V) (ex : Q'.X ≃+ Q.X), PullData Q θ Q' ex → ∃ β : Q'.B.left ⟶ Q.B.left, IsGrpPullback Q'.B Q.B (spMap θ) β ∧ (∀ a, (Q'.c a).left ≫ β = spMap θ ≫ (Q.c (ex a)).left) ∧ ∀ (inc : Q'.B ⟶ D₁.P.A) (xi : Q'.X →+ D₁.X), inc.left ≫ GlobalTheory.PsiEvenPull.proj hD = β ≫ F.inc.left → (∀ y, hD.xe (xi y) = F.xi (ex y)) → (∀ y, D₁.c (xi y) = Q'.c y ≫ inc) → ∃ w : LB.Iso (abelian₂ Q'.B Q'.M.L) ((abelian₂ D₁.P.A D₁.P.L).pull (lift (fst Q'.B Q'.B ≫ inc) (snd Q'.B Q'.B ≫ inc ≫ o₁.onB.act F.f) : G2 Q'.B ⟶ G2 D₁.P.A).left), w.IsGen ∧ ∀ a b z J J', Good D₁.P.L z J → Good Q'.M.L z J' → val (Q'.tau a b) (𝟙 _) z J' = lamVal w (lift (toUnit (TK V) ≫ Q'.c a) (toUnit (TK V) ≫ Q'.c b)).left z J J' * val (D₁.tau (xi a) (F.f • xi b)) (𝟙 _) z J := by
  first | exact @GlobalTheory.FactorTau.factor_tau_pull | exact GlobalTheory.FactorTau.factor_tau_pull | (intros; apply GlobalTheory.FactorTau.factor_tau_pull <;> assumption)
