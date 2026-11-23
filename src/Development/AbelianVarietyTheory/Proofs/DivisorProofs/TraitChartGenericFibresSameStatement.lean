module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitChartGenericFibresSame
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.trait_chart_generic_fibres_same : ∀ {g n : ℕ} {φ : InvFun ℤ} (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → GlobalTheory.Mum.CanonOn C.Q (PrimeSpectrum.basicOpen (∏ k, C.t k)) G₁ P → ∀ (T : GlobalTheory.Poinc.Trait F) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (θ : C.R →+* V') (f : T.V →+* V') (fK : FractionRing T.V →+* FractionRing V'), IsCN V' → IsLocalHom θ → (∀ k, θ (C.s k) ≠ 0) → (∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a)) → ∀ (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin C.T.r → ℤ)), DegFrom C.T (θ.comp C.iw) (fun k => θ (C.s k)) C.form n D'.toPre e → ∀ (G' : Over (Sp V')) [GrpObj G'] [IsCommMonObj G'] (πG : G'.left ⟶ T.G.left) (A' : PolAV (Sp (FractionRing V'))) (U' : Unif (maximalIdeal V') D' A' G'), IsUnifAlong F T.y (T.U.gen.hom.left ≫ T.α) f πG U' → SameFib F.univ.A F.univ.P (spMap fK ≫ T.y) G₁ P (spMap ((algebraMap V' (FractionRing V')).comp θ)) := by
  first | exact @GlobalTheory.TChart.sameFib_trait_chart | exact GlobalTheory.TChart.sameFib_trait_chart | (intros; apply GlobalTheory.TChart.sameFib_trait_chart <;> assumption)
