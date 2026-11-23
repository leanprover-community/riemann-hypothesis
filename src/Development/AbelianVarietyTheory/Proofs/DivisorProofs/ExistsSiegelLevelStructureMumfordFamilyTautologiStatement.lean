module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelLevelStructureMumfordFamilyTautologi
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_siegelLevelStructure_mumfordFamily_tautological : ∀ (g n : ℕ) (φ : InvFun ℤ), 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) → ∀ c : SiegPre g n (zetaAway n) (spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b)), c.Principal → (∃ (a : c.A.left ⟶ G₁.left) (a₂ : (G2 c.A).left ⟶ (G2 G₁).left), IsGrpPullback c.A G₁ (spMap (algebraMap C.R (Localization.Away (∏ k, C.t k)))) a ∧ IsSquare a a₂ ∧ LBIso c.P (P.pull a₂)) → ∃ (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (yU : Sp (Localization.Away (∏ k, C.t k)) ⟶ F.X) (l : Localization.Away (∏ k, C.t k) →+* FractionRing C.R), C.IsFam F G₁ y α₁ ∧ SiegPB c F.univ yU ∧ l.comp (algebraMap C.R (Localization.Away (∏ k, C.t k))) = algebraMap C.R (FractionRing C.R) ∧ y = spMap l ≫ yU := by
  first | exact @GlobalTheory.TChart.Taut.exists_isFam_of_siegPre | exact GlobalTheory.TChart.Taut.exists_isFam_of_siegPre | (intros; apply GlobalTheory.TChart.Taut.exists_isFam_of_siegPre <;> assumption)
