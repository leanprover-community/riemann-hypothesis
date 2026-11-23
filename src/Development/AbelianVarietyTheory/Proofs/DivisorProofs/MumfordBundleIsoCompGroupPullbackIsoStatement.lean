module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCompGroupPullbackIso
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
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.PrimCocycle
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.mumfordBundleIso_comp_group_pullback_iso : ∀ {S S₁ S₂ S₀ : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (B' : Over S₁) [GrpObj B'] (G' : Over S₂) [GrpObj G'] [IsCommMonObj G'] (T : Over S₀) [GrpObj T] [IsCommMonObj T] (f₁ : S₁ ⟶ S) (f₂ : S₂ ⟶ S₁) (β' : B'.left ⟶ G.left) (Φ : G'.left ⟶ B'.left) (φ : G'.left ⟶ G.left) (β₂ : (G2 B').left ⟶ (G2 G).left) (β₂' : (G2 B').left ⟶ (G2 T).left) (L : LB G.left) (L' : LB G'.left) (M : LB T.left) (gp' : IsGrpPullback B' G f₁ β') (gΦ : IsGrpPullback G' B' f₂ Φ), IsSquare β' β₂ → Φ ≫ β' = φ → L.IsLB → L'.IsLB → M.IsLB → ∀ (v : LB.Iso L' (L.pull φ)) (w₁ : LB.Iso ((abelian₂ G L).pull β₂) ((abelian₂ T M).pull β₂')), v.IsGen → w₁.IsGen → ∃ w : LB.Iso (abelian₂ G' L') ((abelian₂ T M).pull (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂')), w.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 G').left) (z : Z) (J : (Z ⟶ T.left) → M.ι) (J₁ : (Z ⟶ G.left) → L.ι) (J' : (Z ⟶ G'.left) → L'.ι), Good M z J → Good L z J₁ → Good L' z J' → lamVal w p z J J' = isoVal w₁ (p ≫ GlobalTheory.HalfBC.sqOf gΦ) z J J₁ * ∏ I, gw v (p ≫ lamφ G' I) z (J₁ ((p ≫ lamφ G' I) ≫ φ)) (J' (p ≫ lamφ G' I)) ^ lamε I := by
  first | exact @GlobalTheory.LamPullComp.lamIso_comp_pull | exact GlobalTheory.LamPullComp.lamIso_comp_pull | (intros; apply GlobalTheory.LamPullComp.lamIso_comp_pull <;> assumption)
