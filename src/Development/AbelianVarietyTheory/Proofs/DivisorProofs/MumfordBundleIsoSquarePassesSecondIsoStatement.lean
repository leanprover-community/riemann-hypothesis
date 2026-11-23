module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoSquarePassesSecondIso
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum


theorem _root_.GlobalTheory.T.mumfordBundleIso_square_passes_second_iso : ∀ {S S' : Scheme.{0}} {f : S' ⟶ S} {B C : Over S} {B₁ C₁ : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj C]
  [IsCommMonObj C] [GrpObj B₁] [IsCommMonObj B₁] [GrpObj C₁] [IsCommMonObj C₁] {δ : C₁.left ⟶ C.left} {M : LB B.left} {N : LB C.left} {M₁ : LB B₁.left} {N₁ : LB C₁.left}
  (gC : IsGrpPullback C₁ C f δ), M.IsLB → N.IsLB → M₁.IsLB → N₁.IsLB → ∀ (β₂ : (G2 B₁).left ⟶ (G2 B).left) (u : LB.Iso (abelian₂ B₁ M₁) ((abelian₂ B M).pull β₂)), u.IsGen →
  ∀ (v' : LB.Iso N₁ (N.pull δ)), v'.IsGen → ∀ {m : (G2 B).left ⟶ (G2 C).left} {m₁ : (G2 B₁).left ⟶ (G2 C₁).left},
    m₁ ≫ sqOf gC = β₂ ≫ m → ∀ (w : LB.Iso (abelian₂ B M) ((abelian₂ C N).pull m)), w.IsGen →
    ∃ w₁ : LB.Iso (abelian₂ B₁ M₁) ((abelian₂ C₁ N₁).pull m₁), w₁.IsGen ∧
      ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 B₁).left) (z : Z) I J I₁ J₁, Good N z I → Good M z J → Good N₁ z I₁ →
        Good M₁ z J₁ → (∏ k, om v' z I I₁ ((p ≫ m₁) ≫ lamφ C₁ k) ^ lamε k) * lamVal w₁ p z I₁ J₁ =
          lamVal w (p ≫ β₂) z I J * lamVal u p z J J₁ := by
  first | exact @GlobalTheory.FactorPull.lam_down_gen | exact GlobalTheory.FactorPull.lam_down_gen | (intros; apply GlobalTheory.FactorPull.lam_down_gen <;> assumption)
