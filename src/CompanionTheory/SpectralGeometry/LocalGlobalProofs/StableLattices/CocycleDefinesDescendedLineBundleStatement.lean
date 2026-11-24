module

public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CocycleDefinesDescendedLineBundle
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.cocycle_defines_descended_line_bundle : H90 → ∀ {Z Q : Scheme.{0}} (h : Z ⟶ Q), Flat h → LocallyOfFinitePresentation h → Surjective h →
    ∀ (u : Γ(pullback h h, ⊤)) (hu : IsUnit u),
    (∀ (W : Scheme.{0}) (a b c : W ⟶ Z) (hab : a ≫ h = b ≫ h) (hbc : b ≫ h = c ≫ h),
      (pullback.lift a c (hab.trans hbc)).appTop u =
        (pullback.lift a b hab).appTop u * (pullback.lift b c hbc).appTop u) →
    ∃ N : LB Q, N.IsLB ∧ ∃ T : LB.Gen (N.pull h), T.IsGen ∧
      ∀ (W : Scheme.{0}) (a b : W ⟶ Z) (hab : a ≫ h = b ≫ h) (w : W) (i : N.ι), h (a w) ∈ N.U i →
        gm a w ((N.pull h).U fun _ => i) (T.s fun _ => i) =
          gm (pullback.lift a b hab) w ⊤ hu.unit * gm b w ((N.pull h).U fun _ => i) (T.s fun _ => i) := by
  first | exact @GlobalTheory.CompanionTheory.LbCocycle.exists_lb | exact GlobalTheory.CompanionTheory.LbCocycle.exists_lb | (intros; apply GlobalTheory.CompanionTheory.LbCocycle.exists_lb <;> assumption)
