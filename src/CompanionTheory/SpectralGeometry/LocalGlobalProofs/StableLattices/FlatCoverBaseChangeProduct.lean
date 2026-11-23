module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.RigDesc

theorem isPullback_snd_lift_fst_snd_comp {S : Scheme.{0}} (A X Y : Over S) (q : X ⟶ Y) :
    IsPullback (snd A X).left (lift (fst A X) (snd A X ≫ q)).left q.left (snd A Y).left := by
  have hX : IsPullback (fst A X).left (snd A X).left A.hom X.hom := by
    simpa only [Over.fst_left, Over.snd_left] using IsPullback.of_hasPullback A.hom X.hom
  have hY : IsPullback (fst A Y).left (snd A Y).left A.hom Y.hom := by
    simpa only [Over.fst_left, Over.snd_left] using IsPullback.of_hasPullback A.hom Y.hom
  have e₁ : (lift (fst A X) (snd A X ≫ q)).left ≫ (fst A Y).left = (fst A X).left := by
    rw [← Over.comp_left, lift_fst]
  have e₂ : (lift (fst A X) (snd A X ≫ q)).left ≫ (snd A Y).left = (snd A X).left ≫ q.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hout : IsPullback ((lift (fst A X) (snd A X ≫ q)).left ≫ (fst A Y).left) (snd A X).left
      A.hom (q.left ≫ Y.hom) := by
    rw [e₁, Over.w q]
    exact hX
  exact (IsPullback.of_right hout e₂ hY).flip

theorem lift_fst_snd_comp_flat_lfp_surjective :
    ∀ (S : Scheme.{0}) (A X Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ q : X ⟶ Y, Flat q.left →
    LocallyOfFinitePresentation q.left → Surjective q.left →
    Flat (lift (fst A X) (snd A X ≫ q)).left ∧ LocallyOfFinitePresentation (lift (fst A X) (snd A X ≫ q)).left ∧
      Surjective (lift (fst A X) (snd A X ≫ q)).left := by
  intro S A X Y _ _ q hf hl hs
  have h := isPullback_snd_lift_fst_snd_comp A X Y q
  exact ⟨MorphismProperty.of_isPullback (P := @Flat) h hf,
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) h hl,
    MorphismProperty.of_isPullback (P := @Surjective) h hs⟩

end GlobalTheory.CompanionTheory.RigDesc
