module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TheoremOfCubeGeneratorExists
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
import Mathlib.Tactic.NormNum.RealSqrt
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.theorem_of_cube_generator_exists : ∀ (S : Scheme.{0}) (A X Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ (q : X ⟶ Y) (M : LB (A ⊗ X).left), M.IsLB →
    Triv (ev M (1 : X ⟶ A) (𝟙 X)) →
    (∀ (T : Over S) (x x' : T ⟶ X), x ≫ q = x' ≫ q →
        LBIso (ev M (fst A T) (snd A T ≫ x)) (ev M (fst A T) (snd A T ≫ x'))) →
    ∃ c : LB.Gen (LB.LinComb M (K := Fin 2) ![pullback.fst (lift (fst A X) (snd A X ≫ q)).left (lift (fst A X) (snd A X ≫ q)).left,
        pullback.snd (lift (fst A X) (snd A X ≫ q)).left (lift (fst A X) (snd A X ≫ q)).left] ![-1, 1]), c.IsGen ∧
      ∀ (W : Scheme.{0}) (a b d : W ⟶ (A ⊗ X).left) (hab : a ≫ (lift (fst A X) (snd A X ≫ q)).left = b ≫ (lift (fst A X) (snd A X ≫ q)).left)
        (hbd : b ≫ (lift (fst A X) (snd A X ≫ q)).left = d ≫ (lift (fst A X) (snd A X ≫ q)).left) (w : W) (J : (W ⟶ (A ⊗ X).left) → M.ι), Good M w J →
        val c (pullback.lift a b hab) w J * val c (pullback.lift b d hbd) w J = val c (pullback.lift a d (hab.trans hbd)) w J := by
  exact @GlobalTheory.CompanionTheory.RigDescLink.descent_datum
