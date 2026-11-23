module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.pairs_holds :
    UpperTheory.Gal.KunnethLefschetz.Pairs := by
  unfold Pairs
  intro k _ d X p hsep hsm
  have hfst : SmoothOfRelativeDimension d (pullback.fst p p) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := d)).of_isPullback
      (IsPullback.of_hasPullback p p).flip hsm
  have hcomp : SmoothOfRelativeDimension (d + d) (pullback.fst p p ≫ p) :=
    smoothOfRelativeDimension_comp (n := d) (m := d) (pullback.fst p p) p
  have hid : SmoothOfRelativeDimension 0 (𝟙 (S k)) := inferInstance
  refine ⟨⟨inferInstance, hcomp, ?_⟩, fun y => ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · rw [pullback.diagonal_fst_assoc]
    exact hsm
  · have h1 : IsClosedImmersion (y.1 ≫ p) := by rw [y.2]; infer_instance
    exact IsClosedImmersion.of_comp y.1 p
  · rw [Nat.zero_add]; exact hsm
  · rw [y.2]; exact hid
  · have key : ∀ s : PullbackCone (slice y) (pullback.diagonal p),
        s.fst = s.snd ∧ s.fst ≫ p ≫ y.1 = s.snd := by
      intro s
      have c := s.condition
      have c1 := congrArg (· ≫ pullback.fst p p) c
      have c2 := congrArg (· ≫ pullback.snd p p) c
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
        pullback.diagonal_snd, Category.comp_id] at c1 c2
      exact ⟨c1, c2⟩
    refine IsPullback.of_isLimit' ⟨?_⟩ (PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ p) ?_ ?_ ?_)
    · have e1 : slice y ≫ pullback.fst p p = 𝟙 X := pullback.lift_fst _ _ _
      have e2 : slice y ≫ pullback.snd p p = p ≫ y.1 := pullback.lift_snd _ _ _
      have hy : y.1 ≫ p ≫ y.1 = y.1 := by rw [← Category.assoc, y.2, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, e1, Category.assoc, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, e2, hy, Category.assoc, pullback.diagonal_snd, Category.comp_id]
    · intro s
      rw [Category.assoc, (key s).2, (key s).1]
    · intro s
      rw [Category.assoc, (key s).2]
    · intro s m h1 _
      rw [← h1, Category.assoc, y.2, Category.comp_id]
