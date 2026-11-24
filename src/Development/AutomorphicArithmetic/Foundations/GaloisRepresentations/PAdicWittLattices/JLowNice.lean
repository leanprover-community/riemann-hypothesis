module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.JumpStepOf
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

private theorem sq_bc {T Y S B : Scheme.{0}} (s : T ⟶ Y) (p : Y ⟶ S) (c : B ⟶ S) :
    IsPullback (pullback.fst (s ≫ p) c)
      (pullback.lift (pullback.fst (s ≫ p) c ≫ s) (pullback.snd (s ≫ p) c)
        (by rw [Category.assoc, pullback.condition]) : pullback (s ≫ p) c ⟶ pullback p c)
      s (pullback.fst p c) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd p c) (v₂₂ := p) (h₃₁ := c) ?_ ?_
    (IsPullback.of_hasPullback p c)
  · rw [pullback.lift_snd]
    exact IsPullback.of_hasPullback (s ≫ p) c
  · rw [pullback.lift_fst]

theorem UpperTheory.Gal.G3.jLowNice :
    FEtBasic → PositivityTheory.AutomorphicGaloisHodgeTate.G8.LowNice := by
  intro hb k L _ _ H θ O _ _ C D
  haveI : Smooth C.p := C.smooth
  refine ⟨?_, ?_, ?_⟩
  · show Smooth (pullback.snd C.p (UpperTheory.Gal.Int.Geo.gen O k))
    infer_instance
  · exact GlobalTheory.ProjSpace.isProjOver_pullback_snd (algebraMap O k) C.proj
  · intro g
    exact ⟨D.d g, hb.1 _ _ _ _ _ (sq_bc (D.s g) C.p (UpperTheory.Gal.Int.Geo.gen O k)) (D.fet g)⟩
