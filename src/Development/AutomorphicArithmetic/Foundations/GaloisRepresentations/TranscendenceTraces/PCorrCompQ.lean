module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.corrCompQ_of :
    CycComp → WtBC → WtComp → TrBCQ → TrCompQ → CorrCompQ := by
  intro hC hBC hWC hTB hTC S Y X c d
  haveI := c.fin
  haveI := d.fin
  have pb := IsPullback.of_hasPullback d.p c.f
  have hbw := hBC _ _ d.p c.f d.w pb d.wt
  have hw := hWC (pullback.snd d.p c.f) c.p (Wt.comap (pullback.fst d.p c.f) d.w) c.w hbw c.wt
  let e : Corr S X := ⟨pullback d.p c.f, pullback.snd d.p c.f ≫ c.p, pullback.fst d.p c.f ≫ d.f,
    Wt.mul (pullback.snd d.p c.f) (Wt.comap (pullback.fst d.p c.f) d.w) c.w, inferInstance, hw⟩
  refine ⟨e, pullback.fst d.p c.f, pullback.snd d.p c.f, pb, rfl, rfl, rfl, ?_, ?_⟩
  · exact hC c d e _ _ pb rfl rfl rfl
  · intro l _ n i hl hl2
    have hpull : pullHQ l (sch.map (pullback.fst d.p c.f ≫ d.f)) n i =
        pullHQ l (sch.map (pullback.fst d.p c.f)) n i ∘ₗ pullHQ l (sch.map d.f) n i := by
      simp only [pullHQ, Functor.map_comp, pullHl_comp, LinearMap.baseChange_comp]
    have key := hTB l n i _ _ d.p c.f d.w pb d.wt hl2
    show trHQ l (pullback.snd d.p c.f ≫ c.p) _ n i ∘ₗ pullHQ l (sch.map (pullback.fst d.p c.f ≫ d.f)) n i =
      (trHQ l c.p c.w n i ∘ₗ pullHQ l (sch.map c.f) n i) ∘ₗ (trHQ l d.p d.w n i ∘ₗ pullHQ l (sch.map d.f) n i)
    rw [hTC l n i _ _ _ _ hbw c.wt hl, hpull]
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply]
    exact congrArg (trHQ l c.p c.w n i) (LinearMap.congr_fun key _).symm
