module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.WtDegConst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trBCQ_of :
    TrHl → TrBC → WtBC → TrBCQ := by
  intro hHl hBC hWt l _ n i Z' S' Z S v p' p g _ w hpb hw hl
  haveI : IsFinite p' := MorphismProperty.of_isPullback (P := @IsFinite) hpb inferInstance
  have hw' : IsWt p' (Wt.comap v w) := hWt v p' p g w hpb hw
  have hl' : IsUnit ((l : ℕ) : Γ(S', ⊤)) := by
    have := hl.map g.appTop.hom
    rwa [map_natCast] at this
  have key : pullHl l (sch.map g) n i ∘ₗ trHl l p w n i =
      trHl l p' (Wt.comap v w) n i ∘ₗ pullHl l (sch.map v) n i := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext k
    have hk : IsUnit ((↑(l ^ k) : ℕ) : Γ(S, ⊤)) := by
      rw [Nat.cast_pow]
      exact hl.pow k
    show (pull (ZMod (l ^ k)) (sch.map g) (tw (l ^ k) i) n) ((trHl l p w n i x).1 k) =
      (trHl l p' (Wt.comap v w) n i (pullHl l (sch.map v) n i x)).1 k
    rw [hHl l n i p w hw hl x k, hHl l n i p' (Wt.comap v w) hw' hl' _ k]
    exact hBC (l ^ k) n i v p' p g w hpb hw hk (x.1 k)
  unfold trHQ pullHQ
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, key]
