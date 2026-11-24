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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trChar_of :
    FL → OpEq → TrSum → PtInj → TrChar := by
  intro hFL hOp hTS hPI q _ i Z S p _ w hw hq
  have hOver : (trFam p w q i).Over (tr0 p w q i) := by
    unfold trFam
    exact GlobalTheory.EtC.pick_spec (hFL q p (tw q i) (tw q i) (tr0 p w q i)).1
  refine ⟨hOver, ?_, ?_⟩
  · intro A a
    exact ⟨(tr0 p w q i).app A a, hOver A a, hTS q i p w hw hq A a⟩
  · intro τ hτ n
    have hτo : τ.Over (tr0 p w q i) := by
      intro A a
      obtain ⟨b, hb, hs⟩ := hτ A a
      have hbe : b = (tr0 p w q i).app A a := by
        apply hPI q i A.U
        intro Ω _ _ x
        rw [hs Ω x, hTS q i p w hw hq A a Ω x]
      rw [hb, hbe]
    exact hOp q p (tw q i) (tw q i) (tr0 p w q i) (trFam p w q i) τ hOver hτo n
