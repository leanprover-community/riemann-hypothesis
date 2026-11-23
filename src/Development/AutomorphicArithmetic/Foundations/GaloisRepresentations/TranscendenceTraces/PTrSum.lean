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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trSum_of :
    SumEx → SumNat → PtInj → FibFin → TrSum := by
  intro hEx hNat hInj hFin q _ i Z S p _ w hw hq
  have uniq : ∀ (A : Sq p) (a : Sec (tw q i) A.V) (b b' : Sec (tw q i) A.U),
      IsSum w A a b → IsSum w A a b' → b = b' := by
    intro A a b b' hb hb'
    apply hInj q i A.U b b'
    intro Ω _ _ x
    rw [hb Ω x, hb' Ω x]
  have ex : ∃ t : Fam0 p (tw q i) (tw q i),
      ∀ (A : Sq p) (a : Sec (tw q i) A.V), IsSum w A a (t.app A a) := by
    choose f hf using fun (A : Sq p) (a : Sec (tw q i) A.V) => hEx q i p w hw hq A a
    refine ⟨⟨fun A => { toFun := f A, map_zero' := ?_, map_add' := ?_ }, ?_⟩, ?_⟩
    · refine uniq A 0 _ _ (hf A 0) ?_
      intro Ω _ _ x
      simp [Sec.res]
    · intro a a'
      refine uniq A (a + a') _ _ (hf A (a + a')) ?_
      intro Ω _ _ x
      have hfin : (fib A.r x).Finite := by
        haveI := Sq.finite A
        exact hFin A.r Ω x
      rw [show Sec.res x (f A a + f A a') = Sec.res x (f A a) + Sec.res x (f A a') by simp [Sec.res],
        hf A a Ω x, hf A a' Ω x, ← finsum_mem_add_distrib hfin]
      apply finsum_mem_congr rfl
      intro z _
      simp [Sec.res, smul_add]
    · intro A B t a
      exact uniq A (Sec.res t.k a) _ _ (hNat _ (tw q i) w t a (f B a) (hf B a)) (hf A _)
    · intro A a
      exact hf A a
  exact pick_spec ex
