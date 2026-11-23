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

theorem UpperTheory.Gal.TranscendenceTraces.trPush_of :
    TrChar → FamPush → WtPush → RpBasic → RpOp → TrPush := by
  intro hTr hFam hWt hRp hOp q _ n i Z Z' S h p _ _ w hw hq x
  obtain ⟨σ, hσ, hσd⟩ := hFam q i h p w (trFam (h ≫ p) w q i) (hTr q i (h ≫ p) w hw hq).2.1
  have hw' := hWt h p w hw
  have e2 : tr p (Wt.push h w) q n i = σ.op n := by
    ext y
    exact (hTr q i p (Wt.push h w) hw' hq).2.2 σ hσ n ▸ rfl
  rw [e2]
  obtain ⟨a, ha⟩ := (hRp (ZMod q) (res (ZMod q) (tw q i)) Z' n).1 x
  have h1 := hOp (ZMod q) (ZMod q) σ n x a ha
  have h2 := hOp (ZMod q) (ZMod q) (trFam (h ≫ p) w q i) n _ _
    ((hRp (ZMod q) (res (ZMod q) (tw q i)) Z' n).2.2.2.1 Z h x a ha)
  exact ((hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.1 _ _ _ _ h2 h1).2.1 (hσd n a).symm
