module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.IsSimpleTriv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset

namespace CompanionTheory.RgExh.Hk

open Formalism.REAL (GlRel qdet)

variable {n : ℕ}

theorem glRel_tau (X : GMod n) : GlRel (fun a b => -X.E b a) := by
  intro a b c d
  have h := X.gl b a d c
  simp only [neg_mul_neg]
  rw [h]
  rcases eq_or_ne a d with h1 | h1 <;> rcases eq_or_ne b c with h2 | h2
  · subst h1; subst h2; simp; abel
  · subst h1; simp [h2, Ne.symm h2]
  · subst h2; simp [h1, Ne.symm h1]
  · simp [h1, h2, Ne.symm h1, Ne.symm h2]

def tauMod (X : GMod n) : GMod n := ⟨X.V, fun a b => -X.E b a, glRel_tau X⟩

def QdetTau : Prop :=
  ∀ (n : ℕ) (X : GMod n) (u : ℂ), qdet (tauMod X).E u = ((-1 : ℂ) ^ n) • qdet X.E (-u + ((n : ℂ) - 1))

end CompanionTheory.RgExh.Hk
