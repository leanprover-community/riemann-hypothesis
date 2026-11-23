module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

abbrev KPair (ε : Fin n → Bool) : Type := {ab : Fin n × Fin n // ab.2 < ab.1 ∧ ε ab.1 = ε ab.2}

abbrev KCo (ε : Fin n → Bool) : Type := (Fin n → ℝ) × (KPair ε → ℂ)

def kMat {ε : Fin n → Bool} (w : KCo ε) : Matrix (Fin n) (Fin n) ℂ := fun a b =>
  if a = b then Complex.I * ((w.1 a : ℝ) : ℂ)
  else if h : b < a ∧ ε a = ε b then w.2 ⟨(a, b), h⟩
  else if h' : a < b ∧ ε b = ε a then -star (w.2 ⟨(b, a), h'⟩) else 0

abbrev GCo (ε : Fin n → Bool) : Type := KCo ε × (PCoord ε → ℂ)

def gMat {ε : Fin n → Bool} (s : GCo ε) : Matrix (Fin n) (Fin n) ℂ := kMat s.1 + pmat s.2

def expSet {ε : Fin n → Bool} (S : Set (GCo ε)) : Set (UJ ε) :=
  {g | ∃ s ∈ S, toM g = NormedSpace.exp (gMat s)}

def polSet {ε : Fin n → Bool} (S : Set (GCo ε)) : Set (UJ ε) :=
  {g | ∃ s ∈ S, toM g = NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2)}

def DensOn {ε : Fin n → Bool} (ν : Set (GCo ε) → ENNReal) (d : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ δ > 0, ∀ S : Set (GCo ε), MeasurableSet S → (∀ s ∈ S, ‖s‖ < δ) →
    ν S ≤ ENNReal.ofReal ((1 + η) * d) * volume S ∧ ENNReal.ofReal ((1 - η) * d) * volume S ≤ ν S

end ReciprocityTheory.ChartRestriction.DS
