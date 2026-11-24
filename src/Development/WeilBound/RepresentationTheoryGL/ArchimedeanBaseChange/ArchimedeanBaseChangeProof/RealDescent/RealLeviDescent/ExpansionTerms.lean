module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ConeWeightsNotSecondType
public import Mathlib.Data.Fin.Tuple.Sort
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgBcC.RealD

open PositivityTheory.RgBcC.Real

variable {n : ℕ}

def domC (x : Fin n → ℝ) : Fin n → ℝ := x ∘ Tuple.sort (fun a => -x a)

def spinSq (ν : Fin n → ℝ) : ℝ := nsq (domC (ν - rhoV n) + rhoV n)

def LSq (lam : Fin n → ℤ) : ℝ := nsq fun a => 2 * ((lam a : ℝ) + rhoV n a)


open Classical in
def topTypes (lam : Fin n → ℤ) : Finset (Fin n → ℝ) :=
  (((univ : Finset (Finset (Fin n × Fin n))).filter fun B => ∀ p ∈ B, p.1 < p.2).image fun B =>
    domC ((fun a => 2 * (lam a : ℝ) + 2 * rhoV n a) + rhoV n - wtB B) - rhoV n).filter fun ν => StrictAnti (ν + rhoV n)

def LemmaHT : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → harmSet lam ⊆ topTypes lam ∧
    ∀ ν ∈ topTypes lam, spinSq ν ≤ LSq lam ∧ (spinSq ν = LSq lam → ν ∈ harmSet lam)

def SecondTypeWeightsShorter : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev → ∀ ν, IsSecondTypeWeight lam lev ν →
    ν ∈ topTypes lam ∧ nsq (ν + rhoV n) < nsq (muQ lam lev + rhoV n)

end PositivityTheory.RgBcC.RealD
