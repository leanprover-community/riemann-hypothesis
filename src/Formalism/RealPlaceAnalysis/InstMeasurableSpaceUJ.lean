module

public import Formalism.RealPlaceAnalysis.Complexify
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.Group.Subgroup

@[expose] public section

open MeasureTheory

noncomputable section

namespace Formalism.REAL

instance instLocallyCompactUJ (n : ℕ) (ε : Fin n → Bool) : LocallyCompactSpace (UJ ε) :=
  uJLocCompact_of isClosedEmbeddingMatrix n ε

instance instMeasurableSpaceUJ (n : ℕ) (ε : Fin n → Bool) : MeasurableSpace (UJ ε) := borel _

instance instBorelSpaceUJ (n : ℕ) (ε : Fin n → Bool) : BorelSpace (UJ ε) := ⟨rfl⟩

instance instSecondCountableUJ (n : ℕ) (ε : Fin n → Bool) : SecondCountableTopology (UJ ε) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  exact (isClosedEmbeddingMatrix n ε).1.isInducing.secondCountableTopology

def muG {n : ℕ} (ε : Fin n → Bool) : Measure (UJ ε) := Measure.haar

instance instIsHaarMuG (n : ℕ) (ε : Fin n → Bool) : (muG ε).IsHaarMeasure := by
  unfold muG; infer_instance

def hsG {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : ℝ :=
  hs ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

def Unimodular : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g : UJ ε), Measure.map (fun x => x * g) (muG ε) = muG ε

def InvInvariant : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), Measure.map (fun x : UJ ε => x⁻¹) (muG ε) = muG ε

def BallFinite : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (R : ℝ), muG ε {g | hsG g ≤ R} < ⊤

def VolGrowth : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
    muG ε {g | hsG g ≤ R ^ 2} ≤ ENNReal.ofReal (C * R ^ (2 * n ^ 2))

end Formalism.REAL
