module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def kerOp {X : Type} [MeasurableSpace X] (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) (F : GA E a → ℂ) :
    GA E a → ℂ := fun g => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν

structure IsBCC (F : GA E a → ℂ) : Prop where
  cont : Continuous F
  bdd : ∃ C : ℝ, ∀ g, ‖F g‖ ≤ C
  cusp : IsCuspidal F
  left : ∀ γ g, F (ratGL E a γ * g) = F g


variable (E a) in
def lieBasis : Module.Basis (Fin (Module.finrank ℝ (Lie E a))) ℝ (Lie E a) := Module.finBasis ℝ (Lie E a)


variable (E a) in
def lieCoord (i : Fin (Module.finrank ℝ (Lie E a))) : Lie E a →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap ((lieBasis E a).coord i))

def adCoef (γ : GL (Fin a) (Cinf E)) (p : Fin (Module.finrank ℝ (Lie E a)) × Fin (Module.finrank ℝ (Lie E a))) : ℂ :=
  lieCoord E a p.1 (toL ((γ⁻¹).val * Matrix.of (lieBasis E a p.2) * γ.val))

theorem sum_lieCoord (X : Lie E a) : ∑ i, ((lieBasis E a).coord i X) • lieBasis E a i = X :=
  (lieBasis E a).sum_repr X

end GlobalTheory.JSW
