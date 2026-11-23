module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDefs
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

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def StBeHerm : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, ∀ η ξ : Wp, ⟪ξ, beOp D X u u' η⟫_ℂ = ⟪beOp D X u' u ξ, η⟫_ℂ

def StBePos : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    aM k r ≤ X.a → ∀ u ∈ Vfl X, ∀ ξ : Wp, 0 ≤ (⟪ξ, beOp D X u u ξ⟫_ℂ).re

def StSchurW : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp), IsDiag D → ∀ v w v' w' : Wp,
    ∫ h : Mt k r, ⟪w, D.π (Matrix.of h) v⟫_ℂ * star ⟪w', D.π (Matrix.of h) v'⟫_ℂ ∂D.μW =
      ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (Module.finrank ℂ Wp : ℂ)

def StSInt : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp), IsDiag D → ∀ b : ℝ, AB k r ≤ b →
    Integrable (fun p : Mt k r × Mt k r => gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b)) (D.μW.prod D.μN)

end ReciprocityTheory.ChartRestriction.DS.Mult1
