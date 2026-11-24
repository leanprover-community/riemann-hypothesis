module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.AnForm.A

open MeasureTheory

noncomputable section

def logMono {D : ℕ} (m : Fin D → ℤ) (z : Fin D → ℂ) : ℝ :=
  ∑ i, (m i : ℝ) * Real.log ‖z i‖

def LogNormLocIntCStatement : Prop :=
  LocallyIntegrable (fun z : ℂ => Real.log ‖z‖) volume

def LogCoordLocIntStatement : Prop :=
  ∀ (D : ℕ) (i : Fin D), LocallyIntegrable (fun z : Fin D → ℂ => Real.log ‖z i‖) volume

def LogMonoLocIntStatement : Prop :=
  ∀ (D : ℕ) (m : Fin D → ℤ), LocallyIntegrable (logMono m) volume

def LogUnitMonoLocIntStatement : Prop :=
  ∀ (D : ℕ) (m : Fin D → ℤ) (U : Set (Fin D → ℂ)) (u : (Fin D → ℂ) → ℂ), IsOpen U →
    DifferentiableOn ℂ u U → (∀ z ∈ U, u z ≠ 0) →
    LocallyIntegrableOn (fun z => Real.log ‖u z * ∏ i, z i ^ m i‖) U volume

end

end ReciprocityTheory.AnForm.A
