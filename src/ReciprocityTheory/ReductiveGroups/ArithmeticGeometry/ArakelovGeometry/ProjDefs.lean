module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import Mathlib.FieldTheory.Relrank
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo Polynomial

variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}

structure IsProjFrame (x : κ → Ω) (e : Fin (D + 1) → κ) : Prop where
  inj : Function.Injective e
  free : coordIdeal ℤ (x ∘ e) = ⊥
  integral : ∀ i, IsIntegral (coneRing ℤ (x ∘ e)) (C (x i) * X : Polynomial Ω)

structure IsRatProjFrame (x : κ → Ω) (e : Fin (D + 1) → κ) : Prop where
  inj : Function.Injective e
  free : coordIdeal ℤ (x ∘ e) = ⊥
  integral : ∀ i, IsIntegral (coneRing ℚ (x ∘ e)) (C (x i) * X : Polynomial Ω)

def fnField (x : κ → Ω) : IntermediateField ℚ Ω :=
  IntermediateField.adjoin ℚ {t | ∃ i j, t = x i / x j}

def projDeg (x : κ → Ω) (e : Fin (D + 1) → κ) : ℕ :=
  IntermediateField.relfinrank (fnField (x ∘ e)) (fnField x)


open Classical in
def scaleOff (e : Fin (D + 1) → κ) (m : ℕ) (x : κ → Ω) : κ → Ω :=
  by
    classical
    exact fun i => if i ∈ Set.range e then x i else (m : Ω) * x i

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
