module

public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
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

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexOrder

namespace Line

end Line

section FS


end FS

section Reg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

structure WeightReg (ι : K → Type) [∀ k, Fintype (ι k)] where

  reg : ℝ → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι
  deg : ∀ t A, (reg t A).a = A.a
  smooth : ∀ t A, IsSmoothHerm A → IsSmoothHerm (reg t A)
  shift : ∀ t (A A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (k : ℝ), 0 < k → A'.a = A.a →
    (∀ z : (Σ b, ι b) → ℂ, (∀ b, ∃ i, z ⟨b, i⟩ ≠ 0) → A'.h z = k * A.h z) →
    ∀ z : (Σ b, ι b) → ℂ, (∀ b, ∃ i, z ⟨b, i⟩ ≠ 0) → (reg t A').h z = k * (reg t A).h z


open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet in
def weightRegRef : WeightReg (PBlk 2) where
  reg _ A := (HermLine.ofMetrics (fun k => fsMetric (ι := PBlk 2 k)) A.a).tensor
    (constLine (A.h (fun _ => 1) / (HermLine.ofMetrics (fun k => fsMetric (ι := PBlk 2 k)) A.a).h (fun _ => 1))
      (div_pos (A.pos _ fun _ => ⟨0, one_ne_zero⟩)
        ((HermLine.ofMetrics (fun k => fsMetric (ι := PBlk 2 k)) A.a).pos _ fun _ => ⟨0, one_ne_zero⟩)))
  deg _ A := by simp [HermLine.tensor, constLine, HermLine.ofMetrics]
  smooth _ A _ := isSmoothHerm_tensor (Inter.isSmoothHerm_ofMetrics_fs _) (isSmoothHerm_constLine _ _)
  shift _ A A' k hk ha hh z _ := by
    have h1 := hh (fun _ => 1) fun _ => ⟨0, one_ne_zero⟩
    simp only [HermLine.tensor, constLine, ha, h1]
    ring

end Reg


variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]


end GroundTheory.Heights₂.Heights.LowerBoundFree
