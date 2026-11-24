module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.PullHomeoApply
public import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil

namespace PositivityTheory.PfBern.Frob

def FrobeniusReciprocity : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) [LocallyCompactSpace H], IsClosed (H : Set G) → IsUnimod G → IsUnimod H →
    ∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
      [TotallyDisconnectedSpace X] [MulAction G X] [ContinuousSMul G X]
      (p : X → G ⧸ H), Continuous p →
    ∀ (hp : ∀ (g : G) (x : X), p (g • x) = g • p x)
      (χ : G →* ℂˣ), Continuous (fun g => (χ g : ℂ)) →
    ∀ (μG : Measure G) [IsHaarMeasure μG] (μH : Measure H) [IsHaarMeasure μH],
    ∃ Fr : eqv (X := X) χ ≃ₗ[ℂ] eqvF hp (χ.comp H.subtype),
      (∀ (ξ : eqv (X := X) χ) (C : Set X), IsClosed C → (∀ (g : G), ∀ x ∈ C, g • x ∈ C) →
        (SupportedIn (ξ : Distr X) C ↔
          SupportedIn ((Fr ξ : eqvF hp _) : Distr (Fib p)) (Subtype.val ⁻¹' C))) ∧
      (∀ (ξ : eqv (X := X) χ) (α : SB G) (φ : SB (Fib p)) (f : SB X),
        (∀ (g : G) (z : Fib p), (f : X → ℂ) (g • z.1) =
            ∫ h, (α : G → ℂ) (g * (h : G)) * (φ : Fib p → ℂ) (fibSmul hp h⁻¹ z) ∂μH) →
        (ξ : Distr X) f =
          (∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG) * ((Fr ξ : eqvF hp _) : Distr (Fib p)) φ)

section Uses

variable (hF : FrobeniusReciprocity)
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {H : Subgroup G} [LocallyCompactSpace H] (hH : IsClosed (H : Set G)) (uG : IsUnimod G)
  (uH : IsUnimod H)
  {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] [MulAction G X] [ContinuousSMul G X]
  {p : X → G ⧸ H} (hpc : Continuous p) (hp : ∀ (g : G) (x : X), p (g • x) = g • p x)
  {χ : G →* ℂˣ} (hχ : Continuous (fun g => (χ g : ℂ)))
include hF hH uG uH hpc hχ

end Uses

end PositivityTheory.PfBern.Frob
