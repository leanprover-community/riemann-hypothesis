module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
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

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

section Objects

variable {K : Type} {ι : K → Type} {K₂ : Type} {ι₂ : K₂ → Type}

def formApply (g : (Σ k, ι₂ k) → MRing ι) (z : (Σ k, ι k) → ℂ) : (Σ k, ι₂ k) → ℂ :=
  fun q => eval z (map (Int.castRingHom ℂ) (g q))

variable [Fintype K] [∀ k, Fintype (ι k)]

end Objects

def GraphChangeOfModel.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
      (P : Ideal (MRing ι)) (d : ℕ) (g : (Σ k, ι₂ k) → MRing ι) (δ : K₂ → K → ℕ)
      (G : GenFibre inrV (graphIdeal P g))
      (J : IFamily G.Φ (fibreIdx (Sum.elim ι ι₂) (Sum.inr : K₂ → K ⊕ K₂)))
      (L : Fin d → HermLine ι₂) (L₁ : Fin d → HermLine ι),
      IsArithVar P d → (∀ q, IsMultiHomog (g q) (δ q.1)) → IsBasePtFree P g →
      IsArithVar (imageZ inrV (graphIdeal P g)) d → IsFieldIntersection J →
      (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSmoothHerm (L₁ j)) →
      (∀ j k, (L₁ j).a k = ∑ k₂, (L j).a k₂ * (δ k₂ k : ℤ)) →
      (∀ j, ∀ z ∈ mcPts P, (L₁ j).h z = (L j).h (formApply g z)) →
      I K ι P d L₁ = (J (fibreIdeal Sum.inr G) 0 Fin.elim0 : ℝ) * I K₂ ι₂ (imageZ inrV (graphIdeal P g)) d L

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.HilbertSamuel
