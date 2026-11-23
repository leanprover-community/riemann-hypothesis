module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def IsIsometricOn (P : Ideal (MRing ι)) (A B : HermLine ι) : Prop :=
  ∃ (f g : MRing ι) (α β : K → ℕ), IsMultiHomog f α ∧ IsMultiHomog g β ∧ f ∉ P ∧ g ∉ P ∧
    (∀ k, (α k : ℤ) - β k = A.a k - B.a k) ∧ divCycle P f = divCycle P g ∧
    ∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) f)‖ * B.h z = ‖eval z (map (Int.castRingHom ℂ) g)‖ * A.h z

end Objects

def IsomInvariance.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (L L' : Fin n → HermLine ι),
      IsArithVar P n → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSmoothHerm (L' j)) →
      (∀ j, IsIsometricOn P (L j) (L' j)) → I P n L = I P n L'

def GraphIsometric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι ι₂ : K → Type) [∀ k, Fintype (ι k)] [∀ k, Fintype (ι₂ k)]
    (P : Ideal (MRing ι)) (d : ℕ) (A : ∀ k, ι₂ k → ι k → ℤ) (B₁ : HermLine ι) (B : HermLine ι₂)
    (B₁' B' : HermLine (Sum.elim ι ι₂)),
    IsArithVar P d → IsBasePtFree P (linForm A) → B₁.a = B.a →
    (∀ z ∈ mcPts P, B₁.h z = B.h (linApply A z)) →
    IsPullHerm Sum.inl inlV B₁ B₁' → IsPullHerm Sum.inr inrV B B' →
    IsIsometricOn (graphIdeal P (linForm A)) B₁' B'

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.HilbertSamuel
