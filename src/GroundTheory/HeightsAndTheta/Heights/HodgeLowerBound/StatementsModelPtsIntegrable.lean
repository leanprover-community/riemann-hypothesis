module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPtsBddConv
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

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm.M (IsCompatChart)

def ModelPtsIntegrable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (M : CxModel P e) (n : ℕ) (ψ : Fin n → OpenPartialHomeomorph M.Xc (Fin e → ℂ)) (L : HermLine ι) (c : ℝ)
    (N : Set ((Σ k, ι k) → ℂ)) (E : Set M.Xc) (v : M.Xc → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → IsSmoothHerm L → IsPtsNull P e N →
    (∀ j, IsCompatChart M.atlas (ψ j)) → (∀ x, ∃ j, x ∈ (ψ j).source) →
    (∀ j, volume ((ψ j).target ∩ (ψ j).symm ⁻¹' E) = 0) →
    (∀ j, ∀ Q ⊆ (ψ j).target, IsCompact Q → IntegrableOn (fun y => v ((ψ j).symm y)) Q) →
    (∀ z ∈ mcPts P, z ∉ N → M.proj z ∉ E → g z = v (M.proj z)) →
      IsPtsIntegrable P (fun (_ : Fin e) z => c * Real.log (L.h z)) g

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
