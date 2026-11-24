module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
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

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable def scaledFSH {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] : HermLine ι :=
  (fsH ι).tensor (constLine (-1))

def ScaledFSTopPos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ)
    (II : IntersectionSystem),
    IsIntersectionSystem II → 1 ≤ d → IsArithVar P d → 0 < II K ι P d (fun _ => scaledFSH ι)

theorem scaledFSH_a {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] :
    (scaledFSH ι).a = fun _ => 1 := by
  funext k
  simp [scaledFSH, HermLine.tensor, fsH, HermLine.ofMetrics, constLine, HermLine.ofWeight]

theorem scaledFSH_h {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (z : (Σ k, ι k) → ℂ) :
    (scaledFSH ι).h z = (∏ k, (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩)) * Real.exp 1 := by
  simp [scaledFSH, HermLine.tensor, fsH, HermLine.ofMetrics, constLine, HermLine.ofWeight]

end GroundTheory.Heights₂.Heights.HilbertSamuel
