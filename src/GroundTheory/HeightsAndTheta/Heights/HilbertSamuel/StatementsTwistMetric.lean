module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.PenHost
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.BergmanDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory NumberField

def TwistMetric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι))
    (II : IntersectionSystem) (u : (F →+* ℂ) → ℝ),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → IsConjInvariantH A →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    (∀ sg, u (ComplexEmbedding.conjugate sg) = u sg) → ∑ sg, u sg = 0 →
    ∃ c : ℝ, ∀ δ : ℝ, 0 < δ → ∃ A' : HermLine ι, A'.a = A.a ∧
      IsSemipositiveRel P0 (mCoordIdeal y) A' ∧ IsConjInvariantH A' ∧
      (∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z →
        A'.h z = Real.exp (u sg + δ) * A.h z) ∧
      II K ι (mCoordIdeal y) (D + 1) (fun _ => A') ≤ II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + c * δ

end GroundTheory.Heights₂.Heights.HilbertSamuel
