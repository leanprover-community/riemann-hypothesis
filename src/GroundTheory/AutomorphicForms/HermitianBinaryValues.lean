module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.GlobalFields.Adele.BaseChange.FiniteMap
import GroundTheory.GlobalFields.HerbrandQuotients.RationalForm
import GroundTheory.GlobalFields.SemilocalAlgebras.ContinuousCompletionMap
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances

@[expose] public section

noncomputable section

namespace GroundTheory.Automorphic

open NumberField IsDedekindDomain GroundTheory.Global Filter

section Algebra

variable {K : Type*} [Field K]

end Algebra

section Archimedean

open NumberField.InfinitePlace.Completion

variable {K : Type*} [Field K] {v : InfinitePlace K}

theorem continuous_ringEquivRealOfIsReal (hv : v.IsReal) :
    Continuous (ringEquivRealOfIsReal hv) := by
  have : (ringEquivRealOfIsReal hv : v.Completion → ℝ) = extensionEmbeddingOfIsReal hv := by
    ext x
    simp
  rw [this]
  exact (isometry_extensionEmbeddingOfIsReal hv).continuous

end Archimedean

section Main

open NumberField.InfinitePlace.Completion

universe u

variable {K : Type u} [Field K] [NumberField K]

section AtL

open scoped NumberField.LiesOver
open GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange

variable {γ t : K} [Fact (∀ r : K, r ^ 2 ≠ -γ + t * r)]

end AtL

end Main

end GroundTheory.Automorphic
