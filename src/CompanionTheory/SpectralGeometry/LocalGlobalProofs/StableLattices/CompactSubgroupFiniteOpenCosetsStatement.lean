module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Topology.Algebra.Group.Defs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CompactSubgroupFiniteOpenCosets
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


theorem _root_.GlobalTheory.T.compact_subgroup_finite_open_cosets : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K₀ K : Subgroup G), IsCompact (K₀ : Set G) → IsOpen (K : Set G) → ∃ (d : ℕ) (c : Fin d → G), (∀ i, c i ∈ K₀) ∧ ∀ g ∈ K₀, ∃ i, ∃ κ ∈ K, g = κ * c i := by
  first | exact @GlobalTheory.CompanionTheory.CosetCover.exists_finite_coset_cover | exact GlobalTheory.CompanionTheory.CosetCover.exists_finite_coset_cover | (intros; apply GlobalTheory.CompanionTheory.CosetCover.exists_finite_coset_cover <;> assumption)
