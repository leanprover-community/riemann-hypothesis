module

public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MapRestrictIsHaarOfOpenProductCompact
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

open MeasureTheory

theorem _root_.GlobalTheory.T.map_restrict_isHaar_of_open_product_compact : ∀ (G B : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [MeasurableSpace B] [BorelSpace B] [T2Space B] (ν : Measure G) [ν.IsHaarMeasure] (A : Subgroup G) (i : B →* G) (p : G →* B), IsOpen (A : Set G) → Continuous i → Continuous p → (∀ b, p (i b) = b) → (∀ b, i b ∈ A) → IsCompact {g : G | g ∈ A ∧ p g = 1} → (Measure.map p (ν.restrict A)).IsHaarMeasure := by
  first | exact @GlobalTheory.ChainOnto.map_restrict_isHaar | exact GlobalTheory.ChainOnto.map_restrict_isHaar | (intros; apply GlobalTheory.ChainOnto.map_restrict_isHaar <;> assumption)
