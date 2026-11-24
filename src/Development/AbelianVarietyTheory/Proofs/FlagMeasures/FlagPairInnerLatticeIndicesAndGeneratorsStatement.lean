module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairInnerLatticeIndicesAndGenerators
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

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.flagPairInnerLattice_indices_and_generators : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → (idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) : ℝ) * cardB N.F N.F' Λ = delBar N.F N.F' Λ ∧ idx (latL N.F' N.F Λ) (lamOne N.F N.F' Λ) = idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) ∧ lamOne N.F N.F' Λ ≤ latL N.F N.F' Λ ⊓ latL N.F' N.F Λ ∧ idx (latL N.F N.F' Λ ⊓ latL N.F' N.F Λ) (lamOne N.F N.F' Λ) ≤ cardB N.F N.F' Λ ∧ GenBy (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) N.j := by
  first | exact @GlobalTheory.DegCnt.InnerIndex.main | exact GlobalTheory.DegCnt.InnerIndex.main | (intros; apply GlobalTheory.DegCnt.InnerIndex.main <;> assumption)
