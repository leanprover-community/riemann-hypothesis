module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Formalism.HermitianLattices.StatementMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodula
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

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ M : Submodule (𝓞 K) V, IsIntLat h M → discN h M ≠ 0 ∧ (discN h M = 1 ↔ IsUnimodular h M) ∧ (∀ M' : Submodule (𝓞 K) V, IsIntLat h M' → M ≤ M' → idxN M' M ≠ 0 ∧ discN h M = discN h M' * idxN M' M ^ 2) ∧ (∀ N ∈ genus h M, IsIntLat h N ∧ discN h N = discN h M) ∧ (∀ P : Ideal (𝓞 K), P.IsMaximal → ((discN h M : ℕ) : 𝓞 K) ∉ P → IsUnimodularAt h P M) ∧ (∀ M' : Submodule (𝓞 K) V, IsIntLat h M' → M ≤ M' → ∀ P : Ideal (𝓞 K), P.IsMaximal → IsUnimodularAt h P M → loc (K := K) P M = loc (K := K) P M') := by
  first | exact @GlobalTheory.Mass.DiscOrder.main | exact GlobalTheory.Mass.DiscOrder.main | (intros; apply GlobalTheory.Mass.DiscOrder.main <;> assumption)
