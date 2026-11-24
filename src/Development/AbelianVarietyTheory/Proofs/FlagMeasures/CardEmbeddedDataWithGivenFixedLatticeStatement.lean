module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardEmbeddedDataWithGivenFixedLattice
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

theorem _root_.GlobalTheory.T.card_embeddedData_with_given_fixedLattice : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (La : Submodule (𝓞 K) V) (x : ℕ), ((({d | IsDat H g L₀ j x d ∧ fixLat d.2 = La}).encard : ℕ∞) : ℝ≥0∞) ≤ ((x : ℝ≥0∞) * D₀) ^ (3 * (2 * j + 1)) := by
  first | exact @GlobalTheory.DegCnt.DatCount.main | exact GlobalTheory.DegCnt.DatCount.main | (intros; apply GlobalTheory.DegCnt.DatCount.main <;> assumption)
