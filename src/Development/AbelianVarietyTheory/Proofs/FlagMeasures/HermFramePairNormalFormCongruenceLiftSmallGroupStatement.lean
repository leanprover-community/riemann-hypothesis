module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormCongruenceLiftSmallGroup
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

theorem _root_.GlobalTheory.T.hermFramePairNormalForm_congruence_lift_smallGroup : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ 𝔫 : Ideal (𝓞 K), (∀ x ∈ 𝔫, ∃ y ∈ 𝔫, (y : K) = star (x : K)) → ∀ s ∈ N.R, (∀ x ∈ N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F'), s x - x ∈ (Ideal.span {(N.T : 𝓞 K)} * 𝔫) • (N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F'))) → ∃ s' ∈ N.Rs, (∀ y ∈ V0 N.F N.F', s' y = s y) ∧ ∀ x ∈ N.P0, s' x - x ∈ 𝔫 • N.P0 := by
  first | exact @GlobalTheory.DegCnt.LiftS.lift_congruence | exact GlobalTheory.DegCnt.LiftS.lift_congruence | (intros; apply GlobalTheory.DegCnt.LiftS.lift_congruence <;> assumption)
