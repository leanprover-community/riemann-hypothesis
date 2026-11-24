module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasis
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.finiteAdeleVector_annihilators_compact_open_basis : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → (∀ L : AddSubgroup (Fin N → Af F), IsOpen (L : Set (Fin N → Af F)) → IsCompact {u : Fin N → Af F | ∀ y ∈ L, ψ (pairA F 0 (Bd (Af F) a u y)) = 1}) ∧ (∀ K : Set (Fin N → Af F), IsCompact K → {y : Fin N → Af F | ∀ u ∈ K, ψ (pairA F 0 (Bd (Af F) a u y)) = 1} ∈ 𝓝 0) ∧ ∀ U ∈ 𝓝 (0 : Fin N → Af F), ∃ L : AddSubgroup (Af F), IsOpen (L : Set (Af F)) ∧ IsCompact (L : Set (Af F)) ∧ ∀ u : Fin N → Af F, (∀ l, u l ∈ L) → u ∈ U := by
  first | exact @GlobalTheory.SWQ.finite_annihilators | exact GlobalTheory.SWQ.finite_annihilators | (intros; apply GlobalTheory.SWQ.finite_annihilators <;> assumption)
