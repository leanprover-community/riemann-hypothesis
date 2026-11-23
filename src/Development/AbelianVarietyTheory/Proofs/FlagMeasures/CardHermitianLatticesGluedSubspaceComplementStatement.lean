module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Formalism.HermitianLattices.StatementMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianLatticesGluedSubspaceComplement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.card_hermitianLattices_glued_subspace_complement : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ (U : Submodule K V) (A : Submodule (𝓞 K) U) (B : Submodule (𝓞 K) (perp h U)) (e e' : ℕ), IsIntLat (hRes h U) A → IsIntLat (hRes h (perp h U)) B → (∃ t : Finset ↥U, t.card ≤ e ∧ dual (hRes h U) A = A ⊔ Submodule.span (𝓞 K) (t : Set _)) → (∃ t : Finset ↥(perp h U), t.card ≤ e' ∧ dual (hRes h (perp h U)) B = B ⊔ Submodule.span (𝓞 K) (t : Set _)) → {L : Submodule (𝓞 K) V | IsIntLat h L ∧ latIn U L = A ∧ latIn (perp h U) L = B}.encard ≤ (((discN (hRes h U) A * discN (hRes h (perp h U)) B) ^ (e + e') : ℕ) : ℕ∞) := by
  first | exact @GlobalTheory.Mass.Glue.main | exact GlobalTheory.Mass.Glue.main | (intros; apply GlobalTheory.Mass.Glue.main <;> assumption)
