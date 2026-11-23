module

public import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigTranslateOfSubMemAug
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.isEig_apply_of_sub_mem_aug : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J N₀ N₁ : Set G) (θ : G → ℂ) (z : G), Datum J θ → Datum N₀ (fun _ => 1) → (∀ y ∈ N₀, y ∈ J ∧ θ y = 1) → (∀ y, y ∈ N₁ ↔ z * y * z⁻¹ ∈ N₀) → (∀ j ∈ J, ∃ y ∈ N₀, z⁻¹ * (y⁻¹ * j) * z ∈ J ∧ θ (z⁻¹ * (y⁻¹ * j) * z) = θ j) → ∀ u u' : V, IsEig π J θ u → IsEig π N₁ (fun _ => 1) u' → u - u' ∈ aug π N₁ (fun _ => 1) → IsEig π J θ (π z u') := by
  first | exact @GlobalTheory.PsType.isEig_translate_of_sub_mem_aug | exact GlobalTheory.PsType.isEig_translate_of_sub_mem_aug | (intros; apply GlobalTheory.PsType.isEig_translate_of_sub_mem_aug <;> assumption)
