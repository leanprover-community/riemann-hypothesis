module

public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdealCharacterOfUnitaryHeckeChar
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

open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open Formalism.L2.Host (HChar)


theorem _root_.GlobalTheory.T.exists_idealCharacter_of_unitary_heckeChar : ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K), χ.IsUnitary → ∃ (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ), m ≠ ⊥ ∧ X ⊥ = 0 ∧ X ⊤ = 1 ∧ (∀ I J, X (I * J) = X I * X J) ∧ (∀ I, I ≠ ⊥ → I ⊔ m = ⊤ → ‖X I‖ = 1) ∧ (∀ I, I ⊔ m ≠ ⊤ → X I = 0) ∧ (∀ P : HeightOneSpectrum (𝓞 K), X P.asIdeal = if χ.UnrAt P then ((χ.val P : ℂˣ) : ℂ) else 0) ∧ ∀ (β : 𝓞 K) (k : Kˣ), (k : K) = β → β - 1 ∈ m → X (Ideal.span {β}) = (((χ.inf k : ℂˣ) : ℂ))⁻¹ := by
  first | exact @GlobalTheory.exists_ideal_character_of_unitary_hchar | exact GlobalTheory.exists_ideal_character_of_unitary_hchar | (intros; apply GlobalTheory.exists_ideal_character_of_unitary_hchar <;> assumption)
