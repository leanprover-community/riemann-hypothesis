module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.UnitaryConjugacySignProduct
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.unitary_conjugacy_sign_product : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, (∀ γ γ' : UE E n, γ.1.val.charpoly = P → γ'.1.val.charpoly = P → (∀ w ∈ S, ∃ g : UL n w, locPt w γ' = g⁻¹ * locPt w γ * g) → ∃ g : UE E n, γ' = g⁻¹ * γ * g) ∧ (∀ γ : UE E n, γ.1.val.charpoly = P → ∀ P₁ : E[X], P₁.Monic → P₁ ∣ P → ∏ᶠ w ∈ S, kapSign n w (atPl w P₁) (locPt w γ).1 = 1) ∧ ∀ y : ∀ w : Pl E, UL n w, (∀ w, (y w).1.val.charpoly = atPl w P) → (∀ᶠ w in cofinite, y w ∈ KL n w) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ P → ∏ᶠ w ∈ S, kapSign n w (atPl w P₁) (y w).1 = 1) → ∃ γ : UE E n, γ.1.val.charpoly = P ∧ ∀ w ∈ S, ∃ g : UL n w, locPt w γ = g⁻¹ * y w * g := by
  first | exact @GlobalTheory.UnitaryClasses.main | (intros; apply GlobalTheory.UnitaryClasses.main <;> assumption)
