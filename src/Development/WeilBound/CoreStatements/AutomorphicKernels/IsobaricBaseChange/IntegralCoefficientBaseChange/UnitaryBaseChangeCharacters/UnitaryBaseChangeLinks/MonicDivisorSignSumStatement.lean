module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.MonicDivisorSignSum
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

theorem _root_.GlobalTheory.T.monic_divisor_sign_sum : ∀ (k : Type) [Field k] (P : k[X]), P.Monic → P.Separable → ∀ s : k[X] → ℂ, (∀ Q₁ Q₂ : k[X], Q₁.Monic → Q₂.Monic → Q₁ * Q₂ ∣ P → IsCoprime Q₁ Q₂ → s (Q₁ * Q₂) = s Q₁ * s Q₂) → (∀ Q : k[X], Q.Monic → Q ∣ P → s Q = 1 ∨ s Q = -1) → {Q : k[X] | Q.Monic ∧ Q ∣ P}.Finite ∧ ∑ᶠ Q : {Q : k[X] // Q.Monic ∧ Q ∣ P}, s Q.1 = if ∀ Q : k[X], Q.Monic → Q ∣ P → s Q = 1 then 2 ^ nfac P else 0 := by
  first | exact @GlobalTheory.DivSum.finsum_monic_divisors_sign | exact GlobalTheory.DivSum.finsum_monic_divisors_sign | (intros; apply GlobalTheory.DivSum.finsum_monic_divisors_sign <;> assumption)
