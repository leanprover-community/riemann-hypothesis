module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledVacuumEqHermitianCharacter
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.doubledVacuum_eq_hermitian_character : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L₁ L₂ : Lt E r, SelfD X L₁ → SelfD X L₂ → ∀ M : ℕ, 0 < M → ∀ v₁ v₂ : TF n g, IsVac X bas w (tens (stdL E n) L₁) v₁ → IsVac X bas w (tens (stdL E n) L₂) v₂ → ∃ (β : Matrix (Fin r) (Fin r) E) (t : ℂ), ccT β = β ∧ ∀ Λ ∈ Vset E n M, ∀ x, dbl X bas idx (unitv (projA X bas w (tens Λ L₁) v₁)) (unitv (projA X bas w (tens Λ L₂) v₂)) x = if x ∈ tens Λ (L₁ ⊔ L₂) then t * cexp (π * I * ((Algebra.trace ℚ E (x * β * ccT x).trace : ℚ) : ℂ)) else 0 := by
  first | exact @GlobalTheory.SW.dbl_vacuum | exact GlobalTheory.SW.dbl_vacuum | (intros; apply GlobalTheory.SW.dbl_vacuum <;> assumption)
