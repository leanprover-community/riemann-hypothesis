module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaCharacteristicsIffTestFunctionThetaSeries
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

theorem _root_.GlobalTheory.T.thetaCharacteristics_iff_testFunction_thetaSeries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → (∀ (a b : Fin n → Fin g → ℚ), ∃ φ : TF n g, IsSB φ ∧ (∀ m : Matrix (Fin n) (Fin g) ℚ, φ m = if ∀ k i, IsIntegral ℤ (m k i - a k i) then cexp (2 * π * I * ((∑ k, m k ⬝ᵥ b k : ℚ) : ℂ)) else 0) ∧ ∀ P, ∀ x ∈ X.dom, thP X hr bas idx φ P x = thFr X hr bas idx n (fun k i => (a k i : ℝ)) (fun k i => (b k i : ℝ)) P x) ∧ ∀ φ : TF n g, IsSB φ → ∃ (m : ℕ) (a b : Fin m → Fin n → Fin g → ℚ) (t : Fin m → ℂ), ∀ P, ∀ x ∈ X.dom, thP X hr bas idx φ P x = ∑ j, t j * thFr X hr bas idx n (fun k i => (a j k i : ℝ)) (fun k i => (b j k i : ℝ)) P x := by
  first | exact @GlobalTheory.SW.CharLink.harmonicTheta_eq_sum_thetaCharacteristic | exact GlobalTheory.SW.CharLink.harmonicTheta_eq_sum_thetaCharacteristic | (intros; apply GlobalTheory.SW.CharLink.harmonicTheta_eq_sum_thetaCharacteristic <;> assumption)
