module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
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

theorem _root_.GlobalTheory.T.tensorLattice_selfDual_semicharacter_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L, SelfD X L → ∀ (M : ℕ), ∀ Λ ∈ Vset E n M, (tens Λ L).FG ∧ (∀ y, y ∈ tens Λ L ↔ ∀ y' ∈ tens Λ L, ∃ k : ℤ, ∑ i, EF X (y i) (y' i) = k) ∧ (∀ y ∈ tens Λ L, epsW X w y ^ 2 = 1 ∧ ∀ y' ∈ tens Λ L, epsW X w (y + y') = epsW X w y * epsW X w y' * cexp (-(π * I * ((∑ k, EF X (y k) (y' k) : ℚ) : ℂ)))) ∧ (∀ y : Matrix (Fin n) (Fin r) E, y ∈ tens (stdL E n) L ↔ ∀ k, y k ∈ L) ∧ (∀ L', SelfD X L' → (tens Λ L').relIndex (tens Λ L) = L'.toAddSubgroup.relIndex L.toAddSubgroup ^ n ∧ tens Λ L ⊓ tens Λ L' = tens Λ (L ⊓ L')) ∧ ∀ Λ' ∈ Vset E n M, (tens Λ' L).relIndex (tens Λ L) = Λ'.toAddSubgroup.relIndex Λ.toAddSubgroup ^ r := by
  first | exact @GlobalTheory.SW.TensLat.tens_selfDual_semichar_index | exact GlobalTheory.SW.TensLat.tens_selfDual_semichar_index | (intros; apply GlobalTheory.SW.TensLat.tens_selfDual_semichar_index <;> assumption)
