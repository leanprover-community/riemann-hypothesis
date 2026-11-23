module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionBySetPowFreeOfCardPowNumberField
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

open NumberField

theorem _root_.GlobalTheory.T.torsionBySet_pow_free_of_card_pow_numberField : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (w0 : Ideal (𝓞 F)) (h r : ℕ), w0.IsMaximal → w0 ≠ ⊥ → (∀ j : ℕ, Nat.card (Submodule.torsionBySet (𝓞 F) M ((w0 ^ j : Ideal (𝓞 F)) : Set (𝓞 F))) = Nat.card (𝓞 F ⧸ w0) ^ (j * h)) → ∃ f : (Fin h → 𝓞 F ⧸ w0 ^ r) →+ M, (∀ (c : 𝓞 F) (a : Fin h → 𝓞 F ⧸ w0 ^ r), f (Ideal.Quotient.mk (w0 ^ r) c • a) = c • f a) ∧ Function.Injective f ∧ ∀ g : M, (∀ c ∈ w0 ^ r, c • g = 0) → ∃ a, f a = g := by
  first | (exact @GlobalTheory.torsionBySet_pow_free_of_natCard) | (exact GlobalTheory.torsionBySet_pow_free_of_natCard) | (intros; apply GlobalTheory.torsionBySet_pow_free_of_natCard  <;> assumption)
