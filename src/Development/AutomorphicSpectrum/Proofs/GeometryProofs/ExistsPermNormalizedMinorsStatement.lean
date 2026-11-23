module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitOfSumEqOne
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPermNormalizedMinors
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

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem _root_.GlobalTheory.T.exists_perm_normalized_minors : ∀ {F : Type} [Field F] (O : Subring F) {r : ℕ} (Y : Matrix (Fin r) (Fin r) F), (∀ (k : ℕ) (hk : k + 1 ≤ r) (I' : Fin (k + 1) → Fin r) (I : Fin k → Fin r), NormAt O Y (k + 1) hk I' → NormAt O Y k (Nat.le_of_succ_le hk) I → ∃ f : Fin k → Fin (k + 1), Function.Injective f ∧ NormAt O Y k (Nat.le_of_succ_le hk) (I' ∘ f)) → (∀ (k : ℕ) (hk : k ≤ r), ∃ I : Fin k → Fin r, NormAt O Y k hk I) → ∃ w : Equiv.Perm (Fin r), ∀ (k : ℕ) (hk : k ≤ r), NormAt O Y k hk (w ∘ Fin.castLE hk) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_perm_normAt | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_perm_normAt | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_perm_normAt <;> assumption)
