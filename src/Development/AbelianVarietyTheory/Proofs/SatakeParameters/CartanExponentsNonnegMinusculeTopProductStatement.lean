module

public import Formalism.SatakeDualWeyl.StatementE
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CartanExponentsNonnegMinusculeTopProduct
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsDedekindDomain NumberField Matrix

theorem _root_.GlobalTheory.T.cartanExponents_nonneg_minusculeTop_product : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (ϖ : v.adicCompletion F), Formalism.UG.IsUnifV F v ϖ → ∀ (d : Fin n → ℤ) (k : ℕ), Antitone d → (∀ i, 0 ≤ d i) → (∀ i : Fin n, 0 < d i ↔ (i : ℕ) < k) → ∀ a₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ a₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ a₃ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ d' : Fin n → ℤ, Antitone d' → ∀ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), (a₁ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagPow F v ϖ (fun i => if 0 < d i then d i - 1 else d i) * (a₂ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagPow F v ϖ (fun i => if (i : ℕ) < k then 1 else 0) * (a₃ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = (k₁ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagPow F v ϖ d' * (k₂ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) → (∀ i, 0 ≤ d' i) ∧ (d' = d ∨ (∑ i, d' i = ∑ i, d i ∧ ∑ i, d' i ^ 2 < ∑ i, d i ^ 2)) := by
  first | exact @GlobalTheory.Hk3.MinuscTopLocal.cartan_top_step | exact GlobalTheory.Hk3.MinuscTopLocal.cartan_top_step | (intros; apply GlobalTheory.Hk3.MinuscTopLocal.cartan_top_step <;> assumption)
