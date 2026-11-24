module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoMulIndexSqsInvolution
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

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.two_mul_index_sqs_eq_relIndex_fixed_mul_relIndex_ker : ∀ (A : Type) [CommGroup A] (σ : A →* A) (ε : A), (∀ a, σ (σ a) = a) → (∀ a, a * σ a = 1 → ∃ b, a = b / σ b) → ε ≠ 1 → ε ^ 2 = 1 → σ ε = ε → (∀ a : A, a ^ 2 = 1 → a = 1 ∨ a = ε) → 2 * (sqs (⊤ : Subgroup A)).index = (sqs (σ.eqLocus (MonoidHom.id A))).relIndex (σ.eqLocus (MonoidHom.id A)) * (sqs (MonoidHom.id A * σ).ker).relIndex (MonoidHom.id A * σ).ker := by
  first | exact @GlobalTheory.QNorm.two_mul_index_sqs_involution | exact GlobalTheory.QNorm.two_mul_index_sqs_involution | (intros; apply GlobalTheory.QNorm.two_mul_index_sqs_involution <;> assumption)
