module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTensorPadicIntEquivAdjoinOfFreeFinite
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

open NumberField GlobalTheory.LKInvGood
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_tensorPadicInt_equiv_adjoin_of_free_finite : ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (ℓ : ℕ) [Fact ℓ.Prime], ∃ ι : O ⊗[ℤ] ℤ_[ℓ] ≃+* locOrder ℓ (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range, ∀ o : O, (ι (o ⊗ₜ[ℤ] 1) : ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o) := by
  first | (exact @GlobalTheory.LocIso.tensor_padicInt_equiv_locOrder) | (exact GlobalTheory.LocIso.tensor_padicInt_equiv_locOrder) | (intros; apply GlobalTheory.LocIso.tensor_padicInt_equiv_locOrder  <;> assumption)
