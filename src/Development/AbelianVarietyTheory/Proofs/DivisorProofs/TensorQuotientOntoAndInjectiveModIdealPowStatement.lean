module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorQuotientOntoAndInjectiveModIdealPow
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


theorem _root_.GlobalTheory.T.tensor_quotient_onto_and_injective_mod_ideal_pow : ∀ (R : Type) [CommRing R] (I : Ideal R) (R' : Type) [CommRing R'] [Algebra R R'] (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (O : Type) [CommRing O] [Algebra R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (I ^ (e + 1)).map (algebraMap R C')), (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (I ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) → ∀ (C : Subalgebra R C') (gm : ∀ e : ℕ, (O ⧸ (I ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (I ^ (e + 1)).map (algebraMap R C))), (∀ e (x : O) (c : C), gm e (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ c → Ideal.Quotient.mk ((I ^ (e + 1)).map (algebraMap R C')) (c : C') = i e x) → (∀ y : C', ∃ t : TensorProduct R C R', y - Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t ∈ (I.map (algebraMap R C)).map (algebraMap C C')) ∧ ∀ (n : ℕ) (t : TensorProduct R C R'), Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t ∈ ((I.map (algebraMap R C)) ^ n).map (algebraMap C C') → t ∈ ((I.map (algebraMap R C)) ^ n).map (algebraMap C (TensorProduct R C R')) := by
  first | exact @GlobalTheory.quot_tensor_level | exact GlobalTheory.quot_tensor_level | (intros; apply GlobalTheory.quot_tensor_level <;> assumption)
