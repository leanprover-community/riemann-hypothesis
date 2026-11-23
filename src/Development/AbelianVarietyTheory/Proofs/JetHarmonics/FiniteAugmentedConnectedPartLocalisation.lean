module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MonicEqProd
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

open Polynomial

namespace GlobalTheory

theorem finite_augmented_connected_part_localisation :
    ∀ (F : Type) [Field F] [IsAlgClosed F] (W : ValuationSubring F) (p : W), (∀ a : W, ¬ IsUnit a → ∃ n : ℕ, a ^ n ∈ Ideal.span {p}) → ∀ (A : Type) [CommRing A] [Algebra W A] [Module.Finite W A] (aug : A →ₐ[W] W), ∃ s : A, Function.Surjective (algebraMap A (Localization.Away s)) ∧ (∃ m : ℕ, ((RingHom.ker aug).map (algebraMap A (Localization.Away s))) ^ m ≤ Ideal.span {algebraMap W (Localization.Away s) p}) ∧ ∀ (R : Type) [CommRing R] [Algebra W R] (w : A →ₐ[W] R), (∀ t ∈ RingHom.ker aug, IsNilpotent (w t)) → IsUnit (w s) := by
  first
  | exact @_root_.GlobalTheory.MonicSeparableProduct.main
  | exact _root_.GlobalTheory.MonicSeparableProduct.main
  | (apply _root_.GlobalTheory.MonicSeparableProduct.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.MonicSeparableProduct.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MonicSeparableProduct.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MonicSeparableProduct.main ..)

end GlobalTheory
