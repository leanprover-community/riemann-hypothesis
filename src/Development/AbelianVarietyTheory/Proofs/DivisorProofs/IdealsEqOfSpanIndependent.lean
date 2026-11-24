module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionAdelicSL2
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
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

theorem _root_.GlobalTheory.T.ideals_eq_of_span_independent : ∀ (A B R : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing R] [Algebra A R] {r : ℕ} (v : Fin r → B) (J₁ J₂ : Ideal (R ⊗[A] B)), J₁ ≤ J₂ → Submodule.span R (Set.range (fun k => Ideal.Quotient.mk J₁ ((1 : R) ⊗ₜ[A] v k))) = ⊤ → LinearIndependent R (fun k => Ideal.Quotient.mk J₂ ((1 : R) ⊗ₜ[A] v k)) → J₁ = J₂ := by
  first | (exact @GlobalTheory.tensor_ideal_eq_of_span_of_linearIndependent) | (exact GlobalTheory.tensor_ideal_eq_of_span_of_linearIndependent) | (intros; apply GlobalTheory.tensor_ideal_eq_of_span_of_linearIndependent  <;> assumption)
