module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapSubApply
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

namespace GlobalTheory


open AdicCompletion in
theorem adicCompletion_map_invariants : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J : Ideal A) (N M : Type) [AddCommGroup N] [Module A N]
    [AddCommGroup M] [Module A M] [Module.Finite A M] (f : N →ₗ[A] M) (Γ : Type) [Finite Γ] (g : Γ → (M →ₗ[A] M)),
    Function.Injective f → (∀ x, x ∈ LinearMap.range f ↔ ∀ σ, g σ x = x) →
    Function.Injective (AdicCompletion.map J f) ∧
      ∀ y, y ∈ LinearMap.range (AdicCompletion.map J f) ↔ ∀ σ, AdicCompletion.map J (g σ) y = y := by
  first
  | exact @_root_.GlobalTheory.LinearMapDifferenceFormula.main
  | exact _root_.GlobalTheory.LinearMapDifferenceFormula.main
  | (apply _root_.GlobalTheory.LinearMapDifferenceFormula.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LinearMapDifferenceFormula.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LinearMapDifferenceFormula.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LinearMapDifferenceFormula.main ..)

end GlobalTheory
