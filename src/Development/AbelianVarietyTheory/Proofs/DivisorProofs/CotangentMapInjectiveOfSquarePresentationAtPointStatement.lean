module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Maps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentMapInjectiveOfSquarePresentationAtPoint
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

open scoped TensorProduct

theorem _root_.GlobalTheory.T.cotangent_map_injective_of_square_presentation_at_point : ∀ (O B A σ : Type) [CommRing O] [IsDomain O] [CommRing B] [CommRing A] [Algebra O B] [Algebra O A] [Algebra B A] [IsScalarTower O B A] [Fintype σ] (ε : A →ₐ[O] O) (x : σ → A) (f : σ → MvPolynomial σ B) (c : O), c ≠ 0 → Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (∀ i, MvPolynomial.aeval x (f i) = 0) → RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) ≤ Ideal.span (Set.range f) ⊔ (RingHom.ker ε).comap (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) * RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (∀ a ∈ RingHom.ker ε, c • a ∈ RingHom.ker ε ^ 2 ⊔ ((RingHom.ker ε).comap (algebraMap B A)).map (algebraMap B A)) → ∀ b : B, algebraMap B A b ∈ RingHom.ker ε ^ 2 → b ∈ ((RingHom.ker ε).comap (algebraMap B A)) ^ 2 := by
  first | exact @GlobalTheory.CotangentSquare.cotangent_map_injective_of_square_presentation | exact GlobalTheory.CotangentSquare.cotangent_map_injective_of_square_presentation | (intros; apply GlobalTheory.CotangentSquare.cotangent_map_injective_of_square_presentation <;> assumption)
