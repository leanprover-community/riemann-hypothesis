module

public import Formalism.UnipotentAdelicQuotients.ClassNumberFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialZeroLocusCoordinates
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open GlobalTheory.LKTrip
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_polynomialLocus_similitudeCentralizerTorus : ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D),
  ∃ (N : ℕ) (S : Set (MvPolynomial (Fin N × Fin N) ℚ)) (hS : HeckeCharacterZeroLocus.IsGroupLocus S)
    (φ : ∀ (R : Type) [CommRing R] [Algebra ℚ R], HeckeCharacterZeroLocus.locusSubgroup S hS R →* (R ⊗[ℚ] D)ˣ × Rˣ),
    (∀ (R : Type) [CommRing R] [Algebra ℚ R], Function.Injective (φ R) ∧
      ∀ z : (R ⊗[ℚ] D)ˣ × Rˣ, GlobalTheory.TorCls.TC D σ β y R z ↔ z ∈ Set.range (φ R)) ∧
    (∀ (R R' : Type) [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R'] (f : R →ₐ[ℚ] R')
      (g : HeckeCharacterZeroLocus.locusSubgroup S hS R) (g' : HeckeCharacterZeroLocus.locusSubgroup S hS R'),
      (g' : GL (Fin N) R') = Units.map (f.toRingHom.mapMatrix : Matrix (Fin N) (Fin N) R →+* Matrix (Fin N) (Fin N) R').toMonoidHom (g : GL (Fin N) R) →
      φ R' g' = (Units.map (Algebra.TensorProduct.map f (AlgHom.id ℚ D)).toRingHom.toMonoidHom (φ R g).1,
        Units.map f.toRingHom.toMonoidHom (φ R g).2)) ∧
    (∀ (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R],
      letI : TopologicalSpace (R ⊗[ℚ] D) := moduleTopology R (R ⊗[ℚ] D)
      Continuous (φ R)) := by
  first | (exact @GlobalTheory.TorLoc.exists_locus) | (exact GlobalTheory.TorLoc.exists_locus) | (intros; apply GlobalTheory.TorLoc.exists_locus  <;> assumption)
