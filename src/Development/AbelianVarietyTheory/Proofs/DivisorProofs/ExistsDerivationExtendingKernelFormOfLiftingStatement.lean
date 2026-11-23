module

public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtendingKernelFormOfLifting
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


theorem _root_.GlobalTheory.T.exists_derivation_extending_kernel_form_of_lifting : ∀ (A P R K : Type) [CommRing A] [CommRing P] [IsNoetherianRing P] [CommRing R] [Field K] [Algebra A P] [Algebra A R] [Algebra P R] [IsScalarTower A P R] [Algebra R K] [Algebra P K] [IsScalarTower P R K] [Algebra A K] [IsScalarTower A P K], Function.Surjective (algebraMap P R) → Function.Surjective (algebraMap R K) → (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (β : A →+* C) (φ₀ : R →+* C₀), φ₀.comp (algebraMap A R) = π.comp β → ∃ φ : R →+* C, π.comp φ = φ₀ ∧ φ.comp (algebraMap A R) = β) → ∀ ℓ : RingHom.ker (algebraMap P R) →ₗ[P] K, ∃ D : Derivation A P K, ∀ i : RingHom.ker (algebraMap P R), D i = ℓ i := by
  first | exact @GlobalTheory.LiftDeriv.exists_derivation_extending | exact GlobalTheory.LiftDeriv.exists_derivation_extending | (intros; apply GlobalTheory.LiftDeriv.exists_derivation_extending <;> assumption)
