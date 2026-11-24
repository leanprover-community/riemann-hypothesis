module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealProperties
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

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.adelicCompletion_fractionalIdeal_properties_alt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ I J : FractionalIdeal (𝓞 E)⁰ E, ∀ x ∈ hat1 F (I : Set E), ∀ y ∈ hat1 F (J : Set E), x * y ∈ hat1 F ((I * J : FractionalIdeal (𝓞 E)⁰ E) : Set E)) ∧ (∀ (I : FractionalIdeal (𝓞 E)⁰ E) (x : E), (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F (I : Set E) ↔ x ∈ I) ∧ (∀ (I J : FractionalIdeal (𝓞 E)⁰ E) (z : RA F E), I ≠ 0 → (∀ x ∈ I, z * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) ∈ hat1 F (J : Set E)) → z ∈ hat1 F ((J * I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E)) ∧ ∀ (c : E ≃ₐ[F] E) (I I' : FractionalIdeal (𝓞 E)⁰ E), (∀ x ∈ I, c x ∈ I') → ∀ z ∈ hat1 F (I : Set E), sg (FiniteAdeleRing (𝓞 F) F) c z ∈ hat1 F (I' : Set E) := by
  first | exact @GlobalTheory.AdLat.adelicCompletion_fractionalIdeal_properties | exact GlobalTheory.AdLat.adelicCompletion_fractionalIdeal_properties | (intros; apply GlobalTheory.AdLat.adelicCompletion_fractionalIdeal_properties <;> assumption)
