module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralConjOfIntegralConjGenerator
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.eventually_integral_conj_of_integral_conj_generator : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.Cˣ), (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∀ (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C), Function.Injective ι →
    (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) → ∀ (κ : Type) (b : Module.Basis κ ℚ G.C)
    (κ' : Type) (ℓ : Module.Basis κ' ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ X : (v.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
      IsIntB v b (↑X * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (γ : G.C)) * ↑X⁻¹) →
      ∀ ρ, IsIntB v ℓ ρ →
        IsIntB v b (↑X * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι ρ * ↑X⁻¹) := by
  first | (exact @GlobalTheory.ConjInt.isIntB_conj_map_of_isIntB_conj) | (exact GlobalTheory.ConjInt.isIntB_conj_map_of_isIntB_conj) | (intros; apply GlobalTheory.ConjInt.isIntB_conj_map_of_isIntB_conj  <;> assumption)
