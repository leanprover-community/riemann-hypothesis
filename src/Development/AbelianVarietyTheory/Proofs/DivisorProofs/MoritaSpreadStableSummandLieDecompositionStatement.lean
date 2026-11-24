module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Ideal.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoritaSpreadStableSummandLieDecomposition
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
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u

theorem _root_.GlobalTheory.T.moritaSpread_stableSummand_lieDecomposition : ∀ {C : Type} [CommRing C] (I : Ideal C) {H : Type u} [AddCommGroup H] [Module C H]
  (m : ℕ) [NeZero m] (E : Fin m → Fin m → Module.End C H),
  (∀ i j k l, E i j * E k l = if j = k then E i l else 0) → ∑ i, E i i = 1 →
  ∀ {A : Type} [CommRing A] (σ : A →+* Module.End C H), (∀ i j c, E i j * σ c = σ c * E i j) →
  ∀ {O : Type} [Ring O] (ρ : O →+* Module.End C H),
  (∀ (c : O) i j (N : Submodule C H), (∀ c', ∀ x ∈ N, σ c' x ∈ N) → ∀ x ∈ N, E 0 0 x = x → E 0 i (ρ c (E j 0 x)) ∈ N) →
  ∀ (e : Module.End C H), e * e = e → (∀ i j, E i j * e = e * E i j) →
  ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ i j, ∀ x ∈ F, E i j x ∈ F) → (∀ x ∈ F, e x ∈ F) →
  ∀ (a : ℕ) (χ : Fin a → A →+* C) (G₀ M₀ : Submodule C H), G₀ ⊓ M₀ = ⊥ → G₀ ⊔ M₀ = LinearMap.range (E 0 0 * e) →
    (∀ c, ∀ x ∈ G₀, σ c x ∈ G₀) → G₀ ⊔ I • LinearMap.range (E 0 0 * e) = F ⊓ LinearMap.range (E 0 0 * e) →
    (∀ d ∈ LinearMap.range (E 0 0 * e), ∃ w : Fin a → H, (∀ i c, σ c (w i) - χ i c • w i ∈ G₀) ∧ d - ∑ i, w i ∈ G₀) →
  ∃ G M : Submodule C H, G ⊓ M = ⊥ ∧ G ⊔ M = LinearMap.range e ∧ (∀ (c : O), ∀ x ∈ G, ρ c x ∈ G) ∧
    G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e ∧
    ∀ d ∈ LinearMap.range e, ∃ w : Fin a → H, (∀ i c, σ c (w i) - χ i c • w i ∈ G) ∧ d - ∑ i, w i ∈ G := by
  first | (exact @GlobalTheory.morita_spread_stable_summand_lie) | (exact GlobalTheory.morita_spread_stable_summand_lie) | (intros; apply GlobalTheory.morita_spread_stable_summand_lie  <;> assumption)
