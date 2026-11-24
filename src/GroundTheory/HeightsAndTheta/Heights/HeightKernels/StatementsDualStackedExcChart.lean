module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcLinear
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
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopSimpleSub

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField Matrix

noncomputable section

def IsExcCoords {K : Type} [Field K] [NumberField K] {i : ℕ} (F F' : HermLattice K i) {T : Type}
    (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F')) {k : Type} [Field k]
    (ρ : 𝓞 K →+* k) (π : 𝓞 K) (y₀ : Fin i → K) {m : ℕ} (g : Fin m → Fin i → K) (α : T → k)
    (M : T → Fin (m + 1) → k) : Prop :=
  Function.Surjective ρ ∧ ρ π = 0 ∧ y₀ ∈ F.lattice ∧ (∀ j, g j ∈ F'.lattice) ∧
    (∀ t, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = (b' t : Fin i → K) ⬝ᵥ (algebraMap (𝓞 K) K π • y₀) ∧
      ρ c = α t) ∧
    (∀ t, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = (b t : Fin i → K) ⬝ᵥ y₀ ∧ ρ c = M t 0) ∧
    (∀ t j, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = (b t : Fin i → K) ⬝ᵥ g j ∧ ρ c = M t j.succ) ∧
    (∃ t, α t ≠ 0) ∧ (∃ t, M t 0 ≠ 0) ∧
    (∀ c : 𝓞 K, ρ c = 0 → ∀ φ ∈ dualLattice F', algebraMap (𝓞 K) K c • φ ∈ dualLattice F) ∧
    (∀ φ ∈ dualLattice F', ∀ c : 𝓞 K, algebraMap (𝓞 K) K c = φ ⬝ᵥ (algebraMap (𝓞 K) K π • y₀) →
      ρ c = 0 → φ ∈ dualLattice F) ∧
    (∀ φ ∈ dualLattice F, (∀ c : 𝓞 K, algebraMap (𝓞 K) K c = φ ⬝ᵥ y₀ → ρ c = 0) →
      (∀ j, ∀ c : 𝓞 K, algebraMap (𝓞 K) K c = φ ⬝ᵥ g j → ρ c = 0) →
      φ ∈ Submodule.span ℤ {ψ | ∃ c : 𝓞 K, ρ c = 0 ∧ ∃ χ ∈ dualLattice F, ψ = algebraMap (𝓞 K) K c • χ})

def DualStackedExcCoords.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∃ (k : Type) (_ : Field k) (ρ : 𝓞 K →+* k) (π : 𝓞 K) (y₀ : Fin i → K) (m : ℕ) (g : Fin m → Fin i → K)
      (α : T → k) (M : T → Fin (m + 1) → k), IsExcCoords F F' b b' ρ π y₀ g α M

def DualStackedExcBase.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (k : Type) [Field k] (ρ : 𝓞 K →+* k) (π : 𝓞 K) (y₀ : Fin i → K) (m : ℕ) (g : Fin m → Fin i → K)
      (α : T → k) (M : T → Fin (m + 1) → k), IsExcCoords F F' b b' ρ π y₀ g α M →
      stackedBase b' a ≤ linPrime α M

def DualStackedExcChart.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (k : Type) [Field k] (ρ : 𝓞 K →+* k) (π : 𝓞 K) (y₀ : Fin i → K) (m : ℕ) (g : Fin m → Fin i → K)
      (α : T → k) (M : T → Fin (m + 1) → k), IsExcCoords F F' b b' ρ π y₀ g α M →
      ∀ v u : T, ∃ N : ℕ, ∀ e ∈ linPrime α M,
        (graphFirst v * graphSecond u) ^ N * e ∈ stackedGraph b' a ⊔ Ideal.span {C (a u) * graphFirst u}

namespace DualStackedExcChartExample

open DualTopSimpleSubExample

end DualStackedExcChartExample

end

end GroundTheory.Heights₂.Heights
