module

public import Formalism.HermitianLattices.StatementLat
public import Mathlib.Basic.Complex.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.ThetaLiftIndependence

def kerOpM {R ι κ M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [Fintype ι]
    (w : ι → R) (K : ι → κ → (M →ₗ[R] N)) (f : ι → M) : κ → N :=
  fun j => ∑ i, w i • K i j (f i)

def chainOpM {R : Type*} [CommSemiring R] {ι : ℕ → Type*} [∀ j, Fintype (ι j)]
    {M : ℕ → Type*} [∀ j, AddCommMonoid (M j)] [∀ j, Module R (M j)]
    (w : ∀ j, ι j → R) (K : ∀ j, ι j → ι (j + 1) → (M j →ₗ[R] M (j + 1))) :
    (m : ℕ) → (ι 0 → M 0) → (ι m → M m)
  | 0, f => f
  | m + 1, f => kerOpM (w m) (K m) (chainOpM w K m f)

section Adelic

variable {G : Type} [Group G] {Γ K : Subgroup G}

end Adelic

section Lat

variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]

def autL (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V) :
    Set (V ≃ₗ[K] V) :=
  {g | g ∈ Formalism.HermitianLatticesTheory.isom h ∧ Formalism.HermitianLatticesTheory.gmap g L = L}

def latWt (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V) : ℂ :=
  ((Nat.card (autL h L) : ℕ) : ℂ)⁻¹

def IsClassReps (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V)
    (s : Finset (Submodule (NumberField.RingOfIntegers K) V)) : Prop :=
  (∀ M ∈ s, M ∈ Formalism.HermitianLatticesTheory.genus h L) ∧
    ∀ M ∈ Formalism.HermitianLatticesTheory.genus h L, ∃! N, N ∈ s ∧ ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g N = M

def latLift (h : V →ₗ⋆[K] V →ₗ[K] K) (s : Finset (Submodule (NumberField.RingOfIntegers K) V))
    (f Θ : Submodule (NumberField.RingOfIntegers K) V → ℂ) : ℂ :=
  ∑ L ∈ s, latWt h L * f L * Θ L

end Lat

def LatLiftIndep : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V)
    (f Θ : Submodule (NumberField.RingOfIntegers K) V → ℂ),
    (∀ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ M, f (Formalism.HermitianLatticesTheory.gmap g M) = f M) →
    (∀ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ M, Θ (Formalism.HermitianLatticesTheory.gmap g M) = Θ M) →
    ∀ s s', IsClassReps h L s → IsClassReps h L s' → latLift h s f Θ = latLift h s' f Θ

def ClassRepsDefinite : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ L : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K L →
      (∃ s, IsClassReps h L s) ∧
      (∀ M ∈ Formalism.HermitianLatticesTheory.genus h L, ∃ n : ℕ, 0 < n ∧ latWt h M = (n : ℂ)⁻¹) ∧
      (∃ D : ℕ, 0 < D ∧ ∀ M ∈ Formalism.HermitianLatticesTheory.genus h L, ∃ z : ℤ, (D : ℂ) * latWt h M = z)

def gaussOp {𝔽 V : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [AddCommGroup V] [Module ℂ V]
    (ψ : AddChar 𝔽 ℂ) (ρ : 𝔽ˣ →* (V →ₗ[ℂ] V)) : V →ₗ[ℂ] V :=
  ∑ c : 𝔽ˣ, ψ (c : 𝔽) • ρ c

def gaussOpDual {𝔽 V : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [AddCommGroup V] [Module ℂ V]
    (ψ : AddChar 𝔽 ℂ) (ρ : 𝔽ˣ →* (V →ₗ[ℂ] V)) : V →ₗ[ℂ] V :=
  ∑ c : 𝔽ˣ, ψ (-(c : 𝔽)) • ρ c⁻¹

def GaussOp : Prop :=
  ∀ (𝔽 V : Type) [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [AddCommGroup V] [Module ℂ V]
    (ψ : AddChar 𝔽 ℂ) (ρ : 𝔽ˣ →* (V →ₗ[ℂ] V)), ψ ≠ 1 →
    ∀ v : V, ∑ c : 𝔽ˣ, ρ c v = 0 →
      gaussOp ψ ρ (gaussOpDual ψ ρ v) = (Fintype.card 𝔽 : ℂ) • v ∧
      gaussOpDual ψ ρ (gaussOp ψ ρ v) = (Fintype.card 𝔽 : ℂ) • v

end Formalism.ThetaLiftIndependence
