module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDefs
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

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def CechDSqStatement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (n : ℕ),
    (cechD S ι M (n + 1)).comp (cechD S ι M n) = 0

def CechDDegStatement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (c : K → ℤ) (n : ℕ),
    ∀ φ ∈ cechCc ι 𝓜 c n, cechD S ι M n φ ∈ cechCc ι 𝓜 c (n + 1)

def CechMapDegStatement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (N : Type) [AddCommGroup N] [Module (MRingOver S ι) N] [Module S N]
    [IsScalarTower S (MRingOver S ι) N]
    (𝓜 : (K → ℤ) → Submodule S M) (𝓝 : (K → ℤ) → Submodule S N) (g : M →ₗ[MRingOver S ι] N)
    (c : K → ℤ) (n : ℕ),
    IsMGradedMap S ι 𝓜 𝓝 g →
    (∀ φ ∈ cechCc ι 𝓜 c n, cechMap S ι g n φ ∈ cechCc ι 𝓝 c n) ∧
      (cechD S ι N n).comp (cechMap S ι g n) = (cechMap S ι g (n + 1)).comp (cechD S ι M n)

def CechTopStatement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (c : K → ℤ) (n : ℕ),
    ∑ k, (Fintype.card (ι k) - 1) < n → Subsingleton (cechHc ι 𝓜 c n)

def CechSESStatement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M' : Type) [AddCommGroup M'] [Module (MRingOver S ι) M'] [Module S M']
    [IsScalarTower S (MRingOver S ι) M'] (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (M'' : Type) [AddCommGroup M''] [Module (MRingOver S ι) M''] [Module S M'']
    [IsScalarTower S (MRingOver S ι) M'']
    (𝓜' : (K → ℤ) → Submodule S M') (𝓜 : (K → ℤ) → Submodule S M) (𝓜'' : (K → ℤ) → Submodule S M'')
    (g : M' →ₗ[MRingOver S ι] M) (h : M →ₗ[MRingOver S ι] M''),
    IsMGraded S ι 𝓜' → IsMGraded S ι 𝓜 → IsMGraded S ι 𝓜'' →
    IsMGradedMap S ι 𝓜' 𝓜 g → IsMGradedMap S ι 𝓜 𝓜'' h →
    Function.Injective g → Function.Surjective h → LinearMap.range g = LinearMap.ker h →
    ∀ (c : K → ℤ) (n : ℕ),
      (Subsingleton (cechHc ι 𝓜' c n) → Subsingleton (cechHc ι 𝓜'' c n) →
        Subsingleton (cechHc ι 𝓜 c n)) ∧
      (Subsingleton (cechHc ι 𝓜 c n) → Subsingleton (cechHc ι 𝓜' c (n + 1)) →
        Subsingleton (cechHc ι 𝓜'' c n)) ∧
      (IsNoetherianRing S → Module.Finite S (cechHc ι 𝓜' c n) → Module.Finite S (cechHc ι 𝓜'' c n) →
        Module.Finite S (cechHc ι 𝓜 c n)) ∧
      (IsNoetherianRing S → Module.Finite S (cechHc ι 𝓜 c n) →
        Module.Finite S (cechHc ι 𝓜' c (n + 1)) → Module.Finite S (cechHc ι 𝓜'' c n)) ∧
      (Subsingleton (cechHc ι 𝓜' c 1) →
        ∀ z'' ∈ cechZc ι 𝓜'' c 0, ∃ z ∈ cechZc ι 𝓜 c 0, cechMap S ι h 0 z = z'') ∧
      (∀ z ∈ cechZc ι 𝓜 c 0, cechMap S ι h 0 z = 0 → ∃ z' ∈ cechZc ι 𝓜' c 0, cechMap S ι g 0 z' = z)

def TheoremSStatement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M),
    IsNoetherianRing S → Module.Finite (MRingOver S ι) M → IsMGraded S ι 𝓜 →
    (∀ (c : K → ℤ) (n : ℕ), Module.Finite S (cechHc ι 𝓜 c n)) ∧
    (∃ c₀ : ℤ, ∀ (c : K → ℤ) (n : ℕ), 1 ≤ n → (∀ k, c₀ ≤ c k) → Subsingleton (cechHc ι 𝓜 c n)) ∧
    (∃ c₀ : ℤ, ∀ c : K → ℤ, (∀ k, c₀ ≤ c k) → ∀ z ∈ cechZc ι 𝓜 c 0,
      ∃ m ∈ 𝓜 c, ∀ I, z I = LocalizedModule.mk m 1) ∧
    (∀ d : K → ℤ, (Submodule.span (MRingOver S ι)
      (⋃ c : ℕ, (cechZc ι 𝓜 (d + fun _ => (c : ℤ)) 0 : Set (CechC S ι M 0)))).FG)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
