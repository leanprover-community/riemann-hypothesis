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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def IsPrimeFilt (S : Type*) [CommRing S] {K : Type*} [Fintype K] (ι : K → Type*) [∀ k, Fintype (ι k)]
    {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] (𝓜 : (K → ℤ) → Submodule S M)
    {r : ℕ} (m : Fin r → M) (c : Fin r → K → ℤ) (𝔭 : Fin r → Ideal (MRingOver S ι)) : Prop :=
  (∀ j, m j ∈ 𝓜 (c j)) ∧
    (∀ j, (𝔭 j).IsPrime ∧ IsMultiHomogIdeal (𝔭 j) ∧ Module.annihilator (MRingOver S ι) M ≤ 𝔭 j) ∧
    (∀ j (p : MRingOver S ι), p • m j ∈ Submodule.span (MRingOver S ι) (m '' {l | l < j}) ↔ p ∈ 𝔭 j) ∧
    Submodule.span (MRingOver S ι) (Set.range m) = ⊤

def PrimeFiltStatement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M),
    IsNoetherianRing S → Module.Finite (MRingOver S ι) M → IsMGraded S ι 𝓜 →
    ∃ (r : ℕ) (m : Fin r → M) (c : Fin r → K → ℤ) (𝔭 : Fin r → Ideal (MRingOver S ι)),
      IsPrimeFilt S ι 𝓜 m c 𝔭

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
