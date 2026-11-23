module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AmpleSt
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 Filter Asymptotics

def mConeMapOver (S : Type*) [CommRing S] {K : Type*} {ι : K → Type*} {Ω : Type*} [Field Ω] [Algebra S Ω]
    (y : (Σ k, ι k) → Ω) : MRingOver S ι →ₐ[S] MvPolynomial K Ω :=
  aeval fun p => MvPolynomial.C (y p) * MvPolynomial.X p.1

def mIdealOver (S : Type*) [CommRing S] {K : Type*} {ι : K → Type*} {Ω : Type*} [Field Ω] [Algebra S Ω]
    (y : (Σ k, ι k) → Ω) : Ideal (MRingOver S ι) :=
  RingHom.ker (mConeMapOver S y)

def chartRingOver (S : Type*) [CommRing S] {K : Type*} {ι : K → Type*} {Ω : Type*} [Field Ω] [Algebra S Ω]
    (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : Subalgebra S Ω :=
  Algebra.adjoin S (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)

def secOver (S : Type*) [CommRing S] {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω]
    [Algebra S Ω] (y : (Σ k, ι k) → Ω) (n : K → ℤ) : Submodule S Ω :=
  ⨅ (c : ∀ k, ι k) (_ : ∀ k, y ⟨k, c k⟩ ≠ 0),
    (Subalgebra.toSubmodule (chartRingOver S y c)).comap
      (LinearMap.mulRight S (∏ k, y ⟨k, c k⟩ ^ (-n k)))

def secMOver (S : Type*) [CommRing S] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {Ω : Type*} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (d : K → ℕ) : Submodule S Ω :=
  Submodule.span S {s | ∃ g : MRingOver S ι, IsMultiHomog g d ∧ aeval y g = s}

def GeneratesOver (S : Type*) [CommRing S] {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω]
    [Algebra S Ω] {ι' : Type*} [Fintype ι'] (y : (Σ k, ι k) → Ω) (n : K → ℤ) (x' : ι' → Ω) : Prop :=
  ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ u : ι' → Ω, (∀ j, u j ∈ chartRingOver S y c) ∧
    ∑ j, u j * (x' j * ∏ k, y ⟨k, c k⟩ ^ (-n k)) = 1

def GlobalSectionsComparisonStatement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω]
    (y : (Σ k, ι k) → Ω) (n : K → ℤ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
    ∃ φ : ↥(cechZc ι (quotPart S (mIdealOver S y)) n 0) →ₗ[S] Ω,
      Function.Injective φ ∧ LinearMap.range φ = secOver S y n ∧
      ∀ (z : ↥(cechZc ι (quotPart S (mIdealOver S y)) n 0)) (d : K → ℕ) (g : MRingOver S ι),
        (fun k => (d k : ℤ)) = n → IsMultiHomog g d →
        (∀ I, (z : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) 0) I =
          LocalizedModule.mk (Ideal.Quotient.mk _ g) 1) →
        φ z = aeval y g

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
