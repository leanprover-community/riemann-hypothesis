module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.PullHomeoApply
public import Mathlib.LinearAlgebra.Matrix.Rank
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

noncomputable section

open Matrix Polynomial PositivityTheory.PfBern.Frob

namespace PositivityTheory.RgUd.TP.Desc.Piece.Tr

def DoubleTransfer : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [TotallyDisconnectedSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H₁ H₂ : Subgroup G) [LocallyCompactSpace H₁] [LocallyCompactSpace H₂], IsClosed (H₁ : Set G) →
    IsClosed (H₂ : Set G) → IsUnimod G → IsUnimod H₁ → IsUnimod H₂ →
    ∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
      [MulAction G X] [ContinuousSMul G X] (p₁ : X → G ⧸ H₁) (p₂ : X → G ⧸ H₂), Continuous p₁ → Continuous p₂ →
      ∀ (hp₁ : ∀ (g : G) (x : X), p₁ (g • x) = g • p₁ x) (hp₂ : ∀ (g : G) (x : X), p₂ (g • x) = g • p₂ x)
        (C : Set X), IsClosed C → (∀ g : G, ∀ x ∈ C, g • x ∈ C) →
        (∀ E ∈ eqvF hp₂ ((1 : G →* ℂˣ).comp H₂.subtype), SupportedIn E (Subtype.val ⁻¹' C)) →
        ∀ E ∈ eqvF hp₁ ((1 : G →* ℂˣ).comp H₁.subtype), SupportedIn E (Subtype.val ⁻¹' C)

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def OrbHom : Prop :=
  ∀ (N : ℕ) (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A], IsReduced A →
    ∀ ρ ρ' : A →ₐ[k] Matrix (Fin N) (Fin N) k, (∀ e : A, IsIdempotentElem e → (ρ e).rank = (ρ' e).rank) →
      ∃ g : GL (Fin N) k, ∀ a, ρ' a = g.val * ρ a * g⁻¹.val

def OrbClosed : Prop :=
  ∀ (N r : ℕ) (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A], IsReduced A →
    ∀ (b : Fin r → A), Submodule.span k (Set.range b) = ⊤ → ∀ ρ₀ : A →ₐ[k] Matrix (Fin N) (Fin N) k,
      IsClosed {w : Fin r → Matrix (Fin N) (Fin N) k | ∃ g : GL (Fin N) k, ∀ i, w i = g.val * ρ₀ (b i) * g⁻¹.val}

end PositivityTheory.RgUd.TP.Desc.Piece.Tr
