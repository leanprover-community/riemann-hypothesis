module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteRepSetOfOrtho
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SigmaCount
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsBasisLocF
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomLiftBasis
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SigmaCountPosBasis
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.VdEqZeroOfNotLe
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

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_isom_lift (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ k)
    (X : Module.End (𝓞 K) (↥(locF 𝔭 A₀) ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 A₀))))
    (hX : ∀ x y x' y' : ↥(locF 𝔭 A₀), Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
      Submodule.Quotient.mk y' = X (Submodule.Quotient.mk y) →
      CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V))) :
    ∃ g ∈ autSub h (locF 𝔭 A₀), ∀ x x' : ↥(locF 𝔭 A₀), Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
      g x - x' ∈ ((extP K 𝔭) ^ (k - eA h (locF 𝔭 A₀) 𝔭) • (locF 𝔭 A₀) : Submodule (𝓞 K) V) := by
  obtain ⟨b, hbL, hb⟩ := LocalSpans.exists_basis_locF hA₀ h𝔭
  obtain ⟨H, hH, -⟩ := LocF.exists_gram hA₀i b hbL
  have hd' := LocF.aniso_of_totPosDef hd
  have key : ∀ A : Submodule (𝓞 K) V, A = locF 𝔭 (integralBasisSpans.spanO b) → ∀ k : ℕ, eA h A 𝔭 + 1 ≤ k →
      ∀ X : Module.End (𝓞 K) (↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A)),
      (∀ x y x' y' : ↥A, Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
        Submodule.Quotient.mk y' = X (Submodule.Quotient.mk y) →
        CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V))) →
      ∃ g ∈ autSub h A, ∀ x x' : ↥A, Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
        g x - x' ∈ ((extP K 𝔭) ^ (k - eA h A 𝔭) • A : Submodule (𝓞 K) V) := by
    rintro _ rfl k hk X hX
    exact HU.exists_isom_lift_basis hK hF hs hd' b hH h𝔭 (HU.isE_eA hK hF hd' b h𝔭) hk X hX
  exact key _ hb.symm k hk X hX

end Formalism.HermitianLattices.Ext.L3
