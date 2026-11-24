module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver secOver)
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)

def ResidueGen.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω)
    (K' : Type) [Field K'] [Algebra F K'] (y' : (Σ k, ι k) → K'),
    mIdealOver F y ≤ mIdealOver F y' →
    ∀ (R : Subalgebra F Ω) (σ : R →ₐ[F] K'),
      (∀ (f g : MRingOver F ι) (n : K → ℕ), IsMultiHomog f n → IsMultiHomog g n → aeval y' g ≠ 0 →
        ∃ h : aeval y f / aeval y g ∈ R, σ ⟨_, h⟩ = aeval y' f / aeval y' g) →
      (∀ d : ∀ k, ι k, (∀ k, y' ⟨k, d k⟩ ≠ 0) → ∀ z ∈ chartRingOver F y d,
        ∃ h : z ∈ R, σ ⟨z, h⟩ ∈ chartRingOver F y' d) →
    ∀ β : K → ℤ, IndefiniteRowSideFullHecke.Kleiman2.IsGenerated F y β → ∀ d₀ : ∀ k, ι k, (∀ k, y' ⟨k, d₀ k⟩ ≠ 0) →
      ∃ ρ : Ω → K',
        (∀ h ∈ secOver F y β, ∃ hh : h * ∏ k, y ⟨k, d₀ k⟩ ^ (-β k) ∈ R,
          σ ⟨_, hh⟩ = ρ h * ∏ k, y' ⟨k, d₀ k⟩ ^ (-β k)) ∧
        ∀ c : ∀ k, ι k, (∀ k, y' ⟨k, c k⟩ ≠ 0) →
          Submodule.span (chartRingOver F y' c) (ρ '' (secOver F y β : Set Ω)) =
            Submodule.span (chartRingOver F y' c) {(∏ k, y' ⟨k, c k⟩ ^ (-β k))⁻¹}

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
