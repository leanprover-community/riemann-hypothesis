module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionInvarianceCosetSum
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Filter Topology

theorem _root_.GlobalTheory.T.section_invariance_coset_sum : PositivityTheory.RgEis.PiLocalization₂ → ∀ (G : Type) [Group G] (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    (Γ K Q P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) (ξ lam : G → ℝ) (Λ : G → ℂ) (s : ℂ) (w : W) (Ms : ℝ),
    P ≤ Q → (∀ γ ∈ Γ, γ ∈ Q → ∀ x, ξ (γ * x) = ξ x) → (∀ γ ∈ Γ, γ ∈ P → ∀ x, Λ (γ * x) = Λ x) →
    (∀ γ ∈ Γ, γ ∈ P → ∀ x, PositivityTheory.RgEis.sec K P c ρ (γ * x) w = PositivityTheory.RgEis.sec K P c ρ x w) →
    (∀ x, ‖PositivityTheory.RgEis.sec K P c ρ x w‖ ≤ Ms) → PositivityTheory.RgEis.Conv Γ P lam →
    (∀ x, (Λ x + s * ξ x).re = lam x) → ∀ g : G,
    ∑' r : PositivityTheory.RgEis.Cos (Γ ⊓ Q) Γ, Complex.exp (s * ξ (PositivityTheory.RgEis.rep r * g)) •
        PositivityTheory.RgEis.eis (Γ ⊓ Q) K P c ρ Λ (PositivityTheory.RgEis.rep r * g) w =
      PositivityTheory.RgEis.eis Γ K P c ρ (fun x => Λ x + s * ξ x) g w := by
  first | exact @GlobalTheory.CompanionTheory.RgEisCross.stage_eis | exact GlobalTheory.CompanionTheory.RgEisCross.stage_eis | (intros; apply GlobalTheory.CompanionTheory.RgEisCross.stage_eis <;> assumption)
