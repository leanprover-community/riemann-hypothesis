module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoSlopeMetaplecticLiftSchwartz
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

open scoped Matrix

theorem _root_.GlobalTheory.T.tendsto_slope_metaplecticLift_schwartz : ∀ (l : Type) [Fintype l] [DecidableEq l] (G : Type) [Group G] (pr : G →* Matrix.symplecticGroup l ℝ)
    (om : G →* (GlobalTheory.RealWeil.L2 l ≃ₗᵢ[ℂ] GlobalTheory.RealWeil.L2 l)) (omS : G →* (GlobalTheory.RealWeil.Sch l →L[ℂ] GlobalTheory.RealWeil.Sch l)),
    (∀ (g : G) (w : l ⊕ l → ℝ) (f : GlobalTheory.RealWeil.L2 l),
      om g (GlobalTheory.RealWeil.rho w f) = GlobalTheory.RealWeil.rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) →
    (∀ (g : G) (f : GlobalTheory.RealWeil.Sch l), om g (f.toLp 2) = (omS g f).toLp 2) →
    ∀ X ∈ LieAlgebra.Symplectic.sp l ℝ, ∀ γ : ℝ → G, γ 0 = 1 →
    (∀ t, (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = NormedSpace.exp (t • X)) →
    (∀ f : GlobalTheory.RealWeil.Sch l, HasDerivAt (fun t => om (γ t) (f.toLp 2)) ((GlobalTheory.RealWeil.quad X f).toLp 2) 0) →
    ∀ f : GlobalTheory.RealWeil.Sch l,
      Filter.Tendsto (fun t : ℝ => t⁻¹ • (omS (γ t) f - f)) (nhdsWithin 0 {0}ᶜ) (nhds (GlobalTheory.RealWeil.quad X f)) := by
  first | exact @GlobalTheory.RealWeil.tendsto_slope_omS_schwartz | exact GlobalTheory.RealWeil.tendsto_slope_omS_schwartz | (intros; apply GlobalTheory.RealWeil.tendsto_slope_omS_schwartz <;> assumption)
