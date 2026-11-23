module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def NfacRmulStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r), ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
    X.nfac la (rmul x b) = ‖bchar la b‖⁻¹ * X.nfac la x

def NfacLactStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r), ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, X.nfac la (lact γ x) = X.nfac la x

def PnormInvStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsSec la P →
    ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      X.pnorm la P (lact γ (rmul x b)) = X.pnorm la P x

def KapGGStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 x1 : Frame X.Ψ r) (γ : GL (Fin r) E) (U : Set (V (nd X)))
    (Φ : V (nd X) → V (nd X)) (bf : V (nd X) → Frame X.Ψ r), IsOpen U → DifferentiableOn ℂ Φ U →
    (∀ z ∈ U, cpt X x0 z ∈ X.dom ∧ bf z ∈ Bor X.Ψ r ∧
      cpt X x0 z = lact γ (rmul (cpt X x1 (Φ z)) (bf z))) →
    ∀ z ∈ U, (fderiv ℂ Φ z).det = bchar (kapW X) (bf z)

def CurvGGStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x0 : Frame X.Ψ r) (z : V (nd X)), cpt X x0 z ∈ X.dom →
    (X.IsDominant la → ∀ ξ : Fin (nd X) → ℂ,
      0 ≤ (leviV (nd X) (fun w => ((-2 * Real.log (X.nfac la (cpt X x0 w)) : ℝ) : ℂ)) z ξ).re) ∧
    (IsStrictDom X la → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
      0 < (leviV (nd X) (fun w => ((-2 * Real.log (X.nfac la (cpt X x0 w)) : ℝ) : ℂ)) z ξ).re)

def LineBundleFirstBoundGlobalGeneration : Prop :=
  ∀ (r : ℕ) (X : Data E r), 0 < r →
    (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, X.la1 (lact γ (rmul x b)) = X.la1 x) ∧
    ContinuousOn X.la1 X.dom ∧ ∀ x ∈ X.dom, 0 < X.la1 x

end

end ReciprocityTheory.ChartRestriction.G.AR.Inst
