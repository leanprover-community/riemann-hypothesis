module

public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramePeriodsAlongIsotropicFlowAndBlockChange
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
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcSPin

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.framePeriods_along_isotropic_flow_and_block_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ ξ, herm X.Gm ξ ξ = 0 → ∀ (s : X.Ψ → ℂ), ∀ x ∈ X.dom, ∀ (v : Fin r → E) (τ : X.Ψ) (i : ℕ), perFr X (X.flow ξ s x) v τ.1 i = perFr X x v τ.1 i - s τ * τ.1 (X.κ0 * herm X.Gm v ξ) * perFr X x ξ τ.1 i ∧ (i < X.p0 → perFr X (X.flow ξ s x) v (conjEmb τ.1) i = perFr X x v (conjEmb τ.1) i - s τ * conjEmb τ.1 (X.κ0 * herm X.Gm v ξ) * perFr X x ξ (conjEmb τ.1) i)) ∧ ∀ x ∈ X.dom, ∀ (A : X.Ψ → Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) (B : X.Ψ → Matrix (Fin X.p0) (Fin X.p0) ℂ), (∀ τ, (A τ).det ≠ 0) → (∀ τ, (B τ).det ≠ 0) → ∃ x' ∈ X.dom, ∀ (v : Fin r → E) (τ : X.Ψ), (∀ i : Fin (r - X.p0), perFr X x' v τ.1 i = ∑ k, A τ i k * perFr X x v τ.1 k) ∧ ∀ i : Fin X.p0, perFr X x' v (conjEmb τ.1) i = ∑ k, B τ i k * perFr X x v (conjEmb τ.1) k := by
  first | exact @GlobalTheory.PerFlow.perFr_flow_block | exact GlobalTheory.PerFlow.perFr_flow_block | (intros; apply GlobalTheory.PerFlow.perFr_flow_block <;> assumption)
