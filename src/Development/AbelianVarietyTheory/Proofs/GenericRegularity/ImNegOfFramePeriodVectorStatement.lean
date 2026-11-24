module

public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ImNegOfFramePeriodVector
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.im_neg_of_frame_period_vector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (D : Datum H) (r : ℕ) (X : Data E r) (φ : D.La ≃ₗ[𝓞 E] X.Λ), GoodEmb c σ → r = Dw.p + Dw.q → X.p0 = Dw.q → (∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) → (∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b))) → ∀ x ∈ X.dom, ∀ P : D.La →+ (Fin g → ℂ), (∀ a j, P a j = perFr X x (φ a : Fin r → E) (relab c σ (e j).1) (e j).2) → IsPeriod D (fun j => relab c σ (e j).1) P → r ≠ 0 → ∀ τ ∈ X.Ψ, (τ X.ξ0).im < 0 := by
  first | exact @GlobalTheory.FrameSign.im_neg_of_isPeriod | exact GlobalTheory.FrameSign.im_neg_of_isPeriod | (intros; apply GlobalTheory.FrameSign.im_neg_of_isPeriod <;> assumption)
