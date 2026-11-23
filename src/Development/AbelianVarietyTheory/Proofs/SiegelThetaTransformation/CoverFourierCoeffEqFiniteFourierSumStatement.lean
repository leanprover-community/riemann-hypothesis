module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CoverFourierCoeffEqFiniteFourierSum
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.coverFourierCoeff_eq_finite_fourier_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra c.F ℂ] [Algebra d.c₂.F ℂ], (∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t) → d.IsLev → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ (r : ℕ) (X : Data E r) (D : SW.Level X) (hn : r ≤ n), r = Dw.p + Dw.q → LevTie d (algebraMap c.F ℂ) ph D hn → ∀ L ∈ D.lats, ∀ (mk mk₂ δ : Dw.La →ₗ[𝓞 E] (Fin r → E)) (x0 : Fin n → Dw.La), IsMark l L mk → IsMark d.l₂ L mk₂ → MarkOver l d.l₂ L mk mk₂ → IsDual X l (algebraMap c.F ℂ (zetaM c)) L mk δ → IsBaseClassLevelAdapted d D hn x0 δ → ∃ t : ℂ, ‖t‖ = 1 ∧ ∀ Λ ∈ Vset E n d.l₂.M, ∀ N : ℕ, NOK Λ N d.l₂.M → ∀ Y : (Fin n → LevQ Dw d.l₂) → Matrix (Fin n) (Fin r) E, IsRoots d.l₂ L mk₂ N Y → ∀ q, algebraMap d.c₂.F ℂ (d.w x0 q) = t * ∑ᶠ cl : tens Λ ((Ideal.span {2} * conjI D.𝔪) • L) ⧸ (tens Λ ((Ideal.span {2} * conjI D.𝔪 * D.𝔪) • L)).addSubgroupOf _, datF D (Mfr l) hn (cl.out : Matrix (Fin n) (Fin r) E) * cexp (-(2 * Real.pi * I * ((∑ b, EF X ((cl.out : Matrix (Fin n) (Fin r) E) b) (Y q b) : ℚ) : ℂ))) := by
  first | exact @GlobalTheory.Dict.CoverFourier.w_eq_sum | exact GlobalTheory.Dict.CoverFourier.w_eq_sum | (intros; apply GlobalTheory.Dict.CoverFourier.w_eq_sum <;> assumption)
