module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SectionsReadAsTranslatesAtScaledPoint
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

theorem _root_.GlobalTheory.T.sections_read_as_translates_at_scaled_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (N : ℕ), Odd N → ∀ θ, A.Reads 1 y.s θ → (∀ a₁ a₂ : Fin r → E, (∃ u ∈ L, (N ^ 2 : ℕ) • a₁ = (2 : ℕ) • u) → (∃ u ∈ L, (N ^ 2 : ℕ) • a₂ = (2 : ℕ) • u) → ∀ F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)), IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (A.ex (pv X idx x a₁)) (A.ex (pv X idx x a₂)) F → A.Reads ((N : ℤ) ^ 2) F (fun z => fock X bas idx x 1 (pv X idx x ((N : E) • a₂)) (fock X bas idx x 1 (pv X idx x ((N : E) • a₁)) θ) ((N : ℂ) • z))) ∧ ∀ a : Fin r → E, (∃ u ∈ L, (N ^ 2 : ℕ) • a = (2 : ℕ) • u) → ∀ (t : (ptO Xo y.x) ⟶ Xo.univ.t.G) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), IsVtOver Xo.univ.t.G Xo.univ.t.PP N (fun t' => t' = A.ex (pv X idx x a)) y.s t F → A.Reads ((N : ℤ) ^ 2) F (fun z => fock X bas idx x 1 (pv X idx x ((N : E) • a)) θ ((N : ℂ) • z)) := by
  first | exact @GlobalTheory.Dict.reads_isUUOver_isVtOver | exact GlobalTheory.Dict.reads_isUUOver_isVtOver | (intros; apply GlobalTheory.Dict.reads_isUUOver_isVtOver <;> assumption)
