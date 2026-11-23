module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreIsotropicPointsInjectiveRoots
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

theorem _root_.GlobalTheory.T.analyticFibre_isotropic_points_injective_roots : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (n N : ℕ) (Λ : Lt E n), 0 < N → (∀ (Jx : Type) (u : Jx → Matrix (Fin n) (Fin r) E), (∀ i, u i ∈ tens Λ L ∧ ∀ b, ∃ u' ∈ L, N • u i b = (2 : ℕ) • u') → (∀ i i', (∀ b, ∃ u' ∈ L, u i b - u i' b = N • u') → i = i') → (∀ i, InZh Xo (⟨Λ⟩ : GenLat E n) N (fun b => A.ex (pv X idx x ((N : E)⁻¹ • u i b)))) ∧ GeoInj Xo y.x (fun i b => A.ex (pv X idx x ((N : E)⁻¹ • u i b)))) ∧ ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → A.Marked mk → l.M ∣ N → ∀ Y : (Fin n → LevQ Dw l) → Matrix (Fin n) (Fin r) E, IsRoots l L mk N Y → ∀ q b, A.ex (pv X idx x ((N : E)⁻¹ • Y q b)) ^ N = levPt Xo y.x (levRep (q b)) ∧ (∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (A.ex (pv X idx x ((N : E)⁻¹ • Y q b)))) ∧ ∃ u ∈ L, (N ^ 2 : ℕ) • ((N : E)⁻¹ • Y q b) = (2 : ℕ) • u := by
  first | exact @GlobalTheory.Dict.points_inZh_geoInj_roots | exact GlobalTheory.Dict.points_inZh_geoInj_roots | (intros; apply GlobalTheory.Dict.points_inZh_geoInj_roots <;> assumption)
