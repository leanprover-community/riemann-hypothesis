module

public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EvaluationLemmaForNablaLevels
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.evaluation_lemma_for_nabla_levels : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), EvalWD (K := d.c₂.F) (fun S _ _ => FrPt d.Xo₂ d.c₂ S) (fun φ y z => FrMap φ y z) → AllTest d.Xo₂ d.c₂ → @ToroidalLevelCompatibility E _ _ _ H Dw → d.IsLev → d.l₂.A = l.A → ∀ [StarRing (𝓞 E)], IsNab d.Xo₂ d.c₂ d.nab₂ → (∃ ph ψ x₀, d.PhiPin ph ψ x₀ ∧ d.PsiTie ψ) → ∀ (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) d.c₂.F), P ∈ HHa Dw.mult n d.c₂.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (x0 : Fin n → Dw.La) (β : d.c₂.F), ∀ (p : TRing c.F) (y : FrPt Xo c p.R), ∃! u : p.R, ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k], (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) → ∀ (χ : p.R →ₐ[c.F] k) (z : FrPt Xo c k) (z₂ : FrPt d.Xo₂ d.c₂ k), FrMap χ y z → FrOver d z₂ z → ∀ v, ShortValAt d.Xo₂ d.c₂ d.nab₂ (d.w x0) Λ β N P z₂ v → χ u = evR d.Xo₂ d.c₂ d.cδ z₂ * v := by
  first | exact @GlobalTheory.CoverDescent.shortValue_descends | exact GlobalTheory.CoverDescent.shortValue_descends | (intros; apply GlobalTheory.CoverDescent.shortValue_descends <;> assumption)
