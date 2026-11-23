module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCoeffNeZeroOfFourierJacobiArcDatum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.exists_coeff_ne_zero_of_fourierJacobi_arcDatum : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁) (em : K₁ →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (r : ℕ) (U : Unf Xo c (em.comp (algebraMap c.F K₁)) r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Std d → GoodEmb c (em.comp (algebraMap c.F K₁)) → IsUnf U → GlobalTheory.FrameNorm.HasPrinc U l.M → Dom a' n → (∀ k, ∀ gm ∈ (U.X k).Γ, (U.X k).χ (laU U a' n k) gm = 1) → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → Comparison₂ Uw d.a em s.ξ k ξ' x → ∀ F ∈ sec Xo c a' n, (∀ k', (U.X k').IsBddSec (laU U a' n k') (rdU U F k')) → (U.X k).fj (laU U a' n k) ξ' (fun τ => (τ.1 s.ν₀).re) (rdU U F k) x ≠ 0 → ∃ mo : ArcLt Dw →₀ ℕ, cfOf d.yF mo d.jj F ≠ 0 := by
  first | exact @GlobalTheory.DerivativeDetermination.exists_cfOf_ne_zero | exact GlobalTheory.DerivativeDetermination.exists_cfOf_ne_zero | (intros; apply GlobalTheory.DerivativeDetermination.exists_cfOf_ne_zero <;> assumption)
