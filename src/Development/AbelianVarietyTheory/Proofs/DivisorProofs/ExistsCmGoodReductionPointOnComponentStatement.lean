module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmGoodReductionPointOnComponent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem _root_.GlobalTheory.T.exists_cm_goodReduction_point_on_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c), ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra c.F K) (y : FrPt Xo c K) (ρ₀ : 𝓞 K) (σ₁ : K →+* ℂ) (X : GlobalTheory.CM.CMObj H K ρ₀ σ₁ Dw.p Dw.q) (t₀ : SAB H (Sp K)), LiesOn Z y ∧ Nonempty (SABMap t₀ Xo.univ.t y.x) ∧ Nonempty (SABMap t₀ X.B.t (spMap (algebraMap (𝓞 K) K))) ∧ ∀ τ : Psi H, ((ρ₀ : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 H.rt) := by
  first | exact @GlobalTheory.FlatCore.exists_cmPt_on_comp | exact GlobalTheory.FlatCore.exists_cmPt_on_comp | (intros; apply GlobalTheory.FlatCore.exists_cmPt_on_comp <;> assumption)
