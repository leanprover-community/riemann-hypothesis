module

public import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
public import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementC
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


theorem _root_.GlobalTheory.T.meanLogSupNorm_lowerBound_cmFrame_nonvanishing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = ξ) → 1 ≤ Dw.p + Dw.q → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ a n, Dom a n → ∀ F ∈ cusp Xo c U a n, (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → (∀ σ, 0 < supC Xo c U ξ (goodOf c σ) a n F) → ∀ (k : (U c.F.val.toRingHom).Comp) (x₀ : ((U c.F.val.toRingHom).X k).dom) (Xx : FD.DataX E r) (hX : Xx.toData = (U c.F.val.toRingHom).X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → ∀ (La : ℝ) (lam : Fin r → Fin r → E), 1 ≤ La → FD.LamBasis Xx La (hX ▸ x₀.1) lam → rdU (U c.F.val.toRingHom) F k x₀.1 ≠ 0 → -((pDeg (logOm E χ).re + (1 / 2) * Real.log La) * (((∑ b : E →+* ℂ, ∑ i : Fin (Dw.mult b), a (b, i) : ℕ) : ℝ) + ((Module.finrank ℚ E / 2 * r : ℕ) : ℝ) * n)) - ((∑ b : E →+* ℂ, ∑ i : Fin (Dw.mult b), a (b, i) : ℕ) : ℝ) * Real.log ((r : ℝ) * La) ≤ (∑ σ : c.F →+* ℂ, Real.log (supC Xo c U ξ (goodOf c σ) a n F)) / (Module.finrank ℚ c.F : ℝ) := by
  first | exact @GlobalTheory.LamT.meanLogSup_lowerBound | exact GlobalTheory.LamT.meanLogSup_lowerBound | (intros; apply GlobalTheory.LamT.meanLogSup_lowerBound <;> assumption)
