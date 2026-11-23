module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.CompOrd
public import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PointwiseNormSectionEqFlagDomainNorm
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
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

theorem _root_.GlobalTheory.T.pointwise_norm_section_eq_flagDomain_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → FnNe Xo c fn ∧ (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → ∀ k (x : ((U σ).X k).dom) (t : Ix Dw → (CAt σ)ˣ) (y : FrPt Xo c (CAt σ)), FrBor t ((U σ).un k x) y → ∀ a n, Dom a n → ∀ f ∈ sec Xo c a n, ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f y = Formalism.L2.PjFree.lieFac Dw xR a * ((U σ).X k).pnorm (Formalism.L2.PjFree.laU (U σ) a n k) (Formalism.L2.PjFree.rdU (U σ) f k) x.1) ∧ ∀ (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt ((starRingEnd ℂ).comp σ))), FrMap (conjAlg σ) y y' → ∀ a n, ∀ f ∈ sec Xo c a n, ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((starRingEnd ℂ).comp σ) (fn ((starRingEnd ℂ).comp σ)) (ex Dw a n) f y' = ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f y := by
  first | exact @GlobalTheory.FrameNorm.Comparison₂.ptNorm_eq_pnorm | exact GlobalTheory.FrameNorm.Comparison₂.ptNorm_eq_pnorm | (intros; apply GlobalTheory.FrameNorm.Comparison₂.ptNorm_eq_pnorm <;> assumption)
