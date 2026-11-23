module

public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
public import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAt
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsProductCuspFormNeZeroArchSupNormBounds
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_product_cuspForm_ne_zero_arch_supNorm_bounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ₀ : c.F →+* ℂ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → GoodEmb c σ₀ → AllTest Xo c → 2 ≤ r → ∀ (R : ℕ), Odd R → 1 < R → ∀ (DF q m : ℕ) (R0 : ℝ), RunOK E r DF q R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∃ (i : ℕ) (J : Type) (_ : Fintype J) (cf : J → ℤ) (xs : J → Fin r → LatMod Dw (R ^ 4)) (f : Rul Xo c), 0 < i ∧ Nat.card (LevGrp Dw (R ^ 4)) = 2 * R ^ 4 * i ∧ Spans xs ∧ IsEtaRule Xo c R cf xs f ∧ f ∈ cusp Xo c U 0 (2 * R ^ 4 * r * i) ∧ f ≠ 0 ∧ (∀ k, ∃ x ∈ ((U σ₀).X k).dom, rdU (U σ₀) f k x ≠ 0) ∧ (∀ a n g, Dom a n → g ∈ sec Xo c a n → f * g = 0 → g = 0) ∧ (∀ σ, GoodEmb c σ → ∀ k, ∀ x ∈ ((U σ).X k).dom, ((U σ).X k).pnorm (laU (U σ) 0 (2 * R ^ 4 * r * i) k) (rdU (U σ) f k) x ≤ Real.exp (-(i : ℝ) * (I2.phiFD ((U σ).X k) (I2.th (E := E) q R0) x - p16 E r q m R (max 1 (Fintype.card (U σ₀).Comp) * R ^ (8 * I2.PT.f E * r ^ 2))))) ∧ ∀ σ (xi : ℝ), GoodEmb c σ → supC Xo c U xi σ 0 (2 * R ^ 4 * r * i) f ≤ Real.exp (i * p16 E r q m R (max 1 (Fintype.card (U σ₀).Comp) * R ^ (8 * I2.PT.f E * r ^ 2))) := by
  first | exact @GlobalTheory.EtaAn.exists_etaRule_cusp_ne_zero_bounds | exact GlobalTheory.EtaAn.exists_etaRule_cusp_ne_zero_bounds | (intros; apply GlobalTheory.EtaAn.exists_etaRule_cusp_ne_zero_bounds <;> assumption)
