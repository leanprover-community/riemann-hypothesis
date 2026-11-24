module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginWeightIdentity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumFundCoMulSumIic

@[expose] public section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund


theorem _root_.GlobalTheory.T.root_origin_weight_identity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (nu : Wt (CMType H) (D.p + D.q)), (∀ r, (Fx.n r : ℝ) = (Fx.kA * Fx.q' : ℕ) * nu r.1 r.2) → ∃ (n₀ : Option (RootIx D) → ℤ) (N₀ : ℕ), (∀ j, (n₀ j : ℝ) = (Fx.kA * Fx.q' : ℕ) * RM.coef nu (-1) j) ∧ 0 < N₀ ∧ ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) ≠ 0 ∧ ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) ∈ chartLatNm RM.y (combLine (RM.line 1) n₀).a 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.OriginEps.section_on_model | exact GlobalTheory.CompanionTheory.Ar.Small.OriginEps.section_on_model | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.OriginEps.section_on_model <;> assumption)
