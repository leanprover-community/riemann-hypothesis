module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightSectionEqZeroOfVanishingFiniteExtensions
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

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem _root_.GlobalTheory.T.weightSection_eq_zero_of_vanishing_finite_extensions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (h : Rul Xo c), h ∈ sec Xo c a n → (∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (y : FrPt Xo c L), evR Xo c h y = 0) → h = 0 := by
  first | exact @GlobalTheory.Reg.sec_eq_zero_of_finite_values | exact GlobalTheory.Reg.sec_eq_zero_of_finite_values | (intros; apply GlobalTheory.Reg.sec_eq_zero_of_finite_values <;> assumption)
