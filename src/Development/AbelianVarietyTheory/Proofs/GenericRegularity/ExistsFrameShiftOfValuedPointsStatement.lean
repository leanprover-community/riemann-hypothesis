module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Formalism.LocalToGlobal.ProjectiveLattices.CompOrd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFrameShiftOfValuedPoints
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.exists_frame_shift_of_valued_points : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → IntDiagUnit Xo c → (∀ la, ModelAt Xo c la) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (h : GenFrEx Xo c), ∃ δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ, (∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)), ReciprocityTheory.ChartRestriction.G.T0.IsNormDiscrete v → ((∃ la, ReciprocityTheory.ChartRestriction.G.T0.IsOver (K := c.F) v la) ∨ ReciprocityTheory.ChartRestriction.G.T0.IsTrivOn c.F v) → ∃ (T : CDVR) (ψ : Om Z →+* T.Fr) (y : IntFr Xo c T (ψ.comp (algebraMap c.F (Om Z)))), (∀ a : Om Z, a ≠ 0 → ((vV T.V (ψ a) : ℤ) : WithTop ℤ) = v a) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → (evI y f = 0 ↔ evC h Z f = 0) ∧ (evC h Z f ≠ 0 → ordC (δ Z v) v (wtZ a n) (valC h a n f Z) = vV T.V (evI y f))) ∧ ∀ Z : Comp Xo c, ∃ S : Finset (Om Z), (∀ s ∈ S, s ≠ 0) ∧ ∀ v : AddValuation (Om Z) (WithTop ℤ), ReciprocityTheory.ChartRestriction.G.T0.IsNormDiscrete v → ((∃ la, ReciprocityTheory.ChartRestriction.G.T0.IsOver (K := c.F) v la) ∨ ReciprocityTheory.ChartRestriction.G.T0.IsTrivOn c.F v) → (∀ s ∈ S, v s = 0) → δ Z v = 0 := by
  first | exact @GlobalTheory.Reg.exists_frameShift_of_valued_points | exact GlobalTheory.Reg.exists_frameShift_of_valued_points | (intros; apply GlobalTheory.Reg.exists_frameShift_of_valued_points <;> assumption)
