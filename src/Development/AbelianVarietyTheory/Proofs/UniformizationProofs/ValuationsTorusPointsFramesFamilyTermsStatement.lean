module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsTorusPointsFramesFamilyTerms
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.valuations_torusPoints_frames_familyTerms : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ g : GtPtF D.toPre F, (∃! l : D.toPre.X →+ ℚ, GtV hϖ hv g l) ∧ (∀ (k : ℕ) (w : Frm D.toPre F k g.b), w.IsGen → ∃! r, GenV hϖ hv w r) ∧ (∀ (k : ℕ) (w : Frm D.toPre F k g.b), FrmOne w → g.b = 1 → GenV hϖ hv w 0) ∧ (∀ (g' g'' : GtPtF D.toPre F) l l', g.IsAdd g' g'' → GtV hϖ hv g l → GtV hϖ hv g' l' → GtV hϖ hv g'' (l + l')) ∧ (∀ (k : ℕ), 1 ≤ k → ∀ p : QkPt D.toPre F k, GtV hϖ hv p.g fun χ => (QForm.bOf D.toPre Q p.y χ : ℚ) / k) ∧ (∀ y, GtPtF.IsIota y g → GtV hϖ hv g fun χ => (QForm.bOf D.toPre Q y χ : ℚ)) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (w : Frm D.toPre F k g.b) (s : Fam D.toPre F k), w.IsGen → NullV v (coef s g w) ∧ ∀ l ω r, GtV hϖ hv g l → GenV hϖ hv w ω → NuGe D Q F v k s r → ∀ χ, ((r + (Q χ : ℚ) / k + l χ + ω : ℚ) : WithTop ℚ) ≤ v (coef s g w χ) := by
  first | exact @GlobalTheory.UT.CoefVal.main | exact GlobalTheory.UT.CoefVal.main | (intros; apply GlobalTheory.UT.CoefVal.main <;> assumption)
