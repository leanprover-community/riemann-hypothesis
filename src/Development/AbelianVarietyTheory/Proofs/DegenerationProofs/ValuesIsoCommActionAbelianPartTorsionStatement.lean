module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RatTors
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuesIsoCommActionAbelianPartTorsion
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

theorem _root_.GlobalTheory.T.valuesIso_comm_action_abelianPart_torsion : GlobalTheory.UT.LL → BrGtSt → AllS fun {E} _ _ _ {H} {_} {_} {_} {_} _ {_} {_} _ _ {_} a {_} _ _ A u r {_} M _ {_} ν' J => M.P.TorsionIso → ∀ k : ℕ, 0 < k → Labels A u r M ν' J k → (∀ (x : 𝓞 E) y, ν'.eX (J.e (A.arc.act x y)) = x • ν'.eX (J.e y)) → ∀ (x : 𝓞 E) (y y' : A.N.A), y ^ k = 1 → (letI := H.starRing; A.ν.eA y' = A.ν.eA y ≫ a.oa.onB.act x → ν'.eA (J.φ y') = ν'.eA (J.φ y) ≫ M.P.oD.onB.act x) := by
  first | exact @GlobalTheory.Ex.ActPt.main | exact GlobalTheory.Ex.ActPt.main | (intros; apply GlobalTheory.Ex.ActPt.main <;> assumption)
