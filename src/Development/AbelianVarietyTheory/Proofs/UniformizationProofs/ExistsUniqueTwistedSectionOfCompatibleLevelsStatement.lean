module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueTwistedSectionOfCompatibleLevels
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.existsUnique_twistedSection_of_compatible_levels : Laws → Laws2 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V) (k : ℕ), 1 ≤ k → ∀ (α : D.X) (f : ∀ e, LB.Sec (LB.LinComb D.P.L (fun i => (D.prBe (IsLocalRing.maximalIdeal V) e).left ≫ D.famφB α i) (DegPre.famε k))), (∀ e z J, Good D.P.L z J → sval (f (e + 1)) (thickMap V _ e D.P.A) z J = sval (f e) (𝟙 _) z J) → ∃! s : D.SecB k α, ∀ e z J, Good D.P.L z J → sval s (D.prBe (IsLocalRing.maximalIdeal V) e).left z J = sval (f e) (𝟙 _) z J) := by
  first | exact @GlobalTheory.SecLimit.existsUnique_sec_of_compatible | exact GlobalTheory.SecLimit.existsUnique_sec_of_compatible | (intros; apply GlobalTheory.SecLimit.existsUnique_sec_of_compatible <;> assumption)
