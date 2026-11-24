module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackCompDiagonalBundle
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.harrisTaylorObjectPullback_comp_diagonalBundle : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S S' S'' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (s'' : S'' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N s') (o'' : Obj b N s'') (f : S' ⟶ S) (f' : S'' ⟶ S'), (Nonempty (ObjMap o'' o' f') → Nonempty (ObjMap o' o f) → Nonempty (ObjMap o'' o (f' ≫ f))) ∧ ∀ m : ObjMap o' o f, LBIso (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull m.φ) := by
  first | exact @GlobalTheory.UPel.HT.objMap_comp_diag_lbIso | exact GlobalTheory.UPel.HT.objMap_comp_diag_lbIso | (intros; apply GlobalTheory.UPel.HT.objMap_comp_diag_lbIso <;> assumption)
