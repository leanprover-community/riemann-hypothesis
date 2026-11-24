module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFinrankEqNormPow
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

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isFinite_and_finrank_act_eq_norm_pow : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A →
    ∀ (F : Type) [Field F] [NumberField F] (ρ : OAct (𝓞 F) A) (l d : ℕ), l.Prime → (l : k) ≠ 0 →
    Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ l = 1} = l ^ (d * Module.finrank ℚ F) →
    ∀ c : 𝓞 F, c ≠ 0 → IsFinite (ρ.act c).left ∧
      (ρ.act c).left.finrank ((1 : Over.mk (𝟙 (Sp k)) ⟶ A).left (IsLocalRing.closedPoint k)) =
        (Algebra.norm ℤ c).natAbs ^ d := by
  first | (exact @GlobalTheory.AV.OActDeg.isFinite_and_finrank_eq_norm_pow) | (exact GlobalTheory.AV.OActDeg.isFinite_and_finrank_eq_norm_pow) | (intros; apply GlobalTheory.AV.OActDeg.isFinite_and_finrank_eq_norm_pow  <;> assumption)
