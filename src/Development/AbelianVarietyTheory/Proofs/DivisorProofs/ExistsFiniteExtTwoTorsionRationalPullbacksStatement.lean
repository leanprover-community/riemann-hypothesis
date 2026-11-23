module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtTwoTorsionRationalPullbacks
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_finite_ext_two_torsion_rational_pullbacks : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∃ (K' : Type) (_ : Field K') (_ : Algebra (FractionRing R) K'), Module.Finite (FractionRing R) K' ∧ ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] (ρ : R →+* R₂) (i : K' →+* FractionRing R₂), (∀ r : R, i (algebraMap (FractionRing R) K' (algebraMap R (FractionRing R) r)) = algebraMap R₂ (FractionRing R₂) (ρ r)) → ∀ (G₁ : Over (Sp R₂)) [GrpObj G₁] (β : G₁.left ⟶ G.left), IsGrpPullback G₁ G (spMap ρ) β → TwoTorsRat G₁ := by
  first | exact @GlobalTheory.TwoTorsPull.twoTorsRat_of_pullback | exact GlobalTheory.TwoTorsPull.twoTorsRat_of_pullback | (intros; apply GlobalTheory.TwoTorsPull.twoTorsRat_of_pullback <;> assumption)
