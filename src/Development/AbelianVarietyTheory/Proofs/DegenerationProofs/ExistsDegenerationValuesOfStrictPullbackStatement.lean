module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrict
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationValuesOfStrictPullback
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
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

theorem _root_.GlobalTheory.T.exists_degenerationValues_of_strict_pullback : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D'), Strict hD.w → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F], (∀ x, algebraMap (FractionRing R') F (algebraMap R' _ (φ x)) = algebraMap (FractionRing R) F (algebraMap R _ x)) → ∀ (N : NumD F) (ν : NumOf D F N) (th' : H0 D'.P.L 1), (∀ s : H0 D'.P.L 1, ∃ r : R', ∀ j, s.f j = resTop _ (scal D'.P.A.hom r) * th'.f j) → (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → sval ν.th (r ≫ PsiEvenPull.proj hD) z J = (gw hD.w r z (J (r ≫ PsiEvenPull.proj hD)) (J' r)).val * sval th' r z J') → ∃ ν' : NumOf D' F N, (∀ y, hD.xe (ν'.eX y) = ν.eX y) ∧ ∀ x, (ν'.eA x).left ≫ PsiEvenPull.proj hD = (ν.eA x).left := by
  first | exact @GlobalTheory.ValuesStrictPull.exists_numOf_strict_pull | exact GlobalTheory.ValuesStrictPull.exists_numOf_strict_pull | (intros; apply GlobalTheory.ValuesStrictPull.exists_numOf_strict_pull <;> assumption)
