module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FamilyFunctionalEquationFieldChange
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

theorem _root_.GlobalTheory.T.familyFunctionalEquation_field_change : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] (k : ℕ) (f : ∀ α, SecBT D T k α) (F F' : Type) [Field F] [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] (φ : TF (R := R) F ⟶ T) (φ' : TF (R := R) F' ⟶ T) (s : Raw D F k) (s' : Raw D F' k), Function.Injective φ.left.appTop.hom → PullB D F φ k f s → PullB D F' φ' k f s' → DegPre.FamFE D F k s → DegPre.FamFE D F' k s' := by
  first | exact @GlobalTheory.famFE_field_change | exact GlobalTheory.famFE_field_change | (intros; apply GlobalTheory.famFE_field_change <;> assumption)
