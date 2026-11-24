module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionFamilyZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnitGeneratorOfLineBundleLocalSection
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_localUnitGenerator_of_lineBundleLocalSectionFamily : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (J : Type) (D : J → X.Opens) (k : J → L.ι) (hD : ∀ j, D j ≤ L.U (k j)) (e : ∀ j, Γ(X, D j)), GlobalTheory.Pinch.IsSecFam L D k hD e → ∃ (V : X.Opens) (a : ∀ i, Γ(X, V ⊓ L.U i)ˣ), (∀ j (x : X) (h : x ∈ D j), IsUnit ((X.presheaf.germ (D j) x h).hom (e j)) → x ∈ V) ∧ GlobalTheory.Pinch.LocGen L V a := by
  first | exact @GlobalTheory.Pinch.exists_locGen_of_secFam | exact GlobalTheory.Pinch.exists_locGen_of_secFam | (intros; apply GlobalTheory.Pinch.exists_locGen_of_secFam <;> assumption)
