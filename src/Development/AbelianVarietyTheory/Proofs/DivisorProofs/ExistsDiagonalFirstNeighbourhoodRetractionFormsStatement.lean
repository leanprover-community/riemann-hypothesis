module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalFirstNeighbourhoodRetractionForms
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

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.exists_diagonal_firstNeighbourhood_retraction_forms : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R), ∃ (S : Thick κ t ⥤ Thick κ t) (u v : 𝟭 _ ⟶ S) (r1 : ∀ T, (KK κ t).M1.obj (S.obj T) →+ (KK κ t).M1.obj T) (r2 : ∀ T, (KK κ t).M2.obj (S.obj T) →+ (KK κ t).M2.obj T) (r3 : ∀ T, (KK κ t).M3.obj (S.obj T) →+ (KK κ t).M3.obj T), ((∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r1 T' ((KK κ t).M1.map (S.map φ) x) = (KK κ t).M1.map φ (r1 T x)) ∧ (∀ T x, r1 T ((KK κ t).M1.map (u.app T) x) = 0) ∧ (∀ T x, r1 T ((KK κ t).M1.map (v.app T) x) = x)) ∧ ((∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r2 T' ((KK κ t).M2.map (S.map φ) x) = (KK κ t).M2.map φ (r2 T x)) ∧ (∀ T x, r2 T ((KK κ t).M2.map (u.app T) x) = 0) ∧ (∀ T x, r2 T ((KK κ t).M2.map (v.app T) x) = x)) ∧ (∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r3 T' ((KK κ t).M3.map (S.map φ) x) = (KK κ t).M3.map φ (r3 T x)) ∧ (∀ T x, r3 T ((KK κ t).M3.map (u.app T) x) = 0) ∧ (∀ T x, r3 T ((KK κ t).M3.map (v.app T) x) = x) := by
  first | exact @GlobalTheory.PDForm.Nbhd.exists_retraction | exact GlobalTheory.PDForm.Nbhd.exists_retraction | (intros; apply GlobalTheory.PDForm.Nbhd.exists_retraction <;> assumption)
