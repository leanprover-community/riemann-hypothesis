module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNerveLevelwiseEquivalenceIntegralPullback
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.cechNerve_levelwise_equivalence_integral_pullback : ∀ (R : Type) [CommRing R] (F : Shv R) (Y X Y' X' : Scheme.{0}) (a : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (b : X' ⟶ X),
    IsPullback a f' f b → IsIntegralHom f →
    (∀ (Z Z' : Scheme.{0}) (h : Z ⟶ X) (h' : Z' ⟶ X') (φ : Z' ⟶ Z), IsIntegralHom h → IsPullback φ h' h b → Eqv R (sch.map φ) F) →
    ∀ (m : cech f' ⟶ cech f), IsPullback m (cechAug f') (cechAug f) (sch.map b) → ∀ n, Eqv R (disc.map (m.app n)) F := by
  first | (exact @GlobalTheory.cech_level_eqv_of_integral_pullback) | (exact GlobalTheory.cech_level_eqv_of_integral_pullback) | (intros; apply GlobalTheory.cech_level_eqv_of_integral_pullback  <;> assumption)
