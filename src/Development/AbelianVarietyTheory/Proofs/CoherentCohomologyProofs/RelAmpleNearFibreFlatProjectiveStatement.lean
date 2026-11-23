module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelAmpleNearFibreFlatProjective
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.relAmple_near_fibre_flat_projective : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (B : Over (Spec (CommRingCat.of R))) (L : LB B.left), Flat B.hom → IsProjBy B.hom → L.IsLB → ∀ (K : Type) [Field K] (g : R →+* K), (∀ y : K, ∃ a b : R, g b ≠ 0 ∧ y * g b = g a) → RelAmple ((Over.pullback (Spec.map (CommRingCat.ofHom g))).obj B) (L.pull (pullback.fst B.hom (Spec.map (CommRingCat.ofHom g)))) → ∃ r : R, g r ≠ 0 ∧ RelAmple ((Over.pullback (Scheme.Opens.ι (X := Spec (CommRingCat.of R)) (PrimeSpectrum.basicOpen r))).obj B) (L.pull (pullback.fst B.hom (Scheme.Opens.ι (X := Spec (CommRingCat.of R)) (PrimeSpectrum.basicOpen r)))) := by
  first | exact @GlobalTheory.AmpleNear.relAmple_near_fibre | exact GlobalTheory.AmpleNear.relAmple_near_fibre | (intros; apply GlobalTheory.AmpleNear.relAmple_near_fibre <;> assumption)
