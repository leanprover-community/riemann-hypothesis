module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechFiniteVanishesOffOrigin
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.mumfordBundle_cech_finite_vanishes_off_origin : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ P.A.left) (Y : Scheme.{0}) (π : Y ⟶ (P.A ⊗ P.A).left) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f (fst P.A P.A).left t → IsOpenImmersion t → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → IsNoetherianRing R ∧ (∀ p, Module.Flat R ((cechLB f ((translDiff P.A P.L (𝟙 P.A)).pull π) D).X p)) ∧ (∀ p, Module.Finite R ((cechLB f ((translDiff P.A P.L (𝟙 P.A)).pull π) D).homology p)) ∧ ∀ χ : R →+* K, (Spec.map (CommRingCat.ofHom χ) ≫ t) ≫ P.A.hom = 𝟙 _ → Spec.map (CommRingCat.ofHom χ) ≫ t ≠ η[P.A].left → ∀ p, ∃ r : R, χ r ≠ 0 ∧ ∀ z : (cechLB f ((translDiff P.A P.L (𝟙 P.A)).pull π) D).homology p, r • z = 0 := by
  first | exact @GlobalTheory.MumfordSupport.cohomology_finite_and_vanishes_off_origin | exact GlobalTheory.MumfordSupport.cohomology_finite_and_vanishes_off_origin | (intros; apply GlobalTheory.MumfordSupport.cohomology_finite_and_vanishes_off_origin <;> assumption)
