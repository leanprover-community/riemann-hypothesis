module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LineBundleTrivialBasicOpenOfTrivialFibreProduct
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
theorem _root_.GlobalTheory.T.lineBundle_trivial_basicOpen_of_trivial_fibre_product : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (x₀ : 𝟙_ (Over (Sp R)) ⟶ X) (y₀ : 𝟙_ (Over (Sp R)) ⟶ Y), Flat X.hom → Flat Y.hom → IsProper X.hom → IsProper Y.hom → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (Y).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (Y).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X ⊗ Y).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X ⊗ Y).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → ∀ M : LB (X ⊗ Y).left, M.IsLB → Nonempty (Perf (X ⊗ Y).hom M) → Triv (M.pull (lift (𝟙 X) (toUnit X ≫ y₀)).left) → Triv (M.pull (lift (toUnit Y ≫ x₀) (𝟙 Y)).left) → ∀ (K : Type) [Field K] (g₀ : R →+* K) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ (X ⊗ Y).left) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π₀ f₀ (X ⊗ Y).hom (Spec.map (CommRingCat.ofHom g₀)) → Triv (M.pull π₀) → ∃ r : R, g₀ r ≠ 0 ∧ Triv (M.pull ((X ⊗ Y).hom ⁻¹ᵁ (PrimeSpectrum.basicOpen r)).ι) := by
  first | exact @GlobalTheory.Exist.ProdOpen.triv_basicOpen_of_triv_fibre_prod | exact GlobalTheory.Exist.ProdOpen.triv_basicOpen_of_triv_fibre_prod | (intros; apply GlobalTheory.Exist.ProdOpen.triv_basicOpen_of_triv_fibre_prod <;> assumption)
