module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem isFinite_fromSpecResidueField_comp_of_isClosed_of_closedPoint : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Over (Sp R)), LocallyOfFiniteType X.hom → ∀ x : X.left, X.hom x = closedPoint R → IsClosed ({x} : Set X.left) → IsFinite (X.left.fromSpecResidueField x ≫ X.hom) := by
  intro R _ _ X hX x hx hc
  haveI := hX
  haveI := isClosed_singleton_iff_isClosedImmersion.mp hc
  have hf : LocallyOfFiniteType (X.left.fromSpecResidueField x ≫ X.hom) := inferInstance
  have hpt : ∀ p : Spec (X.left.residueField x), (X.left.fromSpecResidueField x ≫ X.hom) p = closedPoint R := by
    intro p
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply, hx]
  rw [← Spec.map_preimage (X.left.fromSpecResidueField x ≫ X.hom)] at hf hpt ⊢
  rw [IsFinite.SpecMap_iff]
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hf
  generalize Spec.preimage (X.left.fromSpecResidueField x ≫ X.hom) = φ at hf hpt ⊢
  let K := X.left.residueField x
  let p0 : PrimeSpectrum K := ⟨⊥, Ideal.isPrime_bot⟩
  have hker : RingHom.ker φ.hom = maximalIdeal R := by
    have h1 := congrArg PrimeSpectrum.asIdeal (hpt p0)
    have h2 : (Spec.map φ).base p0 = PrimeSpectrum.comap φ.hom p0 := rfl
    rw [show (Spec.map φ) p0 = (Spec.map φ).base p0 from rfl, h2] at h1
    have h3 : Ideal.comap φ.hom ⊥ = (closedPoint R).asIdeal := by simpa [p0] using h1
    exact h3
  let k := ResidueField R
  let ψ : k →+* K := Ideal.Quotient.lift (maximalIdeal R) φ.hom (fun a ha => by
    rw [← RingHom.mem_ker, hker]; exact ha)
  have hφ : φ.hom = ψ.comp (residue R) := by
    ext a; rfl
  rw [hφ] at hf ⊢
  have hψ : ψ.FiniteType := RingHom.FiniteType.of_comp_finiteType hf
  letI : Algebra k K := ψ.toAlgebra
  haveI : Algebra.FiniteType k K := hψ
  have : Module.Finite k K := finite_of_finite_type_of_isJacobsonRing k K
  have hψf : ψ.Finite := this
  exact hψf.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective)

end GlobalTheory
