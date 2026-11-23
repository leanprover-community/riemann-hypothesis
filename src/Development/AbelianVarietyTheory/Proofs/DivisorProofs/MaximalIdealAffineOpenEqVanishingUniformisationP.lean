module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MaxPoints

theorem main : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A →
    ∀ (U : A.left.Opens), IsAffineOpen U → ∀ m : Ideal Γ(A.left, U), m.IsMaximal →
      ∃ z ∈ pre u.ex U, ∀ b, b ∈ m ↔ val u.ex U b z = 0 := by
  intro A _ g L u hA U hU m hm
  haveI : Smooth A.hom := hA.smooth
  have hft : LocallyOfFiniteType A.hom := inferInstance
  let c : ℂ →+* Γ(A.left, U) :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ A.hom.appLE ⊤ U (fun _ _ => trivial)).hom
  have hc : c.FiniteType := by
    have h1 : (A.hom.appLE ⊤ U (fun _ _ => trivial)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType A.hom hft ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
  letI : Algebra ℂ Γ(A.left, U) := c.toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(A.left, U) := hc
  haveI : IsJacobsonRing Γ(A.left, U) := isJacobsonRing_of_finiteType (A := ℂ)
  letI : Field (Γ(A.left, U) ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite ℂ (Γ(A.left, U) ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (Γ(A.left, U) ⧸ m)
  have hb : Function.Bijective (algebraMap ℂ (Γ(A.left, U) ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let i : ℂ ≃ₐ[ℂ] (Γ(A.left, U) ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId ℂ _) hb
  let e : Γ(A.left, U) →ₐ[ℂ] ℂ := (i.symm : (Γ(A.left, U) ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m)
  have he : ∀ a, e.toRingHom (constFn A.hom U a) = a := fun a => e.commutes a
  obtain ⟨x, ⟨hxU, hx⟩, -⟩ := GlobalTheory.existsUnique_point_of_ringHom A U hU e.toRingHom he
  obtain ⟨z, rfl⟩ := u.ex_onto x
  refine ⟨z, hxU, fun b => ?_⟩
  change b ∈ m ↔ valAt' (u.ex z).left U b = 0
  rw [hx b]
  change b ∈ m ↔ i.symm (Ideal.Quotient.mk m b) = 0
  rw [← map_zero i.symm, i.symm.injective.eq_iff, Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.MaxPoints
