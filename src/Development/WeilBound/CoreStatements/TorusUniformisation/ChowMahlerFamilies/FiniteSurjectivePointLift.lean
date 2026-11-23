module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.PullbackCarrier
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ToXQFst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.FiniteSurjectivePointLift

theorem exists_ringHom (L A : Type) [Field L] [CommRing A] [Nontrivial A] (φ : L →+* A) (hφ : φ.Finite) :
    ∃ ψ : A →+* AlgebraicClosure L, ψ.comp φ = algebraMap L (AlgebraicClosure L) := by
  letI := φ.toAlgebra
  haveI : Module.Finite L A := hφ
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI := Ideal.Quotient.field m
  haveI : Module.Finite L (A ⧸ m) := inferInstance
  haveI : Algebra.IsAlgebraic L (A ⧸ m) := inferInstance
  let j : (A ⧸ m) →ₐ[L] AlgebraicClosure L := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(j.comp (Ideal.Quotient.mkₐ L m)).toRingHom, ?_⟩
  ext x
  exact (j.comp (Ideal.Quotient.mkₐ L m)).commutes x

theorem exists_point (L : Type) [Field L] (P : Scheme.{0}) [Nonempty P] (g : P ⟶ Spec (CommRingCat.of L))
    [IsFinite g] : ∃ x : Spec (CommRingCat.of (AlgebraicClosure L)) ⟶ P,
      x ≫ g = Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L))) := by
  haveI hA : IsAffine P := isAffine_of_isAffineHom g
  have hfin : (g.appTop).hom.Finite := g.finite_app ⊤ (isAffineOpen_top _)
  let φ : L →+* Γ(P, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ g.appTop).hom
  have hφ : φ.Finite := by
    refine RingHom.Finite.comp hfin ?_
    exact RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of L)).inv).2
  haveI : Nonempty (⊤ : P.Opens) := ⟨⟨Classical.arbitrary P, trivial⟩⟩
  obtain ⟨ψ, hψ⟩ := exists_ringHom L Γ(P, ⊤) φ hφ
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ P.isoSpec.inv, ?_⟩
  rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv]
  simp only [← Spec.map_comp]
  congr 1
  ext x
  exact congrArg (fun f => f x) hψ

end PositivityTheory.Xgn.FiniteSurjectivePointLift

theorem PositivityTheory.Xgn.finite_surjective_point_lift : ∀ (Z' Z : Scheme.{0}) (π : Z' ⟶ Z), IsFinite π → Surjective π → ∀ (L : Type) [Field L] (zZ : Sp L ⟶ Z),
    ∃ x : Sp (AlgebraicClosure L) ⟶ Z', x ≫ π = spMap (algebraMap L (AlgebraicClosure L)) ≫ zZ := by
  intro Z' Z π hfin hsurj L _ zZ
  haveI : Surjective (pullback.snd π zZ) := inferInstance
  obtain ⟨p, -⟩ := (pullback.snd π zZ).surjective (IsLocalRing.closedPoint L)
  haveI : Nonempty ↥(pullback π zZ) := ⟨p⟩
  obtain ⟨x, hx⟩ := FiniteSurjectivePointLift.exists_point L (pullback π zZ) (pullback.snd π zZ)
  refine ⟨x ≫ pullback.fst π zZ, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hx]
