module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorDown

theorem ext_of_fraction_meet : ∀ (Z : Scheme.{0}) (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (gam : FractionRing R →+* FractionRing R'), (∀ (x : FractionRing R) (w : R'), algebraMap R' _ w = gam x → ∃ r : R, algebraMap R _ r = x) → ∀ (x : Sp (FractionRing R) ⟶ Z) (a' : Sp R' ⟶ Z), jK R' ≫ a' = spMap gam ≫ x → ∃ a : Sp R ⟶ Z, jK R ≫ a = x := by
  intro Z R R' _ _ _ _ _ gam hgam x a' hx
  obtain ⟨U, hU, hz, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens)
    (show a' (IsLocalRing.closedPoint R') ∈ (⊤ : Z.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  have hra : Set.range a' ⊆ Set.range hU'.fromSpec := by
    rw [hU'.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint p).map a'.continuous).mem_open U.isOpen hz
  have hrx : Set.range x ⊆ Set.range hU'.fromSpec := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨t'⟩ : Nonempty (Sp (FractionRing R')) := inferInstance
    have e1 : (spMap gam) t' = t := Subsingleton.elim _ _
    have e2 := congrArg (fun h : Sp (FractionRing R') ⟶ Z => h t') hx
    simp only [Scheme.Hom.comp_apply] at e2
    rw [← e1, ← e2]
    exact hra ⟨_, rfl⟩
  have ha₁ := IsOpenImmersion.lift_fac hU'.fromSpec a' hra
  have hx₁ := IsOpenImmersion.lift_fac hU'.fromSpec x hrx
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec a' hra)] at ha₁
  rw [← Spec.map_preimage (IsOpenImmersion.lift hU'.fromSpec x hrx)] at hx₁
  set ψ := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec a' hra) with hψ
  set χ := Spec.preimage (IsOpenImmersion.lift hU'.fromSpec x hrx) with hχ
  have key : ψ ≫ CommRingCat.ofHom (algebraMap R' (FractionRing R')) = χ ≫ CommRingCat.ofHom gam := by
    apply Spec.map_injective
    rw [← cancel_mono hU'.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      ha₁, hx₁]
    exact hx
  have hmem : ∀ b : Γ(Z, U), χ.hom b ∈ (algebraMap R (FractionRing R)).range := by
    intro b
    have e := congrArg (fun h => h.hom b) key
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
    obtain ⟨r, hr⟩ := hgam (χ.hom b) (ψ.hom b) e
    exact ⟨r, hr⟩
  have hinj : Function.Injective (algebraMap R (FractionRing R)).rangeRestrict := fun a b h =>
    IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val h)
  let eR := RingEquiv.ofBijective (algebraMap R (FractionRing R)).rangeRestrict
    ⟨hinj, RingHom.rangeRestrict_surjective _⟩
  let θ : Γ(Z, U) →+* R := eR.symm.toRingHom.comp (χ.hom.codRestrict _ hmem)
  have hθ : ∀ b, algebraMap R (FractionRing R) (θ b) = χ.hom b := by
    intro b
    have := eR.apply_symm_apply (χ.hom.codRestrict _ hmem b)
    exact congrArg Subtype.val this
  refine ⟨Spec.map (CommRingCat.ofHom θ : Γ(Z, U) ⟶ CommRingCat.of R) ≫ hU'.fromSpec, ?_⟩
  rw [← hx₁, ← Category.assoc]
  congr 1
  rw [← Spec.map_comp]
  congr 1
  ext b
  exact hθ b

end GlobalTheory.TorDown
